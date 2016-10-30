/**
 * $RCSfile: MessageRouter.java,v $
 * $Revision: 3007 $
 * $Date: 2005-10-31 13:29:25 -0300 (Mon, 31 Oct 2005) $
 *
 * Copyright (C) 2005-2008 Jive Software. All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package org.jivesoftware.openfire;

import org.apache.http.HttpEntity;
import org.apache.http.NameValuePair;
import org.apache.http.client.entity.UrlEncodedFormEntity;
import org.apache.http.client.methods.CloseableHttpResponse;
import org.apache.http.client.methods.HttpPost;
import org.apache.http.impl.client.CloseableHttpClient;
import org.apache.http.impl.client.HttpClients;
import org.apache.http.message.BasicNameValuePair;
import org.dom4j.QName;
import org.jivesoftware.database.DbConnectionManager;
import org.jivesoftware.openfire.carbons.Sent;
import org.jivesoftware.openfire.container.BasicModule;
import org.jivesoftware.openfire.forward.Forwarded;
import org.jivesoftware.openfire.interceptor.InterceptorManager;
import org.jivesoftware.openfire.interceptor.PacketRejectedException;
import org.jivesoftware.openfire.session.ClientSession;
import org.jivesoftware.openfire.session.LocalClientSession;
import org.jivesoftware.openfire.session.Session;
import org.jivesoftware.openfire.user.UserManager;
import org.jivesoftware.util.Blowfish;
import org.jivesoftware.util.Encryptor;
import org.jivesoftware.util.JiveGlobals;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.xmpp.packet.JID;
import org.xmpp.packet.Message;
import org.xmpp.packet.Packet;
import org.xmpp.packet.PacketError;
import org.dom4j.Element;

import java.io.BufferedReader;
import java.io.ByteArrayOutputStream;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.net.URL;
import java.net.URLConnection;
import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Date;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.StringTokenizer;

/**
 * <p>
 * Route message packets throughout the server.
 * </p>
 * <p>
 * Routing is based on the recipient and sender addresses. The typical packet
 * will often be routed twice, once from the sender to some internal server
 * component for handling or processing, and then back to the router to be
 * delivered to it's final destination.
 * </p>
 * 
 * @author Iain Shigeoka
 */
public class MessageRouter extends BasicModule {

	private static Logger log = LoggerFactory.getLogger(MessageRouter.class);
	
	 //默认传输编码
    public static String ENCODING = "UTF8";	

	private OfflineMessageStrategy messageStrategy;
	private RoutingTable routingTable;
	private SessionManager sessionManager;
	private MulticastRouter multicastRouter;
	private UserManager userManager;

	private String serverName;

	/**
	 * Constructs a message router.
	 */
	public MessageRouter() {
		super("XMPP Message Router");
	}

	/**
	 * <p>
	 * Performs the actual packet routing.
	 * </p>
	 * <p>
	 * You routing is considered 'quick' and implementations may not take
	 * excessive amounts of time to complete the routing. If routing will take a
	 * long amount of time, the actual routing should be done in another thread
	 * so this method returns quickly.
	 * </p>
	 * <h2>Warning</h2>
	 * <p>
	 * Be careful to enforce concurrency DbC of concurrent by synchronizing any
	 * accesses to class resources.
	 * </p>
	 * 
	 * @param packet
	 *            The packet to route
	 * @throws NullPointerException
	 *             If the packet is null
	 */
	public void route(Message packet) {
		if (packet == null) {
			throw new NullPointerException();
		}
		ClientSession session = sessionManager.getSession(packet.getFrom());

		try {
			// Invoke the interceptors before we process the read packet
			InterceptorManager.getInstance().invokeInterceptors(packet,
					session, true, false);
			if (session == null
					|| session.getStatus() == Session.STATUS_AUTHENTICATED) {
				JID recipientJID = packet.getTo();

				// If the server receives a message stanza with no 'to'
				// attribute, it MUST treat the message as if the 'to' address
				// were the bare JID <localpart@domainpart> of the sending
				// entity.
				if (recipientJID == null) {
					recipientJID = packet.getFrom().asBareJID();
				}

				// Check if the message was sent to the server hostname
				if (recipientJID.getNode() == null
						&& recipientJID.getResource() == null
						&& serverName.equals(recipientJID.getDomain())) {
					if (packet.getElement().element("addresses") != null) {
						// Message includes multicast processing instructions.
						// Ask the multicastRouter
						// to route this packet
						multicastRouter.route(packet);
					} else {
						// Message was sent to the server hostname so forward it
						// to a configurable
						// set of JID's (probably admin users)
						sendMessageToAdmins(packet);
					}
					return;
				}

				boolean isAcceptable = true;
				if (session instanceof LocalClientSession) {
					System.out.println("========MessageRouter===aa=======");  
					// Check if we could process messages from the recipient.
					// If not, return a not-acceptable error as per XEP-0016:
					// If the user attempts to send an outbound stanza to a
					// contact and that stanza type is blocked, the user's
					// server MUST NOT route the stanza to the contact but
					// instead MUST return a <not-acceptable/> error
					Message dummyMessage = packet.createCopy();
					dummyMessage.setFrom(packet.getTo());
					dummyMessage.setTo(packet.getFrom());
					if (!((LocalClientSession) session)
							.canProcess(dummyMessage)) {
						System.out.println("========MessageRouter===aa===11====");
						packet.setTo(session.getAddress());
						packet.setFrom((JID) null);
						packet.setError(PacketError.Condition.not_acceptable);
						session.process(packet);
						isAcceptable = false;
					}
				}
				if (isAcceptable) {
					boolean isPrivate = packet.getElement().element(
							QName.get("private", "urn:xmpp:carbons:2")) != null;
					try {
						// Deliver stanza to requested route
						routingTable.routePacket(recipientJID, packet, false);
						OfflineMessageStore oms = new OfflineMessageStore();
						oms.addMessage_toHistory(packet);
						
						// 向客户端发回执
						Message yuanMessage = packet.createCopy();
	                    Message receiptMessage = new Message();
	                    receiptMessage.setTo(yuanMessage.getFrom());
	                    receiptMessage.setType(Message.Type.normal);
	                    receiptMessage.setBody("rrrrrrrrrrr");
	                    System.out.println("0000000000回执内容" + receiptMessage);
	                    try {
	                        XMPPServer.getInstance().getPacketDeliverer().deliver(receiptMessage);
	                        System.out.println("服务端回执成功！");
	                    } catch (Exception e) {
	                        e.printStackTrace();
	                    }
						
					} catch (Exception e) {
						log.error("Failed to route packet: " + packet.toXML(),
								e);
						routingFailed(recipientJID, packet);
					}

					// Sent carbon copies to other resources of the sender:
					// When a client sends a <message/> of type "chat"
					if (packet.getType() == Message.Type.chat && !isPrivate
							&& session != null) {
						System.out.println("========MessageRouter===00=======");  
						 							// &&
													// session.isMessageCarbonsEnabled()
													// ??? // must the own
													// session also be carbon
													// enabled?
						List<JID> routes = routingTable.getRoutes(packet
								.getFrom().asBareJID(), null);
						for (JID route : routes) {
							System.out.println("========MessageRouter===11======="+session.getAddress().toString());  
							// The sending server SHOULD NOT send a forwarded
							// copy to the sending full JID if it is a
							// Carbons-enabled resource.
							if (!route.equals(session.getAddress())) {
								ClientSession clientSession = sessionManager
										.getSession(route);
								if (clientSession != null
										&& clientSession
												.isMessageCarbonsEnabled()) {
									Message message = new Message();
									// The wrapping message SHOULD maintain the
									// same 'type' attribute value
									message.setType(packet.getType());
									// the 'from' attribute MUST be the
									// Carbons-enabled user's bare JID
									message.setFrom(packet.getFrom()
											.asBareJID());
									// and the 'to' attribute SHOULD be the full
									// JID of the resource receiving the copy
									message.setTo(route);
									// The content of the wrapping message MUST
									// contain a <sent/> element qualified by
									// the namespace "urn:xmpp:carbons:2", which
									// itself contains a <forwarded/> qualified
									// by the namespace "urn:xmpp:forward:0"
									// that contains the original <message/>
									// stanza.
									message.addExtension(new Sent(
											new Forwarded(packet)));
									clientSession.process(message);
									System.out.println("========MessageRouter===22=======");  
								}
							}
						}
					}
				}
			} else {
				System.out.println("========MessageRouter===33======="+packet.getBody().toString());  	
				
//				Blowfish bf = new Blowfish("56t1ij4tiOETyJs");
//				System.out.println("========MessageRouter===33===password==1=="
//				+bf.decryptString("a4534ae8dd9a9323dfcde08b89c09cd6f556c9a67835c987d588b5e7b21a5f7b"));
//				
//				System.out.println("========MessageRouter===33===mingma===="
//						+bf.encryptString("12345678"));
//				
//				System.out.println("========MessageRouter===33===password==1=="
//						+bf.decryptString(bf.encryptString("12345678")));				
				
				if(packet.getBody().toString().startsWith("Verify:")||packet.getBody().toString().startsWith("Forget:")){
					String phonenumber = "";
					if(packet.getBody().toString().startsWith("Verify:")){
						System.out.println("====Verify:====");
						phonenumber = packet.getBody().toString().replace("Verify:", "");
					}else if(packet.getBody().toString().startsWith("Forget:")){
						System.out.println("====Forget:====");
						phonenumber = packet.getBody().toString().replace("Forget:", "");
					}
					System.out.println("========MessageRouter===33======="+phonenumber); 
					
					Random rd = new Random();
					int result =rd.nextInt(900000)+100000;
					String postUrl="http://sms.jiangukj.com/SendSms.aspx";
					
					boolean flag = false;
					
					Connection con = null;
					PreparedStatement pstmt = null;
					ResultSet rs = null;				
					try {	
						con = DbConnectionManager.getConnection();
						pstmt=con.prepareStatement("select * from ofUser where username=?");
						pstmt.setString(1,phonenumber);
						System.out.println("====check=========77==========");
						rs=pstmt.executeQuery();
						if (rs.next())
						{
							System.out.println("====check=========88==========");
							flag = true;
						}
					} catch (SQLException e) {
						e.printStackTrace();
					}finally {
						DbConnectionManager.closeConnection(pstmt, con);
					}
	
					if(!flag){
						 Map<String,String> map = new HashMap<String,String>();
						 map.put("action","code");
						 map.put("username","zwzfj2");
						 map.put("userpass","lglp112522");
						 map.put("mobiles",phonenumber);
						 map.put("content",result+"");
						 map.put("codeid", "3907");
						 //String aa = httpPost(postUrl, map);
					}
					
					packet.setTo(session.getAddress());
					
					if(packet.getBody().toString().startsWith("Verify:")){
						System.out.println("====Verify:==111==");
						if(!flag){
							packet.setBody("Verify:Unregistered:"+result);
						}else{
							packet.setBody("Verify:HasRegistered");
						}
					}else if(packet.getBody().toString().startsWith("Forget:")){
						System.out.println("====Forget:====");
						if(!flag){
							packet.setBody("Forget:Unregistered");
						}else{
							packet.setBody("Forget:HasRegistered:"+result);
						}
					}
					
					packet.setFrom((JID) null);
					packet.setError(PacketError.Condition.not_authorized);
					session.process(packet);
				}
				if(packet.getBody().toString().startsWith("ChangePassword:")){
					String newStrs = packet.getBody().toString().replace("ChangePassword:", "");
					System.out.println("====check=========Forget:ChangePassword======newStrs===="+newStrs);
					String nPhone = newStrs.split("&")[0];
					String nPassword = newStrs.split("&")[1];
					System.out.println("====check=========Forget:ChangePassword======nPhone===="+nPhone);
					System.out.println("====check=========Forget:ChangePassword======nPassword===="+nPassword);
					Connection con = null;
					PreparedStatement pstmt = null;
					ResultSet rs = null;	
					String encryptedPassword = "";
					try {	
						con = DbConnectionManager.getConnection();
						pstmt=con.prepareStatement("select propValue  from ofProperty where name = 'passwordKey'");						
						System.out.println("====check=========Forget:ChangePassword======11====");
						rs=pstmt.executeQuery();
						if (rs.next())
						{
							encryptedPassword = rs.getString(1);
							System.out.println("====check=========Forget:ChangePassword====22======"+rs.getString(1));							
						}												

					} catch (SQLException e) {
						e.printStackTrace();
					}finally {
						DbConnectionManager.closeConnection(pstmt, con);
					}
					
					Blowfish bf = new Blowfish(encryptedPassword);
					String newPassword = bf.encryptString(nPassword);				
					
					Connection con1 = null;
					PreparedStatement pstmt1 = null;
					try {
						System.out.println("====check=========Forget:ChangePassword====333======");			
						con1 = DbConnectionManager.getConnection();
						pstmt1 = con1.prepareStatement("update ofUser set encryptedPassword = '"+newPassword+"' where username = '"+nPhone+"'");	
						System.out.println("====check=========Forget:ChangePassword====44======");			
						pstmt1.executeUpdate();
					}catch (SQLException e) {
						e.printStackTrace();
					}finally {
						DbConnectionManager.closeConnection(pstmt1, con1);
					}
					packet.setTo(session.getAddress());
					packet.setBody("ChangePassword:OK");
					packet.setFrom((JID) null);
					packet.setError(PacketError.Condition.not_authorized);
					session.process(packet);						
				}
			}
			// Invoke the interceptors after we have processed the read packet
			InterceptorManager.getInstance().invokeInterceptors(packet,
					session, true, true);
		} catch (PacketRejectedException e) {
			// An interceptor rejected this packet
			if (session != null && e.getRejectionMessage() != null
					&& e.getRejectionMessage().trim().length() > 0) {
				// A message for the rejection will be sent to the sender of the
				// rejected packet
				Message reply = new Message();
				reply.setID(packet.getID());
				reply.setTo(session.getAddress());
				reply.setFrom(packet.getTo());
				reply.setType(packet.getType());
				reply.setThread(packet.getThread());
				reply.setBody(e.getRejectionMessage());
				session.process(reply);
			}
		}
	}
	
	 /**
     * Http Post 封装
     * @param url 请求的url地址
     * @param paras 参数集合
     * @return String 返回结果:字符串
     *
     */
    public static String httpPost(String url,Map<String,String> paras){

        //初始化返回结果
        String resultStr = null;
        try{
            //创建安全的httpClient
            CloseableHttpClient httpClient = HttpClients.createDefault();

            //根据参数集合构造表单列表
            List<NameValuePair> formParas = new ArrayList<NameValuePair>();
            if(paras != null){
                for(String key :paras.keySet()){
                    formParas.add(new BasicNameValuePair(key,paras.get(key)));
                }
            }

            //对表单进行编码格式化
            UrlEncodedFormEntity entity = new UrlEncodedFormEntity(formParas, ENCODING);

            //初始化post
            HttpPost httpPost = new HttpPost(url);

            //设置post内容
            httpPost.setEntity(entity);

            //初始化安全的HttpResponse
            CloseableHttpResponse httpResponse = httpClient.execute(httpPost);
            try{
                //执行请求
                HttpEntity httpEntity = httpResponse.getEntity();

                //获取请求结果
                if(httpEntity!= null){
                    //利用缓冲区,获取返回结果输入流并读取
                    InputStream inputStream = httpEntity.getContent();
                    ByteArrayOutputStream bos = new ByteArrayOutputStream();
                    try{
                        byte[] buffer = new byte[1024];
                        int length;
                        while((length = inputStream.read(buffer))!= -1){
                            bos.write(buffer,0,length);
                        }
                        byte[] result = bos.toByteArray();

                        //将获取到的字节数据结果转换为字符串
                        resultStr = new String(result,ENCODING);
                        System.out.println(resultStr);
                    }catch (Exception e){
                        System.out.println(e.getMessage());
                    }finally {
                        //关闭输入流
                        inputStream.close();
                    }
                }
            }catch (Exception e){
                System.out.println(e.getMessage());
            }finally {
                httpResponse.close();
            }
        }catch (Exception e){
            System.out.println(e.getMessage());
        }
        return  resultStr;
    }

	/**
	 * Forwards the received message to the list of users defined in the
	 * property <b>xmpp.forward.admins</b>. The property may include bare JIDs
	 * or just usernames separated by commas or white spaces. When using bare
	 * JIDs the target user may belong to a remote server.
	 * <p>
	 * 
	 * If the property <b>xmpp.forward.admins</b> was not defined then the
	 * message will be sent to all the users allowed to enter the admin console.
	 * 
	 * @param packet
	 *            the message to forward.
	 */
	private void sendMessageToAdmins(Message packet) {
		String jids = JiveGlobals.getProperty("xmpp.forward.admins");
		if (jids != null && jids.trim().length() > 0) {
			// Forward the message to the users specified in the
			// "xmpp.forward.admins" property
			StringTokenizer tokenizer = new StringTokenizer(jids, ", ");
			while (tokenizer.hasMoreTokens()) {
				String username = tokenizer.nextToken();
				Message forward = packet.createCopy();
				if (username.contains("@")) {
					// Use the specified bare JID address as the target address
					forward.setTo(username);
				} else {
					forward.setTo(username + "@" + serverName);
				}
				route(forward);
			}
		} else {
			// Forward the message to the users allowed to log into the admin
			// console
			for (JID jid : XMPPServer.getInstance().getAdmins()) {
				Message forward = packet.createCopy();
				forward.setTo(jid);
				route(forward);
			}
		}
	}

	@Override
	public void initialize(XMPPServer server) {
		super.initialize(server);
		messageStrategy = server.getOfflineMessageStrategy();
		routingTable = server.getRoutingTable();
		sessionManager = server.getSessionManager();
		multicastRouter = server.getMulticastRouter();
		userManager = server.getUserManager();
		serverName = server.getServerInfo().getXMPPDomain();
	}

	/**
	 * Notification message indicating that a packet has failed to be routed to
	 * the recipient.
	 * 
	 * @param recipient
	 *            address of the entity that failed to receive the packet.
	 * @param packet
	 *            Message packet that failed to be sent to the recipient.
	 */
	public void routingFailed(JID recipient, Packet packet) {
		log.debug("Message sent to unreachable address: " + packet.toXML());
		final Message msg = (Message) packet;
		boolean storeOffline = true;

		if (msg.getType().equals(Message.Type.chat)
				&& serverName.equals(recipient.getDomain())
				&& recipient.getResource() != null) {
			// Find an existing AVAILABLE session with non-negative priority.
			for (JID address : routingTable.getRoutes(recipient.asBareJID(),
					packet.getFrom())) {
				ClientSession session = routingTable.getClientRoute(address);
				if (session != null && session.isInitialized()) {
					if (session.getPresence().getPriority() >= 1) {
						storeOffline = false;
					}
				}
			}
		}

		if (!storeOffline) {
			// If message was sent to an unavailable full JID of a user then
			// retry using the bare JID.
			routingTable.routePacket(recipient.asBareJID(), packet, false);
		} else {
			// Delegate to offline message strategy, which will either bounce or
			// ignore the message depending on user settings.
			messageStrategy.storeOffline((Message) packet);
		}
	}
}
