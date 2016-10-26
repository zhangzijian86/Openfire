/*
 * Generated by the Jasper component of Apache Tomcat
 * Version: JspC/ApacheTomcat8
 * Generated at: 2016-10-26 07:33:04 UTC
 * Note: The last modified time of this file was set to
 *       the last modified time of the source file after
 *       generation to assist with modification tracking.
 */
package org.jivesoftware.openfire.admin;

import javax.servlet.*;
import javax.servlet.http.*;
import javax.servlet.jsp.*;
import java.io.*;
import java.text.SimpleDateFormat;
import java.util.Date;
import java.text.ParseException;
import org.jivesoftware.util.ParamUtils;
import org.jivesoftware.util.Log;
import org.jivesoftware.util.StringUtils;

public final class log_jsp extends org.apache.jasper.runtime.HttpJspBase
    implements org.apache.jasper.runtime.JspSourceDependent {


    static final SimpleDateFormat formatter = new SimpleDateFormat("yyyy.MM.dd kk:mm:ss");

    private static String parseDate(String input) {
        if (input == null || "".equals(input)) {
            return input;
        }
        if (input.length() < 19) {
            return input;
        }
        String d = input.substring(0,19);
        // try to parse it
        try {
            StringBuffer buf = new StringBuffer(input.length());
            synchronized (formatter) {
                Date date = formatter.parse(d);
                buf.append("<span class=\"date\" title=\"").append(formatter.format(date))
                        .append("\">");
            }
            buf.append(d).append("</span>");
            buf.append(input.substring(19,input.length()));
            return buf.toString();
        }
        catch (ParseException pe) {
            return input;
        }
    }

    private static String hilite(String input) {
        if (input == null || "".equals(input)) {
            return input;
        }
        if (input.indexOf("org.jivesoftware.") > -1) {
            StringBuffer buf = new StringBuffer();
            buf.append("<span class=\"hilite\">").append(input).append("</span>");
            return buf.toString();
        }
        else if (input.trim().startsWith("---") && input.trim().endsWith("---")) {
            StringBuffer buf = new StringBuffer();
            buf.append("<span class=\"hilite-marker\">").append(input).append("</span>");
            return buf.toString();
        }
        return input;
    }

  private static final javax.servlet.jsp.JspFactory _jspxFactory =
          javax.servlet.jsp.JspFactory.getDefaultFactory();

  private static java.util.Map<java.lang.String,java.lang.Long> _jspx_dependants;

  private org.apache.jasper.runtime.TagHandlerPool _005fjspx_005ftagPool_005ffmt_005fmessage_0026_005fkey_005fnobody;

  private javax.el.ExpressionFactory _el_expressionfactory;
  private org.apache.tomcat.InstanceManager _jsp_instancemanager;

  public java.util.Map<java.lang.String,java.lang.Long> getDependants() {
    return _jspx_dependants;
  }

  public void _jspInit() {
    _005fjspx_005ftagPool_005ffmt_005fmessage_0026_005fkey_005fnobody = org.apache.jasper.runtime.TagHandlerPool.getTagHandlerPool(getServletConfig());
    _el_expressionfactory = _jspxFactory.getJspApplicationContext(getServletConfig().getServletContext()).getExpressionFactory();
    _jsp_instancemanager = org.apache.jasper.runtime.InstanceManagerFactory.getInstanceManager(getServletConfig());
  }

  public void _jspDestroy() {
    _005fjspx_005ftagPool_005ffmt_005fmessage_0026_005fkey_005fnobody.release();
  }

  public void _jspService(final javax.servlet.http.HttpServletRequest request, final javax.servlet.http.HttpServletResponse response)
        throws java.io.IOException, javax.servlet.ServletException {

    final javax.servlet.jsp.PageContext pageContext;
    javax.servlet.http.HttpSession session = null;
    final javax.servlet.ServletContext application;
    final javax.servlet.ServletConfig config;
    javax.servlet.jsp.JspWriter out = null;
    final java.lang.Object page = this;
    javax.servlet.jsp.JspWriter _jspx_out = null;
    javax.servlet.jsp.PageContext _jspx_page_context = null;


    try {
      response.setContentType("text/html");
      pageContext = _jspxFactory.getPageContext(this, request, response,
      			"error.jsp", true, 8192, true);
      _jspx_page_context = pageContext;
      application = pageContext.getServletContext();
      config = pageContext.getServletConfig();
      session = pageContext.getSession();
      out = pageContext.getOut();
      _jspx_out = out;

      out.write("\n\n\n\n\n");
      org.jivesoftware.admin.AdminPageBean pageinfo = null;
      pageinfo = (org.jivesoftware.admin.AdminPageBean) _jspx_page_context.getAttribute("pageinfo", javax.servlet.jsp.PageContext.REQUEST_SCOPE);
      if (pageinfo == null){
        pageinfo = new org.jivesoftware.admin.AdminPageBean();
        _jspx_page_context.setAttribute("pageinfo", pageinfo, javax.servlet.jsp.PageContext.REQUEST_SCOPE);
      }
      out.write('\n');
      out.write('\n');
      out.write('\n');
      out.write('\n');

    // Get parameters
    String log = ParamUtils.getParameter(request,"log");
    String numLinesParam = ParamUtils.getParameter(request,"lines");
    int numLines = ParamUtils.getIntParameter(request,"lines",50);
    String mode = ParamUtils.getParameter(request,"mode");

    // Only allow requests for valid log file names.
    if (!("debug".equals(log) || "warn".equals(log) || "info".equals(log) || "error".equals(log))) {
        log = null;
    }

    // Set defaults
    if (log == null) {
        log = "error";
    }
    if (mode == null) {
        mode = "asc";
    }
    if (numLinesParam == null) {
        numLinesParam = "50";
    }

    // Other vars
    File logDir = new File(Log.getLogDirectory());
    String filename = log + ".log";
    File logFile = new File(logDir, filename);
    
    String lines[] = new String[0];
    int start = 0;
    try {
	    BufferedReader in = new BufferedReader(new InputStreamReader(new FileInputStream(logFile), "UTF-8"));
	    String line;
	    int totalNumLines = 0;
	    while ((line=in.readLine()) != null) {
	        totalNumLines++;
	    }
	    in.close();
	    // adjust the 'numLines' var to match totalNumLines if 'all' was passed in:
	    if ("All".equals(numLinesParam)) {
	        numLines = totalNumLines;
	    }
	    lines = new String[numLines];
	    in = new BufferedReader(new InputStreamReader(new FileInputStream(logFile), "UTF-8"));
	    // skip lines
	    start = totalNumLines - numLines;
	    if (start < 0) { start = 0; }
	    for (int i=0; i<start; i++) {
	        in.readLine();
	    }
	    int i = 0;
	    if ("asc".equals(mode)) {
	        while ((line=in.readLine()) != null && i<numLines) {
	            line = StringUtils.escapeHTMLTags(line);
	            line = parseDate(line);
	            line = hilite(line);
	            lines[i] = line;
	            i++;
	        }
	    }
	    else {
	        int end = lines.length-1;
	        while ((line=in.readLine()) != null && i<numLines) {
	            line = StringUtils.escapeHTMLTags(line);
	            line = parseDate(line);
	            line = hilite(line);
	            lines[end-i] = line;
	            i++;
	        }
	    }
	    numLines = start + i;
    } catch (FileNotFoundException ex) {
    	Log.info("Could not open (log)file.", ex);
    }

      out.write("\n\n<html>\n<head>\n    <title>");
      out.print( StringUtils.escapeHTMLTags(log) );
      out.write("</title>\n    <meta name=\"decorator\" content=\"none\"/>\n    <style type=\"text/css\">\n    .log TABLE {\n        border : 1px #ccc solid;\n    }\n    .log TH {\n        font-family : verdana, arial, sans-serif;\n        font-weight : bold;\n        font-size : 8pt;\n    }\n    .log TR TH {\n        background-color : #ddd;\n        border-bottom : 1px #ccc solid;\n        padding-left : 2px;\n        padding-right : 2px;\n        text-align : left;\n    }\n    .log .head-num {\n        border-right : 1px #ccc solid;\n    }\n    .log TD {\n        font-family : courier new,monospace;\n        font-size : 9pt;\n        background-color : #ffe;\n    }\n    .log .num {\n        width : 1%;\n        background-color : #eee !important;\n        border-right : 1px #ccc solid;\n        padding-left : 2px;\n        padding-right : 2px;\n    }\n    .log .line {\n        padding-left : 10px;\n    }\n    .hilite {\n        color : #900;\n    }\n    .hilite-marker {\n        background-color : #ff0;\n        color : #000;\n        font-weight : bold;\n    }\n    </style>\n");
      out.write("</head>\n<body>\n\n<div class=\"log\">\n<table cellpadding=\"1\" cellspacing=\"0\" border=\"0\" width=\"100%\">\n<tr>\n    <th class=\"head-num\">");
      if (_jspx_meth_fmt_005fmessage_005f0(_jspx_page_context))
        return;
      out.write("</th>\n    <th>&nbsp;</th>\n</tr>\n<tr>\n    <td width=\"1%\" nowrap class=\"num\">\n        ");
  if ("asc".equals(mode)) { 
      out.write("\n            ");
  for (int j=start+1; j<=numLines; j++) { 
      out.write("\n                ");
      out.print( j );
      out.write("<br>\n            ");
  } 
      out.write("\n        ");
  } else { 
      out.write("\n            ");
  for(int j=numLines; j>=start+1; j--) { 
      out.write("\n                ");
      out.print( j );
      out.write("<br>\n            ");
  } 
      out.write("\n        ");
  } 
      out.write("\n    </td>\n    <td width=\"99%\" class=\"line\">\n        ");
 for (String line1 : lines) {
            if (line1 != null) {
        
      out.write("\n        <nobr>");
      out.print( line1 );
      out.write("\n        </nobr>\n        <br>\n\n        ");
 }
        }
        
      out.write("\n    </td>\n</tr>\n</table>\n</div>\n\n</body>\n</html>\n");
    } catch (java.lang.Throwable t) {
      if (!(t instanceof javax.servlet.jsp.SkipPageException)){
        out = _jspx_out;
        if (out != null && out.getBufferSize() != 0)
          try {
            if (response.isCommitted()) {
              out.flush();
            } else {
              out.clearBuffer();
            }
          } catch (java.io.IOException e) {}
        if (_jspx_page_context != null) _jspx_page_context.handlePageException(t);
        else throw new ServletException(t);
      }
    } finally {
      _jspxFactory.releasePageContext(_jspx_page_context);
    }
  }

  private boolean _jspx_meth_fmt_005fmessage_005f0(javax.servlet.jsp.PageContext _jspx_page_context)
          throws java.lang.Throwable {
    javax.servlet.jsp.PageContext pageContext = _jspx_page_context;
    javax.servlet.jsp.JspWriter out = _jspx_page_context.getOut();
    //  fmt:message
    org.apache.taglibs.standard.tag.rt.fmt.MessageTag _jspx_th_fmt_005fmessage_005f0 = (org.apache.taglibs.standard.tag.rt.fmt.MessageTag) _005fjspx_005ftagPool_005ffmt_005fmessage_0026_005fkey_005fnobody.get(org.apache.taglibs.standard.tag.rt.fmt.MessageTag.class);
    _jspx_th_fmt_005fmessage_005f0.setPageContext(_jspx_page_context);
    _jspx_th_fmt_005fmessage_005f0.setParent(null);
    // /log.jsp(210,25) name = key type = null reqTime = true required = false fragment = false deferredValue = false expectedTypeName = null deferredMethod = false methodSignature = null
    _jspx_th_fmt_005fmessage_005f0.setKey("log.line");
    int _jspx_eval_fmt_005fmessage_005f0 = _jspx_th_fmt_005fmessage_005f0.doStartTag();
    if (_jspx_th_fmt_005fmessage_005f0.doEndTag() == javax.servlet.jsp.tagext.Tag.SKIP_PAGE) {
      _005fjspx_005ftagPool_005ffmt_005fmessage_0026_005fkey_005fnobody.reuse(_jspx_th_fmt_005fmessage_005f0);
      return true;
    }
    _005fjspx_005ftagPool_005ffmt_005fmessage_0026_005fkey_005fnobody.reuse(_jspx_th_fmt_005fmessage_005f0);
    return false;
  }
}
