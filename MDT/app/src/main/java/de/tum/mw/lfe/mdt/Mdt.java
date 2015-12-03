package de.tum.mw.lfe.mdt;

//------------------------------------------------------
//Revision History 'Mobile Detection Task (MDT)'
//------------------------------------------------------
//Version	Date			Author				Mod
//1			Jan, 2014		Michael Krause		initial
//1.1		May, 2014		Michael Krause		external button bugs(loop, downCount)
//1.2		June, 2014		Michael Krause		removed some bugs
//1.3		Aug, 2014		Michael Krause		rearranged layout + added log of hold time of ext. button
//1.4		Feb, 2015		Michael Krause		converted from eclipse to android studio
//1.5		Dec, 2015		Michael Krause		added NanoHttpd webserver
//------------------------------------------------------

/*
  Copyright (C) 2014  Michael Krause (krause@tum.de), Institute of Ergonomics, Technische Universität München
  
  This program is free software: you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation, either version 3 of the License, or
  (at your option) any later version.
  
  This program is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.
  
  You should have received a copy of the GNU General Public License
  along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */


import java.io.BufferedReader;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.net.Inet4Address;
import java.net.InetAddress;
import java.net.NetworkInterface;
import java.net.ServerSocket;
import java.net.Socket;
import java.net.URLDecoder;
import java.net.URLEncoder;
import java.nio.ByteBuffer;
import java.text.DecimalFormat;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Calendar;
import java.util.Date;
import java.util.Enumeration;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.TimeZone;

import android.media.AudioFormat;
import android.media.AudioManager;
import android.media.AudioRecord;
import android.media.AudioTrack;
import android.media.MediaRecorder;
import android.media.Ringtone;
import android.media.RingtoneManager;
import android.net.Uri;
import android.os.Bundle;
import android.os.Environment;
import android.os.Handler;
import android.os.Message;
import android.os.PowerManager;
import android.os.SystemClock;
import android.os.Vibrator;
import android.app.Activity;
import android.app.AlertDialog;
import android.content.BroadcastReceiver;
import android.content.Context;
import android.content.DialogInterface;
import android.content.Intent;
import android.content.IntentFilter;
import android.content.SharedPreferences;
import android.content.pm.ActivityInfo;
import android.content.res.Configuration;
import android.content.res.Resources;
import android.graphics.Color;
import android.graphics.ColorMatrixColorFilter;
import android.graphics.drawable.Drawable;
import android.text.Html;
import android.text.SpannableString;
import android.text.method.LinkMovementMethod;
import android.text.util.Linkify;
import android.util.AttributeSet;
import android.util.Log;
import android.view.KeyEvent;
import android.view.MotionEvent;
import android.view.View;
import android.view.ViewGroup;
import android.view.Window;
import android.view.WindowManager;
import android.widget.Button;
import android.widget.CheckBox;
import android.widget.RadioButton;
import android.widget.ScrollView;
import android.widget.SeekBar;
import android.widget.TextView;
import android.widget.Toast;

import fi.iki.elonen.NanoHTTPD;


public class Mdt extends Activity {
	
	private Button mResponseB;
	private Handler mHandler = new Handler();
	private Boolean mRunning = false; // MDT is running
	private Boolean mTactile = true;
	private Boolean mVisual = false;
	private Boolean mExternalButtonEnabled = false;
	private Boolean mExternalButtonClosed = false;
	private Boolean mLongPressAlarmEnabled = false;//long press alarm is enabled
	private int mLongPressAlarmCount = 0;//long press alarm was activated by a long press
	private byte mMarker = '-';//marker received via network	
	private Ringtone mRingtone;//ring tone for long press alarm	
	private Vibrator mVibrator;
	private Random   mRandom;
	private File     mFile=null;
	private int      mCount=0;
	private int      mButtonDownCount=0;//how often the touch & externalButton is pressed down
	private long     mOnset;
	private long     mNextOnset;
	private long     mOnsetDiff;
	private Boolean  mWaitingForResponse = false;
	private Boolean  mCalculateHoldTime = false;//flag between press and release to calculate holdtime
	private long     mHoldTime;//how long the user hold the button last time
	private ArrayList<Long> mResults = new ArrayList<Long>();//used to store all RTs and calculate avg

    private AlertDialog mAlert;

	private ServerRunnable mServerRunnable = null;
	private Thread mServerThread = null;
	private List<byte[]> mToSend = new ArrayList<byte[]>();
	public static final int PORT = 7007; // open this port
	public static final int PACKETSIZE = 46;//bytes in mToSend packets

	//private HeadsetButtonIntentReceiver mHeadsetButtonReceiver = new HeadsetButtonIntentReceiver(this); 

	private Mdt mContext = this;
	private PowerManager.WakeLock mWakeLock;
	
	private static final String TAG = "MDT.Activity";	
	public static final String CSV_DELIMITER = ";"; //delimiter within csv
	public static final String CSV_LINE_END = "\r\n"; //line end in csv
	public static final String FOLDER = "MDT"; //folder
	public static final String FOLDER_DATE_STR = "yyyy-MM-dd";//logging folder format
	public static final String FILE_EXT = ".txt";
	public static final String HEADER ="count;timestampStimulusOnset;diffToPlanedOnset;timestampNextOnset;rt;result;buttonDownCount;visual;tactile;longPressAlarmEnabled;longPressAlarmActivated;externalButton;holdTime;marker;";
	public static final int RANDOM_STIMULUS_MIN = 3000; //[ms] random stimulus onset is between MIN and MAX
	public static final int RANDOM_STIMULUS_MAX = 5000; //[ms]
	public static final int MAX_STIMULUS_DURATION = 1000; //[ms]
	public static final int MIN_RT = 100; //[ms] lower is a cheat/not possible
	public static final int MAX_RT = 2500; //[ms] higher is a miss
	public static final String CHEAT = "C"; // string for cheat in csv; or 'premature response' 
	public static final String HIT  = "H"; // string for hit in csv; or 'requested response'
	public static final String MISS = "M"; // string for miss in csv; or 'missing response'
										//note: repeated and unrequested responses are indirectly handled by just incrementing mButtonDownCount
	//enum results
	public static final byte B_CHEAT = 0; // enum byte for cheat in tcp packets
	public static final byte B_HIT = 1; // enum for hit in tcp packets
	public static final byte B_MISS = 2; // enum for miss in tcp packets
	public static final byte B_START = 3; // enum for start in tcp packets
	public static final byte B_STOP = 4; // enum for stop in tcp packets
	//enum packettypes
	public static final byte PACKET_TYPE_RT = 0;//reaction time
	public static final byte PACKET_TYPE_START = 1;
	public static final byte PACKET_TYPE_STOP = 2;

	public static final long NO_RESPONSE = -1; // value to identify no response

	public static final char START_SIGN = '#'; // send this sign on port to start
	public static final char STOP_SIGN = '$'; // send this sign on port to stop
	public static final byte START_CODE = 32; // send this code on port to start =SPACE
	public static final byte STOP_CODE = 27; // send this code on port to stop =ESC

	public static final char TACTILE_OFF_SIGN = 'M'; // send this sign to switch tactile off "mute" 
	public static final char TACTILE_ON_SIGN = 'T'; // send this sign to switch tactile on  "tactile"
	public static final char VISUAL_OFF_SIGN = 'H'; // send this sign to switch visual off  "hidden"
	public static final char VISUAL_ON_SIGN = 'V'; // send this sign to switch visual on  "visual"
	public static final char EXTERNAL_BUTTON_OFF_SIGN = 'I'; // send this sign to switch external button enabled off  "internal"
	public static final char EXTERNAL_BUTTON_ON_SIGN = 'E'; // send this sign to switch external button enabled on  "external"
	public static final char LONGPRESS_ALARM_OFF_SIGN = 'S'; // send this sign to switch long press alarm off  "silent"
	public static final char LONGPRESS_ALARM_ON_SIGN = 'L'; // send this sign to switch long press alarm on  "long press alarm"
	public static final int LONGPRESS_ALARM_MS = 1500; // long press alarm after [ms]. if user touches down button longer than this
	public static final byte[] MARKER = {'0','1','2','3','4','5','6','7','8','9'};
	
	public static final char NOT_CONNECTED = 0;
	public static final char CONNECTED = 1;
	public static final char UPDATE_MARKER_TEXT = 2;
	
	private static final String PREFERENCES = "mdtPreferences";

    private static final int OUT_SOUND_DURATION = 1; // [s]
    private static final int OUT_SAMPLE_RATE = 22050;
    private static final int OUT_SAMPLE_NUM = OUT_SOUND_DURATION  * OUT_SAMPLE_RATE;
    private short mOutSoundData[] = new short[OUT_SAMPLE_NUM];
    private static final int IN_SAMPLE_RATE = OUT_SAMPLE_RATE*2;
    private static final short IN_BUTTON_DEBOUNCE = 50;//milli sec for debouncing
    
    private static final boolean OPEN = false;// external button open
    private static final boolean CLOSED = true;// external button closed

    private AudioTrack mAudioTrack = null;
    private AudioRecord mAudioRecord = null;
    private AudioRecorderRunnable mAudioRecorderRunnable = null;
    private Thread mAudioRecorderThread = null;
    private int mRestoreVolume = 0;//the app stores the Music stream value onResume and restores the value onPause 

    public static final int WEB_PORT = 7070;//provide webserver gui on this port
    public static final int REFRESH = 2;//refresh every 2s
    private WebServer mWebserver;
	
	//-------------------------------------------------------------------
	final Handler mGuiHandler = new Handler(){
		  @Override
		  public void handleMessage(Message msg) {
			super.handleMessage(msg);
			    
			RadioButton connectedRB = (RadioButton)findViewById(R.id.connectedRB);

		    if(msg.what==NOT_CONNECTED){
				connectedRB.setChecked(false);
		    }
		    if(msg.what==CONNECTED){
				connectedRB.setChecked(true);
			}		    
		    if(msg.what==UPDATE_MARKER_TEXT){
		    	String temp = new String(Character.toChars(mMarker));//convert char to string
		    	connectedRB.setText(temp);
			}
		    

		  }
		};	
	//-------------------------------------------------------------------
	/*	
		public class HeadsetButtonIntentReceiver extends BroadcastReceiver {
			private Mdt mParent;
			
			public HeadsetButtonIntentReceiver(Mdt parent) {
			    super();
			    mParent = parent;
			}

			@Override
			public void onReceive(Context context, Intent intent) {
			    String intentAction = intent.getAction();
			    if (!Intent.ACTION_MEDIA_BUTTON.equals(intentAction)) {
			        return;
			    }
			    KeyEvent event = (KeyEvent)intent.getParcelableExtra(Intent.EXTRA_KEY_EVENT);
			    if (event == null) {
			        return;
			    }
			    int action = event.getAction();
			    int keycode = event.getKeyCode();
			    
			    if ((action == KeyEvent.ACTION_DOWN) && (event.getRepeatCount() == 0)) {
			    	long downTime = event.getDownTime();
			    	//tell parent we got response from head set button
			    	mParent.response(downTime, true);//true means from headsetButton
			    }
			    abortBroadcast();
			}
		}
	*/

    //-------------------------------------------------------------------
    private class WebServer extends NanoHTTPD {

        public WebServer() {
            super(WEB_PORT);
        }

        @Override
        public Response serve(String uri, Method method,
                              Map<String, String> header, Map<String, String> parameters,
                              Map<String, String> files) {

            Log.i(TAG, "WebServer():" + uri);

            String serverURL = "http://" + getIpAddress() + ":" + Integer.toString(WEB_PORT);

            if (uri.endsWith("listing")) {
                File folder = new File(getLoggingFolder());
                File[] dir1files = folder.listFiles();
                StringBuilder page = new StringBuilder(10000);//~10KByte
                page.append("<html><head><title>Mdt File Listing</title></head><body><a href=\"" + serverURL + "\">&lt;&lt;&lt;Control panel</a><hr/>");
                page.append("<br/>");
                page.append(getLoggingFolder());
                page.append("<br/>");
                page.append("<ul>");
                for (File file1 : dir1files) {
                    if (file1.isDirectory()) {
                        page.append("<li><b>");
                        page.append(file1.getName());
                        page.append("</b></li>");
                        page.append("<ul>");
                        File[] dir2files = file1.listFiles();
                        for (File file2 : dir2files) {
                            page.append("<li>");
                            String fname = "";
                            try {
                                fname = URLEncoder.encode(file2.getName(), "UTF-8");
                            } catch (Exception e) {
                                Log.e(TAG, "URLEncoder failed: " + e.getMessage());
                                fname = "";
                            }
                            page.append("<a href=\"" + serverURL + "/download?filename=" + fname + "\">" + fname + "</a>");
                            page.append("</li>");
                        }
                        page.append("</ul>");
                    } else {
                        page.append("<li>");
                        String fname = "";
                        try {
                            fname = URLEncoder.encode(file1.getName(), "UTF-8");
                        } catch (Exception e) {
                            Log.e(TAG, "URLEncoder failed: " + e.getMessage());
                            fname = "";
                        }
                        page.append("<a href=\"" + serverURL + "/download?filename=\"" + fname + "\">" + fname + "</a>");
                        page.append("</li>");
                    }

                }
                page.append("</ul>");
                page.append("</body></html>");
                return NanoHTTPD.newFixedLengthResponse(Response.Status.OK, NanoHTTPD.MIME_HTML, page.toString());
            }



            if ((uri.contains("download"))) {
                String filename = URLDecoder.decode(parameters.get("filename"));

                File folder = new File(getLoggingFolder());
                File[] dir1files = folder.listFiles();
                for (File file1 : dir1files) {
                    if (file1.isDirectory()) {
                        File[] dir2files = file1.listFiles();
                        for (File file2 : dir2files) {
                            if (file2.getName().equals(filename)) {
                                try{
                                    FileInputStream fis = new FileInputStream(file2);
                                    return newFixedLengthResponse(Response.Status.OK, MIME_PLAINTEXT, fis, file2.length());
                                } catch (Exception e) {
                                    Log.e(TAG, "send file failed: " + e.getMessage());
                                }
                            }
                        }
                    } else {
                        if (file1.getName().equals(filename)) {
                            //this should not happen; data files are always stored inside subfolders
                        }
                    }
                }

            }


            if (uri.contains("control")) {
                String command = parameters.get("command");
                if (command.equals("start")) {
                    startExp();
                }
                if (command.equals("stop")) {
                    stopExp();
                }
                if (command.equals("tactileOn")) {
                    mTactile= true;
                    refreshGui();
                }
                if (command.equals("tactileOff")) {
                    mTactile= false;
                    refreshGui();
                }
                if (command.equals("visualOn")) {
                    mVisual= true;
                    refreshGui();
                }
                if (command.equals("visualOff")) {
                    mVisual= false;
                    refreshGui();
                }
                if (command.equals("longpressOn")) {
                    mLongPressAlarmEnabled= true;
                    removeOrStopLongPressAlarm();
                    refreshGui();
                }
                if (command.equals("longpressOff")) {
                    mLongPressAlarmEnabled= false;
                    removeOrStopLongPressAlarm();
                    refreshGui();
                }
                if (command.equals("externalOn")) {
                    enableExternalButton();
                }
                if (command.equals("externalOff")) {
                    disableExternalButton();
                }

                if (command.equals("marker")) {
                    int parameter  = 48+Integer.parseInt(parameters.get("marker"));//48+x convert 1-9 to ascii code

                    for (int i=0; i < MARKER.length; i++){
                        if (parameter == MARKER[i]){
                            mMarker = MARKER[i];
                            Message msg2 = mGuiHandler.obtainMessage();
                            msg2.what = UPDATE_MARKER_TEXT;
                            mGuiHandler.sendMessage(msg2);

                        }
                    } //for

                }
            }

            if ((uri.contains("licence"))) {
                StringBuilder page = new StringBuilder(10000);//~10KByte
                page.append("*below the licence for the code part (NanoHttpd) that allowed a quick implementation of the web server: s\n");
                page.append("*********************************************\n");
                page.append("*NanoHttpd - Core\n");
                page.append("*%% \n");
                page.append("*Copyright(C) 2012 - 2015 nanohttpd \n");
                page.append("*%% \n");
                page.append("*Redistribution and use in source and binary forms, with or without modification, \n");
                page.append("*are permitted provided that the following conditions are met:\n");
                page.append("*\n");
                page.append("*1. Redistributions of source code must retain the above copyright notice, this\n");
                page.append("* list of conditions and the following disclaimer.\n");
                page.append("*\n");
                page.append("*2. Redistributions in binary form must reproduce the above copyright notice,\n");
                page.append("*this list of conditions and the following disclaimer in the documentation\n");
                page.append("*and / or other materials provided with the distribution.\n");
                page.append("*\n");
                page.append("*3. Neither the name of the nanohttpd nor the names of its contributors\n");
                page.append("*may be used to endorse or promote products derived from this software without\n");
                page.append("*specific prior written permission.\n");
                page.append("*\n");
                page.append("*THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS \"AS IS\" AND\n");
                page.append("*ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED\n");
                page.append("*WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED.\n");
                page.append("*IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT,\n");
                page.append("*INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,\n");
                page.append("*BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,\n");
                page.append("*DATA, OR PROFITS; OR BUSINESS INTERRUPTION)HOWEVER CAUSED AND ON ANY THEORY OF\n");
                page.append("*LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT(INCLUDING NEGLIGENCE\n");
                page.append("*OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED\n");
                page.append("*OF THE POSSIBILITY OF SUCH DAMAGE.\n");

                return NanoHTTPD.newFixedLengthResponse(Response.Status.OK, NanoHTTPD.MIME_PLAINTEXT, page.toString());

            }

            //default


            StringBuilder page = new StringBuilder(2048);

            page.append("<html><head><title>Occlusion Control</title><meta http-equiv=\"refresh\" content=\""+ Integer.toString(REFRESH)+"; URL=" + serverURL + "\"/></head><body>");
            page.append("<a href=\"" + serverURL + "/listing\">file listing</a><br/><a href=\"" + serverURL + "/licence\">NanoHttpd licence</a><hr/>");

            if (mRunning) {
                page.append("<br/>Experiment is running <a href=\"" + serverURL + "/control?command=stop\">[Stop]</a>");
            } else {
                page.append("<br/><a href=\"" + serverURL + "/control?command=start\">[Start Experiment]</a>");
            }

            if (mTactile) {
                page.append("<br/>Tactile is on : <a href=\"" + serverURL + "/control?command=tactileOff\">[switch off]</a>");
            } else {
                page.append("<br/><a href=\"" + serverURL + "/control?command=tactileOn\">[Tactile on]</a>");
            }

            if (mVisual) {
                page.append("<br/>Visual is on : <a href=\"" + serverURL + "/control?command=visualOff\">[switch off]</a>");
            } else {
                page.append("<br/><a href=\"" + serverURL + "/control?command=visualOn\">[Visual on]</a>");
            }

            if (mLongPressAlarmEnabled) {
                page.append("<br/>Longpress alarm is on : <a href=\"" + serverURL + "/control?command=longpressOff\">[switch off]</a>");
            } else {
                page.append("<br/><a href=\"" + serverURL + "/control?command=longpressOn\">[Longpress alarm on]</a></li>");
            }

            if (mExternalButtonEnabled) {
                page.append("<br/>External button enabled: <a href=\"" + serverURL + "/control?command=externalOff\">[switch off]</a>");
            } else {
                page.append("<br/><a href=\"" + serverURL + "/control?command=externalOn\">[Enable external button]</a>");
            }

            if (mCount > 0){
                page.append("<hr/>");
                page.append(getResultStat(true));
                page.append("<hr/>");
            }

            page.append("<br/>current experimental marker:"+(char)mMarker);


            page.append("<br/>set marker: ");
            page.append("<a href=\"" + serverURL + "/control?command=marker&marker=0\"> [ 0 ] </a>");
            page.append("<a href=\"" + serverURL + "/control?command=marker&marker=1\"> [ 1 ] </a>");
            page.append("<a href=\"" + serverURL + "/control?command=marker&marker=2\"> [ 2 ] </a>");
            page.append("<a href=\"" + serverURL + "/control?command=marker&marker=3\"> [ 3 ] </a>");
            page.append("<a href=\"" + serverURL + "/control?command=marker&marker=4\"> [ 4 ] </a>");
            page.append("<a href=\"" + serverURL + "/control?command=marker&marker=5\"> [ 5 ] </a>");
            page.append("<a href=\"" + serverURL + "/control?command=marker&marker=6\"> [ 6 ] </a>");
            page.append("<a href=\"" + serverURL + "/control?command=marker&marker=7\"> [ 7 ] </a>");
            page.append("<a href=\"" + serverURL + "/control?command=marker&marker=8\"> [ 8 ] </a>");
            page.append("<a href=\"" + serverURL + "/control?command=marker&marker=9\"> [ 9 ] </a>");
            page.append("</li>");
            page.append("</ul><br/>[updates every "+Integer.toString(REFRESH)+"s]</body></html>");

            return NanoHTTPD.newFixedLengthResponse(Response.Status.OK, NanoHTTPD.MIME_HTML, page.toString());

        }
    }
    //-------------------------------------------------------------------
    private void startWebServer(){
        mWebserver = new WebServer();
        try {
            mWebserver.start();
        } catch(Exception e) {
            Log.e(TAG, "Error while web starting:"+e.getMessage());
        }
        Log.i(TAG, "Web server started");
    }

    private void stopWebServer(){
        if (mWebserver != null) mWebserver.stop();
    }

    private String getLoggingFolder(){//helper
        return Environment.getExternalStorageDirectory () + File.separator + FOLDER + File.separator;
    }
    //-------------------------------------------------------------------
	
		
		
	    class ServerRunnable implements Runnable {
	    	private CommunicationThread commThread;
	    	private Thread thread;
	    	private ServerSocket mServerSocket;
	    	private Socket mClientSocket;
	    	
	    	public ServerRunnable(){
	            try {
	            	if (mServerSocket == null) mServerSocket = new ServerSocket(PORT);
	            } catch (Exception e) {
	            	Log.e(TAG,"ServerThread failed on open port: "+ e.getMessage());
	            }
	    	}
	 
	        public void run() {
	            
                while (!Thread.currentThread().isInterrupted()) {
	                try {
	                    Thread.sleep(1000);
	                    mClientSocket = mServerSocket.accept();
	                    commThread = new CommunicationThread(mClientSocket);
	                    thread = new Thread(commThread);
	                    thread.start();
	                } catch (Exception e) {
	                	if(!Thread.currentThread().isInterrupted()){//only log error if this was not an intentional interrupt
	                		Log.e(TAG,"ServerThread failed on accept connection: "+ e.getMessage());
	                	}	
	                }
                }//while
                
                closeSockets();
                
	        }//run

            public String ipStatus(){
                String tempStr = "";
                if((mServerSocket != null) && (mServerSocket.isBound()) ){
                    tempStr += getIpAddress() + ":"+PORT;
                }else{
                    tempStr += "-----";
                }
                return tempStr;
            }

	        //helpers
            public void closeSockets(){
                try{
                    if (mServerSocket != null) mServerSocket.close();
                    if (mClientSocket != null) mClientSocket.close();
                  } catch (Exception e) {
                	  Log.e(TAG,"ServerThread failed to close sockets: "+ e.getMessage());
                  }
            }

	    }


    //-------------------------------------------------------------------
    public String getIpAddress(){
        try {
            for (Enumeration<NetworkInterface> en = NetworkInterface.getNetworkInterfaces(); en.hasMoreElements();) {
                NetworkInterface intf = en.nextElement();
                for (Enumeration<InetAddress> enumIpAddr = intf.getInetAddresses(); enumIpAddr.hasMoreElements();) {
                    InetAddress inetAddress = enumIpAddr.nextElement();
                    if (!inetAddress.isLoopbackAddress() && inetAddress instanceof Inet4Address) {
                        return inetAddress.getHostAddress().toString();
                    }
                }
            }
        } catch (Exception e) {
            Log.e(TAG, "getIpAddress() failed: " + e.getMessage());
        }
        return "---";
    }
	//-------------------------------------------------------------------
	
		class CommunicationThread implements Runnable {

			private Socket clientSocket;
			private BufferedReader input;
			//private BufferedWriter output;
			private OutputStream output;

			
			public CommunicationThread(Socket clientSocket) {
				this.clientSocket = clientSocket;

				try {
					this.input = new BufferedReader(new InputStreamReader(this.clientSocket.getInputStream()));
					//this.output = new BufferedWriter(new OutputStreamWriter(this.clientSocket.getOutputStream()));
					this.output = this.clientSocket.getOutputStream();
				} catch (Exception e) {
	            	Log.e(TAG,"CommunicationThread failed on create streams: "+ e.getMessage());
				}
			}

			public void run() {
				
			    Message msg = mGuiHandler.obtainMessage();
			    msg.what = CONNECTED;
			    mGuiHandler.sendMessage(msg);

				int read;
				while ((!Thread.currentThread().isInterrupted()) && (!clientSocket.isClosed())) {
					
					SystemClock.sleep(1);//TODO adjust to your needs
					
					try {
						if(input.ready()){
							read = input.read();							
						}else{
							read =-1;
						}
						if (read != -1){							  
							
						       switch(read) {

					            case START_SIGN:
                                    startExp();
					                break;
					            case START_CODE:
                                    startExp();
					                break;
					            case STOP_SIGN:
					            	stopExp();
					                break;
					            case STOP_CODE:
					            	stopExp();
					                break;
					            case TACTILE_OFF_SIGN:
					            	mTactile= false;
					            	refreshGui();
					                break;
					            case TACTILE_ON_SIGN:
					            	mTactile= true; 
					            	refreshGui();
					                break;
					            case VISUAL_OFF_SIGN:
					            	mVisual= false; 
					            	refreshGui();
					                break;
					            case VISUAL_ON_SIGN:
					            	mVisual= true; 
					            	refreshGui();
					                break;
					            case LONGPRESS_ALARM_OFF_SIGN:
					            	mLongPressAlarmEnabled= false; 
					            	removeOrStopLongPressAlarm();
					            	refreshGui();
					                break;
					            case LONGPRESS_ALARM_ON_SIGN:
					            	mLongPressAlarmEnabled= true;
					            	refreshGui();
					                break;
					            case EXTERNAL_BUTTON_OFF_SIGN:
					            	disableExternalButton();
					                break;
					            case EXTERNAL_BUTTON_ON_SIGN:
					            	enableExternalButton();
					                break;
					            default:     
					            	break;
					            	
					        }//switch							

						  for (int i=0; i < MARKER.length; i++){
							 if (read == MARKER[i]){
								  mMarker = MARKER[i];
							      Message msg2 = mGuiHandler.obtainMessage();
							      msg2.what = UPDATE_MARKER_TEXT;
							      mGuiHandler.sendMessage(msg2);

							 }
						 } //for
						     
						}//if
						
						
												
						//output

						synchronized(mToSend){//sync against append and clear
							if(mToSend.size() > 0){
								Log.d(TAG,"Send");
								output.write(mToSend.get(0),0,PACKETSIZE);//send first in queue
								output.flush();
								mToSend.remove(0);//remove first from queue
								
							}
						}//sync
						
						
					} catch (Exception e) {
		            	Log.e(TAG,"CommunicationThread failed while input/output: "+ e.getMessage());
		            	Thread.currentThread().interrupt();
					}
					
				}//while
				try{	
					input.close();
					output.close();
				} catch (Exception e) {
	            	Log.e(TAG,"CommunicationThread failed on closing streams: "+ e.getMessage());
				}
			    Message msg2 = mGuiHandler.obtainMessage();
			    msg2.what = NOT_CONNECTED;
			    mGuiHandler.sendMessage(msg2);

			}//run

		}
	//-------------------------------------------------------------------
		   public class AudioRecorderRunnable implements Runnable {
		        private boolean endRecording = false;
		        private Mdt parent = null;
		        private long externalButtonLastPressed=0; 
		        private long externalButtonLastReleased=0;
		        private long avgAudioLevel=0;
		        private int musicVolume=0;
		        
		        public AudioRecorderRunnable(Mdt a){
		        	parent = a;
		        	
		        	try{
		    			AudioManager audioManager = (AudioManager)getSystemService(Context.AUDIO_SERVICE); 
		    			musicVolume = audioManager.getStreamMaxVolume(AudioManager.STREAM_MUSIC)/2;//set music volume to 50%
		        	}catch(Exception e){
		        		Log.e(TAG, "getStreamMaxVolume() failed: "+e.getMessage());
		        	}
		        	
                	setMusicVolume(musicVolume);

		        }
		        
		        public int getMusicVolume(){
		        	int vol = 0;
		        	try{
		    			AudioManager audioManager = (AudioManager)getSystemService(Context.AUDIO_SERVICE); 
		    	        vol = audioManager.getStreamVolume(AudioManager.STREAM_MUSIC);
		    	        
		        	}catch(Exception e){
		        		Log.e(TAG, "getMusicVolume() failed: "+e.getMessage());
		        	}
		        	return vol;

		        } 		        
		        
		        public void setMusicVolume(int vol){
		        	try{
		    			AudioManager audioManager = (AudioManager)getSystemService(Context.AUDIO_SERVICE); 
		    	        audioManager.setStreamVolume(AudioManager.STREAM_MUSIC, vol, 0);
		    	        
		        	}catch(Exception e){
		        		Log.e(TAG, "setMusicVolume() failed: "+e.getMessage());
		        	}

		        } 		        
		        
		        public int getAvgAudioLevel(){
		        	return (int)avgAudioLevel;
		        }
		        public void end(){
		        	endRecording = true;
		        }
		        
		        public void releaseRecorder(){
		            if (mAudioRecord != null) {
		                try {
		                	mAudioRecord.stop();
		                	mAudioRecord.release();

		                } catch (Exception e) {
		                    Log.e(TAG, "release mAudioRecord failed: "+e.getMessage());
		                }
		                mAudioRecord = null;
		            }
		        	
		        }
		    	
		        public void run() {
		            int minBufferSize;
		            short[] inSoundData;

		            try {
		                minBufferSize = AudioRecord.getMinBufferSize(IN_SAMPLE_RATE, AudioFormat.CHANNEL_CONFIGURATION_MONO, AudioFormat.ENCODING_PCM_16BIT);
		                mAudioRecord = new AudioRecord(MediaRecorder.AudioSource.MIC, IN_SAMPLE_RATE, AudioFormat.CHANNEL_CONFIGURATION_MONO, AudioFormat.ENCODING_PCM_16BIT, minBufferSize);
		                inSoundData = new short[minBufferSize];
		                mAudioRecord.startRecording();

		        		short[] previous_in_abs_temp = new short[4];
		        		
		                while (!endRecording) {
		                	int read = mAudioRecord.read(inSoundData, 0, inSoundData.length);
		                	long sum = 0;
		                	long count = 0;
		            		int avg_in_abs_temp;

		                	if (read > 0){//no error
		                		long now = SystemClock.uptimeMillis();
		                		//long now = Calendar.getInstance(TimeZone.getTimeZone("UTC")).getTimeInMillis(); 
		                		short in_abs_temp;

	            				int threshold_pressed = parent.getThreshold();
	            				int threshold_released = parent.getThreshold() -parent.getThreshold()/2;//we lower the released threshold by 50%, kind of hysteresis
	            				
		                		for (int i=0; i < read; i++){
		                			in_abs_temp = (short)Math.abs(inSoundData[i]);
		                			sum += in_abs_temp;//for visual bar
		                			previous_in_abs_temp[3] = previous_in_abs_temp[2];
		                			previous_in_abs_temp[2] = previous_in_abs_temp[1];
		                			previous_in_abs_temp[1] = previous_in_abs_temp[0];
		                			previous_in_abs_temp[0] = in_abs_temp;
		                			// do some weak averaging, if we captured the zero crossing
		                			avg_in_abs_temp = (previous_in_abs_temp[0] + previous_in_abs_temp[1] + previous_in_abs_temp[2] + previous_in_abs_temp[3])/4;
		                			
		            				//when the sample was taken:
		            				//  assumed reference is 'now' 
		            				//  the first sample was ('read'*1000)/ IN_SAMPLE_RATE  ago in time
		            				long timeOfThisSample = now - ((read-i)*1000/ IN_SAMPLE_RATE);
		            				
		            				
		                			if (avg_in_abs_temp > threshold_pressed){//button pressed
		                				count++;
		                				
		                				if ( (mExternalButtonClosed == OPEN) &&
			                					 ((timeOfThisSample - externalButtonLastPressed ) > IN_BUTTON_DEBOUNCE) &&
			                					 ((timeOfThisSample - externalButtonLastReleased) > IN_BUTTON_DEBOUNCE)){//DEBUGED in V1.1
		                						//button pressed EVENT
		                						externalButtonLastPressed = timeOfThisSample;
		                						mExternalButtonClosed = CLOSED;
		                						mCalculateHoldTime = true;//stop the time until release
		                						//Log.i(TAG,"button closed "+Long.toString(count) +" read:" +Integer.toString(read));
		                						parent.response(timeOfThisSample, true);//log as external button result
		                					
		                				}//else discard as 'bouncing'
		                			}	
		                   			if (avg_in_abs_temp < threshold_released){//button released
		                				
		                				if ( (mExternalButtonClosed == CLOSED) &&
		                					 ((timeOfThisSample - externalButtonLastPressed ) > IN_BUTTON_DEBOUNCE) && //DEBUGGED in V1.1
		                   					 ((timeOfThisSample - externalButtonLastReleased) > IN_BUTTON_DEBOUNCE)){//debounce
		                   						//button pressed EVENT
		                						externalButtonLastReleased = timeOfThisSample;
		                						mExternalButtonClosed = OPEN;
		                						if (mCalculateHoldTime){
		                							mCalculateHoldTime = false;
		                							mHoldTime = externalButtonLastReleased -externalButtonLastPressed;
		                						}
		                						//Log.i(TAG,"button open");
		                   						//parent.buttonReleased()
		                   					
		                   				}//else discard as 'bouncing'
		                				
		                			}
		                			
		                		}
		                		//Log.i(TAG, "audio level: "+Float.toString(sum/(float)read));
		                		avgAudioLevel = sum/read;
           						if(!parent.experimentIsRunning()) parent.refreshGui();//if experiment is not running refresh GUI
		                	}
		                	
		                	if (getMusicVolume() != musicVolume) setMusicVolume(musicVolume);
		                	
		                }//while
		                
		                releaseRecorder();

		            } catch (Exception e) {
		                Log.e(TAG, "audio recording runnable failed: "+e.getMessage());
		            }

		        }
		    } 
		   
	public void enableExternalButton(){
    	mExternalButtonEnabled= true;
    	refreshGui();
    	
        getMusicVolume();
        startSoundOut();
        startSoundInRec();	
	}	   
	public void disableExternalButton(){
    	mExternalButtonEnabled= false;
    	refreshGui();

        restoreMusicVolume();
        stopSoundOut();        
        stopSoundInRec();	
	}	   
		    

    
    void getMusicVolume(){//get music volume so we can restore later
    	try{
			AudioManager audioManager = (AudioManager)getSystemService(Context.AUDIO_SERVICE);
			mRestoreVolume = audioManager.getStreamVolume(AudioManager.STREAM_MUSIC);
    	}catch(Exception e){
    		Log.e(TAG, "getVolume() failed: "+e.getMessage());
    	}	
    }
    
    void restoreMusicVolume(){
    	try{
			AudioManager audioManager = (AudioManager)getSystemService(Context.AUDIO_SERVICE);
	        audioManager.setStreamVolume(AudioManager.STREAM_MUSIC, mRestoreVolume, 0);
    	}catch(Exception e){
    		Log.e(TAG, "restoreMusicVolume() failed: "+e.getMessage());
    	}	
    }
    
    private void startSoundInRec(){
        mAudioRecorderRunnable = new AudioRecorderRunnable(this);
        mAudioRecorderThread = new Thread(mAudioRecorderRunnable);
        mAudioRecorderThread.start();
        
    }	
    
    private void stopSoundInRec(){
        if (mAudioRecorderRunnable != null){
        	mAudioRecorderRunnable.end();
        	mAudioRecorderRunnable = null;
        }   	    
    }
    
    private void stopSoundOut(){
        if (mAudioTrack != null){
        	mAudioTrack.stop(); 
        	mAudioTrack.release();
        }
    }

    private void startSoundOut(){
    	
    	int n=0;//index
    	
        for (int i = 0; i < OUT_SAMPLE_NUM; ++i) {
        	if (i%2 == 0){//even
        		mOutSoundData[n++] = Short.MAX_VALUE;
        	}else{//odd
        		mOutSoundData[n++] = Short.MIN_VALUE;
        	}
        }
    	
        mAudioTrack = new AudioTrack(AudioManager.STREAM_MUSIC, OUT_SAMPLE_RATE, AudioFormat.CHANNEL_CONFIGURATION_MONO, AudioFormat.ENCODING_PCM_16BIT, mOutSoundData.length*2, AudioTrack.MODE_STATIC);
        mAudioTrack.write(mOutSoundData, 0, mOutSoundData.length);
        mAudioTrack.setLoopPoints(0, OUT_SAMPLE_NUM, -1);//first write() than setLoop()! some phones are picky. debugged in V1.1
        mAudioTrack.play();
        
        //ensure audioTrack volume is on
        float max = mAudioTrack.getMaxVolume();
        mAudioTrack.setStereoVolume(max, max);

    }		    	

	//-------------------------------------------------------------------
	
		
	private String getVersionString(){
		String retString = "";
		String appVersionName = "";
		int appVersionCode = 0;
		try{
			appVersionName = getPackageManager().getPackageInfo(getPackageName(), 0 ).versionName;
			appVersionCode= getPackageManager().getPackageInfo(getPackageName(), 0 ).versionCode;
		}catch (Exception e) {
			Log.e(TAG, "getVersionString failed: "+e.getMessage());
		 }
		
		retString = "V"+appVersionName+"."+appVersionCode;
		
		return retString;
	}	
	    
	
	private void removeOrStopLongPressAlarm(){
		try{
			 mHandler.removeCallbacks(longPressAlarm);
			 if (mRingtone != null) mRingtone.stop();
			}catch(Exception e){Log.e(TAG, "error remove/stop ring tone. message: "+e.getMessage());}

	}
		
		
    private Runnable longPressAlarm = new Runnable() {
		@Override
		public void run() {
			mLongPressAlarmCount++;
			try{
				  mRingtone.play();
				}catch(Exception e){Log.e(TAG, "error play long press alarm tone. message: "+e.getMessage());}
		} 			    	
    };	
	    
    private Runnable visualRed = new Runnable() {
		@Override
		public void run() {
			mResponseB.setBackgroundColor(Color.RED);
			//mResponseB.getDrawingTime();
			
		} 			    	
    };	
	
    private Runnable visualDefault = new Runnable() {
		@Override
		public void run() {
     		//mResponseB.setBackgroundResource(android.R.drawable.btn_default);		
			mResponseB.setBackgroundColor(Color.WHITE);
		} 			    	
    };	
	
    private Runnable stimulusOnset = new Runnable() {
        @Override
        public void run() {  	   
          if (mRunning){
        	  
        	  if (mWaitingForResponse){//if we are still waiting for a response for the last stimulus
        		  logging(NO_RESPONSE, mExternalButtonEnabled);//log it
        	  }
        	  
        	        		 
        	  if (mTactile){
	     		 mVibrator.vibrate(MAX_STIMULUS_DURATION);
	     	  }
        	  
     		 
        	  if (mVisual){
			     mResponseB.post(visualRed);
			     mResponseB.postDelayed(visualDefault,MAX_STIMULUS_DURATION);     		 
        	  }
     		 
   		      mOnset = Calendar.getInstance(TimeZone.getTimeZone("UTC")).getTimeInMillis();//now
   		      mOnsetDiff = mOnset - mNextOnset;// difference (whatHappened - plannedOnset) 
        	  long nextSoa = getNextSoa();
        	  //Log.i(TAG, "getNextSoa:" +Long.toString(nextSoa));
        	  mHandler.postDelayed(this, nextSoa);
   		      mNextOnset = mOnset + nextSoa;
        	  //Log.i(TAG, "mNextOnset:" +Long.toString(mNextOnset));
 	  
   		      mWaitingForResponse = true;
       		  mCount++;

          }	else{
        	  //end
        	  mResponseB.post(visualDefault);
        	  mHandler.removeCallbacks(this);
          }  
     };	
    };
    
    protected int getNextSoa(){
    	int ret = RANDOM_STIMULUS_MIN + mRandom.nextInt(RANDOM_STIMULUS_MAX -RANDOM_STIMULUS_MIN);//random value between MIN and MAX
    	return ret;
    }
    
    protected void getWakeLock(){
	    try{
			PowerManager powerManger = (PowerManager) getSystemService(Context.POWER_SERVICE);
	        mWakeLock = powerManger.newWakeLock(PowerManager.ACQUIRE_CAUSES_WAKEUP|PowerManager.FULL_WAKE_LOCK, "de.tum.ergonomie.mdt");
	        mWakeLock.acquire();
		}catch(Exception e){
        	Log.e(TAG,"get wakelock failed:"+ e.getMessage());
		}	
    }
    
	@Override
	protected void onCreate(Bundle savedInstanceState) {
		super.onCreate(savedInstanceState);
				

    	mRandom = new Random();
    	
    	
	    setRequestedOrientation(ActivityInfo.SCREEN_ORIENTATION_PORTRAIT);
        
        //no title
        requestWindowFeature(Window.FEATURE_NO_TITLE);
        //full screen
        getWindow().setFlags(WindowManager.LayoutParams.FLAG_FULLSCREEN,  WindowManager.LayoutParams.FLAG_FULLSCREEN);
		
        //full light
        android.provider.Settings.System.putInt(getContentResolver(), android.provider.Settings.System.SCREEN_BRIGHTNESS, 255); 
        /*
        WindowManager.LayoutParams layoutParams = getWindow().getAttributes();
        layoutParams.screenBrightness = WindowManager.LayoutParams.BRIGHTNESS_OVERRIDE_FULL;
        getWindow().setAttributes(layoutParams);        
 		*/
        
		setContentView(R.layout.activity_main);
	
		
		initResponseButton();
		        
		
		// Get instance of vibrator from current Context
		try{
		 mVibrator = (Vibrator) getSystemService(VIBRATOR_SERVICE);
		}catch(Exception e){
          error("failed to get vibrator: "+ e.getMessage());//toast error
		}		
	    

		//init headset response button
		/*
        IntentFilter filter = new IntentFilter(Intent.ACTION_MEDIA_BUTTON);
        filter.setPriority(10000);
        registerReceiver(mHeadsetButtonReceiver, filter);		
		*/
		
		//init touch response button
		initResponseButton();	
		
		startServer();//is also called in onResume, but needed for showHelp()
		
		showHelp();
		
		//load from preferences
        SharedPreferences settings = mContext.getSharedPreferences(PREFERENCES, Context.MODE_PRIVATE);
        mTactile = settings.getBoolean("mTactile", true);
        mVisual = settings.getBoolean("mVisual", false);
        mLongPressAlarmEnabled = settings.getBoolean("mLongPressAlarmEnabled", false);
        mExternalButtonEnabled = settings.getBoolean("mExternalButtonEnabled", false);
        int audioThreshold = settings.getInt("audioThreshold", Short.MAX_VALUE/4);
                
        CheckBox tactileC = (CheckBox)findViewById(R.id.tactileC);
        CheckBox visualC = (CheckBox)findViewById(R.id.visualC);
        CheckBox longpressC = (CheckBox)findViewById(R.id.longpressC);
   	   
	   	tactileC.setChecked(mTactile);
	   	visualC.setChecked(mVisual);
	   	longpressC.setChecked(mLongPressAlarmEnabled);
	   	
   	    TextView thresholdV = (TextView)findViewById(R.id.thresholdV);
   	    SeekBar thresholdSB = (SeekBar)findViewById(R.id.thresholdSB);
		thresholdSB.setMax(Short.MAX_VALUE);
		thresholdSB.setProgress(audioThreshold);
		thresholdSB.setProgressDrawable(getResources().getDrawable(R.drawable.audiothreshold));
		
	}

	public int getThreshold(){
		int ret = -1;
   	    SeekBar thresholdSB = (SeekBar)findViewById(R.id.thresholdSB);
   	    ret = thresholdSB.getProgress();
		return ret;
	}

	public void initResponseButton() {

		  mResponseB = (Button)findViewById(R.id.responseB);
		  String tempStr = "";
	      mResponseB.setText(tempStr);		

    	  mResponseB.post(visualDefault);


		mResponseB.setOnTouchListener(new View.OnTouchListener() {

				@Override
				public boolean onTouch(View v, MotionEvent event) {
					if (event.getAction() == MotionEvent.ACTION_DOWN ) {
						
						long downTime = event.getDownTime();
						response(downTime, false);//false means not the headsetButton

				    	//init ring tone for long press alarm
						if (mLongPressAlarmEnabled){
							try{
							  Uri notification = RingtoneManager.getDefaultUri(RingtoneManager.TYPE_RINGTONE);
							  mRingtone  = RingtoneManager.getRingtone(getApplicationContext(), notification);
						      mHandler.postDelayed(longPressAlarm, LONGPRESS_ALARM_MS);
							}catch(Exception e){Log.e(TAG, "error preparing long press alarm tone. message: "+e.getMessage());}
						}
						
						
	                    return true;
	                }
					
					if (event.getAction() == MotionEvent.ACTION_UP ) {
						removeOrStopLongPressAlarm();
	                    return true;
	                }
					
					return false;
				}
			   });			 
	    
	}	
	
	@Override
	public void onConfigurationChanged(Configuration newConfig) {
	    super.onConfigurationChanged(newConfig);
        //only portrait
	    setRequestedOrientation(ActivityInfo.SCREEN_ORIENTATION_PORTRAIT);
	    
	    
	}	

	

	public void	response(long downTime, boolean externalButton){//is called by button down on responseButton or externalButton down; downtime in uptime
		 mButtonDownCount++;
		 mVibrator.cancel();
		 mResponseB.post(visualDefault);
		 
		 if ((mWaitingForResponse) && (mRunning)){
			 long reference = Calendar.getInstance(TimeZone.getTimeZone("UTC")).getTimeInMillis() - SystemClock.uptimeMillis();
			 long rt = reference + downTime - mOnset;
			 logging(rt, externalButton);
			 
			 mWaitingForResponse = false; //we act only on first response
			 
		 }
		 
	}
	
	public byte Bool2Byte(Boolean bool){
		if (bool){
			return 1;
		}else{
			return 0;
		}
	}
	public void clearPacketsToSendQueue(){
		
		synchronized(mToSend){//sync against append and send
		   mToSend.clear();
		}//sync	


	}
	
	public void appendPacketToSend(byte packetType, long rt,  boolean externalButton){

		//int  count (4)
		//long onset (8)
		//(int cast)long onsetDiff (4)
		//long nextOnset (8)
		//(int cast)long rt (4)
		//byte result (1)
		//int buttonDownCount (4)
		//byte bool mode visual (1)
		//byte bool mode tactile (1)
		//byte bool mLongPressAlarmEnabled (1)
		//int mLongPressAlarmCount (4)
		//byte externalButton (1)
		//byte mMarker (1)
		//int mQueuedPackets (4)
		//-----------------
		//       => total 46 bytes => PACKETSIZE
		
		byte[] bytes = new byte[PACKETSIZE];
		ByteBuffer bytebuffer = ByteBuffer.wrap(bytes);
		//bytebuffer.order(ByteOrder.BIG_ENDIAN);
		bytebuffer.putInt(mCount);
		bytebuffer.putLong(mOnset);
		bytebuffer.putInt((int)mOnsetDiff);
		bytebuffer.putLong(mNextOnset);
		bytebuffer.putInt((int)rt);

		byte temp = -1;//error
		
		if (packetType == PACKET_TYPE_RT){
			temp = B_HIT;//hit
			 if (rt < MIN_RT){temp = B_CHEAT;}//cheat
			 if ((rt > MAX_RT)|| (rt == NO_RESPONSE)){temp = B_MISS;}//miss	
		}
		if (packetType == PACKET_TYPE_START){
			temp = B_START;
		}
		if (packetType == PACKET_TYPE_STOP){
			temp = B_STOP;
		}
		
		bytebuffer.put(temp);
		bytebuffer.putInt(mButtonDownCount);
		
		bytebuffer.put(Bool2Byte(mVisual));
		bytebuffer.put(Bool2Byte(mTactile));
		bytebuffer.put(Bool2Byte(mLongPressAlarmEnabled));
		
		bytebuffer.putInt(mLongPressAlarmCount);
		bytebuffer.put(Bool2Byte(externalButton));
		bytebuffer.put(mMarker);		
				
		synchronized(mToSend){//sync against send and clear
			
			bytebuffer.putInt(mToSend.size());//how many packets are quequed befoe this packet
			
			mToSend.add(bytes);//queque this packet
			
			Log.i(TAG,"queued packets: " +Integer.toString(mToSend.size()));
		}//sync	
	}
	
	public void writeToLoggingFile(long rt, boolean externalButton){
		 StringBuilder log = new StringBuilder(2048);
		 log.append(mCount);
		 log.append(CSV_DELIMITER);
		 log.append(mOnset);
		 log.append(CSV_DELIMITER);
		 log.append(mOnsetDiff);
		 log.append(CSV_DELIMITER);
		 log.append(mNextOnset);
		 log.append(CSV_DELIMITER);
		 if (rt != NO_RESPONSE){
			 log.append(rt);
		 }else{
			 log.append("");//in case of no reponse => ""
		 }
		 log.append(CSV_DELIMITER);
		 	 
		 
		 String temp = HIT;
		 if (rt < MIN_RT){temp = CHEAT;}
		 if ((rt > MAX_RT)|| (rt == NO_RESPONSE)){temp = MISS;}
		 log.append(temp);
		 log.append(CSV_DELIMITER);
		 log.append(mButtonDownCount);
		 log.append(CSV_DELIMITER);
		 log.append(mVisual);
		 log.append(CSV_DELIMITER);
		 log.append(mTactile);
		 log.append(CSV_DELIMITER);
		 log.append(mLongPressAlarmEnabled);
		 log.append(CSV_DELIMITER);
		 log.append(mLongPressAlarmCount);
		 log.append(CSV_DELIMITER);
		 log.append(externalButton);
		 log.append(CSV_DELIMITER);
		 log.append(mHoldTime);
		 log.append(CSV_DELIMITER);
		 log.append((char)mMarker);
		 log.append(CSV_DELIMITER);
		 log.append(CSV_LINE_END);
		 		 
		 
		   try{
			   String tempStr = log.toString();
			    byte[] bytes = tempStr.getBytes("US-ASCII");
				writeToFile(bytes,mFile);
			   }catch(Exception e){
				   error("error writing log data: "+e.getMessage());//toast
				   finish();//we quit. we will not continue without file logging
			   }		
	}
	
	public void logging(long rt, boolean externalButton){
		
				appendPacketToSend(PACKET_TYPE_RT, rt, externalButton);
				
				writeToLoggingFile(rt, externalButton);
				
				
			 //add RT to array, so we can later caluclate avg RT
			 mResults.add(rt);		   
		   
	}
	
	
	public void  toggleExternalButton(View v){//is called by click on enable external Bbtton check box
		mExternalButtonEnabled = !(mExternalButtonEnabled);
		if(mExternalButtonEnabled){
			enableExternalButton();
		}else{
			disableExternalButton();
		}
	}

	public void toggleTactile(View v){//is called by click on tactile check box
		mTactile = !(mTactile);
		refreshGui();
	}
	
	
	public void toggleVisual(View v){//is called by click on visual check box
		mVisual = !(mVisual);
		refreshGui();
	}
	public void toggleLongPressAlarm(View v){//is called by click on toggleLongPressAlarm check box
		mLongPressAlarmEnabled = !(mLongPressAlarmEnabled);
		refreshGui();
	}
	
	
	class refresh implements Runnable {

		@Override
		public void run() {
		   	   Button startB = (Button)findViewById(R.id.startB);
		   	   Button stopB = (Button)findViewById(R.id.stopB);
		   	   Button responseB = (Button)findViewById(R.id.responseB);
		   	   Button helpB = (Button)findViewById(R.id.helpB);
		   	   ScrollView scrollView = (ScrollView)findViewById(R.id.configScrollView);
		   	   
		   	   TextView resultV = (TextView)findViewById(R.id.resultV);
		   	   
		   	   CheckBox tactileC = (CheckBox)findViewById(R.id.tactileC);
		   	   CheckBox visualC = (CheckBox)findViewById(R.id.visualC);
		   	   CheckBox longpressC = (CheckBox)findViewById(R.id.longpressC);
		   	   CheckBox externalButtonC = (CheckBox)findViewById(R.id.externalC);
		   	   RadioButton externalButtonR = (RadioButton)findViewById(R.id.buttonClosedR);
		   	   
		   	   TextView thresholdV = (TextView)findViewById(R.id.thresholdV);
		   	   SeekBar thresholdSB = (SeekBar)findViewById(R.id.thresholdSB);
		   	   
			   	tactileC.setChecked(mTactile);
			   	visualC.setChecked(mVisual);
			   	longpressC.setChecked(mLongPressAlarmEnabled);
			   	externalButtonC.setChecked(mExternalButtonEnabled);
			   	externalButtonR.setChecked(mExternalButtonClosed);
		   		if (mRunning){
		   			scrollView.setVisibility(View.INVISIBLE);
		   			resultV.setVisibility(View.INVISIBLE);
		   			helpB.setVisibility(View.INVISIBLE);
				   	responseB.setText("Touch screen to respond");
		   		}else{
		   			scrollView.setVisibility(View.VISIBLE);
		   			resultV.setVisibility(View.VISIBLE);		   			
		   			helpB.setVisibility(View.VISIBLE);
		   			responseB.setText("");
		   			thresholdSB.setMax(Short.MAX_VALUE);
		   			if (mAudioRecorderRunnable != null) thresholdSB.setSecondaryProgress(mAudioRecorderRunnable.getAvgAudioLevel());//visualize audio level
		   			//show stats
			   	   if (mCount > 0){
			   			resultV.setText(getResultStat(false));
			   	   }
		   			
		   		}
		   		
		   	  // tactileC.setEnabled(!r);
		   	  // visualC.setEnabled(!r);
		   	   startB.setEnabled(!mRunning);
		   	   stopB.setEnabled(mRunning);
		   	   responseB.setEnabled(mRunning);						
		}
	}

    public String getResultStat(boolean html){//helper
        double avgRt = getAvgRt();
        double hitRate = getHitRate();
        DecimalFormat rateFormat = new DecimalFormat("##0");
        DecimalFormat rtFormat = new DecimalFormat("#000");
        StringBuilder temp = new StringBuilder(4096);
        temp.append("Average RT:");
        temp.append(rtFormat.format(avgRt));
        temp.append("ms");
        if (html){
            temp.append("<br/>");
        }else{
            temp.append("\r\n");
        }
        temp.append("Hit Rate:");
        temp.append(rateFormat.format(hitRate));
        temp.append("%");
        if (html){
            temp.append("<br/>");
        }else{
            temp.append("\r\n");
        }
        temp.append("Stimulus Count:");
        temp.append(Integer.toString(mCount));
        //temp.append("\r\nIP:Port: ");
        //temp.append(mServerRunnable.ipStatus());
        return temp.toString();
    }

	public void	refreshGui(){//refresh/set enabled statuses of buttons etc.
		mHandler.post(new refresh());
	}
	
	
	public void startExp(View v){//stub is called by click on startButton
        startExp();
	}
	
	
	public void	startExp(){//is called by click on startButton or external TCP command

        if (mAlert !=null){ mAlert.cancel(); }

		if (mRunning) {return;}//experiment already running so return, dont start multiple times!
		   
		   mRunning = true;
		   refreshGui();		   
		   
		   
		   mFile = prepareLogging();
		   try{
			String header = HEADER +  getVersionString() + "\r\n";
		    byte[] headerBytes = header.getBytes("US-ASCII");
			writeToFile(headerBytes,mFile);
		   }catch(Exception e){
			   error("error writing header: "+e.getMessage());//toast
			   finish();//we quit. we will not continue without file logging
		   }
		   
		   clearPacketsToSendQueue();//delete/comment this if queue should not be cleared at every start of an new experiment
		   
		   appendPacketToSend(PACKET_TYPE_START, 0, mExternalButtonEnabled);// send a tcp packet that signals we started

		   
		   mCount = 0;
		   mButtonDownCount = 0;
		   mLongPressAlarmCount = 0;
		   mHoldTime = 0;
		   
		   mWaitingForResponse = false;
		   mResults = new ArrayList<Long>();//reset result array

		   
		   long now = Calendar.getInstance(TimeZone.getTimeZone("UTC")).getTimeInMillis();//now
     	   long nextSoa = getNextSoa();
	       mHandler.postDelayed(stimulusOnset, nextSoa);   			   
		   mNextOnset = now + nextSoa;		   	   
	}		
	
	public void	stopExp(View v){//stub is called by click on stopButton;
		stopExp();
	}	
	
	public void	stopExp(){//is called by click on stopButton or external TCP command
		   mRunning = false;
	       mHandler.removeCallbacks(stimulusOnset);
	       appendPacketToSend(PACKET_TYPE_STOP, 0, mExternalButtonEnabled);// send a tcp packet that signals we stopped
		   refreshGui();
		   removeOrStopLongPressAlarm();		   		   
	}	
	
	public double getAvgRt(){
		double totalSum = 0;
		double avg = 0;
		long count=0;
		for (int i = 0; i < mResults.size(); i++){
			   if ((mResults.get(i) >= MIN_RT) && (mResults.get(i) <= MAX_RT) && (mResults.get(i) != NO_RESPONSE)){
				   totalSum += mResults.get(i);
				   count++;
			   }
		}
		if (count > 0){
			avg =  totalSum / (double)count; 
		}
		return avg;
	}
	
	public double getHitRate(){
		double hitRate = -1;
		int hitCount = 0;
		int missCount = 0;
		for (int i = 0; i < mResults.size(); i++){
			  //count hits
			   if ((mResults.get(i) >= MIN_RT) && (mResults.get(i) <= MAX_RT) && (mResults.get(i) != NO_RESPONSE)){
				   hitCount++;
			   }
			   //count misses
			   if ((mResults.get(i) == NO_RESPONSE) || (mResults.get(i) > MAX_RT)){
				   missCount++;
			   }			   
		}//for
		
		//calculate rate
		if ((hitCount + missCount) == 0){
			hitRate = 0;
		}else{
			hitRate = ((double)hitCount * 100.0 / (double)(hitCount + missCount));
		}
		return hitRate;
	}
	
	
	public File  prepareLogging(){
		File file = null;
		File folder = null;
		SimpleDateFormat  dateFormat = new SimpleDateFormat(FOLDER_DATE_STR);
		String folderTimeStr =  dateFormat.format(new Date());
		String timestamp = Long.toString(Calendar.getInstance(TimeZone.getTimeZone("UTC")).getTimeInMillis());
	   try{
		   //try to prepare external logging
           String folderStr = getLoggingFolder() + folderTimeStr;
		   file = new File(folderStr, timestamp + FILE_EXT);
		   folder = new File(folderStr);
		   folder.mkdirs();//create missing dirs
		   file.createNewFile();
		   if (!file.canWrite()) throw new Exception();
	   }catch(Exception e){
		   try{
	    	   error("maybe no SD card inserted");//toast
			   finish();//we quit. we will not continue without file logging

			   //we do not log to internal memory, its not so easy to get the files back, external is easier via usb mass storage
			   /*
			   //try to prepare internal logging
				File intfolder = getApplicationContext().getDir("data", Context.MODE_WORLD_WRITEABLE);
				String folderStr = intfolder.getAbsolutePath() + File.separator + folderTimeStr;
				toasting("logging internal to: " +folderStr, Toast.LENGTH_LONG);
				file = new File(folderStr, timestamp + FILE_EXT);
			    folder = new File(folderStr);
			    folder.mkdirs();//create missing dirs
				file.createNewFile();
				if (!file.canWrite()) throw new Exception();
				*/
		   }catch(Exception e2){
			   file= null;
	    	   error("exception during prepareLogging(): " + e2.getMessage());//toast
			   finish();//we quit. we will not continue without file logging
		   } 
		   
		  		   
		   
	   }
	   return file;
	}	

	public void writeToFile(byte[] data, File file){
   		       		
   		if (data == null){//error
       		error("writeFile() data==null?!");
       		finish();//we quit. we will not continue without file logging
   		}
   		
		FileOutputStream dest = null; 
							
		try {
			dest = new FileOutputStream(file, true);
			dest.write(data);
		}catch(Exception e){
			error("writeFile() failed. msg: " + e.getMessage());
       		finish();//we quit. we will not continue without file logging
			
		}finally {
			try{
				dest.flush();
				dest.close();
			}catch(Exception e){}
		}
		
		return;
   }	
	

	@Override
	public void onResume() {
        super.onResume();
        
        getWakeLock();
        
		startServer();//telnet

        startWebServer();//http

        
        if(mExternalButtonEnabled){
        	enableExternalButton();//turn on sound out, recording, etc.
        }
	}	

	
	@Override
	public void onPause() {
        super.onPause();
        
        if(mRunning){
        	stopExp();
        }
        if(mWakeLock != null){
        	mWakeLock.release();
        }
        
        saveToPrefs();//order important disableExternalButton() disables external button checkbox
        
        if(mExternalButtonEnabled){
        	disableExternalButton();//turn off recording, restore sound , etc.
        }
       
        
	}	
	
	public void startServer(){
		if (mServerRunnable == null){
			mServerRunnable	= new ServerRunnable();
		}
		if (mServerThread == null){
		    mServerThread = new Thread(mServerRunnable);
		    mServerThread.start();
		}
	}
	
	public void stopServer(){
        try {
        	mServerThread.interrupt();
        	mServerRunnable.closeSockets();
        } catch (Exception e) {
			Log.e(TAG, "mServerThread.interrupt() failed: " + e.getMessage());
        }
	}
	
	@Override
	public void onDestroy() {
        super.onDestroy();	
     
        //unregisterReceiver(mHeadsetButtonReceiver);
		
	}	
	
	/*
	 //override back button
	@Override
	public void onBackPressed() {
	}
	
	@Override
	public boolean onKeyDown(int keyCode, KeyEvent event) {
	     if (keyCode == KeyEvent.KEYCODE_BACK) {
	     //preventing default
	     return true;
	     }
	     return super.onKeyDown(keyCode, event);    
	}
	*/	
	
	    @Override
	    protected void onStop() {
	        super.onStop();
	        
	        stopServer();//telnet

            stopWebServer();//http
	    }	
	
	/*
	@Override
	public boolean onCreateOptionsMenu(Menu menu) {
		// Inflate the menu; this adds items to the action bar if it is present.
		getMenuInflater().inflate(R.menu.activity_main, menu);
		return true;
	}
	*/
	    
	    
	private void saveToPrefs(){
		//save changes to app preferences
	    SharedPreferences settings = getSharedPreferences(PREFERENCES, Context.MODE_PRIVATE);
	    SharedPreferences.Editor editor = settings.edit();
	    editor.putBoolean("mTactile", mTactile);
	    editor.putBoolean("mVisual", mVisual);
	    editor.putBoolean("mLongPressAlarmEnabled", mLongPressAlarmEnabled);
	    editor.putBoolean("mExternalButtonEnabled", mExternalButtonEnabled);
	    SeekBar thresholdSB = (SeekBar)findViewById(R.id.thresholdSB);
	    editor.putInt("audioThreshold", thresholdSB.getProgress());
	    editor.commit();	
		}

	private void toasting(final String msg, final int duration){
		Context context = getApplicationContext();
		CharSequence text = msg;
		Toast toast = Toast.makeText(context, text, duration);
		toast.show();		
	}
	
	public boolean experimentIsRunning(){
		return mRunning;
	}
	
	private void error(final String msg){//toast and log some errors
		toasting(msg, Toast.LENGTH_LONG);
		Log.e(TAG,msg);
	}
	public void showHelp(View v){// stub is called by click on helpButton
		showHelp();
	}
	public void showHelp(){
        StringBuilder help = new StringBuilder(2048);

        help.append("If you do experiments secure your network appropriately. You can use a web browser to connect to:"+getIpAddress()+ ":"+Integer.toString(WEB_PORT));
        help.append("<br/>or telnet to IP:Port: ");
        help.append(mServerRunnable.ipStatus());
        help.append("<br/>send e.g. via telnet:<br/>'"+ START_SIGN +"' / '"+ STOP_SIGN +"' to start/stop");
        help.append("<br/>'"+ TACTILE_ON_SIGN +"' / '"+ TACTILE_OFF_SIGN +"' tactile on/off");
        help.append("<br/>'"+ VISUAL_ON_SIGN +"' / '"+ VISUAL_OFF_SIGN +"' to switch visual on/off");
        help.append("<br/>'"+ LONGPRESS_ALARM_ON_SIGN +"' / '"+ LONGPRESS_ALARM_OFF_SIGN +"' long press alarm on/off");
        help.append("<br/>'"+ EXTERNAL_BUTTON_ON_SIGN +"' / '"+ EXTERNAL_BUTTON_OFF_SIGN +"' to enable/disable external button");
        help.append("<br/><br/>" + getVersionString() + " <a href=\"mailto:krause@tum.de\">krause@tum.de</a> 2014\nInstitute of Ergonomics, TUM.");
        help.append("<br/><br/>More information on MDT, etc. on <a href=\"http://www.lfe.mw.tum.de/en/mdt\">http://www.lfe.mw.tum.de/en/mdt</a>");
        help.append("<br/> This program is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more details.");

	      final SpannableString s = new SpannableString(Html.fromHtml(help.toString()));
	      Linkify.addLinks(s, Linkify.EMAIL_ADDRESSES|Linkify.WEB_URLS);
	      
	       mAlert = new AlertDialog.Builder(this)
	          .setMessage( s )
		      .setTitle("Mobile Detection Task (MDT)")
		      .setPositiveButton(android.R.string.ok,
		         new DialogInterface.OnClickListener() {
		         public void onClick(DialogInterface dialog, int whichButton){}
		         })
		      .show();
		   
		   ((TextView)mAlert.findViewById(android.R.id.message)).setMovementMethod(LinkMovementMethod.getInstance());
	
	}



}
