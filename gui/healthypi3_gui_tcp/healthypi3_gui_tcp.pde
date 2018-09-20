//////////////////////////////////////////////////////////////////////////////////////////
//
//   Raspberry Pi/ Desktop GUI for controlling the HealthyPi HAT v3
//
//   Copyright (c) 2016 ProtoCentral
//   
//   This software is licensed under the MIT License(http://opensource.org/licenses/MIT). 
//   
//   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT 
//   NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. 
//   IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, 
//   WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE 
//   SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
//
/////////////////////////////////////////////////////////////////////////////////////////

import g4p_controls.*;                       // Processing GUI Library to create buttons, dropdown,etc.,
import processing.serial.*;                  // Serial Library
import grafica.*;

// Java Swing Package For prompting message
import java.awt.*;
import javax.swing.*;
import static javax.swing.JOptionPane.*;

// File Packages to record the data into a text file
import javax.swing.JFileChooser;
import java.io.FileWriter;
import java.io.BufferedWriter;
import java.io.BufferedReader;
import java.io.DataOutputStream;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;

// Http post requests
import java.net.URL;
import java.net.HttpURLConnection;
import javax.net.ssl.HttpsURLConnection;
import java.net.URLConnection;

// Date Format
import java.util.List;
import java.util.*;
import java.text.DateFormat;
import java.text.SimpleDateFormat;

// zip
import java.util.zip.ZipEntry;
import java.util.zip.ZipOutputStream;

// General Java Package
import java.math.*;
import controlP5.*;
import mqtt.*;
import org.eclipse.paho.client.mqttv3.MqttException;

MQTTClient client;
ControlP5 cp5;

String default_mqtt_server = "mqtt.noteart.app:1883";
String default_mqtt_username = "wisdomaic";
String default_mqtt_password = "happy2018";
int mqtt_post_interval=1000; //millisecond

Textlabel lblHR;
Textlabel lblSPO2;
Textlabel lblRR;
Textlabel lblBP;
Textlabel lblTemp;
Textlabel lblDeviceID;
Textlabel lblMQTT;
Textlabel lblMQTTStatus;

/************** Packet Validation  **********************/
private static final int CESState_Init = 0;
private static final int CESState_SOF1_Found = 1;
private static final int CESState_SOF2_Found = 2;
private static final int CESState_PktLen_Found = 3;

/*CES CMD IF Packet Format*/
private static final int CES_CMDIF_PKT_START_1 = 0x0A;
private static final int CES_CMDIF_PKT_START_2 = 0xFA;
private static final int CES_CMDIF_PKT_STOP = 0x0B;

/*CES CMD IF Packet Indices*/
private static final int CES_CMDIF_IND_LEN = 2;
private static final int CES_CMDIF_IND_LEN_MSB = 3;
private static final int CES_CMDIF_IND_PKTTYPE = 4;
private static int CES_CMDIF_PKT_OVERHEAD = 5;

/************** Packet Related Variables **********************/

int ecs_rx_state = 0;                                        // To check the state of the packet
int CES_Pkt_Len;                                             // To store the Packet Length Deatils
int CES_Pkt_Pos_Counter, CES_Data_Counter;                   // Packet and data counter
int CES_Pkt_PktType;                                         // To store the Packet Type
char CES_Pkt_Data_Counter[] = new char[1000];                // Buffer to store the data from the packet
char CES_Pkt_ECG_Counter[] = new char[4];                    // Buffer to hold ECG data
char CES_Pkt_Resp_Counter[] = new char[4];                   // Respiration Buffer
char CES_Pkt_SpO2_Counter_RED[] = new char[4];               // Buffer for SpO2 RED
char CES_Pkt_SpO2_Counter_IR[] = new char[4];                // Buffer for SpO2 IR
int pSize = 1000;                                            // Total Size of the buffer
int arrayIndex = 0;                                          // Increment Variable for the buffer
float time = 0;                                              // X axis increment variable

// Buffer for ecg,spo2,respiration,and average of thos values
float[] xdata = new float[pSize];
float[] ecgdata = new float[pSize];
float[] respdata = new float[pSize];
float[] bpmArray = new float[pSize];
float[] ecg_avg = new float[pSize];                          
float[] resp_avg = new float[pSize];
float[] spo2data = new float[pSize];
float[] spo2Array_IR = new float[pSize];
float[] spo2Array_RED = new float[pSize];
float[] rpmArray = new float[pSize];
float[] ppgArray = new float[pSize];

/************** Graph Related Variables **********************/

double maxe, mine, maxr, minr, maxs, mins;             // To Calculate the Minimum and Maximum of the Buffer
double ecg, resp, spo2_ir, spo2_red, spo2, redAvg, irAvg, ecgAvg, resAvg;  // To store the current ecg value
double respirationVoltage=20;                          // To store the current respiration value
boolean startPlot = false;                             // Conditional Variable to start and stop the plot

GPlot plotPPG;
GPlot plotECG;
GPlot plotResp;

int step = 0;
int stepsPerCycle = 100;
int lastStepTime = 0;
boolean clockwise = true;
float scale = 5;

/************** File Related Variables **********************/

static String ecgFileName = "";
static String ecgFilePath = "";
boolean logging = true;                                // Variable to check whether to record the data or not
FileWriter output;                                      // In-built writer class object to write the data to file
JFileChooser jFileChooser;                              // Helps to choose particular folder to save the file
Date date;                                              // Variables to record the date related values                              
BufferedWriter bufferedWriter;
DateFormat dateFormat;

/************** Port Related Variables **********************/

Serial port = null;                                     // Oject for communicating via serial port
String[] comList;                                       // Buffer that holds the serial ports that are paired to the laptop
char inString = '\0';                                   // To receive the bytes from the packet
String selectedPort;                                    // Holds the selected port number

/************** Logo Related Variables **********************/

PImage logo;
boolean gStatus;                                        // Boolean variable to save the grid visibility status

int nPoints1 = pSize;
int totalPlotsHeight=0;
int totalPlotsWidth=0;
int heightHeader=100;
int updateCounter=0;

boolean is_raspberrypi=false;

int global_hr;
int global_rr;
float global_temp;
int global_spo2;

int global_test=0;

boolean ECG_leadOff,spo2_leadOff;
boolean ShowWarning = true;
boolean ShowWarningSpo2=true;

boolean mqtt_on=false;
int mqtt_post_start_time=0;
int mqtt_post_stop_time=0;

int mqtt_hr=0;
int mqtt_rr=0;
int mqtt_spo2=0;
float mqtt_temp=0;

Accordion accordion;

String mqtt_server;
String mqtt_username;
String mqtt_password;

static String DEVICE_ID = "-----";

public void setup() 
{
  println(System.getProperty("os.name"));
  println(System.getProperty("os.arch"));
  
  GPointsArray pointsPPG = new GPointsArray(nPoints1);
  GPointsArray pointsECG = new GPointsArray(nPoints1);
  GPointsArray pointsResp = new GPointsArray(nPoints1);

  //size(1600, 800, JAVA2D);
  fullScreen();
   
  // ch
  heightHeader=100;
  println("Height:"+height);

  totalPlotsHeight=height-heightHeader;
  
  // device identifier
  DEVICE_ID = getCPUSerialUUID();
  
  // initialize bufferedWriter to store ECG data
  try {
    ecgFileName = String.valueOf(System.currentTimeMillis())+".csv";
    File csvFile = new File(ecgFileName); 
    ecgFilePath = csvFile.getCanonicalPath();
    println(ecgFilePath);
    date = new Date();
    output = new FileWriter(csvFile, true);
    bufferedWriter = new BufferedWriter(output);
    bufferedWriter.write(date.toString()+"");
    bufferedWriter.newLine();
    bufferedWriter.write("TimeStamp,ECG,SpO2,Respiration");
    bufferedWriter.newLine();
  }
  catch(Exception e)
  {
    e.printStackTrace();
  }
  
  // GUI
  makeGUI();
  
  plotECG = new GPlot(this);
  plotECG.setPos(0,50);
  plotECG.setDim(width, (totalPlotsHeight/3)-10);
  plotECG.setBgColor(0);
  plotECG.setBoxBgColor(0);
  plotECG.setLineColor(color(0, 255, 0));
  plotECG.setLineWidth(3);
  plotECG.setMar(0,0,0,0);
  
  plotPPG = new GPlot(this);
  plotPPG.setPos(0,(totalPlotsHeight/3+60));
  plotPPG.setDim(width, (totalPlotsHeight/3)-10);
  plotPPG.setBgColor(0);
  plotPPG.setBoxBgColor(0);
  plotPPG.setLineColor(color(255, 255, 0));
  plotPPG.setLineWidth(3);
  plotPPG.setMar(0,0,0,0);

  plotResp = new GPlot(this);
  plotResp.setPos(0,(totalPlotsHeight/3+totalPlotsHeight/3+70));
  plotResp.setDim(width, (totalPlotsHeight/3)-10);
  plotResp.setBgColor(0);
  plotResp.setBoxBgColor(0);
  plotResp.setLineColor(color(0,0,255));
  plotResp.setLineWidth(3);
  plotResp.setMar(0,0,0,0);

  for (int i = 0; i < nPoints1; i++) 
  {
    pointsPPG.add(i,0);
    pointsECG.add(i,0);
    pointsResp.add(i,0); 
  }

  plotECG.setPoints(pointsECG);
  plotPPG.setPoints(pointsPPG);
  plotResp.setPoints(pointsPPG);


  /*******  Initializing zero for buffer ****************/

  for (int i=0; i<pSize; i++) 
  {
    time = time + 1;
    xdata[i]=time;
    ecgdata[i] = 0;
    respdata[i] = 0;
    ppgArray[i] = 0;
  }
  time = 0;
  
  mqtt_post_start_time=0;
  mqtt_post_stop_time=1000;
  
  
  delay(2000);
  if(System.getProperty("os.arch").contains("arm"))
  {
    startSerial("/dev/ttyAMA0",57600);
  }
}

void setupMQTT() 
{
    mqtt_server = cp5.get(Textfield.class,"MQTT Server Name").getText();
    mqtt_username = cp5.get(Textfield.class,"MQTT username").getText();
    mqtt_password = cp5.get(Textfield.class,"MQTT password").getText();
      
    client = new MQTTClient(this);
    String mqtt_connect_string = "mqtt://"+ mqtt_username +":"+mqtt_password+"@"+mqtt_server;
    println(mqtt_connect_string);
    try 
    {
      client.connect(mqtt_connect_string, "processing");
      lblMQTTStatus.setText("Connected to:"+mqtt_server);
    } catch (Exception e)
    {
        lblMQTTStatus.setText("Failed to connect");
    }
}

void messageReceived(String topic, byte[] payload) 
{
  println("MQTT message recd: " + topic + " - " + new String(payload));
}

public void makeGUI()
{  
   cp5 = new ControlP5(this);
   cp5.addButton("关闭")
     .setValue(0)
     .setPosition(width-110,10)
     .setSize(100,40)
     .setFont(createFont("Impact",15))
     .addCallback(new CallbackListener() {
      public void controlEvent(CallbackEvent event) {
        if (event.getAction() == ControlP5.ACTION_RELEASE) 
        {
          CloseApp();
          //cp5.remove(event.getController().getName());
        }
      }
     } 
     );
  
   //cp5.addButton("Record")
   //  .setValue(0)
   //  .setPosition(width-225,10)
   //  .setSize(100,40)
   //  .setFont(createFont("Impact",15))
   //  .addCallback(new CallbackListener() {
   //   public void controlEvent(CallbackEvent event) {
   //     if (event.getAction() == ControlP5.ACTION_RELEASE) 
   //     {
   //       RecordData();
   //       //cp5.remove(event.getController().getName());
   //     }
   //   }
   //  } 
   //  );
     
     cp5.addButton("MQTT 开启/关闭")
     .setValue(0)
     .setPosition(width-330,10)
     .setSize(100,40)
     .setColorBackground(color(255,0,0))
     .setFont(createFont("Impact",15))
     .addCallback(new CallbackListener() {
      public void controlEvent(CallbackEvent event) {
        if (event.getAction() == ControlP5.ACTION_RELEASE) 
        {
            MQTT_ONOFF();
        }
      }
     } 
     );
    
    Group grpMQTTSettings = cp5.addGroup("MQTT设置")
                .setBackgroundColor(color(0,0,255))
                .setBarHeight(40)
                //.setSize(200,40)
                .setFont(createFont("Impact",15))
                .setBackgroundHeight(300)

                ;
        
          cp5.addTextfield("MQTT Server Name")
           .setPosition(10,5)
           .setSize(200,40)
           //.setFont(font)
           .setFont(createFont("Arial",15))
           .setFocus(true)
           .setColor(color(255,255,255))
           .setText(default_mqtt_server)
           .moveTo(grpMQTTSettings);
           
          cp5.addTextfield("MQTT username")
           .setPosition(10,70)
           .setSize(200,40)
           //.setFont(font)
           .setFont(createFont("Impact",15))
           .setFocus(true)
           .setColor(color(255,255,255))
           .setText(default_mqtt_username)
           .moveTo(grpMQTTSettings);
           
          cp5.addTextfield("MQTT password")
           .setPosition(10,140)
           .setSize(200,40)
           //.setFont(font)
           .setFont(createFont("Impact",15))
           .setFocus(true)
           .setColor(color(255,255,255))
           .setText(default_mqtt_password)
           .moveTo(grpMQTTSettings); 
           
         cp5.addTextfield("Feedname")
           .setPosition(10,210)
           .setSize(200,40)
           //.setFont(font)
           .setFont(createFont("Impact",15))
           .setFocus(true)
           .setColor(color(255,255,255))
           .moveTo(grpMQTTSettings); 
           
         cp5.addButton("Save")
           .setValue(0)
           .setPosition(110,255)
           .setSize(100,40)
           .setFont(createFont("Impact",15))
           .moveTo(grpMQTTSettings) 
           .addCallback(new CallbackListener() {
            public void controlEvent(CallbackEvent event) {
              if (event.getAction() == ControlP5.ACTION_RELEASE) 
              {
                accordion.close();
                //CloseApp();
                //cp5.remove(event.getController().getName());
              }
            }
           } 
           );
                 
    accordion = cp5.addAccordion("acc")
                 .setPosition(width-555,10)
                 .setWidth(220)
                 .setHeight(40)
                       
                 .addItem(grpMQTTSettings);
                 
  if(!System.getProperty("os.arch").contains("arm"))
  {     
      cp5.addScrollableList("选择串口")
         .setPosition(300, 10)
         .setSize(300, 100)
         .setFont(createFont("Impact",15))
         .setBarHeight(40)
         .setItemHeight(40)
         .addItems(Serial.list())
         .setType(ScrollableList.DROPDOWN) // currently supported DROPDOWN and LIST
         .addCallback(new CallbackListener() 
         {
            public void controlEvent(CallbackEvent event) 
            {
              if (event.getAction() == ControlP5.ACTION_RELEASE && 
                startPlot == false) 
              {
                startSerial(event.getController().getLabel(),115200);
              }
            }
         } 
       );     
    }
  

       lblHR = cp5.addTextlabel("lblHR")
      .setText("心率: --- bpm")
      .setPosition(width-550,50)
      .setColorValue(color(255,255,255))
      .setFont(createFont("Impact",40));

       lblSPO2 = cp5.addTextlabel("lblSPO2")
      .setText("血氧: --- %")
      .setPosition(width-550,(totalPlotsHeight/3+10))
      .setColorValue(color(255,255,255))
      .setFont(createFont("Impact",40));
 

      lblRR = cp5.addTextlabel("lblRR")
      .setText("呼吸: --- bpm")
      .setPosition(width-550,(totalPlotsHeight/3+totalPlotsHeight/3+10))
      .setColorValue(color(255,255,255))
      .setFont(createFont("Impact",40));
    
      lblTemp = cp5.addTextlabel("lblTemp")
      .setText("温度: --- C")
      //.setPosition((width/3)*2,height-80)
      .setPosition(width-550,height-80)
      .setColorValue(color(255,255,255))
      .setFont(createFont("Verdana",40));
      
      /*label for device indentifier*/
      lblDeviceID = cp5.addTextlabel("lblDeviceID")
      .setText("设备ID:" + DEVICE_ID)
      .setPosition((width/40)*1,height-80)
      .setColorValue(color(255,255,255))
      .setFont(createFont("Verdana",15));

      lblMQTT = cp5.addTextlabel("lblMQTT")
      .setText("MQTT OFF | ")
      .setPosition(5,height-25)
      .setColorValue(color(255,255,255))
      .setFont(createFont("Verdana",20));
      
      lblMQTTStatus = cp5.addTextlabel("lblMQTTStatus")
      .setText("Connected to: none")
      .setPosition(150,height-25)
      .setColorValue(color(255,255,255))
      .setFont(createFont("Verdana",20));
    
     //cp5.addButton("logo")
     //.setPosition(10,10)
     //.setImages(loadImage("protocentral.png"), loadImage("protocentral.png"), loadImage("protocentral.png"))
     //.updateSize();
     
      cp5.addButton("ECG上传")
         .setValue(0)
         .setPosition(10,10)
         .setSize(100,40)
         .setFont(createFont("Impact",15))
         .addCallback(new CallbackListener() {
            public void controlEvent(CallbackEvent event) {
              if (event.getAction() == ControlP5.ACTION_RELEASE) 
              {
                UploadData(ecgFilePath);
              }
            }
         });
          
    if(height<=480) //condition for Raspberry Pi 7" display
    {  
        lblHR.setFont(createFont("Arial",20));
        lblHR.setPosition(width-200,5+heightHeader);      
        
        lblSPO2.setFont(createFont("Arial",20));
        lblSPO2.setPosition(width-200,(totalPlotsHeight/3+heightHeader));
      
        lblTemp.setPosition((width/3)*2,height-25)
        .setFont(createFont("Verdana",20));
        
        lblRR.setPosition(width-200,(totalPlotsHeight/3+totalPlotsHeight/3+10+heightHeader))
        .setFont(createFont("Impact",20));
        
        lblMQTT.setPosition(5,height-25);
        lblMQTTStatus.setPosition(150,height-25);
        
        lblDeviceID
        .setPosition(5,height-50)
        .setFont(createFont("Verdana",15));
    }
}

void MQTT_ONOFF()
{
    if(false==mqtt_on)
    {
        mqtt_on=true;
        lblMQTT.setText("MQTT ON");
        setupMQTT();
    }
    else
    {
        mqtt_on=false;
        lblMQTT.setText("MQTT OFF");
    }
}

public void draw() 
{
  background(0);

  GPointsArray pointsPPG = new GPointsArray(nPoints1);
  GPointsArray pointsECG = new GPointsArray(nPoints1);
  GPointsArray pointsResp = new GPointsArray(nPoints1);

  if (startPlot)                             // If the condition is true, then the plotting is done
  {
    for(int i=0; i<nPoints1;i++)
    {    
      pointsECG.add(i,ecgdata[i]);
      pointsPPG.add(i,spo2data[i]); 
      pointsResp.add(i,respdata[i]);  
    }
  } 
  else                                     // Default value is set
  {
  }

  plotECG.setPoints(pointsECG);
  plotPPG.setPoints(pointsPPG);
  plotResp.setPoints(pointsResp);
  
  plotECG.beginDraw();
  plotECG.drawBackground();
  plotECG.drawLines();
  plotECG.endDraw();
  
  plotPPG.beginDraw();
  plotPPG.drawBackground();
  plotPPG.drawLines();
  plotPPG.endDraw();

  plotResp.beginDraw();
  plotResp.drawBackground();
  plotResp.drawLines();
  plotResp.endDraw();
}

public void CloseApp() 
{
  int dialogResult = JOptionPane.showConfirmDialog (null, "Would You Like to Close The Application?");
  if (dialogResult == JOptionPane.YES_OPTION) {
    try
    {
      //Runtime runtime = Runtime.getRuntime();
      //Process proc = runtime.exec("sudo shutdown -h now");
      System.exit(0);
    }
    catch(Exception e)
    {
      exit();
    }
  } else
  {
  }
}

/* upload data to remote server */
public void UploadData(String uploadFilePath)
{
  String requestURL = "https://www.beethoven.app/v1/storage/ECG";
  String auth = "c4bdc39825b64c56af79ed2199374652,1533838545274,4f5b2575b205e8a8231906318b0072cb";
  try {
    toZip(uploadFilePath);
  } catch(Exception e) {
    e.printStackTrace();
  }
  
  println(uploadFilePath);
  
  try {
    sendPost(requestURL, auth, uploadFilePath+".zip");
  } catch(Exception e) {
    e.printStackTrace();
  }
}


void startSerial(String startPortName, int baud)
{
  if (System.getProperty("os.name").equals("Mac OS X") == true && 
    System.getProperty("os.arch").equals("x86_64") == true && 
    startPortName.equals("/dev/tty.usbmodem1421") == false) {
      return;
  }
   
  try
  {
      port = new Serial(this,startPortName, baud);
      port.clear();
      startPlot = true;
  }
  catch(Exception e)
  {

    showMessageDialog(null, "Port is busy", "Alert", ERROR_MESSAGE);
    System.exit (0);
  }
}

void serialEvent (Serial blePort) 
{
  inString = blePort.readChar();
  ecsProcessData(inString);
}

void ecsProcessData(char rxch)
{
  switch(ecs_rx_state)
  {
  case CESState_Init:
    if (rxch==CES_CMDIF_PKT_START_1)
      ecs_rx_state=CESState_SOF1_Found;
    break;

  case CESState_SOF1_Found:
    if (rxch==CES_CMDIF_PKT_START_2)
      ecs_rx_state=CESState_SOF2_Found;
    else
      ecs_rx_state=CESState_Init;                    //Invalid Packet, reset state to init
    break;

  case CESState_SOF2_Found:
    //    println("inside 3");
    ecs_rx_state = CESState_PktLen_Found;
    CES_Pkt_Len = (int) rxch;
    CES_Pkt_Pos_Counter = CES_CMDIF_IND_LEN;
    CES_Data_Counter = 0;
    break;

  case CESState_PktLen_Found:
    //    println("inside 4");
    CES_Pkt_Pos_Counter++;
    if (CES_Pkt_Pos_Counter < CES_CMDIF_PKT_OVERHEAD)  //Read Header
    {
      if (CES_Pkt_Pos_Counter==CES_CMDIF_IND_LEN_MSB)
        CES_Pkt_Len = (int) ((rxch<<8)|CES_Pkt_Len);
      else if (CES_Pkt_Pos_Counter==CES_CMDIF_IND_PKTTYPE)
        CES_Pkt_PktType = (int) rxch;
    } else if ( (CES_Pkt_Pos_Counter >= CES_CMDIF_PKT_OVERHEAD) && (CES_Pkt_Pos_Counter < CES_CMDIF_PKT_OVERHEAD+CES_Pkt_Len+1) )  //Read Data
    {
      if (CES_Pkt_PktType == 2)
      {
        CES_Pkt_Data_Counter[CES_Data_Counter++] = (char) (rxch);          // Buffer that assigns the data separated from the packet
      }
    } else  //All  and data received
    {
      if (rxch==CES_CMDIF_PKT_STOP)
      {     
        CES_Pkt_ECG_Counter[0] = CES_Pkt_Data_Counter[0];
        CES_Pkt_ECG_Counter[1] = CES_Pkt_Data_Counter[1];


        CES_Pkt_Resp_Counter[0] = CES_Pkt_Data_Counter[2];
        CES_Pkt_Resp_Counter[1] = CES_Pkt_Data_Counter[3];

        CES_Pkt_SpO2_Counter_IR[0] = CES_Pkt_Data_Counter[4];
        CES_Pkt_SpO2_Counter_IR[1] = CES_Pkt_Data_Counter[5];
        CES_Pkt_SpO2_Counter_IR[2] = CES_Pkt_Data_Counter[6];
        CES_Pkt_SpO2_Counter_IR[3] = CES_Pkt_Data_Counter[7];

        CES_Pkt_SpO2_Counter_RED[0] = CES_Pkt_Data_Counter[8];
        CES_Pkt_SpO2_Counter_RED[1] = CES_Pkt_Data_Counter[9];
        CES_Pkt_SpO2_Counter_RED[2] = CES_Pkt_Data_Counter[10];
        CES_Pkt_SpO2_Counter_RED[3] = CES_Pkt_Data_Counter[11];

        float Temp_Value = (float) ((int) CES_Pkt_Data_Counter[12]| CES_Pkt_Data_Counter[13]<<8)/100;                // Temperature
        // BP Value Systolic and Diastolic
        
        int global_RespirationRate = (int) (CES_Pkt_Data_Counter[14]);
        int global_spo2= (int) (CES_Pkt_Data_Counter[15]);
        int global_HeartRate = (int) (CES_Pkt_Data_Counter[16]);
         
        int BP_Value_Sys = (int) CES_Pkt_Data_Counter[17];
        int BP_Value_Dia = (int) CES_Pkt_Data_Counter[18];
        
        int leadstatus =  CES_Pkt_Data_Counter[19];
        leadstatus &= 0x01; 
        if(leadstatus== 0x01) ECG_leadOff = true;  
        else ECG_leadOff = false;
        
        leadstatus =  CES_Pkt_Data_Counter[19];
        leadstatus &= 0x02; 
        if(leadstatus == 0x02) spo2_leadOff = true;
        else spo2_leadOff = false;
        

        int data1 = CES_Pkt_ECG_Counter[0] | CES_Pkt_ECG_Counter[1]<<8; //reversePacket(CES_Pkt_ECG_Counter, CES_Pkt_ECG_Counter.length-1);
        data1 <<= 16;
        data1 >>= 16;
        ecg = (double) data1/(Math.pow(10, 3));

        int data2 = CES_Pkt_Resp_Counter[0] | CES_Pkt_Resp_Counter[1] <<8; //reversePacket(CES_Pkt_ECG_Counter, CES_Pkt_ECG_Counter.length-1);
        data2 <<= 16;
        data2 >>= 16;
        resp = (double) data2/(Math.pow(10, 3));

        int data3 = reversePacket(CES_Pkt_SpO2_Counter_IR, CES_Pkt_SpO2_Counter_IR.length-1);
        spo2_ir = (double) data3;

        int data4 = reversePacket(CES_Pkt_SpO2_Counter_RED, CES_Pkt_SpO2_Counter_RED.length-1);
        spo2_red = (double) data4;

        ecg_avg[arrayIndex] = (float)ecg;
        ecgAvg = averageValue(ecg_avg);
        ecg = (ecg_avg[arrayIndex] - ecgAvg);

        spo2Array_IR[arrayIndex] = (float)spo2_ir;
        spo2Array_RED[arrayIndex] = (float)spo2_red;
        redAvg = averageValue(spo2Array_RED);
        irAvg = averageValue(spo2Array_IR);
        spo2 = (spo2Array_IR[arrayIndex] - irAvg);

        resp_avg[arrayIndex]= (float)resp;
        resAvg =  averageValue(resp_avg);
        resp = (resp_avg[arrayIndex] - resAvg);

        time = time+1;
        xdata[arrayIndex] = time;

        ecgdata[arrayIndex] = (float)ecg;
        respdata[arrayIndex]= (float)resp;
        spo2data[arrayIndex] = (float)spo2;
        bpmArray[arrayIndex] = (float)ecg;
        rpmArray[arrayIndex] = (float)resp;
        ppgArray[arrayIndex] = (float)spo2;

        if(ECG_leadOff == true)
        {
           if(ShowWarning == true)
           {
             lblHR.setColorValue(color(255,0,0));
             lblRR.setColorValue(color(255,0,0));
             lblHR.setText("LEAD ERROR");
             lblRR.setText("LEAD ERROR");
             ShowWarning = false;
           }
        }
        else 
        {
          if(ShowWarning == false)
          {
             lblHR.setColorValue(color(255,255,255));
             lblRR.setColorValue(color(255,255,255));
             ShowWarning = true;
          }
          global_rr = global_RespirationRate;
          lblRR.setText("呼吸: " + global_RespirationRate+ " rpm");
          global_hr = global_HeartRate;
          lblHR.setText("心率: " + global_HeartRate + " bpm");          
        }
        
        if(spo2_leadOff == true)
        {
          if(ShowWarningSpo2 == true)
           {
             lblSPO2.setColorValue(color(255,0,0));
             lblSPO2.setText("SpO2 Probe Error");
             ShowWarningSpo2 = false;
           }
        }
        else 
        {
           if(ShowWarningSpo2 == false)
            {
               lblSPO2.setColorValue(color(255,255,255));
               ShowWarningSpo2 = true;
            }
           lblSPO2.setText("血氧: " + global_spo2 + "%");
        }
       
        arrayIndex++;
        updateCounter++;

        if(updateCounter==100)
        {
          if (startPlot)
          {
            global_temp=Temp_Value;
            lblTemp.setText("温度: "+Temp_Value+" C");
            
          }
          updateCounter=0;
        }
        
        if (arrayIndex == pSize)
        {  
          arrayIndex = 0;
          time = 0;
        }       

        // If record button is clicked, then logging is done

        if(mqtt_on==true)
        {
          if(millis()-mqtt_post_stop_time >= mqtt_post_start_time)
          {
            mqtt_hr=global_hr;
            mqtt_rr=global_rr;
            mqtt_temp=global_temp;
            mqtt_spo2=global_spo2;
            
            thread("publishMQTT");
            mqtt_post_start_time=millis();
          }
          else
          {
            //mqtt_post_start_time
          }
        }
        
        if (logging == true)
        {
          try 
          {
            //date = new Date();
            //dateFormat = new SimpleDateFormat("HH:mm:ss");
            bufferedWriter.write(String.valueOf(System.currentTimeMillis())+","+ecg+","+spo2+","+resp);
            bufferedWriter.newLine();
          }
          catch(IOException e) 
          {
            println("It broke!!!");
            e.printStackTrace();
          }
        }
        ecs_rx_state=CESState_Init;
      } else
      {
        ecs_rx_state=CESState_Init;
      }
    }
    break;

  default:
    break;
  }
}

void publishMQTT()
{
    String jsonString = "{\"heartrate\":" + String.valueOf(mqtt_hr)  + "," + "\"resprate\":" + String.valueOf(mqtt_rr) + "," + "\"spo2\":" + String.valueOf(mqtt_spo2) + "," + "\"temperature\":" + String.valueOf(mqtt_temp) + " }";
    println(jsonString);
    client.publish("HealthPi", jsonString);
    //client.publish("MockRobot", jsonString);
   //client.publish(mqtt_username+"/feeds/healthypi.heartrate", ""+mqtt_hr);
   //client.publish(mqtt_username+"/feeds/healthypi.respiration", ""+mqtt_rr);
   //client.publish(mqtt_username+"/feeds/healthypi.spo2", ""+mqtt_spo2);
   //client.publish(mqtt_username+"/feeds/healthypi.temperature", ""+mqtt_temp);       
}

/*********************************************** Recursive Function To Reverse The data *********************************************************/

public int reversePacket(char DataRcvPacket[], int n)
{
  if (n == 0)
    return (int) DataRcvPacket[n]<<(n*8);
  else
    return (DataRcvPacket[n]<<(n*8))| reversePacket(DataRcvPacket, n-1);
}

/*************** Function to Calculate Average *********************/
double averageValue(float dataArray[])
{

  float total = 0;
  for (int i=0; i<dataArray.length; i++)
  {
    total = total + dataArray[i];
  }
  return total/dataArray.length;
}

/*************** Function to Calculate the Hardware UUID ***********/
public static String getCPUSerialUUID() {
    String result = "";  
    String cpuSerial = "";
    String CPU_ID_CMD = "";
    if(System.getProperty("os.arch").contains("arm")) {
      /* work for raspberry pi */
      CPU_ID_CMD = "cat /proc/cpuinfo | grep Serial | awk ' {print $3}'";
    } else {
      CPU_ID_CMD = "dmidecode -t 4 | grep ID |sort -u |awk -F': ' '{print $2}'";
    }
    Process p;  
    try {  
        p = Runtime.getRuntime().exec(new String[]{"sh","-c",CPU_ID_CMD});//The Conduit 
        BufferedReader br = new BufferedReader(new InputStreamReader(p.getInputStream()));  
        String line;  
        while ((line = br.readLine()) != null) {  
                result += line;  
                break;  
        }  
        br.close();  
    } catch (IOException e) {  
    }
    cpuSerial = result.trim();
    return UUID.nameUUIDFromBytes(cpuSerial.getBytes()).toString();  
}  

/******************* Fuction to compress a single file to zip format (on the same directory)******************/
public void toZip(String srcFilePath) throws Exception {
   try {
     
     File srcFile = new File(srcFilePath);
     String zipFilePath = srcFilePath + ".zip";
     // create byte buffer
     byte[] buffer = new byte[1024];
     
     FileOutputStream fos = new FileOutputStream(zipFilePath);
     ZipOutputStream zos = new ZipOutputStream(fos);

     FileInputStream fis = new FileInputStream(srcFile);
     // begin to write a new zip entry, postions the stream to the start of the entry data
     zos.putNextEntry(new ZipEntry(srcFile.getName()));
     
     int length;
     
     while ((length = fis.read(buffer)) > 0) {
       zos.write(buffer, 0 ,length);
     }
     
     zos.closeEntry();
     
     //close the InputStream
     fis.close();
     
     //close the ZipOutputStream
     zos.close();
     
   } catch (IOException ioe) {
     ioe.printStackTrace();
   }
}

/******************* Function to do HTTP POST Request***********************/
public void sendPost(String requestURL, String auth, String filePath) throws Exception {
  
  String charset = "UTF-8";
  File uploadFile = new File(filePath);
  try {
    MultipartUtility multipart = new MultipartUtility(requestURL, charset);
    
    //multipart.addHeaderField("User-Agent", "CodeJava");
    //multipart.addHeaderField("Test-Header", "Header-Value");
    
    multipart.addFormField("authentication", auth);
    multipart.addFormField("identifier", DEVICE_ID);
    
    multipart.addFilePart("fileUpload", uploadFile);

    List<String> response = multipart.finish();
    
    System.out.println("SERVER REPLIED:");
    
    for (String line : response) {
      System.out.println(line);
    }
    } catch (IOException ex) {
      System.err.println(ex);
    }
}

/**
 * This utility class provides an abstraction layer for sending multipart HTTP
 * POST requests to a web server. 
 * @author www.codejava.net
 *
 */
public class MultipartUtility {
  private final String boundary;
  private static final String LINE_FEED = "\r\n";
  private HttpsURLConnection httpConn;
  private String charset;
  private OutputStream outputStream;
  private PrintWriter writer;

  /**
   * This constructor initializes a new HTTP POST request with content type
   * is set to multipart/form-data
   * @param requestURL
   * @param charset
   * @throws IOException
   */
  public MultipartUtility(String requestURL, String charset)
      throws IOException {
    this.charset = charset;
    
    // creates a unique boundary based on time stamp
    boundary = "===" + System.currentTimeMillis() + "===";
    
    URL url = new URL(requestURL);
    httpConn = (HttpsURLConnection) url.openConnection();
    httpConn.setUseCaches(false);
    httpConn.setDoOutput(true);  // indicates POST method
    httpConn.setDoInput(true);
    httpConn.setRequestProperty("Content-Type",
        "multipart/form-data; boundary=" + boundary);
    // httpConn.setRequestProperty("User-Agent", "CodeJava Agent");
    // httpConn.setRequestProperty("Test", "Bonjour");
    outputStream = httpConn.getOutputStream();
    writer = new PrintWriter(new OutputStreamWriter(outputStream, charset),
        true);
  }

  /**
   * Adds a form field to the request
   * @param name field name
   * @param value field value
   */
  public void addFormField(String name, String value) {
    writer.append("--" + boundary).append(LINE_FEED);
    writer.append("Content-Disposition: form-data; name=\"" + name + "\"")
        .append(LINE_FEED);
    writer.append("Content-Type: text/plain; charset=" + charset).append(
        LINE_FEED);
    writer.append(LINE_FEED);
    writer.append(value).append(LINE_FEED);
    writer.flush();
  }

  /**
   * Adds a upload file section to the request 
   * @param fieldName name attribute in <input type="file" name="..." />
   * @param uploadFile a File to be uploaded 
   * @throws IOException
   */
  public void addFilePart(String fieldName, File uploadFile)
      throws IOException {
    String fileName = uploadFile.getName();
    writer.append("--" + boundary).append(LINE_FEED);
    writer.append(
        "Content-Disposition: form-data; name=\"" + fieldName
            + "\"; filename=\"" + fileName + "\"")
        .append(LINE_FEED);
    writer.append(
        "Content-Type: "
            + URLConnection.guessContentTypeFromName(fileName))
        .append(LINE_FEED);
    writer.append("Content-Transfer-Encoding: binary").append(LINE_FEED);
    writer.append(LINE_FEED);
    writer.flush();

    FileInputStream inputStream = new FileInputStream(uploadFile);
    byte[] buffer = new byte[4096];
    int bytesRead = -1;
    while ((bytesRead = inputStream.read(buffer)) != -1) {
      outputStream.write(buffer, 0, bytesRead);
    }
    outputStream.flush();
    inputStream.close();
    
    writer.append(LINE_FEED);
    writer.flush();    
  }

  /**
   * Adds a header field to the request.
   * @param name - name of the header field
   * @param value - value of the header field
   */
  public void addHeaderField(String name, String value) {
    writer.append(name + ": " + value).append(LINE_FEED);
    writer.flush();
  }
  
  /**
   * Completes the request and receives response from the server.
   * @return a list of Strings as response in case the server returned
   * status OK, otherwise an exception is thrown.
   * @throws IOException
   */
  public List<String> finish() throws IOException {
    List<String> response = new ArrayList<String>();

    writer.append(LINE_FEED).flush();
    writer.append("--" + boundary + "--").append(LINE_FEED);
    writer.close();

    // checks server's status code first
    int status = httpConn.getResponseCode();
    if (status == HttpsURLConnection.HTTP_OK) {
      BufferedReader reader = new BufferedReader(new InputStreamReader(
          httpConn.getInputStream()));
      String line = null;
      while ((line = reader.readLine()) != null) {
        response.add(line);
      }
      reader.close();
      httpConn.disconnect();
    } else {
      throw new IOException("Server returned non-OK status: " + status);
    }

    return response;
  }
}
