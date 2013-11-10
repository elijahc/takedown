var port
var pusher    = new Pusher('45401c0274262b3ea071')
var channel = pusher.subscribe('game')

chrome.runtime.onConnect.addListener(function(conn) {
  port = conn

  console.assert(port.name == "takedown");
  port.onMessage.addListener(function(msg) {
    console.log(msg)
    if (msg.init)
        port.postMessage({init: "polo"})



  });
});

channel.bind('update_battlefield', function(data) {
  console.log(data.battlefield);
  port.postMessage(data)
});

channel.bind('alert', function(data) {
  console.log(data);
  alert(data)
});
