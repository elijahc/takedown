chrome.runtime.onConnect.addListener(function(port) {
  console.assert(port.name == "knockknock");
  port.onMessage.addListener(function(msg) {
    if (msg.joke == "Knock knock")
      port.postMessage({question: "Who's there?"});
    else if (msg.answer == "Madame")
      port.postMessage({question: "Madame who?"});
    else if (msg.answer == "Madame... Bovary")
      port.postMessage({question: "I don't get it."});
  });
});
function runBrowser(){
    chrome.app.window.create('browser.html', {
        id: "window",
        bounds: {
            'width': 1024,
            'height': 768
        }
    });

};

function runTest(){
    // Center window on screen.
    var screenWidth = screen.availWidth;
    var screenHeight = screen.availHeight;
    var width = 800;
    var height = 600;


    chrome.app.window.create('index.html', {
        width: width,
        height: height,
        left: Math.round((screenWidth-width)/2),
        top: Math.round((screenHeight-height)/2)
    });

    var deck;
    var deckURL = 'http://tappedout.net/mtg-decks/rougejitsu/playtest.js'
    var xhr = new XMLHttpRequest();
    xhr.open('GET', deckURL, true);
    xhr.onreadystatechange = function(){
        console.log(xhr.responseText)
        deck = JSON.parse(xhr.responseText)
    };
    xhr.send();
    console.log(deck)
}
