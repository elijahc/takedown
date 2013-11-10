var port = chrome.runtime.connect({name: "takedown"});
port.postMessage({init: "marco"})
port.onMessage.addListener(function(msg) {
    console.log(msg)
    if (msg.battlefield)
        $('#opponent_battlefield').html(msg.battlefield)
});

$('#stage').prepend("<div id='opponent_battlefield' class='zone' style='display: none; top: 60px; bottom:230px;'></div>")
$('#next_turn').clone().attr('id', 'attack').addClass('no_rounded_right').removeClass('no_rounded_left').html('Attack').insertAfter('#next_turn')

$('#mulligan').clone().attr('id', 'view').removeClass('no_rounded_right').addClass('solid').html('You').insertAfter('#restart')
$('#help_link_wrapper').clone().attr('id', 'game_select').first().html('<a>Join a Game</a>').insertAfter('#help_link_wrapper')

$('#view').on('click', function(){
    var you = $('#battlefield').toggle()
    var him = $('#opponent_battlefield').toggle()

    you.attr('id', 'opponent_battlefield')
    him.attr('id', 'battlefield')
    $('#view').toggleClass('solid')
});

$('#battlefield').on("DOMSubtreeModified", function(event){
    if ($(event.target).attr('id') == 'battlefield'){
        port.postMessage({ event: 'battlefield_changed', battlefield: $('#battlefield').html() });
    }
});
