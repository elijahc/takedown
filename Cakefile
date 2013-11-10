JAVASCRIPTS_PATH    = 'build/'
COFFEESCRIPTS_PATH  = 'src/'

task 'build', 'Build extension code into the directory build/', ->
    ps = spawn 'coffee', ["--output", JAVASCRIPTS_PATH, "--compile", COFFEESCRIPTS_PATH]
    ps.stdout.on('data', log)
    ps.stderr.on('data', log)
    ps.on 'exit', (code) ->
        if code != 0
            console.log 'failed'

task 'say:hello', 'Description', ->
    console.log 'Hello World'
