
-- example script that demonstrates use of setup() to pass
-- a random server address to each thread


function setup(thread)
end

function init(args)
   local msg = "thread addr: %s"
   print(msg:format(wrk.thread.addr))
end

request = function() 
  wrk.headers["Connection"] = "Keep-Alive"
  param_num = math.random(0,4294967295 )
  param_value = string.format("0x%x" , param_num)
  path = "/?opcode=" .. param_value
  return wrk.format("GET", path)
end
