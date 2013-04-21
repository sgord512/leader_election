int leader = 0;
int finished = 0;
while(finished != 0) { 
    msg = receive();
    if(msg == 0) {
        finished = 1;
    } else {         
        if(msg == uid()) { 
            leader = msg;
            finished = 1;
            send(0, 0);
        } else { 
            if(msg > uid()) { 
                leader = msg;
                send(0, leader);
    }
 }
