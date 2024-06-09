module global_assumes (input clk, input reset);
    initial assume (reset);
endmodule
bind game_fsm global_assumes global_assumes_i(.*);
