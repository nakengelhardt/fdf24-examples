module cover_win_check (input logic clk, input logic reset, input game_state_t game_state, input logic debug_active);
    won: cover property (@(posedge clk) game_state == GAME_WON [*2]);
endmodule 
bind game_fsm cover_win_check cover_win_check_i(.*);
