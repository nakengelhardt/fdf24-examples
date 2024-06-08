module integration_test_debounce_fsm(
    input logic clk,
    input logic reset,
    input logic raw_btn_up,
    input logic raw_btn_down,
    input logic raw_btn_left,
    input logic raw_btn_right,
    input logic raw_btn_A,
    input logic raw_btn_B,
    input logic raw_btn_start,
    output logic show_pre_game_screen,
    output logic show_won_game_screen,
    output logic show_lost_game_screen,
    output logic [MAP_IDX_SIZE_X-1:0] player_pos_x,
    output logic [MAP_IDX_SIZE_Y-1:0] player_pos_y
);

// Internal signals for debounced buttons
logic btn_up, btn_down, btn_left, btn_right, btn_A, btn_B, btn_start;

game_fsm fsm_inst (.*);

debouncer #(
    .DEBOUNCE_DELAY(5)  // Small value for sim/formal to make trace length manageable
) debouncer_inst (.*);

endmodule

