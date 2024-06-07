module debug_module #(
    parameter int GAME_MAP_WIDTH = 16,
    parameter int GAME_MAP_HEIGHT = 15,
    localparam int MAP_IDX_SIZE_X = $clog2(GAME_MAP_WIDTH+1),
    localparam int MAP_IDX_SIZE_Y = $clog2(GAME_MAP_HEIGHT+1),
    parameter logic [MAP_IDX_SIZE_X-1:0] WIN_POS_X = GAME_MAP_WIDTH-1,
    parameter logic [MAP_IDX_SIZE_Y-1:0] WIN_POS_Y = GAME_MAP_HEIGHT-1
)(
    input logic clk,
    input logic reset,
    input logic btn_up,
    input logic btn_down,
    input logic btn_left,
    input logic btn_right,
    input logic btn_A,
    input logic btn_B,
    input logic btn_start,
    output logic debug_active,
    output logic [MAP_IDX_SIZE_X-1:0] debug_pos_x,
    output logic [MAP_IDX_SIZE_Y-1:0] debug_pos_y
);
    localparam int HIST_LEN = 11;
    localparam int NUM_BTN = 7;

    logic [NUM_BTN*HIST_LEN-1:0] button_history;

    // Shift register to hold the last HIST_LEN button presses
    logic [NUM_BTN-1:0] current_button_state;
    assign current_button_state = {btn_up, btn_down, btn_left, btn_right, btn_A, btn_B, btn_start};

    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            button_history <= '0;
        end else begin
            button_history <= {button_history[NUM_BTN*(HIST_LEN-1)-1:0], current_button_state};
        end
    end

    // Check for Konami Code
    // Up, Up, Down, Down, Left, Right, Left, Right, B, A, Start
    logic konami_code_detected;
    localparam logic [NUM_BTN-1:0] UP    = {1'b1, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0};
    localparam logic [NUM_BTN-1:0] DOWN  = {1'b0, 1'b1, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0};
    localparam logic [NUM_BTN-1:0] LEFT  = {1'b0, 1'b0, 1'b1, 1'b0, 1'b0, 1'b0, 1'b0};
    localparam logic [NUM_BTN-1:0] RIGHT = {1'b0, 1'b0, 1'b0, 1'b1, 1'b0, 1'b0, 1'b0};
    localparam logic [NUM_BTN-1:0] A     = {1'b0, 1'b0, 1'b0, 1'b0, 1'b1, 1'b0, 1'b0};
    localparam logic [NUM_BTN-1:0] B     = {1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b1, 1'b0};
    localparam logic [NUM_BTN-1:0] START = {1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b1};
    localparam logic [NUM_BTN*HIST_LEN-1:0] KONAMI_CODE = {UP, UP, DOWN, DOWN, LEFT, RIGHT, LEFT, RIGHT, B, A, START};
    assign konami_code_detected = (button_history == KONAMI_CODE);

    // Debug outputs
    always_comb begin
        if (konami_code_detected) begin
            debug_active <= 1'b1;
            debug_pos_x <= WIN_POS_X;
            debug_pos_y <= WIN_POS_Y;
        end else begin
            debug_active <= 1'b0;
            debug_pos_x <= '0;
            debug_pos_y <= '0;
        end
    end

    // initial assume(reset);
    // cover property (@(posedge clk) debug_active);
endmodule
