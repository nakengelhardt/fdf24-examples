module game_fsm #(
    parameter int GAME_MAP_WIDTH = 16,
    parameter int GAME_MAP_HEIGHT = 15,
    localparam int MAP_IDX_SIZE_X = $clog2(GAME_MAP_WIDTH+1),
    localparam int MAP_IDX_SIZE_Y = $clog2(GAME_MAP_HEIGHT+1),
    parameter logic [MAP_IDX_SIZE_X-1:0] START_POS_X = '0,
    parameter logic [MAP_IDX_SIZE_Y-1:0] START_POS_Y = '0,
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
    output logic show_pre_game_screen,
    output logic show_won_game_screen,
    output logic show_lost_game_screen,
    output logic [MAP_IDX_SIZE_X-1:0] player_pos_x,
    output logic [MAP_IDX_SIZE_Y-1:0] player_pos_y
);

    typedef enum logic [1:0] {
        PRE_GAME,
        GAME_RUNNING,
        GAME_WON,
        GAME_LOST
    } game_state_t;

    game_state_t game_state;
    game_state_t next_game_state;
    logic [MAP_IDX_SIZE_X-1:0] next_player_pos_x;
    logic [MAP_IDX_SIZE_Y-1:0] next_player_pos_y;
    logic position_ok;
    logic debug_active;
    logic [MAP_IDX_SIZE_X-1:0] debug_pos_x;
    logic [MAP_IDX_SIZE_Y-1:0] debug_pos_y;


    // Game FSM
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            game_state <= PRE_GAME;
            player_pos_x <= START_POS_X;
            player_pos_y <= START_POS_Y;
        end else begin
            game_state <= next_game_state;
            player_pos_x <= debug_active ? debug_pos_x : next_player_pos_x;
            player_pos_y <= debug_active ? debug_pos_y : next_player_pos_y;
        end
    end

    always_comb begin
        next_game_state = game_state;
        next_player_pos_x = player_pos_x;
        next_player_pos_y = player_pos_y;
        show_pre_game_screen = 1'b0;
        show_won_game_screen = 1'b0;
        show_lost_game_screen = 1'b0;
        case (game_state)
            PRE_GAME: begin
                next_player_pos_x = START_POS_X;
                next_player_pos_y = START_POS_Y;
                show_pre_game_screen = 1'b1;
                if (btn_start) next_game_state = GAME_RUNNING;
            end
            GAME_RUNNING: begin
                if (btn_up && player_pos_y < GAME_MAP_HEIGHT) next_player_pos_y = player_pos_y + 1'b1;
                else if (btn_down && player_pos_y > 0) next_player_pos_y = player_pos_y - 1'b1;
                else if (btn_left && player_pos_x > 0) next_player_pos_x = player_pos_x - 1'b1;
                else if (btn_right && player_pos_x < GAME_MAP_WIDTH) next_player_pos_x = player_pos_x + 1'b1;
               
                if (next_player_pos_x == WIN_POS_X && next_player_pos_y == WIN_POS_Y) begin
                    next_game_state = GAME_WON;
                end
                if (!position_ok) begin
                    next_game_state = GAME_LOST;
                end
            end
            GAME_WON: begin
                show_won_game_screen = 1'b1;
                if (btn_up || btn_down || btn_left || btn_right || btn_A || btn_B || btn_start) next_game_state = PRE_GAME;
            end
            GAME_LOST: begin
                show_lost_game_screen = 1'b1;
                if (btn_up || btn_down || btn_left || btn_right || btn_A || btn_B || btn_start) next_game_state = PRE_GAME;
            end
        endcase
    end

    // Are you winning, son?
    position_checker #(
        .GAME_MAP_WIDTH(GAME_MAP_WIDTH),
        .GAME_MAP_HEIGHT(GAME_MAP_HEIGHT)
    ) pos_checker (
        .x(next_player_pos_x),
        .y(next_player_pos_y),
        .btn_A(btn_A),
        .btn_B(btn_B),
        .position_ok(position_ok)
    );

    // For debugging
    debug_module #(
        .GAME_MAP_WIDTH(GAME_MAP_WIDTH),
        .GAME_MAP_HEIGHT(GAME_MAP_HEIGHT),
        .WIN_POS_X(GAME_MAP_WIDTH-1),
        .WIN_POS_Y(GAME_MAP_HEIGHT-1)
    ) debug_inst (
        .clk(clk),
        .reset(reset),
        .btn_up(btn_up),
        .btn_down(btn_down),
        .btn_left(btn_left),
        .btn_right(btn_right),
        .btn_A(btn_A),
        .btn_B(btn_B),
        .btn_start(btn_start),
        .debug_active(debug_active),
        .debug_pos_x(debug_pos_x),
        .debug_pos_y(debug_pos_y)
    );

    
    initial assume (reset);
    assume property (@(posedge clk) (btn_up + btn_down + btn_right + btn_left < 2));
    assume property (@(posedge clk) (btn_A + btn_B < 2));
    won: cover property (@(posedge clk) game_state == GAME_WON [*2]);
    restrict property (@(posedge clk) !debug_active);

endmodule
