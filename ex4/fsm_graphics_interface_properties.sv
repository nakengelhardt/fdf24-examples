module fsm_graphics_interface_properties #( 
    parameter ASSUME_MODE = 1
) (
    input logic clk,
    input logic reset,
    input logic show_pre_game_screen,
    input logic show_won_game_screen,
    input logic show_lost_game_screen,
    input logic [MAP_IDX_SIZE_X-1:0] player_pos_x,
    input logic [MAP_IDX_SIZE_Y-1:0] player_pos_y
);
    
    property one_screen;
        @(posedge clk) (show_pre_game_screen + show_won_game_screen + show_lost_game_screen < 2);
    endproperty

    generate if (ASSUME_MODE) begin
            assume property (one_screen);
    end else begin
            p_one_screen: assert property (one_screen);
    end
    endgenerate

endmodule

