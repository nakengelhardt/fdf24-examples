module fsm_tb ();

logic clk;
logic reset;
logic btn_up;
logic btn_down;
logic btn_left;
logic btn_right;
logic btn_A;
logic btn_B;
logic btn_start;
logic show_pre_game_screen;
logic show_won_game_screen;
logic show_lost_game_screen;
logic [MAP_IDX_SIZE_X-1:0] player_pos_x;
logic [MAP_IDX_SIZE_Y-1:0] player_pos_y;
logic write_enable;
logic [MAP_IDX_SIZE_X-1:0] write_x;
logic [MAP_IDX_SIZE_Y-1:0] write_y;
terrain_t write_data;
    
// Temporary storage for loading data from file
terrain_t map[0:GAME_MAP_HEIGHT-1][0:GAME_MAP_WIDTH-1];

game_fsm fsm_inst (.*);

// Load the map data from the file
initial begin
    $readmemb("map_data.mem", map);

    btn_up = 1'b0;
    btn_down = 1'b0;
    btn_left = 1'b0;
    btn_right = 1'b0;
    btn_A = 1'b0;
    btn_B = 1'b0;
    btn_start = 1'b0;
    write_enable = 1'b0;
    write_x = 0;
    write_y = 0;
    write_data = TERRAIN_NORMAL;
  
    $dumpfile("fsm_tb.vcd");
    $dumpvars(0, fsm_tb);

    clk = 1'b0;
    reset = 1'b1;

    #5;
    clk = 1'b1;
    #5;
    clk = 1'b0;
    write_enable = 1;
    for (int i = 0; i < GAME_MAP_HEIGHT; i++) begin
        for (int j = 0; j < GAME_MAP_WIDTH; j++) begin
            write_x = i;
            write_y = j;
            write_data = map[i][j];
            #5;
            clk = 1'b1;
            #5;
            clk = 1'b0;
        end
    end
    write_enable = 0;
    #5;
    clk = 1'b1;
    #5;
    clk = 1'b0;

    $finish;

end

endmodule
