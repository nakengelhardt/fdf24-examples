
module position_checker (
    input clk,
    input reset,
    input logic [MAP_IDX_SIZE_X-1:0] x,
    input logic [MAP_IDX_SIZE_Y-1:0] y,
    input logic btn_A,
    input logic btn_B,
    input logic write_enable,
    input logic [MAP_IDX_SIZE_X-1:0] write_x,
    input logic [MAP_IDX_SIZE_Y-1:0] write_y,
    input terrain_t write_data,
    output logic position_ok
);

    terrain_t map_ram[0:GAME_MAP_WIDTH-1][0:GAME_MAP_HEIGHT-1];

    always_ff @(posedge clk) begin
        if (write_enable)
            map_ram[write_x][write_y] <= write_data;
    end

    terrain_t terrain_value;

    always_comb begin
        position_ok = 1'b0;
        terrain_value = map_ram[x][y];

        // Determine if the position is okay based on terrain type and buttons pressed
        case (terrain_value)
            TERRAIN_NORMAL: position_ok = 1'b1;
            TERRAIN_WATER:  position_ok = btn_A ? 1'b1 : 1'b0;
            TERRAIN_GAS:    position_ok = btn_B ? 1'b1 : 1'b0;
            TERRAIN_LAVA:   position_ok = 1'b0;
        endcase
    end

endmodule
