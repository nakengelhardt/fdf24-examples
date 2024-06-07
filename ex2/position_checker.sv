
module position_checker #(
    parameter int GAME_MAP_WIDTH = 16,
    parameter int GAME_MAP_HEIGHT = 15,
    parameter string MAP_FILE = "map_data.mem"
)(
    input logic [$clog2(GAME_MAP_WIDTH+1)-1:0] x,
    input logic [$clog2(GAME_MAP_HEIGHT+1)-1:0] y,
    input logic btn_A,
    input logic btn_B,
    output logic position_ok
);

    // Enum for terrain types
    typedef enum logic [1:0] {
        TERRAIN_NORMAL   = 2'b00,
        TERRAIN_WATER    = 2'b01,
        TERRAIN_GAS      = 2'b10,
        TERRAIN_LAVA     = 2'b11
    } terrain_t;

    // ROM to store map data
    terrain_t map_rom[0:GAME_MAP_WIDTH-1][0:GAME_MAP_HEIGHT-1];

    // Load the map data from the file
    initial begin
        $readmemb(MAP_FILE, map_rom);
    end

    terrain_t terrain_value;

    always_comb begin
        position_ok = 1'b0;
        terrain_value = map_rom[x][y];

        // Determine if the position is okay based on terrain type and buttons pressed
        case (terrain_value)
            TERRAIN_NORMAL: position_ok = 1'b1;
            TERRAIN_WATER:  position_ok = btn_A ? 1'b1 : 1'b0;
            TERRAIN_GAS:    position_ok = btn_B ? 1'b1 : 1'b0;
            TERRAIN_LAVA:   position_ok = 1'b0;
        endcase
    end

endmodule
