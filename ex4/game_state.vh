localparam int GAME_MAP_WIDTH = 16;
localparam int GAME_MAP_HEIGHT = 15;
localparam int MAP_IDX_SIZE_X = $clog2(GAME_MAP_WIDTH+1);
localparam int MAP_IDX_SIZE_Y = $clog2(GAME_MAP_HEIGHT+1);

typedef enum logic [1:0] {
    PRE_GAME,
    GAME_RUNNING,
    GAME_WON,
    GAME_LOST
} game_state_t;
