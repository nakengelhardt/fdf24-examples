module debouncer #(
    parameter int DEBOUNCE_DELAY = 1000000  // Adjust as needed
)(
    input logic clk,
    input logic reset,
    input logic raw_btn_up,
    input logic raw_btn_down,
    input logic raw_btn_left,
    input logic raw_btn_right,
    input logic raw_btn_A,
    input logic raw_btn_B,
    input logic raw_btn_start,
    output logic btn_up,
    output logic btn_down,
    output logic btn_left,
    output logic btn_right,
    output logic btn_A,
    output logic btn_B,
    output logic btn_start
);

    // Internal signals for debounced states
    logic debounced_btn_up, debounced_btn_down, debounced_btn_left, debounced_btn_right;
    logic debounced_btn_A, debounced_btn_B, debounced_btn_start;

    // Debounce counters and states
    logic [31:0] counter_up, counter_down, counter_left, counter_right;
    logic [31:0] counter_A, counter_B, counter_start;
    logic btn_up_state, btn_down_state, btn_left_state, btn_right_state;
    logic btn_A_state, btn_B_state, btn_start_state;

    // Debounce process for each button
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            counter_up <= 0;
            counter_down <= 0;
            counter_left <= 0;
            counter_right <= 0;
            counter_A <= 0;
            counter_B <= 0;
            counter_start <= 0;
            debounced_btn_up <= 0;
            debounced_btn_down <= 0;
            debounced_btn_left <= 0;
            debounced_btn_right <= 0;
            debounced_btn_A <= 0;
            debounced_btn_B <= 0;
            debounced_btn_start <= 0;
        end else begin
            // Debouncing logic for each button
            if (raw_btn_up == btn_up_state) begin
                counter_up <= 0;
            end else if (counter_up == DEBOUNCE_DELAY) begin
                counter_up <= 0;
                btn_up_state <= raw_btn_up;
                debounced_btn_up <= raw_btn_up;
            end else begin
                counter_up <= counter_up + 1;
            end

            if (raw_btn_down == btn_down_state) begin
                counter_down <= 0;
            end else if (counter_down == DEBOUNCE_DELAY) begin
                counter_down <= 0;
                btn_down_state <= raw_btn_down;
                debounced_btn_down <= raw_btn_down;
            end else begin
                counter_down <= counter_down + 1;
            end

            if (raw_btn_left == btn_left_state) begin
                counter_left <= 0;
            end else if (counter_left == DEBOUNCE_DELAY) begin
                counter_left <= 0;
                btn_left_state <= raw_btn_left;
                debounced_btn_left <= raw_btn_left;
            end else begin
                counter_left <= counter_left + 1;
            end

            if (raw_btn_right == btn_right_state) begin
                counter_right <= 0;
            end else if (counter_right == DEBOUNCE_DELAY) begin
                counter_right <= 0;
                btn_right_state <= raw_btn_right;
                debounced_btn_right <= raw_btn_right;
            end else begin
                counter_right <= counter_right + 1;
            end

            if (raw_btn_A == btn_A_state) begin
                counter_A <= 0;
            end else if (counter_A == DEBOUNCE_DELAY) begin
                counter_A <= 0;
                btn_A_state <= raw_btn_A;
                debounced_btn_A <= raw_btn_A;
            end else begin
                counter_A <= counter_A + 1;
            end

            if (raw_btn_B == btn_B_state) begin
                counter_B <= 0;
            end else if (counter_B == DEBOUNCE_DELAY) begin
                counter_B <= 0;
                btn_B_state <= raw_btn_B;
                debounced_btn_B <= raw_btn_B;
            end else begin
                counter_B <= counter_B + 1;
            end

            if (raw_btn_start == btn_start_state) begin
                counter_start <= 0;
            end else if (counter_start == DEBOUNCE_DELAY) begin
                counter_start <= 0;
                btn_start_state <= raw_btn_start;
                debounced_btn_start <= raw_btn_start;
            end else begin
                counter_start <= counter_start + 1;
            end
        end
    end

    // Generate single active cycle signals
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            btn_up <= 0;
            btn_down <= 0;
            btn_left <= 0;
            btn_right <= 0;
            btn_A <= 0;
            btn_B <= 0;
            btn_start <= 0;
        end else begin
            btn_up <= debounced_btn_up && !debounced_btn_down && !debounced_btn_left && !debounced_btn_right;
            btn_down <= !debounced_btn_up && debounced_btn_down && !debounced_btn_left && !debounced_btn_right;
            btn_left <= !debounced_btn_up && !debounced_btn_down && debounced_btn_left && !debounced_btn_right;
            btn_right <= !debounced_btn_up && !debounced_btn_down && !debounced_btn_left && debounced_btn_right;
            btn_A <= debounced_btn_A && !debounced_btn_B;
            btn_B <= !debounced_btn_A && debounced_btn_B;
            btn_start <= debounced_btn_start;
        end
    end

endmodule
