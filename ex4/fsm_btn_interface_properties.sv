module fsm_btn_interface_properties #(
    parameter ASSUME_MODE = 1
) (
    input logic clk,
    input logic reset,
    input logic btn_up,
    input logic btn_down,
    input logic btn_left,
    input logic btn_right,
    input logic btn_A,
    input logic btn_B,
    input logic btn_start
);

    property one_dir_btn;
        @(posedge clk) (btn_up + btn_down + btn_right + btn_left < 2);
    endproperty

    property one_modifier_btn;
        @(posedge clk) (btn_A + btn_B < 2);
    endproperty

    generate if (ASSUME_MODE) begin
        assume property (one_dir_btn);
        assume property (one_modifier_btn);
    end else begin 
        p_one_dir_btn: assert property (one_dir_btn);
        p_one_modifier_btn: assert property (one_modifier_btn);
    end
    endgenerate
endmodule
