module tb();
    wire a, b, o;
    dut dut_i(.*);

    always_comb begin
        assume(b == 1'b0);
        assert(o == a);
    end
endmodule
