module dut(input a, input b, output o);
    assign o = a ^ b;
    always_comb begin
        assume(b == 1'b0);
        assert(o == a);
    end
endmodule
