module dut_check(input a, input b, input o);
    always_comb begin
        assume(b == 1'b0);
        assert(o == a);
    end
endmodule

bind dut dut_check dut_check_i(.*);
