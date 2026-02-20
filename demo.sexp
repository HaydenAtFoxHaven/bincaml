(load-il "examples/cntlm-simp-output.il")
(run-transforms "remove-unreachable-block" "cf-expressions" "intra-dead-store-elim")
; (run-transforms "ssa")
(run-transform "demo-cfg-tnum-wint-reduced-analysis")