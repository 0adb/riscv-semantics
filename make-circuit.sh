#!/bin/bash
cd src
sed Spec/Decode.hs -i -e 's/.*if supports. iset then result. else.*/-- REDACTED to make clash work/g' \
                      -e 's/.*if bitwidth iset == 64.*/-- REDACTED to make clash work/g'
stack exec --package clash-ghc -- clash --verilog Platform/Clash.hs
git checkout -- Spec/Decode.hs
