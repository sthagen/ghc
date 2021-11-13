#
test('selfloop', [cmm_src], compile, ['-no-hs-main'])
test('cmm_sink_sp', [ only_ways(['optasm']), grep_errmsg('(\[Sp.*\]).*(=).*(\[.*R1.*\]).*;',[1,2,3]), cmm_src], compile, ['-no-hs-main -ddump-cmm -dsuppress-uniques -O'])
test('cmm_sink_hp', [cmm_src,grep_errmsg('I64\[.*Hp.*=.*;')], compile, ['-no-hs-main -O -ddump-cmm'])
test('cmm_hp_invariant', [cmm_src,grep_errmsg('Hp invariant violated')], compile_fail, ['-no-hs-main -dcmm-lint'])

test('T16930', normal, makefile_test, ['T16930'])
test('T17442', normal, compile, [''])
test('T20725', normal, compile, ['-package ghc'])
