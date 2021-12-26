test('SetAndGetBacktraceMechanisms', normal, compile_and_run, [''])
test('collectBacktraces', [only_ways(prof_ways)], compile_and_run, ['-finfo-table-map -prof'])
