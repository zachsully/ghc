test('join001', normal, compile, ['-O'])

test('join002',
  [stats_num_field('bytes allocated', [(wordsize(64), 2000290792, 0)])],
  compile_and_run,
  [''])
test('join003',
  [stats_num_field('bytes allocated', [(wordsize(64), 2000290792, 0)])],
  compile_and_run,
  [''])
test('join004',
  [stats_num_field('bytes allocated', [(wordsize(64), 48146720, 5)])],
  compile_and_run,
  [''])

test('join005', normal, compile, ['-O'])
test('join006', normal, compile, ['-O'])
