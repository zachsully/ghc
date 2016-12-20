test('T10858',
     [compiler_stats_num_field('bytes allocated',
          [ (wordsize(64), 262782552, 8) ]),
          # Initial:    222312440
          # 2016-12-19  262782552  Join points (#19288)
      only_ways(['normal']),
      when(msys(), expect_broken(12713))
      ],
     compile,
     ['-O'])
