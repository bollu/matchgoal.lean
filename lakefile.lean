import Lake
open Lake DSL

package «matchgoal» {
  -- add package configuration options here
}

lean_lib «Matchgoal» {
  -- add library configuration options here
}

@[default_target]
lean_exe «matchgoal» {
  root := `Main
}
