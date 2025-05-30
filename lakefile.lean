import Lake
open Lake DSL

package "CrashCourse" where
  version := v!"0.1.0"

@[default_target]
lean_lib «CrashCourse» where
  -- add library configuration options here
