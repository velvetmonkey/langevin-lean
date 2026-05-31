import Lake
open Lake DSL

require "leanprover-community" / "mathlib" @ git "v4.28.0"

package «LangevinLean» where

@[default_target]
lean_lib «LangevinLean» where
