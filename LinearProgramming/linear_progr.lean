import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Reflection
import Mathlib.Data.Matrix.RowCol

open Matrix
variable(m n :ℕ)
variable (M : Matrix (Fin m) (Fin n) ℝ) (v : (Fin n) → ℝ)(v₁: (Fin m) → ℝ )(i: Fin m)
#check M *ᵥ v  -- works
#check row v
#check col v
#check (row v₁) * M
#check col (M i)
