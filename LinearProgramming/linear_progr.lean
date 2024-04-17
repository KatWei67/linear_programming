import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Reflection
import Mathlib.Data.Matrix.RowCol

open Matrix
variable(m n :ℕ)
variable (M : Matrix (Fin m) (Fin n) ℝ) (v : (Fin n) → ℝ)(v₁: (Fin m) → ℝ )(i: Fin m)(k: Fin n)

#check M *ᵥ v  -- works
#check row v
#check col v
#check (row v₁) * M
#check M i
#check col (M i)


variable (A : Matrix (Fin n) (Fin n) ℝ)
variable (S : Set ((Fin n) → ℝ)) (hS : S = {v | A *ᵥ v = 0})

variable (B: Set (Matrix (Fin n) Unit ℝ))(hB : B = {v | ∃ m₁, v = col (M m₁)})
-- def S := {v | A *ᵥ v = 0}
#check {v | ∃j, col (A j) = v}
#check S
