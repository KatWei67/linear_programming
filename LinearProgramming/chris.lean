import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Reflection
import Mathlib.Data.Matrix.RowCol
import Mathlib.Algebra.BigOperators.Finprod
open BigOperators
open Finset
open Matrix
--experiement
variable{m n :ℕ}
variable (M : Matrix (Fin m) (Fin n) ℝ) (v : (Fin n) → ℝ)(v₁: (Fin m) → ℝ )(i: Fin m)(k: Fin n)

#check M *ᵥ v  -- works
#check row v
#check col v
#check (row v₁) * M
#check fun i => M i k
#check col (M i)

-- take the column of a matrix
def matrix_col (M : Matrix (Fin m) (Fin n) ℝ) (k: Fin n) := λ x => M x k

variable (A : Matrix (Fin n) (Fin n) ℝ)
variable (S : Set ((Fin n) → ℝ)) (hS : S = {v | A *ᵥ v = 0})

variable (B: Set (Matrix (Fin n) Unit ℝ))(hB : B = {v | ∃ m₁, v = col (M m₁)})

variable(a: EuclideanSpace ℝ (Fin n))(b: EuclideanSpace ℝ (Fin n))
#check a ⬝ᵥ b
