import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Reflection
import Mathlib.Data.Matrix.RowCol

import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Real.Basic
-- check

open Matrix

variable(m n :ℕ)
variable (M : Matrix (Fin m) (Fin n) ℝ) (v : (Fin n) → ℝ)(v₁: (Fin m) → ℝ )(i: Fin m)(j: Fin n)
#check M *ᵥ v  -- works
#check row v
#check col v
#check (row v₁) * M
#check col (M i)
#check row (M i)

variable (A : Matrix (Fin n) (Fin n) ℝ)
variable (S : Set ((Fin n) → ℝ)) (hS : S = {v | A *ᵥ v = 0})
-- def S := {v | A *ᵥ v = 0}
#check {v | ∃j, col (A j) = v}
#check S


-- Farkas' Lemma
-- Define mathematical conditions
variables {m n : ℕ}
variables (A : Matrix (Fin m) (Fin n) ℝ) (c : (Fin n) → ℝ)

def all_non_positive (v : (Fin m) → ℝ) : Prop :=
  ∀ i, v i ≤ 0

def all_non_negative (v : (Fin m) → ℝ) : Prop :=
  ∀ i, v i ≥ 0

-- Define the conditions of Farkas' Lemma
def system_one_has_solution (A : Matrix (Fin m) (Fin n) ℝ) (c : (Fin n) → ℝ) : Prop :=
  ∃ x : (Fin n) → ℝ, all_non_positive (A *ᵥ x) ∧ c * x > 0

def system_two_has_solution (A : Matrix (Fin m) (Fin n) ℝ) (c : (Fin n) → ℝ) : Prop :=
  ∃ lambda : (Fin m) → ℝ, (transpose A) *ᵥ lambda = c ∧ all_non_negative lambda
