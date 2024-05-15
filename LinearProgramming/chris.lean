import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Reflection
import Mathlib.Data.Matrix.RowCol
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.Convex.Basic
open BigOperators
open Finset
open Matrix
--experiement
variable{m n :ℕ}
variable (vmatrix : Fin m → Fin n → ℝ)
noncomputable section

def sumK (s : Fin m → ℝ  ) (v : Fin m → Fin n → ℝ)
:= ∑ i: Fin m, s i • v i

def K: Set (Fin n → ℝ) := {x | ∃ s ≥ 0, x = (sumK s vmatrix)}

def K_polar: Set (Fin n → ℝ) :=
{y | ∀ x ∈ K vmatrix, y ⬝ᵥ x ≤ 0}

#check Convex ℝ (K vmatrix)

theorem K_convex: Convex ℝ (K vmatrix) := by
  rw[Convex]
  intro x hx
  rw[K] at hx
  simp at hx
  rcases hx with ⟨sx ,⟨hsxnonneg, hx⟩ ⟩
  rw[StarConvex]
  intro y hy a b ha hb hab
  rcases hy with ⟨sy , ⟨hsynonneg,hy⟩ ⟩
  rw[K]
  simp
  use a • sx + b • sy
  constructor
  . have h1 : 0 ≤ a • sx := by exact smul_nonneg ha hsxnonneg
    have h2: 0 ≤ b • sy := by exact smul_nonneg hb hsynonneg
    exact Left.add_nonneg h1 h2
  . rw[hx, hy]
    rw[sumK, sumK, sumK]
    simp


    sorry






-- variable (M : Matrix (Fin m) (Fin n) ℝ) (v : (Fin n) → ℝ)(v₁: (Fin m) → ℝ )(i: Fin m)(k: Fin n)

-- #check M *ᵥ v  -- works
-- #check row v
-- #check col v
-- #check (row v₁) * M
-- #check fun i => M i k
-- #check col (M i)

-- -- take the column of a matrix
-- def matrix_col (M : Matrix (Fin m) (Fin n) ℝ) (k: Fin n) := λ x => M x k

-- variable (A : Matrix (Fin n) (Fin n) ℝ)
-- variable (S : Set ((Fin n) → ℝ)) (hS : S = {v | A *ᵥ v = 0})

-- variable (B: Set (Matrix (Fin n) Unit ℝ))(hB : B = {v | ∃ m₁, v = col (M m₁)})

-- variable(a: EuclideanSpace ℝ (Fin n))(b: EuclideanSpace ℝ (Fin n))
-- #check a ⬝ᵥ b
