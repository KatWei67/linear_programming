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
    rw[Finset.smul_sum, Finset.smul_sum]
    rw[add_sum_vec]
    simp

theorem K_polar_convex: Convex ℝ (K_polar vmatrix) := by
  rw[Convex]
  intros x hx y hy a b ha hb ha_b
  rw[K_polar] at hx
  simp at hx
  rw[K] at hx
  rw[K_polar] at hy
  rw[K] at hy
  rw[K_polar]
  simp
  rw[K]
  intro z hz
  have h_1: x ⬝ᵥ z ≤ 0 := by
    exact hx z hz
  have h_2: y ⬝ᵥ z ≤ 0 := by
    exact hy z hz
  apply add_nonpos
  have h_3: a * x ⬝ᵥ z ≤ 0 := by exact mul_nonpos_of_nonneg_of_nonpos ha (hx z hz)
  exact h_3
  have h_4: b * y ⬝ᵥ z ≤ 0 := by exact mul_nonpos_of_nonneg_of_nonpos hb (hy z hz)
  exact h_4 

-- Lemma 1.6
-- Farkas' Lemma
-- Define mathematical conditions
variable {m n : ℕ}
variable (A : Matrix (Fin m) (Fin n) ℝ) (c : (Fin n) → ℝ)
variable {m n : ℕ}
variable (A : Matrix (Fin m) (Fin n) ℝ) (c : (Fin n) → ℝ)

def all_non_positive (v : (Fin m) → ℝ) : Prop :=
  ∀ i, v i ≤ 0

def all_non_negative (v : (Fin m) → ℝ) : Prop :=
  ∀ i, v i ≥ 0

-- Define the conditions of Farkas' Lemma
def system_one_has_solution (A : Matrix (Fin m) (Fin n) ℝ) (c : (Fin n) → ℝ) : Prop :=
  ∃ x : (Fin n) → ℝ, all_non_positive (A *ᵥ x) ∧ c * x > 0

def system_two_has_solution (A : Matrix (Fin m) (Fin n) ℝ) (c : (Fin n) → ℝ) : Prop :=
  ∃ lambda : (Fin m) → ℝ, (transpose A) *ᵥ lambda = c ∧ all_non_negative lambda
