import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Reflection
import Mathlib.Data.Matrix.RowCol
import Mathlib.Algebra.BigOperators.Finprod
open BigOperators
open Finset
open Matrix

noncomputable section

def zero_vec(n: ℕ ): Fin n → ℝ := λ x => 0
variable {n m:ℕ} [NeZero m]


def sumK (s : Fin m → NNReal) (v : Fin m → Fin n → ℝ)
:= ∑ i in range m, s i • v i

-- Define K cone 1.2
variable (vmatrix : Fin m → Fin n → ℝ)

def K: Set (Fin n → ℝ) := {x | ∃ s, x = (sumK s vmatrix)}

def s_lambda(i : Fin m): (Fin m) → NNReal:= λ x =>
if x = i then 1 else 0

lemma t1(i: Fin m): (s_lambda i i) • vmatrix i = vmatrix i := by
  ext
  simp [s_lambda]

lemma t2(i: Fin m)(t: Fin m)(h: t ≠ i): (s_lambda i t ) • vmatrix i = zero_vec n:= by
  ext x
  have: s_lambda i t = 0 := by
    ext
    simp [s_lambda]
    by_contra
    apply h
    assumption
  rw[this]
  rw[zero_vec]
  apply zero_mul

-- all column vectors are in the cone
lemma vec_in_K(i': Fin m): vmatrix i' ∈ K vmatrix:= by
  rw[K]
  use s_lambda i'
  unfold sumK
  sorry

--Define K_polar 1.3
def K_polar: Set (Fin n → ℝ) :=
{y | ∀ x ∈ K vmatrix, y ⬝ᵥ x ≤ 0}

--Define K' dual cone 1.4
def K': Set (Fin n → ℝ) := {x | ∀ i, (vmatrix i) ⬝ᵥ x ≤ 0}
#check K' vmatrix
--Define K_polar_pol 1.5 polar cone of a polar cone
def K_polar_pol: Set (Fin n → ℝ) :=
{x | ∀ y ∈ K_polar vmatrix, y ⬝ᵥ x ≤ 0 }


theorem dual_eq_polar : K' vmatrix = K_polar vmatrix := by
   ext y
   constructor
   . sorry
   . intro hy
     --have h1: ∀ y ∈ K, x ⬝ᵥ y ≤ 0 := by
     rw[K_polar] at hy
     rw [K']
     intro i
     have h1: ∀ x ∈ K vmatrix, x ⬝ᵥ y ≤ 0 := by
       sorry
     sorry


theorem cone_eq_polar_pol: K vmatrix = K_polar_pol vmatrix:= by
  sorry
