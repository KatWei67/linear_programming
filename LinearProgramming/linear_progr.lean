import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Reflection
import Mathlib.Data.Matrix.RowCol
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.BigOperators.Basic
open BigOperators
open Finset
open Matrix

noncomputable section

def zero_vec(n: ℕ ): Fin n → ℝ := λ x => 0
variable {n m:ℕ} [NeZero m]

theorem dotProduct_comm' (x: Fin n → ℝ )(y: Fin n → ℝ): x ⬝ᵥ y = y ⬝ᵥ x := by
   apply Matrix.dotProduct_comm

def sumK (s : Fin m → NNReal) (v : Fin m → Fin n → ℝ)
:= ∑ i: Fin m, s i • v i

-- Define K cone 1.2
variable (vmatrix : Fin m → Fin n → ℝ)

def K: Set (Fin n → ℝ) := {x | ∃ s, x = (sumK s vmatrix)}
#check K
def s_lambda(i : Fin m): (Fin m) → NNReal:= λ x =>
if x = i then 1 else 0

-- all column vectors are in the cone

lemma vec_in_K(i': Fin m): vmatrix i' ∈ K vmatrix:= by
  rw[K]
  use s_lambda i'
  unfold sumK
  -- rw [s_lambda_def]
  simp [s_lambda]

--Define K_polar 1.3
def K_polar: Set (Fin n → ℝ) :=
{y | ∀ x ∈ K vmatrix, y ⬝ᵥ x ≤ 0}

--Define K' dual cone 1.4
def K': Set (Fin n → ℝ) := {x | ∀ i, x ⬝ᵥ (vmatrix i)  ≤ 0}
#check K' vmatrix
--Define K_polar_pol 1.5 polar cone of a polar cone
def K_polar_pol: Set (Fin n → ℝ) :=
{x | ∀ y ∈ K_polar vmatrix, y ⬝ᵥ x ≤ 0 }
variable(i: Fin m)
#check vmatrix i


lemma dotproduct_sum_eq (v : Fin n → ℝ ) (A : Fin m → (Fin n → ℝ ))
: v ⬝ᵥ ∑ i, A i = ∑ i, v ⬝ᵥ A i := by
  convert_to v ⬝ᵥ (1 ᵥ* A) = (A *ᵥ v) ⬝ᵥ 1
  · unfold Matrix.vecMul
    congr
    ext
    simp [Matrix.dotProduct]
  · congr
    simp [Matrix.mulVec]
    ext
    simp [Matrix.dotProduct, mul_comm]
  conv => rhs; rw [Matrix.dotProduct_comm]
  rw [Matrix.dotProduct_mulVec]
  conv => lhs; rw [Matrix.dotProduct_comm]


lemma Farkas_lemma_partial(t: Fin n → ℝ)( ht: t ∉ K vmatrix):
∃ y ∈ K' vmatrix, y ⬝ᵥ t > 0:= by sorry


theorem dual_eq_polar : K' vmatrix = K_polar vmatrix := by
   ext y
   constructor
   . intro hk'
     rw[K'] at hk'
     rw[K_polar]
     intro x hx
     rw[K] at hx
     rcases hx with ⟨s, hs⟩
     rw[hs]
     unfold sumK
     simp at hk'
     rw[dotproduct_sum_eq]
     have(x: Fin m): y ⬝ᵥ s x • vmatrix x =  s x • y ⬝ᵥ vmatrix x := by
        rw [Matrix.dotProduct_comm]
        simp
        rw[dotProduct_comm']
     simp[this]
     have h (x: Fin m) : s x • (y ⬝ᵥ vmatrix x) ≤ 0 := by
       have h1: s x ≥ 0 := by exact zero_le (s x)
       apply smul_nonpos_of_nonneg_of_nonpos h1 (hk' x)
     exact Fintype.sum_nonpos h
   . intro hy
     rw[K_polar] at hy
     rw [K']
     intro i
     have h: vmatrix i ∈ K vmatrix := by
        exact vec_in_K vmatrix i
     have: ∀ x ∈ K vmatrix, y ⬝ᵥ x ≤ 0 := by
       exact hy
     apply this at h
     exact h




theorem cone_eq_polar_pol: K vmatrix = K_polar_pol vmatrix:= by
  sorry
