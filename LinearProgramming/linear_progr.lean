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

def sumK (s : Fin m → ℝ) (v : Fin m → Fin n → ℝ)
:= ∑ i: Fin m, s i • v i

variable (vmatrix : Fin m → Fin n → ℝ)

-- Define K cone 1.2
def K: Set (Fin n → ℝ) := {x | ∃ s ≥ 0, x = (sumK s vmatrix)}
#check K
def s_lambda(i : Fin m): (Fin m) → ℝ := λ x =>
if x = i then 1 else 0
#check s_lambda

-- all column vectors are in the cone
lemma vec_in_K(i': Fin m): vmatrix i' ∈ K vmatrix:= by
  rw[K]
  use s_lambda i'
  unfold sumK
  simp [s_lambda]
  intro ix
  rw[s_lambda]
  simp
  by_cases h : (ix = i')
  simp [h]
  simp [h]

--Define K_polar 1.3
def K_polar: Set (Fin n → ℝ) :=
{y | ∀ x ∈ K vmatrix, y ⬝ᵥ x ≤ 0}

--Define K' dual cone 1.4
def K': Set (Fin n → ℝ) := {x | ∀ i, (vmatrix i) ⬝ᵥ x ≤ 0}

def K_dual: Set (Fin n → ℝ) := {x | vmatrix *ᵥ x ≤ 0}

lemma dual_eq: K' vmatrix = K_dual vmatrix := by
  ext x
  constructor
  . intro h'
    rw[K'] at h'
    simp at h'
    rw[K_dual]
    simp[h']
    intro i'
    exact h' i'
  . intro h_dual
    rw[K_dual] at h_dual
    simp at h_dual
    rw[K']
    simp
    intro i
    exact h_dual i

--Define K_polar_pol 1.5 polar cone of a polar cone
def K_polar_pol: Set (Fin n → ℝ) :=
{x | ∀ y ∈ K_polar vmatrix, y ⬝ᵥ x ≤ 0 }


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


lemma Farkas_lemma_2(t: Fin n → ℝ)(h: t ∉ K vmatrix): ∃ y : Fin n → ℝ, vmatrix *ᵥ y ≤ 0
∧ t ⬝ᵥ y > 0 := by sorry

theorem dual_eq_polar : K' vmatrix = K_polar vmatrix := by
   ext y
   constructor
   . intro hk'
     rw[K'] at hk'
     rw[K_polar]
     intro x hx
     rw[K] at hx
     rcases hx with ⟨s, hs_nonneg,hs⟩
     rw[hs]
     unfold sumK
     simp at hk'
     rw[dotproduct_sum_eq]
     have(x: Fin m): y ⬝ᵥ s x • vmatrix x =  s x •vmatrix x  ⬝ᵥ y:= by
        rw [Matrix.dotProduct_comm]
     simp[this]
     have h (x: Fin m) : s x • (vmatrix x ⬝ᵥ y) ≤ 0 := by
       have h1: s x ≥ 0 := by exact hs_nonneg x
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
     rw[dotProduct_comm']
     exact h


theorem cone_eq_polar_pol: K vmatrix = K_polar_pol vmatrix:= by
  ext x
  constructor
  . intro hk
    rw[K_polar_pol]
    rw[K_polar]
    simp
    intro y hy
    apply hy
    exact hk
  . intro hpp
    contrapose hpp
    rw[K] at hpp
    simp at hpp
    have h': x ∉ K vmatrix := by
      rw[K]
      simp
      exact hpp
    push_neg at hpp
    have h1: ∃ y: Fin n  → ℝ , vmatrix *ᵥ y ≤ 0 ∧ x ⬝ᵥ y > 0 := by
      apply Farkas_lemma_2 vmatrix x h'
    rcases h1 with ⟨y, hy⟩
    intro hx
    have h1: y ∈ K_dual vmatrix := by
      rw[K_dual]
      simp
      exact hy.1
    have h2: y ∈ K' vmatrix := by
      rw[dual_eq vmatrix]
      exact h1
    have h3: K_polar vmatrix = K' vmatrix := by
      simp[dual_eq_polar vmatrix]
    have h4: y ∈ K_polar vmatrix := by
      rw[h3]
      exact h2
    rw[K_polar_pol] at hx; simp at hx
    have: y ⬝ᵥ x ≤ 0 := by
      apply hx
      exact h4
    rw[dotProduct_comm'] at this
    linarith[this, hy.2]


lemma add_sum_vec (a b: ℝ)(va vb: Fin m → ℝ)(vmatrix: Fin m → Fin n → ℝ):
∑ i : Fin m, a • va i • vmatrix i + ∑ i : Fin m, b • vb i • vmatrix i = ∑ i : Fin m, (a
• va i + b • vb i) •
vmatrix i := by
  rw[← Finset.sum_add_distrib]
  apply Finset.sum_congr
  . rfl
  . intro x hx
    rw[add_smul]
    rw[smul_assoc,smul_assoc]

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

theorem K_polar_convex:  Convex ℝ (K_polar vmatrix) := by
  rw[Convex]
  intro x hx
  rw[StarConvex]
  intro y hy
  intro a b apos bpos aplusb
  rw[K_polar]
  simp
  intro z hz
  have h1: x ⬝ᵥ z ≤ 0 := by
    rw[K_polar] at hx
    simp at hx
    apply hx z
    exact hz
  have h2: y ⬝ᵥ z ≤ 0 := by
    rw[K_polar] at hy
    simp at hy
    apply hy z
    exact hz
  apply add_nonpos
  . apply mul_nonpos_iff.2
    left
    constructor
    . exact apos
    . exact h1
  . apply mul_nonpos_iff.2
    left
    constructor
    exact bpos
    exact h2
