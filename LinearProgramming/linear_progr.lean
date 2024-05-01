import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Reflection
import Mathlib.Data.Matrix.RowCol
import Mathlib.Algebra.BigOperators.Finprod
open BigOperators
open Finset
open Matrix

noncomputable section
variable {n m:ℕ} [NeZero m]

def sumK (s : Fin m → NNReal) (v : Fin m → EuclideanSpace ℝ (Fin n))
:= ∑ i in range m, s i • v i

-- Define K cone 1.2
variable (vmatrix : Fin m → EuclideanSpace ℝ (Fin n))
#check sumK
variable(K: Set (EuclideanSpace ℝ (Fin n)))(hK: K =
{x | ∃ s, x = (sumK s vmatrix)})

--Define K_polar 1.3
variable(K_polar: Set (EuclideanSpace ℝ (Fin n)))
(hK_polar: K_polar =
{y | ∀ x ∈ K, y ⬝ᵥ x ≤ 0})

--Define K' dual cone 1.4
variable(K': Set (EuclideanSpace ℝ (Fin n)))
(hK': K' = {x | ∀ i, (vmatrix i) ⬝ᵥ x ≤ 0})

--Define K_polar_pol 1.5 polar cone of a polar cone
variable(K_polar_pol: Set (EuclideanSpace ℝ (Fin n)))
(hK_polar_pol: K_polar_pol =
{x | ∀ y ∈ K_polar, y ⬝ᵥ x ≤ 0 })


def s_lambda(i : Fin m): (Fin m) → NNReal:= λ x =>
if x = i then 1 else 0
#eval (1:ℝ)
--first Q
variable(i: Fin m)
#check s_lambda i i


example: s_lambda i i = 1 := by
  ext
  simp [s_lambda]

#check s_lambda i
#check vmatrix i
--lemma const_mul_vec_i(i: Fin m): (s_lambda i) • (vmatrix i) = vmatrix i := by
  --sorry

-- all column vectors are in the cone
lemma vec_in_K(i: Fin m): vmatrix i ∈ K := by
  rw[hK]
  use s_lambda i
  unfold sumK
  simp
  sorry

lemma dual_eq_polar : K' = K_polar := by
   ext y
   constructor
   . sorry
   . intro hy
     --have h1: ∀ y ∈ K, x ⬝ᵥ y ≤ 0 := by
     rw[hK_polar] at hy
     rw [hK']
     intro i
     have h1: ∀ x ∈ K, x ⬝ᵥ y ≤ 0 := by
       sorry
     sorry


     --rw[hK] at hy



lemma cone_eq_polar_pol : K = K_polar_pol := by
  sorry
