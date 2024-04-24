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
variable(K: Set (EuclideanSpace ℝ (Fin n)))(hK: K = {x | ∃ s, x = (sumK s vmatrix)})

--Define K_polar 1.3
variable(K_polar: Set (EuclideanSpace ℝ (Fin n)))(hK_polar: K_polar =
{y | ∀ x ∈ K, y ⬝ᵥ x ≤ 0})

--Define K' dual cone 1.4
variable(K': Set (EuclideanSpace ℝ (Fin n)))(hK': K' = {x | ∀ i, (vmatrix i) ⬝ᵥ x ≤ 0})

--Define K_polar_pol 1.5 polar cone of a polar cone
variable(K_polar_pol: Set (EuclideanSpace ℝ (Fin n)))(hK_polar_pol: K_polar_pol =
{x | ∀ y ∈ K_polar, y ⬝ᵥ x ≤ 0 })

