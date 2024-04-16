import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Reflection
#check EuclideanSpace
open Matrix
variable (k : Type) [Field k] (n : ℕ)

#check EuclideanSpace k (Fin n)

example {𝕜 : Type u_8} [RCLike 𝕜] {n : Type u_9} [Fintype n] (x : EuclideanSpace 𝕜 n) : true := by rfl
variable (x: EuclideanSpace k (Fin n))
def E :=  EuclideanSpace k (Fin n)
#check E k n


variable(m n :ℕ) (x: E k n)
def M := Matrix (Fin m) (Fin n) ℝ
def v := (Fin n) → ℝ
--#check Matrix.mulVecᵣ M v

--#check (Matrix (Fin m) (Fin n) k) *ᵥ x
--
