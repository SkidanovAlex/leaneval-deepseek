import Mathlib
import Submission.Commons.Combinatorics.Additive.Gowers.gowers_cauchy_schwarz_general
import Submission.Commons.Combinatorics.Transference.Unorm_pow

set_option maxHeartbeats 1000000

namespace Commons.Combinatorics.Transference

open Finset
open scoped BigOperators

/-- Gowers–Cauchy–Schwarz for the `K`-fold product of dual functions at a fixed shift `H`:
the inner pairing is bounded by the cube sum of `f` times the product of the cube sums of
the functions `g_{ω·H}(x) = ∏_j F_j (x + ω·H_j)`. -/
theorem gcs_fold {G : Type*} [AddCommGroup G] [Fintype G] (d : ℕ) (f : G → ℝ) {K : ℕ}
    (F : Fin K → G → ℝ) (H : Fin K → Fin d → G) :
    (∑ h : Fin d → G, ∑ x : G, f x * ∏ ω ∈ (Finset.univ.erase (0 : Fin d → Bool)),
        ∏ j : Fin K,
          F j (x + (∑ i, if ω i then h i else 0) + (∑ i, if ω i then H j i else 0)))^(2^d)
      ≤ cubeSum d f * ∏ ω ∈ (Finset.univ.erase (0 : Fin d → Bool)),
          cubeSum d (fun x => ∏ j : Fin K, F j (x + ∑ i, if ω i then H j i else 0)) := by
  classical
  -- The family obtained from `f` and the shifted `K`-fold products `ω ↦ ∏_j F_j(· + ω·H_j)`:
  -- the vertex `0` carries `f`, every other vertex `ω` carries `∏_j F_j(· + ω·H_j)`.
  let Φ : (Fin d → Bool) → G → ℝ :=
    fun ω x => ∏ j : Fin K, F j (x + ∑ i, if ω i then H j i else 0)
  let Ψ : (Fin d → Bool) → G → ℝ := fun ω x => if ω = 0 then f x else Φ ω x
  have hgcs := Commons.Combinatorics.Additive.Gowers.gowers_cauchy_schwarz_general d Ψ
  -- The left-hand side is the Gowers inner product of `Ψ`.
  have hL : (∑ h : Fin d → G, ∑ x : G, f x * ∏ ω ∈ (Finset.univ.erase (0 : Fin d → Bool)),
        ∏ j : Fin K,
          F j (x + (∑ i, if ω i then h i else 0) + (∑ i, if ω i then H j i else 0)))
      = ∑ h : Fin d → G, ∑ x : G, ∏ ω : Fin d → Bool,
          Ψ ω (x + ∑ i : Fin d, (if ω i then h i else 0)) := by
    apply Finset.sum_congr rfl; intro h _
    apply Finset.sum_congr rfl; intro x _
    rw [← Finset.mul_prod_erase (Finset.univ : Finset (Fin d → Bool))
          (fun ω => Ψ ω (x + ∑ i : Fin d, (if ω i then h i else 0))) (Finset.mem_univ 0)]
    congr 1
    · simp only [Ψ]
      simp
    · apply Finset.prod_congr rfl; intro ω hω
      simp only [Ψ]
      rw [if_neg (Finset.mem_erase.mp hω).1]
  -- The right-hand side is the product of the cube sums of `Ψ`.
  have hR : (∏ ω : Fin d → Bool, cubeSum d (Ψ ω))
      = cubeSum d f * ∏ ω ∈ (Finset.univ.erase (0 : Fin d → Bool)),
          cubeSum d (fun x => ∏ j : Fin K, F j (x + ∑ i, if ω i then H j i else 0)) := by
    rw [← Finset.mul_prod_erase (Finset.univ : Finset (Fin d → Bool))
          (fun ω => cubeSum d (Ψ ω)) (Finset.mem_univ 0)]
    congr 1
    · congr 1
      funext x
      simp only [Ψ]
      simp
    · apply Finset.prod_congr rfl; intro ω hω
      congr 1
      funext x
      simp only [Ψ]
      rw [if_neg (Finset.mem_erase.mp hω).1]
  calc (∑ h : Fin d → G, ∑ x : G, f x * ∏ ω ∈ (Finset.univ.erase (0 : Fin d → Bool)),
        ∏ j : Fin K,
          F j (x + (∑ i, if ω i then h i else 0) + (∑ i, if ω i then H j i else 0)))^(2^d)
      = (∑ h : Fin d → G, ∑ x : G, ∏ ω : Fin d → Bool,
          Ψ ω (x + ∑ i : Fin d, (if ω i then h i else 0)))^(2^d) := by rw [hL]
    _ ≤ ∏ ω : Fin d → Bool, cubeSum d (Ψ ω) := hgcs
    _ = cubeSum d f * ∏ ω ∈ (Finset.univ.erase (0 : Fin d → Bool)),
          cubeSum d (fun x => ∏ j : Fin K, F j (x + ∑ i, if ω i then H j i else 0)) := hR

end Commons.Combinatorics.Transference
