import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.Data.Real.Basic

namespace Commons.Combinatorics.Transference

open Finset
open scoped BigOperators

/-- Green–Tao Lemma 6.3, the identity `⟨F, 𝒟F⟩ = ‖F‖_{U^d}^{2^d}`: pairing `F` with its
dual function `𝒟F(x) = ∑_h ∏_{ω ≠ 0} F(x + ω·h)` gives the `d`-cube sum of `F`. -/
theorem dual_first {G : Type*} [AddCommGroup G] [Fintype G] (d : ℕ) (F : G → ℝ) :
    ∑ x : G, F x * (∑ h : Fin d → G,
        ∏ ω ∈ (Finset.univ.erase (0 : Fin d → Bool)), F (x + ∑ i, (if ω i then h i else 0)))
      = ∑ h : Fin d → G, ∑ x : G,
          ∏ ω : Fin d → Bool, F (x + ∑ i, (if ω i then h i else 0)) := by
  have hL : (∑ x : G, F x * (∑ h : Fin d → G,
        ∏ ω ∈ (Finset.univ.erase (0 : Fin d → Bool)), F (x + ∑ i, (if ω i then h i else 0))))
      = ∑ x : G, ∑ h : Fin d → G, F x *
        ∏ ω ∈ (Finset.univ.erase (0 : Fin d → Bool)), F (x + ∑ i, (if ω i then h i else 0)) := by
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.mul_sum]
  have hR : (∑ h : Fin d → G, ∑ x : G,
          ∏ ω : Fin d → Bool, F (x + ∑ i, (if ω i then h i else 0)))
      = ∑ h : Fin d → G, ∑ x : G, F x *
        ∏ ω ∈ (Finset.univ.erase (0 : Fin d → Bool)), F (x + ∑ i, (if ω i then h i else 0)) := by
    apply Finset.sum_congr rfl
    intro h _
    apply Finset.sum_congr rfl
    intro x _
    rw [← Finset.mul_prod_erase Finset.univ
      (fun ω : Fin d → Bool => F (x + ∑ i, (if ω i then h i else 0)))
      (Finset.mem_univ (0 : Fin d → Bool))]
    have hz : (∑ i, (if (0 : Fin d → Bool) i then h i else 0)) = 0 := by
      simp
    rw [hz, add_zero]
  rw [hL, hR, Finset.sum_comm]

end Commons.Combinatorics.Transference