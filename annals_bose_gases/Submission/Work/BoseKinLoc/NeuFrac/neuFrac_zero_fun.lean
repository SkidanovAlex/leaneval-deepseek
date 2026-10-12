import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.NeuFrac.neuFrac_add_const_L2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.NeuFrac.neuFrac_zero_fun` — the Neumann fraction of the zero state

`neuFrac ℓ a2 u ϕ` (`Work.BoseKinLoc.Defs`, FS `eq:DefT`'s first term before the prefactor) is
the box Neumann-resolvent fraction written as a Dirichlet-principle infimum

    `neuFrac ℓ a² u ϕ = inf_g [ ‖ϕ‖²_Λ − 2a²⟨ϕ,g⟩_Λ + a²(‖∇g‖²_Λ + a²‖g‖²_Λ) ]`,   `Λ = Λ(u)`,

over globally smooth compactly supported trials `g`.  Here `ϕ = 0`, so every term containing
`ϕ` drops out and the defining set of trials reduces to

    `S = { a²·(Σ_k ∫_Λ (∂_k g)² + a² ∫_Λ g²) | g smooth compactly supported }`.

Two elementary facts close the `sInf`: `0 ∈ S` (the trial `g = 0`, all derivatives of the zero
function vanishing) and `0 ≤ c` for every `c ∈ S` (each element of `S` is `a² ≥ 0` times a sum
of two integrals of squares).  With `0 ≤ a²` — the hypothesis of the statement, so that the
degenerate case `a² = 0` is included — this pins `sInf S = 0`.

The proof below is self-contained (only the definition of `neuFrac` from `Defs` is used);
the general fact `sInf S = 0` for a set of reals containing `0` and bounded below by `0` is
extracted as `sInf_eq_zero_of_zero_mem_of_nonneg`.
-/

noncomputable section

open MeasureTheory
open scoped Topology ContDiff

namespace Work.BoseKinLoc.NeuFrac

open Submission.BoseGases

/-- A set of reals containing `0` and bounded below by `0` has infimum `0`. -/
lemma sInf_eq_zero_of_zero_mem_of_nonneg {S : Set ℝ} (h0 : 0 ∈ S)
    (hnn : ∀ c ∈ S, 0 ≤ c) : sInf S = 0 :=
  le_antisymm (csInf_le ⟨0, hnn⟩ h0) (le_csInf ⟨0, h0⟩ hnn)

/-- `neuFrac` of the zero state vanishes, for every `a² ≥ 0` (including `a² = 0`). -/
theorem neuFrac_zero_fun {ℓ a2 : ℝ} (ha2 : 0 ≤ a2) (u : EuclideanSpace ℝ (Fin 3)) :
    Work.BoseKinLoc.neuFrac ℓ a2 u (fun _ => (0 : ℝ)) = 0 := by
  unfold Work.BoseKinLoc.neuFrac
  apply sInf_eq_zero_of_zero_mem_of_nonneg
  · exact ⟨fun _ : ℝ³ => (0 : ℝ), contDiff_const, HasCompactSupport.zero, by simp⟩
  · rintro c ⟨g, -, -, rfl⟩
    have h1 : (∫ z in Work.BoseKinLoc.lamBox ℓ u, ((fun _ : ℝ³ => (0 : ℝ)) z) ^ 2) = 0 := by
      simp
    have h2 : (∫ z in Work.BoseKinLoc.lamBox ℓ u, ((fun _ : ℝ³ => (0 : ℝ)) z) * g z) = 0 := by
      simp
    rw [h1, h2]
    simp only [mul_zero, sub_zero, zero_add]
    exact mul_nonneg ha2 (add_nonneg
      (Finset.sum_nonneg fun k _ => integral_nonneg fun z => sq_nonneg _)
      (mul_nonneg ha2 (integral_nonneg fun z => sq_nonneg _)))

end Work.BoseKinLoc.NeuFrac
