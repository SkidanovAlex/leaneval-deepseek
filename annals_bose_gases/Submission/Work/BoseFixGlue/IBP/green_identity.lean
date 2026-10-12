import ChallengeDeps
import Mathlib.Order.CompletePartialOrder
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.CellIBP
import Submission.Work.BoseFixGlue.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory Filter Metric
open scoped Topology BigOperators Real

/-!
# `Work.BoseFixGlue.IBP.green_identity` — the Green identity of FS's localisation comparison

For a smooth `Φ` whose (closed) support lies in the centred box `abox N L`, the
gradient-form kinetic energy of `Φ` equals the operator form `⟨Φ, −ΔᵢΦ⟩` integrated
over the box:

`∑ᵢ ∫ Σ_k (∂_{i,k} Φ)² = ∑ᵢ ∫_{abox N L} Φ · (−Δᵢ Φ)`.

Proof. `tsupport Φ ⊆ abox N L ⊆ abox N (max L 1)` and `abox N (max L 1)` is compact
(`abox_compact`, valid since `max L 1 > 0`), so `Φ` has compact support.  Hence the
whole-space integration by parts `kinetic_term_eq_grad` (smooth compactly supported
`Φ`: `∫ Φ·(−ΔᵢΦ) = Σ_k ∫ (∂_{i,k}Φ)²`, proved in `Submission.CellIBP`) applies, and the
sum over `k` is interchanged with the integral (`integral_finsetSum`, integrability from
`kinetic_dirSq_integrable`).  Finally the integral over all of `X N` of `Φ·(−ΔᵢΦ)`
equals the integral over the box, because `Φ` vanishes off `tsupport Φ ⊆ abox N L`
(`setIntegral_eq_integral_of_forall_compl_eq_zero`).
-/

namespace Work.BoseFixGlue.IBP

theorem green_identity {N : ℕ} {L : ℝ} {Φ : Submission.BoseGases.X N → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hsupp : tsupport Φ ⊆ Submission.BoseGases.abox N L) :
    (∑ i : Fin N, ∫ x : Submission.BoseGases.X N, ∑ k : Fin 3,
        (fderiv ℝ Φ x (Submission.BoseGases.kcDir N i k)) ^ 2)
      = ∑ i : Fin N, ∫ x in Submission.BoseGases.abox N L,
          Φ x * (-(BoseGases.partialLaplacian i Φ x)) := by
  have hmax : 0 < max L 1 := lt_of_lt_of_le zero_lt_one (le_max_right L 1)
  have hmono : Submission.BoseGases.abox N L ⊆ Submission.BoseGases.abox N (max L 1) := by
    intro x hx
    simp only [Submission.BoseGases.mem_abox_iff] at hx
    intro i
    simp only [Submission.BoseGases.mem_acube_iff] at hx ⊢
    intro m
    obtain ⟨h1, h2⟩ := hx i m
    have hL1 : L ≤ max L 1 := le_max_left L 1
    exact ⟨by linarith, by linarith⟩
  have hcs : HasCompactSupport Φ :=
    IsCompact.of_isClosed_subset (Submission.BoseGases.abox_compact N hmax) (isClosed_tsupport Φ)
      (hsupp.trans hmono)
  have key : ∀ i : Fin N,
      (∫ x : Submission.BoseGases.X N, ∑ k : Fin 3,
        (fderiv ℝ Φ x (Submission.BoseGases.kcDir N i k)) ^ 2)
      = ∫ x in Submission.BoseGases.abox N L, Φ x * (-(BoseGases.partialLaplacian i Φ x)) := by
    intro i
    have hdir : ∀ k : Fin 3, Integrable (fun x : Submission.BoseGases.X N =>
        (fderiv ℝ Φ x (Submission.BoseGases.kcDir N i k)) ^ 2) volume :=
      fun k => Submission.BoseGases.kinetic_dirSq_integrable hΦ hcs i k
    rw [integral_finsetSum (Finset.univ : Finset (Fin 3)) (fun k _ => hdir k)]
    rw [← Submission.BoseGases.kinetic_term_eq_grad hΦ hcs i]
    rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := Submission.BoseGases.abox N L)
      (f := fun x => Φ x * (-(BoseGases.partialLaplacian i Φ x))) (fun x hx => by
        have hx' : x ∉ tsupport Φ := fun h => hx (hsupp h)
        simp [image_eq_zero_of_notMem_tsupport hx'])]
  exact Finset.sum_congr rfl (fun i _ => key i)

end Work.BoseFixGlue.IBP
