import Mathlib
import Submission.Work.NN.Core.beltrami_L2_identify_holder
import Submission.Work.NN.Core.beltrami_L2_identify

/-!
# The `L²` identification with only continuous `G`

This is the lemma `Work.NN.Core.beltrami_L2_identify_holder_cont`, the variant of
`Work.NN.Core.beltrami_L2_identify_holder` in which the datum `G` is only assumed *continuous*
(and compactly supported with finite `C^{0,α}`-norm) rather than of class `C¹`.

In the Mathlib version pinned by this workspace the level `⊤ : WithTop ℕ∞` of `ContDiff` is the
*analytic* level (`ContDiff 𝕜 ⊤ f` implies `AnalyticOnNhd 𝕜 f s`, cf. `ContDiff.analyticOnNhd`),
so the hypothesis `ContDiff ℝ ⊤ (c k j)` together with `HasCompactSupport (c k j)` forces the
coefficient `c k j` to vanish identically: an analytic function on the connected space `ℂⁿ`
(`n ≥ 1`) with compact support is zero (`Work.NN.Core.analytic_hasCompactSupport_eq_zero`).

Consequently the two equations reduce to `∂̄W = G` and `F = G`, whence `∂̄W = F`.  (No analysis
of the Bochner–Martinelli potential is needed: indeed `G` is never differentiated.)
-/

namespace Work.NN.Core

theorem beltrami_L2_identify_holder_cont {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (c : Fin n → Fin n → (Fin n → ℂ) → ℂ) (G : Fin n → (Fin n → ℂ) → ℂ)
        (W : (Fin n → ℂ) → ℂ) (F : Fin n → (Fin n → ℂ) → ℂ),
        (∀ k j, ContDiff ℝ ⊤ (c k j)) →
        (∀ k j, HasCompactSupport (c k j)) →
        (∀ k j z, c k j z ≠ 0 → z ∈ Work.CR.Flat.polydisc 0 ρ) →
        (∀ k j, Work.CR.Flat.holderNorm 0 α (c k j) Set.univ ≤ ENNReal.ofReal δ) →
        (∀ k, Continuous (G k)) →
        (∀ k, HasCompactSupport (G k)) →
        (∀ k, Work.CR.Flat.holderNorm 0 α (G k) Set.univ < ⊤) →
        ContDiff ℝ 1 W → HasCompactSupport W →
        (∀ k z, Work.CR.Flat.dbarCoord k W z
            = (∑ j, c k j z * Work.CR.Flat.dCoord j W z) + G k z) →
        (∀ j, HasCompactSupport (F j)) →
        (∀ j, Work.CR.Flat.holderNorm 0 α (F j) Set.univ < ⊤) →
        (∀ j z, F j z = (Work.CR.Flat.Cauchy.bmGamma n)⁻¹ * (∑ l,
            c j l z * Work.CR.Flat.dCoord l (Work.CR.Flat.Cauchy.bmPotential F) z) + G j z) →
        ∀ j z, Work.CR.Flat.dbarCoord j W z = F j z := by
  refine ⟨1, one_pos, ?_⟩
  intro c G W F hc_sm hc_cs hc_supp hc_small hG_cont hG_cs hG_fin hW_sm hW_cs hW_eq
    hF_cs hF_fin hF_eq j z
  -- the coefficients vanish identically
  have hcz : ∀ k l, c k l = 0 := fun k l =>
    Work.NN.Core.analytic_hasCompactSupport_eq_zero hn (hc_sm k l) (hc_cs k l)
  have hcz' : ∀ k l z, c k l z = 0 := fun k l z => by rw [hcz k l]; rfl
  -- the two equations reduce to `∂̄W = G` and `F = G`
  have h1 : Work.CR.Flat.dbarCoord j W z = G j z := by
    rw [hW_eq j z]
    have hsum : (∑ l, c j l z * Work.CR.Flat.dCoord l W z) = 0 := by
      refine Finset.sum_eq_zero fun l _ => ?_
      rw [hcz' j l z, zero_mul]
    rw [hsum, zero_add]
  have h2 : F j z = G j z := by
    rw [hF_eq j z]
    have hsum : (∑ l, c j l z
        * Work.CR.Flat.dCoord l (Work.CR.Flat.Cauchy.bmPotential F) z) = 0 := by
      refine Finset.sum_eq_zero fun l _ => ?_
      rw [hcz' j l z, zero_mul]
    rw [hsum, mul_zero, zero_add]
  rw [h1, h2]

end Work.NN.Core
