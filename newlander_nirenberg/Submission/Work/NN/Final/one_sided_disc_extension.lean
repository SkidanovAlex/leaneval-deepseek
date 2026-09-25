/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The one-sided disc extension

This file proves `Work.NN.Final.one_sided_disc_extension`: a function `g` which is `C^k` on
`U × ball(0,1)` (with finite `C^{k,α}` norm there) extends to a `C^k` function on the larger
`U × ball(0,c)` with the `C^{k,α}` norm controlled.

The extension is the explicit radial (one-sided) Seeley construction `discExt k (discWt k)
discScale g` of `Submission.Work.NN.Final.DiscRadialDefs`: for `‖z‖ > 1` it is the finite sum
`∑_{m ≤ k} a m * χ (b m * (‖z‖ - 1)) * g (x, ρ_m z)` over the affine radial reflections `ρ_m`
(with `ρ_m` of radial derivative `- b m` at the sphere, so that the moment identities
`∑_{m ≤ k} a m * (-(b m))^j = 1` (`j ≤ k`) make the jets of the extension match those of `g` to
order `k`), on the sphere it is the radial boundary value of `g`, and on the open unit disc it is
`g` itself.

The two analytic inputs are proved separately:

* `Work.NN.DiscRadial.disc_ext_contDiffOn` — the `C^k` smoothness of the construction;
* `Work.NN.DiscRadial.disc_ext_holderNorm_le` — the `C^{k,α}` norm bound.
-/
import Mathlib
import Submission.Work.CR.Flat.Holder
import Submission.Work.NN.Final.DiscRadialDefs
import Submission.Work.NN.Final.DiscExtDefs
import Submission.Work.NN.DiscRadial.disc_ext_contDiffOn
import Submission.Work.NN.DiscRadial.disc_ext_holderNorm_le

noncomputable section

open scoped NNReal ENNReal ContDiff Topology
open Set Metric Filter

namespace Work.NN.Final

/-- The one-sided disc extension: a `C^k` function on `U × ball(0,1)` with finite `C^{k,α}`
norm extends to `U × ball(0,c)` (`c > 1`) with controlled `C^{k,α}` norm. -/
theorem one_sided_disc_extension {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {c : ℝ} (hc : 1 < c) :
    ∃ C : ℕ → ℝ, (∀ k, 0 < C k) ∧
      ∀ (k : ℕ) (U : Set X) (g : X × ℂ → ℂ), IsOpen U →
        (∀ m : ℕ, m ≤ k → ContDiffOn ℝ (m : WithTop ENat) g (U ×ˢ Metric.ball (0 : ℂ) 1)) →
        Work.CR.Flat.holderNorm k α g (U ×ˢ Metric.ball (0 : ℂ) 1) ≠ ⊤ →
        ∃ G : X × ℂ → ℂ,
          ContDiffOn ℝ (k : WithTop ENat) G (U ×ˢ Metric.ball (0 : ℂ) c) ∧
          (∀ p : X × ℂ, p.1 ∈ U → ‖p.2‖ < 1 → G p = g p) ∧
          Work.CR.Flat.holderNorm k α G (U ×ˢ Metric.ball (0 : ℂ) c)
            ≤ ENNReal.ofReal (C k) * Work.CR.Flat.holderNorm k α g (U ×ˢ Metric.ball (0 : ℂ) 1) := by
  obtain ⟨C, hCpos, hC⟩ := Work.NN.DiscRadial.disc_ext_holderNorm_le (X := X) hα0 hα1 hc
  refine ⟨C, hCpos, fun k U g hU hg hfin => ?_⟩
  have hs := Work.NN.DiscRadial.disc_ext_contDiffOn (X := X) hα0 hU hc hg hfin
  exact ⟨discExt k (discWt k) discScale g, hs,
    fun p _ hlt => discExt_of_norm_lt_one hlt,
    hC k U g hU hg hfin hs⟩

/-- The `DiscExt` predicate of `Submission/Work/NN/Final/DiscExtDefs.lean` holds for every
`α ∈ (0,1)` and `c > 1`, with the explicit radial Seeley construction as the extension. -/
theorem discExt_property {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {c : ℝ} (hc : 1 < c) :
    DiscExt α c := fun X _ _ => one_sided_disc_extension hα0 hα1 hc

end Work.NN.Final
