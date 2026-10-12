import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB2.DvApriori.BandDefs
import Submission.Work.BoseFixB2.DvApriori.tBamp_pair_fixed_p_zero
import Submission.Work.BoseFixB2.Sector.aQ_sym_box
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.Analysis.BoseBand

/-!
# `Work.Analysis.BoseBand.tBamp_pair_fixed_p_zero`

For a fixed momentum `p`, the box integral of
`indU ℓ 0 (x j) · Re[ star (tBamp χ₀ p W j x) · tBamp χ₀ p V j x ]`, with `χ₀ = bsWin ℓ 0`,
vanishes as soon as `hpeel` holds, i.e. as soon as

    ∫_{abox n ℓ} indU ℓ 0 (x j) · W (x_{j←z}) · V (x_{j←z'}) = 0   for all z, z' .

Mathematically: expanding both amplitudes `tBamp χ₀ p Φ j x = ∫_{acube ℓ} χ₀(z) e^{-i⟪p,z⟫}
Φ(x_{j←z}) dz` (the window is supported on the box) and applying Fubini to the resulting
`(x, z, z')`-integral (joint integrability from compact support + continuity), the double integral
of the exponential factor `χ₀(z)χ₀(z')e^{i⟪p,z⟫}e^{-i⟪p,z'⟫}` — a constant in `x` — against
`∫_x indU ℓ 0 (x j) W(x_{j←z})V(x_{j←z'}) = 0` is zero.

The same statement (with the identical proof, for the window `bsWin ℓ 0 = chiScale ℓ`) has already
been committed to the shared library as `Work.BoseFixB2.DvApriori.tBamp_pair_fixed_p_zero`; this
module re-exports it under the requested name, exactly as
`Work.Analysis.BoseBand.swap_p_abox_tBamp_pair` builds on its `DvApriori` namesake. -/
theorem tBamp_pair_fixed_p_zero {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {j k : Fin n} (hjk : j ≠ k)
    {W V : Submission.BoseGases.X n → ℝ} (hW : Continuous W) (hV : Continuous V)
    (hpeel : ∀ z z' : EuclideanSpace ℝ (Fin 3), (∫ x in Submission.BoseGases.abox n ℓ,
        Work.BoseKinLoc.indU ℓ 0 (x j)
          * (W (Function.update x j z) * V (Function.update x j z'))) = 0)
    (p : EuclideanSpace ℝ (Fin 3)) :
    (∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x j) *
      (star (Work.SmallBoxTBWord.tBamp (Work.BSKinetic.bsWin ℓ 0) p W j x) *
        Work.SmallBoxTBWord.tBamp (Work.BSKinetic.bsWin ℓ 0) p V j x).re) = 0 :=
  Work.BoseFixB2.DvApriori.tBamp_pair_fixed_p_zero hℓ hjk hW hV hpeel p

end Work.Analysis.BoseBand
