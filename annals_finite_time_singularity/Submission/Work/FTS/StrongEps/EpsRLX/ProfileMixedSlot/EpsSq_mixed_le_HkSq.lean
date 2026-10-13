/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsRLX/ProfileMixedSlot/EpsSq_mixed_le_HkSq.lean`

**A mixed slot of an open-class `ℋ^k`-datum is in the `X`-space of the `ε`-scheme, with no more
size than the `ℋ^k`-norm.**

For `f : ℝ → ℝ → ℝ` which is `C^∞` on the open quadrant (`Work.FTS.EllipticEst.SmoothOpen f`,
the honest regularity class of the chapter) and honestly in `ℋ^k` (`Work.Spaces.HkMem α k f`),
and for every mixed slot `D_z^j D_θ^i f` with `1 ≤ i` and `i + j ≤ k`:

* `EpsMem α (D_z^jD_θ^i f)` — the weighted square `(D_z^jD_θ^i f · epsW α)²` is product-integrable
  on the domain `Iz × Iθ`;
* `EpsSq α (D_z^jD_θ^i f) ≤ HkSq α k f`.

The point is that the weight `epsW α z θ = w z / sin(2θ)^{γ/2}` of the `ε`-scheme (`EpsSpace.lean`)
and the mixed-block weight `Wt α z θ = w z · sin(2θ)^{-γ/2}` of `ℋ^k` (`Spaces/Defs.lean`) have the
*same square* on `Iθ` (`EpsSqTools.epsW_sq_eq`, `EpsSqTools.Wt_sq_eq_eps`), so the slot is literally
one summand of the (nonnegative) `ℋ^k`-integrand:

* the membership is the product-measure form of the product integrability of the slot, which is
  `Work.FTS.EllipticEst.AeSlotOneAe.Interp.integrable_uncurry_slot_mixed`;
* the size bound is `Work.FTS.StrongEps.EpsRLX.slot_mixed_le_HkSq` (the same slot dominated by
  `HkSq`) after replacing `epsW²` by `Wt²` inside the inner `θ`-integral.

Everything here is `sorry`-free.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsRLX.ProfileSlotCompare

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsRLX.ProfileMixedSlot

set_option autoImplicit false

/-! ## The two weights agree after squaring -/

/-- **The weighted square of a mixed slot does not depend on which of the two weights
(`epsW` of the `ε`-scheme, `Wt` of `ℋ^k`) is used**: at an angle `θ ∈ Iθ` they have the common
value `(D_z^jD_θ^i f)² · w(z)² · sin(2θ)^{-γ}`. -/
theorem mixed_epsW_sq_eq (α : ℝ) (f : ℝ → ℝ → ℝ) (j i : ℕ) {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.mixed j i f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2
      = (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 := by
  simp only [mul_pow, Work.FTS.StrongEps.EpsSqTools.epsW_sq_eq hθ,
    Work.FTS.StrongEps.EpsSqTools.Wt_sq_eq_eps hθ]

/-- The weight `epsW α z θ = w(z)/sin(2θ)^{γ/2}` of the `ε`-scheme agrees with the mixed-block
weight `Wt α z θ = w(z)·sin(2θ)^{-γ/2}` at every angle `θ ∈ Iθ`. -/
theorem epsW_eq_Wt_of_mem_Iθ {α z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.FTS.StrongEps.epsW α z θ = Work.Spaces.Wt α z θ := by
  have hs : 0 ≤ Real.sin (2 * θ) := Work.FTS.StrongEps.EpsSqTools.sin_two_nonneg_Iθ_eps hθ
  rw [Work.FTS.StrongEps.epsW, Work.Spaces.Wt, Work.Spaces.wTheta, div_eq_mul_inv,
    ← Real.rpow_neg hs]

/-! ## The domain measure -/

/-- The product of the two restricted measures on the domain `Iz × Iθ` is the restriction of the
volume of `ℝ × ℝ`. -/
theorem domain_restrict_eq :
    (volume : Measure (ℝ × ℝ)).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
      = (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ) := by
  rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_restrict]

/-- `EpsMem` re-expressed as integrability for the product of the two restricted measures on the
domain, `(volume.restrict Iz).prod (volume.restrict Iθ)` — the form in which the product
integrability of a slot is available. -/
theorem EpsMem_iff_integrable_prod {α : ℝ} {f : ℝ → ℝ → ℝ} :
    Work.FTS.StrongEps.EpsMem α f ↔ MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (f p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
  rw [Work.FTS.StrongEps.EpsMem, MeasureTheory.IntegrableOn, domain_restrict_eq]

/-! ## The main estimate -/

theorem EpsSq_mixed_le_HkSq {α : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ}
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α k f)
    {j i : ℕ} (hi : 1 ≤ i) (hij : i + j ≤ k) :
    Work.FTS.StrongEps.EpsMem α (Work.Spaces.mixed j i f) ∧
    Work.FTS.StrongEps.EpsSq α (Work.Spaces.mixed j i f) ≤ Work.Spaces.HkSq α k f := by
  have hsq : ∀ z θ, θ ∈ Work.Spaces.Iθ →
      (Work.Spaces.mixed j i f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2
        = (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 :=
    fun z θ hθ => mixed_epsW_sq_eq α f j i hθ
  refine ⟨?_, ?_⟩
  · -- the membership: product integrability of the slot, transported from `Wt` to `epsW`
    rw [EpsMem_iff_integrable_prod]
    have hprod := Work.FTS.EllipticEst.AeSlotOneAe.Interp.integrable_uncurry_slot_mixed
      hso hm j i hi hij
    refine hprod.congr ?_
    have hae : ∀ᵐ p ∂((volume.restrict Work.Spaces.Iz).prod
        (volume.restrict Work.Spaces.Iθ)), p ∈ Work.Spaces.Iz ×ˢ Work.Spaces.Iθ := by
      rw [← domain_restrict_eq]
      exact MeasureTheory.ae_restrict_mem (μ := (volume : Measure (ℝ × ℝ)))
        (measurableSet_Ici.prod measurableSet_Icc)
    filter_upwards [hae] with p hp
    simp only [Function.uncurry]
    exact (hsq p.1 p.2 (Set.mem_prod.mp hp).2).symm
  · -- the size bound: the slot is one summand of the `ℋ^k`-integrand
    obtain ⟨_, hle⟩ := Work.FTS.StrongEps.EpsRLX.slot_mixed_le_HkSq hso hm
      (j := j) (i := i) hi hij
    rw [Work.FTS.StrongEps.EpsSq]
    refine le_trans (le_of_eq ?_) hle
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with z
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem (s := Work.Spaces.Iθ) measurableSet_Icc]
      with θ hθ
    exact hsq z θ hθ

end Work.FTS.StrongEps.EpsRLX.ProfileMixedSlot
