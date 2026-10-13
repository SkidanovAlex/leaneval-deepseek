import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongEps.HkMem_of_tendsto
import Submission.Work.FTS.EllExist.Honesty.hkMem_of_liminf_slice
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd
import Submission.Work.FTS_EllLimOK.aemeasurable_uncurry_of_tendsto_Q0
import Submission.Work.FTS_EllLimOK.aemeasurable_slice_of_tendsto_Ioo

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `ℋ³`-membership and `ℋ³`-bound of a slot-wise limit

`Work.FTS.StrongEps.HkMem_of_tendsto` proves this descent statement for a limit `f` which is
itself assumed `C³` on the open quadrant.  The regularity of `f` is used there **only** through
the measurability of the limit integrand (`aesm_slice_HkIntegrand_of_contDiffOn` /
`aesm_integral_HkIntegrand_of_contDiffOn`).  Here the regularity hypothesis on `f` is dropped:
the measurability is recovered from the *slot-wise convergence* of the approximants, each of
which is `C^∞` on the open quadrant.

The route is the Fatou engine `Work.FTS.EllExist.Honesty.hkMem_of_liminf_slice`:

* the open quadrant `Q0` is conull for `dz dθ` on `Iz × Iθ`, so the boundary values of `f`
  (about which nothing is known) are irrelevant; on `Q0` every slot of `f` is a pointwise limit
  of slots of `fs n`, and these are continuous there, whence
  `Work.FTS_EllLimOK.aemeasurable_uncurry_of_tendsto_Q0` gives the joint a.e. measurability of
  `HkIntegrand α 3 f` (a finite sum of squares of slots), hence — via
  `AEStronglyMeasurable.integral_prod_right'` — the a.e. measurability of its `θ`-integral;
* `Work.FTS_EllLimOK.aemeasurable_slice_of_tendsto_Ioo` gives the a.e. measurability of each
  angular slice (at `z = 0` the integrand vanishes identically);
* the pointwise convergence of the slots on `Q0` upgrades to that of the integrand
  (`HkIntegrand_tendsto_of_mixed`), which on the conull set `Ioo 0 (π/2)` turns the `liminf`
  domination into an equality.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Real Topology

namespace Work.FTS.StrongEps.E5G

set_option maxHeartbeats 800000

theorem hkMem_three_of_slot_tendsto {α R : ℝ} {fs : ℕ → ℝ → ℝ → ℝ} {f : ℝ → ℝ → ℝ}
    (hfs : ∀ n : ℕ, Work.Spaces.HkMem α 3 (fs n))
    (hb : ∀ n : ℕ, Work.Spaces.HkNorm α 3 (fs n) ≤ R)
    (hsm : ∀ n : ℕ, ∀ m : ℕ, ContDiffOn ℝ m (Function.uncurry (fs n)) Work.FTS.EllipticEst.Q0)
    (hconv : ∀ (j i : ℕ), j + i ≤ 3 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed j i (fs n) z θ) Filter.atTop
        (nhds (Work.Spaces.mixed j i f z θ)))
    (hz : ∀ z ∈ Work.Spaces.Iz, ∃ Bz : ℝ, ∀ n : ℕ,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 3 (fs n) z θ) ≤ Bz) :
    Work.Spaces.HkMem α 3 f ∧ Work.Spaces.HkNorm α 3 f ≤ R := by
  classical
  -- the approximants are `C³` (indeed `C^∞`) on the open quadrant
  have hsm3 : ∀ n : ℕ, ContDiffOn ℝ (3 : ℕ) (Function.uncurry (fs n)) Work.FTS.EllipticEst.Q0 :=
    fun n => hsm n 3
  -- slot-wise convergence upgrades to convergence of the `ℋ³`-integrand, on `Q0`
  have hconvInt : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Filter.Tendsto (fun n : ℕ => Work.Spaces.HkIntegrand α 3 (fs n) z θ) Filter.atTop
        (nhds (Work.Spaces.HkIntegrand α 3 f z θ)) :=
    fun z θ hzθ => Work.FTS.StrongEps.HkIntegrand_tendsto_of_mixed
      (α := α) (k := 3) (F := f) (Fs := fs) (z := z) (θ := θ)
      (fun j i hji => hconv j i hji z θ hzθ)
  -- continuity of the angular slice of the integrand of an approximant, for `z > 0`
  have hsliceCont : ∀ (n : ℕ) (z : ℝ), 0 < z →
      ContinuousOn (fun θ => Work.Spaces.HkIntegrand α 3 (fs n) z θ) (Set.Ioo 0 (π / 2)) := by
    intro n z hzpos
    have hc := Work.FTS.StrongEps.continuousOn_HkIntegrand_fin α 3 (fs n) (hsm3 n)
    have hcomp := hc.comp (f := fun θ : ℝ => (z, θ)) (s := Set.Ioo 0 (π / 2))
      (continuousOn_const.prodMk continuousOn_id)
      (fun θ hθ => Work.FTS.EllipticEst.mem_Q0.mpr ⟨hzpos, hθ.1, hθ.2⟩)
    simpa [Function.comp_def] using hcomp
  -- joint a.e. measurability of the integrand of the limit, as a pointwise limit on `Q0`
  have hEM : AEMeasurable
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 3 f p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.FTS_EllLimOK.aemeasurable_uncurry_of_tendsto_Q0
      (un := fun n z θ => Work.Spaces.HkIntegrand α 3 (fs n) z θ)
      (u := fun z θ => Work.Spaces.HkIntegrand α 3 f z θ)
      (fun n => Work.FTS.StrongEps.continuousOn_HkIntegrand_fin α 3 (fs n) (hsm3 n))
      hconvInt
  -- hence the a.e. strong measurability of its `θ`-integral
  have houter : MeasureTheory.AEStronglyMeasurable
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 3 f z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    hEM.aestronglyMeasurable.integral_prod_right'
  -- and of each angular slice
  have hsl : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.AEStronglyMeasurable
      (fun θ => Work.Spaces.HkIntegrand α 3 f z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    intro z hz'
    rcases lt_or_eq_of_le (show (0 : ℝ) ≤ z from hz') with hzpos | hz0
    · exact (Work.FTS_EllLimOK.aemeasurable_slice_of_tendsto_Ioo
        (un := fun n θ => Work.Spaces.HkIntegrand α 3 (fs n) z θ)
        (u := fun θ => Work.Spaces.HkIntegrand α 3 f z θ)
        (fun n => hsliceCont n z hzpos)
        (fun θ hθ => hconvInt z θ ⟨hzpos, hθ.1, hθ.2⟩)).aestronglyMeasurable
    · subst hz0
      rw [show (fun θ => Work.Spaces.HkIntegrand α 3 f 0 θ) = fun _ : ℝ => (0 : ℝ) from
        funext fun θ => Work.FTS.StrongEps.HkIntegrand_eq_zero_at_z_zero α 3 f θ]
      exact aestronglyMeasurable_const
  -- the `liminf` domination of the limit integrand by the approximants, a.e. in `θ`
  have hae : ∀ z ∈ Work.Spaces.Iz, ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Work.Spaces.HkIntegrand α 3 f z θ
        ≤ Filter.liminf (fun n => Work.Spaces.HkIntegrand α 3 (fs n) z θ) Filter.atTop := by
    intro z hz'
    rcases lt_or_eq_of_le (show (0 : ℝ) ≤ z from hz') with hzpos | hz0
    · -- the endpoints `0`, `π/2` are null, and on the open interval the integrand converges
      have hμ : MeasureTheory.volume.restrict Work.Spaces.Iθ
          = MeasureTheory.volume.restrict (Set.Ioo 0 (π / 2)) :=
        (Measure.restrict_congr_set (MeasureTheory.Ioo_ae_eq_Icc
          (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := (π / 2)))).symm
      rw [hμ]
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo fun θ hθ => ?_
      have hc := hconvInt z θ ⟨hzpos, hθ.1, hθ.2⟩
      rw [hc.liminf_eq]
    · subst hz0
      filter_upwards with θ
      rw [Work.FTS.StrongEps.HkIntegrand_eq_zero_at_z_zero α 3 f θ,
        show (fun n : ℕ => Work.Spaces.HkIntegrand α 3 (fs n) 0 θ) = fun _ : ℕ => (0 : ℝ) from
          funext fun n => Work.FTS.StrongEps.HkIntegrand_eq_zero_at_z_zero α 3 (fs n) θ,
        Filter.liminf_const]
  -- the uniform `ℋ³`-bounds of the approximants, as squared norms
  have hbSq : ∀ n : ℕ, Work.Spaces.HkSq α 3 (fs n) ≤ R ^ 2 := by
    intro n
    have hsq : Work.Spaces.HkSq α 3 (fs n) = Work.Spaces.HkNorm α 3 (fs n) ^ 2 := by
      rw [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 3 (fs n))]
    rw [hsq]
    exact pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α 3 (fs n)) (hb n) 2
  -- Fatou, twice
  obtain ⟨hmemf, hsqle⟩ := Work.FTS.EllExist.Honesty.hkMem_of_liminf_slice
    (α := α) (k := 3) (f := f) (fs := fs) (C := R ^ 2) (sq_nonneg R)
    hfs hbSq hsl houter hae hz
  refine ⟨hmemf, ?_⟩
  have hR0 : 0 ≤ R := le_trans (Work.Spaces.HkNorm_nonneg α 3 (fs 0)) (hb 0)
  calc Work.Spaces.HkNorm α 3 f = Real.sqrt (Work.Spaces.HkSq α 3 f) := rfl
    _ ≤ Real.sqrt (R ^ 2) := Real.sqrt_le_sqrt hsqle
    _ = R := Real.sqrt_sq hR0

end Work.FTS.StrongEps.E5G
