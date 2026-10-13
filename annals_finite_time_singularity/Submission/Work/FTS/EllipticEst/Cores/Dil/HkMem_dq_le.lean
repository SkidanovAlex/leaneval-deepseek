/-
Copyright: work module for the Elgindi finite-time singularity project.

# The radial difference quotient of an `ℋ⁰`-datum

For `g` of class `C^∞` on the open quadrant whose radial derivative `D_z g = z ∂_z g` is
honestly in `ℋ⁰` and `c > 1`, the radial difference quotient

  `dq c g z θ = (g (c z) θ - g z θ)/(c - 1)`

is again in `ℋ⁰`, with squared `ℋ⁰`-norm bounded by `c³` times that of `D_z g`.

## The route

The fundamental theorem of calculus on the `z`-slice, followed by the substitution
`y = z u`, gives the *`u`-integral representation*

  `dq c g z θ = (c-1)⁻¹ ∫_1^c D_z g (z u) θ / u du`.

Cauchy–Schwarz on `[1,c]` (length `c-1`) then turns this into the *pointwise majorant*

  `HkIntegrand α 0 (dq c g) z θ ≤ Mdq α c g z θ`,
  `Mdq α c g z θ = (c-1)⁻¹ ∫_1^c u² HkIntegrand α 0 (D_z g) (z u) θ du`,

the point of the factor `u²` being the weight comparison `w z ≤ u² w (z u)` (`u ≥ 1`).

The majorant is then estimated in two steps:

* its `ℋ⁰`-lintegral is bounded by `(c+1)/2 ≤ c³` times that of `D_z g`: interchange the
  `(z,θ)`- and `u`-integrals (Tonelli) and substitute `y = z u` in the radial variable,
  which absorbs the `u²` into the Jacobian `u⁻¹`;
* its `θ`-slices and the `z`-integral of its slices are integrable, again by the
  `z u`-substitution, so that `HkMem_of_majorant` yields the `ℋ⁰`-membership.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.EllipticEst.Cores.Dil.DilBasic
import Submission.Work.FTS.EllipticEst.Cores.Dil.HkSqLimit
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.FTS.EllipticEst.AngSecond.lintegral_w_sq_shift_two_le
import Submission.Work.RPFresh.integral_mul_sq_le_sq_mul_sq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cores.Dil

set_option autoImplicit false
set_option maxHeartbeats 8000000

/-! ## The level-`0` radial majorant of the difference quotient -/

/-- The majorant `(c-1)⁻¹ ∫_1^c u² HkIntegrand α 0 (D_z g) (z u) θ du` of the level-`0`
integrand of the difference quotient. -/
def Mdq (α c : ℝ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  (c - 1)⁻¹ * ∫ u in (1 : ℝ)..c, u ^ 2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) (z * u) θ

theorem Iz_eq : Work.Spaces.Iz = Set.Ici (0:ℝ) := rfl

theorem Iθ_eq : Work.Spaces.Iθ = Set.Icc 0 (Real.pi / 2) := rfl

theorem Mdq_nonneg {α c : ℝ} {g : ℝ → ℝ → ℝ} (hc : 1 < c) (z θ : ℝ) :
    0 ≤ Mdq α c g z θ := by
  refine mul_nonneg (inv_nonneg.mpr (by linarith)) ?_
  refine intervalIntegral.integral_nonneg (le_of_lt hc) fun u hu => ?_
  exact mul_nonneg (by positivity)
    (Work.Spaces.HkIntegrand_nonneg α 0 (Work.Spaces.Dz g) (z * u) θ)

/-! ## The weight comparison `w z ≤ u² w (z u)` for `u ≥ 1` -/

theorem w_nonneg (z : ℝ) : 0 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w]
  exact div_nonneg (by positivity) (by positivity)

theorem w_sq_le_mul_four {z u : ℝ} (hz : 0 < z) (hu : 1 ≤ u) :
    (Work.Spaces.w z) ^ 2 ≤ u ^ 4 * (Work.Spaces.w (z * u)) ^ 2 := by
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have hle : (1 + z) ^ 2 ≤ (1 + z * u) ^ 2 := by
    have h1 : 1 + z ≤ 1 + z * u := by nlinarith [hz.le, hu]
    exact pow_le_pow_left₀ (by positivity) h1 2
  have hstep : Work.Spaces.w z ≤ u ^ 2 * Work.Spaces.w (z * u) := by
    have hzu : (z * u) ^ 2 ≠ 0 := pow_ne_zero 2 (mul_ne_zero (ne_of_gt hz) (ne_of_gt hu0))
    rw [Work.Spaces.w, Work.Spaces.w, show (z * u) ^ 2 = u ^ 2 * z ^ 2 from by ring]
    rw [div_le_iff₀ (by positivity)]
    field_simp
    nlinarith [hle]
  calc (Work.Spaces.w z) ^ 2 ≤ (u ^ 2 * Work.Spaces.w (z * u)) ^ 2 :=
        pow_le_pow_left₀ (w_nonneg z) hstep 2
    _ = u ^ 4 * (Work.Spaces.w (z * u)) ^ 2 := by ring

/-! ## The `u`-integral representation of the difference quotient -/

theorem dq_eq_intervalIntegral_div {g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g)
    {c z θ : ℝ} (hc : 1 < c) (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    dq c g z θ = (c - 1)⁻¹ * ∫ u in (1 : ℝ)..c, Work.Spaces.Dz g (z * u) θ / u := by
  have hcpos : 0 < c := lt_trans zero_lt_one hc
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hzc : z ≤ c * z := by nlinarith
  -- FTC on the `z`-slice
  have hderiv : ∀ s ∈ Set.uIcc z (c * z),
      HasDerivAt (fun s : ℝ => g s θ) (Work.Spaces.pz g s θ) s := by
    intro s hs
    rw [Set.uIcc_of_le hzc] at hs
    exact hg.hasDerivAt_slice hθ (lt_of_lt_of_le hz hs.1)
  have hcont : ContinuousOn (fun s : ℝ => Work.Spaces.pz g s θ) (Set.uIcc z (c * z)) := by
    rw [Set.uIcc_of_le hzc]
    exact ((hg.pz).curry_z hθ).continuousOn.mono fun s hs => lt_of_lt_of_le hz hs.1
  have hFTC : ∫ s in z..c * z, Work.Spaces.pz g s θ = g (c * z) θ - g z θ :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  -- the substitution `s = z u`
  have hsub : z * (∫ u in (1 : ℝ)..c, Work.Spaces.pz g (z * u) θ)
      = ∫ s in z..c * z, Work.Spaces.pz g s θ := by
    have h := intervalIntegral.smul_integral_comp_mul_left (a := (1:ℝ)) (b := c)
      (fun s : ℝ => Work.Spaces.pz g s θ) z
    simpa only [mul_one, mul_comm z c, smul_eq_mul] using h
  -- rewrite `pz` in terms of `Dz`
  have hpz : (∫ u in (1 : ℝ)..c, Work.Spaces.pz g (z * u) θ)
      = ∫ u in (1 : ℝ)..c, Work.Spaces.Dz g (z * u) θ / (z * u) := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    have hu1 : (1 : ℝ) ≤ u := by
      rw [Set.uIcc_of_le (le_of_lt hc)] at hu; exact hu.1
    have hu0 : u ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hu1)
    rw [Work.Spaces.Dz]
    field_simp
  have hcancel : z * (∫ u in (1 : ℝ)..c, Work.Spaces.Dz g (z * u) θ / (z * u))
      = ∫ u in (1 : ℝ)..c, Work.Spaces.Dz g (z * u) θ / u := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun u hu => ?_
    have hu1 : (1 : ℝ) ≤ u := by
      rw [Set.uIcc_of_le (le_of_lt hc)] at hu; exact hu.1
    have hu0 : u ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hu1)
    field_simp
  rw [show dq c g z θ = (g (c * z) θ - g z θ) / (c - 1) from rfl, ← hFTC, ← hsub, hpz, hcancel]
  field_simp

/-! ## Cauchy–Schwarz on an interval -/

theorem sq_intervalIntegral_le {F : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hF : IntervalIntegrable F MeasureTheory.volume a b)
    (hF2 : IntervalIntegrable (fun u => F u ^ 2) MeasureTheory.volume a b) :
    (∫ u in a..b, F u) ^ 2 ≤ (b - a) * ∫ u in a..b, F u ^ 2 := by
  have hF' : MeasureTheory.Integrable F (MeasureTheory.volume.restrict (Set.Ioc a b)) := by
    have h := intervalIntegrable_iff.mp hF
    rwa [Set.uIoc_of_le hab] at h
  have hF2' : MeasureTheory.Integrable (fun u => F u ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioc a b)) := by
    have h := intervalIntegrable_iff.mp hF2
    rwa [Set.uIoc_of_le hab] at h
  have hmu : (MeasureTheory.volume.restrict (Set.Ioc a b)) Set.univ ≠ ∞ := by
    rw [MeasureTheory.Measure.restrict_apply_univ, Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  have hone : MeasureTheory.Integrable (fun _ : ℝ => (1:ℝ) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioc a b)) := by
    simpa using (integrableOn_const (s := Set.Ioc a b) (C := (1:ℝ)) hmu (by simp))
  have hcs := Work.RPFresh.integral_mul_sq_le_sq_mul_sq
    (MeasureTheory.volume.restrict (Set.Ioc a b)) hF'.aestronglyMeasurable
    aestronglyMeasurable_const hF2' hone
  have hleft : (∫ u in a..b, F u) = ∫ u in Set.Ioc a b, F u :=
    intervalIntegral.integral_of_le hab
  have hright : (∫ u in a..b, F u ^ 2) = ∫ u in Set.Ioc a b, F u ^ 2 :=
    intervalIntegral.integral_of_le hab
  have honeval : (∫ u in Set.Ioc a b, (1:ℝ) ^ 2) = b - a := by
    rw [MeasureTheory.integral_const, smul_eq_mul, MeasureTheory.Measure.real,
      MeasureTheory.Measure.restrict_apply_univ, Real.volume_Ioc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
    ring
  have hmain : (∫ u in Set.Ioc a b, F u) ^ 2
      ≤ (∫ u in Set.Ioc a b, F u ^ 2) * (b - a) := by
    rw [← honeval]
    simpa only [mul_one] using hcs
  rw [hleft, hright]
  rw [mul_comm]
  exact hmain

/-! ## The level-`0` integrand as a product of squares -/

theorem HkIntegrand_sq_eq {α : ℝ} (f : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.HkIntegrand α 0 f z θ
      = (f z θ) ^ 2 * ((Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  rw [HkIntegrand_zero_apply, mul_pow, div_pow,
    show (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ 2
        = Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) * Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)
      from by ring,
    ← Real.rpow_add hs,
    show Work.Spaces.eta / 2 + Work.Spaces.eta / 2 = Work.Spaces.eta from by ring,
    div_eq_mul_inv, ← Real.rpow_neg (le_of_lt hs)]

theorem HkIntegrand_sin_eq_zero {α : ℝ} (f : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hs : Real.sin (2 * θ) = 0) : Work.Spaces.HkIntegrand α 0 f z θ = 0 := by
  rw [HkIntegrand_zero_apply]
  have h0 : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) = 0 := by
    rw [hs, Real.zero_rpow]
    norm_num [Work.Spaces.eta]
  rw [h0]
  simp

theorem continuousOn_w : ContinuousOn Work.Spaces.w (Set.Ioi (0:ℝ)) := by
  have h : (Work.Spaces.w : ℝ → ℝ) = fun z : ℝ => (1 + z) ^ 2 / z ^ 2 := by
    funext z; rfl
  rw [h]
  exact ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
    (continuousOn_id.pow 2) (fun z hz => pow_ne_zero 2 (ne_of_gt hz))

/-! ## The pointwise majorisation -/

theorem HkIntegrand_dq_le_Mdq {α c : ℝ} {g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (hc : 1 < c) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 0 (dq c g) z θ ≤ Mdq α c g z θ := by
  have hc1 : (1:ℝ) ≤ c := le_of_lt hc
  have hcne : c - 1 ≠ 0 := ne_of_gt (by linarith)
  intro z hz θ hθ
  rcases eq_or_lt_of_le (show (0:ℝ) ≤ z from hz) with hz0 | hzpos
  · -- `z = 0`
    subst hz0
    rw [Work.FTS.LocData.HkIntegrand_zero_fst]
    refine le_of_eq ?_
    rw [Mdq]
    have h0 : (fun u : ℝ => u ^ 2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) (0 * u) θ)
        = fun _ : ℝ => 0 := by
      funext u
      rw [zero_mul, Work.FTS.LocData.HkIntegrand_zero_fst, mul_zero]
    rw [h0, intervalIntegral.integral_zero, mul_zero]
  · rcases eq_or_lt_of_le hθ.1 with hθ0 | hθpos
    · -- `θ = 0`
      subst hθ0
      have hs : Real.sin (2 * (0:ℝ)) = 0 := by simp
      rw [HkIntegrand_sin_eq_zero (dq c g) hs]
      refine le_of_eq ?_
      rw [Mdq]
      have h0 : (fun u : ℝ => u ^ 2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) (z * u) 0)
          = fun _ : ℝ => 0 := by
        funext u
        rw [HkIntegrand_sin_eq_zero (Work.Spaces.Dz g) hs, mul_zero]
      rw [h0, intervalIntegral.integral_zero, mul_zero]
    · rcases lt_or_eq_of_le hθ.2 with hθlt | hθpi
      · -- interior case
        have hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθpos, hθlt⟩
        have hs : 0 < Real.sin (2 * θ) :=
          Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ'.1])
            (by linarith [hθ'.2, Real.pi_pos])
        have hsn : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := Real.rpow_nonneg hs.le _
        have hFTC := dq_eq_intervalIntegral_div hg hc hzpos hθ'
        -- the level-`0` integrand of `D_z g`, in product form
        have hcoe : ∀ y : ℝ, Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) y θ
            = (Work.Spaces.Dz g y θ) ^ 2
              * ((Work.Spaces.w y) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) :=
          fun y => HkIntegrand_sq_eq (Work.Spaces.Dz g) hθ'
        have hmap : ∀ u ∈ Set.Icc (1:ℝ) c, 0 < z * u := fun u hu =>
          mul_pos hzpos (lt_of_lt_of_le zero_lt_one (Set.mem_Icc.mp hu).1)
        -- continuity of the relevant integrands on `[1,c]`
        have hcontDz : ContinuousOn (fun u : ℝ => Work.Spaces.Dz g (z * u) θ) (Set.Icc (1:ℝ) c) :=
          ((hg.Dz).curry_z hθ').continuousOn.comp (by fun_prop) hmap
        have hcontF : ContinuousOn (fun u : ℝ => Work.Spaces.Dz g (z * u) θ / u)
            (Set.Icc (1:ℝ) c) :=
          hcontDz.div continuousOn_id fun u hu =>
            ne_of_gt (lt_of_lt_of_le zero_lt_one (Set.mem_Icc.mp hu).1)
        have hint1 : IntervalIntegrable (fun u : ℝ => Work.Spaces.Dz g (z * u) θ / u)
            MeasureTheory.volume 1 c := by
          exact (show ContinuousOn (fun u : ℝ => Work.Spaces.Dz g (z * u) θ / u)
              (Set.uIcc (1:ℝ) c) from by rw [Set.uIcc_of_le hc1]; exact hcontF).intervalIntegrable
        have hint2 : IntervalIntegrable
            (fun u : ℝ => (Work.Spaces.Dz g (z * u) θ / u) ^ 2) MeasureTheory.volume 1 c := by
          exact (show ContinuousOn (fun u : ℝ => (Work.Spaces.Dz g (z * u) θ / u) ^ 2)
              (Set.uIcc (1:ℝ) c) from by rw [Set.uIcc_of_le hc1]; exact hcontF.pow 2).intervalIntegrable
        have hcs := sq_intervalIntegral_le hc1 hint1 hint2
        -- the squared representation of `dq`
        have hdq2 : (dq c g z θ) ^ 2
            ≤ (c - 1)⁻¹ * ∫ u in (1:ℝ)..c, (Work.Spaces.Dz g (z * u) θ / u) ^ 2 := by
          rw [hFTC]
          calc ((c - 1)⁻¹ * ∫ u in (1:ℝ)..c, Work.Spaces.Dz g (z * u) θ / u) ^ 2
              = ((c - 1)⁻¹) ^ 2
                * (∫ u in (1:ℝ)..c, Work.Spaces.Dz g (z * u) θ / u) ^ 2 := by ring
            _ ≤ ((c - 1)⁻¹) ^ 2
                * ((c - 1) * ∫ u in (1:ℝ)..c, (Work.Spaces.Dz g (z * u) θ / u) ^ 2) :=
                mul_le_mul_of_nonneg_left hcs (by positivity)
            _ = (c - 1)⁻¹ * ∫ u in (1:ℝ)..c, (Work.Spaces.Dz g (z * u) θ / u) ^ 2 := by
                field_simp
        -- the majorant
        rw [HkIntegrand_sq_eq (dq c g) hθ', Mdq]
        calc (dq c g z θ) ^ 2 * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
            ≤ ((c - 1)⁻¹ * ∫ u in (1:ℝ)..c, (Work.Spaces.Dz g (z * u) θ / u) ^ 2)
                * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) :=
              mul_le_mul_of_nonneg_right hdq2 (by positivity)
          _ = (c - 1)⁻¹ * ∫ u in (1:ℝ)..c,
                ((Work.Spaces.Dz g (z * u) θ / u) ^ 2
                  * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) := by
              rw [intervalIntegral.integral_mul_const]
              ring
          _ ≤ (c - 1)⁻¹ * ∫ u in (1:ℝ)..c,
                u ^ 2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) (z * u) θ := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              have hcontHk : ContinuousOn (fun u : ℝ =>
                  Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) (z * u) θ)
                  (Set.Icc (1:ℝ) c) := by
                rw [show (fun u : ℝ => Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) (z * u) θ)
                    = fun u : ℝ => (Work.Spaces.Dz g (z * u) θ) ^ 2
                        * ((Work.Spaces.w (z * u)) ^ 2
                          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) from
                  funext fun u => hcoe (z * u)]
                exact (hcontDz.pow 2).mul
                  (((continuousOn_w.comp (by fun_prop) hmap).pow 2).mul continuousOn_const)
              have hcontR : ContinuousOn (fun u : ℝ =>
                  u ^ 2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) (z * u) θ)
                  (Set.Icc (1:ℝ) c) :=
                (continuousOn_id.pow 2).mul hcontHk
              have hintL : IntervalIntegrable (fun u : ℝ =>
                  (Work.Spaces.Dz g (z * u) θ / u) ^ 2
                    * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))
                  MeasureTheory.volume 1 c := by
                exact (show ContinuousOn (fun u : ℝ =>
                    (Work.Spaces.Dz g (z * u) θ / u) ^ 2
                      * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))
                    (Set.uIcc (1:ℝ) c) from by
                  rw [Set.uIcc_of_le hc1]; exact (hcontF.pow 2).mul continuousOn_const).intervalIntegrable
              have hintR : IntervalIntegrable (fun u : ℝ =>
                  u ^ 2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) (z * u) θ)
                  MeasureTheory.volume 1 c := by
                exact (show ContinuousOn (fun u : ℝ =>
                    u ^ 2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) (z * u) θ)
                    (Set.uIcc (1:ℝ) c) from by
                  rw [Set.uIcc_of_le hc1]; exact hcontR).intervalIntegrable
              refine intervalIntegral.integral_mono_on hc1 hintL hintR (fun u hu => ?_)
              have hu1 : (1:ℝ) ≤ u := hu.1
              have hu0 : u ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hu1)
              have hA : 0 ≤ (Work.Spaces.Dz g (z * u) θ) ^ 2
                  * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) / u ^ 2 :=
                div_nonneg (mul_nonneg (sq_nonneg _) hsn) (by positivity)
              have hkey := mul_le_mul_of_nonneg_right (w_sq_le_mul_four hzpos hu1) hA
              rw [hcoe (z * u)]
              calc (Work.Spaces.Dz g (z * u) θ / u) ^ 2
                    * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
                  = (Work.Spaces.w z) ^ 2
                    * ((Work.Spaces.Dz g (z * u) θ) ^ 2
                      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) / u ^ 2) := by ring
                _ ≤ (u ^ 4 * (Work.Spaces.w (z * u)) ^ 2)
                    * ((Work.Spaces.Dz g (z * u) θ) ^ 2
                      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) / u ^ 2) := hkey
                _ = u ^ 2 * ((Work.Spaces.Dz g (z * u) θ) ^ 2
                    * ((Work.Spaces.w (z * u)) ^ 2
                      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) := by
                    field_simp
      · -- `θ = π/2`
        subst hθpi
        have hs : Real.sin (2 * (Real.pi / 2)) = 0 := by
          rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
        rw [HkIntegrand_sin_eq_zero (dq c g) hs]
        refine le_of_eq ?_
        rw [Mdq]
        have h0 : (fun u : ℝ => u ^ 2 *
            Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) (z * u) (Real.pi / 2))
            = fun _ : ℝ => 0 := by
          funext u
          rw [HkIntegrand_sin_eq_zero (Work.Spaces.Dz g) hs, mul_zero]
        rw [h0, intervalIntegral.integral_zero, mul_zero]

/-! ## Measure bookkeeping on the quadrant -/

theorem quadMeasure_eq_restrict :
    quadMeasure = ((MeasureTheory.volume : Measure ℝ).prod MeasureTheory.volume).restrict
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  have hIz : (Work.Spaces.Iz : Set ℝ) =ᵐ[MeasureTheory.volume] Set.Ioi 0 :=
    (MeasureTheory.Ioi_ae_eq_Ici' (μ := MeasureTheory.volume) (a := (0:ℝ)) (by simp)).symm
  have hIθ : (Work.Spaces.Iθ : Set ℝ) =ᵐ[MeasureTheory.volume]
      Set.Ioo 0 (Real.pi / 2) :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume)).symm
  show (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) = _
  rw [MeasureTheory.Measure.prod_restrict]
  exact MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Measure.set_prod_ae_eq hIz hIθ)

/-- A function which is continuous on a conull set is a.e.-measurable. -/
theorem aemeasurable_of_continuousOn_of_ae_mem {α β : Type*} [TopologicalSpace α]
    [MeasurableSpace α] [OpensMeasurableSpace α] [TopologicalSpace β] [MeasurableSpace β]
    [BorelSpace β] {f : α → β} {s : Set α} {μ : MeasureTheory.Measure α} (hs : MeasurableSet s)
    (hae : ∀ᵐ x ∂μ, x ∈ s) (hf : ContinuousOn f s) : AEMeasurable f μ := by
  have h : AEMeasurable f (μ.restrict s) := hf.aemeasurable hs
  rwa [MeasureTheory.Measure.restrict_eq_self_of_ae_mem hae] at h

theorem aemeasurable_quad {F : ℝ × ℝ → ENNReal}
    (hF : ContinuousOn F (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    AEMeasurable F quadMeasure := by
  rw [quadMeasure_eq_restrict]
  exact aemeasurable_of_continuousOn_of_ae_mem ((isOpen_Ioi.prod isOpen_Ioo).measurableSet)
    (MeasureTheory.ae_restrict_mem ((isOpen_Ioi.prod isOpen_Ioo).measurableSet)) hF

theorem aemeasurable_theta_prod_Ioo {c : ℝ} {F : ℝ × ℝ → ENNReal}
    (hF : ContinuousOn F (Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Ioo (1:ℝ) c)) :
    AEMeasurable F ((MeasureTheory.volume.restrict Work.Spaces.Iθ).prod
      (MeasureTheory.volume.restrict (Set.Ioo (1:ℝ) c))) := by
  have hIθ : (Work.Spaces.Iθ : Set ℝ) =ᵐ[MeasureTheory.volume]
      Set.Ioo 0 (Real.pi / 2) :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume)).symm
  rw [MeasureTheory.Measure.prod_restrict]
  rw [MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Measure.set_prod_ae_eq hIθ (Filter.EventuallyEq.rfl))]
  exact aemeasurable_of_continuousOn_of_ae_mem
    ((isOpen_Ioo.prod isOpen_Ioo).measurableSet)
    (MeasureTheory.ae_restrict_mem ((isOpen_Ioo.prod isOpen_Ioo).measurableSet)) hF

theorem aemeasurable_quad_prod_Ioo {c : ℝ} {F : (ℝ × ℝ) × ℝ → ENNReal}
    (hF : ContinuousOn F
      ((Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) ×ˢ Set.Ioo (1:ℝ) c)) :
    AEMeasurable F (quadMeasure.prod
      (MeasureTheory.volume.restrict (Set.Ioo (1:ℝ) c))) := by
  have hIz : (Work.Spaces.Iz : Set ℝ) =ᵐ[MeasureTheory.volume] Set.Ioi 0 :=
    (MeasureTheory.Ioi_ae_eq_Ici' (μ := MeasureTheory.volume) (a := (0:ℝ)) (by simp)).symm
  have hIθ : (Work.Spaces.Iθ : Set ℝ) =ᵐ[MeasureTheory.volume]
      Set.Ioo 0 (Real.pi / 2) :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume)).symm
  show AEMeasurable F (((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)).prod
      (MeasureTheory.volume.restrict (Set.Ioo (1:ℝ) c)))
  rw [MeasureTheory.Measure.prod_restrict, MeasureTheory.Measure.prod_restrict]
  rw [MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Measure.set_prod_ae_eq
      (MeasureTheory.Measure.set_prod_ae_eq hIz hIθ) (Filter.EventuallyEq.rfl))]
  exact aemeasurable_of_continuousOn_of_ae_mem
    (((isOpen_Ioi.prod isOpen_Ioo).prod isOpen_Ioo).measurableSet)
    (MeasureTheory.ae_restrict_mem
      (((isOpen_Ioi.prod isOpen_Ioo).prod isOpen_Ioo).measurableSet)) hF

/-! ## Change of variables for the lower Lebesgue integral -/

theorem lintegral_comp_mul (H : ℝ → ENNReal) {k : ℝ} (hk : 0 < k) :
    (∫⁻ y, H (k * y)) = ENNReal.ofReal k⁻¹ * ∫⁻ y, H y := by
  have hk0 : k ≠ 0 := ne_of_gt hk
  let e : ℝ ≃ᵐ ℝ := (Homeomorph.mulLeft₀ k hk0).toMeasurableEquiv
  have he : ⇑e = (fun z : ℝ => k * z) := rfl
  have hmap : Measure.map (⇑e) MeasureTheory.volume
      = ENNReal.ofReal k⁻¹ • MeasureTheory.volume := by
    rw [he, Real.map_volume_mul_left hk0, abs_of_pos (inv_pos.mpr hk)]
  calc ∫⁻ y, H (k * y) = ∫⁻ y, H (e y) := by rw [he]
    _ = ∫⁻ y, H y ∂(Measure.map (⇑e) MeasureTheory.volume) :=
        (lintegral_map_equiv H e).symm
    _ = ∫⁻ y, H y ∂(ENNReal.ofReal k⁻¹ • MeasureTheory.volume) := by rw [hmap]
    _ = ENNReal.ofReal k⁻¹ * ∫⁻ y, H y := by
        rw [MeasureTheory.lintegral_smul_measure, smul_eq_mul]

theorem lintegral_Ioo_comp_mul {G : ℝ → ENNReal} {k a b : ℝ} (hk : 0 < k) :
    (∫⁻ y in Set.Ioo a b, G (k * y))
      = ENNReal.ofReal k⁻¹ * ∫⁻ y in Set.Ioo (k * a) (k * b), G y := by
  have hmem : ∀ y : ℝ, y ∈ Set.Ioo a b ↔ k * y ∈ Set.Ioo (k * a) (k * b) := by
    intro y
    simp only [Set.mem_Ioo]
    exact ⟨fun h => ⟨by nlinarith [h.1, hk], by nlinarith [h.2, hk]⟩,
      fun h => ⟨by nlinarith [h.1, hk], by nlinarith [h.2, hk]⟩⟩
  have hind : ∀ y : ℝ, (Set.Ioo a b).indicator (fun y => G (k * y)) y
      = (Set.Ioo (k * a) (k * b)).indicator G (k * y) := by
    intro y
    by_cases hy : y ∈ Set.Ioo a b
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem ((hmem y).mp hy)]
    · rw [Set.indicator_of_notMem hy]
      by_cases h2 : k * y ∈ Set.Ioo (k * a) (k * b)
      · exact absurd ((hmem y).mpr h2) hy
      · rw [Set.indicator_of_notMem h2]
  calc (∫⁻ y in Set.Ioo a b, G (k * y))
      = ∫⁻ y, (Set.Ioo a b).indicator (fun y => G (k * y)) y :=
        (MeasureTheory.lintegral_indicator measurableSet_Ioo _).symm
    _ = ∫⁻ y, (Set.Ioo (k * a) (k * b)).indicator G (k * y) :=
        MeasureTheory.lintegral_congr hind
    _ = ENNReal.ofReal k⁻¹ * ∫⁻ y, (Set.Ioo (k * a) (k * b)).indicator G y :=
        lintegral_comp_mul _ hk
    _ = ENNReal.ofReal k⁻¹ * ∫⁻ y in Set.Ioo (k * a) (k * b), G y := by
        rw [MeasureTheory.lintegral_indicator measurableSet_Ioo]

/-! ## The interval-integral bridge -/

theorem ofReal_intervalIntegral_eq_lintegral {F : ℝ → ℝ} {c : ℝ} (hc : 1 < c)
    (hF : ContinuousOn F (Set.Icc (1:ℝ) c)) (hnn : ∀ u ∈ Set.Icc (1:ℝ) c, 0 ≤ F u) :
    ENNReal.ofReal (∫ u in (1:ℝ)..c, F u)
      = ∫⁻ u in Set.Ioo (1:ℝ) c, ENNReal.ofReal (F u) := by
  have hio : MeasureTheory.IntegrableOn F (Set.Ioc (1:ℝ) c) MeasureTheory.volume :=
    (hF.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  have hnn' : ∀ᵐ u ∂(MeasureTheory.volume.restrict (Set.Ioc (1:ℝ) c)), 0 ≤ F u := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with u hu
    exact hnn u (Set.Ioc_subset_Icc_self hu)
  rw [intervalIntegral.integral_of_le hc.le]
  rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hio hnn']
  show (∫⁻ u, ENNReal.ofReal (F u) ∂(MeasureTheory.volume.restrict (Set.Ioc (1:ℝ) c)))
      = ∫⁻ u in Set.Ioo (1:ℝ) c, ENNReal.ofReal (F u)
  rw [← MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioo_ae_eq_Ioc (a := (1:ℝ)) (b := c))]

/-! ## The `u`-substitution of the majorant -/

theorem HkIntegrand_zero_continuousOn {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
  (hg.Dz).continuousOn_HkIntegrand α 0

theorem lintegral_shift_quad {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g) {u : ℝ} (hu : 0 < u) :
    (∫⁻ p, ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) (p.1 * u) p.2)
        ∂quadMeasure)
      = ENNReal.ofReal u⁻¹ * ∫⁻ p, ENNReal.ofReal
          (Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) p.1 p.2) ∂quadMeasure := by
  have hc1 : ContinuousOn (fun p : ℝ × ℝ => ENNReal.ofReal
      (Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) p.1 p.2))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    ENNReal.continuous_ofReal.comp_continuousOn (HkIntegrand_zero_continuousOn hg)
  have hφ : ContinuousOn (fun p : ℝ × ℝ => (p.1 * u, p.2))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    ((continuous_fst.mul continuous_const).prodMk continuous_snd).continuousOn
  have hc2 : ContinuousOn (fun p : ℝ × ℝ => ENNReal.ofReal
      (Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) (p.1 * u) p.2))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    ENNReal.continuous_ofReal.comp_continuousOn
      ((HkIntegrand_zero_continuousOn hg).comp hφ
        (fun p hp => ⟨mul_pos hp.1 hu, hp.2⟩))
  have hm1 := aemeasurable_quad hc1
  have hm2 := aemeasurable_quad hc2
  have hμz : (MeasureTheory.volume.restrict Work.Spaces.Iz)
      = MeasureTheory.volume.restrict (Set.Ioi (0:ℝ)) := by
    show MeasureTheory.volume.restrict (Set.Ici (0:ℝ)) = _
    exact (MeasureTheory.restrict_Ioi_eq_restrict_Ici (a := (0:ℝ))).symm
  rw [MeasureTheory.lintegral_prod _ hm2, MeasureTheory.lintegral_prod _ hm1]
  have hcongr : (∫⁻ z in Set.Ioi (0:ℝ), ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) (z * u) θ))
      = ∫⁻ z in Set.Ioi (0:ℝ), ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) (u * z) θ) :=
    MeasureTheory.lintegral_congr fun z => MeasureTheory.lintegral_congr fun θ => by rw [mul_comm]
  rw [hμz, hcongr, Work.FTS.EllipticEst.AngSecond.lintegral_Ioi_comp_mul_pos u hu
    (fun z : ℝ => ∫⁻ θ in Work.Spaces.Iθ,
      ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) z θ))]

/-! ## The `ofReal` expansion of the majorant -/

theorem continuousOn_u_majorant {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g) {c z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    ContinuousOn (fun u : ℝ => u ^ 2
        * Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) (z * u) θ) (Set.Icc (1:ℝ) c) := by
  have hmap : ∀ u ∈ Set.Icc (1:ℝ) c, 0 < z * u := fun u hu =>
    mul_pos hz (lt_of_lt_of_le zero_lt_one (Set.mem_Icc.mp hu).1)
  have h1 : ContinuousOn (fun u : ℝ => (Work.Spaces.Dz g (z * u) θ) ^ 2) (Set.Icc (1:ℝ) c) :=
    (((hg.Dz).curry_z hθ).continuousOn.pow 2).comp (by fun_prop) hmap
  have h2 : ContinuousOn (fun u : ℝ => (Work.Spaces.w (z * u)) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) (Set.Icc (1:ℝ) c) :=
    ((continuousOn_w.comp (by fun_prop) hmap).pow 2).mul continuousOn_const
  rw [show (fun u : ℝ => u ^ 2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) (z * u) θ)
      = fun u : ℝ => u ^ 2 * ((Work.Spaces.Dz g (z * u) θ) ^ 2
          * ((Work.Spaces.w (z * u)) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) from
    funext fun u => by rw [HkIntegrand_sq_eq (Work.Spaces.Dz g) hθ]]
  exact (continuousOn_id.pow 2).mul (h1.mul h2)

theorem ofReal_Mdq_eq {α c : ℝ} {g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (hc : 1 < c) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    ENNReal.ofReal (Mdq α c g z θ)
      = ENNReal.ofReal ((c - 1)⁻¹) * ∫⁻ u in Set.Ioo (1:ℝ) c,
          ENNReal.ofReal (u ^ 2
            * Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) (z * u) θ) := by
  have hnn : ∀ u ∈ Set.Icc (1:ℝ) c, 0 ≤ u ^ 2
      * Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) (z * u) θ := fun u _ =>
    mul_nonneg (by positivity) (Work.Spaces.HkIntegrand_nonneg α 0 (Work.Spaces.Dz g) (z * u) θ)
  rw [Mdq, ENNReal.ofReal_mul (inv_nonneg.mpr (by linarith)),
    ofReal_intervalIntegral_eq_lintegral hc (continuousOn_u_majorant hg hz hθ) hnn]

/-- The `ofReal` expansion of the majorant on the whole quadrant. -/
theorem ofReal_Mdq_eq_Iθ {α c : ℝ} {g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (hc : 1 < c) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      ENNReal.ofReal (Mdq α c g z θ)
        = ENNReal.ofReal ((c - 1)⁻¹) * ∫⁻ u in Set.Ioo (1:ℝ) c,
            ENNReal.ofReal (u ^ 2
              * Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) (z * u) θ) := by
  have hc1 : (1:ℝ) ≤ c := le_of_lt hc
  intro z hz θ hθ
  have hslicezero : ∀ θ' : ℝ, Real.sin (2 * θ') = 0 →
      (fun u : ℝ => ENNReal.ofReal (u ^ 2 *
        Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) (z * u) θ')) = fun _ : ℝ => 0 := by
    intro θ' hs
    funext u
    rw [HkIntegrand_sin_eq_zero (Work.Spaces.Dz g) hs, mul_zero, ENNReal.ofReal_zero]
  have hMzero : ∀ θ' : ℝ, Real.sin (2 * θ') = 0 → Mdq α c g z θ' = 0 := by
    intro θ' hs
    rw [Mdq]
    have hzero : (fun u : ℝ => u ^ 2 *
        Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) (z * u) θ') = fun _ : ℝ => 0 := by
      funext u; rw [HkIntegrand_sin_eq_zero (Work.Spaces.Dz g) hs, mul_zero]
    rw [hzero, intervalIntegral.integral_zero, mul_zero]
  rcases eq_or_lt_of_le (show (0:ℝ) ≤ z from hz) with hz0 | hzpos
  · subst hz0
    have h1 : Mdq α c g 0 θ = 0 := by
      rw [Mdq]
      have hzero : (fun u : ℝ => u ^ 2 *
          Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) (0 * u) θ) = fun _ : ℝ => 0 := by
        funext u; rw [zero_mul, Work.FTS.LocData.HkIntegrand_zero_fst, mul_zero]
      rw [hzero, intervalIntegral.integral_zero, mul_zero]
    have h2 : (∫⁻ u in Set.Ioo (1:ℝ) c, ENNReal.ofReal (u ^ 2 *
        Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) (0 * u) θ)) = 0 := by
      have hzero : (fun u : ℝ => ENNReal.ofReal (u ^ 2 *
          Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) (0 * u) θ)) = fun _ : ℝ => 0 := by
        funext u
        rw [zero_mul, Work.FTS.LocData.HkIntegrand_zero_fst, mul_zero, ENNReal.ofReal_zero]
      rw [hzero, MeasureTheory.lintegral_zero]
    rw [h1, h2, mul_zero, ENNReal.ofReal_zero]
  · rcases eq_or_lt_of_le hθ.1 with hθ0 | hθpos
    · subst hθ0
      have hs : Real.sin (2 * (0:ℝ)) = 0 := by simp
      rw [hMzero 0 hs, MeasureTheory.lintegral_congr (fun u => congrFun (hslicezero 0 hs) u)]
      simp
    · rcases lt_or_eq_of_le hθ.2 with hθlt | hθpi
      · exact ofReal_Mdq_eq hg hc hzpos ⟨hθpos, hθlt⟩
      · subst hθpi
        have hs : Real.sin (2 * (Real.pi / 2)) = 0 := by
          rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
        rw [hMzero (Real.pi / 2) hs,
          MeasureTheory.lintegral_congr (fun u => congrFun (hslicezero (Real.pi / 2) hs) u)]
        simp

/-! ## The `ℋ⁰`-lintegral of the majorant -/

theorem lintegral_Mdq_le {α c : ℝ} {g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (hc : 1 < c)
    (hgmem : Work.Spaces.HkMem α 0 (Work.Spaces.Dz g)) :
    (∫⁻ p, ENNReal.ofReal (Mdq α c g p.1 p.2) ∂quadMeasure)
      ≤ ENNReal.ofReal (c ^ 3) * (∫⁻ p, ENNReal.ofReal
          (Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) p.1 p.2) ∂quadMeasure) := by
  have hc1 : (1:ℝ) ≤ c := le_of_lt hc
  set Y : ENNReal := ∫⁻ p, ENNReal.ofReal
      (Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) p.1 p.2) ∂quadMeasure with hY
  have hYne : Y ≠ ⊤ := by
    have hmeasDz : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal
        (Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) p.1 p.2)) quadMeasure :=
      aemeasurable_ofReal_HkIntegrand_of_continuousOn (HkIntegrand_zero_continuousOn hg)
    rw [hY, ← ofReal_HkSq_zero hgmem hmeasDz]
    exact ENNReal.ofReal_ne_top
  -- the triple integrand
  have hcont3 : ContinuousOn (fun q : (ℝ × ℝ) × ℝ => ENNReal.ofReal (q.2 ^ 2 *
      Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) (q.1.1 * q.2) q.1.2))
      ((Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) ×ˢ Set.Ioo (1:ℝ) c) := by
    refine ENNReal.continuous_ofReal.comp_continuousOn ?_
    refine ContinuousOn.mul (continuous_snd.pow 2).continuousOn ?_
    have hφ : ContinuousOn (fun q : (ℝ × ℝ) × ℝ => (q.1.1 * q.2, q.1.2))
        ((Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) ×ˢ Set.Ioo (1:ℝ) c) :=
      (((continuous_fst.fst.mul continuous_snd)).prodMk continuous_fst.snd).continuousOn
    exact (HkIntegrand_zero_continuousOn hg).comp hφ (fun q hq => by
      obtain ⟨hq1, hq2⟩ := hq
      obtain ⟨h2a, hq2b⟩ := Set.mem_Ioo.mp hq2
      exact ⟨mul_pos (Set.mem_Ioi.mp hq1.1) (by linarith), hq1.2⟩)
  have hmeas3 : AEMeasurable (fun q : (ℝ × ℝ) × ℝ => ENNReal.ofReal (q.2 ^ 2 *
      Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) (q.1.1 * q.2) q.1.2))
      (quadMeasure.prod (MeasureTheory.volume.restrict (Set.Ioo (1:ℝ) c))) :=
    aemeasurable_quad_prod_Ioo hcont3
  -- step 1: pointwise expansion of `ofReal (Mdq _ _)`, a.e. on the quadrant
  have hstep1 : (∫⁻ p, ENNReal.ofReal (Mdq α c g p.1 p.2) ∂quadMeasure)
      ≤ ∫⁻ p, ENNReal.ofReal ((c - 1)⁻¹) * (∫⁻ u in Set.Ioo (1:ℝ) c,
          ENNReal.ofReal (u ^ 2 *
            Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) (p.1 * u) p.2)) ∂quadMeasure := by
    refine MeasureTheory.lintegral_mono_ae ?_
    rw [quadMeasure_eq_restrict]
    refine MeasureTheory.ae_restrict_of_forall_mem
      (measurableSet_Ioi.prod measurableSet_Ioo) ?_
    intro p hp
    obtain ⟨hz, hθ0, hθ1⟩ := hp
    exact le_of_eq (ofReal_Mdq_eq_Iθ (α := α) hg hc p.1
      (le_of_lt (show (0:ℝ) < p.1 from hz)) p.2
      ⟨(show (0:ℝ) ≤ p.2 from hθ0.le), hθ1.le⟩)
  -- step 2: pull out the constant
  rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at hstep1
  -- step 3: Tonelli
  have hswap : (∫⁻ p, (∫⁻ u in Set.Ioo (1:ℝ) c, ENNReal.ofReal (u ^ 2 *
        Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) (p.1 * u) p.2)) ∂quadMeasure)
      = ∫⁻ u in Set.Ioo (1:ℝ) c, (∫⁻ p, ENNReal.ofReal (u ^ 2 *
        Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) (p.1 * u) p.2) ∂quadMeasure) :=
    MeasureTheory.lintegral_lintegral_swap hmeas3
  rw [hswap] at hstep1
  -- step 4: the `u`-integral
  have hstep4 : (∫⁻ u in Set.Ioo (1:ℝ) c, ∫⁻ p, ENNReal.ofReal (u ^ 2 *
        Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) (p.1 * u) p.2) ∂quadMeasure)
      = ∫⁻ u in Set.Ioo (1:ℝ) c, (ENNReal.ofReal (u ^ 2) * ENNReal.ofReal u⁻¹) * Y := by
    refine MeasureTheory.setLIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
    have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one (Set.mem_Ioo.mp hu).1.le
    calc (∫⁻ p, ENNReal.ofReal (u ^ 2 *
          Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) (p.1 * u) p.2) ∂quadMeasure)
        = ∫⁻ p, ENNReal.ofReal (u ^ 2) * ENNReal.ofReal
            (Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) (p.1 * u) p.2) ∂quadMeasure :=
          MeasureTheory.lintegral_congr fun p =>
            ENNReal.ofReal_mul (sq_nonneg u)
      _ = ENNReal.ofReal (u ^ 2) * ∫⁻ p, ENNReal.ofReal
            (Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) (p.1 * u) p.2) ∂quadMeasure :=
          MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal (u ^ 2) * ENNReal.ofReal u⁻¹ * Y := by
          have hs := lintegral_shift_quad (α := α) (g := g) hg hu0
          rw [hY, mul_assoc]
          exact congrArg (fun w => ENNReal.ofReal (u ^ 2) * w) hs
  rw [hstep4] at hstep1
  -- step 5: collapse `ofReal u² * ofReal u⁻¹ = ofReal u`
  have hstep5 : (∫⁻ u in Set.Ioo (1:ℝ) c,
        (ENNReal.ofReal (u ^ 2) * ENNReal.ofReal u⁻¹) * Y)
      = ENNReal.ofReal (∫ u in (1:ℝ)..c, u) * Y := by
    rw [MeasureTheory.lintegral_mul_const' _ _ hYne]
    congr 1
    have hpt : ∀ u ∈ Set.Ioo (1:ℝ) c,
        ENNReal.ofReal (u ^ 2) * ENNReal.ofReal u⁻¹ = ENNReal.ofReal u := by
      intro u hu
      have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one (Set.mem_Ioo.mp hu).1.le
      rw [← ENNReal.ofReal_mul (sq_nonneg u),
        show u ^ 2 * u⁻¹ = u from by field_simp]
    rw [MeasureTheory.setLIntegral_congr_fun measurableSet_Ioo hpt]
    exact (ofReal_intervalIntegral_eq_lintegral hc
      (continuousOn_id : ContinuousOn (fun u : ℝ => u) (Set.Icc (1:ℝ) c))
      (fun u hu => le_trans zero_le_one (Set.mem_Icc.mp hu).1)).symm
  rw [hstep5] at hstep1
  -- step 6: the constant `(c-1)⁻¹ ∫_1^c u du ≤ c³`
  refine hstep1.trans ?_
  have hval : (c - 1)⁻¹ * (∫ u in (1:ℝ)..c, u) ≤ c ^ 3 := by
    have hint : (∫ u in (1:ℝ)..c, u) ≤ ∫ u in (1:ℝ)..c, (c:ℝ) :=
      intervalIntegral.integral_mono_on hc.le continuousOn_id.intervalIntegrable
        intervalIntegrable_const (fun u hu => hu.2)
    have hconst : (∫ u in (1:ℝ)..c, (c:ℝ)) = (c - 1) * c := by
      rw [intervalIntegral.integral_const]
      simp [smul_eq_mul]
    rw [hconst] at hint
    have hc2 : c ≤ c ^ 3 := by nlinarith [sq_nonneg c, hc]
    have hpos : 0 < c - 1 := by linarith
    have : (c - 1) * c ≤ (c - 1) * c ^ 3 := mul_le_mul_of_nonneg_left hc2 hpos.le
    rw [inv_mul_le_iff₀ hpos]
    linarith
  calc ENNReal.ofReal ((c - 1)⁻¹) * (ENNReal.ofReal (∫ u in (1:ℝ)..c, u) * Y)
      = ENNReal.ofReal ((c - 1)⁻¹ * (∫ u in (1:ℝ)..c, u)) * Y := by
        rw [ENNReal.ofReal_mul (inv_nonneg.mpr (by linarith)), mul_assoc]
    _ ≤ ENNReal.ofReal (c ^ 3) * Y :=
        mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hval) bot_le

/-! ## The `θ`-slices of the majorant are integrable -/

theorem integrableOn_Mdq_slice {α c : ℝ} {g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (hc : 1 < c)
    (hgmem : Work.Spaces.HkMem α 0 (Work.Spaces.Dz g)) :
    ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ => Mdq α c g z θ)
      Work.Spaces.Iθ := by
  intro z hz
  rcases eq_or_lt_of_le (show (0:ℝ) ≤ z from hz) with hz0 | hzpos
  · subst hz0
    have h0 : ∀ θ, Mdq α c g 0 θ = 0 := by
      intro θ
      rw [Mdq]
      have hzero : (fun u : ℝ => u ^ 2 *
          Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) (0 * u) θ) = fun _ : ℝ => 0 := by
        funext u; rw [zero_mul, Work.FTS.LocData.HkIntegrand_zero_fst, mul_zero]
      rw [hzero, intervalIntegral.integral_zero, mul_zero]
    refine MeasureTheory.IntegrableOn.congr_fun MeasureTheory.integrableOn_zero
      (fun θ _ => (h0 θ).symm) (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)
  · have hcont2 : ContinuousOn (fun q : ℝ × ℝ => ENNReal.ofReal (q.2 ^ 2 *
        Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) (z * q.2) q.1))
        (Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Ioo (1:ℝ) c) := by
      refine ENNReal.continuous_ofReal.comp_continuousOn ?_
      refine ContinuousOn.mul (continuous_snd.pow 2).continuousOn ?_
      have hφ : ContinuousOn (fun q : ℝ × ℝ => (z * q.2, q.1))
          (Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Ioo (1:ℝ) c) :=
        ((continuous_const.mul continuous_snd).prodMk continuous_fst).continuousOn
      refine (HkIntegrand_zero_continuousOn hg).comp hφ ?_
      intro q hq
      obtain ⟨hq1, hq2⟩ := hq
      exact ⟨mul_pos hzpos (lt_trans zero_lt_one (Set.mem_Ioo.mp hq2).1), hq1⟩
    have hmeas2 : AEMeasurable (fun q : ℝ × ℝ => ENNReal.ofReal (q.2 ^ 2 *
        Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) (z * q.2) q.1))
        ((MeasureTheory.volume.restrict Work.Spaces.Iθ).prod
          (MeasureTheory.volume.restrict (Set.Ioo (1:ℝ) c))) :=
      aemeasurable_theta_prod_Ioo hcont2
    have hA : AEMeasurable (fun θ : ℝ => ENNReal.ofReal (Mdq α c g z θ))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      have h1 : AEMeasurable (fun θ : ℝ => ENNReal.ofReal ((c - 1)⁻¹) *
          ∫⁻ u in Set.Ioo (1:ℝ) c, ENNReal.ofReal (u ^ 2 *
            Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) (z * u) θ))
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
        (hmeas2.lintegral_prod_right).const_mul _
      refine h1.congr ?_
      filter_upwards [MeasureTheory.ae_restrict_mem
        (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)] with θ hθ
      exact (ofReal_Mdq_eq_Iθ (α := α) hg hc z hz θ hθ).symm
    have hfin : (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Mdq α c g z θ)) < ⊤ := by
      set G : ℝ → ENNReal := fun y => ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) y θ) with hG
      have hGbridge : (∫⁻ y in Set.Ioi (0:ℝ), G y)
          = ENNReal.ofReal (Work.Spaces.HkSq α 0 (Work.Spaces.Dz g)) := by
        have hmeasDz : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal
            (Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) p.1 p.2)) quadMeasure :=
          aemeasurable_ofReal_HkIntegrand_of_continuousOn (HkIntegrand_zero_continuousOn hg)
        have hμz : (MeasureTheory.volume.restrict Work.Spaces.Iz)
            = MeasureTheory.volume.restrict (Set.Ioi (0:ℝ)) := by
          show MeasureTheory.volume.restrict (Set.Ici (0:ℝ)) = _
          exact (MeasureTheory.restrict_Ioi_eq_restrict_Ici (a := (0:ℝ))).symm
        rw [hG]
        rw [← hμz, ← MeasureTheory.lintegral_prod _ hmeasDz]
        exact (ofReal_HkSq_zero hgmem hmeasDz).symm
      have hGle : (∫⁻ u in Set.Ioo (1:ℝ) c, G (z * u))
          ≤ ENNReal.ofReal z⁻¹ * ENNReal.ofReal
              (Work.Spaces.HkSq α 0 (Work.Spaces.Dz g)) := by
        rw [lintegral_Ioo_comp_mul (G := G) hzpos]
        refine mul_le_mul_of_nonneg_left ?_ bot_le
        rw [← hGbridge]
        exact MeasureTheory.lintegral_mono_set (fun y hy =>
          lt_of_lt_of_le hzpos (le_of_lt (by simpa using hy.1)))
      have hbnd : (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Mdq α c g z θ))
          ≤ ENNReal.ofReal ((c - 1)⁻¹) * (ENNReal.ofReal (c ^ 2) *
              (ENNReal.ofReal z⁻¹ * ENNReal.ofReal
                (Work.Spaces.HkSq α 0 (Work.Spaces.Dz g)))) := by
        rw [MeasureTheory.setLIntegral_congr_fun
          (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)
          (fun θ hθ => ofReal_Mdq_eq_Iθ (α := α) hg hc z hz θ hθ)]
        rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        rw [MeasureTheory.lintegral_lintegral_swap hmeas2]
        refine mul_le_mul_of_nonneg_left ?_ bot_le
        calc (∫⁻ u in Set.Ioo (1:ℝ) c, ∫⁻ θ in Work.Spaces.Iθ,
              ENNReal.ofReal (u ^ 2 *
                Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) (z * u) θ))
            = ∫⁻ u in Set.Ioo (1:ℝ) c, ENNReal.ofReal (u ^ 2) * G (z * u) := by
              refine MeasureTheory.setLIntegral_congr_fun measurableSet_Ioo (fun u _ => ?_)
              rw [hG, MeasureTheory.setLIntegral_congr_fun
                (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)
                (fun θ _ => ENNReal.ofReal_mul (sq_nonneg u))]
              exact MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
          _ ≤ ∫⁻ u in Set.Ioo (1:ℝ) c, ENNReal.ofReal (c ^ 2) * G (z * u) := by
              refine MeasureTheory.setLIntegral_mono' measurableSet_Ioo (fun u hu => ?_)
              refine mul_le_mul_of_nonneg_right ?_ bot_le
              exact ENNReal.ofReal_le_ofReal
                (pow_le_pow_left₀ (zero_le_one.trans (Set.mem_Ioo.mp hu).1.le)
                  (Set.mem_Ioo.mp hu).2.le 2)
          _ = ENNReal.ofReal (c ^ 2) * ∫⁻ u in Set.Ioo (1:ℝ) c, G (z * u) :=
              MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
          _ ≤ ENNReal.ofReal (c ^ 2) * (ENNReal.ofReal z⁻¹ * ENNReal.ofReal
                (Work.Spaces.HkSq α 0 (Work.Spaces.Dz g))) :=
              mul_le_mul_of_nonneg_left hGle bot_le
      exact lt_of_le_of_lt hbnd (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)))
    have ham : AEStronglyMeasurable (fun θ => Mdq α c g z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      have h2 : AEMeasurable (fun θ : ℝ =>
          (ENNReal.ofReal (Mdq α c g z θ)).toReal)
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
        ENNReal.measurable_toReal.comp_aemeasurable hA
      refine h2.aestronglyMeasurable.congr ?_
      filter_upwards [MeasureTheory.ae_restrict_mem
        (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)] with θ _
      exact ENNReal.toReal_ofReal (Mdq_nonneg hc z θ)
    exact (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable ham
      (Filter.Eventually.of_forall fun θ => Mdq_nonneg hc z θ)).mp hfin.ne

/-! ## The `z`-integral of the slices of the majorant is integrable -/

theorem integrableOn_Mdq_z {α c : ℝ} {g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (hc : 1 < c)
    (hgmem : Work.Spaces.HkMem α 0 (Work.Spaces.Dz g)) :
    MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, Mdq α c g z θ)
      Work.Spaces.Iz := by
  have hslice := integrableOn_Mdq_slice hg hc hgmem
  have hcont3 : ContinuousOn (fun q : (ℝ × ℝ) × ℝ => ENNReal.ofReal (q.2 ^ 2 *
      Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) (q.1.1 * q.2) q.1.2))
      ((Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) ×ˢ Set.Ioo (1:ℝ) c) := by
    refine ENNReal.continuous_ofReal.comp_continuousOn ?_
    refine ContinuousOn.mul (continuous_snd.pow 2).continuousOn ?_
    have hφ : ContinuousOn (fun q : (ℝ × ℝ) × ℝ => (q.1.1 * q.2, q.1.2))
        ((Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) ×ˢ Set.Ioo (1:ℝ) c) :=
      ((continuous_fst.fst.mul continuous_snd).prodMk continuous_fst.snd).continuousOn
    refine (HkIntegrand_zero_continuousOn hg).comp hφ ?_
    intro q hq
    obtain ⟨hq1, hq2⟩ := hq
    obtain ⟨h2a, hq2b⟩ := Set.mem_Ioo.mp hq2
    exact ⟨mul_pos (Set.mem_Ioi.mp hq1.1) (by linarith), hq1.2⟩
  have hmeas3 : AEMeasurable (fun q : (ℝ × ℝ) × ℝ => ENNReal.ofReal (q.2 ^ 2 *
      Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) (q.1.1 * q.2) q.1.2))
      (quadMeasure.prod (MeasureTheory.volume.restrict (Set.Ioo (1:ℝ) c))) :=
    aemeasurable_quad_prod_Ioo hcont3
  have hmeas : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (Mdq α c g p.1 p.2))
      quadMeasure := by
    have h1 : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal ((c - 1)⁻¹) *
        ∫⁻ u in Set.Ioo (1:ℝ) c, ENNReal.ofReal (u ^ 2 *
          Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) (p.1 * u) p.2)) quadMeasure :=
      (hmeas3.lintegral_prod_right).const_mul _
    refine h1.congr ?_
    rw [quadMeasure_eq_restrict]
    filter_upwards [MeasureTheory.ae_restrict_mem
      (measurableSet_Ioi.prod measurableSet_Ioo)] with p hp
    obtain ⟨hz, hθ⟩ := hp
    exact (ofReal_Mdq_eq_Iθ (α := α) hg hc p.1 (Set.mem_Ioi.mp hz).le p.2
      ⟨le_of_lt (Set.mem_Ioo.mp hθ).1, (Set.mem_Ioo.mp hθ).2.le⟩).symm
  have hbridge : (∫⁻ z in Work.Spaces.Iz,
        ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Mdq α c g z θ))
      = ∫⁻ p, ENNReal.ofReal (Mdq α c g p.1 p.2) ∂quadMeasure := by
    rw [show (∫⁻ z in Work.Spaces.Iz,
          ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Mdq α c g z θ))
        = ∫⁻ z in Set.Ici (0:ℝ),
          ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Mdq α c g z θ) from rfl]
    rw [MeasureTheory.setLIntegral_congr_fun measurableSet_Ici
      (fun z hz => MeasureTheory.ofReal_integral_eq_lintegral_ofReal
        (hslice z (show z ∈ Work.Spaces.Iz from hz))
        (Filter.Eventually.of_forall fun θ => Mdq_nonneg hc z θ))]
    exact (MeasureTheory.lintegral_prod _ hmeas).symm
  have hfin : (∫⁻ z in Work.Spaces.Iz,
      ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Mdq α c g z θ)) < ⊤ := by
    have hmeasDz : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal
        (Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) p.1 p.2)) quadMeasure :=
      aemeasurable_ofReal_HkIntegrand_of_continuousOn (HkIntegrand_zero_continuousOn hg)
    rw [hbridge]
    refine lt_of_le_of_lt (lintegral_Mdq_le hg hc hgmem) ?_
    rw [← ofReal_HkSq_zero hgmem hmeasDz]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  have hmes : AEStronglyMeasurable (fun z => ∫ θ in Work.Spaces.Iθ, Mdq α c g z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have h2 : AEMeasurable (fun z : ℝ =>
        (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Mdq α c g z θ)).toReal)
        (MeasureTheory.volume.restrict (Set.Ici (0:ℝ))) :=
      ENNReal.measurable_toReal.comp_aemeasurable hmeas.lintegral_prod_right
    rw [show (MeasureTheory.volume.restrict Work.Spaces.Iz)
        = MeasureTheory.volume.restrict (Set.Ici (0:ℝ)) from rfl]
    refine h2.aestronglyMeasurable.congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      (hslice z (show z ∈ Work.Spaces.Iz from hz))
      (Filter.Eventually.of_forall fun θ => Mdq_nonneg hc z θ)]
    exact ENNReal.toReal_ofReal
      (MeasureTheory.integral_nonneg fun θ => Mdq_nonneg hc z θ)
  exact (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hmes
    (Filter.Eventually.of_forall fun z =>
      MeasureTheory.integral_nonneg fun θ => Mdq_nonneg hc z θ)).mp hfin.ne

theorem HkMem_dq_le {α c : ℝ} {g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (hgmem : Work.Spaces.HkMem α 0 (Work.Spaces.Dz g))
    (hc : 1 < c) :
    Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.Cores.Dil.dq c g) ∧
      Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.Cores.Dil.dq c g)
        ≤ c ^ 3 * Work.Spaces.HkSq α 0 (Work.Spaces.Dz g) := by
  have hcpos : 0 < c := lt_trans zero_lt_one hc
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.HkIntegrand α 0 (dq c g) p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    (smoothOpen_dq hg hcpos).continuousOn_HkIntegrand α 0
  have hmem : Work.Spaces.HkMem α 0 (dq c g) :=
    Work.FTS.LocData.HkMem_of_majorant α 0 hcont
      (integrableOn_Mdq_slice hg hc hgmem)
      (integrableOn_Mdq_z hg hc hgmem)
      (fun z hz θ hθ => HkIntegrand_dq_le_Mdq hg hc z hz θ hθ)
  refine ⟨hmem, ?_⟩
  have hmeasdq : AEMeasurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 (dq c g) p.1 p.2)) quadMeasure :=
    aemeasurable_ofReal_HkIntegrand_of_continuousOn hcont
  have hmeasDz : AEMeasurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) p.1 p.2))
      quadMeasure :=
    aemeasurable_ofReal_HkIntegrand_of_continuousOn (HkIntegrand_zero_continuousOn hg)
  have hdom : (∫⁻ p, ENNReal.ofReal
        (Work.Spaces.HkIntegrand α 0 (dq c g) p.1 p.2) ∂quadMeasure)
      ≤ ∫⁻ p, ENNReal.ofReal (Mdq α c g p.1 p.2) ∂quadMeasure := by
    refine MeasureTheory.lintegral_mono_ae ?_
    rw [quadMeasure_eq_restrict]
    refine MeasureTheory.ae_restrict_of_forall_mem
      (measurableSet_Ioi.prod measurableSet_Ioo) ?_
    intro p hp
    obtain ⟨hz, hθ⟩ := hp
    exact ENNReal.ofReal_le_ofReal
      (HkIntegrand_dq_le_Mdq hg hc p.1 (Set.mem_Ioi.mp hz).le p.2
        ⟨(Set.mem_Ioo.mp hθ).1.le, (Set.mem_Ioo.mp hθ).2.le⟩)
  refine (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (by positivity) (Work.Spaces.HkSq_nonneg α 0 (Work.Spaces.Dz g)))).mp ?_
  rw [ENNReal.ofReal_mul (by positivity), ofReal_HkSq_zero hmem hmeasdq,
    ofReal_HkSq_zero hgmem hmeasDz]
  exact hdom.trans (lintegral_Mdq_le hg hc hgmem)

end Work.FTS.EllipticEst.Cores.Dil
