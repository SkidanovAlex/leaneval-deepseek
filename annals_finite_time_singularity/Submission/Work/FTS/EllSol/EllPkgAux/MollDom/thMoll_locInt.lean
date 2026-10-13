/-
# `Work.FTS.EllSol.EllPkgAux.MollDom.thMoll_locInt`

**Local integrability in the logarithmic radial variable of the angular mollification.**

For a datum `u : ℝ → ℝ → ℝ` whose angular slices are continuous on `Iθ = [0, π/2]` and vanish
at the two endpoints, which is *jointly* continuous on the open quadrant `Q0`, and which is
`L¹`-dominated on each slice by a function `F` that is integrable on each `[a, b]` with
`0 < a ≤ b`, the map

  `t ↦ thMoll u ε (exp t) θ`

is locally integrable on `ℝ`, for every `ε ∈ (0, 1/2]` and every `θ ∈ Iθ`.

The two ingredients are

* the *pointwise* slice bound `|thMoll u ε z θ| ≤ 3 (ε · sMass)⁻¹ ∫_{Iθ} |u z ·|` for `z > 0`,
  which is the (proved) fold `thMoll_abs_le` together with the bound `KJ ε θ s ≤ 3 (ε · sMass)⁻¹`
  of the three-image kernel, followed by the domination hypothesis `hFb`;
* the *measurability* of `t ↦ thMoll u ε (exp t) θ`, obtained by writing `thMoll` as an integral
  over the `s`-line of the jointly a.e.-measurable integrand `sKer ε (θ - s) · Qext u (exp t) s`
  (`AEStronglyMeasurable.integral_prod_right'`).  The truncation `QextTr` below is the version of
  the doubly odd extension whose ingredients are continuous on the *open* pieces `(-π/2, 0)`,
  `(0, π/2)`, `(π/2, π)`; it agrees with `Qext` on all of `(-π/2, π)` (using the endpoint *values*
  `u z 0 = 0`, `u z (π/2) = 0`).

The change of variables `z = exp t` is handled in `integrableOn_comp_exp_of_Icc` /
`locallyIntegrable_mul_comp_exp`, which turn the `Icc`-integrability of `F` on the positive half
line into the local integrability of `t ↦ C · F (exp t)`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllSol.EllPkgAux.thMollTransfer2
import Submission.Work.FTS.EllSol.EllPkgAux.MollBase
import Submission.Work.FTS.EllSol.EllPkgAux.thMollSliceL2
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

set_option maxHeartbeats 2000000

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux.MollDom

local notation "Iθ" => Work.Spaces.Iθ

open Work.FTS.EllSol.PkgK5.K5c (thMoll Qext sKer sMass Qext_of_mem Qext_neg_of_pos
  Qext_pihalf_odd sKer_eq_zero_of_le_abs)
open Work.FTS.EllSol.EllPkgAux (KJ KJ_le KJ_nonneg tsl_integrableOn_mul_continuous)

/-! ## The logarithmic change of variables -/

/-- **Integrability of `t ↦ F (exp t)` on an interval.**  If `F` is integrable on every
`[a, b]` with `0 < a ≤ b`, then `t ↦ F (exp t)` is integrable on every `[a, b]`, `a ≤ b`.

This is the substitution `z = exp t` (`integrableOn_image_iff_integrableOn_abs_deriv_smul` with
`f = exp`, `f' = exp`, whose Jacobian factor `exp t ≥ exp a > 0` is bounded below away from `0`
on `[a, b]`). -/
theorem integrableOn_comp_exp_of_Icc {F : ℝ → ℝ}
    (hF : ∀ a b : ℝ, 0 < a → a ≤ b → MeasureTheory.IntegrableOn F (Set.Icc a b))
    {a b : ℝ} (hab : a ≤ b) :
    MeasureTheory.IntegrableOn (fun t : ℝ => F (Real.exp t)) (Set.Icc a b) := by
  -- the image of `[a,b]` under `exp` is `[exp a, exp b]`, where `F` is integrable
  have h1 : MeasureTheory.IntegrableOn F (Real.exp '' Set.Icc a b) := by
    rw [Real.image_exp_Icc]
    exact hF (Real.exp a) (Real.exp b) (Real.exp_pos a) (Real.exp_le_exp.mpr hab)
  -- change of variables
  have h2 : MeasureTheory.IntegrableOn (fun x : ℝ => |Real.exp x| • F (Real.exp x))
      (Set.Icc a b) :=
    (MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul (s := Set.Icc a b)
      (f := Real.exp) (f' := Real.exp) measurableSet_Icc
      (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn F).mp h1
  have h2' : MeasureTheory.IntegrableOn (fun x : ℝ => Real.exp x * F (Real.exp x))
      (Set.Icc a b) := by
    refine h2.congr_fun (fun x _ => ?_) measurableSet_Icc
    show |Real.exp x| • F (Real.exp x) = Real.exp x * F (Real.exp x)
    rw [smul_eq_mul, abs_of_pos (Real.exp_pos x)]
  -- the majorant `(exp a)⁻¹ · |exp t · F (exp t)|`
  have h3 : MeasureTheory.Integrable
      (fun t : ℝ => (Real.exp a)⁻¹ * |Real.exp t * F (Real.exp t)|)
      (MeasureTheory.volume.restrict (Set.Icc a b)) :=
    (show MeasureTheory.Integrable (fun t : ℝ => |Real.exp t * F (Real.exp t)|)
        (MeasureTheory.volume.restrict (Set.Icc a b)) from h2'.abs).const_mul _
  refine Integrable.mono' h3 ?_ ?_
  · -- a.e.-strong measurability: `F (exp t)` is the product of `(exp t)⁻¹` and `exp t * F (exp t)`
    have hcont_inv : Continuous (fun t : ℝ => (Real.exp t)⁻¹) := by
      have hfun : (fun t : ℝ => (Real.exp t)⁻¹) = fun t : ℝ => Real.exp (-t) := by
        funext t
        exact (Real.exp_neg t).symm
      rw [hfun]
      exact Real.continuous_exp.comp continuous_neg
    have heq : (fun t : ℝ => F (Real.exp t))
        = fun t : ℝ => (Real.exp t)⁻¹ * (Real.exp t * F (Real.exp t)) := by
      funext t
      rw [inv_mul_cancel_left₀ (ne_of_gt (Real.exp_pos t))]
    rw [heq]
    exact (hcont_inv.aestronglyMeasurable).mul h2'.aestronglyMeasurable
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with t ht
    have hpa : 0 < Real.exp a := Real.exp_pos a
    have hge : 1 ≤ Real.exp t * (Real.exp a)⁻¹ := by
      have hle : Real.exp a ≤ Real.exp t := Real.exp_le_exp.mpr ht.1
      have h3' := mul_le_mul_of_nonneg_right hle (inv_nonneg.mpr hpa.le)
      rwa [mul_inv_cancel₀ (ne_of_gt hpa)] at h3'
    rw [Real.norm_eq_abs]
    calc |F (Real.exp t)| = 1 * |F (Real.exp t)| := (one_mul _).symm
      _ ≤ (Real.exp t * (Real.exp a)⁻¹) * |F (Real.exp t)| :=
            mul_le_mul_of_nonneg_right hge (abs_nonneg _)
      _ = (Real.exp a)⁻¹ * |Real.exp t * F (Real.exp t)| := by
            rw [abs_mul, abs_of_pos (Real.exp_pos t)]; ring

/-- **Local integrability of `t ↦ C · F (exp t)`** for a function `F` integrable on every
`[a, b]` with `0 < a ≤ b`.  Every compact set of the `t`-line is contained in some `[A, B]`,
whose image under `exp` is a compact interval of positive reals. -/
theorem locallyIntegrable_mul_comp_exp {F : ℝ → ℝ} {C : ℝ}
    (hF : ∀ a b : ℝ, 0 < a → a ≤ b → MeasureTheory.IntegrableOn F (Set.Icc a b)) :
    MeasureTheory.LocallyIntegrable (fun t : ℝ => C * F (Real.exp t)) MeasureTheory.volume := by
  refine MeasureTheory.locallyIntegrable_iff.mpr fun k hk => ?_
  obtain ⟨C₀, hC₀⟩ := hk.exists_bound_of_continuousOn
    (f := fun x : ℝ => x) continuous_id.continuousOn
  have hDpos : 0 < |C₀| + 1 := by positivity
  have hsub : k ⊆ Set.Icc (-(|C₀| + 1)) (|C₀| + 1) := by
    intro x hx
    have h : |x| ≤ C₀ := by simpa only [Real.norm_eq_abs] using hC₀ x hx
    have h2 : |x| ≤ |C₀| + 1 := by linarith [le_abs_self C₀]
    exact ⟨by linarith [(abs_le.mp h2).1], by linarith [(abs_le.mp h2).2]⟩
  have hbase : MeasureTheory.IntegrableOn (fun t : ℝ => F (Real.exp t))
      (Set.Icc (-(|C₀| + 1)) (|C₀| + 1)) :=
    integrableOn_comp_exp_of_Icc hF (by linarith [hDpos])
  refine MeasureTheory.IntegrableOn.mono_set ?_ hsub
  exact (show MeasureTheory.Integrable (fun t : ℝ => F (Real.exp t))
      (MeasureTheory.volume.restrict (Set.Icc (-(|C₀| + 1)) (|C₀| + 1))) from hbase).const_mul C

/-! ## The truncated doubly odd extension -/

/-- The truncation of the doubly odd extension `s ↦ Qext u (exp t) s` to the three intervals on
which its ingredients are honest compositions with `u` on the open quadrant:
`s ∈ (-π/2, 0)` reads `-u (exp t) (-s)`, `s ∈ (0, π/2)` reads `u (exp t) s`, and
`s ∈ (π/2, π)` reads `-u (exp t) (π - s)`.  Off these three intervals the value is `0`; on the
rest of `(-π/2, π)` it therefore agrees with `Qext` (the two intervals left over are the points
`s = 0`, `s = π/2`, where `Qext u (exp t) s = u (exp t) s = 0` by the endpoint values).
Off `(-π/2, π)` the mollifying kernel vanishes, so `QextTr` may be used in place of `Qext` inside
the integral defining `thMoll`. -/
def QextTr (u : ℝ → ℝ → ℝ) (t s : ℝ) : ℝ :=
  (if s ∈ Set.Ioo (-(Real.pi / 2)) 0 then -u (Real.exp t) (-s) else 0)
    + (if s ∈ Set.Ioo 0 (Real.pi / 2) then u (Real.exp t) s else 0)
    + (if s ∈ Set.Ioo (Real.pi / 2) Real.pi then -u (Real.exp t) (Real.pi - s) else 0)

/-- `QextTr u` agrees with `Qext u (exp ·)` on the window `(-π/2, π)`. -/
theorem QextTr_eq_Qext {u : ℝ → ℝ → ℝ} (h0 : ∀ w : ℝ, u w 0 = 0)
    (hp : ∀ w : ℝ, u w (Real.pi / 2) = 0) {t s : ℝ}
    (hs : s ∈ Set.Ioo (-(Real.pi / 2)) Real.pi) :
    QextTr u t s = Qext u (Real.exp t) s := by
  classical
  -- `Qext` on the right half
  have hQpi : ∀ r ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Qext u (Real.exp t) (Real.pi - r) = -u (Real.exp t) r := by
    intro r hr
    have hs1 : 0 < Real.pi / 2 - r := by linarith [hr.2]
    have hs2 : Real.pi / 2 - r ≤ Real.pi / 2 := by linarith [hr.1]
    have hodd := Qext_pihalf_odd u (Real.exp t) (Real.pi / 2 - r) hs1 hs2
    have e1 : Real.pi / 2 - (Real.pi / 2 - r) = r := by ring
    have e2 : Real.pi / 2 + (Real.pi / 2 - r) = Real.pi - r := by ring
    rw [e1, e2] at hodd
    have hQt : Qext u (Real.exp t) r = u (Real.exp t) r :=
      Qext_of_mem u (Real.exp t) r ⟨hr.1.le, hr.2.le⟩
    rw [hQt] at hodd
    linarith [hodd]
  have hzero : Qext u (Real.exp t) 0 = 0 := by
    simp only [Qext_of_mem u (Real.exp t) 0 ⟨le_refl 0, by positivity⟩, h0]
  have hhalf : Qext u (Real.exp t) (Real.pi / 2) = 0 := by
    simp only [Qext_of_mem u (Real.exp t) (Real.pi / 2) ⟨by positivity, le_refl _⟩, hp]
  rcases lt_trichotomy s 0 with h | h | h
  · -- `s < 0`
    have hmem : s ∈ Set.Ioo (-(Real.pi / 2)) 0 := ⟨hs.1, h⟩
    have h1 : ¬ s ∈ Set.Ioo 0 (Real.pi / 2) := fun hh => absurd hh.1 (not_lt.mpr h.le)
    have h2 : ¬ s ∈ Set.Ioo (Real.pi / 2) Real.pi :=
      fun hh => absurd hh.1 (not_lt.mpr (le_trans (le_of_lt h) (by positivity)))
    have htr : QextTr u t s = -u (Real.exp t) (-s) := by
      rw [QextTr, if_pos hmem, if_neg h1, if_neg h2, add_zero, add_zero]
    have hQ : Qext u (Real.exp t) s = -u (Real.exp t) (-s) := by
      have hh := Qext_neg_of_pos u (Real.exp t) (-s) (by linarith)
      simpa only [neg_neg] using hh
    rw [htr, hQ]
  · -- `s = 0`
    subst h
    have h1 : ¬ (0 : ℝ) ∈ Set.Ioo (-(Real.pi / 2)) 0 := fun hh => absurd hh.2 (lt_irrefl 0)
    have h2 : ¬ (0 : ℝ) ∈ Set.Ioo 0 (Real.pi / 2) := fun hh => absurd hh.1 (lt_irrefl 0)
    have h3 : ¬ (0 : ℝ) ∈ Set.Ioo (Real.pi / 2) Real.pi :=
      fun hh => absurd hh.1 (not_lt.mpr (by positivity))
    have htr : QextTr u t 0 = 0 := by
      rw [QextTr, if_neg h1, if_neg h2, if_neg h3, zero_add, zero_add]
    rw [htr, hzero]
  · rcases lt_trichotomy s (Real.pi / 2) with h2 | h2 | h2
    · -- `0 < s < π/2`
      have hmem : s ∈ Set.Ioo 0 (Real.pi / 2) := ⟨h, h2⟩
      have h1 : ¬ s ∈ Set.Ioo (-(Real.pi / 2)) 0 := fun hh => absurd hh.2 (not_lt.mpr h.le)
      have h3 : ¬ s ∈ Set.Ioo (Real.pi / 2) Real.pi := fun hh => absurd hh.1 (not_lt.mpr h2.le)
      have htr : QextTr u t s = u (Real.exp t) s := by
        rw [QextTr, if_neg h1, if_pos hmem, if_neg h3, zero_add, add_zero]
      have hQ : Qext u (Real.exp t) s = u (Real.exp t) s :=
        Qext_of_mem u (Real.exp t) s ⟨h.le, h2.le⟩
      rw [htr, hQ]
    · -- `s = π/2`
      subst h2
      have h1 : ¬ (Real.pi / 2) ∈ Set.Ioo (-(Real.pi / 2)) 0 :=
        fun hh => absurd hh.2 (not_lt.mpr (by positivity))
      have h2' : ¬ (Real.pi / 2) ∈ Set.Ioo 0 (Real.pi / 2) :=
        fun hh => absurd hh.2 (lt_irrefl _)
      have h3 : ¬ (Real.pi / 2) ∈ Set.Ioo (Real.pi / 2) Real.pi :=
        fun hh => absurd hh.1 (lt_irrefl _)
      have htr : QextTr u t (Real.pi / 2) = 0 := by
        rw [QextTr, if_neg h1, if_neg h2', if_neg h3, zero_add, zero_add]
      rw [htr, hhalf]
    · -- `s > π/2`
      have hmem : s ∈ Set.Ioo (Real.pi / 2) Real.pi := ⟨h2, hs.2⟩
      have h1 : ¬ s ∈ Set.Ioo (-(Real.pi / 2)) 0 :=
        fun hh => absurd hh.2 (not_lt.mpr (le_of_lt h))
      have h3 : ¬ s ∈ Set.Ioo 0 (Real.pi / 2) := fun hh => absurd hh.2 (not_lt.mpr h2.le)
      have htr : QextTr u t s = -u (Real.exp t) (Real.pi - s) := by
        rw [QextTr, if_neg h1, if_neg h3, if_pos hmem, zero_add, zero_add]
      have hr : Real.pi - s ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
        ⟨by linarith [hs.2], by linarith [h2]⟩
      have hQ : Qext u (Real.exp t) s = -u (Real.exp t) (Real.pi - s) := by
        have hh := hQpi (Real.pi - s) hr
        rw [show Real.pi - (Real.pi - s) = s by ring] at hh
        exact hh
      rw [htr, hQ]

/-- **The truncated extension is a.e.-strongly measurable.**  Each of its three summands is the
indicator of a measurable set of the function `exp`-composition of `uncurry u`, which is
continuous on that set (because the set is contained in `exp ⁻¹' Q0`). -/
theorem aesm_QextTr {u : ℝ → ℝ → ℝ}
    (huc : ContinuousOn (Function.uncurry u) Work.FTS.EllipticEst.Q0) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => QextTr u p.1 p.2)
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
  classical
  have hS1 : MeasurableSet {p : ℝ × ℝ | p.2 ∈ Set.Ioo (-(Real.pi / 2)) 0} :=
    measurableSet_Ioo.preimage measurable_snd
  have hS2 : MeasurableSet {p : ℝ × ℝ | p.2 ∈ Set.Ioo 0 (Real.pi / 2)} :=
    measurableSet_Ioo.preimage measurable_snd
  have hS3 : MeasurableSet {p : ℝ × ℝ | p.2 ∈ Set.Ioo (Real.pi / 2) Real.pi} :=
    measurableSet_Ioo.preimage measurable_snd
  have hG1 : ContinuousOn (fun p : ℝ × ℝ => -u (Real.exp p.1) (-p.2))
      {p : ℝ × ℝ | p.2 ∈ Set.Ioo (-(Real.pi / 2)) 0} := by
    refine ContinuousOn.neg ?_
    refine huc.comp ((Real.continuous_exp.comp continuous_fst).prodMk
      continuous_snd.neg).continuousOn ?_
    rintro p ⟨hp1, hp2⟩
    have hz : 0 < Real.exp p.1 := Real.exp_pos p.1
    have hy1 : 0 < -p.2 := neg_pos.mpr hp2
    have hy2 : -p.2 < Real.pi / 2 := by linarith [hp1]
    exact Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hy1, hy2⟩
  have hG2 : ContinuousOn (fun p : ℝ × ℝ => u (Real.exp p.1) p.2)
      {p : ℝ × ℝ | p.2 ∈ Set.Ioo 0 (Real.pi / 2)} := by
    refine huc.comp ((Real.continuous_exp.comp continuous_fst).prodMk
      continuous_snd).continuousOn ?_
    rintro p ⟨hp1, hp2⟩
    exact Work.FTS.EllipticEst.mem_Q0.mpr ⟨Real.exp_pos p.1, hp1, hp2⟩
  have hG3 : ContinuousOn (fun p : ℝ × ℝ => -u (Real.exp p.1) (Real.pi - p.2))
      {p : ℝ × ℝ | p.2 ∈ Set.Ioo (Real.pi / 2) Real.pi} := by
    refine ContinuousOn.neg ?_
    refine huc.comp ((Real.continuous_exp.comp continuous_fst).prodMk
      (continuous_const.sub continuous_snd)).continuousOn ?_
    rintro p ⟨hp1, hp2⟩
    have hz : 0 < Real.exp p.1 := Real.exp_pos p.1
    have hy1 : 0 < Real.pi - p.2 := sub_pos.mpr hp2
    have hy2 : Real.pi - p.2 < Real.pi / 2 := by linarith [hp1]
    exact Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hy1, hy2⟩
  have hm1 : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      (if p.2 ∈ Set.Ioo (-(Real.pi / 2)) 0 then -u (Real.exp p.1) (-p.2) else 0))
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
    have hiff : (fun p : ℝ × ℝ =>
        (if p.2 ∈ Set.Ioo (-(Real.pi / 2)) 0 then -u (Real.exp p.1) (-p.2) else 0))
        = Set.indicator {p : ℝ × ℝ | p.2 ∈ Set.Ioo (-(Real.pi / 2)) 0}
            (fun p : ℝ × ℝ => -u (Real.exp p.1) (-p.2)) := by
      funext p
      rw [Set.indicator_apply]
      simp only [Set.mem_setOf_eq]
    rw [hiff]
    exact (aestronglyMeasurable_indicator_iff hS1).mpr (hG1.aestronglyMeasurable hS1)
  have hm2 : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      (if p.2 ∈ Set.Ioo 0 (Real.pi / 2) then u (Real.exp p.1) p.2 else 0))
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
    have hiff : (fun p : ℝ × ℝ =>
        (if p.2 ∈ Set.Ioo 0 (Real.pi / 2) then u (Real.exp p.1) p.2 else 0))
        = Set.indicator {p : ℝ × ℝ | p.2 ∈ Set.Ioo 0 (Real.pi / 2)}
            (fun p : ℝ × ℝ => u (Real.exp p.1) p.2) := by
      funext p
      rw [Set.indicator_apply]
      simp only [Set.mem_setOf_eq]
    rw [hiff]
    exact (aestronglyMeasurable_indicator_iff hS2).mpr (hG2.aestronglyMeasurable hS2)
  have hm3 : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      (if p.2 ∈ Set.Ioo (Real.pi / 2) Real.pi then -u (Real.exp p.1) (Real.pi - p.2) else 0))
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
    have hiff : (fun p : ℝ × ℝ =>
        (if p.2 ∈ Set.Ioo (Real.pi / 2) Real.pi then -u (Real.exp p.1) (Real.pi - p.2) else 0))
        = Set.indicator {p : ℝ × ℝ | p.2 ∈ Set.Ioo (Real.pi / 2) Real.pi}
            (fun p : ℝ × ℝ => -u (Real.exp p.1) (Real.pi - p.2)) := by
      funext p
      rw [Set.indicator_apply]
      simp only [Set.mem_setOf_eq]
    rw [hiff]
    exact (aestronglyMeasurable_indicator_iff hS3).mpr (hG3.aestronglyMeasurable hS3)
  have hsum : AEStronglyMeasurable
      ((fun p : ℝ × ℝ =>
          (if p.2 ∈ Set.Ioo (-(Real.pi / 2)) 0 then -u (Real.exp p.1) (-p.2) else 0))
        + (fun p : ℝ × ℝ =>
          (if p.2 ∈ Set.Ioo 0 (Real.pi / 2) then u (Real.exp p.1) p.2 else 0))
        + (fun p : ℝ × ℝ =>
          (if p.2 ∈ Set.Ioo (Real.pi / 2) Real.pi then -u (Real.exp p.1) (Real.pi - p.2)
            else 0))) (MeasureTheory.volume.prod MeasureTheory.volume) :=
    (hm1.add hm2).add hm3
  have hfun : (fun p : ℝ × ℝ => QextTr u p.1 p.2)
      = ((fun p : ℝ × ℝ =>
          (if p.2 ∈ Set.Ioo (-(Real.pi / 2)) 0 then -u (Real.exp p.1) (-p.2) else 0))
        + (fun p : ℝ × ℝ =>
          (if p.2 ∈ Set.Ioo 0 (Real.pi / 2) then u (Real.exp p.1) p.2 else 0))
        + (fun p : ℝ × ℝ =>
          (if p.2 ∈ Set.Ioo (Real.pi / 2) Real.pi then -u (Real.exp p.1) (Real.pi - p.2)
            else 0))) := by
    funext p
    simp only [QextTr, Pi.add_apply]
  rw [hfun]
  exact hsum

/-- **`QextTr` may replace `Qext` under the mollifying kernel.**  If `s` lies in the window met by
the kernel (`|θ - s| < ε`, and `ε ≤ 1/2`, `θ ∈ Iθ`) then `QextTr` and `Qext` agree there; otherwise
the kernel vanishes. -/
theorem sKer_mul_QextTr_eq {u : ℝ → ℝ → ℝ} (h0 : ∀ w : ℝ, u w 0 = 0)
    (hp : ∀ w : ℝ, u w (Real.pi / 2) = 0) {ε θ t s : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (hθ : θ ∈ Iθ) :
    sKer ε (θ - s) * Qext u (Real.exp t) s = sKer ε (θ - s) * QextTr u t s := by
  classical
  by_cases hwin : s ∈ Set.Ioo (-(1 / 2)) (Real.pi / 2 + 1 / 2)
  · have hs : s ∈ Set.Ioo (-(Real.pi / 2)) Real.pi :=
      ⟨by linarith [hwin.1, Real.pi_gt_three], by linarith [hwin.2, Real.pi_gt_three]⟩
    rw [QextTr_eq_Qext h0 hp hs]
  · have hker : sKer ε (θ - s) = 0 := by
      rw [Set.mem_Ioo, not_and_or, not_lt, not_lt] at hwin
      refine sKer_eq_zero_of_le_abs hε ?_
      rcases hwin with h | h
      · rw [abs_of_nonneg (by linarith [hθ.1, h])]
        linarith [hθ.1, h, hε1]
      · rw [abs_of_nonpos (by linarith [hθ.2, h])]
        linarith [hθ.2, h, hε1]
    rw [hker, zero_mul, zero_mul]

/-! ## The pointwise slice bound -/

/-- **The slice bound of the angular mollification**: for `z > 0`, `θ ∈ Iθ` and `ε ∈ (0, 1/2]`,

  `|thMoll u ε z θ| ≤ 3 (ε · sMass)⁻¹ ∫_{Iθ} |u z ·|`. -/
theorem thMoll_norm_le {u : ℝ → ℝ → ℝ} {ε θ z : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (hθ : θ ∈ Iθ) (hcont : ContinuousOn (fun s : ℝ => u z s) Iθ) :
    ‖thMoll u ε z θ‖ ≤ 3 * (ε * sMass)⁻¹ * ∫ s in Iθ, |u z s| := by
  classical
  have hIθc : IsCompact (Iθ : Set ℝ) := isCompact_Icc
  have hint : MeasureTheory.IntegrableOn (fun s : ℝ => u z s) Iθ :=
    ContinuousOn.integrableOn_compact (μ := MeasureTheory.volume) (K := Iθ) hIθc hcont
  have h1 := thMoll_abs_le u hε hε1 hint hθ
  have hintabs : MeasureTheory.Integrable (fun s : ℝ => |u z s|)
      (MeasureTheory.volume.restrict Iθ) :=
    (show MeasureTheory.Integrable (fun s : ℝ => u z s) (MeasureTheory.volume.restrict Iθ)
      from hint).abs
  have hi2 : MeasureTheory.Integrable (fun s : ℝ => 3 * (ε * sMass)⁻¹ * |u z s|)
      (MeasureTheory.volume.restrict Iθ) := hintabs.const_mul _
  have hpt : ∀ s : ℝ, KJ ε θ s * |u z s| ≤ 3 * (ε * sMass)⁻¹ * |u z s| :=
    fun s => mul_le_mul_of_nonneg_right (KJ_le hε θ s) (abs_nonneg _)
  have hmono : (∫ s in Iθ, KJ ε θ s * |u z s|) ≤ ∫ s in Iθ, 3 * (ε * sMass)⁻¹ * |u z s| :=
    MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun s => mul_nonneg (KJ_nonneg hε θ s) (abs_nonneg _))
      hi2 (Filter.Eventually.of_forall hpt)
  calc ‖thMoll u ε z θ‖
      = |thMoll u ε z θ| := Real.norm_eq_abs _
    _ ≤ ∫ s in Iθ, KJ ε θ s * |u z s| := h1
    _ ≤ ∫ s in Iθ, 3 * (ε * sMass)⁻¹ * |u z s| := hmono
    _ = 3 * (ε * sMass)⁻¹ * ∫ s in Iθ, |u z s| := MeasureTheory.integral_const_mul _ _

/-! ## The local integrability -/

theorem thMoll_locInt {u : ℝ → ℝ → ℝ} {ε θ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (hθ : θ ∈ Work.Spaces.Iθ)
    (h0 : ∀ w : ℝ, u w 0 = 0) (hp : ∀ w : ℝ, u w (Real.pi / 2) = 0)
    (hcont : ∀ w : ℝ, 0 < w → ContinuousOn (fun s : ℝ => u w s) Work.Spaces.Iθ)
    (huc : ContinuousOn (Function.uncurry u) Work.FTS.EllipticEst.Q0)
    {F : ℝ → ℝ} (hF : ∀ a b : ℝ, 0 < a → a ≤ b → MeasureTheory.IntegrableOn F (Set.Icc a b))
    (hFb : ∀ w : ℝ, 0 < w → ∫ s in Work.Spaces.Iθ, |u w s| ≤ F w) :
    MeasureTheory.LocallyIntegrable
      (fun t : ℝ => Work.FTS.EllSol.PkgK5.K5c.thMoll u ε (Real.exp t) θ) MeasureTheory.volume := by
  classical
  -- ## the a.e.-strong measurability of `t ↦ thMoll u ε (exp t) θ`
  have haesm : AEStronglyMeasurable (fun t : ℝ => thMoll u ε (Real.exp t) θ)
      MeasureTheory.volume := by
    have hmeas1 : AEStronglyMeasurable
        (fun p : ℝ × ℝ => sKer ε (θ - p.2) * QextTr u p.1 p.2)
        (MeasureTheory.volume.prod MeasureTheory.volume) :=
      ((Work.FTS.EllSol.K5cAux.continuous_sKer ε).comp
        (continuous_const.sub continuous_snd)).aestronglyMeasurable.mul (aesm_QextTr huc)
    have hmeas2 : AEStronglyMeasurable
        (fun t : ℝ => ∫ s : ℝ, sKer ε (θ - s) * QextTr u t s) MeasureTheory.volume :=
      hmeas1.integral_prod_right'
    refine hmeas2.congr (Filter.Eventually.of_forall fun t => ?_)
    show (∫ s : ℝ, sKer ε (θ - s) * QextTr u t s)
      = ∫ s : ℝ, sKer ε (θ - s) * Qext u (Real.exp t) s
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun s =>
      (sKer_mul_QextTr_eq h0 hp hε hε1 hθ).symm)
  -- ## the pointwise domination by the majorant `3 (ε · sMass)⁻¹ · F (exp t)`
  have hbnd : ∀ t : ℝ, ‖thMoll u ε (Real.exp t) θ‖
      ≤ ‖3 * (ε * sMass)⁻¹ * F (Real.exp t)‖ := by
    intro t
    have hzt : 0 < Real.exp t := Real.exp_pos t
    have hslice := thMoll_norm_le hε hε1 hθ (hcont (Real.exp t) hzt)
    have hcnonneg : 0 ≤ 3 * (ε * sMass)⁻¹ :=
      mul_nonneg (by norm_num) (le_of_lt (inv_pos.mpr
        (mul_pos hε Work.FTS.EllSol.PkgK5.K5c.sMass_pos)))
    have hBC : 3 * (ε * sMass)⁻¹ * ∫ s in Iθ, |u (Real.exp t) s|
        ≤ 3 * (ε * sMass)⁻¹ * F (Real.exp t) :=
      mul_le_mul_of_nonneg_left (hFb (Real.exp t) hzt) hcnonneg
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    exact le_trans (le_trans hslice hBC) (le_abs_self _)
  -- ## the majorant is locally integrable
  have hloc : MeasureTheory.LocallyIntegrable
      (fun t : ℝ => 3 * (ε * sMass)⁻¹ * F (Real.exp t)) MeasureTheory.volume :=
    locallyIntegrable_mul_comp_exp hF
  exact MeasureTheory.LocallyIntegrable.mono hloc haesm (Filter.Eventually.of_forall hbnd)

end Work.FTS.EllSol.EllPkgAux.MollDom
