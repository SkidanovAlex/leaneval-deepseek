import Mathlib
import Submission.Work.Drive.chordSweepSmooth

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology intervalIntegral

/-!
# Foundations for the smoothed sweep: the bump and convolution with affine maps

* `Work.Drive.integral_sweepBump : ∫ sweepBump = 1`, `Work.Drive.integral_sweepBump_mul :
  ∫ u * sweepBump u = 0` (the bump is even), `Work.Drive.sweepBump_pos`, support in `[-1,1]`.
  Consequently both smoothing convolutions of the chord sweep (`sweepSmoothT`, `sweepFam`) are
  **convex combinations** of values of the chamfered loop over a window.
* `Work.Drive.sweepBlur_affine : ∫ sweepBump u • (p + (t - δ * u) • v) = p + t • v`: convolution
  with the bump fixes affine functions.  Hence away from the four corners of the chamfered loop the
  slice is exactly a blurred knot arc / a blurred chord segment, and only the four corner windows
  carry the genuine smoothing error.
-/

/-! ## The bump -/

/-- The symmetry of `Real.smoothTransition`: `σ x + σ (1 - x) = 1`. -/
lemma sweepTransition_symm (x : ℝ) : Real.smoothTransition x + Real.smoothTransition (1 - x) = 1 := by
  rw [Real.smoothTransition, Real.smoothTransition]
  have h3 : (1 : ℝ) - (1 - x) = x := by ring
  rw [h3]
  have hden : expNegInvGlue x + expNegInvGlue (1 - x) ≠ 0 :=
    ne_of_gt (Real.smoothTransition.pos_denom x)
  rw [add_comm (expNegInvGlue (1 - x)) (expNegInvGlue x)]
  rw [← add_div]
  exact div_self hden

lemma sweepBump_continuous : Continuous sweepBump := by
  change Continuous (fun u : ℝ => Real.smoothTransition (1 + u) * Real.smoothTransition (1 - u))
  exact (Real.smoothTransition.continuous.comp (continuous_const.add continuous_id)).mul
    (Real.smoothTransition.continuous.comp (continuous_const.sub continuous_id))

lemma sweepBump_nonneg (u : ℝ) : 0 ≤ sweepBump u := by
  rw [sweepBump]
  exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

lemma sweepBump_eq_zero {u : ℝ} (h : 1 ≤ |u|) : sweepBump u = 0 := by
  rw [sweepBump]
  rcases le_total 0 u with hu | hu
  · have h1 : 1 ≤ u := by rwa [abs_of_nonneg hu] at h
    rw [Real.smoothTransition.zero_of_nonpos (by linarith : 1 - u ≤ 0), mul_zero]
  · have h1 : u ≤ -1 := by rw [abs_of_nonpos hu] at h; linarith
    rw [Real.smoothTransition.zero_of_nonpos (by linarith : 1 + u ≤ 0), zero_mul]

lemma sweepBump_pos {u : ℝ} (h1 : -1 < u) (h2 : u < 1) : 0 < sweepBump u := by
  rw [sweepBump]
  exact mul_pos (Real.smoothTransition.pos_of_pos (by linarith))
    (Real.smoothTransition.pos_of_pos (by linarith))

lemma sweepBump_even (u : ℝ) : sweepBump (-u) = sweepBump u := by
  unfold sweepBump; ring_nf

lemma integral_smoothTransition_zero_one : (∫ x in (0:ℝ)..1, Real.smoothTransition x) = 1/2 := by
  have hsub : (∫ x in (0:ℝ)..1, Real.smoothTransition (1 - x))
      = (∫ x in (0:ℝ)..1, Real.smoothTransition x) := by
    rw [intervalIntegral.integral_comp_sub_left (fun x => Real.smoothTransition x) (a := 0) (b := 1)]
    norm_num
  have hone : (∫ x in (0:ℝ)..1, (Real.smoothTransition x + Real.smoothTransition (1 - x))) = 1 := by
    rw [show (fun x : ℝ => Real.smoothTransition x + Real.smoothTransition (1 - x)) = fun _ => (1:ℝ) from
      funext sweepTransition_symm]
    simp
  have hA : (∫ x in (0:ℝ)..1, Real.smoothTransition x)
      + (∫ x in (0:ℝ)..1, Real.smoothTransition (1 - x)) = 1 := by
    rw [← intervalIntegral.integral_add (μ := MeasureTheory.volume)
      (f := Real.smoothTransition) (g := fun x : ℝ => Real.smoothTransition (1 - x))
      (Real.smoothTransition.continuous.intervalIntegrable 0 1)
      ((Real.smoothTransition.continuous.comp
        (continuous_const.sub continuous_id)).intervalIntegrable 0 1)]
    exact hone
  rw [← hsub] at hA
  nlinarith [hA]

/-- **The bump has total mass one.** -/
lemma integral_sweepBump : (∫ u in (-1:ℝ)..1, sweepBump u) = 1 := by
  have hadd : ((∫ x in (-1:ℝ)..0, sweepBump x)) + (∫ x in (0:ℝ)..1, sweepBump x)
      = (∫ x in (-1:ℝ)..1, sweepBump x) :=
    intervalIntegral.integral_add_adjacent_intervals
      (show IntervalIntegrable sweepBump MeasureTheory.volume (-1) 0 from
        sweepBump_continuous.intervalIntegrable _ _)
      (show IntervalIntegrable sweepBump MeasureTheory.volume 0 1 from
        sweepBump_continuous.intervalIntegrable _ _)
  have hleft : (∫ u in (-1:ℝ)..0, sweepBump u) = 1/2 := by
    have h1 : (∫ u in (-1:ℝ)..0, sweepBump u)
        = (∫ u in (-1:ℝ)..0, Real.smoothTransition (1 + u)) := by
      refine intervalIntegral.integral_congr (fun u hu => ?_)
      rw [Set.uIcc_of_le (by norm_num : (-1:ℝ) ≤ 0)] at hu
      rw [sweepBump]
      rw [Real.smoothTransition.one_of_one_le (show (1:ℝ) ≤ 1 - u by linarith [hu.2]), mul_one]
    rw [h1]
    have hshift : (∫ u in (-1:ℝ)..0, Real.smoothTransition (1 + u))
        = (∫ x in (0:ℝ)..1, Real.smoothTransition x) := by
      rw [intervalIntegral.integral_comp_add_left (fun x => Real.smoothTransition x) 1]
      norm_num
    rw [hshift, integral_smoothTransition_zero_one]
  have hright : (∫ u in (0:ℝ)..1, sweepBump u) = 1/2 := by
    have h1 : (∫ u in (0:ℝ)..1, sweepBump u)
        = (∫ u in (0:ℝ)..1, (1 - Real.smoothTransition u)) := by
      refine intervalIntegral.integral_congr (fun u hu => ?_)
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hu
      rw [sweepBump]
      rw [Real.smoothTransition.one_of_one_le (show (1:ℝ) ≤ 1 + u by linarith [hu.1]), one_mul]
      have := sweepTransition_symm u
      linarith
    rw [h1, intervalIntegral.integral_sub intervalIntegrable_const
      (Real.smoothTransition.continuous.intervalIntegrable 0 1)]
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one]
    rw [integral_smoothTransition_zero_one]; ring
  rw [← hadd, hleft, hright]; norm_num

/-- **The first moment of the bump vanishes** (the bump is even). -/
lemma integral_sweepBump_mul : (∫ u in (-1:ℝ)..1, u * sweepBump u) = 0 := by
  set f : ℝ → ℝ := fun u => u * sweepBump u with hf
  have hcomp : (∫ u in (-1:ℝ)..1, f (-u)) = (∫ u in (-1:ℝ)..1, f u) := by
    rw [intervalIntegral.integral_comp_neg f]; norm_num
  have hpoint : ∀ u : ℝ, f (-u) = -f u := by
    intro u
    show -u * sweepBump (-u) = -(u * sweepBump u)
    rw [sweepBump_even]; ring
  have hneg : (∫ u in (-1:ℝ)..1, f (-u)) = -(∫ u in (-1:ℝ)..1, f u) := by
    have : (∫ u in (-1:ℝ)..1, f (-u)) = (∫ u in (-1:ℝ)..1, -f u) :=
      intervalIntegral.integral_congr (fun u _ => hpoint u)
    rw [this, intervalIntegral.integral_neg]
  rw [hneg] at hcomp
  linarith

/-- **The second moment of the bump is positive** (it drives the strictness of the smoothing
estimates). -/
lemma integral_sweepBump_sq_pos : 0 < (∫ u in (-1:ℝ)..1, u ^ 2 * sweepBump u) := by
  have hcont : Continuous (fun u : ℝ => u ^ 2 * sweepBump u) :=
    continuous_id.pow 2 |>.mul sweepBump_continuous
  have hnonneg : ∀ u : ℝ, 0 ≤ u ^ 2 * sweepBump u :=
    fun u => mul_nonneg (sq_nonneg u) (sweepBump_nonneg u)
  have hle : (∫ u in ((1:ℝ)/4)..(1/2), u ^ 2 * sweepBump u)
      ≤ (∫ u in (-1:ℝ)..1, u ^ 2 * sweepBump u) := by
    refine intervalIntegral.integral_mono_interval (by norm_num) (by norm_num) (by norm_num) ?_
      (hcont.intervalIntegrable (-1) 1)
    exact Filter.Eventually.of_forall hnonneg
  have hlow : ∀ u ∈ Set.Icc ((1:ℝ)/4) (1/2),
      (1/16) * (Real.smoothTransition (1/2)) ≤ u ^ 2 * sweepBump u := by
    intro u hu
    have hb : sweepBump u = Real.smoothTransition (1 - u) := by
      rw [sweepBump]
      rw [Real.smoothTransition.one_of_one_le (show (1:ℝ) ≤ 1 + u by linarith [hu.1]), one_mul]
    have hle1 : (1:ℝ)/2 ≤ 1 - u := by linarith [hu.2]
    have hσ : Real.smoothTransition (1/2) ≤ Real.smoothTransition (1 - u) :=
      Real.smoothTransition.monotone hle1
    have hu2 : (1:ℝ)/16 ≤ u ^ 2 := by nlinarith [hu.1]
    have hnn : 0 ≤ Real.smoothTransition (1 - u) := Real.smoothTransition.nonneg _
    rw [hb]
    nlinarith [hu2, hσ, hnn, Real.smoothTransition.nonneg (1/2)]
  have hmin : (∫ u in ((1:ℝ)/4)..(1/2), ((1:ℝ)/16) * Real.smoothTransition (1/2))
      ≤ (∫ u in ((1:ℝ)/4)..(1/2), u ^ 2 * sweepBump u) :=
    intervalIntegral.integral_mono_on (by norm_num) intervalIntegrable_const
      (hcont.intervalIntegrable _ _) hlow
  have hval : (∫ u in ((1:ℝ)/4)..(1/2), ((1:ℝ)/16) * Real.smoothTransition (1/2))
      = (1/4) * ((1/16) * Real.smoothTransition (1/2)) := by
    rw [intervalIntegral.integral_const]; norm_num
  have hpos : 0 < Real.smoothTransition (1/2) := Real.smoothTransition.pos_of_pos (by norm_num)
  linarith [hval ▸ hmin, hle]

/-! ## Convolution fixes affine functions -/

/-- The blur of a constant `Space`-valued function. -/
lemma sweepBlur_const (p : Space) :
    (∫ u in (-1:ℝ)..1, sweepBump u • p) = p := by
  rw [intervalIntegral.integral_smul_const, integral_sweepBump, one_smul]

/-- The scalar blur of an affine real function: the form of the affine map is preserved
because the bump has mass `1` and vanishing first moment. -/
lemma sweepBlur_affine_scalar (t δ : ℝ) :
    (∫ u in (-1:ℝ)..1, (t - δ * u) * sweepBump u) = t := by
  have hsplit : ∀ u : ℝ, (t - δ * u) * sweepBump u = t * sweepBump u - δ * (u * sweepBump u) := by
    intro u; ring
  simp only [hsplit]
  rw [intervalIntegral.integral_sub (μ := MeasureTheory.volume)
    (f := fun u : ℝ => t * sweepBump u) (g := fun u : ℝ => δ * (u * sweepBump u))
    ((sweepBump_continuous.const_mul t).intervalIntegrable _ _)
    (((continuous_id.mul sweepBump_continuous).const_mul δ).intervalIntegrable _ _)]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_sweepBump, integral_sweepBump_mul]
  ring

/-- **The blur of an affine function is the function itself**: both `∫ sweepBump = 1` and the
vanishing of the first moment enter here.  This is the reason the blurred chord side of the sweep
is again an honest straight chord, and the blurred arc side is a reparametrisation. -/
lemma sweepBlur_affine (p v : Space) (t δ : ℝ) :
    (∫ u in (-1:ℝ)..1, sweepBump u • (p + (t - δ * u) • v)) = p + t • v := by
  have hpoint : (fun u : ℝ => sweepBump u • (p + (t - δ * u) • v))
      = fun u : ℝ => sweepBump u • p + ((t - δ * u) * sweepBump u) • v := by
    funext u
    rw [smul_add, smul_smul, mul_comm (sweepBump u) (t - δ * u)]
  have h1 : (∫ u in (-1:ℝ)..1, sweepBump u • p) = p := sweepBlur_const p
  have h2 : (∫ u in (-1:ℝ)..1, ((t - δ * u) * sweepBump u) • v) = t • v := by
    rw [intervalIntegral.integral_smul_const, sweepBlur_affine_scalar]
  rw [hpoint, intervalIntegral.integral_add (μ := MeasureTheory.volume)
    (f := fun u : ℝ => sweepBump u • p)
    (g := fun u : ℝ => ((t - δ * u) * sweepBump u) • v)
    ((sweepBump_continuous.smul continuous_const).intervalIntegrable _ _)
    ((((continuous_const.sub (continuous_const.mul continuous_id)).mul sweepBump_continuous).smul
      continuous_const).intervalIntegrable _ _)]
  rw [h1, h2]


/-
## Status and plan for `sweepFam_slices_window` (read this before attacking the `sorry`)

The target `Work.Drive.sweepFam_slices_window` asks: for every smooth knot `r`, every band-arc
data `D` and every `O`-avoiding arc, there is `L > 0` such that for all `0 < lam, δ₁, δ₂ ≤ L` and
all `σ ∈ [1/1000, 99/100]`, the doubly smoothed slice
`sweepFam r D lam δ₁ δ₂ σ` is injective on `[0, period)` with nonvanishing velocity.  Note that
`L` may depend on `r` and `d` (they are parameters of the theorem): the statement is *not*
uniform in the knot.

### Structural facts established in this file

* `integral_sweepBump : ∫ sweepBump = 1` and `integral_sweepBump_mul : ∫ u * sweepBump u = 0`
  (`sweepBump` is even).  Consequently *both* smoothing convolutions have total mass one and
  vanishing first moment: `sweepFam r D lam δ₁ δ₂ σ t` is a **convex combination** of the values
  of the chamfered loop in a window `(σ ∓ δ₂) × (t ∓ δ₁)`.
* `sweepBlur_affine : ∫ sweepBump u • (p + (t - δ u) • v) = p + t • v`: the blur of an affine map
  is the map itself.  Hence, *away from the four corners*, the slice is exactly
  * on the arc zone:  `t ↦ r(x(t - c δ₁ u))` blurred, i.e. a fixed `C^∞` reparametrisation of the
   blurred knot — the *arc part is a genuine curve*;
  * on the chord zone: a point of the *blurred chord* (the segment between the blurred endpoints
    `∫ sweepBump v • r (ta (σ - δ₂ v))` and `∫ sweepBump v • r (tb (σ - δ₂ v))`).

### The difficulty (traps found by numerical and local analysis — do not rediscover)

The naive route "the slice is a small `C¹` perturbation of the (injective) chamfered loop, hence
injective" is **false in general**: uniform closeness to an injective curve does not preserve
injectivity, and the `C¹` perturbation is *not* small at the corners (its derivative is `O(1/δ₁)`).
The route that does work has to be quantitative, and the margins are *tiny*:

* at the four corners the two strands (arc side and chord side) meet; the slice's local separation
  can be of order `lam · (knot constant)` (numerically `≈ 2·10⁻³ · lam` for the extremal
  "tangency" configurations below), and the velocity can dip to `≈ 10⁻³` (compared with a typical
  speed `≈ 0.4`).  Both quantities stay *positive* but the constants are knot dependent.
* the extremal configurations are the **tangency** ones, where the chord `T := r (tb) - r (ta)` is
  parallel to `r' (tb)` (or to `r' (ta)`).  There the chamfer's velocity
  `(2/period) • (sweepW • r' (tb) - T)` is *nearly* antiparallel to the chord's velocity
  `-(2/period) • T`; the mixture of the two can nearly cancel.  What saves injectivity and the
  velocity is the *next order* term: the chamfer vector is
  `lam • (sweepW • r' (tb) - T) - (lam * sweepW)²/2 • r'' (tb) + …`, and for an *analytic* knot this
  residue is never exactly parallel to `T` (it would force the knot to contain a line segment).
  This is why the theorem is true, and why the proof must be *analytic* (using the finite order of
  vanishing of e.g. `t ↦ ⟨r' (t), n⟩` at the tangency parameter), not merely `C¹`.
* `conclusion`: the correct architecture is (i) the quantitative local analysis of the four
  corners together with (ii) the two-scale argument (a definite local chord bound, then a
  separation bound for parameter differences above the smoothing width).  The workspace lemma
  `Work.Drive.correction_clauses_of_bounds` is exactly the right consumer for (ii) once the
  corner analysis supplies its hypotheses `hb1`, `hb2`, `hb3` for the *single-convolved* base
  slices `sweepSmoothT`, and once the second convolution (in `σ`) is shown to be a uniformly small
  `C¹` correction — this is the plan recorded in `sweepToNeedleFamily.lean`.
  WARNING: that plan silently assumes that all four corner angles of the chamfered loop are
  bounded away from `π`; the tangency configurations above are exactly the cases where this fails,
  and they need the separate (analytic) treatment described above.
-/



/-! ## The chord parameter of the chamfered loop -/

/-- The chord fraction used by `sweepLoopChamfer` on its chord zone: for a loop parameter with
`sweepParam t' ∈ [1/2 + lam/2, 1 - lam/2]` the loop is `sweepChord' r D s' (sweepChordParam lam
(sweepParam t'))`. -/
noncomputable def sweepChordParam (lam u : ℝ) : ℝ :=
  (1 - lam) - ((u - (1 / 2 + lam / 2)) / (1 / 2 - lam)) * (1 - 2 * lam)

end Work.Drive
