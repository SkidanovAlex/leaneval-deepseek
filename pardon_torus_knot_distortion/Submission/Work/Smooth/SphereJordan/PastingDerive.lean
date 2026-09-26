import Submission.Work.Smooth.SphereJordan.Pasting
import Submission.Work.Smooth.SphereJordan.Twist
import Submission.Work.Smooth.SphereJordan.injOn_arcPoint
import Submission.Work.Smooth.SphereJordan.continuous_piecewise_disc
import Submission.Work.Smooth.SphereJordan.exists_ball_avoiding_homeomorph
import Submission.Work.Smooth.SphereJordan.lift_of_range_subset
import Submission.Work.Topology.SphereSlicing.range_closedCurve_isCompact

/-!
# The cut-and-paste from the three named inputs: the proof

This file proves `Work.Topology.Classical.CutsAlongSubdisc` from the named inputs of
`Submission/Work/Smooth/SphereJordan/Pasting.lean`
(`AnnulusSchoenflies`, `SurfaceDiscPushOff`, and either the position hypothesis `CurvesInterior`
or the pinched surgery `PinchedPushThrough`); see the module docstring of that file for the
construction (discard a collar of the innermost curve, push the sub-disc it bounds off the surface,
glue the truncated outer piece to the cap).

The concrete shape of the new disc, with `e := D.e`, `γ := D.curves j`, `f` the innermost
sub-disc, `g : 𝔻 → 𝔻` the (injective, continuous) map with `e ∘ g = f`, `Θ` the Schoenflies
homeomorphism of the annulus form applied to `g`, and `z₁ θ := Θ⁻¹ (r₀ • e^{iθ})`:

* the **outer piece** is `z ↦ e (Θ₁.symm z)`, where `Θ₁` is the Schoenflies homeomorphism of the
  annulus form applied to `h₁ := Θ⁻¹ ∘ (r₀ • ·)`; it maps the circle of radius `1/2` to the curve
  `e ∘ z₁` and the circle `∂𝔻` identically to `α`;
* the **cap** is the disc `cap` given by `SurfaceDiscPushOff` with boundary `e ∘ z₁`;
* the **new disc** is `e' z = if ‖z‖ ≤ 1/2 then cap' (dblMap z) else e (Θ₁.symm z)`, with the
  total radial doubling map `dblMap` in place of `z ↦ 2z` and `cap' := cap ∘ twistFun s₁` the cap
  with the orientation sign `s₁` of the second application of `AnnulusSchoenflies` absorbed by the
  disc twist of `Submission/Work/Smooth/SphereJordan/Twist` (see the README, §5.2/§6.4).
-/

open Set
open LeanEval.KnotTheory.PardonDistortion

namespace Work.Smooth.SphereJordan

noncomputable section

/-! ## Elementary facts about the model disc -/

theorem norm_coe_le_one (z : Disc) : ‖((z : Disc) : ℂ)‖ ≤ 1 := by
  have h := z.2
  rwa [Metric.mem_closedBall, dist_zero_right] at h

theorem norm_halfCirclePoint (θ : ℝ) : ‖((halfCirclePoint θ : Disc) : ℂ)‖ = 1 / 2 := by
  rw [halfCirclePoint_coe, norm_mul, Work.Smooth.Jordan.circlePoint_coe,
    Complex.norm_exp_ofReal_mul_I, mul_one]
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.norm_def,
    Complex.normSq_ofReal, Real.sqrt_mul_self (by norm_num : (0 : ℝ) ≤ 1 / 2)]

/-- A point of the model disc of norm `1/2` is `halfCirclePoint θ` for some `θ`. -/
theorem exists_halfCirclePoint_eq (z : Disc) (hz : ‖((z : Disc) : ℂ)‖ = 1 / 2) :
    ∃ θ : ℝ, z = halfCirclePoint θ := by
  have h2z : ‖(2 * ((z : Disc) : ℂ))‖ = 1 := by
    rw [norm_mul, hz]
    norm_num
  obtain ⟨θ, hθ⟩ := Work.Smooth.Jordan.exists_circlePoint_eq
    ⟨2 * ((z : Disc) : ℂ), by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact le_of_eq h2z⟩ h2z
  refine ⟨θ, ?_⟩
  apply Subtype.ext
  rw [halfCirclePoint_coe]
  have hval : ((Work.Smooth.Jordan.circlePoint θ : Disc) : ℂ) = 2 * ((z : Disc) : ℂ) :=
    congrArg (fun w : Disc => (w : ℂ)) hθ
  rw [hval]
  ring

/-! ## The total radial doubling map of the model disc -/

/-- The scalar factor of the doubling map: `2` on the half-disc `{‖z‖ ≤ 1/2}` and `1/‖z‖` outside
it. -/
def dblFactor (z : Disc) : ℂ :=
  if ‖((z : Disc) : ℂ)‖ ≤ 1 / 2 then (2 : ℂ)
    else Complex.ofReal ((‖((z : Disc) : ℂ)‖)⁻¹)

theorem dblFactor_of_le {z : Disc} (hz : ‖((z : Disc) : ℂ)‖ ≤ 1 / 2) : dblFactor z = 2 := by
  show (if ‖((z : Disc) : ℂ)‖ ≤ 1 / 2 then (2 : ℂ) else _) = 2
  rw [if_pos hz]

theorem dblFactor_of_gt {z : Disc} (hz : 1 / 2 < ‖((z : Disc) : ℂ)‖) :
    dblFactor z = Complex.ofReal ((‖((z : Disc) : ℂ)‖)⁻¹) := by
  show (if ‖((z : Disc) : ℂ)‖ ≤ 1 / 2 then (2 : ℂ) else _) = _
  rw [if_neg (not_le.mpr hz)]

theorem continuous_dblFactor : Continuous dblFactor := by
  apply continuous_if
  · intro z hz
    have hzeq : ‖((z : Disc) : ℂ)‖ = 1 / 2 :=
      frontier_le_subset_eq (continuous_norm.comp continuous_subtype_val) continuous_const hz
    rw [hzeq]
    norm_num
  · exact continuous_const.continuousOn
  · have h1 : ContinuousOn (fun z : Disc => ((‖((z : Disc) : ℂ)‖)⁻¹ : ℝ))
        {z : Disc | (1 : ℝ) / 2 ≤ ‖((z : Disc) : ℂ)‖} :=
      ContinuousOn.inv₀ ((continuous_norm.comp continuous_subtype_val).continuousOn)
        (fun z hz => by
          have : ((1 : ℝ) / 2) ≤ ‖((z : Disc) : ℂ)‖ := hz
          positivity)
    have hsub : closure {x : Disc | ¬ ‖((x : Disc) : ℂ)‖ ≤ 1 / 2} ⊆
        {z : Disc | (1 : ℝ) / 2 ≤ ‖((z : Disc) : ℂ)‖} := by
      simpa only [not_le] using
        closure_lt_subset_le (f := fun _ : Disc => (1 : ℝ) / 2)
          (g := fun z : Disc => ‖((z : Disc) : ℂ)‖) continuous_const
          (continuous_norm.comp continuous_subtype_val)
    exact (Complex.continuous_ofReal.comp_continuousOn h1).mono hsub

/-- The **total radial doubling map** of the model disc: it is `z ↦ 2z` on the closed half-disc
`{‖z‖ ≤ 1/2}` and `z ↦ z/‖z‖` (the radial projection to the boundary circle) outside it.  It is
continuous, agrees with the doubling on the half-disc, and maps the circle of radius `1/2` onto the
boundary circle preserving the parametrisation. -/
def dblMap (z : Disc) : Disc :=
  ⟨dblFactor z * ((z : Disc) : ℂ), by
    rw [Metric.mem_closedBall, dist_zero_right, dblFactor]
    split_ifs with h
    · have h2 : ‖(2 : ℂ)‖ = 2 := by
        rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.norm_def, Complex.normSq_ofReal,
          Real.sqrt_mul_self (by norm_num : (0 : ℝ) ≤ 2)]
      rw [norm_mul, h2]
      nlinarith [norm_coe_le_one z]
    · have hz : 0 < ‖((z : Disc) : ℂ)‖ := by
        have h1 : (0 : ℝ) < 1 / 2 := by norm_num
        exact lt_trans h1 (not_le.mp h)
      rw [norm_mul, Complex.norm_def, Complex.normSq_ofReal,
        Real.sqrt_mul_self (by positivity : (0 : ℝ) ≤ (‖((z : Disc) : ℂ)‖)⁻¹),
        inv_mul_cancel₀ (ne_of_gt hz)]⟩

theorem continuous_dblMap : Continuous dblMap :=
  Continuous.subtype_mk (continuous_dblFactor.mul continuous_subtype_val) _

theorem dblMap_coe (z : Disc) :
    ((dblMap z : Disc) : ℂ) = dblFactor z * ((z : Disc) : ℂ) := rfl

/-- On the half-disc the doubling map is multiplication by `2`. -/
theorem dblMap_coe_of_le {z : Disc} (hz : ‖((z : Disc) : ℂ)‖ ≤ 1 / 2) :
    ((dblMap z : Disc) : ℂ) = 2 * ((z : Disc) : ℂ) := by
  rw [dblMap_coe, dblFactor_of_le hz]

/-- The doubling map carries the circle of radius `1/2` onto the boundary circle, preserving the
parametrisation. -/
theorem dblMap_halfCirclePoint (θ : ℝ) :
    dblMap (halfCirclePoint θ) = Work.Smooth.Jordan.circlePoint θ := by
  apply Subtype.ext
  rw [dblMap_coe_of_le (le_of_eq (norm_halfCirclePoint θ)), halfCirclePoint_coe]
  ring

/-- The doubling map is injective on the closed half-disc. -/
theorem dblMap_injOn_half {z z' : Disc} (hz : ‖((z : Disc) : ℂ)‖ ≤ 1 / 2)
    (hz' : ‖((z' : Disc) : ℂ)‖ ≤ 1 / 2) (h : dblMap z = dblMap z') : z = z' := by
  apply Subtype.ext
  have h2 : 2 * ((z : Disc) : ℂ) = 2 * ((z' : Disc) : ℂ) := by
    rw [← dblMap_coe_of_le hz, ← dblMap_coe_of_le hz', h]
  exact mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) h2

/-! ## The scaling map of the model disc -/

/-- The scaling map `z ↦ r • z` of the model disc, for `0 ≤ r ≤ 1`. -/
def scaleMap (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) : Disc → Disc :=
  fun z => ⟨(r : ℂ) * ((z : Disc) : ℂ), by
    rw [Metric.mem_closedBall, dist_zero_right, norm_mul]
    have hn : ‖(r : ℂ)‖ = r := by
      rw [Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self hr0]
    rw [hn]
    nlinarith [norm_coe_le_one z]⟩

theorem scaleMap_apply (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (z : Disc) :
    ((scaleMap r hr0 hr1 z : Disc) : ℂ) = (r : ℂ) * ((z : Disc) : ℂ) := rfl

theorem norm_scaleMap (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (z : Disc) :
    ‖((scaleMap r hr0 hr1 z : Disc) : ℂ)‖ = r * ‖((z : Disc) : ℂ)‖ := by
  rw [scaleMap_apply, norm_mul]
  congr 1
  rw [Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self hr0]

theorem continuous_scaleMap (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    Continuous (scaleMap r hr0 hr1) :=
  Continuous.subtype_mk (continuous_const.mul continuous_subtype_val) _

theorem scaleMap_injective (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hrpos : 0 < r) :
    Function.Injective (scaleMap r hr0 hr1) := by
  intro a b hab
  have h : (r : ℂ) * ((a : Disc) : ℂ) = (r : ℂ) * ((b : Disc) : ℂ) := by
    rw [← scaleMap_apply r hr0 hr1 a, ← scaleMap_apply r hr0 hr1 b, hab]
  exact Subtype.ext (mul_left_cancel₀ (by exact_mod_cast (ne_of_gt hrpos)) h)

theorem range_scaleMap (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hrpos : 0 < r) :
    Set.range (scaleMap r hr0 hr1) = {w : Disc | ‖((w : Disc) : ℂ)‖ ≤ r} := by
  ext w
  constructor
  · rintro ⟨z, rfl⟩
    simp only [Set.mem_setOf_eq]
    rw [norm_scaleMap]
    nlinarith [norm_coe_le_one z]
  · intro hw
    have hrne : (r : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hrpos)
    have hinv : ‖((r : ℂ)⁻¹)‖ = r⁻¹ := by
      rw [norm_inv, Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self hr0]
    refine ⟨⟨(r : ℂ)⁻¹ * ((w : Disc) : ℂ), ?_⟩, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right, norm_mul, hinv]
      rw [inv_mul_le_iff₀ hrpos, mul_one]
      exact hw
    · apply Subtype.ext
      rw [scaleMap_apply]
      rw [← mul_assoc, mul_inv_cancel₀ hrne, one_mul]

/-- The norm of the standard boundary circle point. -/
theorem norm_circlePoint (θ : ℝ) : ‖((Work.Smooth.Jordan.circlePoint θ : Disc) : ℂ)‖ = 1 := by
  rw [Work.Smooth.Jordan.circlePoint_coe, Complex.norm_exp_ofReal_mul_I]

/-- **A point on the closed half-disc is in the image of `h`** — the "closed" direction of the
range clause of `AnnulusSchoenflies`. -/
theorem mem_range_of_norm_le_half (Θ : Disc ≃ₜ Disc) (h : C(Disc, Disc))
    (hΘ : ∀ x : Disc, (∃ z : Disc, h z = x) ↔ ‖((Θ x : Disc) : ℂ)‖ ≤ 1 / 2) :
    ∀ x : Disc, ‖((Θ x : Disc) : ℂ)‖ ≤ 1 / 2 → x ∈ Set.range h :=
  fun x hx => (hΘ x).mpr hx

/-! ## The cut-and-paste -/

/-- **The cut-and-paste of Pardon's second innermost argument**, from `AnnulusSchoenflies` and
`SurfaceDiscPushOff`, for slice-disc data whose innermost curve misses the boundary curve of the
disc and whose disc is *locally flat* (`LocallyFlat D.e`, the tameness that the push-off of the
surface disc needs; it is not a consequence of the `SliceDisc` structure, which assumes only that
the disc is embedded continuously). -/
theorem cutsAlongSubdisc_inside (hA : AnnulusSchoenflies) {P : Work.CoreTopology.ParamTorus}
    (hB : SurfaceDiscPushOff P) (D : Work.Topology.SphereSlicing.SliceDisc P)
    (htame : LocallyFlat D.e) (j : D.ι)
    (f : C(Disc, R3))
    (hf_inj : Function.Injective f)
    (hf_bd : ∀ θ : ℝ, f (Work.Smooth.Jordan.circlePoint θ) = (D.curves j).γ θ)
    (hf_off : ∀ z : Disc, ‖(z : ℂ)‖ < 1 → f z ∉ P.carrier)
    (hf_sub : Set.range f ⊆ Set.range D.e)
    (hf_disj : ∀ i : D.ι, i ≠ j → Disjoint (Set.range (D.curves i).γ)
      (f '' {z : Disc | ‖(z : ℂ)‖ < 1}))
    (hpos : Disjoint (Set.range (D.curves j).γ)
      (Set.range fun θ : ℝ => D.e (Work.Smooth.Jordan.circlePoint θ))) :
    ∃ e' : C(Disc, R3),
      Function.Injective e' ∧
      (∀ θ : ℝ, e' (Work.Smooth.Jordan.circlePoint θ) = D.α.γ θ) ∧
      (∀ i : D.ι, i ≠ j → Set.range (D.curves i).γ ⊆ Set.range e') ∧
      (∀ z : Disc, ‖(z : ℂ)‖ < 1 → e' z ∈ P.carrier →
        ∃ i : D.ι, i ≠ j ∧ e' z ∈ Set.range (D.curves i).γ) := by
  classical
  -- the lift of the innermost sub-disc through the embedding `D.e`
  obtain ⟨g, hg_inj, hg_spec⟩ := lift_of_range_subset D.e D.inj f hf_inj hf_sub
  -- the position hypothesis: the innermost curve misses the boundary curve
  set hdisj := hpos with hdisj_def
  -- the model curve of the innermost curve lies in the open disc
  have hg_bd : ∀ θ : ℝ, ‖((g (Work.Smooth.Jordan.circlePoint θ) : Disc) : ℂ)‖ < 1 := by
    intro θ
    refine lt_of_le_of_ne (norm_coe_le_one _) ?_
    intro hnorm
    obtain ⟨σ, hσ⟩ :=
      Work.Smooth.Jordan.exists_circlePoint_eq (g (Work.Smooth.Jordan.circlePoint θ)) hnorm
    have hmem : (D.curves j).γ θ ∈ Set.range (D.curves j).γ := ⟨θ, rfl⟩
    have hmem2 : (D.curves j).γ θ ∈
        Set.range fun τ : ℝ => D.e (Work.Smooth.Jordan.circlePoint τ) :=
      ⟨σ, by
        show D.e (Work.Smooth.Jordan.circlePoint σ) = (D.curves j).γ θ
        rw [hσ]
        exact (hg_spec _).trans (hf_bd θ)⟩
    exact Set.disjoint_left.mp hdisj hmem hmem2
  -- the annulus form of Schoenflies, applied to `g`
  obtain ⟨Θ, s, hs, hΘbd, hΘγ, hΘimg, hΘimglt⟩ := hA g hg_inj hg_bd
  -- the pull-backs of the other intersection curves
  haveI : CompactSpace Disc := isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : ℂ) 1)
  let K : {i : D.ι // i ≠ j} → Set Disc :=
    fun i => {z : Disc | D.e z ∈ Set.range (D.curves i.1).γ}
  have hK : ∀ i, IsCompact (K i) := by
    intro i
    exact (IsClosed.preimage D.e.continuous
      (Work.Topology.SphereSlicing.range_closedCurve_isCompact (D.curves i.1)).isClosed).isCompact
  have hdisjK : ∀ i, Disjoint (K i) (Θ ⁻¹' {x : Disc | ‖((x : Disc) : ℂ)‖ ≤ 1 / 2}) := by
    intro i
    rw [Set.disjoint_left]
    intro z hz hz'
    have hz'' : ‖((Θ z : Disc) : ℂ)‖ ≤ 1 / 2 := hz'
    rcases lt_or_eq_of_le hz'' with hlt | heq
    · -- in the open half-disc: the preimage is in the image of `g` on the open disc
      obtain ⟨w, hgw⟩ := (hΘimg z).mpr (le_of_lt hlt)
      have hw : ‖((w : Disc) : ℂ)‖ < 1 := (hΘimglt w).mpr (by rw [hgw]; exact hlt)
      have h1 : D.e z ∈ P.carrier := by
        obtain ⟨t, ht⟩ := hz
        rw [← ht]
        exact (D.curves i.1).mem t
      have h2 : D.e z ∉ P.carrier := by
        have hzeq : D.e z = f w := by rw [← hgw, hg_spec]
        rw [hzeq]
        exact hf_off w hw
      exact h2 h1
    · -- on the sphere of radius `1/2`: the preimage is on the curve `γ`
      have hzJ : z ∈ Set.range (fun τ : ℝ => g (Work.Smooth.Jordan.circlePoint τ)) := by
        obtain ⟨w, hw⟩ := mem_range_of_norm_le_half Θ g hΘimg z (le_of_eq heq)
        have hwbd : ‖((w : Disc) : ℂ)‖ = 1 := by
          refine le_antisymm (norm_coe_le_one w) (le_of_not_gt ?_)
          intro hlt
          have h' : ‖((Θ (g w) : Disc) : ℂ)‖ < 1 / 2 := (hΘimglt w).mp hlt
          rw [hw, heq] at h'
          exact absurd h' (lt_irrefl (1 / 2))
        obtain ⟨τ, hτ⟩ := Work.Smooth.Jordan.exists_circlePoint_eq w hwbd
        exact ⟨τ, by
          show g (Work.Smooth.Jordan.circlePoint τ) = z
          rw [hτ, hw]⟩
      obtain ⟨τ, hτ⟩ := hzJ
      have hzr : D.e z ∈ Set.range (D.curves i.1).γ := hz
      refine Set.disjoint_left.mp (D.curves_disjoint i.2) hzr ?_
      exact ⟨τ, by rw [← hτ, hg_spec, hf_bd τ]⟩
  -- the truncation radius
  obtain ⟨r₀, hr₀lo, hr₀hi, hr₀disj⟩ := exists_ball_avoiding_homeomorph Θ _ K hK hdisjK
  have hr₀pos : 0 < r₀ := lt_trans (by norm_num) hr₀lo
  have hr₀le : r₀ ≤ 1 := le_of_lt hr₀hi
  -- the truncation map `h₁ = Θ⁻¹ ∘ (r₀ ·)` and its boundary curve `z₁`
  let h₁ : C(Disc, Disc) := ⟨fun z => Θ.symm (scaleMap r₀ (le_of_lt hr₀pos) hr₀le z),
    Θ.symm.continuous.comp (continuous_scaleMap r₀ (le_of_lt hr₀pos) hr₀le)⟩
  let z₁ : ℝ → Disc := fun θ => Θ.symm (arcPoint r₀ θ)
  have hz₁_spec : ∀ θ : ℝ, h₁ (Work.Smooth.Jordan.circlePoint θ) = z₁ θ := by
    intro θ
    show Θ.symm (scaleMap r₀ (le_of_lt hr₀pos) hr₀le (Work.Smooth.Jordan.circlePoint θ))
      = Θ.symm (arcPoint r₀ θ)
    have h2 : scaleMap r₀ (le_of_lt hr₀pos) hr₀le (Work.Smooth.Jordan.circlePoint θ)
        = arcPoint r₀ θ := by
      apply Subtype.ext
      rw [scaleMap_apply, arcPoint_eq_radiusPoint r₀ θ (le_of_lt hr₀pos) hr₀le, radiusPoint_coe]
    rw [h2]
  have h₁_inj : Function.Injective h₁ := by
    intro a b hab
    have h2 : scaleMap r₀ (le_of_lt hr₀pos) hr₀le a
        = scaleMap r₀ (le_of_lt hr₀pos) hr₀le b := Θ.symm.injective hab
    exact scaleMap_injective r₀ (le_of_lt hr₀pos) hr₀le hr₀pos h2
  have hnot_one : ∀ θ : ℝ, ‖((arcPoint r₀ θ : Disc) : ℂ)‖ ≠ 1 := by
    intro θ h1
    have hr : ‖((arcPoint r₀ θ : Disc) : ℂ)‖ = r₀ :=
      norm_arcPoint r₀ θ (le_of_lt hr₀pos) hr₀le
    rw [hr] at h1
    linarith [hr₀hi]
  have hnot_one_z₁ : ∀ θ : ℝ, ‖((z₁ θ : Disc) : ℂ)‖ ≠ 1 := by
    intro θ h1
    obtain ⟨σ, hσ⟩ := Work.Smooth.Jordan.exists_circlePoint_eq (z₁ θ) h1
    apply hnot_one θ
    have h2 : Θ (z₁ θ) = arcPoint r₀ θ := Θ.apply_symm_apply _
    rw [← h2, ← hσ, hΘbd σ]
    exact norm_circlePoint σ
  have h₁_bd : ∀ θ : ℝ, ‖((h₁ (Work.Smooth.Jordan.circlePoint θ) : Disc) : ℂ)‖ < 1 := by
    intro θ
    rw [hz₁_spec θ]
    exact lt_of_le_of_ne (norm_coe_le_one _) (hnot_one_z₁ θ)
  -- the annulus form of Schoenflies, applied to `h₁`
  obtain ⟨Θ₁, s₁, hs₁, hΘ₁bd, hΘ₁γ, hΘ₁img, hΘ₁imglt⟩ := hA h₁ h₁_inj h₁_bd
  -- the twisted parametrisation of the inner boundary curve of the outer piece
  have hΘ₁z : ∀ σ : ℝ, Θ₁ (z₁ (s₁ * σ)) = halfCirclePoint σ := fun σ => by
    rw [← hz₁_spec (s₁ * σ)]
    exact hΘ₁γ σ
  -- properties of `z₁`
  have harc_cont : Continuous (fun θ : ℝ => arcPoint r₀ θ) := by
    have hfun : (fun θ : ℝ => arcPoint r₀ θ)
        = fun θ : ℝ => scaleMap r₀ (le_of_lt hr₀pos) hr₀le
            (Work.Smooth.Jordan.circlePoint θ) := by
      funext θ
      apply Subtype.ext
      rw [scaleMap_apply, arcPoint_eq_radiusPoint r₀ θ (le_of_lt hr₀pos) hr₀le, radiusPoint_coe]
    rw [hfun]
    exact (continuous_scaleMap r₀ (le_of_lt hr₀pos) hr₀le).comp
      Work.InnermostDisk.continuous_circlePoint
  have hz₁_cont : Continuous z₁ := Θ.symm.continuous.comp harc_cont
  have hz₁_per : Function.Periodic z₁ (2 * Real.pi) := by
    intro θ
    show Θ.symm (arcPoint r₀ (θ + 2 * Real.pi)) = Θ.symm (arcPoint r₀ θ)
    have h2 : arcPoint r₀ (θ + 2 * Real.pi) = arcPoint r₀ θ := by
      have h3 : Work.Smooth.Jordan.circlePoint (θ + 2 * Real.pi)
          = Work.Smooth.Jordan.circlePoint θ :=
        Work.InnermostDisk.circlePoint_add_two_pi θ
      apply Subtype.ext
      rw [arcPoint_eq_radiusPoint r₀ (θ + 2 * Real.pi) (le_of_lt hr₀pos) hr₀le,
        arcPoint_eq_radiusPoint r₀ θ (le_of_lt hr₀pos) hr₀le, radiusPoint_coe, radiusPoint_coe, h3]
    rw [h2]
  have hz₁_inj : Set.InjOn z₁ (Set.Ico 0 (2 * Real.pi)) := by
    intro a ha b hb hab
    have h1 : arcPoint r₀ a = arcPoint r₀ b := Θ.symm.injective hab
    exact injOn_arcPoint r₀ (le_of_lt hr₀pos) hr₀le (ne_of_gt hr₀pos) ha hb h1
  have hz₁_norm : ∀ θ : ℝ, ‖((z₁ θ : Disc) : ℂ)‖ < 1 := fun θ =>
    lt_of_le_of_ne (norm_coe_le_one _) (hnot_one_z₁ θ)
  -- `g(𝔻)` meets the half-disc, and its image lies in `h₁(𝔻)` inside the half-disc
  have hΘg : ∀ z : Disc, ‖((Θ (g z) : Disc) : ℂ)‖ ≤ 1 / 2 := by
    intro z
    rcases lt_or_eq_of_le (norm_coe_le_one z) with hz | hz
    · exact (hΘimg (g z)).mp ⟨z, rfl⟩
    · obtain ⟨σ, hσ⟩ := Work.Smooth.Jordan.exists_circlePoint_eq z hz
      have hss : s * (s * σ) = σ := by rcases hs with h | h <;> rw [h] <;> ring
      rw [← hσ, ← hss, hΘγ (s * σ)]
      exact le_of_eq (norm_halfCirclePoint (s * σ))
  have hrange_h₁ : Set.range h₁ = Θ ⁻¹' {x : Disc | ‖((x : Disc) : ℂ)‖ ≤ r₀} := by
    ext w
    constructor
    · rintro ⟨z, rfl⟩
      show ‖((Θ (Θ.symm (scaleMap r₀ (le_of_lt hr₀pos) hr₀le z)) : Disc) : ℂ)‖ ≤ r₀
      rw [Θ.apply_symm_apply, norm_scaleMap]
      nlinarith [norm_coe_le_one z, hr₀hi]
    · intro hw
      have hw' : ‖((Θ w : Disc) : ℂ)‖ ≤ r₀ := hw
      have hmem : Θ w ∈ Set.range (scaleMap r₀ (le_of_lt hr₀pos) hr₀le) := by
        rw [range_scaleMap r₀ (le_of_lt hr₀pos) hr₀le hr₀pos]
        exact hw'
      obtain ⟨u, hu⟩ := hmem
      exact ⟨u, by
        show Θ.symm (scaleMap r₀ (le_of_lt hr₀pos) hr₀le u) = w
        rw [hu, Θ.symm_apply_apply]⟩
  have hg_in_h₁ : ∀ t : Disc, ∃ u : Disc, ‖((u : Disc) : ℂ)‖ < 1 ∧ h₁ u = g t := by
    intro t
    have h1 : ‖((Θ (g t) : Disc) : ℂ)‖ ≤ 1 / 2 := hΘg t
    have hlt : ‖((Θ (g t) : Disc) : ℂ)‖ < r₀ := lt_of_le_of_lt h1 hr₀lo
    have hmem : Θ (g t) ∈ Set.range (scaleMap r₀ (le_of_lt hr₀pos) hr₀le) := by
      rw [range_scaleMap r₀ (le_of_lt hr₀pos) hr₀le hr₀pos]
      exact le_of_lt hlt
    obtain ⟨u, hu⟩ := hmem
    refine ⟨u, ?_, ?_⟩
    · have hnorm := norm_scaleMap r₀ (le_of_lt hr₀pos) hr₀le u
      rw [hu] at hnorm
      have hlt' : r₀ * ‖((u : Disc) : ℂ)‖ < r₀ * 1 := by rw [← hnorm]; simpa using hlt
      simpa using (mul_lt_mul_iff_of_pos_left hr₀pos).mp hlt'
    · show Θ.symm (scaleMap r₀ (le_of_lt hr₀pos) hr₀le u) = g t
      rw [hu, Θ.symm_apply_apply]
  -- the truncation curve misses the surface
  have hz₁_off : ∀ θ : ℝ, D.e (z₁ θ) ∉ P.carrier := by
    intro θ hmem
    have hzn : ‖((z₁ θ : Disc) : ℂ)‖ < 1 := hz₁_norm θ
    obtain ⟨i, hi⟩ := D.covers (z₁ θ) hzn hmem
    have hΘz₁ : ‖((Θ (z₁ θ) : Disc) : ℂ)‖ = r₀ := by
      rw [show Θ (z₁ θ) = arcPoint r₀ θ from Θ.apply_symm_apply _, norm_arcPoint r₀ θ
        (le_of_lt hr₀pos) hr₀le]
    rcases eq_or_ne i j with rfl | hij
    · obtain ⟨t, ht⟩ := hi
      have hzeq : z₁ θ = g (Work.Smooth.Jordan.circlePoint t) := by
        apply D.inj
        rw [hg_spec]
        exact ht.symm.trans (hf_bd t).symm
      have hle : ‖((Θ (z₁ θ) : Disc) : ℂ)‖ ≤ 1 / 2 := by
        rw [hzeq]
        exact hΘg (Work.Smooth.Jordan.circlePoint t)
      rw [hΘz₁] at hle
      linarith [hr₀lo]
    · have hmemK : z₁ θ ∈ K ⟨i, hij⟩ := hi
      have hball : z₁ θ ∈ Θ ⁻¹' {x : Disc | ‖((x : Disc) : ℂ)‖ ≤ r₀} := by
        show ‖((Θ (z₁ θ) : Disc) : ℂ)‖ ≤ r₀
        rw [hΘz₁]
      exact (Set.disjoint_left.mp (hr₀disj ⟨i, hij⟩) hmemK) hball
  -- the cap given by the push-off of the surface disc
  obtain ⟨cap, hcap_inj, hcap_bd, hcap_off, hcap_meet⟩ :=
    hB D.e D.inj (fun θ => by
      rw [show D.e (Work.Smooth.Jordan.circlePoint θ) = D.α.γ θ from D.boundary θ]
      exact (D.α).mem θ)
      (D.curves j) (D.curves_subset j)
      (Work.InnermostDisk.boundsDiscInSurface_of_not_isEssential P (D.curves_inessential j))
      z₁ hz₁_cont hz₁_per hz₁_inj hz₁_norm hz₁_off h₁ h₁_inj hz₁_spec
      (by
        rintro y ⟨t, rfl⟩
        obtain ⟨u, -, hu⟩ := hg_in_h₁ (Work.Smooth.Jordan.circlePoint t)
        exact ⟨g (Work.Smooth.Jordan.circlePoint t), ⟨u, hu⟩,
          by show D.e (g (Work.Smooth.Jordan.circlePoint t)) = (D.curves j).γ t
             rw [hg_spec]
             exact hf_bd t⟩)
      -- the innermost clause: the interior of the disc spanned by `z₁` meets `F` only along `γ`
      (by
        intro w hw hmem
        have hwlt : ‖((h₁ w : Disc) : ℂ)‖ < 1 := by
          refine lt_of_le_of_ne (norm_coe_le_one _) ?_
          intro h1
          obtain ⟨τ, hτ⟩ := Work.Smooth.Jordan.exists_circlePoint_eq (h₁ w) h1
          have h2 : ‖((Θ (h₁ w) : Disc) : ℂ)‖ = 1 := by
            rw [← hτ, hΘbd τ]
            exact norm_circlePoint τ
          have h3 : (Θ (h₁ w) : Disc) = scaleMap r₀ (le_of_lt hr₀pos) hr₀le w := by
            show Θ (Θ.symm (scaleMap r₀ (le_of_lt hr₀pos) hr₀le w))
              = scaleMap r₀ (le_of_lt hr₀pos) hr₀le w
            rw [Θ.apply_symm_apply]
          rw [h3, norm_scaleMap] at h2
          nlinarith [norm_coe_le_one w, hr₀hi]
        obtain ⟨i, hi⟩ := D.covers (h₁ w) hwlt hmem
        rcases eq_or_ne i j with rfl | hij
        · exact hi
        · exfalso
          have hmemK : h₁ w ∈ K ⟨i, hij⟩ := hi
          have hball : h₁ w ∈ Θ ⁻¹' {x : Disc | ‖((x : Disc) : ℂ)‖ ≤ r₀} := by
            rw [← hrange_h₁]
            exact ⟨w, rfl⟩
          exact (Set.disjoint_left.mp (hr₀disj ⟨i, hij⟩) hmemK) hball)
        -- the tameness of the disc (the hypothesis `LocallyFlat D.e` of the slice disc)
        htame
  -- the cap with the orientation sign of `h₁` absorbed: its boundary curve is the curve
  -- `θ ↦ D.e (z₁ (s₁ * θ))`, which is the inner boundary curve of the outer piece
  let cap' : C(Disc, R3) := cap.comp (twistFun s₁)
  have hcap'_bd : ∀ θ : ℝ, cap' (Work.Smooth.Jordan.circlePoint θ) = D.e (z₁ (s₁ * θ)) := by
    intro θ
    show cap (twistFun s₁ (Work.Smooth.Jordan.circlePoint θ)) = D.e (z₁ (s₁ * θ))
    rw [twistFun_circlePoint hs₁ θ, hcap_bd (s₁ * θ)]
  have hcap'_inj : Function.Injective cap' := hcap_inj.comp (twistFun_injective hs₁)
  have hcap'_off : ∀ z : Disc, ‖(z : ℂ)‖ < 1 → cap' z ∉ P.carrier := by
    intro z hz
    exact hcap_off (twistFun s₁ z) (by rwa [twistFun_norm])
  have hcap'_meet : ∀ z : Disc, ‖(z : ℂ)‖ < 1 → cap' z ∈ Set.range D.e →
      cap' z ∈ Set.range fun θ : ℝ => D.e (z₁ θ) := by
    intro z hz h
    exact hcap_meet (twistFun s₁ z) (by rwa [twistFun_norm]) h
  -- the outer piece and the glued disc
  have hcap_dbl_cont : Continuous (fun z : Disc => cap' (dblMap z)) :=
    cap'.continuous.comp continuous_dblMap
  have hout_cont : Continuous (fun z : Disc => D.e (Θ₁.symm z)) :=
    D.e.continuous.comp Θ₁.symm.continuous
  have hagree : ∀ z : Disc, ‖((z : Disc) : ℂ)‖ = 1 / 2 →
      cap' (dblMap z) = D.e (Θ₁.symm z) := by
    intro z hz
    obtain ⟨σ, rfl⟩ := exists_halfCirclePoint_eq z hz
    show cap' (dblMap (halfCirclePoint σ)) = D.e (Θ₁.symm (halfCirclePoint σ))
    rw [dblMap_halfCirclePoint, hcap'_bd σ, ← hΘ₁z σ, Θ₁.symm_apply_apply]
  let e' : C(Disc, R3) :=
    ⟨fun z => if ‖((z : Disc) : ℂ)‖ ≤ 1 / 2 then cap' (dblMap z) else D.e (Θ₁.symm z),
      continuous_piecewise_disc (fun z : Disc => cap' (dblMap z))
        (fun z : Disc => D.e (Θ₁.symm z)) hcap_dbl_cont hout_cont hagree⟩
  -- the curve `z₁` is the inner boundary curve of the outer piece
  have hz₁range : ∀ w : Disc, w ∈ Set.range z₁ ↔ ‖((Θ₁ w : Disc) : ℂ)‖ = 1 / 2 := by
    intro w
    constructor
    · rintro ⟨θ, rfl⟩
      have hss : s₁ * (s₁ * θ) = θ := by rcases hs₁ with h | h <;> rw [h] <;> ring
      have h2 : Θ₁ (z₁ θ) = halfCirclePoint (s₁ * θ) := by
        simpa [hss] using hΘ₁z (s₁ * θ)
      rw [h2, norm_halfCirclePoint]
    · intro hw
      obtain ⟨σ, hσ⟩ := exists_halfCirclePoint_eq (Θ₁ w) hw
      refine ⟨s₁ * σ, ?_⟩
      apply Θ₁.injective
      rw [hΘ₁z σ, hσ]
  -- the new disc is embedded
  have he'_inj : Function.Injective e' := by
    intro z z' h
    by_cases hz : ‖((z : Disc) : ℂ)‖ ≤ 1 / 2
    · by_cases hz' : ‖((z' : Disc) : ℂ)‖ ≤ 1 / 2
      · have h1 : cap' (dblMap z) = cap' (dblMap z') := by
          have hh := h
          rwa [show e' z = cap' (dblMap z) from if_pos hz,
            show e' z' = cap' (dblMap z') from if_pos hz'] at hh
        exact dblMap_injOn_half hz hz' (hcap'_inj h1)
      · rcases lt_or_eq_of_le hz with hlt | heq
        · have hEq : cap' (dblMap z) = D.e (Θ₁.symm z') := by
            have hh := h
            rwa [show e' z = cap' (dblMap z) from if_pos hz,
              show e' z' = D.e (Θ₁.symm z') from if_neg hz'] at hh
          have hnd : ‖((dblMap z : Disc) : ℂ)‖ < 1 := by
            rw [dblMap_coe_of_le hz, norm_mul]
            have h2 : ‖(2 : ℂ)‖ = 2 := by
              rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.norm_def,
                Complex.normSq_ofReal, Real.sqrt_mul_self (by norm_num : (0 : ℝ) ≤ 2)]
            rw [h2]
            nlinarith [norm_nonneg ((z : Disc) : ℂ)]
          obtain ⟨θ, hθ⟩ := hcap'_meet (dblMap z) hnd ⟨Θ₁.symm z', hEq.symm⟩
          have hθ' : D.e (z₁ θ) = cap' (dblMap z) := hθ
          have h2 : z₁ θ = Θ₁.symm z' := by
            apply D.inj
            rw [hθ']
            exact hEq
          have h3 : ‖((z' : Disc) : ℂ)‖ = 1 / 2 := by
            have h4 := (hz₁range (Θ₁.symm z')).mp ⟨θ, h2⟩
            rwa [Θ₁.apply_symm_apply] at h4
          exact absurd h3 (by have := not_le.mp hz'; linarith)
        · obtain ⟨σ, rfl⟩ := exists_halfCirclePoint_eq z heq
          have hz1σ : e' (halfCirclePoint σ) = D.e (z₁ (s₁ * σ)) := by
            show (if ‖((halfCirclePoint σ : Disc) : ℂ)‖ ≤ 1 / 2
              then cap' (dblMap (halfCirclePoint σ)) else D.e (Θ₁.symm (halfCirclePoint σ)))
              = D.e (z₁ (s₁ * σ))
            rw [if_pos (le_of_eq (norm_halfCirclePoint σ)), dblMap_halfCirclePoint, hcap'_bd σ]
          have hEq : D.e (z₁ (s₁ * σ)) = D.e (Θ₁.symm z') := by
            have hh := h
            rwa [show e' (halfCirclePoint σ) = D.e (z₁ (s₁ * σ)) from hz1σ,
              show e' z' = D.e (Θ₁.symm z') from if_neg hz'] at hh
          have h2 : z₁ (s₁ * σ) = Θ₁.symm z' := D.inj hEq
          have h4 : Θ₁ (z₁ (s₁ * σ)) = halfCirclePoint σ := hΘ₁z σ
          have h3 : z' = halfCirclePoint σ := by
            calc z' = Θ₁ (Θ₁.symm z') := (Θ₁.apply_symm_apply z').symm
              _ = Θ₁ (z₁ (s₁ * σ)) := by rw [← h2]
              _ = halfCirclePoint σ := h4
          exact h3.symm
    · by_cases hz' : ‖((z' : Disc) : ℂ)‖ ≤ 1 / 2
      · rcases lt_or_eq_of_le hz' with hlt | heq
        · have hEq : D.e (Θ₁.symm z) = cap' (dblMap z') := by
            have hh := h
            rwa [show e' z = D.e (Θ₁.symm z) from if_neg hz,
              show e' z' = cap' (dblMap z') from if_pos hz'] at hh
          have hnd : ‖((dblMap z' : Disc) : ℂ)‖ < 1 := by
            rw [dblMap_coe_of_le hz', norm_mul]
            have h2 : ‖(2 : ℂ)‖ = 2 := by
              rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.norm_def,
                Complex.normSq_ofReal, Real.sqrt_mul_self (by norm_num : (0 : ℝ) ≤ 2)]
            rw [h2]
            nlinarith [norm_nonneg ((z' : Disc) : ℂ)]
          obtain ⟨θ, hθ⟩ := hcap'_meet (dblMap z') hnd ⟨Θ₁.symm z, hEq⟩
          have hθ' : D.e (z₁ θ) = cap' (dblMap z') := hθ
          have h2 : z₁ θ = Θ₁.symm z := by
            apply D.inj
            rw [hθ']
            exact hEq.symm
          have h3 : ‖((z : Disc) : ℂ)‖ = 1 / 2 := by
            have h4 := (hz₁range (Θ₁.symm z)).mp ⟨θ, h2⟩
            rwa [Θ₁.apply_symm_apply] at h4
          exact absurd h3 (by have := not_le.mp hz; linarith)
        · obtain ⟨σ, rfl⟩ := exists_halfCirclePoint_eq z' heq
          have hz1σ : e' (halfCirclePoint σ) = D.e (z₁ (s₁ * σ)) := by
            show (if ‖((halfCirclePoint σ : Disc) : ℂ)‖ ≤ 1 / 2
              then cap' (dblMap (halfCirclePoint σ)) else D.e (Θ₁.symm (halfCirclePoint σ)))
              = D.e (z₁ (s₁ * σ))
            rw [if_pos (le_of_eq (norm_halfCirclePoint σ)), dblMap_halfCirclePoint, hcap'_bd σ]
          have hEq : D.e (Θ₁.symm z) = D.e (z₁ (s₁ * σ)) := by
            have hh := h
            rwa [show e' (halfCirclePoint σ) = D.e (z₁ (s₁ * σ)) from hz1σ,
              show e' z = D.e (Θ₁.symm z) from if_neg hz] at hh
          have h2 : z₁ (s₁ * σ) = Θ₁.symm z := D.inj hEq.symm
          have h4 : Θ₁ (z₁ (s₁ * σ)) = halfCirclePoint σ := hΘ₁z σ
          have h3 : z = halfCirclePoint σ := by
            calc z = Θ₁ (Θ₁.symm z) := (Θ₁.apply_symm_apply z).symm
              _ = Θ₁ (z₁ (s₁ * σ)) := by rw [← h2]
              _ = halfCirclePoint σ := h4
          exact h3
      · have h1 : D.e (Θ₁.symm z) = D.e (Θ₁.symm z') := by
          have hh := h
          rwa [show e' z = D.e (Θ₁.symm z) from if_neg hz,
            show e' z' = D.e (Θ₁.symm z') from if_neg hz'] at hh
        have h2 : Θ₁.symm z = Θ₁.symm z' := D.inj h1
        calc z = Θ₁ (Θ₁.symm z) := (Θ₁.apply_symm_apply z).symm
          _ = Θ₁ (Θ₁.symm z') := by rw [h2]
          _ = z' := Θ₁.apply_symm_apply z'
  -- its boundary curve is `α`
  have he'_bd : ∀ θ : ℝ, e' (Work.Smooth.Jordan.circlePoint θ) = D.α.γ θ := by
    intro θ
    have h1 : Θ₁.symm (Work.Smooth.Jordan.circlePoint θ)
        = Work.Smooth.Jordan.circlePoint θ := by
      simpa [hΘ₁bd θ] using Θ₁.symm_apply_apply (Work.Smooth.Jordan.circlePoint θ)
    show (if ‖((Work.Smooth.Jordan.circlePoint θ : Disc) : ℂ)‖ ≤ 1 / 2
      then cap' (dblMap (Work.Smooth.Jordan.circlePoint θ))
      else D.e (Θ₁.symm (Work.Smooth.Jordan.circlePoint θ))) = D.α.γ θ
    rw [if_neg (by rw [norm_circlePoint]; norm_num), h1]
    exact D.boundary θ
  -- it contains every other intersection curve
  have he'_other : ∀ i : D.ι, i ≠ j → Set.range (D.curves i).γ ⊆ Set.range e' := by
    intro i hij y hy
    obtain ⟨z₀, hz₀⟩ := D.curves_subset i hy
    have hmemK : z₀ ∈ K ⟨i, hij⟩ := by
      show D.e z₀ ∈ Set.range (D.curves i).γ
      rw [hz₀]
      exact hy
    have hnotball : ¬ (‖((Θ z₀ : Disc) : ℂ)‖ ≤ r₀) :=
      Set.disjoint_left.mp (hr₀disj ⟨i, hij⟩) hmemK
    have hgt : r₀ < ‖((Θ z₀ : Disc) : ℂ)‖ := not_le.mp hnotball
    have hz₀_not : ¬ (∃ w : Disc, ‖((w : Disc) : ℂ)‖ < 1 ∧ h₁ w = z₀) := by
      rintro ⟨w, hw, hwz⟩
      have h3 : scaleMap r₀ (le_of_lt hr₀pos) hr₀le w = Θ z₀ := by
        have h4 : Θ (h₁ w) = Θ z₀ := congrArg (fun u : Disc => Θ u) hwz
        have h5 : h₁ w = Θ.symm (scaleMap r₀ (le_of_lt hr₀pos) hr₀le w) := rfl
        rw [h5, Θ.apply_symm_apply] at h4
        exact h4
      have hA : ‖((Θ z₀ : Disc) : ℂ)‖ = r₀ * ‖((w : Disc) : ℂ)‖ := by
        rw [← h3, norm_scaleMap]
      have hle : ‖((Θ z₀ : Disc) : ℂ)‖ ≤ r₀ := by
        rw [hA]
        nlinarith [norm_coe_le_one w]
      linarith
    have hge : 1 / 2 ≤ ‖((Θ₁ z₀ : Disc) : ℂ)‖ :=
      not_lt.mp (fun hlt => by
        obtain ⟨w, hw⟩ := (hΘ₁img z₀).mpr (le_of_lt hlt)
        exact hz₀_not ⟨w, (hΘ₁imglt w).mpr (by rw [hw]; exact hlt), hw⟩)
    have hΘ₁ : 1 / 2 < ‖((Θ₁ z₀ : Disc) : ℂ)‖ := by
      rcases lt_or_eq_of_le hge with hlt | heq
      · exact hlt
      · -- the equality case: `z₀` would be on the boundary curve of `h₁`, i.e. on `γ`
        exfalso
        have hzimg : z₀ ∈ Set.range h₁ :=
          mem_range_of_norm_le_half Θ₁ h₁ hΘ₁img z₀ (le_of_eq heq.symm)
        obtain ⟨w, hw⟩ := hzimg
        have hnotin : ¬ ‖((w : Disc) : ℂ)‖ < 1 := by
          intro hlt'
          have h' : ‖((Θ₁ (h₁ w) : Disc) : ℂ)‖ < 1 / 2 := (hΘ₁imglt w).mp hlt'
          rw [hw, ← heq] at h'
          exact absurd h' (lt_irrefl (1 / 2))
        have hwbd : ‖((w : Disc) : ℂ)‖ = 1 :=
          le_antisymm (norm_coe_le_one w) (not_lt.mp hnotin)
        obtain ⟨τ, hτ⟩ := Work.Smooth.Jordan.exists_circlePoint_eq w hwbd
        have hz₁w : z₀ = z₁ τ := by
          rw [show z₁ τ = h₁ (Work.Smooth.Jordan.circlePoint τ) from (hz₁_spec τ).symm, hτ]
          exact hw.symm
        have hcontra : D.e z₀ ∉ P.carrier := by
          rw [hz₁w]
          exact hz₁_off τ
        have hmem : D.e z₀ ∈ P.carrier := by
          obtain ⟨t, ht⟩ := hmemK
          rw [← ht]
          exact (D.curves i).mem t
        exact hcontra hmem
    refine ⟨Θ₁ z₀, ?_⟩
    show (if ‖((Θ₁ z₀ : Disc) : ℂ)‖ ≤ 1 / 2
      then cap' (dblMap (Θ₁ z₀)) else D.e (Θ₁.symm (Θ₁ z₀))) = y
    rw [if_neg (not_le.mpr hΘ₁), Θ₁.symm_apply_apply]
    exact hz₀
  -- and it meets the surface in the interior only along them
  have he'_cond : ∀ z : Disc, ‖((z : Disc) : ℂ)‖ < 1 → e' z ∈ P.carrier →
      ∃ i : D.ι, i ≠ j ∧ e' z ∈ Set.range (D.curves i).γ := by
    intro z hz hmem
    rcases lt_trichotomy ‖((z : Disc) : ℂ)‖ (1 / 2) with hlt | heq | hgt
    · have hzle : ‖((z : Disc) : ℂ)‖ ≤ 1 / 2 := le_of_lt hlt
      have heq' : e' z = cap' (dblMap z) := by
        show (if ‖((z : Disc) : ℂ)‖ ≤ 1 / 2 then cap' (dblMap z)
          else D.e (Θ₁.symm z)) = _
        rw [if_pos hzle]
      have hnd : ‖((dblMap z : Disc) : ℂ)‖ < 1 := by
        rw [dblMap_coe_of_le hzle, norm_mul]
        have h2 : ‖(2 : ℂ)‖ = 2 := by
          rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.norm_def,
            Complex.normSq_ofReal, Real.sqrt_mul_self (by norm_num : (0 : ℝ) ≤ 2)]
        rw [h2]
        nlinarith [norm_nonneg ((z : Disc) : ℂ)]
      exact absurd (heq' ▸ hmem) (hcap'_off (dblMap z) hnd)
    · obtain ⟨σ, rfl⟩ := exists_halfCirclePoint_eq z heq
      have hz1σ : e' (halfCirclePoint σ) = D.e (z₁ (s₁ * σ)) := by
        show (if ‖((halfCirclePoint σ : Disc) : ℂ)‖ ≤ 1 / 2
          then cap' (dblMap (halfCirclePoint σ)) else D.e (Θ₁.symm (halfCirclePoint σ)))
          = D.e (z₁ (s₁ * σ))
        rw [if_pos (le_of_eq (norm_halfCirclePoint σ)), dblMap_halfCirclePoint, hcap'_bd σ]
      exact absurd (hz1σ ▸ hmem) (hz₁_off (s₁ * σ))
    · have hzle : ¬ (‖((z : Disc) : ℂ)‖ ≤ 1 / 2) := not_le.mpr hgt
      have heq' : e' z = D.e (Θ₁.symm z) := by
        show (if ‖((z : Disc) : ℂ)‖ ≤ 1 / 2 then cap' (dblMap z)
          else D.e (Θ₁.symm z)) = _
        rw [if_neg hzle]
      have hw : ‖((Θ₁.symm z : Disc) : ℂ)‖ < 1 := by
        refine lt_of_le_of_ne (norm_coe_le_one _) ?_
        intro h1
        obtain ⟨τ, hτ⟩ := Work.Smooth.Jordan.exists_circlePoint_eq (Θ₁.symm z) h1
        have h2 : ‖((Θ₁ (Θ₁.symm z) : Disc) : ℂ)‖ = 1 := by
          rw [← hτ, hΘ₁bd τ]
          exact norm_circlePoint τ
        rw [Θ₁.apply_symm_apply] at h2
        rw [h2] at hz
        exact absurd hz (by norm_num)
      obtain ⟨i, hi⟩ := D.covers (Θ₁.symm z) hw (heq' ▸ hmem)
      refine ⟨i, ?_, ?_⟩
      · intro hij
        subst hij
        obtain ⟨t, ht⟩ := hi
        have hwt : Θ₁.symm z = g (Work.Smooth.Jordan.circlePoint t) := by
          apply D.inj
          rw [hg_spec]
          exact ht.symm.trans (hf_bd t).symm
        obtain ⟨u, hu, huu⟩ := hg_in_h₁ (Work.Smooth.Jordan.circlePoint t)
        have hthis : ‖((Θ₁ (g (Work.Smooth.Jordan.circlePoint t)) : Disc) : ℂ)‖ ≤ 1 / 2 :=
          (hΘ₁img (g (Work.Smooth.Jordan.circlePoint t))).mp ⟨u, huu⟩
        rw [← hwt, Θ₁.apply_symm_apply] at hthis
        linarith
      · rwa [heq']
  exact ⟨e', he'_inj, he'_bd, he'_other, he'_cond⟩


/-- **The cut-and-paste at a single torus**: `CutsAlongSubdisc P` from the inputs at that torus —
the annulus form of Schoenflies, the push-off of a surface disc, and Pardon's surgery in the
*pinched* configuration (which covers the configurations in which the position hypothesis
`CurvesInterior` fails). -/
theorem cutsAlongSubdisc_of_props_or_pinched (hA : AnnulusSchoenflies)
    {P : Work.CoreTopology.ParamTorus} (hB : SurfaceDiscPushOff P) (hP : PinchedPushThrough P)
    (hTame : ∀ D : Work.Topology.SphereSlicing.SliceDisc P, LocallyFlat D.e) :
    Work.Topology.Classical.CutsAlongSubdisc P := by
  intro D j f hf_inj hf_bd hf_off hf_sub hf_disj
  classical
  by_cases hpos : Disjoint (Set.range (D.curves j).γ)
      (Set.range fun θ : ℝ => D.e (Work.Smooth.Jordan.circlePoint θ))
  · exact cutsAlongSubdisc_inside hA hB D (hTame D) j f hf_inj hf_bd hf_off hf_sub hf_disj hpos
  · exact hP D j f hf_inj hf_bd hf_off hf_sub hf_disj hpos

/-! ## The cut-and-paste from the named inputs -/

/-- **The cut-and-paste of Pardon's second innermost argument**, from the three named inputs
`AnnulusSchoenflies`, `SurfaceDiscPushOff` and the position hypothesis `CurvesInterior`. -/
theorem cutsAlongSubdisc_of_props (hA : AnnulusSchoenflies)
    (hB : ∀ Q : Work.CoreTopology.ParamTorus, SurfaceDiscPushOff Q)
    (hC : ∀ Q : Work.CoreTopology.ParamTorus, CurvesInterior Q)
    (hTame : ∀ (Q : Work.CoreTopology.ParamTorus)
      (D : Work.Topology.SphereSlicing.SliceDisc Q), LocallyFlat D.e) :
    ∀ P : Work.CoreTopology.ParamTorus, Work.Topology.Classical.CutsAlongSubdisc P := by
  intro P D j f hf_inj hf_bd hf_off hf_sub hf_disj
  exact cutsAlongSubdisc_inside hA (hB P) D (hTame P D) j f hf_inj hf_bd hf_off hf_sub hf_disj
    (hC P D j f hf_inj hf_bd hf_sub)

/-- **The cut-and-paste of Pardon's second innermost argument**, from `AnnulusSchoenflies`,
`SurfaceDiscPushOff` and Pardon's surgery in the pinched configuration `PinchedPushThrough` (which
needs Alexander's theorem and isotopy extension).  No position hypothesis on the slice discs is
needed: the pinched configurations, in which `CurvesInterior` fails, are covered by
`PinchedPushThrough`. -/
theorem cutsAlongSubdisc_of_props_and_pinched (hA : AnnulusSchoenflies)
    (hB : ∀ Q : Work.CoreTopology.ParamTorus, SurfaceDiscPushOff Q)
    (hP : ∀ Q : Work.CoreTopology.ParamTorus, PinchedPushThrough Q)
    (hTame : ∀ (Q : Work.CoreTopology.ParamTorus)
      (D : Work.Topology.SphereSlicing.SliceDisc Q), LocallyFlat D.e) :
    ∀ P : Work.CoreTopology.ParamTorus, Work.Topology.Classical.CutsAlongSubdisc P := by
  intro P
  exact cutsAlongSubdisc_of_props_or_pinched hA (hB P) (hP P) (hTame P)

end

end Work.Smooth.SphereJordan
