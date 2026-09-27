import Mathlib
import Submission.Work.Drive.planeChartDefs
import Submission.Work.Drive.sideCountDefs
import Submission.Work.Drive.coreLoopClosed
import Submission.Work.Drive.stripChartSmooth
import Submission.Work.Drive.cappedPlaneFamily
import Submission.Work.Drive.essential_loop
import Submission.Work.Drive.stripConfigInterface

/-!
# The core loop of a plane chart is injective modulo `1`

The core loop of a plane chart `Q` (`Work.Drive.coreLoop Q t = Q (exp (i π t))`,
`Submission/Work/Drive/sideCountDefs.lean`) is the image in the capping space of the **diameters** of
`γ`: at the parameter `t` the point is the class of the chord joining `i z` to `- i z`, where
`z = exp (i π t)`.

The chart satisfies, on the unit circle `‖z‖ = 1`, the *strip clause*: `Q z` is the configuration
class of the chord whose capping coordinates are

> `unitConf γ z = μ γ (Circle.exp (arg z + π/2), Circle.exp (arg z - π/2))`,

i.e. the chord `{i z, - i z}` written through the square-root lift `Circle.exp` of the argument (the
two `Circle.exp`-parameters differ by `π`, so that the endpoints `i z` and `- i z` are well defined
up to the sign ambiguity of `Circle.exp`).  Since two chords with the same configuration are the same
unordered pair of points of `γ` (`Work.Drive.muOrd_injective_unordered`) and `γ` is injective, the
class `Q z` determines the pair `{i z, - i z}`, hence `z` **up to sign**.

Modulo `±`, the pair `{i z, - i z}` is exactly the diameter at the direction of `z`: with
`z = exp (i π t)` the parametrisation is the essential loop `Work.Drive.coreLoopPt γ (t + 1/2)` of
`Submission/Work/Drive/essential_loop.lean` (`θ ↦ μ γ (corePt θ, - corePt θ)` with
`corePt θ = Circle.exp (π θ)`).  The conclusion follows from the injectivity of `corePt` modulo its
period `2` (`Work.Drive.corePt_eq_iff`).

## Main content

* `Work.Drive.unitConf` — the configuration point of the chord `{i z, - i z}` in the
  `Circle.exp`-square-root lift of the argument of `z`;
* `Work.Drive.planeChart_unit_val` — **the strip clause in configuration form**: for `‖z‖ = 1` the
  chart value `Q z` is the class of `confOf (unitConf γ z)`;
* `Work.Drive.coreLoopPt_half` — `unitConf γ (exp (i π s)) = coreLoopPt γ (s + 1/2)`, the dictionary
  between the chart's parametrisation and the essential loop;
* `Work.Drive.coreLoop_injective_mod_one` — the target: `coreLoop Q s = coreLoop Q s'` forces
  `s' - s ∈ ℤ`.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff Topology
open Classical

noncomputable section

/-! ## Elementary facts about the exponential parametrisation of the unit circle -/

/-- The point of the unit circle at which the core loop sits: `exp (i π t)`. -/
lemma norm_loopPt (t : ℝ) : ‖Complex.exp (Real.pi * (t : ℂ) * Complex.I)‖ = 1 := by
  rw [Complex.norm_exp]
  have h : (Real.pi * (t : ℂ) * Complex.I).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [h, Real.exp_zero]

/-- **The square-root lift of the argument**: `Circle.exp (arg z + π/2)` has the value `i z` on the
unit circle.  This is the choice of a continuous argument of the diameter through `z` used by the
strip clause of the chart. -/
lemma circleExp_arg_add (z : ℂ) (hz : ‖z‖ = 1) :
    ((Circle.exp (z.arg + Real.pi / 2) : Circle) : ℂ) = z * Complex.I := by
  rw [Circle.coe_exp]
  rw [show ((z.arg + Real.pi / 2 : ℝ) : ℂ) * Complex.I
      = (z.arg : ℂ) * Complex.I + (Real.pi : ℂ) / 2 * Complex.I by push_cast; ring]
  rw [Complex.exp_add, Complex.exp_pi_div_two_mul_I]
  have h : Complex.exp ((z.arg : ℂ) * Complex.I) = z := by
    simpa [hz] using Complex.norm_mul_exp_arg_mul_I z
  rw [h]

/-- The two square-root lifts of the argument differ by the antipode: the chord presented by the
strip clause has endpoints `i z` and `- i z`. -/
lemma circleExp_arg_sub_eq_neg (z : ℂ) :
    Circle.exp (z.arg - Real.pi / 2) = -Circle.exp (z.arg + Real.pi / 2) := by
  have h : Circle.exp (z.arg - Real.pi / 2) = Circle.exp (z.arg + Real.pi / 2 + Real.pi) := by
    rw [circle_exp_eq_iff_exists_int]
    refine ⟨-1, ?_⟩
    push_cast
    ring
  rw [h, Circle.exp_add, circle_exp_pi, mul_neg, mul_one]

/-! ## The configuration of the chord `{i z, -i z}` -/

/-- **The configuration point of the diameter at `z`**, in the square-root lift of the argument of
`z`: the chord of `γ` with endpoints `i z` and `- i z`.  This is the configuration datum that the
strip clause of the plane chart assigns to the unit complex number `z`. -/
def unitConf (γ : Circle → ℝ × ℝ) (z : ℂ) : (ℝ × ℝ) × UnitAddCircle × ℝ :=
  Submission.Configuration.muOrd γ
    (Circle.exp (z.arg + Real.pi / 2), Circle.exp (z.arg - Real.pi / 2))

/-- The capping coordinates of the chord with parameters `(a, b)` (the two parameters are read through
`Circle.exp`, so only their classes modulo `2π` matter). -/
lemma stripData_mk2_core (γ : Circle → ℝ × ℝ) (a b : ℝ) :
    stripData γ (mk2 a b)
      = confOf (Submission.Configuration.muOrd γ (Circle.exp a, Circle.exp b)) := by
  simp [stripData, mk2]

/-- **The rotated strip chart as a class of the configuration piece.** -/
lemma stripChart_inl_eq (γ : Circle → ℝ × ℝ) (hγne : ∀ x : Circle, γ x ≠ 0) (v : UnitAddCircle)
    (w : EuclideanSpace ℝ (Fin 2)) :
    stripChart γ hγne v w = Quotient.mk'' (Sum.inl (⟨((stripData γ w).1, (stripData γ w).2.1,
      (stripData γ w).2.2 + v), stripData_pos hγne w,
      confOf_snd_norm_le_one (Submission.Configuration.muOrd γ (Circle.exp (w 0), Circle.exp (w 1)))⟩
        : ConfigPiece) : ConfigPiece ⊕ CapPiece) := by
  unfold stripChart confPiece stripData rotConfig
  rfl

/-! ## The strip clause in configuration form -/

/-- **The plane chart reads the unit circle off the configurations of the diameters.**  For
`‖z‖ = 1` the strip clause of `IsPlaneChart` gives `Q z` as the configuration class of
`unitConf γ z`: the strip clause presents `Q z` as `stripChart γ hγne 0` at the parameters
`arg z ± √(π²(‖z‖ - 1/2)/2)`, and at `‖z‖ = 1` the square root is `π/2`, so the two parameters of the
chord are `arg z + π/2` and `arg z - π/2`. -/
lemma planeChart_unit_val {γ : Circle → ℝ × ℝ} {hγne : ∀ x : Circle, γ x ≠ 0}
    {Q : ℂ → CappingSpace} (hQ : IsPlaneChart γ hγne Q) {z : ℂ} (hz : ‖z‖ = 1) :
    ∃ (h1 : 0 < (confOf (unitConf γ z)).1) (h2 : ‖(confOf (unitConf γ z)).2.1‖ ≤ 1),
      Q z = Quotient.mk'' (Sum.inl (confPiece (unitConf γ z) h1 h2) : ConfigPiece ⊕ CapPiece) := by
  have hz1 : 1 / 2 < ‖z‖ := by rw [hz]; norm_num
  have hz2 : ‖z‖ ≤ 1 := by rw [hz]
  have hsq : Real.sqrt (Real.pi ^ 2 * (‖z‖ - 1 / 2) / 2) = Real.pi / 2 := by
    rw [hz]
    have h : Real.pi ^ 2 * (1 - 1 / 2) / 2 = (Real.pi / 2) ^ 2 := by ring
    rw [h, Real.sqrt_sq (by positivity)]
  have hstrip := hQ.2.1 z hz1 hz2
  rw [hsq] at hstrip
  refine ⟨?_, ?_, ?_⟩
  · rw [unitConf, ← stripData_mk2_core γ (z.arg + Real.pi / 2) (z.arg - Real.pi / 2)]
    exact stripData_pos hγne _
  · rw [unitConf, ← stripData_mk2_core γ (z.arg + Real.pi / 2) (z.arg - Real.pi / 2)]
    exact confOf_snd_norm_le_one _
  · rw [hstrip, stripChart_inl_eq]
    refine congrArg (Quotient.mk'') (congrArg Sum.inl (Subtype.ext ?_))
    show ((stripData γ (mk2 (z.arg + Real.pi / 2) (z.arg - Real.pi / 2))).1,
        (stripData γ (mk2 (z.arg + Real.pi / 2) (z.arg - Real.pi / 2))).2.1,
        (stripData γ (mk2 (z.arg + Real.pi / 2) (z.arg - Real.pi / 2))).2.2 + 0)
      = confOf (unitConf γ z)
    rw [stripData_mk2_core]
    simp only [unitConf, add_zero]

/-! ## The dictionary between the chart's core loop and the essential loop -/

/-- **The configuration of the diameter at `exp (i π s)` is the essential loop at `s + 1/2`.**  Indeed
the square-root lift of the argument of `exp (i π s)` is the angle `π s`, so that the two
`Circle.exp`-parameters of `unitConf` are `π s + π/2 = π (s + 1/2)` and `π s - π/2`; the latter
presents the antipode. -/
lemma coreLoopPt_half (γ : Circle → ℝ × ℝ) (s : ℝ) :
    coreLoopPt γ (s + 1 / 2)
      = unitConf γ (Complex.exp (Real.pi * (s : ℂ) * Complex.I)) := by
  set z : ℂ := Complex.exp (Real.pi * (s : ℂ) * Complex.I) with hzdef
  have hz : ‖z‖ = 1 := by rw [hzdef]; exact norm_loopPt s
  have hc : ((Circle.exp (z.arg + Real.pi / 2) : Circle) : ℂ)
      = ((corePt (s + 1 / 2) : Circle) : ℂ) := by
    rw [circleExp_arg_add z hz, hzdef]
    rw [corePt, Circle.coe_exp]
    rw [show ((Real.pi * (s + 1 / 2) : ℝ) : ℂ) * Complex.I
        = Real.pi * (s : ℂ) * Complex.I + (Real.pi : ℂ) / 2 * Complex.I by push_cast; ring]
    rw [Complex.exp_add, Complex.exp_pi_div_two_mul_I]
  have h1 : Circle.exp (z.arg + Real.pi / 2) = corePt (s + 1 / 2) := Subtype.ext hc
  have h2 : Circle.exp (z.arg - Real.pi / 2) = -corePt (s + 1 / 2) := by
    rw [circleExp_arg_sub_eq_neg z, h1]
  rw [hzdef]
  simp only [coreLoopPt, unitConf]
  rw [← h2, ← h1]

/-! ## The core loop is injective modulo `1` -/

theorem coreLoop_injective_mod_one {γ : Circle → ℝ × ℝ}
    (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ∞ γ) (hγne : ∀ x : Circle, γ x ≠ 0)
    {Q : ℂ → CappingSpace} (hQ : IsPlaneChart γ hγne Q) {s s' : ℝ}
    (h : coreLoop Q s = coreLoop Q s') : ∃ k : ℤ, s' = s + k := by
  set z : ℂ := Complex.exp (Real.pi * (s : ℂ) * Complex.I) with hzdef
  set z' : ℂ := Complex.exp (Real.pi * (s' : ℂ) * Complex.I) with hzdef'
  have hz : ‖z‖ = 1 := by rw [hzdef]; exact norm_loopPt s
  have hz' : ‖z'‖ = 1 := by rw [hzdef']; exact norm_loopPt s'
  have hQz : Q z = Q z' := h
  obtain ⟨h1, h2, hv⟩ := planeChart_unit_val hQ hz
  obtain ⟨h1', h2', hv'⟩ := planeChart_unit_val hQ hz'
  -- the two configuration pieces are equal, hence so are the configurations
  have hmk : (Quotient.mk'' (Sum.inl (confPiece (unitConf γ z) h1 h2)) : CappingSpace)
      = Quotient.mk'' (Sum.inl (confPiece (unitConf γ z') h1' h2')) := by
    rw [← hv, ← hv']
    exact hQz
  have hcfg : unitConf γ z = unitConf γ z' :=
    confOf_injective_of_nonneg (Submission.Geometry.eucNorm_nonneg _)
      (Submission.Geometry.eucNorm_nonneg _)
      (by simpa using congrArg Subtype.val (mk_inl_inj.mp hmk))
  -- rewrite both sides as the essential loop
  have e1 : unitConf γ z = coreLoopPt γ (s + 1 / 2) := by
    rw [hzdef]; exact (coreLoopPt_half γ s).symm
  have e2 : unitConf γ z' = coreLoopPt γ (s' + 1 / 2) := by
    rw [hzdef']; exact (coreLoopPt_half γ s').symm
  have hcl : coreLoopPt γ (s + 1 / 2) = coreLoopPt γ (s' + 1 / 2) := by
    rw [← e1, hcfg, e2]
  simp only [coreLoopPt] at hcl
  -- the configurations determine the diameter up to sign, and `corePt` is injective modulo `2`
  rcases muOrd_injective_unordered hγ hcl with ⟨hA, _⟩ | ⟨hA, _⟩
  · rw [corePt_eq_iff] at hA
    obtain ⟨n, hn⟩ := hA
    refine ⟨-2 * n, ?_⟩
    push_cast
    linarith
  · rw [← corePt_add_one (s' + 1 / 2)] at hA
    rw [corePt_eq_iff] at hA
    obtain ⟨n, hn⟩ := hA
    refine ⟨-1 - 2 * n, ?_⟩
    push_cast
    linarith

end

end Work.Drive
