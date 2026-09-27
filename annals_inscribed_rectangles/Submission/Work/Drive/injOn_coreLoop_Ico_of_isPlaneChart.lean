import Mathlib
import Submission.Work.Drive.planeChartDefs
import Submission.Work.Drive.sideCountDefs
import Submission.Work.Drive.cappedPlaneFamily
import Submission.Work.Drive.essential_loop
import Submission.Work.Drive.core_loop
import Submission.Work.Drive.stripChartSmooth
import Submission.Work.Drive.coreLoopClosed

namespace Work.Drive

open Submission.Configuration

/-!
# The core loop of a plane chart is a simple closed curve

`Work.Drive.coreLoop Q t = Q (Circle.exp (π t))` restricted to the boundary circle of the chart is the
loop of *diameters* of `γ`: by the strip clause of `IsPlaneChart`, the value `Q z` at `‖z‖ = 1` is the
configuration point of the chord `{γ (arg z + π/2), γ (arg z - π/2)}` of `γ`, and for
`z = Circle.exp (π t)` this is the chord with endpoint parameters `π t ± π/2`, i.e. a *diameter* of the
curve.  Its configuration data is `Work.Drive.coreMu γ t = muOrd γ (exp (πt + π/2), exp (πt - π/2))`,
which is the diametral configuration `Work.Drive.coreLoopPt γ (t + 1/2)`.

The main statement `Work.Drive.injOn_coreLoop_Ico_of_isPlaneChart` (below) says that this loop is
injective on `[0,1)`: the pair `{exp (πt + π/2), exp (πt - π/2)}` (an unordered pair of points of the
circle, since the two endpoints of a chord may be exchanged) determines `t ∈ [0,1)`.  The two
computational bricks are

* the strip clause, evaluated at `Circle.exp (π t)` and rewritten into the configuration data
  (`Work.Drive.coreLoop_eq_mk_confOf`);
* the injectivity of the configuration map on unordered pairs of `γ`
  (`Work.Drive.muOrd_injective_unordered`), which turns the equality of the two configuration points
  into a *sign* ambiguity — the two endpoint parameters of the diameter either match or are exchanged —
  and both alternatives are then excluded by the injectivity of `Circle.exp` on an interval of length
  `2π` containing all four parameters.

The `+ 1` (i.e. `exp (π t - π/2) = - exp (π t + π/2)`) is the integral part of the argument: the
parameter `t + 1` describes the same diameter with its two endpoints exchanged, so *no* statement with
domain `Icc 0 1` can hold (`coreLoop Q 0 = coreLoop Q 1`, `Work.Drive.coreLoop_zero_eq_one`); `Ico` is
the correct domain.
-/

noncomputable section

/-- **The strip parameter of the seam chord at the loop parameter `t`.**  This is
`mk2 (arg z + π/2) (arg z - π/2)` for `z = Circle.exp (π t)`, i.e. the pair of parameters of the
diameter of `γ` through the curve point at parameter `π t`. -/
def coreParam (t : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  mk2 (Complex.arg (((Circle.exp (Real.pi * t) : Circle) : ℂ)) + Real.pi / 2)
      (Complex.arg (((Circle.exp (Real.pi * t) : Circle) : ℂ)) - Real.pi / 2)

@[simp] lemma coreParam_zero (t : ℝ) :
    coreParam t 0 = Complex.arg (((Circle.exp (Real.pi * t) : Circle) : ℂ)) + Real.pi / 2 := rfl

@[simp] lemma coreParam_one (t : ℝ) :
    coreParam t 1 = Complex.arg (((Circle.exp (Real.pi * t) : Circle) : ℂ)) - Real.pi / 2 := rfl

/-- **The configuration point of the diameter at the loop parameter `t`**: the unordered pair
`{γ (Circle.exp (πt + π/2)), γ (Circle.exp (πt - π/2))}` in configuration coordinates.  It is
`Work.Drive.coreLoopPt γ (t + 1/2)` (the two endpoints of the diameter are exchanged when `t` is shifted
by `1`). -/
def coreMu (γ : Circle → ℝ × ℝ) (t : ℝ) : (ℝ × ℝ) × UnitAddCircle × ℝ :=
  muOrd γ (Circle.exp (Real.pi * t + Real.pi / 2), Circle.exp (Real.pi * t - Real.pi / 2))

/-- The length coordinate of a diametral configuration is non-negative (it is a Euclidean norm). -/
lemma coreMu_len_nonneg (γ : Circle → ℝ × ℝ) (t : ℝ) : 0 ≤ (coreMu γ t).2.2 := by
  simp only [coreMu, muOrd]
  exact Submission.Geometry.eucNorm_nonneg _

/-- **`coreLoop Q t` is `Q` at the circle point `Circle.exp (π t)`.** -/
lemma coreLoop_eq_circleExp (Q : ℂ → CappingSpace) (t : ℝ) :
    coreLoop Q t = Q (((Circle.exp (Real.pi * t) : Circle) : ℂ)) := by
  rw [coreLoop, Circle.coe_exp]
  congr 1
  push_cast
  ring

/-- The first strip parameter of the seam at `t` has the same `Circle.exp` as `π t + π/2`. -/
lemma circleExp_coreParam_zero (t : ℝ) :
    Circle.exp (coreParam t 0) = Circle.exp (Real.pi * t + Real.pi / 2) := by
  rw [coreParam_zero, Circle.exp_add, Circle.exp_add, Circle.exp_arg]

/-- The second strip parameter of the seam at `t` has the same `Circle.exp` as `π t - π/2`. -/
lemma circleExp_coreParam_one (t : ℝ) :
    Circle.exp (coreParam t 1) = Circle.exp (Real.pi * t - Real.pi / 2) := by
  rw [coreParam_one, Circle.exp_sub, Circle.exp_sub, Circle.exp_arg]

/-- **The capping data of the seam chord is the diametral configuration** `coreMu γ t`. -/
lemma stripData_coreParam {γ : Circle → ℝ × ℝ} (t : ℝ) :
    stripData γ (coreParam t) = confOf (coreMu γ t) := by
  show confOf (muOrd γ (Circle.exp (coreParam t 0), Circle.exp (coreParam t 1))) = confOf (coreMu γ t)
  rw [circleExp_coreParam_zero t, circleExp_coreParam_one t]
  rfl

/-- **The strip chart at rotation zero, in configuration coordinates.**  This is the unfolding of
`stripChart` (with `rotConfig 0` removed), in the form used below. -/
lemma stripChart_zero_eq_mk {γ : Circle → ℝ × ℝ} (hγne : ∀ x : Circle, γ x ≠ 0)
    (w : EuclideanSpace ℝ (Fin 2)) :
    stripChart γ hγne 0 w = Quotient.mk'' (Sum.inl (⟨((stripData γ w).1, (stripData γ w).2.1,
      (stripData γ w).2.2), stripData_pos hγne w, confOf_snd_norm_le_one _⟩ :
        ConfigPiece) : ConfigPiece ⊕ CapPiece) := by
  simp only [stripChart, rotConfig, confPiece, stripData, add_zero]

/-- The capping radius of a diametral configuration is positive: a diameter is a non-degenerate chord
(this is `stripData_pos` transported along `stripData_coreParam`). -/
lemma coreMu_pos {γ : Circle → ℝ × ℝ} (hγne : ∀ x : Circle, γ x ≠ 0) (t : ℝ) :
    0 < (confOf (coreMu γ t)).1 := by
  rw [← stripData_coreParam (γ := γ) t]
  exact stripData_pos hγne (coreParam t)

/-- **The point of the chart's core loop at the parameter `t`, in configuration coordinates.**  The
strip clause of `IsPlaneChart` evaluated at `Circle.exp (π t)` gives the configuration point
`coreMu γ t = muOrd γ (exp (πt + π/2), exp (πt - π/2))` of the diameter of `γ` at direction `π t`. -/
lemma coreLoop_eq_mk_confOf {γ : Circle → ℝ × ℝ} (hγne : ∀ x : Circle, γ x ≠ 0)
    {Q : ℂ → CappingSpace} (hQ : IsPlaneChart γ hγne Q) (t : ℝ) :
    coreLoop Q t = Quotient.mk'' (Sum.inl (confPiece (coreMu γ t) (coreMu_pos hγne t)
      (confOf_snd_norm_le_one (coreMu γ t)) : ConfigPiece) : ConfigPiece ⊕ CapPiece) := by
  have hz1 : ‖(((Circle.exp (Real.pi * t) : Circle) : ℂ))‖ = 1 := Circle.norm_coe _
  have hlt : 1 / 2 < ‖(((Circle.exp (Real.pi * t) : Circle) : ℂ))‖ := by rw [hz1]; norm_num
  have hle : ‖(((Circle.exp (Real.pi * t) : Circle) : ℂ))‖ ≤ 1 := le_of_eq hz1
  -- the square-root of the strip clause is `π/2` on the boundary circle
  have hsqrt : Real.sqrt (Real.pi ^ 2 * (‖(((Circle.exp (Real.pi * t) : Circle) : ℂ))‖ - 1 / 2) / 2)
      = Real.pi / 2 := by
    have h1 : Real.pi ^ 2 * (‖(((Circle.exp (Real.pi * t) : Circle) : ℂ))‖ - 1 / 2) / 2
        = (Real.pi / 2) ^ 2 := by rw [hz1]; ring
    rw [h1, Real.sqrt_sq (by positivity)]
  rw [coreLoop_eq_circleExp, hQ.2.1 _ hlt hle, hsqrt]
  show stripChart γ hγne 0 (coreParam t) = _
  rw [stripChart_zero_eq_mk]
  apply congrArg Quotient.mk''
  rw [Sum.inl.injEq]
  refine Subtype.ext ?_
  change ((stripData γ (coreParam t)).1, (stripData γ (coreParam t)).2.1,
    (stripData γ (coreParam t)).2.2) = confOf (coreMu γ t)
  rw [stripData_coreParam t]

/-- **The core loop of a plane chart is a simple closed curve.**

`coreLoop Q t = Q (coreLoopArg t)` is the loop of *diameters* of the curve `γ`: at `‖z‖ = 1` the strip
clause of `IsPlaneChart` reads `Q z = stripChart γ hγne 0 (mk2 (arg z + π/2) (arg z - π/2))`, i.e. `Q z`
is the configuration point of the chord `{γ (arg z + π/2), γ (arg z - π/2)}`; for `z = coreLoopArg t`
(`arg z = π t`) this is the diameter whose two endpoint parameters are `π t ± π/2`, and the *unordered*
pair of those parameters is determined by `t mod 1` (the parameter `t + 1` gives the same chord with its
two endpoints exchanged).  So the core loop is injective on `[0,1)` — the "core" of the configuration
Möbius band, parametrised once.

This is the injectivity input of `Work.Drive.odd_coreSideCountPt_reference` (via
`Work.Drive.injOn_classMeetParams_of_injOn_Ico`): the reference factor `(F1)` of `hn2` counts the
parameters at which the loop's class meets the reference plane, and that count is a count of
*parameters* only if the loop is injective there (`coreLoop Q 1 = coreLoop Q 0` by the seam clause, so
`Icc` would be false — `Ico` is the right domain).

**Proof note.**  The stronger statement `∀ s s', coreLoop Q s = coreLoop Q s' → ∃ k : ℤ, s' = s + k` is
*stated* (with a `sorry`) at `Submission/Work/Drive/coreLoop_injective_mod_one.lean`; do **not** import
that file (its `sorry` would taint this proof).  Prove the stronger form directly here (it implies this
lemma), or prove this one directly.  The bricks are all proved: `stripChart_eq_mk` / `mk_inl_inj`
(`cappedPlaneFamily.lean`), `confOf` injectivity on non-negative radii, `muOrd_injective_unordered` and
`muOrd_comm` (`core_loop.lean`), `stripPt_eq_iff`-style injectivity of the strip parametrisation
(`cappedPlaneCharts.lean`), and the elementary `Circle.exp`-kernel fact
(`essential_loop.lean`'s `circle_exp_eq_iff_exists_int`). -/
theorem injOn_coreLoop_Ico_of_isPlaneChart {γ : Circle → ℝ × ℝ}
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (hγne : ∀ x : Circle, γ x ≠ 0)
    {Q : ℂ → Work.Drive.CappingSpace} (hQ : Work.Drive.IsPlaneChart γ hγne Q) :
    Set.InjOn (Work.Drive.coreLoop Q) (Set.Ico (0 : ℝ) 1) := by
  intro s hs s' hs' h
  -- the two chart values are the configuration points of the two diameters
  have hconf : confOf (coreMu γ s) = confOf (coreMu γ s') := by
    have hcls : (Quotient.mk'' (Sum.inl (confPiece (coreMu γ s) (coreMu_pos hγne s)
        (confOf_snd_norm_le_one (coreMu γ s)) : ConfigPiece) : ConfigPiece ⊕ CapPiece)) =
        (Quotient.mk'' (Sum.inl (confPiece (coreMu γ s') (coreMu_pos hγne s')
        (confOf_snd_norm_le_one (coreMu γ s')) : ConfigPiece) : ConfigPiece ⊕ CapPiece)) :=
      (coreLoop_eq_mk_confOf hγne hQ s).symm.trans (h.trans (coreLoop_eq_mk_confOf hγne hQ s'))
    have := mk_inl_inj.mp hcls
    simpa [confPiece] using congrArg Subtype.val this
  -- equal configurations with non-negative lengths: equal unordered pairs of curve points
  have hmu : coreMu γ s = coreMu γ s' :=
    confOf_injective_of_nonneg (coreMu_len_nonneg γ s) (coreMu_len_nonneg γ s') hconf
  have hx := muOrd_injective_unordered hγ hmu
  -- all four parameters lie in the interval `(-π/2, 3π/2)` of length `2π`, where `Circle.exp` is injective
  have hbound : ∀ t : ℝ, t ∈ Set.Ico (0 : ℝ) 1 → Real.pi * t ∈ Set.Ico (0 : ℝ) Real.pi := by
    intro t ht
    exact ⟨mul_nonneg Real.pi_pos.le ht.1, by nlinarith [ht.2, Real.pi_pos]⟩
  have hmem : ∀ t : ℝ, t ∈ Set.Ico (0 : ℝ) 1 →
      Real.pi * t + Real.pi / 2 ∈ Set.Ico (-(Real.pi / 2)) (3 * Real.pi / 2) := by
    intro t ht
    obtain ⟨h1, h2⟩ := hbound t ht
    exact ⟨by linarith, by linarith⟩
  have hmem' : ∀ t : ℝ, t ∈ Set.Ico (0 : ℝ) 1 →
      Real.pi * t - Real.pi / 2 ∈ Set.Ico (-(Real.pi / 2)) (3 * Real.pi / 2) := by
    intro t ht
    obtain ⟨h1, h2⟩ := hbound t ht
    exact ⟨by linarith, by linarith⟩
  have hinj := Circle.exp_injOn_Ico (a := -(Real.pi / 2)) (b := 3 * Real.pi / 2)
    (by linarith [Real.pi_pos])
  rcases hx with ⟨hx, -⟩ | ⟨hx, -⟩
  · -- the two diameters are described by the same endpoint parameters
    have heq := hinj (hmem s hs) (hmem s' hs') hx
    have h2 : Real.pi * s = Real.pi * s' := by linarith
    exact mul_left_cancel₀ Real.pi_ne_zero h2
  · -- the endpoint parameters are exchanged: `π s + π/2 = π s' - π/2`, i.e. `s = s' - 1`
    have heq := hinj (hmem s hs) (hmem' s' hs') hx
    have h2 : Real.pi * (s - s') = -Real.pi := by linarith
    have h3 : s - s' = -1 := by
      have := mul_left_cancel₀ Real.pi_ne_zero (show Real.pi * (s - s') = Real.pi * (-1) by
        rw [h2]; ring)
      exact this
    linarith [hs.1, hs'.2, h3]

end

end Work.Drive
