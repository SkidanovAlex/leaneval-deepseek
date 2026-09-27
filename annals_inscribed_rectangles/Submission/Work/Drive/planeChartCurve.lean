import Mathlib
import Submission.Work.Drive.cappingMid
import Submission.Work.Drive.planeChartDefs
import Submission.Work.Drive.stripChartSmooth

/-!
# A plane chart determines its curve

`Work.Drive.IsPlaneChart γ hγne Q` forces the value of the chart `Q` on the outer annulus
`1/2 < ‖z‖ ≤ 1` to be the configuration point of the chord with parameters `(arg z ± s (‖z‖))`.  This
file shows that this clause makes the *curve* `γ` accessible from the *chart* `Q` alone:

* the **midpoint** of the chord that `Q z` encodes is `cappingMid (Q z)`
  (`Submission/Work/Drive/cappingMid.lean`), hence a continuous function of `z`, because `Q` is;
* for a *fixed* angle `a` the midpoint of the chord `(a, b)` determines `γ` at `b`
  (`midC_sub`: `(γ a + γ b)/2 - (γ a + γ c)/2 = (γ b - γ c)/2`), and the pairs `(a, b)` with
  `0 < a - b ≤ π` are exactly the pairs reachable by the annulus;
* consequently **`γ` is continuous** (`continuous_curve_of_isPlaneChart`).

So the hypothesis `IsSmoothEmbedding γ` of the workspace's seam/essentiality chapter
(`seamEssentiality.lean`) is *not* an independent input of the design: a plane chart of `γ` already
forces the curve to be regular.
-/

namespace Work.Drive

open scoped Topology Manifold ContDiff

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted

noncomputable section

/-! ## 1. The complex coordinates of the plane, and the chord midpoint -/

/-- The complex coordinate of a point of the plane (`(x, y) ↦ x + i y`). -/
def toCplx (p : ℝ × ℝ) : ℂ := ⟨p.1, p.2⟩

@[simp] lemma toCplx_re (p : ℝ × ℝ) : (toCplx p).re = p.1 := rfl

@[simp] lemma toCplx_im (p : ℝ × ℝ) : (toCplx p).im = p.2 := rfl

lemma toCplx_injective : Function.Injective toCplx := by
  intro p q h
  exact Prod.ext (by simpa using congrArg Complex.re h) (by simpa using congrArg Complex.im h)

lemma toCplx_add (p q : ℝ × ℝ) : toCplx (p + q) = toCplx p + toCplx q := by
  apply Complex.ext <;> simp [toCplx]

lemma toCplx_sub (p q : ℝ × ℝ) : toCplx (p - q) = toCplx p - toCplx q := by
  apply Complex.ext <;> simp [toCplx]

lemma toCplx_smul (t : ℝ) (p : ℝ × ℝ) : toCplx (t • p) = (t : ℂ) * toCplx p := by
  apply Complex.ext <;> simp [toCplx]

lemma toCplx_div_two (p : ℝ × ℝ) : toCplx (p / 2) = toCplx p / 2 := by
  apply Complex.ext <;> simp [toCplx] <;> ring

lemma continuous_toCplx : Continuous toCplx := by
  rw [show toCplx = fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I from by
    funext p
    exact Work.Drive.complex_mk_eq_add_mul_I p.1 p.2]
  exact (Complex.continuous_ofReal.comp continuous_fst).add
    ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)

/-- The midpoint of the chord `(γ a, γ b)` as a complex number. -/
def midC (γ : Circle → ℝ × ℝ) (a b : ℝ) : ℂ :=
  toCplx ((γ (Circle.exp a) + γ (Circle.exp b)) / 2)

/-- **The midpoint identity**: for three angles the second difference of the midpoints is half the
difference of the endpoint values.  With a fixed angle `a` this *determines* `γ`. -/
lemma midC_sub (γ : Circle → ℝ × ℝ) (a b c : ℝ) :
    midC γ a b - midC γ a c = (toCplx (γ (Circle.exp b)) - toCplx (γ (Circle.exp c))) / 2 := by
  rw [midC, midC, toCplx_div_two, toCplx_div_two, toCplx_add, toCplx_add]
  ring

/-- `γ` at the angle `b`, read through the midpoints with the two fixed angles `a`, `c`. -/
lemma toCplx_exp_eq (γ : Circle → ℝ × ℝ) (a b c : ℝ) :
    toCplx (γ (Circle.exp b))
      = 2 * (midC γ a b - midC γ a c) + toCplx (γ (Circle.exp c)) := by
  rw [midC_sub]
  ring

/-! ## 2. The strip point of a pair of angles -/

/-- The radius at which the annulus meets the chords of angular length `a - b`. -/
def chartStripRad (a b : ℝ) : ℝ := 1 / 2 + (a - b) ^ 2 / (2 * Real.pi ^ 2)

/-- **The strip point of a pair of angles**: the point of the annulus whose strip parameter is the
pair `(a, b)`, i.e. with `arg z = (a+b)/2` and `‖z‖ = chartStripRad a b`, so that the two parameters of the
strip clause are `arg z ± s (‖z‖) = a`, `b`. -/
def chartStripPt (a b : ℝ) : ℂ :=
  ((chartStripRad a b : ℝ) : ℂ) * Complex.exp ((((a + b) / 2 : ℝ) : ℂ) * Complex.I)

lemma stripRad_pos (a b : ℝ) : 0 < chartStripRad a b := by
  have h : (0 : ℝ) ≤ (a - b) ^ 2 / (2 * Real.pi ^ 2) := by positivity
  simp only [chartStripRad]
  linarith

lemma stripRad_half_le (a b : ℝ) : 1 / 2 ≤ chartStripRad a b := by
  have h : (0 : ℝ) ≤ (a - b) ^ 2 / (2 * Real.pi ^ 2) := by positivity
  simp only [chartStripRad]
  linarith

lemma stripRad_half_lt {a b : ℝ} (h : a ≠ b) : 1 / 2 < chartStripRad a b := by
  have h2 : (0 : ℝ) < (a - b) ^ 2 / (2 * Real.pi ^ 2) := by
    have : (0 : ℝ) < (a - b) ^ 2 := by positivity
    positivity
  simp only [chartStripRad]
  linarith

lemma stripRad_le_one {a b : ℝ} (h : |a - b| ≤ Real.pi) : chartStripRad a b ≤ 1 := by
  have h2 : (a - b) ^ 2 ≤ Real.pi ^ 2 := by
    have := abs_le.mp h
    nlinarith [this.1, this.2, Real.pi_pos]
  have h3 : (a - b) ^ 2 / (2 * Real.pi ^ 2) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  simp only [chartStripRad]
  linarith

lemma stripRad_eq (a b : ℝ) : chartStripRad a b - 1 / 2 = (a - b) ^ 2 / (2 * Real.pi ^ 2) := by
  simp only [chartStripRad]
  ring

lemma norm_stripPt (a b : ℝ) : ‖chartStripPt a b‖ = chartStripRad a b := by
  have h1 : ‖Complex.exp ((((a + b) / 2 : ℝ) : ℂ) * Complex.I)‖ = 1 := by
    rw [Complex.norm_exp]
    have : ((((a + b) / 2 : ℝ) : ℂ) * Complex.I).re = 0 := by simp
    rw [this, Real.exp_zero]
  rw [chartStripPt, norm_mul, h1, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (stripRad_pos a b)]

/-- **The square root of the radial parameter is half the angular length.** -/
lemma sqrt_stripRad {a b : ℝ} (h : 0 ≤ a - b) :
    Real.sqrt (Real.pi ^ 2 * (chartStripRad a b - 1 / 2) / 2) = (a - b) / 2 := by
  have hsq : Real.pi ^ 2 * (chartStripRad a b - 1 / 2) / 2 = ((a - b) / 2) ^ 2 := by
    rw [stripRad_eq]
    field_simp
  rw [hsq]
  exact Real.sqrt_sq (show (0 : ℝ) ≤ (a - b) / 2 by linarith)

/-- **The argument of the strip point**, in the `toIocMod` normal form. -/
lemma arg_stripPt (a b : ℝ) :
    Complex.arg (chartStripPt a b) = toIocMod Real.two_pi_pos (-Real.pi) ((a + b) / 2) := by
  rw [chartStripPt, Complex.arg_real_mul _ (stripRad_pos a b), Complex.arg_exp_mul_I]

/-- `2π`-periodicity of `Circle.exp` in the `zsmul` form. -/
lemma circle_exp_add_zsmul_two_pi (u : ℝ) (k : ℤ) :
    Circle.exp (u + k • (2 * Real.pi)) = Circle.exp u := by
  rw [Circle.exp_add, Circle.exp_zsmul, Circle.exp_two_pi, one_zpow, mul_one]

/-- **The exponential of the strip parameter is the exponential of the chord endpoint.**  This is the
`mod 2π` bookkeeping that lets the strip clause — stated at `arg z ± s (‖z‖)` — be read at the pair
`(a, b)`. -/
lemma circle_exp_arg_stripPt (a b s : ℝ) :
    Circle.exp (Complex.arg (chartStripPt a b) + s) = Circle.exp ((a + b) / 2 + s) := by
  rw [arg_stripPt]
  obtain ⟨-, k, hk⟩ := (toIocMod_eq_iff Real.two_pi_pos (a := -Real.pi) (b := (a + b) / 2)
    (c := toIocMod Real.two_pi_pos (-Real.pi) ((a + b) / 2))).mp rfl
  conv_rhs => rw [hk]
  rw [show toIocMod Real.two_pi_pos (-Real.pi) ((a + b) / 2) + k • (2 * Real.pi) + s
      = (toIocMod Real.two_pi_pos (-Real.pi) ((a + b) / 2) + s) + k • (2 * Real.pi) by abel,
    circle_exp_add_zsmul_two_pi]

/-- The subtractions form of `circle_exp_arg_stripPt`. -/
lemma circle_exp_arg_sub_stripPt (a b s : ℝ) :
    Circle.exp (Complex.arg (chartStripPt a b) - s) = Circle.exp ((a + b) / 2 - s) := by
  rw [sub_eq_add_neg, circle_exp_arg_stripPt, sub_eq_add_neg]

/-! ## 3. The strip clause read at the strip point -/

/-- The midpoint coordinate of the strip chart is the midpoint of the chord. -/
lemma cappingMid_stripChart (γ : Circle → ℝ × ℝ) (hγne : ∀ x : Circle, γ x ≠ 0)
    (v : UnitAddCircle) (w : EuclideanSpace ℝ (Fin 2)) :
    cappingMid (stripChart γ hγne v w)
      = toCplx ((γ (Circle.exp (w 0)) + γ (Circle.exp (w 1))) / 2) := by
  have hR : (stripR γ w : ℂ) ≠ 0 := by
    have hpos : 0 < (stripData γ w).1 := stripData_pos hγne w
    rw [stripData_fst] at hpos
    exact_mod_cast ne_of_gt hpos
  have h1 : cappingMid (stripChart γ hγne v w) = (stripData γ w).1 * (stripData γ w).2.1 := rfl
  rw [h1, stripData_fst, stripData_snd]
  rw [stripD, mul_comm, div_mul_cancel₀ _ hR]
  rw [stripMid]
  apply Complex.ext <;> simp [toCplx]


/-! ## 4. The strip clause read at the strip point -/

lemma continuous_stripPt (a : ℝ) : Continuous (fun b : ℝ => chartStripPt a b) := by
  unfold chartStripPt chartStripRad
  fun_prop

lemma sqrt_stripPt {a b : ℝ} (hab : 0 < a - b) :
    Real.sqrt (Real.pi ^ 2 * (‖chartStripPt a b‖ - 1 / 2) / 2) = (a - b) / 2 := by
  rw [norm_stripPt]
  exact sqrt_stripRad (le_of_lt hab)

/-- **The strip clause at the strip point.**  The chart sends `chartStripPt a b` — the point of the annulus
whose strip parameters are the chord `(a, b)` — to a configuration point whose midpoint coordinate is
the midpoint of that chord. -/
lemma cappingMid_chart_stripPt {γ : Circle → ℝ × ℝ} {hγne : ∀ x : Circle, γ x ≠ 0}
    {Q : ℂ → CappingSpace} (hQ : IsPlaneChart γ hγne Q) {a b : ℝ}
    (hab : 0 < a - b) (h2 : a - b ≤ Real.pi) :
    cappingMid (Q (chartStripPt a b)) = midC γ a b := by
  have hlt : 1 / 2 < ‖chartStripPt a b‖ := by
    rw [norm_stripPt]
    exact stripRad_half_lt (by linarith)
  have hle : ‖chartStripPt a b‖ ≤ 1 := by
    rw [norm_stripPt]
    exact stripRad_le_one (by rw [abs_of_nonneg (le_of_lt hab)]; exact h2)
  have hsval := sqrt_stripPt (a := a) (b := b) hab
  have hea : Circle.exp (Complex.arg (chartStripPt a b)
      + Real.sqrt (Real.pi ^ 2 * (‖chartStripPt a b‖ - 1 / 2) / 2)) = Circle.exp a := by
    rw [hsval]
    have h := circle_exp_arg_stripPt a b ((a - b) / 2)
    rw [show (a + b) / 2 + (a - b) / 2 = a by ring] at h
    exact h
  have heb : Circle.exp (Complex.arg (chartStripPt a b)
      - Real.sqrt (Real.pi ^ 2 * (‖chartStripPt a b‖ - 1 / 2) / 2)) = Circle.exp b := by
    rw [hsval]
    have h := circle_exp_arg_sub_stripPt a b ((a - b) / 2)
    rw [show (a + b) / 2 - (a - b) / 2 = b by ring] at h
    exact h
  have hQz := hQ.2.1 (chartStripPt a b) hlt hle
  rw [hQz, cappingMid_stripChart]
  rw [mk2_apply_zero, mk2_apply_one]
  rw [hea, heb]
  rfl

/-! ## 5. Continuity of the curve -/

/-- **The midpoint is continuous in the second angle**, on the region `0 < a - b < π` — the region
covered by the annulus clause. -/
lemma continuousAt_midC {γ : Circle → ℝ × ℝ} {hγne : ∀ x : Circle, γ x ≠ 0}
    {Q : ℂ → CappingSpace} (hQc : Continuous Q) (hQ : IsPlaneChart γ hγne Q) {a b : ℝ}
    (hab : b < a) (h2 : a - b < Real.pi) :
    ContinuousAt (fun b' : ℝ => midC γ a b') b := by
  have hcont : Continuous (fun b' : ℝ => cappingMid (Q (chartStripPt a b'))) :=
    continuous_cappingMid.comp (hQc.comp (continuous_stripPt a))
  refine ContinuousAt.congr_of_eventuallyEq hcont.continuousAt ?_
  filter_upwards [isOpen_Ioo.mem_nhds (show b ∈ Set.Ioo (a - Real.pi) a from ⟨by linarith, hab⟩)]
    with b' hb'
  exact (cappingMid_chart_stripPt hQ (by linarith [hb'.2]) (le_of_lt (by linarith [hb'.1]))).symm

/-- The inverse of the complex coordinate, as a continuous map. -/
def ofCplx (z : ℂ) : ℝ × ℝ := (z.re, z.im)

@[simp] lemma ofCplx_toCplx (p : ℝ × ℝ) : ofCplx (toCplx p) = p := by
  simp [ofCplx, toCplx]

lemma continuous_ofCplx : Continuous ofCplx :=
  (Complex.continuous_re.prodMk Complex.continuous_im)

/-- **A plane chart determines its curve: `γ` is continuous.**  The midpoint coordinate of the chart
gives the midpoints of all chords with a fixed endpoint; the second difference of two such midpoints is
half the difference of the endpoints, which pins down `γ` locally. -/
theorem continuous_curve_of_isPlaneChart {γ : Circle → ℝ × ℝ} {hγne : ∀ x : Circle, γ x ≠ 0}
    {Q : ℂ → CappingSpace} (hQ : IsPlaneChart γ hγne Q) : Continuous γ := by
  have hQc : Continuous Q := hQ.1.continuous
  have hmain : Continuous (fun b : ℝ => toCplx (γ (Circle.exp b))) := by
    rw [continuous_iff_continuousAt]
    intro b₀
    have h1 : ContinuousAt (fun b : ℝ => midC γ (b₀ + Real.pi / 2) b) b₀ :=
      continuousAt_midC hQc hQ (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    have h2 : ContinuousAt (fun b : ℝ => midC γ (b₀ + Real.pi / 2) (b₀ + Real.pi / 4)) b₀ :=
      continuousAt_const
    have h3 : ContinuousAt (fun _ : ℝ => toCplx (γ (Circle.exp (b₀ + Real.pi / 4)))) b₀ :=
      continuousAt_const
    have hform : (fun b : ℝ => toCplx (γ (Circle.exp b)))
        = fun b : ℝ => 2 * (midC γ (b₀ + Real.pi / 2) b
            - midC γ (b₀ + Real.pi / 2) (b₀ + Real.pi / 4))
          + toCplx (γ (Circle.exp (b₀ + Real.pi / 4))) := by
      funext b
      exact toCplx_exp_eq γ (b₀ + Real.pi / 2) b (b₀ + Real.pi / 4)
    rw [hform]
    exact ((h1.sub h2).const_mul 2).add h3
  have hq : Topology.IsQuotientMap (⇑Circle.exp) :=
    (Circle.isCoveringMap_exp.isOpenMap).isQuotientMap Circle.exp.continuous Circle.exp_surjective
  have hcircle : Continuous (fun x : Circle => toCplx (γ x)) :=
    (Topology.IsQuotientMap.continuous_iff hq).mpr hmain
  have : γ = ofCplx ∘ fun x : Circle => toCplx (γ x) := by
    funext x
    simp [Function.comp_def]
  rw [this]
  exact continuous_ofCplx.comp hcircle

end

end Work.Drive
