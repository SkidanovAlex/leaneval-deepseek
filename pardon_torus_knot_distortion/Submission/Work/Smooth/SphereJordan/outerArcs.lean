import Mathlib
import Submission.Work.Smooth.SphereJordan.Defs
import Submission.Work.Smooth.Jordan.All

/-!
# The canonical radial arcs of the outer Schoenflies disc `e'`

Let `c : ℝ → ℂ ∪ {∞}` be a simple closed curve on the Riemann sphere, and `T : TwoDiscs c` a
two-disc datum for it (see `Work.Smooth.SphereJordan.TwoDiscs`; produced from the planar
Jordan-Schönflies theorem by `Work.Smooth.SphereJordan.planeTwoDiscs`).  Write `e' := T.e'` for
the second of the two complementary embedded discs, with `e' (circlePoint θ) = c θ`.

This file formalises the *canonical family of radial arcs of the outer disc*: for a point `w` of
the unit circle and `t ∈ (0,1]`,

  `outerArc T w t = e' (t • w)`.

Since `e'` is injective, the parametrisation `(w,t) ↦ e' (t w)` is injective on
`S¹ × (0,1]`: arcs of distinct boundary points are **pairwise disjoint** and the parameter is
recovered along an arc.  The endpoint `t = 1` is the curve point `e' (circlePoint θ) = c θ`, so
each arc joins the point `e' 0` of the second disc to the curve.  For the construction of
`planeTwoDiscs` the base point `e' 0` is `∞`, which makes these arcs exactly the crosscuts of the
planar annulus theorem used by `Work.Smooth.SphereJordan.annulusInjection`: the classical "two
cuts" proof cuts the annulus along two of them, so the disjointness proved here is precisely what
makes the gluing of the two spanning discs well defined.
-/

namespace Work.Smooth.SphereJordan

noncomputable section

open Set Metric

/-- The point `t • w` of the model disc, for `w` on the unit circle and `0 < t ≤ 1`. -/
def arcDisc (w : Metric.sphere (0 : ℂ) 1) (t : ℝ) (ht₀ : 0 < t) (ht₁ : t ≤ 1) : Disc :=
  ⟨t * (w : ℂ), by
    have hw : ‖(w : ℂ)‖ = 1 := by simpa [dist_eq_norm] using w.2
    rw [Metric.mem_closedBall, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ht₀, hw, mul_one]
    exact ht₁⟩

@[simp] theorem arcDisc_coe (w : Metric.sphere (0 : ℂ) 1) (t : ℝ) (ht₀ : 0 < t) (ht₁ : t ≤ 1) :
    ((arcDisc w t ht₀ ht₁ : Disc) : ℂ) = t * (w : ℂ) := rfl

/-- **The radial parametrisation is injective** on the unit circle crossed with `(0,1]`. -/
theorem arcDisc_inj {w₁ w₂ : Metric.sphere (0 : ℂ) 1} {t₁ t₂ : ℝ}
    (ht₁₀ : 0 < t₁) (ht₁₁ : t₁ ≤ 1) (ht₂₀ : 0 < t₂) (ht₂₁ : t₂ ≤ 1)
    (h : arcDisc w₁ t₁ ht₁₀ ht₁₁ = arcDisc w₂ t₂ ht₂₀ ht₂₁) : w₁ = w₂ ∧ t₁ = t₂ := by
  have h₁ : ‖(w₁ : ℂ)‖ = 1 := by simpa [dist_eq_norm] using w₁.2
  have h₂ : ‖(w₂ : ℂ)‖ = 1 := by simpa [dist_eq_norm] using w₂.2
  have hc : t₁ * (w₁ : ℂ) = t₂ * (w₂ : ℂ) := by
    have h' : (arcDisc w₁ t₁ ht₁₀ ht₁₁ : ℂ) = (arcDisc w₂ t₂ ht₂₀ ht₂₁ : ℂ) :=
      congrArg Subtype.val h
    simpa [arcDisc] using h'
  have hn : t₁ = t₂ := by
    have hh := congrArg norm hc
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos ht₁₀, abs_of_pos ht₂₀, h₁, h₂, mul_one, mul_one] at hh
    exact hh
  subst hn
  have hw : (w₁ : ℂ) = (w₂ : ℂ) := by
    refine mul_left_cancel₀ ?_ hc
    exact_mod_cast (ne_of_gt ht₁₀ : t₁ ≠ 0)
  exact ⟨Subtype.ext hw, rfl⟩

/-- **The radial arc of the outer Schoenflies disc** through the boundary point `w`: the point
`e' (t w)`. -/
def outerArc {c : ℝ → RiemannSphere} (T : TwoDiscs c) (w : Metric.sphere (0 : ℂ) 1) (t : ℝ)
    (ht₀ : 0 < t) (ht₁ : t ≤ 1) : RiemannSphere :=
  T.e' (arcDisc w t ht₀ ht₁)

/-- **The radial arcs are pairwise disjoint** (and the parameter along an arc is determined):
the parametrisation is injective because `e'` is. -/
theorem outerArc_inj {c : ℝ → RiemannSphere} {T : TwoDiscs c}
    {w₁ w₂ : Metric.sphere (0 : ℂ) 1} {t₁ t₂ : ℝ}
    (ht₁₀ : 0 < t₁) (ht₁₁ : t₁ ≤ 1) (ht₂₀ : 0 < t₂) (ht₂₁ : t₂ ≤ 1)
    (h : outerArc T w₁ t₁ ht₁₀ ht₁₁ = outerArc T w₂ t₂ ht₂₀ ht₂₁) : w₁ = w₂ ∧ t₁ = t₂ :=
  arcDisc_inj ht₁₀ ht₁₁ ht₂₀ ht₂₁ (T.inj' h)

/-- Two arcs through distinct boundary points, with parameters in `(0,1]`, never meet. -/
theorem outerArc_disjoint {c : ℝ → RiemannSphere} {T : TwoDiscs c}
    {w₁ w₂ : Metric.sphere (0 : ℂ) 1} (hw : w₁ ≠ w₂) {t₁ t₂ : ℝ}
    (ht₁₀ : 0 < t₁) (ht₁₁ : t₁ ≤ 1) (ht₂₀ : 0 < t₂) (ht₂₁ : t₂ ≤ 1) :
    outerArc T w₁ t₁ ht₁₀ ht₁₁ ≠ outerArc T w₂ t₂ ht₂₀ ht₂₁ :=
  fun h => hw (outerArc_inj ht₁₀ ht₁₁ ht₂₀ ht₂₁ h).1

/-- **Canonicity of the inner endpoint**: the radial arc through the boundary point representing
`circlePoint θ` ends, at `t = 1`, at the curve point `c θ`. -/
theorem outerArc_one {c : ℝ → RiemannSphere} (T : TwoDiscs c) (w : Metric.sphere (0 : ℂ) 1)
    (θ : ℝ) (hw : (w : ℂ) = ((circlePoint θ : Disc) : ℂ)) :
    outerArc T w 1 (by norm_num) le_rfl = c θ := by
  have hX : arcDisc w 1 (by norm_num) le_rfl = circlePoint θ := by
    apply Subtype.ext
    simp [arcDisc, hw]
  rw [outerArc, hX, T.boundary' θ]



/-! ## The last time a radial arc is outside the open unit disc -/

/-- A point of the Riemann sphere lying in the *open* unit disc. -/
def InOpenDisc (x : RiemannSphere) : Prop := ∃ z : ℂ, ‖z‖ < 1 ∧ (z : RiemannSphere) = x

/-- A point of the Riemann sphere lying in the *closed* unit disc. -/
def InClosedDisc (x : RiemannSphere) : Prop := ∃ z : ℂ, ‖z‖ ≤ 1 ∧ (z : RiemannSphere) = x

theorem inClosedDisc_of_inOpenDisc {x : RiemannSphere} (h : InOpenDisc x) : InClosedDisc x := by
  obtain ⟨z, hz, hzx⟩ := h
  exact ⟨z, hz.le, hzx⟩

/-- The point of the model disc at parameter `t` along the ray to the unit-circle point `w`,
clamped to `[0,1]`; a *total* function of `t`, which is what the supremum arguments below need.
The scalar is written as an explicit complex number so that no norm rewrite ever has to touch a
`max` of reals. -/
def arcPt (w : Metric.sphere (0 : ℂ) 1) (t : ℝ) : Disc :=
  ⟨((max 0 (min t 1) : ℝ) : ℂ) * (w : ℂ), by
    rw [Metric.mem_closedBall, dist_zero_right, norm_mul]
    have hw : ‖(w : ℂ)‖ = 1 := by simpa [dist_eq_norm] using w.2
    rw [hw, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (le_max_left (0 : ℝ) _)]
    exact max_le (by norm_num) (min_le_right _ _)⟩

@[simp] theorem arcPt_coe (w : Metric.sphere (0 : ℂ) 1) (t : ℝ) :
    ((arcPt w t : Disc) : ℂ) = ((max 0 (min t 1) : ℝ) : ℂ) * (w : ℂ) := rfl

theorem continuous_arcPt (w : Metric.sphere (0 : ℂ) 1) : Continuous (arcPt w) := by
  have h1 : Continuous fun t : ℝ => max 0 (min t 1) := by fun_prop
  have h : Continuous fun t : ℝ => ((max 0 (min t 1) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp h1
  exact Continuous.subtype_mk (h.mul continuous_const) (fun t => (arcPt w t).2)

theorem arcPt_zero (w : Metric.sphere (0 : ℂ) 1) :
    arcPt w 0 = ⟨0, by simp [Metric.mem_closedBall]⟩ := by
  apply Subtype.ext
  show ((max 0 (min (0 : ℝ) 1) : ℝ) : ℂ) * (w : ℂ) = (0 : ℂ)
  norm_num

theorem arcPt_one (w : Metric.sphere (0 : ℂ) 1) :
    arcPt w 1 = arcDisc w 1 (by norm_num) le_rfl := by
  apply Subtype.ext
  show ((max 0 (min (1 : ℝ) 1) : ℝ) : ℂ) * (w : ℂ) = ((1 : ℝ) : ℂ) * (w : ℂ)
  norm_num

theorem arcPt_eq_arcDisc (w : Metric.sphere (0 : ℂ) 1) {t : ℝ} (h₀ : 0 < t) (h₁ : t ≤ 1) :
    arcPt w t = arcDisc w t h₀ h₁ := by
  apply Subtype.ext
  show ((max 0 (min t 1) : ℝ) : ℂ) * (w : ℂ) = (t : ℂ) * (w : ℂ)
  have h : max 0 (min t 1) = t :=
    le_antisymm (max_le h₀.le (min_le_left t 1))
      ((le_min le_rfl h₁).trans (le_max_right 0 (min t 1)))
  rw [h]

/-- The parameters at which the radial arc of `w` is *not* in the open unit disc. -/
def arcOutSet {c : ℝ → RiemannSphere} (T : TwoDiscs c) (w : Metric.sphere (0 : ℂ) 1) : Set ℝ :=
  {t : ℝ | 0 < t ∧ t ≤ 1 ∧ ¬ InOpenDisc (T.e' (arcPt w t))}

theorem arcOutSet_subset {c : ℝ → RiemannSphere} (T : TwoDiscs c)
    (w : Metric.sphere (0 : ℂ) 1) : arcOutSet T w ⊆ Set.Ioc 0 1 :=
  fun _ ht => ⟨ht.1, ht.2.1⟩

theorem arcOutSet_bddAbove {c : ℝ → RiemannSphere} (T : TwoDiscs c)
    (w : Metric.sphere (0 : ℂ) 1) : BddAbove (arcOutSet T w) :=
  ⟨1, fun _ ht => ht.2.1⟩

/-- A single parameter at which the arc misses the open disc witnesses nonemptiness. -/
theorem arcOutSet_nonempty_of {c : ℝ → RiemannSphere} (T : TwoDiscs c)
    {w : Metric.sphere (0 : ℂ) 1} {t : ℝ} (ht₀ : 0 < t) (ht₁ : t ≤ 1)
    (h : ¬ InOpenDisc (T.e' (arcPt w t))) : (arcOutSet T w).Nonempty :=
  ⟨t, ht₀, ht₁, h⟩

/-- **The last time the radial arc of `w` is outside the open unit disc**: the supremum of the
parameters in `(0,1]` at which `e'` carries the arc point outside the open disc. -/
def crosscutTime {c : ℝ → RiemannSphere} (T : TwoDiscs c) (w : Metric.sphere (0 : ℂ) 1) : ℝ :=
  sSup (arcOutSet T w)

theorem crosscutTime_le_one {c : ℝ → RiemannSphere} (T : TwoDiscs c)
    {w : Metric.sphere (0 : ℂ) 1} (hne : (arcOutSet T w).Nonempty) :
    crosscutTime T w ≤ 1 :=
  csSup_le hne (fun _ ht => ht.2.1)

theorem crosscutTime_nonneg {c : ℝ → RiemannSphere} (T : TwoDiscs c)
    {w : Metric.sphere (0 : ℂ) 1} (hne : (arcOutSet T w).Nonempty) :
    0 ≤ crosscutTime T w := by
  obtain ⟨t, ht⟩ := hne
  exact le_trans ht.1.le (le_csSup (arcOutSet_bddAbove T w) ht)

/-- **The crosscut is clean**: beyond the last exit the radial arc stays inside the open disc.
This is the property that makes the sub-arc `[crosscutTime T w, 1]` a crosscut of the annulus:
everything after the exit is inside the disc, and the endpoint `t = 1` is the curve point. -/
theorem crosscutTime_clean {c : ℝ → RiemannSphere} (T : TwoDiscs c)
    {w : Metric.sphere (0 : ℂ) 1} (hne : (arcOutSet T w).Nonempty) {s : ℝ}
    (hs : crosscutTime T w < s) (hs1 : s ≤ 1) : InOpenDisc (T.e' (arcPt w s)) := by
  by_contra hcon
  have h0 : 0 < s := lt_of_le_of_lt (crosscutTime_nonneg T hne) hs
  have hmem : s ∈ arcOutSet T w := ⟨h0, hs1, hcon⟩
  exact absurd (le_csSup (arcOutSet_bddAbove T w) hmem) (not_le.mpr hs)


/-- The closed unit disc inside the Riemann sphere is closed. -/
theorem isClosed_inClosedDisc : IsClosed {x : RiemannSphere | InClosedDisc x} := by
  have heq : {x : RiemannSphere | InClosedDisc x} =
      (fun z : ℂ => (z : RiemannSphere)) '' Metric.closedBall (0 : ℂ) 1 := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, by simpa [Metric.mem_closedBall, dist_eq_norm] using hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      refine ⟨z, ?_, rfl⟩
      simpa [Metric.mem_closedBall, dist_eq_norm] using hz
  rw [heq]
  exact ((isCompact_closedBall (0 : ℂ) 1).image
    (f := fun z : ℂ => (z : RiemannSphere)) OnePoint.continuous_coe).isClosed

/-- **The point at the last exit is in the closed unit disc**: it is the limit of the points of the
radial arc just beyond the exit, which are all inside the open disc.  The single extra input is
that the *endpoint* of the arc, `t = 1`, is itself inside the open disc -- for a two-disc datum of
a plane curve this is the hypothesis that the curve lies in the open disc. -/
theorem crosscutTime_mem_closedDisc {c : ℝ → RiemannSphere} (T : TwoDiscs c)
    {w : Metric.sphere (0 : ℂ) 1} (hne : (arcOutSet T w).Nonempty)
    (h1 : InOpenDisc (T.e' (arcPt w 1))) :
    InClosedDisc (T.e' (arcPt w (crosscutTime T w))) := by
  set t₁ := crosscutTime T w with ht₁
  have hcont : Continuous fun t : ℝ => T.e' (arcPt w t) :=
    T.e'.continuous.comp (continuous_arcPt w)
  have hseq_mem : ∀ n : ℕ,
      InClosedDisc (T.e' (arcPt w (t₁ + (1 - t₁) * ((n : ℝ) + 1)⁻¹))) := by
    intro n
    rcases lt_or_eq_of_le (crosscutTime_le_one T hne) with hlt | heq
    · have hpos : 0 < (1 - t₁) * ((n : ℝ) + 1)⁻¹ := by
        refine mul_pos (by linarith) (inv_pos.mpr (by positivity))
      have hle : t₁ + (1 - t₁) * ((n : ℝ) + 1)⁻¹ ≤ 1 := by
        have hle1 : ((n : ℝ) + 1)⁻¹ ≤ 1 := by
          rw [inv_le_one_iff₀]
          right
          have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
          linarith
        nlinarith [hpos, hle1]
      exact inClosedDisc_of_inOpenDisc
        (crosscutTime_clean T hne (lt_add_of_pos_right t₁ hpos) hle)
    · have hconst : t₁ + (1 - t₁) * ((n : ℝ) + 1)⁻¹ = 1 := by
        rw [← heq]; ring
      rw [hconst]
      exact inClosedDisc_of_inOpenDisc h1
  have hlim : Filter.Tendsto (fun n : ℕ => t₁ + (1 - t₁) * ((n : ℝ) + 1)⁻¹)
      Filter.atTop (nhds t₁) := by
    have h0 : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) Filter.atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    simpa using tendsto_const_nhds.add (h0.const_mul (1 - t₁))
  exact isClosed_inClosedDisc.mem_of_tendsto (hcont.continuousAt.tendsto.comp hlim)
    (Filter.Eventually.of_forall hseq_mem)


/-- The open unit disc inside the Riemann sphere is open. -/
theorem isOpen_inOpenDisc : IsOpen {x : RiemannSphere | InOpenDisc x} := by
  have hset : {x : RiemannSphere | InOpenDisc x}
      = (fun z : ℂ => (z : RiemannSphere)) '' Metric.ball (0 : ℂ) 1 := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, by simpa [Metric.mem_ball, dist_eq_norm] using hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      refine ⟨z, ?_, rfl⟩
      simpa [Metric.mem_ball, dist_eq_norm] using hz
  rw [hset]
  exact OnePoint.isOpen_image_coe.mpr Metric.isOpen_ball

/-- **The point at the last exit is not inside the open disc.**  Otherwise, by continuity of the
radial arc and openness of the disc, a whole punctured neighbourhood of the exit parameter would
also lie in the disc, contradicting that the exit parameter is the supremum of the parameters at
which the arc avoids the disc. -/
theorem crosscutTime_notMem_openDisc {c : ℝ → RiemannSphere} (T : TwoDiscs c)
    {w : Metric.sphere (0 : ℂ) 1} (hne : (arcOutSet T w).Nonempty) :
    ¬ InOpenDisc (T.e' (arcPt w (crosscutTime T w))) := by
  intro hcon
  have hcont : Continuous fun t : ℝ => T.e' (arcPt w t) :=
    T.e'.continuous.comp (continuous_arcPt w)
  obtain ⟨δ, hδ, hδ'⟩ :=
    Metric.mem_nhds_iff.mp ((isOpen_inOpenDisc.preimage hcont).mem_nhds hcon)
  have hkey : ∀ u ∈ arcOutSet T w, u ≤ crosscutTime T w - δ := by
    intro u hu
    by_contra hle
    have hlt : crosscutTime T w - δ < u := lt_of_not_ge hle
    have hub : u ≤ crosscutTime T w := le_csSup (arcOutSet_bddAbove T w) hu
    have hdist : dist u (crosscutTime T w) < δ := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith
    exact hu.2.2 (hδ' (by simpa [Metric.mem_ball] using hdist))
  have hsup := csSup_le hne hkey
  have : crosscutTime T w = sSup (arcOutSet T w) := rfl
  linarith [hsup, hδ]


/-- **The point at the last exit lies on the boundary circle of the model disc**: it is in the
closed disc and (unless the exit parameter is the endpoint of the arc) not in the open disc. -/
theorem crosscutTime_norm_eq_one {c : ℝ → RiemannSphere} (T : TwoDiscs c)
    {w : Metric.sphere (0 : ℂ) 1} (hne : (arcOutSet T w).Nonempty)
    (h1 : InOpenDisc (T.e' (arcPt w 1))) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ (z : RiemannSphere) = T.e' (arcPt w (crosscutTime T w)) := by
  obtain ⟨z, hz, hzx⟩ := crosscutTime_mem_closedDisc T hne h1
  refine ⟨z, ?_, hzx⟩
  rcases lt_or_eq_of_le hz with hlt | heq
  · exact absurd ⟨z, hlt, hzx⟩ (crosscutTime_notMem_openDisc T hne)
  · exact heq


/-- **The radial arc meets the inner disc only at its endpoint.**  For `0 < t < 1` the point
`e' (t • w)` of the outer disc lies outside `range e`: the two discs meet exactly in the curve
`range c`, and `e'` is injective with `e' (circlePoint θ) = c θ`, so a point of the arc inside
`range e` would have to be `e' (circlePoint θ)`, forcing `t = 1`.

Equivalently: the interior of the radial arc of the outer disc misses the inner disc, which is
what makes the sub-arc `[crosscutTime T w, 1]` have its interior in the annulus between the curve
and the unit circle. -/
theorem outerArc_notMem_range_e {c : ℝ → RiemannSphere} (T : TwoDiscs c)
    {w : Metric.sphere (0 : ℂ) 1} {t : ℝ} (ht₀ : 0 < t) (ht₁ : t < 1) :
    T.e' (arcDisc w t ht₀ ht₁.le) ∉ Set.range T.e := by
  rintro ⟨z, hz⟩
  have hmem : T.e' (arcDisc w t ht₀ ht₁.le) ∈ Set.range c := by
    rw [← T.meet]
    exact ⟨⟨z, hz⟩, ⟨arcDisc w t ht₀ ht₁.le, rfl⟩⟩
  obtain ⟨θ, hθ⟩ := hmem
  have hEq : arcDisc w t ht₀ ht₁.le = circlePoint θ :=
    T.inj' (by rw [← hθ, ← T.boundary' θ])
  have hn₁ : ‖((arcDisc w t ht₀ ht₁.le : Disc) : ℂ)‖ = t := by
    rw [arcDisc_coe, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht₀]
    have hw : ‖(w : ℂ)‖ = 1 := by simpa [dist_eq_norm] using w.2
    rw [hw, mul_one]
  have hn₂ : ‖((circlePoint θ : Disc) : ℂ)‖ = 1 := by
    rw [Work.Smooth.Jordan.circlePoint_coe, Complex.norm_exp_ofReal_mul_I]
  have ht : t = 1 := by rw [← hn₁, hEq, hn₂]
  linarith


/-- **The crosscut of the annulus.**  For a parameter `t` strictly between the last exit
`crosscutTime T w` and the endpoint `1`, the point of the outer radial arc lies in the *open
annulus*: it is inside the open unit disc (so it is not the point at infinity and not outside the
model disc) and it is outside the inner disc `range e`.

The three inputs are exactly the bricks landed above:
* `crosscutTime_clean` for membership of the open unit disc after the exit;
* `outerArc_notMem_range_e` for exclusion of the inner disc away from `t = 1`;
* `crosscutTime_nonneg` to turn `crosscutTime T w < t` into positivity of `t`. -/
theorem crosscut_mem_annulus_of_twoDiscs {c : ℝ → RiemannSphere} (T : TwoDiscs c)
    {w : Metric.sphere (0 : ℂ) 1} (hne : (arcOutSet T w).Nonempty) {t : ℝ}
    (h₁ : crosscutTime T w < t) (h₂ : t < 1) :
    InOpenDisc (T.e' (arcPt w t)) ∧ T.e' (arcPt w t) ∉ Set.range T.e := by
  have ht0 : 0 < t := lt_of_le_of_lt (crosscutTime_nonneg T hne) h₁
  have hpt : arcPt w t = arcDisc w t ht0 h₂.le := arcPt_eq_arcDisc w ht0 h₂.le
  refine ⟨crosscutTime_clean T hne h₁ h₂.le, ?_⟩
  rw [hpt]
  exact outerArc_notMem_range_e T ht0 h₂

/-- The bundled form: the image of the **open** parameter interval `(crosscutTime T w, 1)` under
the radial arc is contained in the open annulus `𝔻 ∖ range e`.  This is the statement that the
sub-arc `[crosscutTime T w, 1]` is a crosscut of the annulus between the curve `range c` and the
unit circle: its interior lies in the annulus, and its two endpoints are respectively on the unit
circle (`crosscutTime_norm_eq_one`) and on the curve (`outerArc_one`). -/
theorem crosscut_image_subset_annulus {c : ℝ → RiemannSphere} (T : TwoDiscs c)
    {w : Metric.sphere (0 : ℂ) 1} (hne : (arcOutSet T w).Nonempty) :
    T.e' '' (arcPt w '' Set.Ioo (crosscutTime T w) 1)
      ⊆ {x : RiemannSphere | InOpenDisc x ∧ x ∉ Set.range T.e} := by
  rintro x ⟨y, ⟨t, ht, rfl⟩, rfl⟩
  exact crosscut_mem_annulus_of_twoDiscs T hne ht.1 ht.2


/-- **The two cuts are separated.**  The radial arcs through two distinct boundary points, at
parameters in `(0,1]`, never meet.  This is the first input of the two-cut assembly: with
`w₁ = circlePoint 0` and `w₂ = circlePoint π` it says that the two crosscuts of the annulus are
disjoint, so they cut it into two halves. -/
theorem crosscut_disjoint {c : ℝ → RiemannSphere} (T : TwoDiscs c)
    {w₁ w₂ : Metric.sphere (0 : ℂ) 1} (hw : w₁ ≠ w₂) {t₁ t₂ : ℝ}
    (h₁ : 0 < t₁) (h₁' : t₁ ≤ 1) (h₂ : 0 < t₂) (h₂' : t₂ ≤ 1) :
    T.e' (arcPt w₁ t₁) ≠ T.e' (arcPt w₂ t₂) := by
  intro heq
  rw [arcPt_eq_arcDisc w₁ h₁ h₁', arcPt_eq_arcDisc w₂ h₂ h₂'] at heq
  exact hw (arcDisc_inj h₁ h₁' h₂ h₂' (T.inj' heq)).1

/-!
## The two-cut assembly (road map)

The crosscut layer above is complete: every ingredient of the classical "two cuts" proof of the
planar annulus theorem is now a landed lemma.  What remains of `annulusInjection` is the
assembly, and this is its shape.

1. **Two cuts.**  Fix `w₁ = circlePoint 0` and `w₂ = circlePoint π` in the unit circle (any two
   distinct points do), and set `tᵢ = crosscutTime T wᵢ`, which requires the exit set to be
   nonempty for each `wᵢ` (`arcOutSet_nonempty_of`, applied with a parameter at which the arc is
   outside the open disc -- for the `planeTwoDiscs` datum this holds near `t = 0` because
   `e' 0 = ∞`).
2. **The two halves.**  The sub-arcs `[tᵢ, 1]` are crosscuts (`crosscut_mem_annulus`,
   `crosscut_image_subset_annulus`, with feet `crosscutTime_norm_eq_one` and `outerArc_one`) and
   are disjoint (`crosscut_disjoint`).  The two components of the annulus cut along them are the
   "halves"; each is a closed disc whose boundary is a Jordan curve made of one crosscut, one arc
   of `range c`, the other crosscut and one arc of the unit circle.
3. **Spanning discs.**  Apply `h : PlaneHypothesis` to the two boundary Jordan curves.  The
   *parametrisation* of each spanning disc is free up to precomposition with a self-homeomorphism
   of the disc (`Work.Smooth.SphereJordan.ballHomeo_of_circleHomeo`, the coning/Alexander trick),
   so the two discs can be glued along the two cuts with matching boundary values, and the outer
   boundary may be prescribed to be the identity on the unit circle.
4. **Glue and finish.**  The glued map `G : 𝔻 → 𝔻` is an injective continuous self-map fixing
   `∂𝔻` pointwise and carrying `range c` onto the circle of radius `1/2`; that is the conclusion
   of `Work.Smooth.SphereJordan.annulusInjection` (with the orientation sign supplied by the
   choice of parametrisation of the spanning discs), and `annulusStrict` then follows from the
   reduction documented in `Submission/Work/Smooth/SphereJordan/annulusStrict.lean`.
-/

/-- The point at infinity is not in the closed unit disc. -/
theorem not_inClosedDisc_infty : ¬ InClosedDisc infty := by
  rintro ⟨z, _, hz⟩
  exact OnePoint.coe_ne_infty z hz

/-- **The exit set is nonempty as soon as the arc starts at infinity.**  For the two-disc datum
produced by `Work.Smooth.SphereJordan.planeTwoDiscs` the base point `e' 0` is `∞`, and then the
radial arc leaves the closed unit disc near `t = 0`: continuity at `0` (where the arc point is
`arcPt w 0 = 0`) puts the arc point in the open neighbourhood of `∞` for small positive `t`, and
there it is outside the closed disc, hence outside the open disc.

This is the discharge of the hypothesis `hne` of the crosscut layer for the two cuts at
`w₁ = circlePoint 0` and `w₂ = circlePoint π`. -/
theorem arcOutSet_nonempty_of_base_infty {c : ℝ → RiemannSphere} (T : TwoDiscs c)
    (w : Metric.sphere (0 : ℂ) 1)
    (hbase : T.e' (⟨0, by simp [Metric.mem_closedBall]⟩ : Disc) = infty) :
    (arcOutSet T w).Nonempty := by
  have hcont : Continuous fun t : ℝ => T.e' (arcPt w t) :=
    T.e'.continuous.comp (continuous_arcPt w)
  have h0 : T.e' (arcPt w 0) = infty := by
    rw [arcPt_zero, hbase]
  have hpre : (fun t : ℝ => T.e' (arcPt w t)) ⁻¹' {x : RiemannSphere | ¬ InClosedDisc x}
      ∈ nhds (0 : ℝ) :=
    hcont.continuousAt.preimage_mem_nhds (by rw [h0]; exact isClosed_inClosedDisc.isOpen_compl.mem_nhds not_inClosedDisc_infty)
  obtain ⟨ε, hε, hε'⟩ := Metric.mem_nhds_iff.mp hpre
  refine arcOutSet_nonempty_of T (t := min (ε / 2) (1 / 2)) ?_ ?_ ?_
  · exact lt_min (half_pos hε) (by norm_num)
  · exact le_trans (min_le_right _ _) (by norm_num)
  · intro hcon
    have hpos : 0 < min (ε / 2) (1 / 2) := lt_min (half_pos hε) (by norm_num)
    have hmem : dist (min (ε / 2) (1 / 2)) (0 : ℝ) < ε := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hpos]
      linarith [min_le_left (ε / 2) (1 / 2), half_lt_self hε]
    exact hε' (by simpa [Metric.mem_ball] using hmem) (inClosedDisc_of_inOpenDisc hcon)


/-!
## Step 2 in detail: the two halves (notes from implementing step 1)

Setting up the two cuts concretely (`w₁ = circlePoint 0`, `w₂ = circlePoint π`) exposes an
asymmetry that is worth recording before the halves are attempted, because it dictates which
boundary arcs can be written down explicitly and which cannot.

* **The inner feet are explicit.**  `outerArc_one` says the `t = 1` endpoint of the arc through
  `w` is the curve point `c θ` with `circlePoint θ = w`, so for `w = circlePoint 0` it is `c 0`
  and for `w = circlePoint π` it is `c π`.  The two arcs of `range c` between these feet are then
  literally `c '' Icc 0 π` and `c '' Icc π (2π)` (the curve is `2π`-periodic and injective on
  `[0,2π)`, so these are the two halves of the curve, and they are *parametrised curves* as they
  stand).
* **The outer feet are not explicit.**  `crosscutTime T w` is a supremum (`sSup (arcOutSet T w)`),
  so the outer foot `e' (arcPt w (crosscutTime T w))` is a point of the unit circle whose argument
  is not computable from the data.  Consequently the two arcs of the unit circle between the outer
  feet cannot be parametrised by an explicit formula; they must be obtained as the connected
  components of `S¹ ∖ {outer feet}`, or, more robustly, by *avoiding the explicit parametrisation
  altogether*.

**Suggested route for the halves.**  Rather than assembling each half's boundary as an explicit
concatenation of four parametrised arcs (which the previous bullet obstructs), define the two
halves topologically and let the existing machinery name their boundaries:

1. `A := {x | InOpenDisc x ∧ x ∉ Set.range T.e}` is the open annulus (`crosscut_mem_annulus` puts
   the cut interiors in it);
2. `A ∖ (cut₁ ∪ cut₂)` has exactly two components (each crosscut joins the two boundary circles
   and the two cuts are disjoint by `crosscut_disjoint`);
3. the closure of each component is the "half"; its boundary is a Jordan curve whose four arcs are
   a crosscut, an arc of `range c`, a crosscut and an arc of `S¹`;
4. each half being a *disc* is then what `h : PlaneHypothesis` provides, via
   `Work.Smooth.SphereJordan.disc_spans_schoenflies_clean` (uniqueness of the spanning disc) which
   identifies the range of any injective disc map with the given boundary as the closure of the
   bounded side.

The point of writing this down now: steps 1 and 3 of the road map are cheap *given* step 2's
components, and the expensive part of step 2 is precisely the connectedness bookkeeping in item 2,
not any parametrisation.
-/


/-! ## Step 2, first piece: the open annulus `A` -/

/-- **The open annulus** of the two-disc picture: the points inside the open unit disc which are
not in the inner disc `range e`.  This is the region the two crosscuts cut into halves (`A` of
step 2 of the road map). -/
def openAnnulus {c : ℝ → RiemannSphere} (T : TwoDiscs c) : Set RiemannSphere :=
  {x : RiemannSphere | InOpenDisc x ∧ x ∉ Set.range T.e}

theorem mem_openAnnulus {c : ℝ → RiemannSphere} {T : TwoDiscs c} {x : RiemannSphere} :
    x ∈ openAnnulus T ↔ InOpenDisc x ∧ x ∉ Set.range T.e := Iff.rfl

/-- The inner disc `range e` is closed: it is the continuous image of the compact model disc. -/
theorem isClosed_range_e {c : ℝ → RiemannSphere} (T : TwoDiscs c) : IsClosed (Set.range T.e) :=
  (isCompact_range T.e.continuous).isClosed

/-- **The open annulus is open.** -/
theorem isOpen_openAnnulus {c : ℝ → RiemannSphere} (T : TwoDiscs c) :
    IsOpen (openAnnulus T) :=
  isOpen_inOpenDisc.inter (isClosed_range_e T).isOpen_compl

/-- **The cuts lie in the open annulus**: for a parameter strictly between the last exit and the
endpoint, the point of the radial arc is an interior point of `A`.  This is
`crosscut_mem_annulus` restated in the vocabulary of step 2, and it is exactly what the two cuts
need in order to cut `A`. -/
theorem crosscut_mem_openAnnulus {c : ℝ → RiemannSphere} (T : TwoDiscs c)
    {w : Metric.sphere (0 : ℂ) 1} (hne : (arcOutSet T w).Nonempty) {t : ℝ}
    (h₁ : crosscutTime T w < t) (h₂ : t < 1) :
    T.e' (arcPt w t) ∈ openAnnulus T :=
  crosscut_mem_annulus_of_twoDiscs T hne h₁ h₂





/-! ## Step 2, second piece: the slit annulus -/

/-- **The cut** through the boundary point `w`: the image of the open parameter interval between the
last exit and the endpoint of the radial arc.  Its closure is the crosscut, whose endpoints are on
the unit circle (`crosscutTime_norm_eq_one`) and on the curve (`outerArc_one`). -/
def cutSet {c : ℝ → RiemannSphere} (T : TwoDiscs c) (w : Metric.sphere (0 : ℂ) 1) : Set RiemannSphere :=
  T.e' '' (arcPt w '' Set.Ioo (crosscutTime T w) 1)

/-- **The annulus slit along the two cuts**: the open annulus with both cuts removed. -/
def slitAnnulus {c : ℝ → RiemannSphere} (T : TwoDiscs c) (w₁ w₂ : Metric.sphere (0 : ℂ) 1) : Set RiemannSphere :=
  openAnnulus T \ (cutSet T w₁ ∪ cutSet T w₂)

/-- **The cut lies in the open annulus** (`crosscut_mem_openAnnulus` in the vocabulary of the cut). -/
theorem cutSet_subset_openAnnulus {c : ℝ → RiemannSphere} (T : TwoDiscs c)
    {w : Metric.sphere (0 : ℂ) 1} (hne : (arcOutSet T w).Nonempty) :
    cutSet T w ⊆ openAnnulus T := by
  rintro x ⟨y, ⟨t, ht, rfl⟩, rfl⟩
  exact crosscut_mem_openAnnulus T hne ht.1 ht.2

/-- **The two cuts are disjoint** (`crosscut_disjoint` in set form). -/
theorem cutSet_disjoint {c : ℝ → RiemannSphere} (T : TwoDiscs c)
    {w₁ w₂ : Metric.sphere (0 : ℂ) 1} (hw : w₁ ≠ w₂)
    (hne₁ : (arcOutSet T w₁).Nonempty) (hne₂ : (arcOutSet T w₂).Nonempty) :
    Disjoint (cutSet T w₁) (cutSet T w₂) := by
  rw [Set.disjoint_left]
  rintro x ⟨a, ⟨t, ht, rfl⟩, rfl⟩ ⟨b, ⟨s, hs, hb⟩, hx⟩
  have hEq : T.e' (arcPt w₁ t) = T.e' (arcPt w₂ s) := by rw [← hx, ← hb]
  exact crosscut_disjoint T hw (lt_of_le_of_lt (crosscutTime_nonneg T hne₁) ht.1) ht.2.le
    (lt_of_le_of_lt (crosscutTime_nonneg T hne₂) hs.1) hs.2.le hEq


/-!
## `hne` must ride along: the cost of `crosscutTime` being a `sSup`

`crosscutTime T w = sSup (arcOutSet T w)` is defined as a supremum, so **nothing** about positivity
of `crosscutTime T w` follows from the definitions alone: `crosscutTime_nonneg` and
`crosscutTime_le_one` both *require* `(arcOutSet T w).Nonempty`.  Consequently every statement whose
parameters range over the open interval `Set.Ioo (crosscutTime T w) 1` -- the cuts `cutSet T w`,
the slit annulus, and every component lemma about it -- must carry `(arcOutSet T w).Nonempty` (or a
hypothesis supplying one) if it needs `0 < t` for its points.  In particular
`crosscut_disjoint` takes `(h₁ : 0 < t₁)`, not `crosscutTime T w₁ < t₁`, so `cutSet_disjoint` carries
`hne₁`/`hne₂` and derives positivity by
`lt_of_le_of_lt (crosscutTime_nonneg T hne) ht.1`.

For the datum produced by `Work.Smooth.SphereJordan.planeTwoDiscs` the hypothesis is discharged once
and for all by `arcOutSet_nonempty_of_base_infty` (from `e' 0 = ∞`), so callers in the application
never see it.
-/

/-!
## `hball` must be carried by every global statement about `openAnnulus`

`TwoDiscs c` contains **nothing** tying `range e` (the inner disc) to the unit disc: the two discs
are interchangeable, and `planeTwoDiscs` constructs `e` as the bounded side of an arbitrary plane
curve with no ball hypothesis.  So `openAnnulus T = {x | InOpenDisc x ∧ x ∉ range T.e}` can be
**disconnected**: if `range T.e` is a thin sausage, or a tall ellipse, spanning the unit disc, then
`openAnnulus` is the unit disc minus a band and has two components.  In that situation
`openAnnulus T ∖ cutSet T w` is still disconnected, so every *connectivity* statement about the
annulus or the slit annulus is **false** without an extra hypothesis.

The hypothesis is

  `hball : ∀ z : Disc, InOpenDisc (T.e z)`   -- i.e. `range e ⊆` the open unit disc,

the exact analogue of `hball : ∀ θ, ‖γ.γ θ‖ < 1` in `annulusStrict`/`annulus_of_planeHypothesis`
(where it makes `range e` the inner disc of a genuine annulus).  Consequences to keep in mind:

* **Statements that do *not* need `hball`** (they are local facts about one radial arc and the
  ambient unit disc): `crosscut_mem_annulus`, `crosscutTime_clean`, `crosscutTime_notMem_openDisc`,
  `crosscutTime_norm_eq_one`, `cutSet_subset_openAnnulus`, `cutSet_disjoint`, and the topological
  fact `isOpen_openAnnulus`.  These stand as they are.
* **Statements that *do* need `hball`**: `IsPreconnected (openAnnulus T ∖ cutSet T w)`, the
  two-component theorem for `slitAnnulus T w₁ w₂`, the identity of the two halves with their
  closures, and the Jordan-boundary hookup to `PlaneHypothesis`.  All of them must carry `hball`
  (together with `hne₁`, `hne₂` and `w₁ ≠ w₂` where applicable).
* At the application site `hball` is available: it is the `hball : ∀ θ, ‖γ.γ θ‖ < 1` of
  `annulusStrict`, so nothing is lost -- it merely has to be threaded through.
-/
end

end Work.Smooth.SphereJordan
