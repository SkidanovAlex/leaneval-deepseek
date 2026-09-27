import Mathlib
import Submission.Work.Drive.planeChartDefs
import Submission.Work.Drive.OrderBase
import Submission.Work.Drive.omegaChainInterface
import Submission.Work.Drive.planeChart_eq_imp_annulus
import Submission.Work.Drive.cappedPlane

namespace Work.Drive

open scoped Topology
open Filter
open Submission.Configuration (muOrd actC)
open Submission.Geometry (eucNorm eucNorm_nonneg eucNorm_eq_zero)

noncomputable section

set_option linter.style.haveILetI false

/-!
## Locality notes for `coreLoopStripDisjoint`

This module proves `Work.Drive.coreLoopStripDisjoint` (the `Zc γ` half of the core-loop vs
rotated-plane disjointness) from scratch, with two devices that are worth recording.

* **The side function `capSide`.**  A point of the capping space is the class of a configuration
  point or of a cap point, and the two pieces of `CappingSpace` are glued only along the torus where
  the relevant disk coordinate has norm `1`.  The two formulas `1 - ‖d‖²` (configuration piece) and
  `‖ζ‖² - 1` (cap piece) agree on that torus, so they descend to a *continuous* function
  `capSide : CappingSpace → ℝ`, which is `≥ 0` on the configuration side, `≤ 0` on the cap side and
  `0` exactly on the gluing torus.  It is invariant under `rotCapping`.

* **The boundary circle `‖z'‖ = 1/2`.**  The strip clause of `IsPlaneChart` is strict, so the value of
  the chart on that circle is pinned only by continuity.  Continuity of `capSide ∘ Q` is enough: the
  outer sequence (`‖z'‖` approached from above) gives `capSide (Q z') ≥ 0` and the inner sequence
  (the cap clause) gives `capSide (Q z') ≤ 0`, so `Q z'` lies on the gluing torus — hence a
  configuration point with `‖d‖ = 1`, which cannot be the rotation of the strictly configuration-side
  core-loop value.  No identification of the *direction* coordinate at the boundary is needed, and no
  continuity of `γ` is used.
-/

/-! ## The side function of the capping space -/

/-- The side function, on the disjoint union of the two pieces of the capping space. -/
def capSideFun : ConfigPiece ⊕ CapPiece → ℝ :=
  Sum.elim (fun c : ConfigPiece => 1 - ‖(c : ℝ × ℂ × UnitAddCircle).2.1‖ ^ 2)
    (fun q : CapPiece => ‖(q : ℝ × UnitAddCircle × ℂ).2.2‖ ^ 2 - 1)

/-- The two formulas agree on the glued boundary torus, so the side function descends. -/
lemma capSideFun_rel : ∀ a b : ConfigPiece ⊕ CapPiece, cappingRel a b → capSideFun a = capSideFun b := by
  rintro a b (h | ⟨r, hr, θ, φ, h | h⟩)
  · rw [h]
  · obtain ⟨rfl, rfl⟩ := h
    simp [capSideFun, confBdy, capBdy]
  · obtain ⟨rfl, rfl⟩ := h
    simp [capSideFun, confBdy, capBdy]

lemma continuous_capSideFun : Continuous capSideFun :=
  Continuous.sumElim (by fun_prop) (by fun_prop)

/-- **The side function on the capping space.** -/
def capSide : CappingSpace → ℝ := Quotient.lift capSideFun capSideFun_rel

lemma continuous_capSide : Continuous capSide :=
  Continuous.quotient_lift continuous_capSideFun capSideFun_rel

@[simp] lemma capSide_mk (x : ConfigPiece ⊕ CapPiece) :
    capSide (Quotient.mk'' x) = capSideFun x := rfl

@[simp] lemma capSide_mk_inl (c : ConfigPiece) :
    capSide (Quotient.mk'' (Sum.inl c)) = 1 - ‖(c : ℝ × ℂ × UnitAddCircle).2.1‖ ^ 2 := rfl

@[simp] lemma capSide_mk_inr (q : CapPiece) :
    capSide (Quotient.mk'' (Sum.inr q)) = ‖(q : ℝ × UnitAddCircle × ℂ).2.2‖ ^ 2 - 1 := rfl

/-- The configuration piece value of `rotConfig` is the coordinatewise shift (the disk coordinate is
untouched). -/
lemma csd_rotConfig_val (v : UnitAddCircle) (p : ConfigPiece) :
    (rotConfig v p : ℝ × ℂ × UnitAddCircle)
      = ((p : ℝ × ℂ × UnitAddCircle).1, (p : ℝ × ℂ × UnitAddCircle).2.1,
          (p : ℝ × ℂ × UnitAddCircle).2.2 + v) := rfl

lemma csd_rotConfig_val_snd (v : UnitAddCircle) (p : ConfigPiece) :
    (rotConfig v p : ℝ × ℂ × UnitAddCircle).2.1 = (p : ℝ × ℂ × UnitAddCircle).2.1 := rfl

lemma csd_rotCap_val_thd (v : UnitAddCircle) (q : CapPiece) :
    (rotCap v q : ℝ × UnitAddCircle × ℂ).2.2 = (q : ℝ × UnitAddCircle × ℂ).2.2 := rfl

/-- **The side function is invariant under the rotation.** -/
lemma capSide_rotCapping (v : UnitAddCircle) (x : CappingSpace) :
    capSide (rotCapping v x) = capSide x := by
  induction x using Quotient.inductionOn with
  | h p =>
    cases p with
    | inl c => rw [rotCapping_mk, rotSum_inl, capSide_mk_inl, capSide_mk_inl, csd_rotConfig_val_snd]
    | inr q => rw [rotCapping_mk, rotSum_inr, capSide_mk_inr, capSide_mk_inr, csd_rotCap_val_thd]

/-! ## The configuration point of a chart strip value -/

/-- The configuration point of the plane chart at the strip parameter `w`: the chord of `γ` with
parameters `(w 0, w 1)`, in capping coordinates. -/
def chartConfPt (γ : Circle → ℝ × ℝ) (hγne : ∀ x : Circle, γ x ≠ 0)
    (w : EuclideanSpace ℝ (Fin 2)) : ConfigPiece :=
  confPiece (muOrd γ (Circle.exp (w 0), Circle.exp (w 1))) (stripData_pos hγne w)
    (confOf_snd_norm_le_one _)

@[simp] lemma chartConfPt_val (γ : Circle → ℝ × ℝ) (hγne : ∀ x : Circle, γ x ≠ 0)
    (w : EuclideanSpace ℝ (Fin 2)) :
    (chartConfPt γ hγne w : ℝ × ℂ × UnitAddCircle)
      = confOf (muOrd γ (Circle.exp (w 0), Circle.exp (w 1))) := rfl

lemma chartConfPt_len_nonneg (γ : Circle → ℝ × ℝ) (hγne : ∀ x : Circle, γ x ≠ 0)
    (w : EuclideanSpace ℝ (Fin 2)) :
    ‖(chartConfPt γ hγne w : ℝ × ℂ × UnitAddCircle).2.1‖ ≤ 1 := by
  rw [chartConfPt_val]
  exact confOf_snd_norm_le_one _

/-- The parameter of the strip clause of `IsPlaneChart`, folded into the notation `annW`. -/
lemma annW_eq_clause (z : ℂ) :
    (mk2 (Complex.arg z + Real.sqrt (Real.pi ^ 2 * (‖z‖ - 1 / 2) / 2))
      (Complex.arg z - Real.sqrt (Real.pi ^ 2 * (‖z‖ - 1 / 2) / 2))) = annW z := by
  simp [annW, annS]

/-- **The strip clause of a plane chart, in the notation `annW`.** -/
lemma planeChart_strip_value {γ : Circle → ℝ × ℝ} {hγne : ∀ x : Circle, γ x ≠ 0}
    {Q : ℂ → CappingSpace} (hQ : IsPlaneChart γ hγne Q) {z : ℂ}
    (h1 : 1 / 2 < ‖z‖) (h2 : ‖z‖ ≤ 1) :
    Q z = stripChart γ hγne 0 (annW z) := by
  have h := hQ.2.1 z h1 h2
  rwa [annW_eq_clause z] at h

/-- **The strip chart at rotation zero is the class of its configuration point.** -/
lemma stripChart_zero_eq (γ : Circle → ℝ × ℝ) (hγne : ∀ x : Circle, γ x ≠ 0)
    (w : EuclideanSpace ℝ (Fin 2)) :
    stripChart γ hγne 0 w = Quotient.mk'' (Sum.inl (chartConfPt γ hγne w)) := by
  unfold stripChart
  rw [rotConfig_zero]
  rfl

/-! ## Two elementary lemmas on chords -/

/-- **The disk coordinate of a configuration point of positive chord length is strictly inside the
disk.** -/
lemma confOf_snd_norm_lt_one_of_len_ne_zero (p : (ℝ × ℝ) × UnitAddCircle × ℝ) (h : p.2.2 ≠ 0) :
    ‖(confOf p).2.1‖ < 1 := by
  have hSpos : 0 < Real.sqrt (p.1.1 ^ 2 + p.1.2 ^ 2 + p.2.2 ^ 2) :=
    Real.sqrt_pos.mpr (by nlinarith [sq_pos_of_ne_zero h, sq_nonneg p.1.1, sq_nonneg p.1.2])
  have hS2 : Real.sqrt (p.1.1 ^ 2 + p.1.2 ^ 2 + p.2.2 ^ 2) ^ 2
      = p.1.1 ^ 2 + p.1.2 ^ 2 + p.2.2 ^ 2 := Real.sq_sqrt (by positivity)
  have hnorm2 : ‖(confOf p).2.1‖ ^ 2 < 1 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [confOf]
    rw [← sq, ← sq, div_pow, div_pow, ← add_div, hS2]
    rw [div_lt_one (by positivity)]
    nlinarith [sq_pos_of_ne_zero h]
  nlinarith [norm_nonneg (confOf p).2.1, sq_nonneg (‖(confOf p).2.1‖ - 1)]

/-- **Two chord parameters symmetric about `θ` with half-opening `s ∈ (0, π/2]` exponentiate to
distinct points of the circle.** -/
lemma circle_exp_add_ne_exp_sub {θ s : ℝ} (hs : 0 < s) (hs' : s ≤ Real.pi / 2) :
    Circle.exp (θ + s) ≠ Circle.exp (θ - s) := by
  intro h
  obtain ⟨k, hk⟩ := circle_exp_eq_iff_exists_int.mp h
  have hk' : 2 * s = 2 * Real.pi * (k : ℝ) := by linarith [hk]
  have hkpos : (0 : ℝ) < (k : ℝ) := by nlinarith [hs, Real.pi_pos]
  have hklt : (k : ℝ) < 1 := by nlinarith [hs', Real.pi_pos, hk']
  have hk0 : (0 : ℤ) < k := by exact_mod_cast hkpos
  have hk1 : k < (1 : ℤ) := by exact_mod_cast hklt
  omega

lemma annS_eq_pi_div_two {z : ℂ} (hz : ‖z‖ = 1) : annS z = Real.pi / 2 := by
  rw [annS, hz,
    show Real.pi ^ 2 * (1 - 1 / 2) / 2 = (Real.pi / 2) ^ 2 by ring,
    Real.sqrt_sq (by positivity)]

/-! ## The two sequences of the boundary case -/

lemma tendsto_natCast_add_two : Tendsto (fun n : ℕ => ((n : ℝ) + 2)) atTop atTop := by
  have h1 : Tendsto (fun n : ℕ => ((n + 2 : ℕ) : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).comp (Filter.tendsto_add_atTop_nat 2)
  exact h1.congr' (Filter.Eventually.of_forall (fun n => by push_cast; ring))

lemma tendsto_inv_add_two : Tendsto (fun n : ℕ => ((n : ℝ) + 2)⁻¹) atTop (𝓝 0) :=
  tendsto_natCast_add_two.inv_tendsto_atTop

/-- The outer sequence of the boundary case: `(1/2 + 1/(n+2)) • u` tends to `(1/2) • u`. -/
lemma tendsto_half_add_inv_mul (u : ℂ) :
    Tendsto (fun n : ℕ => (((1 / 2 + ((n : ℝ) + 2)⁻¹ : ℝ)) : ℂ) * u) atTop
      (𝓝 (((1 / 2 : ℝ) : ℂ) * u)) := by
  have h1 : Tendsto (fun n : ℕ => (1 / 2 + ((n : ℝ) + 2)⁻¹ : ℝ)) atTop (𝓝 (1 / 2 + 0)) :=
    tendsto_const_nhds.add tendsto_inv_add_two
  have h2 : Tendsto (fun n : ℕ => (((1 / 2 + ((n : ℝ) + 2)⁻¹ : ℝ)) : ℂ)) atTop
      (𝓝 (((1 / 2 : ℝ)) : ℂ)) := by
    have hc : Tendsto (fun r : ℝ => ((r : ℝ) : ℂ)) (𝓝 (1 / 2 + 0)) (𝓝 (((1 / 2 + 0 : ℝ)) : ℂ)) :=
      Complex.continuous_ofReal.continuousAt.tendsto
    have h := hc.comp h1
    rw [show (1 / 2 + 0 : ℝ) = 1 / 2 by norm_num] at h
    exact h.congr' (Filter.Eventually.of_forall (fun n => rfl))
  exact h2.mul tendsto_const_nhds

/-- The inner sequence of the boundary case: `(1/2 - 1/(n+2)) • u` tends to `(1/2) • u`. -/
lemma tendsto_half_sub_inv_mul (u : ℂ) :
    Tendsto (fun n : ℕ => (((1 / 2 - ((n : ℝ) + 2)⁻¹ : ℝ)) : ℂ) * u) atTop
      (𝓝 (((1 / 2 : ℝ) : ℂ) * u)) := by
  have h1 : Tendsto (fun n : ℕ => (1 / 2 - ((n : ℝ) + 2)⁻¹ : ℝ)) atTop (𝓝 (1 / 2 - 0)) :=
    tendsto_const_nhds.sub tendsto_inv_add_two
  have h2 : Tendsto (fun n : ℕ => (((1 / 2 - ((n : ℝ) + 2)⁻¹ : ℝ)) : ℂ)) atTop
      (𝓝 (((1 / 2 : ℝ)) : ℂ)) := by
    have hc : Tendsto (fun r : ℝ => ((r : ℝ) : ℂ)) (𝓝 (1 / 2 - 0)) (𝓝 (((1 / 2 - 0 : ℝ)) : ℂ)) :=
      Complex.continuous_ofReal.continuousAt.tendsto
    have h := hc.comp h1
    rw [show (1 / 2 - 0 : ℝ) = 1 / 2 by norm_num] at h
    exact h.congr' (Filter.Eventually.of_forall (fun n => rfl))
  exact h2.mul tendsto_const_nhds

/-- The norm of a real number, as a complex number. -/
lemma norm_ofReal_coe (r : ℝ) : ‖((r : ℝ) : ℂ)‖ = |r| := by simp

/-- `1 / ((n:ℝ) + 2) ≤ 1 / 2`. -/
lemma inv_add_two_le_half (n : ℕ) : ((n : ℝ) + 2)⁻¹ ≤ 1 / 2 := by
  rw [inv_le_comm₀ (by positivity) (by norm_num), one_div]
  have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

/-- The norm of a point of the outer sequence. -/
lemma norm_half_add_inv_mul {u : ℂ} (hu : ‖u‖ = 1) (n : ℕ) :
    ‖(((1 / 2 + ((n : ℝ) + 2)⁻¹ : ℝ)) : ℂ) * u‖ = 1 / 2 + ((n : ℝ) + 2)⁻¹ := by
  rw [norm_mul, hu, mul_one, norm_ofReal_coe, abs_of_nonneg (by positivity)]

/-- The norm of a point of the inner sequence. -/
lemma norm_half_sub_inv_mul {u : ℂ} (hu : ‖u‖ = 1) (n : ℕ) :
    ‖(((1 / 2 - ((n : ℝ) + 2)⁻¹ : ℝ)) : ℂ) * u‖ = 1 / 2 - ((n : ℝ) + 2)⁻¹ := by
  rw [norm_mul, hu, mul_one, norm_ofReal_coe,
    abs_of_nonneg (by have := inv_add_two_le_half n; linarith)]

/-- **The `Zc γ` half of the core-loop vs rotated-plane disjointness** (it discharges the `sorry` of `Work.Drive.coreLoop_disjoint_rotCapping_stripPart`, whose version without `hγinj` was refuted by the review gate).  A point of the core loop of a plane chart (`Q` at `‖z‖ = 1`) is never the rotation by `w ∈ Zc γ` of a point of the *strip* part of the chart (`1/2 ≤ ‖z'‖ ≤ 1`).

`Work.Drive.mem_Zc_iff` (proved) identifies `Zc γ = (GoodC γ)ᶜ` with "the configuration strip `stripConfig γ = {muOrd γ (x,y) | x ≠ y}` is disjoint from its rotation `actC u '' stripConfig γ`".  The strip clause of `IsPlaneChart` presents `Q` on `1/2 < ‖z'‖ ≤ 1` as a `stripChart` value, i.e. as the capping-space image of a configuration point of `stripConfig γ`, on which `rotCapping w` acts as `actC w`; an equality would therefore exhibit a meet of the strip with its rotation, i.e. `w ∈ GoodC γ`.  The boundary case `‖z'‖ = 1/2` is not covered by the (strict) strip clause: there `Q z'` is pinned only by continuity to the *degenerate* chord at `γ (arg z')`, whose disk coordinate is `‖d‖ = 1` (the capping radius is `√(|mid|² + len²)`, still `|γ x| > 0`), while `Q z` has `‖d‖ < 1` precisely because the maximal chord (parameters `arg z ± π/2`, separation `π`) is non-degenerate — which is what `hγinj` supplies (in the application: `IsSmoothEmbedding`). -/
theorem coreLoopStripDisjoint {γ : Circle → ℝ × ℝ}
    (hγne : ∀ x : Circle, γ x ≠ 0) (hγinj : Function.Injective γ)
    {Q : ℂ → Work.Drive.CappingSpace} (hQ : Work.Drive.IsPlaneChart γ hγne Q)
    {w : UnitAddCircle} (hw : w ∈ Work.Drive.Zc γ) ⦃z z' : ℂ⦄
    (hz : ‖z‖ = 1) (hz'₁ : 1 / 2 ≤ ‖z'‖) (hz'₂ : ‖z'‖ ≤ 1) :
    Q z ≠ Work.Drive.rotCapping w (Q z') := by
  -- continuity of the chart
  have hQc : Continuous Q := by
    letI := cappingCharted
    exact hQ.1.continuous
  -- the value of the chart on the core loop: the maximal chord
  have hloop : Q z = Quotient.mk'' (Sum.inl (chartConfPt γ hγne (annW z))) := by
    rw [planeChart_strip_value hQ (by rw [hz]; norm_num) (le_of_eq hz), stripChart_zero_eq]
  have hloop_ne : Circle.exp ((annW z) 0) ≠ Circle.exp ((annW z) 1) := by
    rw [annW_apply_zero, annW_apply_one, annS_eq_pi_div_two hz]
    exact circle_exp_add_ne_exp_sub (θ := Complex.arg z) (by positivity) le_rfl
  have hloop_lt : ‖(chartConfPt γ hγne (annW z) : ℝ × ℂ × UnitAddCircle).2.1‖ < 1 := by
    have hlen : (muOrd γ (Circle.exp ((annW z) 0), Circle.exp ((annW z) 1))).2.2 ≠ 0 := by
      intro h0
      refine hloop_ne (hγinj ?_)
      exact sub_eq_zero.mp (eucNorm_eq_zero.mp h0)
    rw [chartConfPt_val]
    exact confOf_snd_norm_lt_one_of_len_ne_zero _
      (by simpa only [muOrd] using hlen)
  intro hcon
  rcases lt_or_eq_of_le hz'₁ with hlt | heq
  · -- ## the strict case: both values are strip values
    have hz'1 : Q z' = stripChart γ hγne 0 (annW z') := planeChart_strip_value hQ hlt hz'₂
    have hA : (Quotient.mk'' (Sum.inl (chartConfPt γ hγne (annW z))) : CappingSpace)
        = Quotient.mk'' (Sum.inl (rotConfig w (chartConfPt γ hγne (annW z')))) := by
      rw [← hloop, hcon, hz'1, stripChart_zero_eq, rotCapping_mk, rotSum_inl]
    have hEq : chartConfPt γ hγne (annW z) = rotConfig w (chartConfPt γ hγne (annW z')) :=
      mk_inl_inj.mp hA
    have hval : confOf (muOrd γ (Circle.exp ((annW z) 0), Circle.exp ((annW z) 1)))
        = confOf (actC w (muOrd γ (Circle.exp ((annW z') 0), Circle.exp ((annW z') 1)))) := by
      have hv : ((confOf (muOrd γ (Circle.exp ((annW z') 0), Circle.exp ((annW z') 1)))).1,
          (confOf (muOrd γ (Circle.exp ((annW z') 0), Circle.exp ((annW z') 1)))).2.1,
          (confOf (muOrd γ (Circle.exp ((annW z') 0), Circle.exp ((annW z') 1)))).2.2 + w)
          = confOf (muOrd γ (Circle.exp ((annW z) 0), Circle.exp ((annW z) 1))) := by
        have h2 := congrArg (Subtype.val) hEq
        rw [csd_rotConfig_val] at h2
        rw [chartConfPt_val] at h2
        exact h2.symm
      rw [← hv]
      rfl
    have hPz : muOrd γ (Circle.exp ((annW z) 0), Circle.exp ((annW z) 1))
        = actC w (muOrd γ (Circle.exp ((annW z') 0), Circle.exp ((annW z') 1))) :=
      confOf_injective_of_nonneg (eucNorm_nonneg _) (by rw [actC]; exact eucNorm_nonneg _) hval
    have hz'_ne : Circle.exp ((annW z') 0) ≠ Circle.exp ((annW z') 1) := by
      rw [annW_apply_zero, annW_apply_one]
      exact circle_exp_add_ne_exp_sub (annS_pos hlt) (annS_le hz'₂)
    exact hw ⟨_, _, _, _, hloop_ne, hz'_ne, hPz⟩
  · -- ## the boundary case: ‖z'‖ = 1/2
    -- the boundary circle is approached from both sides along the ray through `z'`
    set u : ℂ := 2 * z' with hu
    have hu1 : ‖u‖ = 1 := by
      rw [hu, norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num, ← heq]
      norm_num
    have hzu : (((1 / 2 : ℝ)) : ℂ) * u = z' := by rw [hu]; push_cast; ring
    set zn : ℕ → ℂ := fun n => (((1 / 2 + ((n : ℝ) + 2)⁻¹ : ℝ)) : ℂ) * u with hzn
    set yn : ℕ → ℂ := fun n => (((1 / 2 - ((n : ℝ) + 2)⁻¹ : ℝ)) : ℂ) * u with hyn
    have hzn_norm : ∀ n : ℕ, ‖zn n‖ = 1 / 2 + ((n : ℝ) + 2)⁻¹ := by
      intro n
      rw [hzn]
      exact norm_half_add_inv_mul hu1 n
    have hyn_norm : ∀ n : ℕ, ‖yn n‖ = 1 / 2 - ((n : ℝ) + 2)⁻¹ := by
      intro n
      rw [hyn]
      exact norm_half_sub_inv_mul hu1 n
    have hzn_tend : Tendsto zn atTop (𝓝 z') := by
      have h := tendsto_half_add_inv_mul u
      rw [← hzu]
      refine h.congr' ?_
      filter_upwards with n
      rw [hzn]
    have hyn_tend : Tendsto yn atTop (𝓝 z') := by
      have h := tendsto_half_sub_inv_mul u
      rw [← hzu]
      refine h.congr' ?_
      filter_upwards with n
      rw [hyn]
    have houter_tend : Tendsto (fun n : ℕ => capSide (Q (zn n))) atTop (𝓝 (capSide (Q z'))) :=
      ((continuous_capSide.comp hQc).tendsto z').comp hzn_tend
    have hinner_tend : Tendsto (fun n : ℕ => capSide (Q (yn n))) atTop (𝓝 (capSide (Q z'))) :=
      ((continuous_capSide.comp hQc).tendsto z').comp hyn_tend
    have houter_ge : 0 ≤ capSide (Q z') := by
      refine ge_of_tendsto' houter_tend ?_
      intro n
      have hstrip : Q (zn n) = stripChart γ hγne 0 (annW (zn n)) := by
        refine planeChart_strip_value hQ ?_ ?_
        · have hpos : (0 : ℝ) < ((n : ℝ) + 2)⁻¹ := by positivity
          rw [hzn_norm n]
          linarith
        · rw [hzn_norm n]
          have := inv_add_two_le_half n
          linarith
      rw [hstrip, stripChart_zero_eq, capSide_mk_inl]
      have hle := chartConfPt_len_nonneg γ hγne (annW (zn n))
      nlinarith [norm_nonneg (chartConfPt γ hγne (annW (zn n)) : ℝ × ℂ × UnitAddCircle).2.1, hle]
    have hinner_le : capSide (Q z') ≤ 0 := by
      refine le_of_tendsto' hinner_tend ?_
      intro n
      obtain ⟨c, hc⟩ := hQ.2.2.2 (yn n) (by
        have hpos : (0 : ℝ) < ((n : ℝ) + 2)⁻¹ := by positivity
        rw [hyn_norm n]
        linarith)
      rw [hc, capSide_mk_inr]
      have hle := c.2.2
      nlinarith [norm_nonneg (c : ℝ × UnitAddCircle × ℂ).2.2, hle]
    have hside0 : capSide (Q z') = 0 := le_antisymm hinner_le houter_ge
    obtain ⟨x, hx⟩ := Quotient.exists_rep (Q z')
    rcases x with c | q
    · -- ## `Q z'` is a configuration class: it must be a boundary point
      have hside : (1 : ℝ) - ‖(c : ℝ × ℂ × UnitAddCircle).2.1‖ ^ 2 = 0 := by
        have h1 : capSide (Q z') = 1 - ‖(c : ℝ × ℂ × UnitAddCircle).2.1‖ ^ 2 := by
          rw [← hx, capSide_mk_inl]
        rw [← h1, hside0]
      have hc1 : ‖(c : ℝ × ℂ × UnitAddCircle).2.1‖ = 1 := by
        nlinarith [norm_nonneg (c : ℝ × ℂ × UnitAddCircle).2.1]
      have hA : (Quotient.mk'' (Sum.inl (chartConfPt γ hγne (annW z))) : CappingSpace)
          = Quotient.mk'' (Sum.inl (rotConfig w c)) := by
        rw [← hloop, hcon, ← hx, rotCapping_mk, rotSum_inl]
      have hEq : chartConfPt γ hγne (annW z) = rotConfig w c := mk_inl_inj.mp hA
      have hlt' : ‖(c : ℝ × ℂ × UnitAddCircle).2.1‖ < 1 := by
        have h2 : ‖(chartConfPt γ hγne (annW z) : ℝ × ℂ × UnitAddCircle).2.1‖
            = ‖(c : ℝ × ℂ × UnitAddCircle).2.1‖ := by
          rw [hEq, csd_rotConfig_val_snd]
        rwa [h2] at hloop_lt
      rw [hc1] at hlt'
      exact absurd hlt' (lt_irrefl 1)
    · -- ## `Q z'` is a cap class
      have hA : (Quotient.mk'' (Sum.inl (chartConfPt γ hγne (annW z))) : CappingSpace)
          = Quotient.mk'' (Sum.inr (rotCap w q)) := by
        rw [← hloop, hcon, ← hx, rotCapping_mk, rotSum_inr]
      exact mk_inl_ne_mk_inr_of_norm_lt_one hloop_lt hA

end

end Work.Drive
