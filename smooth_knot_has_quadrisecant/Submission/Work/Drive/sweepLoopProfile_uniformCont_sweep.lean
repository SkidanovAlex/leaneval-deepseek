import Mathlib
import Submission.Work.Drive.sweepLoopProfileDefs

/-!
# The chamfered sweep loop is uniformly continuous in the sweep parameter

`Work.Drive.sweepLoopProfile r D lam σ w` depends on the sweep parameter `σ` only through the two
clamped lifts `taR D σ`, `tbR D σ`, and both are continuous functions of `σ` that are *constant*
outside the compact interval `[0,1]` (they are `D.ta`, `D.tb` composed with the clamp).  Hence the
map `σ ↦ sweepLoopProfile r D lam σ w` is uniformly continuous on `ℝ`, with a modulus that is
independent of the chamfer `lam ∈ (0,1/4]` and of the profile `w ∈ [0,1]`.

The proof is a two-step estimate.

* Every point of the loop is either an *arc point* `r (taR D σ + ξ * (tbR D σ - taR D σ))` with
  `ξ ∈ [0,1]`, or a *convex combination* of the two evaluations `r (taR D σ)`, `r (tbR D σ)`
  (the branch conditions of the piecewise definition involve only `lam` and `w`, never `σ`, so the
  branch — and the convex weight — is the same at `σ` and at `σ'`).
* The argument of `r` always lies in the fixed interval `[-3A, 3A]`, where `A ≥ 1` bounds the two
  lifts (`sweepProfileLiftBound`), so the difference of two loop points only needs the uniform
  continuity of `r` on that fixed compact interval.  Differences of arguments are convex
  combinations of `taR D σ' - taR D σ` and `tbR D σ' - tbR D σ`, hence bounded by the larger of
  the two, and those are controlled by the uniform continuity of the lifts, which in turn follows
  from the uniform continuity of `D.ta`, `D.tb` on the compact unit interval composed with the
  1-Lipschitz clamp.

The main result is `Work.Drive.sweepLoopProfile_uniformCont_sweep`.
-/

noncomputable section
namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-! ## Bounds and uniform continuity of the clamped lifts -/

/-- Clamping to `[0,1]` is 1-Lipschitz. -/
private lemma clampI_abs_sub_le (x y : ℝ) :
    |((clampI x : ↥unitInterval) : ℝ) - ((clampI y : ↥unitInterval) : ℝ)| ≤ |x - y| := by
  have hx : ((clampI x : ↥unitInterval) : ℝ) = min 1 (max 0 x) := rfl
  have hy : ((clampI y : ↥unitInterval) : ℝ) = min 1 (max 0 y) := rfl
  rw [hx, hy]
  calc |min 1 (max 0 x) - min 1 (max 0 y)| ≤ max |1 - 1| |max 0 x - max 0 y| :=
        abs_min_sub_min_le_max 1 (max 0 x) 1 (max 0 y)
    _ = |max 0 x - max 0 y| := by simp
    _ ≤ max |0 - 0| |x - y| := abs_max_sub_max_le_max 0 x 0 y
    _ = |x - y| := by simp

/-- The clamped lift data are bounded: there is `A ≥ 1` with `|taR D x| ≤ A` and
`|tbR D x| ≤ A` for all real `x`. -/
private lemma sweepProfileLiftBound {d : BandArcData} (D : SweepData d) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ x : ℝ, |taR D x| ≤ A ∧ |tbR D x| ≤ A := by
  obtain ⟨A₀, hA₀⟩ :=
    (isCompact_univ (X := ↥unitInterval)).exists_bound_of_continuousOn D.cont_ta.continuousOn
  obtain ⟨A₁, hA₁⟩ :=
    (isCompact_univ (X := ↥unitInterval)).exists_bound_of_continuousOn D.cont_tb.continuousOn
  refine ⟨max 1 (max A₀ A₁), le_max_left _ _, fun x => ⟨?_, ?_⟩⟩
  · have h : |taR D x| ≤ A₀ := by
      have h' := hA₀ (clampI x) (Set.mem_univ _)
      simpa [taR, Real.norm_eq_abs] using h'
    exact h.trans ((le_max_left A₀ A₁).trans (le_max_right (1 : ℝ) (max A₀ A₁)))
  · have h : |tbR D x| ≤ A₁ := by
      have h' := hA₁ (clampI x) (Set.mem_univ _)
      simpa [tbR, Real.norm_eq_abs] using h'
    exact h.trans ((le_max_right A₀ A₁).trans (le_max_right (1 : ℝ) (max A₀ A₁)))

/-- The clamped lift `taR D` is uniformly continuous on `ℝ`. -/
private lemma taR_uniformCont {d : BandArcData} (D : SweepData d) :
    ∀ ε > 0, ∃ δ > 0, ∀ x y : ℝ, |x - y| ≤ δ → |taR D x - taR D y| ≤ ε := by
  intro ε hε
  have huc : UniformContinuousOn D.ta (Set.univ : Set ↥unitInterval) :=
    isCompact_univ.uniformContinuousOn_of_continuous D.cont_ta.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ0, hδ⟩ := huc ε hε
  refine ⟨δ / 2, by linarith, fun x y hxy => ?_⟩
  have hd : dist (clampI x) (clampI y) < δ := by
    rw [Subtype.dist_eq, Real.dist_eq]
    have := clampI_abs_sub_le x y
    linarith
  have h := hδ (clampI x) (Set.mem_univ _) (clampI y) (Set.mem_univ _) hd
  have h2 : |taR D x - taR D y| < ε := by simpa [taR, Real.dist_eq] using h
  exact h2.le

/-- The clamped lift `tbR D` is uniformly continuous on `ℝ`. -/
private lemma tbR_uniformCont {d : BandArcData} (D : SweepData d) :
    ∀ ε > 0, ∃ δ > 0, ∀ x y : ℝ, |x - y| ≤ δ → |tbR D x - tbR D y| ≤ ε := by
  intro ε hε
  have huc : UniformContinuousOn D.tb (Set.univ : Set ↥unitInterval) :=
    isCompact_univ.uniformContinuousOn_of_continuous D.cont_tb.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ0, hδ⟩ := huc ε hε
  refine ⟨δ / 2, by linarith, fun x y hxy => ?_⟩
  have hd : dist (clampI x) (clampI y) < δ := by
    rw [Subtype.dist_eq, Real.dist_eq]
    have := clampI_abs_sub_le x y
    linarith
  have h := hδ (clampI x) (Set.mem_univ _) (clampI y) (Set.mem_univ _) hd
  have h2 : |tbR D x - tbR D y| < ε := by simpa [tbR, Real.dist_eq] using h
  exact h2.le

/-- A continuous `Space`-valued map is uniformly continuous on a compact interval, with the
interval as a parameter. -/
private lemma continuous_uniformOn_Icc {f : ℝ → Space} (hf : Continuous f) (M : ℝ) :
    ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ, x ∈ Set.Icc (-M) M → ∀ y : ℝ, y ∈ Set.Icc (-M) M →
      |x - y| ≤ δ → ‖f x - f y‖ ≤ ε := by
  intro ε hε
  have huc : UniformContinuousOn f (Set.Icc (-M) M) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hf.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ0, hδ⟩ := huc ε hε
  refine ⟨δ / 2, by linarith, fun x hx y hy hxy => ?_⟩
  have hd : dist x y < δ := by rw [Real.dist_eq]; linarith
  have h := hδ x hx y hy hd
  rw [dist_eq_norm] at h
  exact h.le

/-! ## Elementary norm and convexity estimates -/

/-- A difference of convex combinations of two pairs of points is a convex combination of the two
differences. -/
private lemma norm_cc_sub_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a a' b b' : E} {t ε : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ha : ‖a' - a‖ ≤ ε) (hb : ‖b' - b‖ ≤ ε) :
    ‖((1 - t) • a' + t • b') - ((1 - t) • a + t • b)‖ ≤ ε := by
  have h : ((1 - t) • a' + t • b') - ((1 - t) • a + t • b)
      = (1 - t) • (a' - a) + t • (b' - b) := by
    rw [smul_sub, smul_sub]; abel
  rw [h]
  calc ‖(1 - t) • (a' - a) + t • (b' - b)‖
      ≤ ‖(1 - t) • (a' - a)‖ + ‖t • (b' - b)‖ := norm_add_le _ _
    _ = (1 - t) * ‖a' - a‖ + t * ‖b' - b‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg ht0]
    _ ≤ (1 - t) * ε + t * ε :=
          add_le_add (mul_le_mul_of_nonneg_left ha (by linarith))
            (mul_le_mul_of_nonneg_left hb ht0)
    _ = ε := by ring

/-- An arc point `taR D σ + ξ * sweepW' D σ` at fraction `ξ ∈ [0,1]` stays within the bound on
the two lifts. -/
private lemma sweepProfile_arc_arg_abs_le {d : BandArcData} (D : SweepData d) {A : ℝ}
    (hA : ∀ x : ℝ, |taR D x| ≤ A ∧ |tbR D x| ≤ A) {σ ξ : ℝ}
    (h0 : 0 ≤ ξ) (h1 : ξ ≤ 1) : |taR D σ + ξ * sweepW' D σ| ≤ A := by
  have hrew : taR D σ + ξ * sweepW' D σ = (1 - ξ) * taR D σ + ξ * tbR D σ := by
    simp only [sweepW']; ring
  rw [hrew]
  calc |(1 - ξ) * taR D σ + ξ * tbR D σ|
      ≤ |(1 - ξ) * taR D σ| + |ξ * tbR D σ| := abs_add_le _ _
    _ = (1 - ξ) * |taR D σ| + ξ * |tbR D σ| := by
          rw [abs_mul, abs_mul, abs_of_nonneg h0,
            abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - ξ)]
    _ ≤ (1 - ξ) * A + ξ * A :=
          add_le_add (mul_le_mul_of_nonneg_left (hA σ).1 (by linarith))
            (mul_le_mul_of_nonneg_left (hA σ).2 h0)
    _ = A := by ring

/-! ## The two kinds of loop points move by at most the modulus of continuity of `r` -/

/-- **Arc points**: if the two lifts move by at most `δ` then an arc point moves by at most `ε`,
where `ε` is a modulus of continuity of `r` on the fixed window `[-3A, 3A]`. -/
private lemma sweepProfile_arc_diff_le (r : ℝ → Space) {d : BandArcData} (D : SweepData d)
    {A δ ε : ℝ} (hA0 : 0 ≤ A) (hA : ∀ x : ℝ, |taR D x| ≤ A ∧ |tbR D x| ≤ A)
    (hr : ∀ x : ℝ, x ∈ Set.Icc (-(3 * A)) (3 * A) → ∀ y : ℝ, y ∈ Set.Icc (-(3 * A)) (3 * A) →
        |x - y| ≤ δ → ‖r x - r y‖ ≤ ε)
    {σ σ' ξ : ℝ} (h0 : 0 ≤ ξ) (h1 : ξ ≤ 1)
    (hσ : |taR D σ' - taR D σ| ≤ δ) (hσ' : |tbR D σ' - tbR D σ| ≤ δ) :
    ‖sweepArc' r D σ' ξ - sweepArc' r D σ ξ‖ ≤ ε := by
  have hmem : taR D σ + ξ * sweepW' D σ ∈ Set.Icc (-(3 * A)) (3 * A) := by
    have h : |taR D σ + ξ * sweepW' D σ| ≤ A := sweepProfile_arc_arg_abs_le D hA h0 h1
    rw [Set.mem_Icc]
    exact ⟨by linarith [neg_abs_le (taR D σ + ξ * sweepW' D σ)],
           by linarith [le_abs_self (taR D σ + ξ * sweepW' D σ)]⟩
  have hmem' : taR D σ' + ξ * sweepW' D σ' ∈ Set.Icc (-(3 * A)) (3 * A) := by
    have h : |taR D σ' + ξ * sweepW' D σ'| ≤ A :=
      sweepProfile_arc_arg_abs_le D hA h0 h1 (σ := σ')
    rw [Set.mem_Icc]
    exact ⟨by linarith [neg_abs_le (taR D σ' + ξ * sweepW' D σ')],
           by linarith [le_abs_self (taR D σ' + ξ * sweepW' D σ')]⟩
  refine hr _ hmem' _ hmem ?_
  have hrew : (taR D σ' + ξ * sweepW' D σ') - (taR D σ + ξ * sweepW' D σ)
      = (1 - ξ) * (taR D σ' - taR D σ) + ξ * (tbR D σ' - tbR D σ) := by
    simp only [sweepW']; ring
  rw [hrew]
  calc |(1 - ξ) * (taR D σ' - taR D σ) + ξ * (tbR D σ' - tbR D σ)|
      ≤ |(1 - ξ) * (taR D σ' - taR D σ)| + |ξ * (tbR D σ' - tbR D σ)| := abs_add_le _ _
    _ = (1 - ξ) * |taR D σ' - taR D σ| + ξ * |tbR D σ' - tbR D σ| := by
          rw [abs_mul, abs_mul, abs_of_nonneg h0,
            abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - ξ)]
    _ ≤ (1 - ξ) * δ + ξ * δ :=
          add_le_add (mul_le_mul_of_nonneg_left hσ (by linarith))
            (mul_le_mul_of_nonneg_left hσ' h0)
    _ = δ := by ring

/-- **Chord points**: a chord point is a convex combination of the two evaluations, so it moves
by at most `ε` as soon as each evaluation does. -/
private lemma sweepProfile_chord_diff_le (r : ℝ → Space) {d : BandArcData} (D : SweepData d)
    {A δ ε : ℝ} (hA0 : 0 ≤ A) (hA : ∀ x : ℝ, |taR D x| ≤ A ∧ |tbR D x| ≤ A)
    (hr : ∀ x : ℝ, x ∈ Set.Icc (-(3 * A)) (3 * A) → ∀ y : ℝ, y ∈ Set.Icc (-(3 * A)) (3 * A) →
        |x - y| ≤ δ → ‖r x - r y‖ ≤ ε)
    {σ σ' ξ : ℝ} (h0 : 0 ≤ ξ) (h1 : ξ ≤ 1)
    (hσ : |taR D σ' - taR D σ| ≤ δ) (hσ' : |tbR D σ' - tbR D σ| ≤ δ) :
    ‖sweepChord' r D σ' ξ - sweepChord' r D σ ξ‖ ≤ ε := by
  have hle : A ≤ 3 * A := by linarith
  have hmem : ∀ x : ℝ, taR D x ∈ Set.Icc (-(3 * A)) (3 * A) := by
    intro x
    rw [Set.mem_Icc]
    have hx := (hA x).1.trans hle
    exact ⟨by linarith [neg_abs_le (taR D x)], by linarith [le_abs_self (taR D x)]⟩
  have hmem' : ∀ x : ℝ, tbR D x ∈ Set.Icc (-(3 * A)) (3 * A) := by
    intro x
    rw [Set.mem_Icc]
    have hx := (hA x).2.trans hle
    exact ⟨by linarith [neg_abs_le (tbR D x)], by linarith [le_abs_self (tbR D x)]⟩
  exact norm_cc_sub_le h0 h1 (hr _ (hmem σ') _ (hmem σ) hσ) (hr _ (hmem' σ') _ (hmem' σ) hσ')

/-! ## The branch fractions of the profile loop

The branch conditions of `sweepLoopProfile` involve only `lam` and `w`, and the convex weights of
the two chamfers lie in `[0,1]` as soon as `0 < lam ≤ 1/4` and `w ∈ [0,1]`. -/

private lemma sweepProfile_branch1_mem {lam w : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1 / 4)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1 / 2) :
    lam + (1 - 2 * lam) * (2 * w) ∈ Set.Icc (0 : ℝ) 1 := by
  rw [Set.mem_Icc]
  constructor
  · nlinarith [h0.le, hw0, h1]
  · have h2w : 2 * w ≤ 1 := by linarith
    have hc : (0 : ℝ) ≤ 1 - 2 * lam := by linarith
    have hm : (1 - 2 * lam) * (2 * w) ≤ 1 - 2 * lam := by
      calc (1 - 2 * lam) * (2 * w) ≤ (1 - 2 * lam) * 1 := mul_le_mul_of_nonneg_left h2w hc
        _ = 1 - 2 * lam := by ring
    linarith

private lemma sweepProfile_branch2_mem {lam w : ℝ} (h0 : 0 < lam) (h1 : 1 / 2 < w)
    (h2 : w ≤ 1 / 2 + lam / 2) : (2 * w - 1) / lam ∈ Set.Icc (0 : ℝ) 1 := by
  rw [Set.mem_Icc]
  exact ⟨div_nonneg (by linarith) h0.le, (div_le_one h0).mpr (by linarith)⟩

private lemma sweepProfile_branch3_mem {lam w : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1 / 4)
    (h2 : 1 / 2 + lam / 2 < w) (h3 : w ≤ 1 - lam / 2) :
    (1 - lam) - ((w - (1 / 2 + lam / 2)) / (1 / 2 - lam)) * (1 - 2 * lam)
      ∈ Set.Icc (0 : ℝ) 1 := by
  rw [Set.mem_Icc]
  have hden : (0 : ℝ) < 1 / 2 - lam := by linarith
  have hu0 : 0 ≤ (w - (1 / 2 + lam / 2)) / (1 / 2 - lam) := div_nonneg (by linarith) hden.le
  have hu1 : (w - (1 / 2 + lam / 2)) / (1 / 2 - lam) ≤ 1 := (div_le_one hden).mpr (by linarith)
  constructor <;> nlinarith [hu0, hu1]

private lemma sweepProfile_branch4_mem {lam w : ℝ} (h0 : 0 < lam) (hw1 : w ≤ 1)
    (h4 : 1 - lam / 2 < w) : (w - (1 - lam / 2)) / (lam / 2) ∈ Set.Icc (0 : ℝ) 1 := by
  rw [Set.mem_Icc]
  have hden : (0 : ℝ) < lam / 2 := by linarith
  exact ⟨div_nonneg (by linarith) hden.le, (div_le_one hden).mpr (by linarith)⟩

/-! ## The four branches of the profile loop -/

private lemma sweepProfile_eq_arc (r : ℝ → Space) {d : BandArcData} (D : SweepData d)
    {lam s w : ℝ} (hw : w ≤ 1 / 2) :
    sweepLoopProfile r D lam s w = sweepArc' r D s (lam + (1 - 2 * lam) * (2 * w)) := by
  simp only [sweepLoopProfile, if_pos hw]

private lemma sweepProfile_eq_lin2 (r : ℝ → Space) {d : BandArcData} (D : SweepData d)
    {lam s w : ℝ} (h1 : ¬ w ≤ 1 / 2) (h2 : w ≤ 1 / 2 + lam / 2) :
    sweepLoopProfile r D lam s w
      = (1 - (2 * w - 1) / lam) • sweepArc' r D s (1 - lam)
        + ((2 * w - 1) / lam) • sweepChord' r D s (1 - lam) := by
  simp only [sweepLoopProfile, if_neg h1, if_pos h2]

private lemma sweepProfile_eq_chord3 (r : ℝ → Space) {d : BandArcData} (D : SweepData d)
    {lam s w : ℝ} (h1 : ¬ w ≤ 1 / 2) (h2 : ¬ w ≤ 1 / 2 + lam / 2) (h3 : w ≤ 1 - lam / 2) :
    sweepLoopProfile r D lam s w
      = sweepChord' r D s ((1 - lam) - ((w - (1 / 2 + lam / 2)) / (1 / 2 - lam))
          * (1 - 2 * lam)) := by
  simp only [sweepLoopProfile, if_neg h1, if_neg h2, if_pos h3]

private lemma sweepProfile_eq_lin4 (r : ℝ → Space) {d : BandArcData} (D : SweepData d)
    {lam s w : ℝ} (h1 : ¬ w ≤ 1 / 2) (h2 : ¬ w ≤ 1 / 2 + lam / 2) (h4 : ¬ w ≤ 1 - lam / 2) :
    sweepLoopProfile r D lam s w
      = (1 - (w - (1 - lam / 2)) / (lam / 2)) • sweepChord' r D s lam
        + ((w - (1 - lam / 2)) / (lam / 2)) • sweepArc' r D s lam := by
  simp only [sweepLoopProfile, if_neg h1, if_neg h2, if_neg h4]

/-! ## The main theorem -/

theorem sweepLoopProfile_uniformCont_sweep {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    {d : LeanEval.KnotTheory.Quadrisecant.BandArcData} (D : Work.Drive.SweepData d)
    (hr : Continuous r) :
    ∀ ε : ℝ, 0 < ε → ∃ θ : ℝ, 0 < θ ∧
      ∀ (lam : ℝ), 0 < lam → lam ≤ 1 / 4 →
        ∀ (σ σ' : ℝ) (w : ℝ), w ∈ Set.Icc (0 : ℝ) 1 → |σ - σ'| ≤ θ →
          ‖Work.Drive.sweepLoopProfile r D lam σ' w - Work.Drive.sweepLoopProfile r D lam σ w‖ ≤ ε := by
  intro ε hε
  obtain ⟨A, hA1, hA⟩ := sweepProfileLiftBound D
  have hA0 : 0 ≤ A := by linarith
  obtain ⟨δr, hδr0, hδr⟩ := continuous_uniformOn_Icc hr (3 * A) ε hε
  obtain ⟨δa, hδa0, hδa⟩ := taR_uniformCont D δr hδr0
  obtain ⟨δb, hδb0, hδb⟩ := tbR_uniformCont D δr hδr0
  refine ⟨min δa δb, lt_min hδa0 hδb0, ?_⟩
  intro lam hlam0 hlam1 σ σ' w hw hσθ
  have hσa : |σ' - σ| ≤ δa := by rw [abs_sub_comm]; exact hσθ.trans (min_le_left _ _)
  have hσb : |σ' - σ| ≤ δb := by rw [abs_sub_comm]; exact hσθ.trans (min_le_right _ _)
  have hta : |taR D σ' - taR D σ| ≤ δr := hδa σ' σ hσa
  have htb : |tbR D σ' - tbR D σ| ≤ δr := hδb σ' σ hσb
  have hw0 : 0 ≤ w := hw.1
  have hw1 : w ≤ 1 := hw.2
  have harc : ∀ ξ : ℝ, 0 ≤ ξ → ξ ≤ 1 →
      ‖sweepArc' r D σ' ξ - sweepArc' r D σ ξ‖ ≤ ε :=
    fun ξ h0 h1 => sweepProfile_arc_diff_le r D hA0 hA hδr h0 h1 hta htb
  have hchord : ∀ ξ : ℝ, 0 ≤ ξ → ξ ≤ 1 →
      ‖sweepChord' r D σ' ξ - sweepChord' r D σ ξ‖ ≤ ε :=
    fun ξ h0 h1 => sweepProfile_chord_diff_le r D hA0 hA hδr h0 h1 hta htb
  have h1ml : 1 - lam ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hlamI : lam ∈ Set.Icc (0 : ℝ) 1 := ⟨hlam0.le, by linarith⟩
  by_cases hwle : w ≤ 1 / 2
  · rw [sweepProfile_eq_arc r D hwle, sweepProfile_eq_arc r D hwle]
    have hb := sweepProfile_branch1_mem hlam0 hlam1 hw0 hwle
    exact harc _ hb.1 hb.2
  · have hneg : ¬ w ≤ 1 / 2 := hwle
    have hwlt : 1 / 2 < w := lt_of_not_ge hwle
    by_cases hw2 : w ≤ 1 / 2 + lam / 2
    · rw [sweepProfile_eq_lin2 r D hneg hw2, sweepProfile_eq_lin2 r D hneg hw2]
      have hm := sweepProfile_branch2_mem hlam0 hwlt hw2
      exact norm_cc_sub_le hm.1 hm.2 (harc (1 - lam) h1ml.1 h1ml.2)
        (hchord (1 - lam) h1ml.1 h1ml.2)
    · by_cases hw3 : w ≤ 1 - lam / 2
      · rw [sweepProfile_eq_chord3 r D hneg hw2 hw3, sweepProfile_eq_chord3 r D hneg hw2 hw3]
        have hm := sweepProfile_branch3_mem hlam0 hlam1 (lt_of_not_ge hw2) hw3
        exact hchord _ hm.1 hm.2
      · rw [sweepProfile_eq_lin4 r D hneg hw2 hw3, sweepProfile_eq_lin4 r D hneg hw2 hw3]
        have hm := sweepProfile_branch4_mem hlam0 hw1 (lt_of_not_ge hw3)
        exact norm_cc_sub_le hm.1 hm.2 (hchord lam hlamI.1 hlamI.2) (harc lam hlamI.1 hlamI.2)

end Work.Drive
