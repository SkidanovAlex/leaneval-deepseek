import Mathlib
import Submission.Work.Drive.chordSweepSmooth

/-!
# Local integrability of the chamfered sweep loop

`Work.Drive.sweepLoopChamfer r D lam s t` is the raw sweep loop of the "sweep through
embeddings" proof, as a function of the *pair* `(s, t)` of (sweep parameter, loop parameter).
Here we show that this two-variable function is locally integrable for the Lebesgue measure on
`ℝ × ℝ`.

The function is *piecewise* in the profile variable `u = sweepParam t ∈ [0,1)`, and every piece is
a continuous function of `(s, u)`; consequently

* it is (Borel) measurable — the branches are built from `r`, `taR`, `tbR`, `sweepW'` and the
  measurable profile `sweepParam` by measurable operations, and the branch conditions are
  measurable sets (`Work.Drive.sweepLoopChamfer_measurable`);
* it is *globally bounded*: `s` enters only through the two continuous lifts `taR D`, `tbR D`,
  whose ranges are bounded (they factor through the compact interval `I`), and the profile
  `u` enters only through explicit convex combinations of at most two evaluations of `r` along
  a fixed bounded parameter interval.  Concretely, with `A` bounding `|taR D|` and `|tbR D|`,
  `K := |lam| + |1-lam|` bounding every profile value/coefficient, and `R` bounding `‖r x‖` for
  `|x| ≤ A (1 + 2K)`, the whole loop is bounded by `(2K+1) * R`
  (`Work.Drive.sweepLoopChamfer_norm_bound`).

Local integrability then follows from `LocallyIntegrable.mono` against the constant function.

## Main theorem

* `Work.Drive.sweepLoopChamfer_locallyIntegrable`
-/

noncomputable section

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant MeasureTheory
open scoped Real Topology unitInterval

/-! ## Continuity of the auxiliary parameter maps -/

/-- The clamping map `ℝ → I` is continuous. -/
lemma sweepLoopChamfer_clampI_continuous : Continuous (clampI : ℝ → I) :=
  Continuous.subtype_mk (continuous_const.min (continuous_const.max continuous_id)) _

/-- The extended `a`-branch lift is continuous. -/
lemma sweepLoopChamfer_taR_continuous {d : BandArcData} (D : SweepData d) : Continuous (taR D) :=
  D.cont_ta.comp sweepLoopChamfer_clampI_continuous

/-- The extended `b`-branch lift is continuous. -/
lemma sweepLoopChamfer_tbR_continuous {d : BandArcData} (D : SweepData d) : Continuous (tbR D) :=
  D.cont_tb.comp sweepLoopChamfer_clampI_continuous

/-- The width of the retained arc is continuous in the sweep parameter. -/
lemma sweepLoopChamfer_sweepW'_continuous {d : BandArcData} (D : SweepData d) : Continuous (sweepW' D) :=
  (sweepLoopChamfer_tbR_continuous D).sub (sweepLoopChamfer_taR_continuous D)

/-! ## Measurability of the loop profile -/

/-- The loop parameter `t ↦ t/period - ⌊t/period⌋` is Borel measurable. -/
lemma sweepLoopChamfer_sweepParam_measurable : Measurable (sweepParam : ℝ → ℝ) := by
  unfold sweepParam
  refine Measurable.sub ?_ ?_
  · exact measurable_id.div_const period
  · fun_prop

/-- **The chamfered loop is measurable in the pair `(s, t)`.** -/
lemma sweepLoopChamfer_measurable {r : ℝ → Space} {d : BandArcData} (D : SweepData d)
    (hr : Continuous r) (lam : ℝ) :
    Measurable (fun p : ℝ × ℝ => sweepLoopChamfer r D lam p.1 p.2) := by
  have hta : Measurable (fun i : I => D.ta i) := D.cont_ta.measurable
  have htb : Measurable (fun i : I => D.tb i) := D.cont_tb.measurable
  have hcl : Measurable (clampI : ℝ → I) := sweepLoopChamfer_clampI_continuous.measurable
  have hr' : Measurable r := hr.measurable
  have hsp : Measurable (fun p : ℝ × ℝ => sweepParam p.2) :=
    sweepLoopChamfer_sweepParam_measurable.comp measurable_snd
  simp only [sweepLoopChamfer]
  refine Measurable.ite ?_ ?_ ?_
  · exact measurableSet_le hsp measurable_const
  · unfold sweepArc' sweepW' taR tbR; fun_prop
  refine Measurable.ite ?_ ?_ ?_
  · exact measurableSet_le hsp measurable_const
  · unfold sweepArc' sweepChord' sweepW' taR tbR; fun_prop
  refine Measurable.ite ?_ ?_ ?_
  · exact measurableSet_le hsp measurable_const
  · unfold sweepChord' taR tbR; fun_prop
  · unfold sweepArc' sweepChord' sweepW' taR tbR; fun_prop

/-! ## Two elementary estimates -/

/-- A convex combination of two reals is bounded by the larger of the two. -/
lemma sweepLoopChamfer_abs_convex_le {a b t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    |(1 - t) * a + t * b| ≤ max |a| |b| := by
  refine (abs_add_le ((1 - t) * a) (t * b)).trans ?_
  rw [abs_mul, abs_mul, abs_of_nonneg (show 0 ≤ 1 - t by linarith), abs_of_nonneg h0]
  calc (1 - t) * |a| + t * |b| ≤ (1 - t) * max |a| |b| + t * max |a| |b| :=
        add_le_add (mul_le_mul_of_nonneg_left (le_max_left |a| |b|) (by linarith))
          (mul_le_mul_of_nonneg_left (le_max_right |a| |b|) h0)
    _ = max |a| |b| := by ring

/-- A convex combination of two vectors is bounded by the larger of the two norms. -/
lemma sweepLoopChamfer_norm_smul_combo_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (P Q : E) :
    ‖(1 - c) • P + c • Q‖ ≤ max ‖P‖ ‖Q‖ := by
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_of_nonneg (show 0 ≤ 1 - c by linarith),
    Real.norm_of_nonneg hc0]
  calc (1 - c) * ‖P‖ + c * ‖Q‖ ≤ (1 - c) * max ‖P‖ ‖Q‖ + c * max ‖P‖ ‖Q‖ :=
        add_le_add (mul_le_mul_of_nonneg_left (le_max_left ‖P‖ ‖Q‖) (by linarith))
          (mul_le_mul_of_nonneg_left (le_max_right ‖P‖ ‖Q‖) hc0)
    _ = max ‖P‖ ‖Q‖ := by ring

/-! ## Bounds for the two kinds of points of the loop -/

/-- The width of the retained arc is bounded by twice the bound on the branches. -/
lemma sweepLoopChamfer_sweepW'_abs_le {d : BandArcData} (D : SweepData d) {A : ℝ}
    (hA : ∀ x : ℝ, |taR D x| ≤ A ∧ |tbR D x| ≤ A) (x : ℝ) :
    |sweepW' D x| ≤ 2 * A := by
  have hsub : |tbR D x - taR D x| ≤ |tbR D x| + |taR D x| := by
    simpa [sub_eq_add_neg] using abs_add_le (tbR D x) (-(taR D x))
  calc |sweepW' D x| = |tbR D x - taR D x| := rfl
    _ ≤ |tbR D x| + |taR D x| := hsub
    _ ≤ A + A := add_le_add (hA x).2 (hA x).1
    _ = 2 * A := by ring

/-- **Arc points of the loop are bounded.**  A point at fraction `ξ` of the retained arc is
evaluated at `taR D s + ξ · sweepW' D s`, which stays in the interval on which `R` bounds `r`. -/
lemma sweepLoopChamfer_sweepArc'_norm_le {r : ℝ → Space} {d : BandArcData} (D : SweepData d) {A K R : ℝ}
    (hA : ∀ x : ℝ, |taR D x| ≤ A ∧ |tbR D x| ≤ A) (hK0 : 0 ≤ K)
    (hR : ∀ x : ℝ, |x| ≤ A * (1 + 2 * K) → ‖r x‖ ≤ R) (s ξ : ℝ) (hξ : |ξ| ≤ K) :
    ‖sweepArc' r D s ξ‖ ≤ R := by
  refine hR _ ?_
  calc |taR D s + ξ * sweepW' D s| ≤ |taR D s| + |ξ * sweepW' D s| := abs_add_le _ _
    _ = |taR D s| + |ξ| * |sweepW' D s| := by rw [abs_mul]
    _ ≤ A + K * (2 * A) :=
        add_le_add (hA s).1 (mul_le_mul hξ (sweepLoopChamfer_sweepW'_abs_le D hA s) (abs_nonneg _) hK0)
    _ = A * (1 + 2 * K) := by ring

/-- **Chord points of the loop are bounded.**  A point at fraction `ξ` of the chord is the convex
combination of the two evaluations `r (taR D s)`, `r (tbR D s)`, both within the bounded
interval. -/
lemma sweepLoopChamfer_sweepChord'_norm_le {r : ℝ → Space} {d : BandArcData} (D : SweepData d) {A K R : ℝ}
    (hA : ∀ x : ℝ, |taR D x| ≤ A ∧ |tbR D x| ≤ A) (hK0 : 0 ≤ K) (hR0 : 0 ≤ R)
    (hR : ∀ x : ℝ, |x| ≤ A * (1 + 2 * K) → ‖r x‖ ≤ R) (s ξ : ℝ) (hξ : |ξ| ≤ K) :
    ‖sweepChord' r D s ξ‖ ≤ (2 * K + 1) * R := by
  have hA0 : 0 ≤ A := le_trans (abs_nonneg (taR D 0)) (hA 0).1
  have hrA : ∀ x : ℝ, |x| ≤ A → ‖r x‖ ≤ R := fun x hx => hR x (by nlinarith [hx, hA0, hK0])
  have hP : ‖r (taR D s)‖ ≤ R := hrA _ (hA s).1
  have hQ : ‖r (tbR D s)‖ ≤ R := hrA _ (hA s).2
  have hbase : ‖sweepChord' r D s ξ‖ ≤ (|1 - ξ| + |ξ|) * R := by
    calc ‖sweepChord' r D s ξ‖ = ‖(1 - ξ) • r (taR D s) + ξ • r (tbR D s)‖ := rfl
      _ ≤ ‖(1 - ξ) • r (taR D s)‖ + ‖ξ • r (tbR D s)‖ := norm_add_le _ _
      _ = |1 - ξ| * ‖r (taR D s)‖ + |ξ| * ‖r (tbR D s)‖ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ |1 - ξ| * R + |ξ| * R :=
            add_le_add (mul_le_mul_of_nonneg_left hP (abs_nonneg _))
              (mul_le_mul_of_nonneg_left hQ (abs_nonneg _))
      _ = (|1 - ξ| + |ξ|) * R := by ring
  refine hbase.trans ?_
  have hkey : |1 - ξ| + |ξ| ≤ 2 * K + 1 := by
    have h1 : |1 - ξ| ≤ 1 + |ξ| := by
      have := abs_add_le (1 : ℝ) (-ξ)
      rw [abs_neg] at this
      simpa [sub_eq_add_neg] using this
    linarith
  exact mul_le_mul_of_nonneg_right hkey hR0

/-! ## The global bound for the chamfered sweep loop -/

/-- **The chamfered sweep loop is globally bounded.**  Each of the four pieces of the loop is
bounded by `(2K+1) * R` as soon as `K` bounds the two profile values `lam`, `1 - lam` and `R`
bounds `‖r x‖` on the interval `|x| ≤ A (1 + 2K)` that the loop's points of evaluation live in. -/
lemma sweepLoopChamfer_norm_bound {r : ℝ → Space} {d : BandArcData} (D : SweepData d) (lam A K R : ℝ)
    (hA : ∀ x : ℝ, |taR D x| ≤ A ∧ |tbR D x| ≤ A) (hK0 : 0 ≤ K)
    (hR : ∀ x : ℝ, |x| ≤ A * (1 + 2 * K) → ‖r x‖ ≤ R)
    (hKlam : |lam| ≤ K) (hK1m : |1 - lam| ≤ K) :
    ∀ s t : ℝ, ‖sweepLoopChamfer r D lam s t‖ ≤ (2 * K + 1) * R := by
  have hR0 : 0 ≤ R := by
    have hA0 : 0 ≤ A := le_trans (abs_nonneg (taR D 0)) (hA 0).1
    exact le_trans (norm_nonneg (r 0)) (hR 0 (by rw [abs_zero]; nlinarith [hA0, hK0]))
  intro s t
  obtain ⟨hu0, hu1⟩ := sweepParam_mem t
  have hC : R ≤ (2 * K + 1) * R := by nlinarith [hR0, hK0]
  have hArc : ∀ ξ : ℝ, |ξ| ≤ K → ‖sweepArc' r D s ξ‖ ≤ R :=
    fun ξ hξ => sweepLoopChamfer_sweepArc'_norm_le D hA hK0 hR s ξ hξ
  have hChord : ∀ ξ : ℝ, |ξ| ≤ K → ‖sweepChord' r D s ξ‖ ≤ (2 * K + 1) * R :=
    fun ξ hξ => sweepLoopChamfer_sweepChord'_norm_le D hA hK0 hR0 hR s ξ hξ
  simp only [sweepLoopChamfer]
  split_ifs with h1 h2 h3
  · -- the arc side: the profile value is a convex combination of `lam` and `1 - lam`
    refine (hArc _ ?_).trans hC
    have h2u0 : 0 ≤ 2 * sweepParam t := by linarith
    have h2u1 : 2 * sweepParam t ≤ 1 := by linarith
    have hrew : lam + (1 - 2 * lam) * (2 * sweepParam t)
        = (1 - 2 * sweepParam t) * lam + (2 * sweepParam t) * (1 - lam) := by ring
    rw [hrew]
    exact (sweepLoopChamfer_abs_convex_le h2u0 h2u1).trans (max_le hKlam hK1m)
  · -- the first chamfer: a convex combination of an arc point and a chord point
    have hlt : 1 / 2 < sweepParam t := lt_of_not_ge h1
    have hpos : 0 < lam := by linarith
    have hc0 : 0 ≤ (2 * sweepParam t - 1) / lam := div_nonneg (by linarith) hpos.le
    have hc1 : (2 * sweepParam t - 1) / lam ≤ 1 := by
      rw [div_le_one hpos]; linarith
    refine (sweepLoopChamfer_norm_smul_combo_le hc0 hc1 _ _).trans (max_le ?_ ?_)
    · exact (hArc _ hK1m).trans hC
    · exact hChord _ hK1m
  · -- the chord side: the profile value is a convex combination of `lam` and `1 - lam`
    have hgt : 1 / 2 + lam / 2 < sweepParam t := lt_of_not_ge h2
    have hden : 0 < 1 / 2 - lam := by linarith
    have hnum0 : 0 ≤ sweepParam t - (1 / 2 + lam / 2) := by linarith
    have hnum1 : sweepParam t - (1 / 2 + lam / 2) ≤ 1 / 2 - lam := by linarith
    have hc0 : 0 ≤ (sweepParam t - (1 / 2 + lam / 2)) / (1 / 2 - lam) :=
      div_nonneg hnum0 hden.le
    have hc1 : (sweepParam t - (1 / 2 + lam / 2)) / (1 / 2 - lam) ≤ 1 := by
      rw [div_le_one hden]; exact hnum1
    refine hChord _ ?_
    have hrew : (1 - lam) - ((sweepParam t - (1 / 2 + lam / 2)) / (1 / 2 - lam)) * (1 - 2 * lam)
        = (1 - (sweepParam t - (1 / 2 + lam / 2)) / (1 / 2 - lam)) * (1 - lam)
          + ((sweepParam t - (1 / 2 + lam / 2)) / (1 / 2 - lam)) * lam := by ring
    rw [hrew]
    exact (sweepLoopChamfer_abs_convex_le hc0 hc1).trans (max_le hK1m hKlam)
  · -- the second chamfer: a convex combination of a chord point and an arc point
    have hgt : 1 - lam / 2 < sweepParam t := lt_of_not_ge h3
    have hden : 0 < lam / 2 := by linarith
    have hc0 : 0 ≤ (sweepParam t - (1 - lam / 2)) / (lam / 2) :=
      div_nonneg (by linarith) hden.le
    have hc1 : (sweepParam t - (1 - lam / 2)) / (lam / 2) ≤ 1 := by
      rw [div_le_one hden]; linarith
    refine (sweepLoopChamfer_norm_smul_combo_le hc0 hc1 _ _).trans (max_le ?_ ?_)
    · exact hChord _ hKlam
    · exact (hArc _ hKlam).trans hC

/-! ## Local integrability -/

theorem sweepLoopChamfer_locallyIntegrable {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space} (hr : Continuous r)
    {d : LeanEval.KnotTheory.Quadrisecant.BandArcData} (D : Work.Drive.SweepData d) (lam : ℝ) :
    MeasureTheory.LocallyIntegrable (fun p : ℝ × ℝ => Work.Drive.sweepLoopChamfer r D lam p.1 p.2) MeasureTheory.volume := by
  -- the two branch lifts are bounded (their ranges are contained in the compact interval `I`)
  obtain ⟨A₀, hA₀⟩ := (isCompact_univ (X := I)).exists_bound_of_continuousOn D.cont_ta.continuousOn
  obtain ⟨B₀, hB₀⟩ := (isCompact_univ (X := I)).exists_bound_of_continuousOn D.cont_tb.continuousOn
  set A : ℝ := max A₀ B₀ with hAdef
  have hA : ∀ x : ℝ, |taR D x| ≤ A ∧ |tbR D x| ≤ A := by
    intro x
    constructor
    · refine le_trans ?_ (le_max_left A₀ B₀)
      simpa [taR, Real.norm_eq_abs] using hA₀ (clampI x) (Set.mem_univ _)
    · refine le_trans ?_ (le_max_right A₀ B₀)
      simpa [tbR, Real.norm_eq_abs] using hB₀ (clampI x) (Set.mem_univ _)
  -- the profile bound `K` and its two consequences for `lam`
  obtain ⟨K, hK0, hKlam, hK1m⟩ : ∃ K : ℝ, 0 ≤ K ∧ |lam| ≤ K ∧ |1 - lam| ≤ K :=
    ⟨|lam| + |1 - lam|, by positivity, by linarith [abs_nonneg (1 - lam)],
      by linarith [abs_nonneg lam]⟩
  -- the bound `R` for `r` on the interval where the loop evaluates it
  set R₀ : ℝ := A * (1 + 2 * K) with hR₀def
  obtain ⟨R₁, hR₁⟩ :=
    (isCompact_Icc (a := -|R₀|) (b := |R₀|)).exists_bound_of_continuousOn hr.continuousOn
  set R : ℝ := max R₁ 0 with hRdef
  have hR : ∀ x : ℝ, |x| ≤ A * (1 + 2 * K) → ‖r x‖ ≤ R := by
    intro x hx
    have hx2 : |x| ≤ |R₀| := le_trans hx (le_abs_self R₀)
    have hmem : x ∈ Set.Icc (-|R₀|) |R₀| := by
      rw [Set.mem_Icc]; exact abs_le.mp hx2
    exact le_trans (hR₁ x hmem) (le_max_left R₁ 0)
  have hbd : ∀ s t : ℝ, ‖sweepLoopChamfer r D lam s t‖ ≤ (2 * K + 1) * R :=
    sweepLoopChamfer_norm_bound D lam A K R hA hK0 hR hKlam hK1m
  have hR0 : 0 ≤ R := le_max_right R₁ 0
  have hC0 : 0 ≤ (2 * K + 1) * R := by nlinarith [hK0, hR0]
  refine (locallyIntegrable_const ((2 * K + 1) * R)).mono
    (sweepLoopChamfer_measurable D hr lam).aestronglyMeasurable ?_
  filter_upwards with p
  rw [Real.norm_of_nonneg hC0]
  exact hbd p.1 p.2

end Work.Drive
