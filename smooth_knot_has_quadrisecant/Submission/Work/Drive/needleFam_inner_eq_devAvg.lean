import Mathlib
import Submission.Work.Drive.needleProfileDefs
import Submission.Work.Drive.sweepLoopChamfer_locallyIntegrable
import Submission.Work.Drive.sweepBlurFacts

set_option maxHeartbeats 2000000

/-!
# The needle's deviation from its chord is the average of the loops' deviations

**NOTE ON THE STATEMENT (read this first).**  The statement was *requested* with `chordEndA r D ε`
and `chordEndB r D ε` (one real argument each).  That text is **not well-typed**:
`Work.Drive.chordEndA` is `def chordEndA (r) {d} (D : SweepData d) (δ₂ ε : ℝ) : Space`
(`needleProfileDefs.lean`), so `chordEndA r D ε : ℝ → Space` and the requested expression asks for
an `HSub Space (ℝ → Space)` instance (and later for an `Inner ℝ (ℝ → Space) Space`); Lean reports
`failed to synthesize instance ... HSub Space (ℝ → Space)`.  The missing explicit argument is
`δ₂` — the same one that occurs in `needleFam r D lam δ₁ δ₂ ε` and in the requester's own copy of
this identity at the end of `Submission/Work/Drive/needleProfileDeviation.lean`
(`chordEndA r D δ₂ ε`).  The theorem below is therefore stated with `chordEndA r D δ₂ ε` /
`chordEndB r D δ₂ ε` — the only reading of the request that elaborates — and is proved in full.


The needle `N = needleFam r D lam δ₁ δ₂ ε` is the double blur of the chamfered sweep loop.  On the
arc zone of the loop parameter, its deviation from its own chord (the segment between the two
`σ`-blurred endpoints `chordEndA`, `chordEndB` of `needleProfileDefs.lean`) is the double average of
the *loops'* deviations `loopDev`, evaluated at the same arc fractions `arcFrac lam δ₁ t u`:

    ⟪N t - chordEndA, e⟫
      = ∫ v, bump v * (∫ u, bump u * ⟪loopDev (ε - δ₂ v) (arcFrac lam δ₁ t u), e⟫)
        + (∫ u, bump u * arcFrac lam δ₁ t u) * ⟪chordEndB - chordEndA, e⟫ .

The proof is a sequence of elementary integral manipulations: the inner product commutes with the
two (interval) integrals, the loop parameter lies on the arc branch (`hzone`), and the retained arc
point is `loopDev` plus the point of the chord at the same fraction.
-/

noncomputable section
namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant MeasureTheory
open scoped Real Topology intervalIntegral

/-! ## Generic interval-integral helper lemmas -/

/-- The inner product `⟪e, ·⟫` commutes with an interval integral. -/
lemma inner_intervalIntegral_comm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {a b : ℝ} {f : ℝ → E} (hf : IntervalIntegrable f volume a b) (e : E) :
    inner ℝ e (∫ x in a..b, f x) = ∫ x in a..b, inner ℝ e (f x) := by
  have h := ContinuousLinearMap.intervalIntegral_comp_comm (L := innerSL ℝ e) (μ := volume) hf
  simp only [innerSL_apply_apply] at h
  rw [← h]

/-- The inner product `⟪·, e⟫` commutes with an interval integral. -/
lemma inner_intervalIntegral_comm_left {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {a b : ℝ} {f : ℝ → E} (hf : IntervalIntegrable f volume a b) (e : E) :
    inner ℝ (∫ x in a..b, f x) e = ∫ x in a..b, inner ℝ (f x) e := by
  rw [← real_inner_comm (∫ x in a..b, f x) e, inner_intervalIntegral_comm hf e]
  exact intervalIntegral.integral_congr (fun x _ => real_inner_comm (f x) e)

/-- A globally bounded measurable function is interval-integrable. -/
lemma intervalIntegrable_of_bounded {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E] {f : ℝ → E} {a b C : ℝ}
    (hm : Measurable f) (hC : ∀ x, ‖f x‖ ≤ C) : IntervalIntegrable f volume a b :=
  IntervalIntegrable.mono_fun' (g := fun _ : ℝ => C) (intervalIntegrable_const (c := C))
    (hm.aestronglyMeasurable.restrict) (Filter.Eventually.of_forall hC)

/-- A measurable function which is bounded on `[-1,1]` is interval-integrable on `[-1,1]`. -/
lemma intervalIntegrable_of_measurable_of_bound_Icc {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {f : ℝ → E} {C : ℝ}
    (hm : Measurable f) (hC : ∀ x ∈ Set.Icc (-1 : ℝ) 1, ‖f x‖ ≤ C) :
    IntervalIntegrable f volume (-1 : ℝ) 1 := by
  refine IntervalIntegrable.mono_fun' (g := fun _ : ℝ => C) (intervalIntegrable_const (c := C))
    (hm.aestronglyMeasurable.restrict) ?_
  refine (MeasureTheory.ae_restrict_mem measurableSet_uIoc).mono ?_
  intro x hx
  rw [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
  exact hC x (Set.Ioc_subset_Icc_self hx)

/-- The smoothing bump is bounded by `1`. -/
lemma sweepBump_le_one (u : ℝ) : sweepBump u ≤ 1 := by
  rw [sweepBump]
  calc Real.smoothTransition (1 + u) * Real.smoothTransition (1 - u) ≤ 1 * 1 :=
        mul_le_mul (Real.smoothTransition.le_one _) (Real.smoothTransition.le_one _)
          (Real.smoothTransition.nonneg _) (by norm_num)
    _ = 1 := by norm_num

/-- `bump · * w ·` is interval-integrable as soon as `w` is measurable and bounded on `[-1,1]`. -/
lemma intervalIntegrable_sweepBump_mul {w : ℝ → ℝ} (hm : Measurable w) {C : ℝ}
    (hC : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |w x| ≤ C) :
    IntervalIntegrable (fun u : ℝ => sweepBump u * w u) volume (-1 : ℝ) 1 := by
  refine intervalIntegrable_of_measurable_of_bound_Icc (C := C)
    (sweepBump_continuous.measurable.mul hm) ?_
  intro x hx
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sweepBump_nonneg x)]
  simpa using mul_le_mul (sweepBump_le_one x) (hC x hx) (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)

/-- Measurability of `a ↦ ⟪f a, e⟫`. -/
lemma measurable_inner_comp {α : Type*} [MeasurableSpace α] {f : α → Space} (hf : Measurable f)
    (e : Space) : Measurable (fun a : α => inner ℝ (f a) e) :=
  continuous_inner.measurable.comp (hf.prodMk measurable_const)

/-- The chamfered loop is on its arc branch when the loop parameter is at most `1/2`. -/
lemma sweepLoopChamfer_arcZone' {r : ℝ → Space} {d : BandArcData} (D : SweepData d)
    {lam s t : ℝ} (h : sweepParam t ≤ 1 / 2) :
    sweepLoopChamfer r D lam s t = sweepArc' r D s (lam + (1 - 2 * lam) * (2 * sweepParam t)) := by
  simp only [sweepLoopChamfer]
  rw [if_pos h]

/-! ## Bounds for the sweep loop and the retained arc -/

/-- The branch lifts `taR`, `tbR` are bounded (their ranges lie in the compact interval `I`). -/
lemma exists_abs_taR_tbR_le {d : BandArcData} (D : SweepData d) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ x : ℝ, |taR D x| ≤ A ∧ |tbR D x| ≤ A := by
  obtain ⟨Aa, hAa⟩ := IsCompact.exists_bound_of_continuousOn (s := Set.univ) isCompact_univ
    D.cont_ta.continuousOn
  obtain ⟨Ab, hAb⟩ := IsCompact.exists_bound_of_continuousOn (s := Set.univ) isCompact_univ
    D.cont_tb.continuousOn
  refine ⟨max (max Aa Ab) 0, le_max_right _ _, fun x => ⟨?_, ?_⟩⟩
  · have h := hAa (clampI x) (Set.mem_univ _)
    rw [Real.norm_eq_abs] at h
    exact h.trans (le_trans (le_max_left _ _) (le_max_left _ _))
  · have h := hAb (clampI x) (Set.mem_univ _)
    rw [Real.norm_eq_abs] at h
    exact h.trans (le_trans (le_max_right _ _) (le_max_left _ _))

/-- A continuous curve is bounded on a closed interval. -/
lemma exists_bound_r_Icc {r : ℝ → Space} (hr : Continuous r) {C : ℝ} (hC : 0 ≤ C) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ x : ℝ, |x| ≤ C → ‖r x‖ ≤ R := by
  obtain ⟨R, hR⟩ := IsCompact.exists_bound_of_continuousOn (s := Set.Icc (-C) C) isCompact_Icc
    hr.continuousOn
  exact ⟨max R 0, le_max_right _ _, fun x hx =>
    (hR x (by rw [Set.mem_Icc]; exact abs_le.mp hx)).trans (le_max_left _ _)⟩

/-- The arc fraction stays in the range of the two profile values `lam` and `1 - lam`. -/
lemma abs_arcFrac_le {lam δ₁ t : ℝ} {u : ℝ} (hu : u ∈ Set.Icc (-1 : ℝ) 1)
    (hzone : ∀ u : ℝ, u ∈ Set.Icc (-1 : ℝ) 1 → sweepParam (t - δ₁ * u) ≤ 1 / 2) :
    |arcFrac lam δ₁ t u| ≤ max |lam| |1 - lam| := by
  have h0 : 0 ≤ 2 * sweepParam (t - δ₁ * u) := by linarith [(sweepParam_mem (t - δ₁ * u)).1]
  have h1 : 2 * sweepParam (t - δ₁ * u) ≤ 1 := by linarith [hzone u hu]
  have hrw : arcFrac lam δ₁ t u
      = (1 - 2 * sweepParam (t - δ₁ * u)) * lam
        + (2 * sweepParam (t - δ₁ * u)) * (1 - lam) := by
    rw [arcFrac]; ring
  rw [hrw]
  exact sweepLoopChamfer_abs_convex_le h0 h1

/-- The deviation of a retained arc from its chord is bounded by twice the loop bound. -/
lemma norm_loopDev_le {r : ℝ → Space} {d : BandArcData} (D : SweepData d) {A K R : ℝ}
    (hA : ∀ x : ℝ, |taR D x| ≤ A ∧ |tbR D x| ≤ A) (hK0 : 0 ≤ K) (hR0 : 0 ≤ R)
    (hR : ∀ x : ℝ, |x| ≤ A * (1 + 2 * K) → ‖r x‖ ≤ R) :
    ∀ (s ξ : ℝ), |ξ| ≤ K → ‖loopDev r D s ξ‖ ≤ 2 * (2 * K + 1) * R := by
  intro s ξ hξ
  have ha := sweepLoopChamfer_sweepArc'_norm_le D hA hK0 hR s ξ hξ
  have hc := sweepLoopChamfer_sweepChord'_norm_le D hA hK0 hR0 hR s ξ hξ
  have hd : loopDev r D s ξ = sweepArc' r D s ξ - sweepChord' r D s ξ := rfl
  rw [hd]
  refine (norm_sub_le _ _).trans ?_
  calc ‖sweepArc' r D s ξ‖ + ‖sweepChord' r D s ξ‖ ≤ R + (2 * K + 1) * R := add_le_add ha hc
    _ = (2 * K + 2) * R := by ring
    _ ≤ (2 * (2 * K + 1)) * R := mul_le_mul_of_nonneg_right (by linarith) hR0
    _ = 2 * (2 * K + 1) * R := by ring

/-! ## Measurability of the pieces -/

/-- The arc fraction is measurable in the loop parameter. -/
lemma measurable_arcFrac (lam δ₁ t : ℝ) :
    Measurable (fun u : ℝ => arcFrac lam δ₁ t u) := by
  have hsp : Measurable (fun u : ℝ => sweepParam (t - δ₁ * u)) :=
    sweepLoopChamfer_sweepParam_measurable.comp (by fun_prop)
  have h2 : Measurable (fun u : ℝ => 2 * sweepParam (t - δ₁ * u)) :=
    measurable_const.mul hsp
  rw [show (fun u : ℝ => arcFrac lam δ₁ t u)
      = (fun u : ℝ => lam + (1 - 2 * lam) * (2 * sweepParam (t - δ₁ * u))) from rfl]
  exact measurable_const.add (measurable_const.mul h2)

/-- The deviation `loopDev` is measurable in the pair (sweep parameter, fraction). -/
lemma measurable_loopDev_pair {r : ℝ → Space} (hr : Continuous r) {d : BandArcData}
    (D : SweepData d) :
    Measurable (fun p : ℝ × ℝ => loopDev r D p.1 p.2) := by
  have hta : Measurable (fun p : ℝ × ℝ => taR D p.1) :=
    (sweepLoopChamfer_taR_continuous D).measurable.comp measurable_fst
  have htb : Measurable (fun p : ℝ × ℝ => tbR D p.1) :=
    (sweepLoopChamfer_tbR_continuous D).measurable.comp measurable_fst
  have hw : Measurable (fun p : ℝ × ℝ => sweepW' D p.1) :=
    (sweepLoopChamfer_sweepW'_continuous D).measurable.comp measurable_fst
  rw [show (fun p : ℝ × ℝ => loopDev r D p.1 p.2)
      = (fun p : ℝ × ℝ => r (taR D p.1 + p.2 * sweepW' D p.1)
          - ((1 - p.2) • r (taR D p.1) + p.2 • r (tbR D p.1))) from rfl]
  exact (hr.measurable.comp (hta.add (measurable_snd.mul hw))).sub
    (((measurable_const.sub measurable_snd).smul (hr.measurable.comp hta)).add
      (measurable_snd.smul (hr.measurable.comp htb)))

/-- The composed deviation `(s,u) ↦ loopDev r D (ε - δ₂ s) (arcFrac lam δ₁ t u)`. -/
lemma measurable_loopDev_pair_eps {r : ℝ → Space} (hr : Continuous r) {d : BandArcData}
    (D : SweepData d) (lam δ₁ δ₂ ε t : ℝ) :
    Measurable (fun p : ℝ × ℝ => loopDev r D (ε - δ₂ * p.1) (arcFrac lam δ₁ t p.2)) :=
  (measurable_loopDev_pair hr D).comp
    ((measurable_const.sub (measurable_const.mul measurable_fst)).prodMk
      ((measurable_arcFrac lam δ₁ t).comp measurable_snd))

/-- `sweepSmoothT` is strongly measurable in the sweep parameter. -/
lemma stronglyMeasurable_sweepSmoothT_sigma {r : ℝ → Space} (hr : Continuous r)
    {d : BandArcData} (D : SweepData d) (lam δ₁ t : ℝ) :
    StronglyMeasurable (fun σ : ℝ => sweepSmoothT r D lam δ₁ σ t) := by
  have hunc : StronglyMeasurable (Function.uncurry (fun σ u : ℝ =>
      sweepBump u • sweepLoopChamfer r D lam σ (t - δ₁ * u))) := by
    show StronglyMeasurable (fun p : ℝ × ℝ =>
      sweepBump p.2 • sweepLoopChamfer r D lam p.1 (t - δ₁ * p.2))
    have h1 : Measurable (fun p : ℝ × ℝ => sweepBump p.2) :=
      sweepBump_continuous.measurable.comp measurable_snd
    have h2 : Measurable (fun p : ℝ × ℝ => sweepLoopChamfer r D lam p.1 (t - δ₁ * p.2)) :=
      (sweepLoopChamfer_measurable D hr lam).comp
        (measurable_fst.prodMk (by fun_prop : Measurable (fun p : ℝ × ℝ => t - δ₁ * p.2)))
    exact (h1.smul h2).stronglyMeasurable
  have hint : StronglyMeasurable (fun σ : ℝ => ∫ u,
      sweepBump u • sweepLoopChamfer r D lam σ (t - δ₁ * u)
        ∂(volume.restrict (Set.uIoc (-1 : ℝ) 1))) :=
    hunc.integral_prod_right
  have heq : (fun σ : ℝ => ∫ u, sweepBump u • sweepLoopChamfer r D lam σ (t - δ₁ * u)
        ∂(volume.restrict (Set.uIoc (-1 : ℝ) 1)))
      = (fun σ : ℝ => sweepSmoothT r D lam δ₁ σ t) := by
    funext σ
    rw [sweepSmoothT, intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
      Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  rw [heq] at hint
  exact hint

/-! ## The per-parameter inner identity on the arc zone -/

/-- **The single blur of the loop, on its arc zone.**  If the whole loop-parameter window of the
inner convolution lies on the arc branch (`hzone`), then `⟪sweepSmoothT … v t, e⟫` is the average
of the retained arcs' deviations from their chords, plus the corresponding average of the chord's
endpoints. -/
lemma sweepSmoothT_inner_arcZone {r : ℝ → Space} (hr : Continuous r) {d : BandArcData}
    (D : SweepData d) {lam δ₁ t : ℝ}
    (hzone : ∀ u : ℝ, u ∈ Set.Icc (-1 : ℝ) 1 → sweepParam (t - δ₁ * u) ≤ 1 / 2)
    (v : ℝ) (e : Space) :
    inner ℝ (sweepSmoothT r D lam δ₁ v t) e
      = (∫ u in (-1 : ℝ)..1, sweepBump u * inner ℝ (loopDev r D v (arcFrac lam δ₁ t u)) e)
        + (1 - ∫ u in (-1 : ℝ)..1, sweepBump u * arcFrac lam δ₁ t u) * inner ℝ (r (taR D v)) e
        + (∫ u in (-1 : ℝ)..1, sweepBump u * arcFrac lam δ₁ t u) * inner ℝ (r (tbR D v)) e := by
  obtain ⟨A, hA0, hA⟩ := exists_abs_taR_tbR_le D
  set K : ℝ := max |lam| |1 - lam| with hK
  have hK0 : 0 ≤ K := by rw [hK]; exact le_trans (abs_nonneg lam) (le_max_left _ _)
  have hKlam : |lam| ≤ K := by rw [hK]; exact le_max_left _ _
  have hK1m : |1 - lam| ≤ K := by rw [hK]; exact le_max_right _ _
  obtain ⟨R, hR0, hR⟩ := exists_bound_r_Icc (r := r) hr (C := A * (1 + 2 * K))
    (by nlinarith [hA0, hK0])
  have hloop : ∀ s t' : ℝ, ‖sweepLoopChamfer r D lam s t'‖ ≤ (2 * K + 1) * R :=
    sweepLoopChamfer_norm_bound D lam A K R hA hK0 hR hKlam hK1m
  set M : ℝ := (2 * (2 * K + 1) + (1 + K)) * R * ‖e‖ with hM
  have hM1 : 2 * (2 * K + 1) * R * ‖e‖ ≤ M := by
    rw [hM]
    have hle : 2 * (2 * K + 1) ≤ 2 * (2 * K + 1) + (1 + K) := by linarith
    calc 2 * (2 * K + 1) * R * ‖e‖ = (2 * (2 * K + 1)) * (R * ‖e‖) := by ring
      _ ≤ (2 * (2 * K + 1) + (1 + K)) * (R * ‖e‖) :=
          mul_le_mul_of_nonneg_right hle (mul_nonneg hR0 (norm_nonneg e))
      _ = (2 * (2 * K + 1) + (1 + K)) * R * ‖e‖ := by ring
  have hM3 : K * R * ‖e‖ ≤ M := by
    rw [hM]
    have hle : K ≤ 2 * (2 * K + 1) + (1 + K) := by linarith
    calc K * R * ‖e‖ = K * (R * ‖e‖) := by ring
      _ ≤ (2 * (2 * K + 1) + (1 + K)) * (R * ‖e‖) :=
          mul_le_mul_of_nonneg_right hle (mul_nonneg hR0 (norm_nonneg e))
      _ = (2 * (2 * K + 1) + (1 + K)) * R * ‖e‖ := by ring
  have hM4 : (1 + 2 * K) * R * ‖e‖ ≤ M := by
    rw [hM]
    have hle : 1 + 2 * K ≤ 2 * (2 * K + 1) + (1 + K) := by linarith
    calc (1 + 2 * K) * R * ‖e‖ = (1 + 2 * K) * (R * ‖e‖) := by ring
      _ ≤ (2 * (2 * K + 1) + (1 + K)) * (R * ‖e‖) :=
          mul_le_mul_of_nonneg_right hle (mul_nonneg hR0 (norm_nonneg e))
      _ = (2 * (2 * K + 1) + (1 + K)) * R * ‖e‖ := by ring
  have hξabs : ∀ u ∈ Set.Icc (-1 : ℝ) 1, |arcFrac lam δ₁ t u| ≤ K := by
    intro u hu
    rw [hK]
    exact abs_arcFrac_le hu hzone
  have hcp : |inner ℝ (r (taR D v)) e| ≤ R * ‖e‖ := by
    calc |inner ℝ (r (taR D v)) e| ≤ ‖r (taR D v)‖ * ‖e‖ := by
          rw [← Real.norm_eq_abs]; exact norm_inner_le_norm _ _
      _ ≤ R * ‖e‖ := mul_le_mul_of_nonneg_right
          (hR _ (le_trans (hA v).1 (by nlinarith [hA0, hK0]))) (norm_nonneg e)
  have hcq : |inner ℝ (r (tbR D v)) e| ≤ R * ‖e‖ := by
    calc |inner ℝ (r (tbR D v)) e| ≤ ‖r (tbR D v)‖ * ‖e‖ := by
          rw [← Real.norm_eq_abs]; exact norm_inner_le_norm _ _
      _ ≤ R * ‖e‖ := mul_le_mul_of_nonneg_right
          (hR _ (le_trans (hA v).2 (by nlinarith [hA0, hK0]))) (norm_nonneg e)
  -- the inner integral
  have hInt : IntervalIntegrable (fun u : ℝ =>
      sweepBump u • sweepLoopChamfer r D lam v (t - δ₁ * u)) volume (-1 : ℝ) 1 := by
    refine intervalIntegrable_of_bounded (C := (2 * K + 1) * R) ?_ ?_
    · exact (sweepBump_continuous.measurable).smul
        ((sweepLoopChamfer_measurable D hr lam).comp
          (measurable_const.prodMk (by fun_prop : Measurable (fun u : ℝ => t - δ₁ * u))))
    · intro u
      rw [norm_smul, Real.norm_of_nonneg (sweepBump_nonneg u)]
      have h : sweepBump u * ‖sweepLoopChamfer r D lam v (t - δ₁ * u)‖
          ≤ 1 * ((2 * K + 1) * R) :=
        mul_le_mul (sweepBump_le_one u) (hloop v (t - δ₁ * u)) (norm_nonneg _)
          (by norm_num : (0 : ℝ) ≤ 1)
      simpa using h
  have step1 : inner ℝ (sweepSmoothT r D lam δ₁ v t) e
      = ∫ u in (-1 : ℝ)..1,
          inner ℝ (sweepBump u • sweepLoopChamfer r D lam v (t - δ₁ * u)) e := by
    rw [sweepSmoothT, inner_intervalIntegral_comm_left hInt e]
  have step2 : (∫ u in (-1 : ℝ)..1,
        inner ℝ (sweepBump u • sweepLoopChamfer r D lam v (t - δ₁ * u)) e)
      = ∫ u in (-1 : ℝ)..1, sweepBump u *
          (inner ℝ (loopDev r D v (arcFrac lam δ₁ t u)) e
            + ((1 - arcFrac lam δ₁ t u) * inner ℝ (r (taR D v)) e
              + arcFrac lam δ₁ t u * inner ℝ (r (tbR D v)) e)) := by
    refine intervalIntegral.integral_congr (fun u hu => ?_)
    have huI : u ∈ Set.Icc (-1 : ℝ) 1 := by
      rwa [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hu
    have hdev : sweepArc' r D v (arcFrac lam δ₁ t u)
        = loopDev r D v (arcFrac lam δ₁ t u) + sweepChord' r D v (arcFrac lam δ₁ t u) := by
      rw [loopDev, sweepChord']; abel
    have harc : sweepLoopChamfer r D lam v (t - δ₁ * u)
        = sweepArc' r D v (arcFrac lam δ₁ t u) := by
      rw [sweepLoopChamfer_arcZone' D (hzone u huI)]
      rfl
    rw [harc, real_inner_smul_left, hdev, inner_add_left,
      sweepChord', inner_add_left, real_inner_smul_left, real_inner_smul_left]
  -- integrability of the pieces
  have hf1 : IntervalIntegrable (fun u : ℝ =>
      sweepBump u * inner ℝ (loopDev r D v (arcFrac lam δ₁ t u)) e) volume (-1 : ℝ) 1 := by
    refine intervalIntegrable_sweepBump_mul (C := M) ?_ ?_
    · exact measurable_inner_comp ((measurable_loopDev_pair hr D).comp
        (measurable_const.prodMk (measurable_arcFrac lam δ₁ t))) e
    · intro x hx
      calc |inner ℝ (loopDev r D v (arcFrac lam δ₁ t x)) e|
          ≤ ‖loopDev r D v (arcFrac lam δ₁ t x)‖ * ‖e‖ := by
            rw [← Real.norm_eq_abs]; exact norm_inner_le_norm _ _
        _ ≤ 2 * (2 * K + 1) * R * ‖e‖ := mul_le_mul_of_nonneg_right
            (norm_loopDev_le D hA hK0 hR0 hR v _ (hξabs x hx)) (norm_nonneg e)
        _ ≤ M := hM1
  have hf21 : IntervalIntegrable (fun u : ℝ =>
      sweepBump u * ((1 - arcFrac lam δ₁ t u) * inner ℝ (r (taR D v)) e)) volume (-1 : ℝ) 1 := by
    refine intervalIntegrable_sweepBump_mul (C := M) ?_ ?_
    · exact (measurable_const.sub (measurable_arcFrac lam δ₁ t)).mul measurable_const
    · intro x hx
      calc |(1 - arcFrac lam δ₁ t x) * inner ℝ (r (taR D v)) e|
          ≤ |1 - arcFrac lam δ₁ t x| * |inner ℝ (r (taR D v)) e| := by rw [abs_mul]
        _ ≤ (1 + K) * (R * ‖e‖) := by
            refine mul_le_mul ?_ hcp (abs_nonneg _) (by linarith [hK0])
            calc |1 - arcFrac lam δ₁ t x| ≤ 1 + |arcFrac lam δ₁ t x| := by
                  have h := abs_add_le (1 : ℝ) (-(arcFrac lam δ₁ t x))
                  rw [abs_neg] at h
                  simpa [sub_eq_add_neg] using h
              _ ≤ 1 + K := by linarith [hξabs x hx]
        _ ≤ M := by
            have h := hM4
            nlinarith [h, hK0, hR0, norm_nonneg e]
  have hf22 : IntervalIntegrable (fun u : ℝ =>
      sweepBump u * (arcFrac lam δ₁ t u * inner ℝ (r (tbR D v)) e)) volume (-1 : ℝ) 1 := by
    refine intervalIntegrable_sweepBump_mul (C := M) ?_ ?_
    · exact (measurable_arcFrac lam δ₁ t).mul measurable_const
    · intro x hx
      calc |arcFrac lam δ₁ t x * inner ℝ (r (tbR D v)) e|
          ≤ |arcFrac lam δ₁ t x| * |inner ℝ (r (tbR D v)) e| := by rw [abs_mul]
        _ ≤ K * (R * ‖e‖) := mul_le_mul (hξabs x hx) hcq (abs_nonneg _) hK0
        _ ≤ M := by
            have h := hM3
            nlinarith [h, hK0, hR0, norm_nonneg e]
  have hf2 : IntervalIntegrable (fun u : ℝ => sweepBump u *
      ((1 - arcFrac lam δ₁ t u) * inner ℝ (r (taR D v)) e
        + arcFrac lam δ₁ t u * inner ℝ (r (tbR D v)) e)) volume (-1 : ℝ) 1 := by
    refine intervalIntegrable_sweepBump_mul (C := M) ?_ ?_
    · exact ((measurable_const.sub (measurable_arcFrac lam δ₁ t)).mul measurable_const).add
        ((measurable_arcFrac lam δ₁ t).mul measurable_const)
    · intro x hx
      calc |(1 - arcFrac lam δ₁ t x) * inner ℝ (r (taR D v)) e
              + arcFrac lam δ₁ t x * inner ℝ (r (tbR D v)) e|
          ≤ |(1 - arcFrac lam δ₁ t x) * inner ℝ (r (taR D v)) e|
            + |arcFrac lam δ₁ t x * inner ℝ (r (tbR D v)) e| := abs_add_le _ _
        _ ≤ (1 + K) * (R * ‖e‖) + K * (R * ‖e‖) := by
            refine add_le_add ?_ ?_
            · rw [abs_mul]
              refine mul_le_mul ?_ hcp (abs_nonneg _) (by linarith [hK0])
              calc |1 - arcFrac lam δ₁ t x| ≤ 1 + |arcFrac lam δ₁ t x| := by
                    have h := abs_add_le (1 : ℝ) (-(arcFrac lam δ₁ t x))
                    rw [abs_neg] at h
                    simpa [sub_eq_add_neg] using h
                _ ≤ 1 + K := by linarith [hξabs x hx]
            · rw [abs_mul]
              exact mul_le_mul (hξabs x hx) hcq (abs_nonneg _) hK0
        _ ≤ M := by
            have h := hM4
            nlinarith [h, hK0, hR0, norm_nonneg e]
  have hbpx : IntervalIntegrable (fun u : ℝ => sweepBump u * arcFrac lam δ₁ t u)
      volume (-1 : ℝ) 1 :=
    intervalIntegrable_sweepBump_mul (measurable_arcFrac lam δ₁ t) (fun x hx => hξabs x hx)
  have hbpc : IntervalIntegrable sweepBump volume (-1 : ℝ) 1 :=
    sweepBump_continuous.intervalIntegrable _ _
  -- the splits
  have split1 : (∫ u in (-1 : ℝ)..1, sweepBump u *
        (inner ℝ (loopDev r D v (arcFrac lam δ₁ t u)) e
          + ((1 - arcFrac lam δ₁ t u) * inner ℝ (r (taR D v)) e
            + arcFrac lam δ₁ t u * inner ℝ (r (tbR D v)) e)))
      = (∫ u in (-1 : ℝ)..1, sweepBump u * inner ℝ (loopDev r D v (arcFrac lam δ₁ t u)) e)
        + ∫ u in (-1 : ℝ)..1, sweepBump u *
            ((1 - arcFrac lam δ₁ t u) * inner ℝ (r (taR D v)) e
              + arcFrac lam δ₁ t u * inner ℝ (r (tbR D v)) e) := by
    rw [← intervalIntegral.integral_add hf1 hf2]
    exact intervalIntegral.integral_congr (fun u _ => by ring)
  have split2 : (∫ u in (-1 : ℝ)..1, sweepBump u *
        ((1 - arcFrac lam δ₁ t u) * inner ℝ (r (taR D v)) e
          + arcFrac lam δ₁ t u * inner ℝ (r (tbR D v)) e))
      = (∫ u in (-1 : ℝ)..1, sweepBump u *
            ((1 - arcFrac lam δ₁ t u) * inner ℝ (r (taR D v)) e))
        + (∫ u in (-1 : ℝ)..1, sweepBump u *
            (arcFrac lam δ₁ t u * inner ℝ (r (tbR D v)) e)) := by
    rw [← intervalIntegral.integral_add hf21 hf22]
    exact intervalIntegral.integral_congr (fun u _ => by ring)
  have pull1 : (∫ u in (-1 : ℝ)..1, sweepBump u *
        ((1 - arcFrac lam δ₁ t u) * inner ℝ (r (taR D v)) e))
      = (∫ u in (-1 : ℝ)..1, sweepBump u * (1 - arcFrac lam δ₁ t u))
        * inner ℝ (r (taR D v)) e := by
    rw [show (fun u : ℝ => sweepBump u * ((1 - arcFrac lam δ₁ t u) * inner ℝ (r (taR D v)) e))
        = (fun u : ℝ => (sweepBump u * (1 - arcFrac lam δ₁ t u)) * inner ℝ (r (taR D v)) e)
        from by funext u; ring]
    rw [intervalIntegral.integral_mul_const]
  have pull2 : (∫ u in (-1 : ℝ)..1, sweepBump u *
        (arcFrac lam δ₁ t u * inner ℝ (r (tbR D v)) e))
      = (∫ u in (-1 : ℝ)..1, sweepBump u * arcFrac lam δ₁ t u)
        * inner ℝ (r (tbR D v)) e := by
    rw [show (fun u : ℝ => sweepBump u * (arcFrac lam δ₁ t u * inner ℝ (r (tbR D v)) e))
        = (fun u : ℝ => (sweepBump u * arcFrac lam δ₁ t u) * inner ℝ (r (tbR D v)) e)
        from by funext u; ring]
    rw [intervalIntegral.integral_mul_const]
  have bpc : (∫ u in (-1 : ℝ)..1, sweepBump u * (1 - arcFrac lam δ₁ t u))
      = 1 - (∫ u in (-1 : ℝ)..1, sweepBump u * arcFrac lam δ₁ t u) := by
    rw [show (fun u : ℝ => sweepBump u * (1 - arcFrac lam δ₁ t u))
        = (fun u : ℝ => sweepBump u - sweepBump u * arcFrac lam δ₁ t u) from by
      funext u; ring]
    rw [intervalIntegral.integral_sub hbpc hbpx, integral_sweepBump]
  rw [step1, step2, split1, split2, pull1, pull2, bpc]
  ring

/-! ## The target -/

/-- **The needle's deviation from its chord is the average of the loops' deviations.** -/
theorem needleFam_inner_eq_devAvg {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr : Continuous r) {d : LeanEval.KnotTheory.Quadrisecant.BandArcData} (D : Work.Drive.SweepData d)
    {lam δ₁ δ₂ ε t : ℝ} (hlam1 : lam < 1 / 2)
    (hzone : ∀ u : ℝ, u ∈ Set.Icc (-1 : ℝ) 1 → Work.Drive.sweepParam (t - δ₁ * u) ≤ 1 / 2)
    {e : LeanEval.KnotTheory.Quadrisecant.Space} :
    inner ℝ (Work.Drive.needleFam r D lam δ₁ δ₂ ε t - Work.Drive.chordEndA r D δ₂ ε) e
      = (∫ v in (-1 : ℝ)..1, Work.Drive.sweepBump v * (∫ u in (-1 : ℝ)..1, Work.Drive.sweepBump u *
            inner ℝ (Work.Drive.loopDev r D (ε - δ₂ * v) (Work.Drive.arcFrac lam δ₁ t u)) e))
        + (∫ u in (-1 : ℝ)..1, Work.Drive.sweepBump u * Work.Drive.arcFrac lam δ₁ t u) *
            inner ℝ (Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε) e := by
  obtain ⟨A, hA0, hA⟩ := exists_abs_taR_tbR_le D
  set K : ℝ := max |lam| |1 - lam| with hK
  have hK0 : 0 ≤ K := by rw [hK]; exact le_trans (abs_nonneg lam) (le_max_left _ _)
  have hKlam : |lam| ≤ K := by rw [hK]; exact le_max_left _ _
  have hK1m : |1 - lam| ≤ K := by rw [hK]; exact le_max_right _ _
  obtain ⟨R, hR0, hR⟩ := exists_bound_r_Icc (r := r) hr (C := A * (1 + 2 * K))
    (by nlinarith [hA0, hK0])
  have hr_le : ∀ y : ℝ, |y| ≤ A → ‖r y‖ ≤ R := fun y hy =>
    hR y (le_trans hy (by nlinarith [hA0, hK0]))
  have hcp_le : ∀ v : ℝ, |inner ℝ (r (taR D (ε - δ₂ * v))) e| ≤ R * ‖e‖ := by
    intro v
    calc |inner ℝ (r (taR D (ε - δ₂ * v))) e| ≤ ‖r (taR D (ε - δ₂ * v))‖ * ‖e‖ := by
          rw [← Real.norm_eq_abs]; exact norm_inner_le_norm _ _
      _ ≤ R * ‖e‖ := mul_le_mul_of_nonneg_right (hr_le _ (hA _).1) (norm_nonneg e)
  have hcq_le : ∀ v : ℝ, |inner ℝ (r (tbR D (ε - δ₂ * v))) e| ≤ R * ‖e‖ := by
    intro v
    calc |inner ℝ (r (tbR D (ε - δ₂ * v))) e| ≤ ‖r (tbR D (ε - δ₂ * v))‖ * ‖e‖ := by
          rw [← Real.norm_eq_abs]; exact norm_inner_le_norm _ _
      _ ≤ R * ‖e‖ := mul_le_mul_of_nonneg_right (hr_le _ (hA _).2) (norm_nonneg e)
  have hdev_bound : ∀ v u : ℝ, u ∈ Set.Icc (-1 : ℝ) 1 →
      |inner ℝ (loopDev r D (ε - δ₂ * v) (arcFrac lam δ₁ t u)) e| ≤ 2 * (2 * K + 1) * R * ‖e‖ := by
    intro v u hu
    calc |inner ℝ (loopDev r D (ε - δ₂ * v) (arcFrac lam δ₁ t u)) e|
        ≤ ‖loopDev r D (ε - δ₂ * v) (arcFrac lam δ₁ t u)‖ * ‖e‖ := by
          rw [← Real.norm_eq_abs]; exact norm_inner_le_norm _ _
      _ ≤ 2 * (2 * K + 1) * R * ‖e‖ := mul_le_mul_of_nonneg_right
          (norm_loopDev_le D hA hK0 hR0 hR _ _ (abs_arcFrac_le hu hzone)) (norm_nonneg e)
  -- the average `G` of the loops' deviations
  set G : ℝ → ℝ := fun v => ∫ u in (-1 : ℝ)..1, sweepBump u *
      inner ℝ (loopDev r D (ε - δ₂ * v) (arcFrac lam δ₁ t u)) e with hG
  have hGval : ∀ v : ℝ, G v = ∫ u in (-1 : ℝ)..1, sweepBump u *
      inner ℝ (loopDev r D (ε - δ₂ * v) (arcFrac lam δ₁ t u)) e := by
    intro v
    simp only [hG]
  have hGmeas : Measurable G := by
    have huncurry : Measurable (fun p : ℝ × ℝ => sweepBump p.2 *
        inner ℝ (loopDev r D (ε - δ₂ * p.1) (arcFrac lam δ₁ t p.2)) e) := by
      refine (sweepBump_continuous.measurable.comp measurable_snd).mul ?_
      exact measurable_inner_comp (measurable_loopDev_pair_eps hr D lam δ₁ δ₂ ε t) e
    have hint : StronglyMeasurable (fun v : ℝ => ∫ u, sweepBump u *
        inner ℝ (loopDev r D (ε - δ₂ * v) (arcFrac lam δ₁ t u)) e
          ∂(volume.restrict (Set.uIoc (-1 : ℝ) 1))) :=
      (StronglyMeasurable.integral_prod_right
        (f := fun v u : ℝ => sweepBump u *
          inner ℝ (loopDev r D (ε - δ₂ * v) (arcFrac lam δ₁ t u)) e)
        (ν := volume.restrict (Set.uIoc (-1 : ℝ) 1)) huncurry.stronglyMeasurable)
    have heq : (fun v : ℝ => ∫ u, sweepBump u *
          inner ℝ (loopDev r D (ε - δ₂ * v) (arcFrac lam δ₁ t u)) e
            ∂(volume.restrict (Set.uIoc (-1 : ℝ) 1))) = G := by
      funext v
      rw [hGval v, intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
        Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    rw [heq] at hint
    exact hint.measurable
  have hGbound : ∀ v : ℝ, |G v| ≤ 2 * (2 * K + 1) * R * ‖e‖ := by
    intro v
    rw [hGval v, ← Real.norm_eq_abs]
    refine (intervalIntegral.norm_integral_le_integral_norm (by norm_num : (-1 : ℝ) ≤ 1)).trans ?_
    have h1 : IntervalIntegrable (fun u : ℝ => ‖sweepBump u *
        inner ℝ (loopDev r D (ε - δ₂ * v) (arcFrac lam δ₁ t u)) e‖) volume (-1 : ℝ) 1 :=
      (intervalIntegrable_sweepBump_mul (measurable_inner_comp
        ((measurable_loopDev_pair hr D).comp (measurable_const.prodMk
          (measurable_arcFrac lam δ₁ t))) e) (hdev_bound v)).norm
    have h2 : IntervalIntegrable (fun u : ℝ => sweepBump u * (2 * (2 * K + 1) * R * ‖e‖))
        volume (-1 : ℝ) 1 :=
      (sweepBump_continuous.mul continuous_const).intervalIntegrable _ _
    refine (intervalIntegral.integral_mono_on (by norm_num) h1 h2 ?_).trans ?_
    · intro u hu
      rw [norm_mul, Real.norm_of_nonneg (sweepBump_nonneg u)]
      exact mul_le_mul_of_nonneg_left (hdev_bound v u hu) (sweepBump_nonneg u)
    · rw [intervalIntegral.integral_mul_const, integral_sweepBump, one_mul]
  -- the scalar quantities
  set A0 : ℝ := ∫ u in (-1 : ℝ)..1, sweepBump u * arcFrac lam δ₁ t u with hA0
  set Ca : ℝ := ∫ v in (-1 : ℝ)..1, sweepBump v * inner ℝ (r (taR D (ε - δ₂ * v))) e with hCa
  set Cb : ℝ := ∫ v in (-1 : ℝ)..1, sweepBump v * inner ℝ (r (tbR D (ε - δ₂ * v))) e with hCb
  -- the v-integrability facts
  have hSmeas : Measurable (fun v : ℝ => sweepSmoothT r D lam δ₁ (ε - δ₂ * v) t) :=
    (stronglyMeasurable_sweepSmoothT_sigma hr D lam δ₁ t).measurable.comp (by fun_prop)
  have hSbound : ∀ v : ℝ, ‖sweepSmoothT r D lam δ₁ (ε - δ₂ * v) t‖ ≤ (2 * K + 1) * R := by
    intro v
    rw [sweepSmoothT]
    refine (intervalIntegral.norm_integral_le_integral_norm (by norm_num : (-1 : ℝ) ≤ 1)).trans ?_
    have hnorm : ∀ u : ℝ,
        ‖sweepBump u • sweepLoopChamfer r D lam (ε - δ₂ * v) (t - δ₁ * u)‖
          ≤ sweepBump u * ((2 * K + 1) * R) := by
      intro u
      rw [norm_smul, Real.norm_of_nonneg (sweepBump_nonneg u)]
      exact mul_le_mul_of_nonneg_left
        (sweepLoopChamfer_norm_bound D lam A K R hA hK0 hR hKlam hK1m _ _)
        (sweepBump_nonneg u)
    have h1 : IntervalIntegrable (fun u : ℝ =>
        ‖sweepBump u • sweepLoopChamfer r D lam (ε - δ₂ * v) (t - δ₁ * u)‖)
        volume (-1 : ℝ) 1 := by
      refine (intervalIntegrable_of_bounded (C := (2 * K + 1) * R) ?_ ?_).norm
      · exact (sweepBump_continuous.measurable).smul
          ((sweepLoopChamfer_measurable D hr lam).comp
            (measurable_const.prodMk (by fun_prop : Measurable (fun u : ℝ => t - δ₁ * u))))
      · intro u
        rw [norm_smul, Real.norm_of_nonneg (sweepBump_nonneg u)]
        have h : sweepBump u * ‖sweepLoopChamfer r D lam (ε - δ₂ * v) (t - δ₁ * u)‖
            ≤ 1 * ((2 * K + 1) * R) :=
          mul_le_mul (sweepBump_le_one u)
            (sweepLoopChamfer_norm_bound D lam A K R hA hK0 hR hKlam hK1m (ε - δ₂ * v)
              (t - δ₁ * u))
            (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
        simpa using h
    have h2 : IntervalIntegrable (fun u : ℝ => sweepBump u * ((2 * K + 1) * R))
        volume (-1 : ℝ) 1 :=
      (sweepBump_continuous.mul continuous_const).intervalIntegrable _ _
    refine (intervalIntegral.integral_mono_on (by norm_num) h1 h2 (fun u _ => hnorm u)).trans ?_
    rw [intervalIntegral.integral_mul_const, integral_sweepBump, one_mul]
  have hSInt : IntervalIntegrable (fun v : ℝ => sweepBump v • sweepSmoothT r D lam δ₁ (ε - δ₂ * v) t)
      volume (-1 : ℝ) 1 := by
    refine intervalIntegrable_of_bounded (C := (2 * K + 1) * R)
      ((sweepBump_continuous.measurable).smul hSmeas) ?_
    intro v
    rw [norm_smul, Real.norm_of_nonneg (sweepBump_nonneg v)]
    have h : sweepBump v * ‖sweepSmoothT r D lam δ₁ (ε - δ₂ * v) t‖ ≤ 1 * ((2 * K + 1) * R) :=
      mul_le_mul (sweepBump_le_one v) (hSbound v) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    simpa using h
  have hPInt : IntervalIntegrable (fun v : ℝ => sweepBump v • r (taR D (ε - δ₂ * v)))
      volume (-1 : ℝ) 1 := by
    refine intervalIntegrable_of_bounded (C := R) ((sweepBump_continuous.measurable).smul
      (hr.measurable.comp ((sweepLoopChamfer_taR_continuous D).measurable.comp
        (by fun_prop : Measurable (fun v : ℝ => ε - δ₂ * v))))) ?_
    intro v
    rw [norm_smul, Real.norm_of_nonneg (sweepBump_nonneg v)]
    have h : sweepBump v * ‖r (taR D (ε - δ₂ * v))‖ ≤ 1 * R :=
      mul_le_mul (sweepBump_le_one v) (hr_le _ (hA _).1) (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
    simpa using h
  have hQInt : IntervalIntegrable (fun v : ℝ => sweepBump v • r (tbR D (ε - δ₂ * v)))
      volume (-1 : ℝ) 1 := by
    refine intervalIntegrable_of_bounded (C := R) ((sweepBump_continuous.measurable).smul
      (hr.measurable.comp ((sweepLoopChamfer_tbR_continuous D).measurable.comp
        (by fun_prop : Measurable (fun v : ℝ => ε - δ₂ * v))))) ?_
    intro v
    rw [norm_smul, Real.norm_of_nonneg (sweepBump_nonneg v)]
    have h : sweepBump v * ‖r (tbR D (ε - δ₂ * v))‖ ≤ 1 * R :=
      mul_le_mul (sweepBump_le_one v) (hr_le _ (hA _).2) (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
    simpa using h
  -- the commutations
  have hSS : inner ℝ (∫ v in (-1 : ℝ)..1, sweepBump v •
        sweepSmoothT r D lam δ₁ (ε - δ₂ * v) t) e
      = ∫ v in (-1 : ℝ)..1, sweepBump v * inner ℝ (sweepSmoothT r D lam δ₁ (ε - δ₂ * v) t) e := by
    rw [inner_intervalIntegral_comm_left hSInt e]
    exact intervalIntegral.integral_congr (fun x _ => by rw [real_inner_smul_left])
  have hPP : inner ℝ (∫ v in (-1 : ℝ)..1, sweepBump v • r (taR D (ε - δ₂ * v))) e = Ca := by
    have hint : (∫ v in (-1 : ℝ)..1, inner ℝ (sweepBump v • r (taR D (ε - δ₂ * v))) e)
        = ∫ v in (-1 : ℝ)..1, sweepBump v * inner ℝ (r (taR D (ε - δ₂ * v))) e :=
      intervalIntegral.integral_congr (fun x _ => by rw [real_inner_smul_left])
    rw [inner_intervalIntegral_comm_left hPInt e, hint, ← hCa]
  have hQQ : inner ℝ (∫ v in (-1 : ℝ)..1, sweepBump v • r (tbR D (ε - δ₂ * v))) e = Cb := by
    have hint : (∫ v in (-1 : ℝ)..1, inner ℝ (sweepBump v • r (tbR D (ε - δ₂ * v))) e)
        = ∫ v in (-1 : ℝ)..1, sweepBump v * inner ℝ (r (tbR D (ε - δ₂ * v))) e :=
      intervalIntegral.integral_congr (fun x _ => by rw [real_inner_smul_left])
    rw [inner_intervalIntegral_comm_left hQInt e, hint, ← hCb]
  have hCB : inner ℝ (chordEndB r D δ₂ ε - chordEndA r D δ₂ ε) e = Cb - Ca := by
    simp only [chordEndB, chordEndA, inner_sub_left]
    rw [hQQ, hPP]
  -- the u-side identity
  have hSval : (∫ v in (-1 : ℝ)..1, sweepBump v *
        inner ℝ (sweepSmoothT r D lam δ₁ (ε - δ₂ * v) t) e)
      = ∫ v in (-1 : ℝ)..1, sweepBump v *
          (G v + (1 - A0) * inner ℝ (r (taR D (ε - δ₂ * v))) e
            + A0 * inner ℝ (r (tbR D (ε - δ₂ * v))) e) := by
    refine intervalIntegral.integral_congr (fun v _ => ?_)
    rw [hGval v, hA0, sweepSmoothT_inner_arcZone hr D hzone (ε - δ₂ * v) e]
  -- the v-side splits
  have hGInt : IntervalIntegrable (fun v : ℝ => sweepBump v * G v) volume (-1 : ℝ) 1 :=
    intervalIntegrable_sweepBump_mul hGmeas (fun x _ => hGbound x)
  have h2Int0 : IntervalIntegrable (fun v : ℝ =>
      sweepBump v * ((1 - A0) * inner ℝ (r (taR D (ε - δ₂ * v))) e)) volume (-1 : ℝ) 1 := by
    refine intervalIntegrable_sweepBump_mul (C := |1 - A0| * (R * ‖e‖))
      (measurable_const.mul (measurable_inner_comp ?_ e)) ?_
    · exact hr.measurable.comp ((sweepLoopChamfer_taR_continuous D).measurable.comp (by fun_prop))
    · intro x hx
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hcp_le x) (abs_nonneg _)
  have h2Int : IntervalIntegrable (fun v : ℝ =>
      (1 - A0) * (sweepBump v * inner ℝ (r (taR D (ε - δ₂ * v))) e)) volume (-1 : ℝ) 1 :=
    h2Int0.congr (fun v _ => by ring)
  have h3Int0 : IntervalIntegrable (fun v : ℝ =>
      sweepBump v * (A0 * inner ℝ (r (tbR D (ε - δ₂ * v))) e)) volume (-1 : ℝ) 1 := by
    refine intervalIntegrable_sweepBump_mul (C := |A0| * (R * ‖e‖))
      (measurable_const.mul (measurable_inner_comp ?_ e)) ?_
    · exact hr.measurable.comp ((sweepLoopChamfer_tbR_continuous D).measurable.comp (by fun_prop))
    · intro x hx
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hcq_le x) (abs_nonneg _)
  have h3Int : IntervalIntegrable (fun v : ℝ =>
      A0 * (sweepBump v * inner ℝ (r (tbR D (ε - δ₂ * v))) e)) volume (-1 : ℝ) 1 :=
    h3Int0.congr (fun v _ => by ring)
  have hsplit : (∫ v in (-1 : ℝ)..1, sweepBump v *
        (G v + (1 - A0) * inner ℝ (r (taR D (ε - δ₂ * v))) e
          + A0 * inner ℝ (r (tbR D (ε - δ₂ * v))) e))
      = (∫ v in (-1 : ℝ)..1, sweepBump v * G v) + (1 - A0) * Ca + A0 * Cb := by
    have hdist : (∫ v in (-1 : ℝ)..1, sweepBump v *
          (G v + (1 - A0) * inner ℝ (r (taR D (ε - δ₂ * v))) e
            + A0 * inner ℝ (r (tbR D (ε - δ₂ * v))) e))
        = ∫ v in (-1 : ℝ)..1, (sweepBump v * G v
            + ((1 - A0) * (sweepBump v * inner ℝ (r (taR D (ε - δ₂ * v))) e)
              + A0 * (sweepBump v * inner ℝ (r (tbR D (ε - δ₂ * v))) e))) :=
      intervalIntegral.integral_congr (fun v _ => by ring)
    rw [hdist, intervalIntegral.integral_add hGInt (h2Int.add h3Int),
      intervalIntegral.integral_add h2Int h3Int,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      ← hCa, ← hCb]
    ring
  -- the final assembly
  have hL : inner ℝ (needleFam r D lam δ₁ δ₂ ε t - chordEndA r D δ₂ ε) e
      = inner ℝ (∫ v in (-1 : ℝ)..1, sweepBump v •
          sweepSmoothT r D lam δ₁ (ε - δ₂ * v) t) e
        - inner ℝ (∫ v in (-1 : ℝ)..1, sweepBump v • r (taR D (ε - δ₂ * v))) e := by
    simp only [needleFam, sweepFam, chordEndA, inner_sub_left]
  have hmain : inner ℝ (needleFam r D lam δ₁ δ₂ ε t - chordEndA r D δ₂ ε) e
      = (∫ v in (-1 : ℝ)..1, sweepBump v * G v)
        + A0 * inner ℝ (chordEndB r D δ₂ ε - chordEndA r D δ₂ ε) e := by
    rw [hL, hSS, hSval, hsplit, hPP, hCB]
    ring
  rw [hmain]

end Work.Drive
