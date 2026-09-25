import Mathlib
import Submission.Commons.Analysis.MeasureTheory.marcinkiewicz_weak_one_strong_two_banach

/-!
# Marcinkiewicz interpolation: weak `(q,q)` + strong `(∞,∞)` implies strong `(p,p)`

For `q ≥ 1`, a Banach space `E`, and an additive operator `T : (α → E) → (β → E)` which is
weak-type `(q,q)` with constant `A₀` and strong-type `(∞,∞)` with constant `A₁`, the operator is
strong-type `(p,p)` for every `p > q`.

The proof is the standard truncation argument.  At level `λ > 0` the function is split as
`f = f·1_{‖f‖ ≤ λ/(2A₁)} + f·1_{‖f‖ > λ/(2A₁)}`; the strong `(∞,∞)` hypothesis kills the
distribution of the "good" part at level `λ/2`, while the weak `(q,q)` hypothesis controls the
`L^q` size of the "bad" part.  Integrating the resulting pointwise-in-`λ` bound against
`p λ^{p-1} dλ` and evaluating the resulting two-dimensional integral gives the constant
`C = (p (2A₀)^q (2A₁)^{p-q} / (p-q))^{1/p}`.
-/

open MeasureTheory Measure Filter Set
open scoped ENNReal Topology

namespace Commons.Analysis.MeasureTheory

/-! ## Elementary `ℝ≥0∞` lemmas -/

/-- Applying an indicator commutes with a positive real power. -/
lemma indicator_rpow {α : Type*} (W : α → ℝ≥0∞) (s : Set α) {r : ℝ} (hr : 0 < r) (x : α) :
    (Set.indicator s W x) ^ r = Set.indicator s (fun x => (W x) ^ r) x := by
  by_cases h : x ∈ s
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, ENNReal.zero_rpow_of_pos hr]

/-- The two ways of writing the indicator of the level set `{y | t/(2c) < W y}` at the point `x`. -/
lemma indicator_cross {α : Type*} (W F : α → ℝ≥0∞) (c : ℝ) (x : α) (t : ℝ) :
    Set.indicator {y : α | ENNReal.ofReal (t / (2*c)) < W y} F x
      = Set.indicator {t' : ℝ | ENNReal.ofReal (t' / (2*c)) < W x} (fun _ => (1:ℝ≥0∞)) t * F x := by
  by_cases h : ENNReal.ofReal (t / (2*c)) < W x
  · rw [Set.indicator_of_mem (show x ∈ {y : α | ENNReal.ofReal (t / (2*c)) < W y} from h),
        Set.indicator_of_mem (show t ∈ {t' : ℝ | ENNReal.ofReal (t' / (2*c)) < W x} from h),
        one_mul]
  · rw [Set.indicator_of_notMem (show x ∉ {y : α | ENNReal.ofReal (t / (2*c)) < W y} from h),
        Set.indicator_of_notMem (show t ∉ {t' : ℝ | ENNReal.ofReal (t' / (2*c)) < W x} from h),
        zero_mul]

/-- Fubini/Tonelli swap for the level-set integral appearing in the truncation argument. -/
lemma swap_lintegral_rpow {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]
    {W F : α → ℝ≥0∞} (hW : Measurable W) (hF : Measurable F) {c : ℝ}
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ t in Set.Ioi (0:ℝ),
        f t * (∫⁻ x, Set.indicator {x : α | ENNReal.ofReal (t / (2*c)) < W x} F x ∂μ)
      = ∫⁻ x, F x * (∫⁻ t in Set.Ioi (0:ℝ), f t *
          Set.indicator {t : ℝ | ENNReal.ofReal (t / (2*c)) < W x} (fun _ => (1:ℝ≥0∞)) t) ∂μ := by
  have hstep1 : ∫⁻ t in Set.Ioi (0:ℝ),
        f t * (∫⁻ x, Set.indicator {x : α | ENNReal.ofReal (t / (2*c)) < W x} F x ∂μ)
      = ∫⁻ t in Set.Ioi (0:ℝ), ∫⁻ x,
          f t * Set.indicator {x : α | ENNReal.ofReal (t / (2*c)) < W x} F x ∂μ := by
    apply lintegral_congr; intro t
    exact (lintegral_const_mul (f t) (hF.indicator (measurableSet_lt measurable_const hW))).symm
  rw [hstep1]
  have hjoint : AEMeasurable (Function.uncurry fun t x =>
        f t * Set.indicator {x : α | ENNReal.ofReal (t / (2*c)) < W x} F x)
      ((volume.restrict (Set.Ioi (0:ℝ))).prod μ) := by
    refine AEMeasurable.mul (hf.comp measurable_fst).aemeasurable ?_
    refine Measurable.aemeasurable ?_
    refine Measurable.indicator (hF.comp measurable_snd) ?_
    exact measurableSet_lt ((measurable_fst.div_const (2*c)).ennreal_ofReal)
      (hW.comp measurable_snd)
  rw [lintegral_lintegral_swap hjoint]
  apply lintegral_congr; intro x
  calc ∫⁻ t in Set.Ioi (0:ℝ),
        f t * Set.indicator {y : α | ENNReal.ofReal (t / (2*c)) < W y} F x
      = ∫⁻ t in Set.Ioi (0:ℝ), f t *
          Set.indicator {t' : ℝ | ENNReal.ofReal (t' / (2*c)) < W x} (fun _ => (1:ℝ≥0∞)) t * F x := by
        apply lintegral_congr; intro t
        rw [indicator_cross W F c x t]; ring
    _ = F x * ∫⁻ t in Set.Ioi (0:ℝ), f t *
          Set.indicator {t' : ℝ | ENNReal.ofReal (t' / (2*c)) < W x} (fun _ => (1:ℝ≥0∞)) t :=
        (lintegral_mul_const (F x) (hf.mul (((measurable_const (a := (1:ℝ≥0∞))).indicator
          (measurableSet_lt ((measurable_id.div_const (2*c)).ennreal_ofReal)
            measurable_const))))).trans (mul_comm _ _)

/-- The elementary integral `∫_0^∞ t^r · 1_{t/(2c) < b} dt = (2cb)^{r+1}/(r+1)`. -/
lemma lintegral_Ioi_rpow_indicator_scale {b c r : ℝ} (hb : 0 ≤ b) (hc : 0 < c) (hr : -1 < r) :
    ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (t ^ r) *
        Set.indicator {t : ℝ | ENNReal.ofReal (t / (2*c)) < ENNReal.ofReal b}
          (fun _ => (1:ℝ≥0∞)) t
      = ENNReal.ofReal ((2*c*b) ^ (r + 1) / (r + 1)) := by
  have hcongr : ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (t ^ r) *
        Set.indicator {t : ℝ | ENNReal.ofReal (t / (2*c)) < ENNReal.ofReal b}
          (fun _ => (1:ℝ≥0∞)) t
      = ∫⁻ t in Set.Ioi (0:ℝ),
          Set.indicator (Set.Ioo (0:ℝ) (2*c*b)) (fun t => ENNReal.ofReal (t ^ r)) t := by
    refine lintegral_congr_ae ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ht
    have h2c : (0:ℝ) < 2*c := by positivity
    have hiff : (ENNReal.ofReal (t / (2*c)) < ENNReal.ofReal b) ↔ t / (2*c) < b :=
      ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)
    have hiff2 : t / (2*c) < b ↔ t < 2*c*b := by
      rw [div_lt_iff₀ h2c]; ring_nf
    by_cases hb' : t < 2*c*b
    · rw [Set.indicator_of_mem (show t ∈ {t : ℝ | ENNReal.ofReal (t / (2*c)) < ENNReal.ofReal b}
          from hiff.mpr (hiff2.mpr hb')),
        Set.indicator_of_mem (show t ∈ Set.Ioo (0:ℝ) (2*c*b) from ⟨ht0, hb'⟩), mul_one]
    · rw [Set.indicator_of_notMem (show t ∉ {t : ℝ | ENNReal.ofReal (t / (2*c)) < ENNReal.ofReal b}
          from fun h => hb' (hiff2.mp (hiff.mp h))),
        Set.indicator_of_notMem (show t ∉ Set.Ioo (0:ℝ) (2*c*b) from fun h => hb' h.2), mul_zero]
  rw [hcongr, lintegral_Ioi_indicator_eq measurableSet_Ioo (fun t ht => ht.1),
      lintegral_Ioo_ofReal_rpow hr (by positivity)]

/-- Rewriting `(2cb)^{r+1}/(r+1)` as a product of the constant and `b^{r+1}`. -/
lemma ofReal_rpow_div_mul_rpow {b c r : ℝ} (hb : 0 ≤ b) (hc : 0 < c) (hr : -1 < r) :
    ENNReal.ofReal ((2*c*b) ^ (r + 1) / (r + 1))
      = ENNReal.ofReal ((2*c) ^ (r + 1) / (r + 1)) * (ENNReal.ofReal b) ^ (r + 1) := by
  have hr1 : (0:ℝ) ≤ r + 1 := by linarith
  have h2c : (0:ℝ) ≤ 2*c := by positivity
  rw [ENNReal.ofReal_rpow_of_nonneg hb hr1, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [Real.mul_rpow h2c hb]
  ring

/-! ## The two-dimensional integral -/

/-- Combination of the Tonelli swap and the elementary one-dimensional integral: the full
"truncation" integral evaluates to the expected `L^p` norm of `v`. -/
lemma key_lintegral {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]
    {v : α → ℝ} (hvm : Measurable v) (hv : ∀ x, 0 ≤ v x)
    {c : ℝ} (hc : 0 < c) {q r : ℝ} (hq : 0 ≤ q) (hr : -1 < r) :
    ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (t ^ r) *
        (∫⁻ x, Set.indicator {x : α | ENNReal.ofReal (t / (2*c)) < ENNReal.ofReal (v x)}
            (fun x => ENNReal.ofReal (v x) ^ q) x ∂μ)
      = ENNReal.ofReal ((2*c) ^ (r + 1) / (r + 1)) *
          ∫⁻ x, ENNReal.ofReal (v x) ^ (q + r + 1) ∂μ := by
  have hW : Measurable fun x : α => ENNReal.ofReal (v x) := hvm.ennreal_ofReal
  have hF : Measurable fun x : α => ENNReal.ofReal (v x) ^ q :=
    ENNReal.continuous_rpow_const.measurable.comp hW
  have hf : Measurable fun t : ℝ => ENNReal.ofReal (t ^ r) := (measurable_rpow_const r).ennreal_ofReal
  rw [swap_lintegral_rpow hW hF hf]
  have hinner : ∀ x : α, ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (t ^ r) *
        Set.indicator {t : ℝ | ENNReal.ofReal (t / (2*c)) < ENNReal.ofReal (v x)}
          (fun _ => (1:ℝ≥0∞)) t
      = ENNReal.ofReal ((2*c) ^ (r + 1) / (r + 1)) * (ENNReal.ofReal (v x)) ^ (r + 1) := by
    intro x
    rw [lintegral_Ioi_rpow_indicator_scale (hv x) hc hr, ofReal_rpow_div_mul_rpow (hv x) hc hr]
  simp_rw [hinner]
  rw [show (∫⁻ x, ENNReal.ofReal (v x) ^ q *
        (ENNReal.ofReal ((2*c) ^ (r + 1) / (r + 1)) * (ENNReal.ofReal (v x)) ^ (r + 1)) ∂μ)
      = ∫⁻ x, ENNReal.ofReal ((2*c) ^ (r + 1) / (r + 1)) * (ENNReal.ofReal (v x)) ^ (q + r + 1) ∂μ from by
        apply lintegral_congr; intro x
        rw [show (ENNReal.ofReal (v x)) ^ (q + r + 1)
              = (ENNReal.ofReal (v x)) ^ q * (ENNReal.ofReal (v x)) ^ (r + 1) from by
              rw [show q + r + 1 = q + (r + 1) by ring,
                ENNReal.rpow_add_of_nonneg q (r + 1) hq (by linarith)]]
        ring]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-! ## The level-set bound -/

/-- The truncated level-set bound: the tail of `T f` at level `lam` is controlled by the weak
`(q,q)` bound applied to the part of `f` above the level `lam/(2A₁)`. -/
lemma lvl_set_q
    {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : MeasureTheory.Measure α} {ν : MeasureTheory.Measure β}
    (T : (α → E) → (β → E))
    (hadd : ∀ f g : α → E, T (f + g) = T f + T g)
    {q A0 A1 : ℝ} (hq : 0 < q) (hA1 : 0 < A1)
    (hweak : ∀ (f : α → E) (lam : ℝ), 0 < lam →
        ν {x : β | lam < ‖T f x‖} ≤ ENNReal.ofReal (A0 / lam) ^ q *
          (MeasureTheory.eLpNorm f (ENNReal.ofReal q) μ) ^ q)
    (hstrong : ∀ f : α → E,
        MeasureTheory.eLpNorm (T f) ⊤ ν ≤ ENNReal.ofReal A1 * MeasureTheory.eLpNorm f ⊤ μ)
    (f : α → E) (hf : AEStronglyMeasurable f μ) {lam : ℝ} (hlam : 0 < lam) :
    ν {x : β | lam < ‖T f x‖} ≤
      ENNReal.ofReal (2 * A0 / lam) ^ q *
        ∫⁻ x, Set.indicator {x : α | ENNReal.ofReal (lam / (2 * A1)) < ENNReal.ofReal ‖f x‖}
          (fun x => ENNReal.ofReal ‖f x‖ ^ q) x ∂μ := by
  have hc_nonneg : 0 ≤ lam / (2 * A1) := by positivity
  set S : Set α := {x : α | ENNReal.ofReal (lam / (2 * A1)) < ENNReal.ofReal ‖f x‖} with hS
  set h : α → E := S.indicator f with hh
  set g : α → E := Sᶜ.indicator f with hg
  have hgh : g + h = f := by
    rw [hg, hh, add_comm]
    exact banach_indicator_add_compl f
  have hSm : NullMeasurableSet S μ :=
    nullMeasurableSet_lt aemeasurable_const hf.norm.aemeasurable.ennreal_ofReal
  have hgm : AEStronglyMeasurable g μ := hf.indicator₀ hSm.compl
  have hhm : AEStronglyMeasurable h μ := hf.indicator₀ hSm
  have hg_linf : MeasureTheory.eLpNorm g ⊤ μ ≤ ENNReal.ofReal (lam / (2 * A1)) := by
    rw [MeasureTheory.eLpNorm_exponent_top hgm]
    refine MeasureTheory.eLpNormEssSup_le_of_ae_bound (Eventually.of_forall fun x => ?_)
    rw [hg]
    by_cases hx : x ∈ Sᶜ
    · rw [Set.indicator_of_mem hx]
      have hxS : x ∉ S := by simpa using hx
      rw [hS] at hxS
      simp only [Set.mem_ofPred_eq, not_lt] at hxS
      exact (ENNReal.ofReal_le_ofReal_iff hc_nonneg).mp hxS
    · rw [Set.indicator_of_notMem hx, norm_zero]
      exact hc_nonneg
  have hg_bound : MeasureTheory.eLpNorm (T g) ⊤ ν ≤ ENNReal.ofReal (lam / 2) := by
    calc MeasureTheory.eLpNorm (T g) ⊤ ν
        ≤ ENNReal.ofReal A1 * MeasureTheory.eLpNorm g ⊤ μ := hstrong g
      _ ≤ ENNReal.ofReal A1 * ENNReal.ofReal (lam / (2 * A1)) :=
          mul_le_mul_of_nonneg_left hg_linf bot_le
      _ = ENNReal.ofReal (lam / 2) := by
          rw [← ENNReal.ofReal_mul hA1.le]
          congr 1
          field_simp
  have hgood_zero : ν {x : β | ENNReal.ofReal (lam / 2) < ‖T g x‖ₑ} = 0 := by
    have hsup : essSup (fun x => ‖T g x‖ₑ) ν ≤ ENNReal.ofReal (lam / 2) := by
      rw [← MeasureTheory.eLpNormEssSup_eq_essSup_enorm]
      exact MeasureTheory.eLpNormEssSup_le_eLpNorm_top.trans hg_bound
    have hae : ∀ᵐ x ∂ν, ‖T g x‖ₑ ≤ ENNReal.ofReal (lam / 2) :=
      (ENNReal.ae_le_essSup (fun x => ‖T g x‖ₑ)).mono (fun x hx => hx.trans hsup)
    have hae' := MeasureTheory.ae_iff.mp hae
    simpa only [not_le] using hae'
  have hsubset : {x : β | lam < ‖T f x‖} ⊆
      {x : β | ENNReal.ofReal (lam / 2) < ‖T g x‖ₑ} ∪
        {x : β | ENNReal.ofReal (lam / 2) < ‖T h x‖ₑ} := by
    intro x hx
    simp only [Set.mem_ofPred_eq, Set.mem_union] at hx ⊢
    have hx' : ENNReal.ofReal lam < ‖T f x‖ₑ := by
      simpa only [ofReal_norm] using (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hlam.le).mpr hx
    by_contra hcon
    rw [not_or] at hcon
    push Not at hcon
    have hsum : ‖T f x‖ₑ ≤ ‖T g x‖ₑ + ‖T h x‖ₑ := by
      conv_lhs => rw [← hgh, hadd g h]
      exact enorm_add_le _ _
    have hle : ‖T f x‖ₑ ≤ ENNReal.ofReal (lam / 2) + ENNReal.ofReal (lam / 2) :=
      hsum.trans (add_le_add hcon.1 hcon.2)
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      show lam / 2 + lam / 2 = lam by ring] at hle
    exact absurd hle (not_le.mpr hx')
  have hHeq : (MeasureTheory.eLpNorm h (ENNReal.ofReal q) μ) ^ q
      = ∫⁻ x, Set.indicator S (fun x => ENNReal.ofReal ‖f x‖ ^ q) x ∂μ := by
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (p := ENNReal.ofReal q)
        (ENNReal.ofReal_pos.mpr hq).ne' ENNReal.ofReal_ne_top hhm, ENNReal.toReal_ofReal hq.le]
    rw [← ENNReal.rpow_mul, show (1 / q) * q = 1 by field_simp, ENNReal.rpow_one]
    refine lintegral_congr fun x => ?_
    rw [hh, enorm_indicator_eq_indicator_enorm, indicator_rpow (fun x => ‖f x‖ₑ) S hq x]
    simp only [← ofReal_norm]
  calc ν {x : β | lam < ‖T f x‖}
      ≤ ν ({x : β | ENNReal.ofReal (lam / 2) < ‖T g x‖ₑ} ∪
            {x : β | ENNReal.ofReal (lam / 2) < ‖T h x‖ₑ}) := measure_mono hsubset
    _ ≤ ν {x : β | ENNReal.ofReal (lam / 2) < ‖T g x‖ₑ} +
          ν {x : β | ENNReal.ofReal (lam / 2) < ‖T h x‖ₑ} := measure_union_le _ _
    _ = ν {x : β | ENNReal.ofReal (lam / 2) < ‖T h x‖ₑ} := by rw [hgood_zero, zero_add]
    _ = ν {x : β | lam / 2 < ‖T h x‖} := by
        congr 1
        ext x
        rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, ← ofReal_norm]
        exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)
    _ ≤ ENNReal.ofReal (A0 / (lam / 2)) ^ q *
          (MeasureTheory.eLpNorm h (ENNReal.ofReal q) μ) ^ q := hweak h (lam / 2) (by positivity)
    _ = ENNReal.ofReal (2 * A0 / lam) ^ q *
          (MeasureTheory.eLpNorm h (ENNReal.ofReal q) μ) ^ q := by
        rw [show A0 / (lam / 2) = 2 * A0 / lam by field_simp]
    _ = ENNReal.ofReal (2 * A0 / lam) ^ q *
          ∫⁻ x, Set.indicator {x : α | ENNReal.ofReal (lam / (2 * A1)) < ENNReal.ofReal ‖f x‖}
            (fun x => ENNReal.ofReal ‖f x‖ ^ q) x ∂μ := by
        rw [hHeq]


/-! ## The main theorem -/

/-- Under the weak `(q,q)` and strong `(∞,∞)` hypotheses, `T f` is a.e. strongly measurable for
every `f ∈ L^p` with `p > q`: the bounded truncations of `f` have a.e. strongly measurable images
(finite `L^∞` norm), and they converge to `T f` in measure by the weak `(q,q)` bound applied to
the unbounded parts, whose `L^q` norms tend to `0`. -/
lemma wq_aestronglyMeasurable_T
    {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup E] [MeasurableSpace E]
    {μ : MeasureTheory.Measure α} {ν : MeasureTheory.Measure β}
    (T : (α → E) → (β → E))
    (hadd : ∀ f g : α → E, T (f + g) = T f + T g)
    {q A0 A1 : ℝ} (hq0 : 0 < q)
    (hweak : ∀ (f : α → E) (lam : ℝ), 0 < lam →
      ν {x : β | lam < ‖T f x‖}
        ≤ ENNReal.ofReal (A0 / lam) ^ q * (MeasureTheory.eLpNorm f (ENNReal.ofReal q) μ) ^ q)
    (hstrong : ∀ f : α → E,
      MeasureTheory.eLpNorm (T f) ⊤ ν ≤ ENNReal.ofReal A1 * MeasureTheory.eLpNorm f ⊤ μ)
    {p : ℝ} (hp : q < p) {f : α → E} (hfm : AEStronglyMeasurable f μ)
    (hfin : eLpNorm f (ENNReal.ofReal p) μ ≠ ∞) :
    AEStronglyMeasurable (T f) ν := by
  have hp0 : 0 < p := lt_trans hq0 hp
  set I : ℝ≥0∞ := ∫⁻ x, ‖f x‖ₑ ^ p ∂μ with hI
  have hIfin : I ≠ ∞ := by
    have h := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (p := ENNReal.ofReal p)
      (ENNReal.ofReal_pos.mpr hp0).ne' ENNReal.ofReal_ne_top (lt_top_iff_ne_top.mpr hfin)
    rw [ENNReal.toReal_ofReal hp0.le] at h
    exact h.ne
  set c : ℕ → ℝ := fun n => (n:ℝ) + 1 with hcdef
  have hc : ∀ n, 0 < c n := fun n => by positivity
  set S : ℕ → Set α := fun n => {x | ENNReal.ofReal (c n) < ‖f x‖ₑ} with hSdef
  have hS : ∀ n, NullMeasurableSet (S n) μ := fun n =>
    nullMeasurableSet_lt aemeasurable_const hfm.enorm
  set h : ℕ → α → E := fun n => (S n).indicator f with hhdef
  set g : ℕ → α → E := fun n => (S n)ᶜ.indicator f with hgdef
  have hsplit : ∀ n, T f = T (g n) + T (h n) := fun n => by
    rw [← hadd, add_comm]; exact congrArg T (banach_indicator_add_compl f).symm
  have hfp : ∀ x, ‖f x‖ₑ ^ p = ENNReal.ofReal (‖f x‖ ^ p) := fun x => by
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le]
  -- the bounded parts
  have hTg : ∀ n, AEStronglyMeasurable (T (g n)) ν := by
    intro n
    have hgm : AEStronglyMeasurable (g n) μ := hfm.indicator₀ (hS n).compl
    have hinf : eLpNorm (g n) ⊤ μ ≤ ENNReal.ofReal (c n) := by
      rw [eLpNorm_exponent_top hgm]
      refine eLpNormEssSup_le_of_ae_bound (Eventually.of_forall fun x => ?_)
      by_cases hx : x ∈ S n
      · have hgx : g n x = 0 := Set.indicator_of_notMem (by simpa using hx) f
        rw [hgx, norm_zero]; exact (hc n).le
      · have hgx : g n x = f x := Set.indicator_of_mem (by simpa using hx) f
        rw [hgx]
        have hx' : ¬ ENNReal.ofReal (c n) < ENNReal.ofReal ‖f x‖ := by
          rw [ofReal_norm]; exact hx
        rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg (hc n).le, not_lt] at hx'
        exact hx'
    refine aestronglyMeasurable_of_eLpNorm_ne_top (p := ⊤) (ne_of_lt ?_)
    exact (hstrong (g n)).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (hinf.trans_lt ENNReal.ofReal_lt_top))
  -- the unbounded parts are small in `L^q`
  have hsmall : ∀ n x, ‖h n x‖ₑ ^ q ≤ ENNReal.ofReal (c n ^ (q - p)) * ‖f x‖ₑ ^ p := by
    intro n x
    by_cases hx : x ∈ S n
    · have hhx : h n x = f x := Set.indicator_of_mem hx f
      rw [hhx, hfp, ← ENNReal.ofReal_mul (Real.rpow_nonneg (hc n).le _), ← ofReal_norm,
        ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hq0.le]
      apply ENNReal.ofReal_le_ofReal
      have hlt : c n < ‖f x‖ := by
        have hx' : ENNReal.ofReal (c n) < ENNReal.ofReal ‖f x‖ := by
          rw [ofReal_norm]; exact hx
        exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (hc n).le).1 hx'
      have hpos : 0 < ‖f x‖ := (hc n).trans hlt
      calc ‖f x‖ ^ q = ‖f x‖ ^ (q - p) * ‖f x‖ ^ p := by
            rw [← Real.rpow_add hpos, show q - p + p = q by ring]
        _ ≤ c n ^ (q - p) * ‖f x‖ ^ p := by
            apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (norm_nonneg _) _)
            exact Real.rpow_le_rpow_of_nonpos (hc n) hlt.le (by linarith)
    · have hhx : h n x = 0 := Set.indicator_of_notMem hx f
      rw [hhx, enorm_zero, ENNReal.zero_rpow_of_pos hq0]
      exact zero_le
  have hhq : ∀ n, eLpNorm (h n) (ENNReal.ofReal q) μ ^ q ≤ ENNReal.ofReal (c n ^ (q - p)) * I := by
    intro n
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (p := ENNReal.ofReal q)
        (ENNReal.ofReal_pos.mpr hq0).ne' ENNReal.ofReal_ne_top (hfm.indicator₀ (hS n)),
      ENNReal.toReal_ofReal hq0.le, ← ENNReal.rpow_mul, show (1 / q) * q = 1 by field_simp,
      ENNReal.rpow_one]
    calc ∫⁻ x, ‖h n x‖ₑ ^ q ∂μ ≤ ∫⁻ x, ENNReal.ofReal (c n ^ (q - p)) * ‖f x‖ₑ ^ p ∂μ :=
          lintegral_mono fun x => hsmall n x
      _ = ENNReal.ofReal (c n ^ (q - p)) * I := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hclim : Tendsto (fun n => ENNReal.ofReal (c n ^ (q - p)) * I) atTop (𝓝 0) := by
    have h1 : Tendsto c atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun n => c n ^ (q - p)) atTop (𝓝 0) := by
      have := (tendsto_rpow_neg_atTop (show 0 < p - q by linarith)).comp h1
      refine this.congr fun n => ?_
      simp only [Function.comp, neg_sub]
    have h3 : Tendsto (fun n => ENNReal.ofReal (c n ^ (q - p))) atTop (𝓝 0) := by
      simpa using ENNReal.tendsto_ofReal h2
    simpa using ENNReal.Tendsto.mul_const h3 (Or.inr hIfin)
  have hconv : TendstoInMeasure ν (fun n => T (g n)) atTop (T f) := by
    refine tendstoInMeasure_of_ne_top fun ε hε hεtop => ?_
    have hεr : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεtop
    have hbound : ∀ n, ν {x | ε ≤ edist (T (g n) x) (T f x)}
        ≤ ENNReal.ofReal (A0 / (ε.toReal / 2)) ^ q * (ENNReal.ofReal (c n ^ (q - p)) * I) := by
      intro n
      refine le_trans (measure_mono ?_) ((hweak (h n) (ε.toReal / 2) (by positivity)).trans
        (mul_le_mul_right (hhq n) _))
      intro x hx
      simp only [Set.mem_setOf_eq] at hx ⊢
      rw [hsplit n, Pi.add_apply, edist_eq_enorm_sub, show T (g n) x - (T (g n) x + T (h n) x)
        = -T (h n) x by abel, enorm_neg, ← ofReal_norm] at hx
      have := ENNReal.toReal_le_of_le_ofReal (norm_nonneg _) hx
      linarith
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
      (fun n => zero_le) hbound
    simpa using ENNReal.Tendsto.const_mul hclim
      (Or.inr (ENNReal.rpow_ne_top_of_nonneg hq0.le ENNReal.ofReal_ne_top))
  obtain ⟨ns, -, hns⟩ := hconv.exists_seq_tendsto_ae
  exact aestronglyMeasurable_of_tendsto_ae atTop (fun i => hTg (ns i)) hns

theorem marcinkiewicz_weak_q_strong_p_top
    {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    {μ : MeasureTheory.Measure α} [MeasureTheory.SFinite μ] {ν : MeasureTheory.Measure β}
    (T : (α → E) → (β → E))
    (hadd : ∀ f g : α → E, T (f + g) = T f + T g)
    (hmeas : ∀ f : α → E, AEMeasurable (T f) ν)
    {q A0 A1 : ℝ} (hq : 1 ≤ q) (hA0 : 0 < A0) (hA1 : 0 < A1)
    (hweak : ∀ (f : α → E) (lam : ℝ), 0 < lam →
      ν {x : β | lam < ‖T f x‖}
        ≤ ENNReal.ofReal (A0 / lam) ^ q * (MeasureTheory.eLpNorm f (ENNReal.ofReal q) μ) ^ q)
    (hstrong : ∀ f : α → E,
      MeasureTheory.eLpNorm (T f) ⊤ ν ≤ ENNReal.ofReal A1 * MeasureTheory.eLpNorm f ⊤ μ)
    (p : ℝ) (hp : q < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : α → E, Measurable f →
      MeasureTheory.eLpNorm (T f) (ENNReal.ofReal p) ν
        ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm f (ENNReal.ofReal p) μ := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hp0 : 0 < p := lt_trans hq0 hp
  have hr0 : -1 < p - 1 - q := by linarith
  set K : ℝ := p * (2*A0)^q * (2*A1)^(p-q) / (p-q) with hK
  have hKpos : 0 < K := by rw [hK]; positivity
  have hKnn : 0 ≤ K := hKpos.le
  refine ⟨K ^ (1/p), by positivity, ?_⟩
  intro f hf
  by_cases hfm : AEStronglyMeasurable f μ
  swap
  · rw [eLpNorm_of_not_aestronglyMeasurable hfm,
      ENNReal.mul_top (ENNReal.ofReal_pos.mpr (by positivity)).ne']
    exact le_top
  by_cases hfin : eLpNorm f (ENNReal.ofReal p) μ = ∞
  · rw [hfin, ENNReal.mul_top (ENNReal.ofReal_pos.mpr (by positivity)).ne']
    exact le_top
  have hTm : AEStronglyMeasurable (T f) ν :=
    wq_aestronglyMeasurable_T T hadd hq0 hweak hstrong hp hfm hfin
  have hvm : Measurable fun x : α => ‖f x‖ := hf.norm
  have hvnn : ∀ x : α, 0 ≤ ‖f x‖ := fun x => norm_nonneg _
  set Ψ : ℝ → ℝ≥0∞ := fun t => ∫⁻ x,
      Set.indicator {x : α | ENNReal.ofReal (t / (2*A1)) < ENNReal.ofReal ‖f x‖}
        (fun x => ENNReal.ofReal ‖f x‖ ^ q) x ∂μ with hΨ
  have hlayer : ∫⁻ x, ‖T f x‖ₑ ^ p ∂ν
      = ENNReal.ofReal p * ∫⁻ t in Set.Ioi (0:ℝ),
          ν {x : β | t < ‖T f x‖} * ENNReal.ofReal (t ^ (p - 1)) := by
    have hcongr : ∫⁻ x, ‖T f x‖ₑ ^ p ∂ν = ∫⁻ x, ENNReal.ofReal (‖T f x‖ ^ p) ∂ν := by
      refine lintegral_congr fun x => ?_
      simpa only [ofReal_norm] using
        ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (T f x)) hp0.le
    rw [hcongr]
    exact lintegral_rpow_eq_lintegral_meas_lt_mul ν (f := fun x => ‖T f x‖)
      (Eventually.of_forall fun x => norm_nonneg _) ((hmeas f).norm) hp0
  have hA : ∫⁻ t in Set.Ioi (0:ℝ), ν {x : β | t < ‖T f x‖} * ENNReal.ofReal (t ^ (p - 1))
      ≤ ENNReal.ofReal ((2*A0)^q) *
          ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (t ^ (p-1-q)) * Ψ t := by
    have hstep : ∫⁻ t in Set.Ioi (0:ℝ), ν {x : β | t < ‖T f x‖} * ENNReal.ofReal (t ^ (p - 1))
        ≤ ∫⁻ t in Set.Ioi (0:ℝ),
            (ENNReal.ofReal (2*A0/t)^q * Ψ t) * ENNReal.ofReal (t ^ (p - 1)) := by
      refine lintegral_mono_ae ?_
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      have h1 := lvl_set_q (μ := μ) (ν := ν) T hadd hq0 hA1 hweak hstrong f hfm ht
      simp only [hΨ] at h1 ⊢
      exact mul_le_mul_of_nonneg_right h1 bot_le
    have hconst : ∀ t : ℝ, 0 < t →
        ENNReal.ofReal (2*A0/t)^q * ENNReal.ofReal (t^(p-1))
          = ENNReal.ofReal ((2*A0)^q) * ENNReal.ofReal (t^(p-1-q)) := by
      intro t ht
      have hreal : (2*A0/t)^q * t^(p-1) = (2*A0)^q * t^(p-1-q) := by
        rw [Real.div_rpow (by positivity) ht.le q]
        rw [div_eq_mul_inv, ← Real.rpow_neg ht.le q]
        rw [mul_assoc, ← Real.rpow_add ht (-q) (p-1)]
        congr 1; ring_nf
      calc ENNReal.ofReal (2*A0/t)^q * ENNReal.ofReal (t^(p-1))
          = ENNReal.ofReal ((2*A0/t)^q) * ENNReal.ofReal (t^(p-1)) := by
              rw [ENNReal.ofReal_rpow_of_nonneg (by positivity : (0:ℝ) ≤ 2*A0/t) hq0.le]
        _ = ENNReal.ofReal ((2*A0/t)^q * t^(p-1)) := (ENNReal.ofReal_mul (by positivity)).symm
        _ = ENNReal.ofReal ((2*A0)^q * t^(p-1-q)) := by rw [hreal]
        _ = ENNReal.ofReal ((2*A0)^q) * ENNReal.ofReal (t^(p-1-q)) := ENNReal.ofReal_mul (by positivity)
    calc ∫⁻ t in Set.Ioi (0:ℝ), ν {x : β | t < ‖T f x‖} * ENNReal.ofReal (t ^ (p - 1))
        ≤ ∫⁻ t in Set.Ioi (0:ℝ),
            (ENNReal.ofReal (2*A0/t)^q * Ψ t) * ENNReal.ofReal (t ^ (p - 1)) := hstep
      _ = ∫⁻ t in Set.Ioi (0:ℝ),
            ENNReal.ofReal ((2*A0)^q) * (ENNReal.ofReal (t^(p-1-q)) * Ψ t) := by
          refine lintegral_congr_ae ?_
          filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
          calc ENNReal.ofReal (2*A0/t)^q * Ψ t * ENNReal.ofReal (t^(p-1))
              = (ENNReal.ofReal (2*A0/t)^q * ENNReal.ofReal (t^(p-1))) * Ψ t := by ring
            _ = (ENNReal.ofReal ((2*A0)^q) * ENNReal.ofReal (t^(p-1-q))) * Ψ t := by
                rw [hconst t ht]
            _ = ENNReal.ofReal ((2*A0)^q) * (ENNReal.ofReal (t^(p-1-q)) * Ψ t) := by ring
      _ = ENNReal.ofReal ((2*A0)^q) *
            ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (t^(p-1-q)) * Ψ t :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hB : ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (t ^ (p-1-q)) * Ψ t
      = ENNReal.ofReal ((2*A1)^(p-q)/(p-q)) * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
    simp only [hΨ]
    rw [key_lintegral (μ := μ) (v := fun x => ‖f x‖) hvm hvnn hA1 (q := q) (r := p-1-q) hq0.le hr0]
    rw [show (2*A1)^(p-1-q+1)/(p-1-q+1) = (2*A1)^(p-q)/(p-q) by
      rw [show p - 1 - q + 1 = p - q by ring]]
    congr 1
    refine lintegral_congr fun x => ?_
    rw [show q + (p - 1 - q) + 1 = p from by ring, ofReal_norm]
  have hKconst : ENNReal.ofReal K
      = ENNReal.ofReal p * (ENNReal.ofReal ((2*A0)^q) * ENNReal.ofReal ((2*A1)^(p-q)/(p-q))) := by
    rw [hK, show p * (2*A0)^q * (2*A1)^(p-q)/(p-q)
          = (p * (2*A0)^q) * ((2*A1)^(p-q)/(p-q)) by ring]
    rw [ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ p * (2*A0)^q)]
    rw [show ENNReal.ofReal (p * (2*A0)^q) = ENNReal.ofReal p * ENNReal.ofReal ((2*A0)^q) from
      ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ p)]
    ring
  have hmain : ∫⁻ x, ‖T f x‖ₑ ^ p ∂ν ≤ ENNReal.ofReal K * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
    rw [hlayer]
    calc ENNReal.ofReal p * ∫⁻ t in Set.Ioi (0:ℝ),
            ν {x : β | t < ‖T f x‖} * ENNReal.ofReal (t ^ (p - 1))
        ≤ ENNReal.ofReal p * (ENNReal.ofReal ((2*A0)^q) *
            ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (t ^ (p-1-q)) * Ψ t) :=
            mul_le_mul_of_nonneg_left hA bot_le
      _ = ENNReal.ofReal p * (ENNReal.ofReal ((2*A0)^q) *
            (ENNReal.ofReal ((2*A1)^(p-q)/(p-q)) * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ)) := by rw [hB]
      _ = ENNReal.ofReal K * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by rw [hKconst]; ring
  have hL : MeasureTheory.eLpNorm (T f) (ENNReal.ofReal p) ν
      = (∫⁻ x, ‖T f x‖ₑ ^ p ∂ν) ^ (1/p) := by
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (p := ENNReal.ofReal p)
      (ENNReal.ofReal_pos.mpr hp0).ne' ENNReal.ofReal_ne_top hTm, ENNReal.toReal_ofReal hp0.le]
  have hR : MeasureTheory.eLpNorm f (ENNReal.ofReal p) μ
      = (∫⁻ x, ‖f x‖ₑ ^ p ∂μ) ^ (1/p) := by
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (p := ENNReal.ofReal p)
      (ENNReal.ofReal_pos.mpr hp0).ne' ENNReal.ofReal_ne_top hfm, ENNReal.toReal_ofReal hp0.le]
  rw [hL, hR]
  calc (∫⁻ x, ‖T f x‖ₑ ^ p ∂ν) ^ (1/p)
      ≤ (ENNReal.ofReal K * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ) ^ (1/p) :=
          ENNReal.rpow_le_rpow hmain (by positivity)
    _ = (ENNReal.ofReal K) ^ (1/p) * (∫⁻ x, ‖f x‖ₑ ^ p ∂μ) ^ (1/p) :=
          ENNReal.mul_rpow_of_nonneg _ _ (by positivity)
    _ = ENNReal.ofReal (K ^ (1/p)) * (∫⁻ x, ‖f x‖ₑ ^ p ∂μ) ^ (1/p) := by
          rw [ENNReal.ofReal_rpow_of_nonneg hKnn (by positivity)]

end Commons.Analysis.MeasureTheory
