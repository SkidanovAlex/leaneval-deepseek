import Mathlib
import Submission.Work.Asymptotics.HalfFunnel.lowBadDefs
import Submission.Work.HFN.HalfFunnel.lowBadAux
import Submission.Work.HFN.HalfFunnel.lowBad_Aexp_tail
import Submission.Work.Asymptotics.measurable_Kaxis_Kfun
import Submission.Work.Asymptotics.layerTrunc_seminorm

/-!
# `lowF2` agrees with the paper's layer `F₂` on the bad-line region

The explicit candidate layer `lowF2` used for the bad-line part of the low-strip seminorm bound
splits the contour integral `∫_0^∞ K(τ,it) e^{-πr²t} dt` into the three pieces `PhiOne` (`(0,1]`),
`PhiTwo` (`[1,∞)`, with the non-decaying part `𝒢` removed) and `PhiSpike` (the spike window with
the translate pole re-inserted), multiplied by `2 - 2cos(πr²)`, plus the paper's `highPart`.

This file proves that `lowF2` is literally the paper's layer `paperLayer (Gcusp ℓ d)`: the pole
pieces of `PhiOne`/`PhiTwo` cancel against `PhiSpike`, and the remaining integrals are exactly
`layerLow` and `layerTrunc`.  The only inputs are the elementary bounds `hdec1` (the translate
pole is well approximated by `K` up to height `lowT`) and the cusp-tail estimate
`lowBad_Aexp_tail` (which is a theorem of the workspace).
-/

namespace Work.HFN.HalfFunnel
open Work.Asymptotics Work.Asymptotics.HalfFunnel  -- ck-hfn-fix: fork moved out of Work.Asymptotics

open MeasureTheory Set UpperHalfPlane
open Work.Kernels
open Work.Asymptotics (Aexp Gcusp paperLayer layerLow layerTrunc sinSq sinSq_eq)

noncomputable section

/-! ## Integrability of the pieces of the bad-line layer -/

/-- The windowed translate pole `(lowWin τ).indicator (tpole τ) · e^{-πxt}` is integrable on `ℝ`:
it is bounded and supported on the finite-measure window `lowWin τ`. -/
lemma integrable_indicator_tpole_exp {τ : ℍ} (hτ : lowBadSet τ) {x : ℝ} (hx : 0 ≤ x) :
    Integrable (fun t : ℝ =>
      (lowWin τ).indicator (fun u => tpole τ u * Complex.exp (-(Real.pi * x * u))) t) volume := by
  have hwin_meas : MeasurableSet (lowWin τ) := by rw [lowWin]; exact measurableSet_Ioo
  have hfin : volume (lowWin τ) < ⊤ :=
    lt_of_le_of_lt (measure_mono (Set.Ioo_subset_Icc_self)) (isCompact_Icc.measure_lt_top)
  refine (integrable_indicator_iff hwin_meas).mpr ?_
  refine IntegrableOn.of_bound hfin ?_ (1 / (2 * Real.pi * |τ.re - tsign τ|)) ?_
  · exact (continuous_tpole hτ).aestronglyMeasurable.mul (by fun_prop)
  · filter_upwards [self_mem_ae_restrict hwin_meas] with u hu
    have hu0 : (0:ℝ) < u := lt_trans (by norm_num) (win_bound hτ hu).1
    have hexp : ‖Complex.exp (-(Real.pi * x * u))‖ = Real.exp (-(Real.pi * x * u)) := by
      rw [Complex.norm_exp]; congr 1; simp
    rw [norm_mul, hexp]
    have hle1 : Real.exp (-(Real.pi * x * u)) ≤ 1 := by
      have h : 0 ≤ Real.pi * x * u := mul_nonneg (mul_nonneg Real.pi_pos.le hx) hu0.le
      rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by linarith)
    have ht := norm_tpole_le hτ u
    calc ‖tpole τ u‖ * Real.exp (-(Real.pi * x * u))
        ≤ (1 / (2 * Real.pi * |τ.re - tsign τ|)) * 1 :=
          mul_le_mul ht hle1 (Real.exp_nonneg _) (by positivity)
      _ = 1 / (2 * Real.pi * |τ.re - tsign τ|) := by ring

/-- `t ↦ K(τ,it) e^{-πxt}` is integrable on `(0,1]`, by the bound `hdec1` on `K - tpole` and the
boundedness of `tpole` there. -/
lemma integrableOn_kaxis_mul_exp_Ioc (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {C : ℝ} (hC : 0 ≤ C) {τ : ℍ} (hτ : lowBadSet τ)
    (hdec1 : ∀ t : ℝ, 0 < t → t ≤ lowT → ‖Kaxis (Kfun ℓ d) τ t - tpole τ t‖ ≤ C)
    {x : ℝ} (hx : 0 ≤ x) :
    IntegrableOn (fun t => Kaxis (Kfun ℓ d) τ t * Complex.exp (-(Real.pi * x * t)))
      (Set.Ioc 0 1) := by
  have hfin : volume (Set.Ioc (0:ℝ) 1) < ⊤ :=
    lt_of_le_of_lt (measure_mono Set.Ioc_subset_Icc_self) isCompact_Icc.measure_lt_top
  have hexp_meas : Continuous (fun t : ℝ => Complex.exp (-(Real.pi * x * t))) := by fun_prop
  refine IntegrableOn.of_bound hfin ?_ (C + 1/(2*Real.pi*|τ.re - tsign τ|)) ?_
  · exact ((measurable_Kaxis_Kfun ℓ d hd τ).mul hexp_meas.measurable).aestronglyMeasurable
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
    have ht0 : 0 < t := ht.1
    have ht1 : t ≤ 1 := ht.2
    rw [norm_mul]
    have hexp : ‖Complex.exp (-(Real.pi * x * t))‖ = Real.exp (-(Real.pi * x * t)) := by
      rw [Complex.norm_exp]; congr 1; simp
    rw [hexp]
    have hle1 : Real.exp (-(Real.pi * x * t)) ≤ 1 := by
      have h : 0 ≤ Real.pi * x * t := mul_nonneg (mul_nonneg Real.pi_pos.le hx) ht0.le
      rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by linarith)
    have hK : ‖Kaxis (Kfun ℓ d) τ t‖ ≤ C + 1/(2*Real.pi*|τ.re - tsign τ|) := by
      have hd1 := hdec1 t ht0 (by rw [lowT]; linarith)
      have ht2 := norm_tpole_le hτ t
      have heq : Kaxis (Kfun ℓ d) τ t = (Kaxis (Kfun ℓ d) τ t - tpole τ t) + tpole τ t := by ring
      rw [heq]
      calc ‖(Kaxis (Kfun ℓ d) τ t - tpole τ t) + tpole τ t‖
            ≤ ‖Kaxis (Kfun ℓ d) τ t - tpole τ t‖ + ‖tpole τ t‖ := norm_add_le _ _
        _ ≤ C + 1/(2*Real.pi*|τ.re - tsign τ|) := by linarith
    calc ‖Kaxis (Kfun ℓ d) τ t‖ * Real.exp (-(Real.pi * x * t))
        ≤ (C + 1/(2*Real.pi*|τ.re - tsign τ|)) * 1 :=
          mul_le_mul hK hle1 (Real.exp_nonneg _) (add_nonneg hC (by positivity))
      _ = C + 1/(2*Real.pi*|τ.re - tsign τ|) := by ring

/-- `t ↦ (K(τ,it) - 𝒢(τ,it)) e^{-πxt}` is integrable on `[1,∞)`: bounded on `[1,lowT]` and
`O((1+t)^M e^{-πt})` beyond `lowT` by `lowBad_Aexp_tail`. -/
lemma integrableOn_diff_mul_exp_Ici (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {C : ℝ} (hC : 0 ≤ C) {τ : ℍ} (hτ : lowBadSet τ)
    (hdec1 : ∀ t : ℝ, 0 < t → t ≤ lowT → ‖Kaxis (Kfun ℓ d) τ t - tpole τ t‖ ≤ C)
    {x : ℝ} (hx : 0 ≤ x) :
    IntegrableOn (fun t => (Kaxis (Kfun ℓ d) τ t - Aexp (Gcusp ℓ d) τ t)
      * Complex.exp (-(Real.pi * x * t))) (Set.Ici 1) := by
  have hcontA : Continuous (fun t : ℝ => Aexp (Gcusp ℓ d) τ t) := by
    unfold Aexp; fun_prop
  have hexp_meas : Continuous (fun t : ℝ => Complex.exp (-(Real.pi * x * t))) := by fun_prop
  have h1 : IntegrableOn (fun t =>
      (Kaxis (Kfun ℓ d) τ t - Aexp (Gcusp ℓ d) τ t) * Complex.exp (-(Real.pi * x * t)))
      (Set.Icc 1 lowT) := by
    obtain ⟨CB, hCB, hCBb⟩ := lowBadSet_Aexp_le ℓ d hd
    refine IntegrableOn.of_bound isCompact_Icc.measure_lt_top ?_
      ((C + 1/(2*Real.pi*|τ.re - tsign τ|)) + CB) ?_
    · exact (((measurable_Kaxis_Kfun ℓ d hd τ).sub hcontA.measurable).mul
        hexp_meas.measurable).aestronglyMeasurable
    · filter_upwards [self_mem_ae_restrict measurableSet_Icc] with t ht
      have ht1 : 1 ≤ t := ht.1
      have ht3 : t ≤ lowT := ht.2
      have ht0 : 0 < t := lt_of_lt_of_le one_pos ht1
      rw [norm_mul]
      have hexp : ‖Complex.exp (-(Real.pi * x * t))‖ = Real.exp (-(Real.pi * x * t)) := by
        rw [Complex.norm_exp]; congr 1; simp
      rw [hexp]
      have hle1 : Real.exp (-(Real.pi * x * t)) ≤ 1 := by
        have h : 0 ≤ Real.pi * x * t := mul_nonneg (mul_nonneg Real.pi_pos.le hx) ht0.le
        rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by linarith)
      have hK : ‖Kaxis (Kfun ℓ d) τ t‖ ≤ C + 1/(2*Real.pi*|τ.re - tsign τ|) := by
        have hd1 := hdec1 t ht0 ht3
        have ht2 := norm_tpole_le hτ t
        have heq : Kaxis (Kfun ℓ d) τ t = (Kaxis (Kfun ℓ d) τ t - tpole τ t) + tpole τ t := by ring
        rw [heq]
        calc ‖(Kaxis (Kfun ℓ d) τ t - tpole τ t) + tpole τ t‖
              ≤ ‖Kaxis (Kfun ℓ d) τ t - tpole τ t‖ + ‖tpole τ t‖ := norm_add_le _ _
          _ ≤ C + 1/(2*Real.pi*|τ.re - tsign τ|) := by linarith
      have hAt : ‖Aexp (Gcusp ℓ d) τ t‖ ≤ CB := hCBb τ hτ t ht1 ht3
      have hdiff : ‖Kaxis (Kfun ℓ d) τ t - Aexp (Gcusp ℓ d) τ t‖
          ≤ (C + 1/(2*Real.pi*|τ.re - tsign τ|)) + CB := by
        calc ‖Kaxis (Kfun ℓ d) τ t - Aexp (Gcusp ℓ d) τ t‖
              ≤ ‖Kaxis (Kfun ℓ d) τ t‖ + ‖Aexp (Gcusp ℓ d) τ t‖ := norm_sub_le _ _
          _ ≤ _ := by linarith
      calc ‖Kaxis (Kfun ℓ d) τ t - Aexp (Gcusp ℓ d) τ t‖ * Real.exp (-(Real.pi * x * t))
          ≤ ((C + 1/(2*Real.pi*|τ.re - tsign τ|)) + CB) * 1 :=
            mul_le_mul hdiff hle1 (Real.exp_nonneg _) (add_nonneg (add_nonneg hC (by positivity)) hCB)
        _ = (C + 1/(2*Real.pi*|τ.re - tsign τ|)) + CB := by ring
  obtain ⟨Ct, Mt, hCt, hMt, htail⟩ := lowBad_Aexp_tail ℓ d hd
  have h2 : IntegrableOn (fun t =>
      (Kaxis (Kfun ℓ d) τ t - Aexp (Gcusp ℓ d) τ t) * Complex.exp (-(Real.pi * x * t)))
      (Set.Ioi lowT) := by
    have hbase : IntegrableOn (fun t : ℝ => t ^ Mt * Real.exp (-(Real.pi * t))) (Set.Ioi 0) := by
      have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1:ℝ)) (s := Mt) (b := Real.pi)
        (by linarith) one_pos Real.pi_pos
      simpa only [Real.rpow_one, neg_mul] using h
    have hbase3 : IntegrableOn (fun t : ℝ => t ^ Mt * Real.exp (-(Real.pi * t)))
        (Set.Ioi lowT) := hbase.mono_set (by rw [lowT]; norm_num)
    have hbase3' : Integrable (fun t : ℝ =>
        Ct * 2 ^ Mt * (t ^ Mt * Real.exp (-(Real.pi * t)))) (volume.restrict (Set.Ioi lowT)) :=
      hbase3.const_mul _
    refine hbase3'.mono' ?_ ?_
    · exact (((measurable_Kaxis_Kfun ℓ d hd τ).sub hcontA.measurable).mul
        hexp_meas.measurable).aestronglyMeasurable
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      have ht3 : lowT < t := ht
      have ht0 : 0 < t := by rw [lowT] at ht3; linarith
      have ht1 : (1:ℝ) ≤ t := by rw [lowT] at ht3; linarith
      rw [norm_mul]
      have hexp : ‖Complex.exp (-(Real.pi * x * t))‖ = Real.exp (-(Real.pi * x * t)) := by
        rw [Complex.norm_exp]; congr 1; simp
      rw [hexp]
      have hle1 : Real.exp (-(Real.pi * x * t)) ≤ 1 := by
        have h : 0 ≤ Real.pi * x * t := mul_nonneg (mul_nonneg Real.pi_pos.le hx) ht0.le
        rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by linarith)
      have htailt := htail τ hτ t (le_of_lt ht3)
      have hpow : (1 + t) ^ Mt ≤ 2 ^ Mt * t ^ Mt := by
        have h1 : (1 + t) ≤ 2 * t := by linarith
        calc (1 + t) ^ Mt ≤ (2 * t) ^ Mt := Real.rpow_le_rpow (by linarith) h1 hMt
          _ = 2 ^ Mt * t ^ Mt := Real.mul_rpow (by norm_num) ht0.le
      calc ‖Kaxis (Kfun ℓ d) τ t - Aexp (Gcusp ℓ d) τ t‖ * Real.exp (-(Real.pi * x * t))
          ≤ (Ct * (1 + t) ^ Mt * Real.exp (-(Real.pi * t))) * 1 :=
            mul_le_mul htailt hle1 (Real.exp_nonneg _) (by positivity)
        _ = Ct * ((1 + t) ^ Mt * Real.exp (-(Real.pi * t))) := by ring
        _ ≤ Ct * ((2 ^ Mt * t ^ Mt) * Real.exp (-(Real.pi * t))) := by
            apply mul_le_mul_of_nonneg_left _ hCt.le
            exact mul_le_mul_of_nonneg_right hpow (Real.exp_nonneg _)
        _ = Ct * 2 ^ Mt * (t ^ Mt * Real.exp (-(Real.pi * t))) := by ring
  have hsplit : Set.Ici (1:ℝ) = Set.Icc 1 lowT ∪ Set.Ioi lowT := by
    ext t; simp only [Set.mem_Ici, Set.mem_union, Set.mem_Icc, Set.mem_Ioi]
    constructor
    · intro h
      by_cases h3 : t ≤ lowT
      · exact Or.inl ⟨h, h3⟩
      · exact Or.inr (not_le.mp h3)
    · rintro (⟨h, -⟩ | h) <;> rw [lowT] at * <;> linarith
  rw [hsplit]
  exact h1.union h2

/-! ## The three pieces of `lowF2` rewritten as differences of plain integrals -/

/-- `PhiOne` is the difference of the `(0,1]`-integral of `K e^{-πxt}` and the contribution of
the windowed pole. -/
lemma PhiOne_eq_decomp (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {C : ℝ} (hC : 0 ≤ C) {τ : ℍ} (hτ : lowBadSet τ)
    (hdec1 : ∀ t : ℝ, 0 < t → t ≤ lowT → ‖Kaxis (Kfun ℓ d) τ t - tpole τ t‖ ≤ C)
    {x : ℝ} (hx : 0 ≤ x) :
    PhiOne ℓ d τ x
      = (∫ t in Set.Ioc 0 1, Kaxis (Kfun ℓ d) τ t * Complex.exp (-(Real.pi * x * t)))
        - (∫ t in Set.Ioc 0 1,
            (lowWin τ).indicator (fun u => tpole τ u * Complex.exp (-(Real.pi * x * u))) t) := by
  have hK : Integrable (fun t : ℝ => Kaxis (Kfun ℓ d) τ t * Complex.exp (-(Real.pi * x * t)))
      (volume.restrict (Set.Ioc 0 1)) := integrableOn_kaxis_mul_exp_Ioc ℓ d hd hC hτ hdec1 hx
  have hW : Integrable (fun t : ℝ =>
      (lowWin τ).indicator (fun u => tpole τ u * Complex.exp (-(Real.pi * x * u))) t)
      (volume.restrict (Set.Ioc 0 1)) :=
    (integrable_indicator_tpole_exp hτ hx).mono_measure Measure.restrict_le_self
  rw [PhiOne]
  rw [show (∫ t in Set.Ioc 0 1, (Kaxis (Kfun ℓ d) τ t
        - (lowWin τ).indicator (tpole τ) t) * Complex.exp (-(Real.pi * x * t)))
      = ∫ t in Set.Ioc 0 1, (Kaxis (Kfun ℓ d) τ t * Complex.exp (-(Real.pi * x * t))
          - (lowWin τ).indicator (fun u => tpole τ u * Complex.exp (-(Real.pi * x * u))) t) from
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun t => by
      classical
      dsimp only
      rw [Set.indicator_apply]
      by_cases h : t ∈ lowWin τ
      · rw [if_pos h, Set.indicator_of_mem h]; ring
      · rw [if_neg h, Set.indicator_of_notMem h]; ring))]
  rw [MeasureTheory.integral_sub hK hW]

/-- `PhiTwo` is the difference of the `[1,∞)`-integral of `(K - 𝒢) e^{-πxt}` and the contribution
of the windowed pole. -/
lemma PhiTwo_eq_decomp (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {C : ℝ} (hC : 0 ≤ C) {τ : ℍ} (hτ : lowBadSet τ)
    (hdec1 : ∀ t : ℝ, 0 < t → t ≤ lowT → ‖Kaxis (Kfun ℓ d) τ t - tpole τ t‖ ≤ C)
    {x : ℝ} (hx : 0 ≤ x) :
    PhiTwo ℓ d τ x
      = (∫ t in Set.Ici 1, (Kaxis (Kfun ℓ d) τ t - Aexp (Gcusp ℓ d) τ t)
          * Complex.exp (-(Real.pi * x * t)))
        - (∫ t in Set.Ici 1,
            (lowWin τ).indicator (fun u => tpole τ u * Complex.exp (-(Real.pi * x * u))) t) := by
  have hKa : Integrable (fun t : ℝ =>
      (Kaxis (Kfun ℓ d) τ t - Aexp (Gcusp ℓ d) τ t) * Complex.exp (-(Real.pi * x * t)))
      (volume.restrict (Set.Ici 1)) := integrableOn_diff_mul_exp_Ici ℓ d hd hC hτ hdec1 hx
  have hW : Integrable (fun t : ℝ =>
      (lowWin τ).indicator (fun u => tpole τ u * Complex.exp (-(Real.pi * x * u))) t)
      (volume.restrict (Set.Ici 1)) :=
    (integrable_indicator_tpole_exp hτ hx).mono_measure Measure.restrict_le_self
  rw [PhiTwo]
  rw [show (∫ t in Set.Ici (1:ℝ), (Kaxis (Kfun ℓ d) τ t - Aexp (Gcusp ℓ d) τ t
        - (lowWin τ).indicator (tpole τ) t) * Complex.exp (-(Real.pi * x * t)))
      = ∫ t in Set.Ici (1:ℝ), ((Kaxis (Kfun ℓ d) τ t - Aexp (Gcusp ℓ d) τ t)
            * Complex.exp (-(Real.pi * x * t))
          - (lowWin τ).indicator (fun u => tpole τ u * Complex.exp (-(Real.pi * x * u))) t) from
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun t => by
      classical
      dsimp only
      rw [Set.indicator_apply]
      by_cases h : t ∈ lowWin τ
      · rw [if_pos h, Set.indicator_of_mem h]; ring
      · rw [if_neg h, Set.indicator_of_notMem h]; ring))]
  rw [MeasureTheory.integral_sub hKa hW]

/-- The windowed pole contributions over `(0,1]` and `[1,∞)` add up to `PhiSpike`: the window is
contained in `(0,∞)` and only the point `1` is counted twice. -/
lemma win_indicator_split {τ : ℍ} (hτ : lowBadSet τ) {x : ℝ} (hx : 0 ≤ x) :
    (∫ t in Set.Ioc 0 1,
        (lowWin τ).indicator (fun u => tpole τ u * Complex.exp (-(Real.pi * x * u))) t)
      + (∫ t in Set.Ici 1,
        (lowWin τ).indicator (fun u => tpole τ u * Complex.exp (-(Real.pi * x * u))) t)
      = ∫ t in lowWin τ, tpole τ t * Complex.exp (-(Real.pi * x * t)) := by
  set g : ℝ → ℂ := fun u => tpole τ u * Complex.exp (-(Real.pi * x * u)) with hgdef
  have hwin_sub : lowWin τ ⊆ Set.Ioi (0:ℝ) := lowWin_subset_Ioi hτ
  have hwin_meas : MeasurableSet (lowWin τ) := by rw [lowWin]; exact measurableSet_Ioo
  have hg : Integrable ((lowWin τ).indicator g) volume :=
    (integrable_indicator_iff hwin_meas).mpr (by
      have hfin : volume (lowWin τ) < ⊤ :=
        lt_of_le_of_lt (measure_mono (Set.Ioo_subset_Icc_self)) (isCompact_Icc.measure_lt_top)
      refine IntegrableOn.of_bound hfin ?_ (1 / (2 * Real.pi * |τ.re - tsign τ|)) ?_
      · exact (continuous_tpole hτ).aestronglyMeasurable.mul (by fun_prop)
      · filter_upwards [self_mem_ae_restrict hwin_meas] with u hu
        have hu0 : (0:ℝ) < u := lt_trans (by norm_num) (win_bound hτ hu).1
        have hexp : ‖Complex.exp (-(Real.pi * x * u))‖ = Real.exp (-(Real.pi * x * u)) := by
          rw [Complex.norm_exp]; congr 1; simp
        rw [norm_mul, hexp]
        have hle1 : Real.exp (-(Real.pi * x * u)) ≤ 1 := by
          have h : 0 ≤ Real.pi * x * u := mul_nonneg (mul_nonneg Real.pi_pos.le hx) hu0.le
          rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by linarith)
        have ht := norm_tpole_le hτ u
        calc ‖tpole τ u‖ * Real.exp (-(Real.pi * x * u))
            ≤ (1 / (2 * Real.pi * |τ.re - tsign τ|)) * 1 :=
              mul_le_mul ht hle1 (Real.exp_nonneg _) (by positivity)
          _ = 1 / (2 * Real.pi * |τ.re - tsign τ|) := by ring)
  have hgIoc : IntegrableOn ((lowWin τ).indicator g) (Set.Ioc 0 1) volume :=
    hg.mono_measure Measure.restrict_le_self
  have hgIci : IntegrableOn ((lowWin τ).indicator g) (Set.Ici 1) volume :=
    hg.mono_measure Measure.restrict_le_self
  have hunion : Set.Ioc (0:ℝ) 1 ∪ Set.Ici 1 = Set.Ioi 0 := by
    ext t; simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ici, Set.mem_Ioi]
    constructor
    · rintro (⟨h, -⟩ | h) <;> linarith
    · intro h
      by_cases h1 : t ≤ 1
      · exact Or.inl ⟨h, h1⟩
      · exact Or.inr (le_of_lt (not_le.mp h1))
  have hdisj : AEDisjoint volume (Set.Ioc (0:ℝ) 1) (Set.Ici 1) := by
    rw [AEDisjoint]
    have h : Set.Ioc (0:ℝ) 1 ∩ Set.Ici 1 = {1} := by
      ext t; simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ici, Set.mem_singleton_iff]
      constructor
      · rintro ⟨⟨-, h1⟩, h2⟩; linarith
      · intro h; subst h; norm_num
    rw [h]; exact measure_singleton 1
  have key1 := setIntegral_union₀ hdisj measurableSet_Ici.nullMeasurableSet hgIoc hgIci
  rw [hunion] at key1
  have key2 : ∫ t in Set.Ioi 0, (lowWin τ).indicator g t = ∫ t, (lowWin τ).indicator g t :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun t ht => by
      rw [Set.indicator_of_notMem]
      exact fun hmem => ht (hwin_sub hmem))
  have key3 : ∫ t, (lowWin τ).indicator g t = ∫ t in lowWin τ, g t := integral_indicator hwin_meas
  rw [key2, key3] at key1
  exact key1.symm

/-- **The sum of the three pieces is the two plain contour integrals.** -/
lemma lowF2_main_sum (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {C : ℝ} (hC : 0 ≤ C) {τ : ℍ} (hτ : lowBadSet τ)
    (hdec1 : ∀ t : ℝ, 0 < t → t ≤ lowT → ‖Kaxis (Kfun ℓ d) τ t - tpole τ t‖ ≤ C)
    {x : ℝ} (hx : 0 ≤ x) :
    PhiOne ℓ d τ x + PhiTwo ℓ d τ x + PhiSpike τ x
      = (∫ t in Set.Ioc 0 1, Kaxis (Kfun ℓ d) τ t * Complex.exp (-(Real.pi * x * t)))
      + (∫ t in Set.Ici 1, (Kaxis (Kfun ℓ d) τ t - Aexp (Gcusp ℓ d) τ t)
          * Complex.exp (-(Real.pi * x * t))) := by
  have h1 := PhiOne_eq_decomp ℓ d hd hC hτ hdec1 hx
  have h2 := PhiTwo_eq_decomp ℓ d hd hC hτ hdec1 hx
  have h3 := win_indicator_split hτ hx
  have hspike : PhiSpike τ x
      = ∫ t in lowWin τ, tpole τ t * Complex.exp (-(Real.pi * x * t)) := rfl
  rw [h1, h2, hspike, ← h3]
  ring

/-! ## The layer pieces in the `r`-variable -/

/-- `layerLow` is the `(0,1]`-integral of `K e^{-πr²t}` times `sinSq r`. -/
lemma layerLow_eq_Ioc (ℓ : LogLambdaData) (d : ℕ) (τ : ℍ) (r : ℝ) :
    layerLow ℓ d τ r
      = sinSq r * ∫ t in Set.Ioc 0 1, Kaxis (Kfun ℓ d) τ t * Complex.exp (-(Real.pi * r ^ 2 * t)) := by
  rw [layerLow, intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]

/-- `layerTrunc` is the `[1,∞)`-integral of `(K - 𝒢) e^{-πr²t}` times `sinSq r`. -/
lemma layerTrunc_eq_Ici (ℓ : LogLambdaData) (d : ℕ) (τ : ℍ) (r : ℝ) :
    layerTrunc (Gcusp ℓ d) ℓ d τ r
      = sinSq r * ∫ t in Set.Ici 1, (Kaxis (Kfun ℓ d) τ t - Aexp (Gcusp ℓ d) τ t)
          * Complex.exp (-(Real.pi * r ^ 2 * t)) := by
  rw [layerTrunc]

/-- `lowF2_main_sum` specialised to `x = r²`, in the exact syntactic form matching `layerLow`
and `layerTrunc`. -/
lemma lowF2_main_sum_r (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {C : ℝ} (hC : 0 ≤ C) {τ : ℍ} (hτ : lowBadSet τ)
    (hdec1 : ∀ t : ℝ, 0 < t → t ≤ lowT → ‖Kaxis (Kfun ℓ d) τ t - tpole τ t‖ ≤ C)
    (r : ℝ) :
    PhiOne ℓ d τ (r ^ 2) + PhiTwo ℓ d τ (r ^ 2) + PhiSpike τ (r ^ 2)
      = (∫ t in Set.Ioc 0 1, Kaxis (Kfun ℓ d) τ t * Complex.exp (-(Real.pi * r ^ 2 * t)))
      + (∫ t in Set.Ici 1, (Kaxis (Kfun ℓ d) τ t - Aexp (Gcusp ℓ d) τ t)
          * Complex.exp (-(Real.pi * r ^ 2 * t))) := by
  have h := lowF2_main_sum ℓ d hd hC hτ hdec1 (sq_nonneg r)
  rw [h]
  simp only [Complex.ofReal_pow]

end

theorem lowF2_eq_paperLayer (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (C : ℝ) (hC : 0 ≤ C)
    (hdec1 : ∀ (τ : UpperHalfPlane), Work.Asymptotics.HalfFunnel.lowBadSet τ →
      ∀ t : ℝ, 0 < t → t ≤ Work.Asymptotics.HalfFunnel.lowT →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
          - Work.Asymptotics.HalfFunnel.tpole τ t‖ ≤ C)
    (hdec2 : ∀ (τ : UpperHalfPlane), Work.Asymptotics.HalfFunnel.lowBadSet τ →
      ∀ t : ℝ, 0 < t → t ≤ Work.Asymptotics.HalfFunnel.lowT →
        Work.Asymptotics.HalfFunnel.lowRho ≤ |t - τ.im| →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ C) :
    ∀ (τ : UpperHalfPlane) (r : ℝ), Work.Asymptotics.HalfFunnel.lowBadSet τ →
      Work.Asymptotics.HalfFunnel.lowF2 ℓ d τ r
        = Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ r := by
  intro τ r hτ
  rw [lowF2, paperLayer, layerLow_eq_Ioc ℓ d τ r, layerTrunc_eq_Ici ℓ d τ r,
    lowF2_main_sum_r ℓ d hd hC hτ (hdec1 τ hτ) r, ← sinSq_eq r]
  ring

end Work.HFN.HalfFunnel
