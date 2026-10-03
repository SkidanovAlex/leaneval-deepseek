import Mathlib
import Submission.Work.Analysis.Probability.lepingle_variation_lp_all
import Submission.Work.Analysis.Probability.doob_maximal_weak_sigmaFinite
import Submission.Work.Analysis.Probability.jump_count_weak_one
import Submission.Work.Analysis.Probability.exists_level_of_Vpath_gt_theta
import Submission.Work.Analysis.Probability.interpolation_weak_one_strong_real
import Submission.Port.Aesm

/-!
# Lépingle's maximal variation inequality in `L^p`, `1 < p < ∞`, `r > 2`

Target: `Work.Analysis.Probability.lepingle_variation_lp_le`.

The case `2 < p` is `Commons.Analysis.Probability.lepingle_lp_gt_two`.
The range `1 < p ≤ 2` is obtained by a Calderón–Zygmund argument: the `L^s`-bound
(`s = r`) and the `L^q`-bound (`q > 2`) for the variation, applied to a truncation
`min(f, Λ)` and its complement, combined with the layer-cake formula.
All supremum manipulation is done in `ℝ≥0∞`.
-/

namespace Work.Analysis.Probability

open MeasureTheory Filter
open scoped ENNReal BigOperators Topology

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}

/-! ## The path functional and its subadditivity -/

/-- The `ℝ≥0∞`-valued `r`-variation of a single path `x : ℕ → ℝ`. -/
noncomputable def Vpath (r : ℝ) (x : ℕ → ℝ) : ℝ≥0∞ :=
  ⨆ (u : {u : ℕ → ℕ // StrictMono u}) (J : ℕ),
    ENNReal.ofReal ((∑ j ∈ Finset.range J, |x (u.1 (j+1)) - x (u.1 j)| ^ r) ^ (1/r))

/-- The `ℝ≥0∞`-valued maximal `r`-variation of a path family `g`, as a supremum over
horizons.  It agrees with `Vpath` applied to the `ω`-slice, see `Vsup_eq_Vpath`. -/
noncomputable def Vsup (g : ℕ → Ω → ℝ) (r : ℝ) : Ω → ℝ≥0∞ :=
  fun ω => ⨆ N, SFTest.Vtr g r N ω

/-- **Subadditivity of the path variation**: `V (x + y) ≤ V x + V y`. -/
lemma Vpath_add_le (x y : ℕ → ℝ) {r : ℝ} (hr : 1 ≤ r) :
    Vpath r (x + y) ≤ Vpath r x + Vpath r y := by
  refine iSup_le (fun u => iSup_le (fun J => ?_))
  have hr0 : (0:ℝ) < r := lt_of_lt_of_le one_pos hr
  have h1r : (0:ℝ) < 1/r := div_pos one_pos hr0
  have hsum_le : (∑ j ∈ Finset.range J, |(x + y) (u.1 (j+1)) - (x + y) (u.1 j)| ^ r)
      ≤ ∑ j ∈ Finset.range J, (|x (u.1 (j+1)) - x (u.1 j)| + |y (u.1 (j+1)) - y (u.1 j)|) ^ r := by
    refine Finset.sum_le_sum (fun j _ => ?_)
    refine Real.rpow_le_rpow (abs_nonneg _) ?_ hr0.le
    simp only [Pi.add_apply]
    rw [show x (u.1 (j+1)) + y (u.1 (j+1)) - (x (u.1 j) + y (u.1 j))
        = (x (u.1 (j+1)) - x (u.1 j)) + (y (u.1 (j+1)) - y (u.1 j)) by ring]
    exact abs_add_le _ _
  have hmin := Real.Lp_add_le_of_nonneg (s := Finset.range J)
    (f := fun j => |x (u.1 (j+1)) - x (u.1 j)|) (g := fun j => |y (u.1 (j+1)) - y (u.1 j)|) hr
    (fun j _ => abs_nonneg _) (fun j _ => abs_nonneg _)
  have hchain : (∑ j ∈ Finset.range J, |(x + y) (u.1 (j+1)) - (x + y) (u.1 j)| ^ r) ^ (1/r)
      ≤ (∑ j ∈ Finset.range J, |x (u.1 (j+1)) - x (u.1 j)| ^ r) ^ (1/r)
        + (∑ j ∈ Finset.range J, |y (u.1 (j+1)) - y (u.1 j)| ^ r) ^ (1/r) :=
    le_trans (Real.rpow_le_rpow (Finset.sum_nonneg (fun j _ => Real.rpow_nonneg (abs_nonneg _) r))
      hsum_le h1r.le) hmin
  refine le_trans (ENNReal.ofReal_le_ofReal hchain) ?_
  rw [ENNReal.ofReal_add (Real.rpow_nonneg (Finset.sum_nonneg (fun j _ => Real.rpow_nonneg (abs_nonneg _) r)) _)
    (Real.rpow_nonneg (Finset.sum_nonneg (fun j _ => Real.rpow_nonneg (abs_nonneg _) r)) _)]
  refine add_le_add ?_ ?_
  · exact le_iSup_of_le u (le_iSup_of_le J le_rfl)
  · exact le_iSup_of_le u (le_iSup_of_le J le_rfl)

lemma Vsup_le_Vpath (X : ℕ → Ω → ℝ) (r : ℝ) (ω : Ω) :
    Vsup X r ω ≤ Vpath r (fun n => X n ω) := by
  show (⨆ N, SFTest.Vtr X r N ω) ≤ Vpath r (fun n => X n ω)
  refine iSup_le (fun N => ?_)
  show SFTest.Vtr X r N ω ≤ Vpath r (fun n => X n ω)
  unfold SFTest.Vtr Vpath
  refine iSup_le (fun u => iSup_le (fun J => ?_))
  by_cases hN : u.1 J ≤ N
  · rw [if_pos hN]; exact le_iSup_of_le u (le_iSup_of_le J le_rfl)
  · rw [if_neg hN]; exact bot_le

lemma Vpath_le_Vsup (X : ℕ → Ω → ℝ) (r : ℝ) (ω : Ω) :
    Vpath r (fun n => X n ω) ≤ Vsup X r ω := by
  show Vpath r (fun n => X n ω) ≤ ⨆ N, SFTest.Vtr X r N ω
  unfold Vpath
  refine iSup_le (fun u => iSup_le (fun J => ?_))
  refine le_trans (le_iSup_of_le u (le_iSup_of_le J ?_))
    (le_iSup (fun N : ℕ => SFTest.Vtr X r N ω) (u.1 J))
  rw [if_pos le_rfl]

lemma Vsup_eq_Vpath (X : ℕ → Ω → ℝ) (r : ℝ) (ω : Ω) :
    Vsup X r ω = Vpath r (fun n => X n ω) :=
  le_antisymm (Vsup_le_Vpath X r ω) (Vpath_le_Vsup X r ω)

lemma measurable_Vsup (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (g : ℕ → Ω → ℝ)
    (hg : ∀ n, Measurable[ℱ n] (g n)) (r : ℝ) : Measurable (Vsup g r) :=
  Measurable.iSup (fun N => SFTest.measurable_Vtr ℱ g hg r N)

/-- **Subadditivity of the maximal variation, almost everywhere.** -/
lemma Vsup_add_le_ae (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) {f g h : Ω → ℝ} {r : ℝ}
    (hr : 1 ≤ r)
    (hadd : ∀ n, μ[f | ℱ n] =ᵐ[μ] fun ω => μ[g | ℱ n] ω + μ[h | ℱ n] ω) :
    Vsup (fun n => μ[f | ℱ n]) r ≤ᵐ[μ]
      Vsup (fun n => μ[g | ℱ n]) r + Vsup (fun n => μ[h | ℱ n]) r := by
  filter_upwards [MeasureTheory.ae_all_iff.mpr hadd] with ω hω
  simp only [Pi.add_apply] at hω ⊢
  rw [Vsup_eq_Vpath (fun n => μ[f | ℱ n]) r ω, Vsup_eq_Vpath (fun n => μ[g | ℱ n]) r ω,
    Vsup_eq_Vpath (fun n => μ[h | ℱ n]) r ω]
  have hpath : (fun n => μ[f | ℱ n] ω) = (fun n => μ[g | ℱ n] ω) + (fun n => μ[h | ℱ n] ω) := by
    funext n; rw [Pi.add_apply]; exact hω n
  rw [hpath]
  exact Vpath_add_le _ _ hr

/-! ## Chebyshev's inequality in `ℝ≥0∞` -/

lemma chebyshev_ennreal {W : Ω → ℝ≥0∞} (hW : Measurable W) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 < t) :
    ENNReal.ofReal t ^ s * μ {ω | ENNReal.ofReal t < W ω} ≤ ∫⁻ ω, W ω ^ s ∂μ := by
  rw [← lintegral_indicator_const (μ := μ) (s := {ω | ENNReal.ofReal t < W ω})
    (c := ENNReal.ofReal t ^ s) (measurableSet_lt measurable_const hW)]
  refine lintegral_mono (fun ω => ?_)
  by_cases hω : ω ∈ {ω | ENNReal.ofReal t < W ω}
  · rw [Set.indicator_of_mem hω]; exact ENNReal.rpow_le_rpow hω.le hs
  · rw [Set.indicator_of_notMem hω]; exact bot_le


/-! ## Power integrals over `(0,1]` and `(1,∞)` -/

lemma lintegral_Ioc_rpow (a : ℝ) (ha : -1 < a) :
    ∫⁻ t in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (t ^ a) ∂volume
      = ENNReal.ofReal (1 / (a + 1)) := by
  have h_int : IntegrableOn (fun t : ℝ => t ^ a) (Set.Ioc 0 1) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact intervalIntegral.intervalIntegrable_rpow' ha
  rw [← ofReal_integral_eq_lintegral_ofReal h_int (by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
    exact Real.rpow_nonneg ht.1.le a)]
  congr 1
  rw [← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  rw [integral_rpow (Or.inl ha), Real.one_rpow, Real.zero_rpow (by linarith : a + 1 ≠ 0)]
  simp [one_div]

lemma lintegral_Ioi_rpow (a : ℝ) (ha : a < -1) :
    ∫⁻ t in Set.Ioi (1:ℝ), ENNReal.ofReal (t ^ a) ∂volume
      = ENNReal.ofReal (-1 / (a + 1)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_Ioi_rpow_of_lt ha zero_lt_one) (by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    exact Real.rpow_nonneg (le_trans zero_le_one ht.le) a)]
  congr 1
  rw [integral_Ioi_rpow_of_lt ha zero_lt_one, Real.one_rpow]

/-! ## The Calderón–Zygmund layer-cake bound -/

/-- The one-dimensional power integral produced by the layer cake with the level
`Λ t = min (t^2) (√t)`:  `∫_0^∞ Λ(t)^(δ-p) t^(p-1-δ) dt ≤ 6/(δ-p)`. -/
lemma lintegral_lam_rpow_le {p δ : ℝ} (hp : 0 < p) (hδ : p < δ) :
    ∫⁻ t in Set.Ioi (0:ℝ),
        ENNReal.ofReal ((min (t^2) (Real.sqrt t)) ^ (δ - p) * t ^ (p - 1 - δ)) ∂volume
      ≤ ENNReal.ofReal (6 / (δ - p)) := by
  have hδp : 0 < δ - p := by linarith
  have hδp' : 0 < δ + p := by linarith
  have hUnion : Set.Ioc (0:ℝ) 1 ∪ Set.Ioi (1:ℝ) = Set.Ioi (0:ℝ) := by
    ext t
    simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro (⟨h1, h2⟩ | h3)
      · exact h1
      · linarith
    · intro h
      rcases le_or_gt t 1 with hle | hgt
      · exact Or.inl ⟨h, hle⟩
      · exact Or.inr hgt
  have hdisj : Disjoint (Set.Ioc (0:ℝ) 1) (Set.Ioi (1:ℝ)) := by
    rw [Set.disjoint_left]
    intro t ht ht'
    exact absurd ht.2 (not_le.mpr ht')
  have hsplit : ∫⁻ t in Set.Ioi (0:ℝ),
        ENNReal.ofReal ((min (t^2) (Real.sqrt t)) ^ (δ - p) * t ^ (p - 1 - δ)) ∂volume
      = (∫⁻ t in Set.Ioc (0:ℝ) 1,
          ENNReal.ofReal ((min (t^2) (Real.sqrt t)) ^ (δ - p) * t ^ (p - 1 - δ)) ∂volume)
        + (∫⁻ t in Set.Ioi (1:ℝ),
          ENNReal.ofReal ((min (t^2) (Real.sqrt t)) ^ (δ - p) * t ^ (p - 1 - δ)) ∂volume) := by
    conv_lhs => rw [← hUnion]
    rw [lintegral_union (μ := volume) measurableSet_Ioi hdisj]
  rw [hsplit]
  have hlow : (∫⁻ t in Set.Ioc (0:ℝ) 1,
        ENNReal.ofReal ((min (t^2) (Real.sqrt t)) ^ (δ - p) * t ^ (p - 1 - δ)) ∂volume)
      ≤ ENNReal.ofReal (1 / (δ - p)) := by
    have step : (∫⁻ t in Set.Ioc (0:ℝ) 1,
        ENNReal.ofReal ((min (t^2) (Real.sqrt t)) ^ (δ - p) * t ^ (p - 1 - δ)) ∂volume)
        ≤ ∫⁻ t in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (t ^ (δ - p - 1)) ∂volume := by
      refine lintegral_mono_ae ?_
      filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
      have ht0 : 0 < t := ht.1
      refine ENNReal.ofReal_le_ofReal ?_
      have h2 : t ^ (δ - p - 1) = t ^ (2 * (δ - p)) * t ^ (p - 1 - δ) := by
        rw [show δ - p - 1 = 2 * (δ - p) + (p - 1 - δ) by ring, Real.rpow_add ht0]
      rw [h2]
      refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg ht0.le _)
      have h1 : (min (t^2) (Real.sqrt t)) ^ (δ - p) ≤ (t ^ 2) ^ (δ - p) :=
        Real.rpow_le_rpow (by positivity) (min_le_left _ _) (by linarith)
      refine le_trans h1 (le_of_eq ?_)
      rw [show (t^2 : ℝ) = t ^ (2:ℝ) by rw [← Real.rpow_ofNat],
        ← Real.rpow_mul (by positivity : (0:ℝ) ≤ t) (2:ℝ) (δ - p)]
    refine le_trans step ?_
    rw [lintegral_Ioc_rpow (δ - p - 1) (by linarith)]
    congr 1
    rw [show δ - p - 1 + 1 = δ - p by ring]
  have hhigh : (∫⁻ t in Set.Ioi (1:ℝ),
        ENNReal.ofReal ((min (t^2) (Real.sqrt t)) ^ (δ - p) * t ^ (p - 1 - δ)) ∂volume)
      ≤ ENNReal.ofReal (2 / (δ - p)) := by
    have hIex : (-(δ - p) / 2 - 1) < -1 := by linarith [hδp]
    have step : (∫⁻ t in Set.Ioi (1:ℝ),
        ENNReal.ofReal ((min (t^2) (Real.sqrt t)) ^ (δ - p) * t ^ (p - 1 - δ)) ∂volume)
        ≤ ∫⁻ t in Set.Ioi (1:ℝ), ENNReal.ofReal (t ^ (-(δ - p) / 2 - 1)) ∂volume := by
      refine lintegral_mono_ae ?_
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      have ht0 : 0 < t := by have h := Set.mem_Ioi.mp ht; linarith
      refine ENNReal.ofReal_le_ofReal ?_
      have h2 : t ^ (-(δ - p) / 2 - 1) = t ^ ((δ - p)/2) * t ^ (p - 1 - δ) := by
        rw [show -(δ - p) / 2 - 1 = (δ - p)/2 + (p - 1 - δ) by ring, Real.rpow_add ht0]
      rw [h2]
      refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg ht0.le _)
      have h1 : (min (t^2) (Real.sqrt t)) ^ (δ - p) ≤ (Real.sqrt t) ^ (δ - p) :=
        Real.rpow_le_rpow (by positivity) (min_le_right _ _) (by linarith)
      refine le_trans h1 (le_of_eq ?_)
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (le_of_lt ht0) (1/2) (δ - p)]
      congr 1
      ring
    refine le_trans step ?_
    rw [lintegral_Ioi_rpow (-(δ - p) / 2 - 1) hIex]
    have hval : (-1:ℝ) / (-(δ - p) / 2 - 1 + 1) = 2 / (δ - p) := by
      rw [show -(δ - p) / 2 - 1 + 1 = -(δ - p)/2 by ring]
      field_simp
    rw [hval]
  refine le_trans (add_le_add hlow hhigh) ?_
  rw [← ENNReal.ofReal_add (div_nonneg zero_le_one hδp.le) (div_nonneg (by norm_num) hδp.le)]
  refine ENNReal.ofReal_le_ofReal ?_
  have h3 : (1:ℝ)/(δ-p) + 2/(δ-p) = 3/(δ-p) := by rw [← add_div]; norm_num
  have h4 : (3:ℝ)/(δ-p) ≤ 6/(δ-p) := by
    rw [div_le_div_iff₀ hδp hδp]; linarith
  linarith


/-! ## Measurability of real powers -/

lemma measurable_rpow_const (c : ℝ) : Measurable fun x : ℝ => x ^ c := by
  have h : (fun x : ℝ => x ^ c) = fun x =>
      if 0 < x then Real.exp (Real.log x * c)
      else if x < 0 then Real.exp (Real.log x * c) * Real.cos (c * Real.pi)
      else (if c = 0 then 1 else 0) := by
    funext x
    rcases lt_trichotomy x 0 with hlt | heq | hgt
    · rw [if_neg (not_lt.mpr hlt.le), if_pos hlt, Real.rpow_def_of_neg hlt]
    · subst heq
      rw [if_neg (lt_irrefl 0), if_neg (lt_irrefl 0)]
      by_cases hc : c = 0
      · rw [if_pos hc, hc, Real.rpow_zero]
      · rw [if_neg hc, Real.zero_rpow hc]
    · rw [if_pos hgt, Real.rpow_def_of_pos hgt]
  rw [h]
  refine Measurable.ite (measurableSet_lt measurable_const measurable_id) ?_
    (Measurable.ite (measurableSet_lt measurable_id measurable_const) ?_ measurable_const)
  · exact Real.measurable_exp.comp (Real.measurable_log.mul measurable_const)
  · exact (Real.measurable_exp.comp (Real.measurable_log.mul measurable_const)).mul measurable_const

lemma measurable_lam_rpow (a b : ℝ) : Measurable fun t : ℝ =>
    ENNReal.ofReal ((min (t^2) (Real.sqrt t)) ^ a * t ^ b) :=
  Measurable.ennreal_ofReal
    (((measurable_rpow_const a).comp
      ((measurable_id.pow_const 2).min Real.continuous_sqrt.measurable)).mul
      (measurable_rpow_const b))

lemma tendsto_natCast_ennreal_atTop : Tendsto (fun n : ℕ => (n : ℝ≥0∞)) atTop (𝓝 (⊤ : ℝ≥0∞)) := by
  rw [nhds_top_order, Filter.tendsto_iInf]
  intro l
  rw [Filter.tendsto_iInf]
  intro hl
  rw [Filter.tendsto_principal]
  obtain ⟨N, hN⟩ := exists_nat_gt (l.toReal)
  refine Filter.eventually_atTop.mpr ⟨N + 1, fun n hn => ?_⟩
  rw [Set.mem_Ioi, ← ENNReal.ofReal_toReal (ne_of_lt hl), ← ENNReal.ofReal_natCast n,
    ENNReal.ofReal_lt_ofReal_iff (by exact_mod_cast (lt_of_lt_of_le (Nat.succ_pos N) hn))]
  exact lt_of_lt_of_le hN (by exact_mod_cast (le_trans (Nat.le_succ N) hn))

/-! ## The Calderón–Zygmund layer-cake lemma -/

/-- **Calderón–Zygmund / layer-cake.**  If the distribution function of `W` obeys a bound which
is adaptable in the truncation level `min (t^2) (√t)`, then the `L^p` bound follows. -/
lemma lintegral_rpow_le_of_distribution_bound {W : Ω → ℝ≥0∞} (hW : Measurable W)
    {p s q : ℝ} (hp : 0 < p) (hps : p < s) (hpq : p < q) :
    ∃ K : ℝ, 0 < K ∧ ∀ (A B : ℝ≥0∞),
      (∀ t : ℝ, 0 < t → μ {ω | ENNReal.ofReal t < W ω} ≤
          A * ENNReal.ofReal ((min (t^2) (Real.sqrt t)) ^ (s - p) / t^s)
        + B * ENNReal.ofReal ((min (t^2) (Real.sqrt t)) ^ (q - p) / t^q)) →
      ∫⁻ ω, W ω ^ p ∂μ ≤ ENNReal.ofReal K * (A + B) := by
  set K : ℝ := max 1 (6 * p) * (1 / (s - p) + 1 / (q - p)) + 1 with hKdef
  have hKpos : 0 < K := by
    rw [hKdef]
    have h1 : 0 < 1 / (s - p) + 1 / (q - p) := by
      have : 0 < s - p := by linarith
      have : 0 < q - p := by linarith
      positivity
    nlinarith [le_max_left (1:ℝ) (6*p), le_max_right (1:ℝ) (6*p)]
  refine ⟨K, hKpos, fun A B hdist => ?_⟩
  have hsp : 0 < s - p := by linarith
  have hqp : 0 < q - p := by linarith
  -- truncation of `W` from above
  set f : ℕ → Ω → ℝ := fun n ω => (W ω ⊓ (n : ℝ≥0∞)).toReal with hfdef
  have hf_nn : ∀ n, 0 ≤ᵐ[μ] f n := fun n => ae_of_all _ (fun ω => ENNReal.toReal_nonneg)
  have hf_meas : ∀ n, AEMeasurable (f n) μ := fun n =>
    ENNReal.measurable_toReal.comp_aemeasurable
      (hW.aemeasurable.inf aemeasurable_const)
  have hofReal : ∀ n ω, ENNReal.ofReal (f n ω) = W ω ⊓ (n : ℝ≥0∞) := fun n ω =>
    ENNReal.ofReal_toReal (ne_top_of_le_ne_top (ENNReal.natCast_ne_top n) inf_le_right)
  -- monotone convergence of the truncated powers
  have hmono : ∀ᵐ ω ∂μ, Monotone (fun n : ℕ => ENNReal.ofReal (f n ω) ^ p) := ae_of_all _ (fun ω => by
    intro a b hab
    change ENNReal.ofReal (f a ω) ^ p ≤ ENNReal.ofReal (f b ω) ^ p
    rw [hofReal a ω, hofReal b ω]
    exact ENNReal.rpow_le_rpow (inf_le_inf_left _ (by exact_mod_cast hab)) hp.le)
  have htendsto : ∀ᵐ ω ∂μ,
      Tendsto (fun n : ℕ => ENNReal.ofReal (f n ω) ^ p) atTop (𝓝 (W ω ^ p)) := ae_of_all _ (fun ω => by
    have hbase : Tendsto (fun n : ℕ => W ω ⊓ (n : ℝ≥0∞)) atTop (𝓝 (W ω)) := by
      by_cases hWtop : W ω = ⊤
      · rw [hWtop]
        exact tendsto_natCast_ennreal_atTop.congr' (Filter.Eventually.of_forall (fun n => by simp))
      · obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt hWtop
        exact tendsto_const_nhds.congr' (by
          filter_upwards [Filter.eventually_ge_atTop N] with n hn
          exact (inf_eq_left.mpr (hN.le.trans (by exact_mod_cast hn))).symm)
    have hcont : Tendsto (fun a : ℝ≥0∞ => a ^ p) (𝓝 (W ω)) (𝓝 (W ω ^ p)) :=
      (ENNReal.continuous_rpow_const (y := p)).tendsto (W ω)
    refine (hcont.comp hbase).congr' (Filter.Eventually.of_forall (fun n => ?_))
    simp only [Function.comp_apply, hofReal n ω])
  have hMCT := MeasureTheory.lintegral_tendsto_of_tendsto_of_monotone
    (fun n => ((hf_meas n).ennreal_ofReal).pow_const p) hmono htendsto
  -- the per-`n` bound
  have hlevel : ∀ n t, 0 < t → μ {ω | t < f n ω} ≤ μ {ω | ENNReal.ofReal t < W ω} := by
    intro n t ht
    refine measure_mono ?_
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    have h1 : ENNReal.ofReal t < ENNReal.ofReal (f n ω) :=
      (ENNReal.ofReal_lt_ofReal_iff (lt_trans ht hω)).mpr hω
    rw [hofReal n ω] at h1
    exact lt_of_lt_of_le h1 inf_le_left
  have h1 : p * (6/(s-p) + 6/(q-p)) ≤ K := by
    rw [hKdef]
    rw [show p * (6/(s-p) + 6/(q-p)) = 6*p/(s-p) + 6*p/(q-p) by ring]
    have hle : 6 * p ≤ max 1 (6 * p) := le_max_right _ _
    have h1 : 6*p/(s-p) ≤ max 1 (6*p) * (1/(s-p)) := by
      rw [mul_one_div]; exact div_le_div_of_nonneg_right hle hsp.le
    have h2 : 6*p/(q-p) ≤ max 1 (6*p) * (1/(q-p)) := by
      rw [mul_one_div]; exact div_le_div_of_nonneg_right hle hqp.le
    have h3 : max 1 (6*p) * (1/(s-p)) + max 1 (6*p) * (1/(q-p))
        = max 1 (6*p) * (1/(s-p) + 1/(q-p)) := by ring
    linarith
  have hbound : ∀ n, ∫⁻ ω, ENNReal.ofReal (f n ω) ^ p ∂μ ≤ ENNReal.ofReal K * (A + B) := by
    intro n
    rw [show (∫⁻ ω, ENNReal.ofReal (f n ω) ^ p ∂μ)
        = ∫⁻ ω, ENNReal.ofReal (f n ω ^ p) ∂μ from
      lintegral_congr (fun ω => ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hp.le)]
    rw [MeasureTheory.lintegral_rpow_eq_lintegral_meas_lt_mul μ (hf_nn n) (hf_meas n) hp]
    by_cases hAB : A + B = ⊤
    · rw [hAB, ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr hKpos))]; exact le_top
    have hstep : (∫⁻ t in Set.Ioi (0:ℝ), μ {a | t < f n a} * ENNReal.ofReal (t ^ (p-1)) ∂volume)
        ≤ ∫⁻ t in Set.Ioi (0:ℝ),
            (A + B) * (ENNReal.ofReal ((min (t^2) (Real.sqrt t)) ^ (s-p) * t ^ (p-1-s))
              + ENNReal.ofReal ((min (t^2) (Real.sqrt t)) ^ (q-p) * t ^ (p-1-q))) ∂volume := by
      refine lintegral_mono_ae ?_
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      have ht0 : 0 < t := ht
      have hx : ENNReal.ofReal ((min (t^2) (Real.sqrt t)) ^ (s-p) / t^s) * ENNReal.ofReal (t ^ (p-1))
          = ENNReal.ofReal ((min (t^2) (Real.sqrt t)) ^ (s-p) * t ^ (p-1-s)) := by
        rw [← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (min (t^2) (Real.sqrt t)) ^ (s-p) / t^s)]
        congr 1
        rw [div_eq_mul_inv, (Real.rpow_neg (le_of_lt ht0) s).symm, mul_assoc, ← Real.rpow_add ht0,
          show -s + (p - 1) = p - 1 - s by ring]
      have hy : ENNReal.ofReal ((min (t^2) (Real.sqrt t)) ^ (q-p) / t^q) * ENNReal.ofReal (t ^ (p-1))
          = ENNReal.ofReal ((min (t^2) (Real.sqrt t)) ^ (q-p) * t ^ (p-1-q)) := by
        rw [← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (min (t^2) (Real.sqrt t)) ^ (q-p) / t^q)]
        congr 1
        rw [div_eq_mul_inv, (Real.rpow_neg (le_of_lt ht0) q).symm, mul_assoc, ← Real.rpow_add ht0,
          show -q + (p - 1) = p - 1 - q by ring]
      set x := ENNReal.ofReal ((min (t^2) (Real.sqrt t)) ^ (s-p) * t ^ (p-1-s)) with hxdef
      set y := ENNReal.ofReal ((min (t^2) (Real.sqrt t)) ^ (q-p) * t ^ (p-1-q)) with hydef
      calc μ {a | t < f n a} * ENNReal.ofReal (t ^ (p-1))
          ≤ μ {a | ENNReal.ofReal t < W a} * ENNReal.ofReal (t ^ (p-1)) :=
            mul_le_mul_left (hlevel n t ht0) (ENNReal.ofReal (t ^ (p-1)))
        _ ≤ (A * ENNReal.ofReal ((min (t^2) (Real.sqrt t)) ^ (s-p) / t^s)
              + B * ENNReal.ofReal ((min (t^2) (Real.sqrt t)) ^ (q-p) / t^q))
              * ENNReal.ofReal (t ^ (p-1)) :=
            mul_le_mul_left (hdist t ht0) (ENNReal.ofReal (t ^ (p-1)))
        _ = A * x + B * y := by
            rw [add_mul, mul_assoc, mul_assoc, hx, hy]
        _ ≤ (A + B) * (x + y) := by
            have h1 : A * x ≤ A * x + A * y := le_self_add
            have h2 : B * y ≤ B * y + B * x := le_self_add
            calc A * x + B * y ≤ (A * x + A * y) + (B * y + B * x) := add_le_add h1 h2
              _ = (A + B) * (x + y) := by ring
        _ = (A + B) * (ENNReal.ofReal ((min (t^2) (Real.sqrt t)) ^ (s-p) * t ^ (p-1-s))
              + ENNReal.ofReal ((min (t^2) (Real.sqrt t)) ^ (q-p) * t ^ (p-1-q))) := by
            rw [hxdef, hydef]
    have hI : (∫⁻ t in Set.Ioi (0:ℝ), μ {a | t < f n a} * ENNReal.ofReal (t ^ (p-1)) ∂volume)
        ≤ (A + B) * (ENNReal.ofReal (6/(s-p)) + ENNReal.ofReal (6/(q-p))) := by
      refine le_trans hstep ?_
      rw [lintegral_const_mul' (A + B) _ hAB]
      refine mul_le_mul_right ?_ (A + B)
      rw [lintegral_add_left (μ := volume.restrict (Set.Ioi (0:ℝ)))
        (measurable_lam_rpow (s-p) (p-1-s))]
      exact add_le_add (lintegral_lam_rpow_le hp hps) (lintegral_lam_rpow_le hp hpq)
    calc ENNReal.ofReal p * (∫⁻ t in Set.Ioi (0:ℝ),
            μ {a | t < f n a} * ENNReal.ofReal (t ^ (p-1)) ∂volume)
        ≤ ENNReal.ofReal p * ((A + B) * (ENNReal.ofReal (6/(s-p)) + ENNReal.ofReal (6/(q-p)))) :=
          mul_le_mul_right hI _
      _ = ENNReal.ofReal (p * (6/(s-p) + 6/(q-p))) * (A + B) := by
          rw [← ENNReal.ofReal_add (div_nonneg (by norm_num) hsp.le) (div_nonneg (by norm_num) hqp.le),
            ENNReal.ofReal_mul hp.le]
          ring
      _ ≤ ENNReal.ofReal K * (A + B) := mul_le_mul_left (ENNReal.ofReal_le_ofReal h1) (A + B)
  exact le_of_tendsto hMCT (Filter.Eventually.of_forall hbound)


/-! ## Bounds for the `ℝ≥0∞`-valued maximal variation in the `σ`-finite-filtration case -/

lemma Vsup_eq_iSup_Vtr (g : ℕ → Ω → ℝ) (r : ℝ) :
    Vsup g r = fun ω => ⨆ N, SFTest.Vtr g r N ω := rfl

lemma Vsup_zero {g : ℕ → Ω → ℝ} {r : ℝ} (hr : 0 < r) (h : ∀ n, g n = 0) : Vsup g r = 0 := by
  funext ω
  refine le_antisymm ?_ bot_le
  refine iSup_le (fun N => ?_)
  unfold SFTest.Vtr
  refine iSup_le (fun u => ?_)
  refine iSup_le (fun J => ?_)
  by_cases hN : u.1 J ≤ N
  · rw [if_pos hN]
    have hz : ∀ j, |g (u.1 (j+1)) ω - g (u.1 j) ω| = 0 := fun j => by
      rw [h (u.1 (j+1)), h (u.1 j)]
      simp
    have hsum : (∑ j ∈ Finset.range J, |g (u.1 (j+1)) ω - g (u.1 j) ω| ^ r) = 0 := by
      refine Finset.sum_eq_zero (fun j _ => ?_)
      rw [hz j, Real.zero_rpow (ne_of_gt hr)]
    rw [hsum, Real.zero_rpow (ne_of_gt (div_pos one_pos hr)), ENNReal.ofReal_zero]
    exact bot_le
  · rw [if_neg hN]
    exact bot_le

/-- The off-diagonal `L^q` bound (`q > 2`) for the `ℝ≥0∞`-valued maximal variation. -/
lemma eLpNorm_Vsup_offdiag {r q : ℝ} (hr0 : 0 < r) (hr2 : 2 < r) (hq2 : 2 < q)
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) [SigmaFinite μ] [SigmaFiniteFiltration μ ℱ] (f : Ω → ℝ)
    (hf : MemLp f (ENNReal.ofReal q) μ) (hfi : Integrable f μ) :
    eLpNorm (Vsup (fun n => condExp (ℱ n) μ f) r) (ENNReal.ofReal q) μ
      ≤ ENNReal.ofReal (8 * Real.sqrt (Commons.Analysis.Probability.lepG r * SFTest.bdgZZ q))
          * eLpNorm f (ENNReal.ofReal q) μ := by
  have hG : 0 < Commons.Analysis.Probability.lepG r := Commons.Analysis.Probability.lepG_pos hr2
  have hZ : 0 < SFTest.bdgZZ q := Commons.Analysis.Probability.bdgZZ_pos hq2
  have hq0 : 0 < q := by linarith
  have hconst : (8:ℝ≥0∞) * ((ENNReal.ofReal (Commons.Analysis.Probability.lepG r)
        * ENNReal.ofReal (SFTest.bdgZZ q))^(1/2 : ℝ))
      ≤ ENNReal.ofReal (8 * Real.sqrt (Commons.Analysis.Probability.lepG r * SFTest.bdgZZ q)) := by
    rw [← ENNReal.ofReal_mul hG.le,
      show (ENNReal.ofReal (Commons.Analysis.Probability.lepG r * SFTest.bdgZZ q))^(1/2:ℝ)
        = ENNReal.ofReal (Real.sqrt (Commons.Analysis.Probability.lepG r * SFTest.bdgZZ q)) from by
      rw [Real.sqrt_eq_rpow,
        ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hG.le hZ.le) (by norm_num : (0:ℝ) ≤ 1/2)],
      show (8:ℝ≥0∞) = ENNReal.ofReal 8 by norm_num,
      ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 8)]
  change eLpNorm (fun ω => ⨆ N, SFTest.Vtr (fun n => condExp (ℱ n) μ f) r N ω)
    (ENNReal.ofReal q) μ ≤ _
  calc eLpNorm (fun ω => ⨆ N, SFTest.Vtr (fun n => condExp (ℱ n) μ f) r N ω) (ENNReal.ofReal q) μ
      ≤ (8 * ((ENNReal.ofReal (Commons.Analysis.Probability.lepG r)
          * ENNReal.ofReal (SFTest.bdgZZ q))^(1/2 : ℝ))) * eLpNorm f (ENNReal.ofReal q) μ := by
        rw [mul_assoc]
        exact Commons.Analysis.Probability.LepLp.eLpNorm_Vinf_le_decoup ℱ f hr0 hr2 hq0 hq2 hf hfi
    _ ≤ ENNReal.ofReal (8 * Real.sqrt (Commons.Analysis.Probability.lepG r * SFTest.bdgZZ q))
          * eLpNorm f (ENNReal.ofReal q) μ := mul_le_mul_left hconst _

/-- From the a.e. subadditivity of the variation: the level sets split. -/
lemma measure_gt_le_add_of_ae_le {A B C : Ω → ℝ≥0∞} (h : A ≤ᵐ[μ] B + C) {t : ℝ} :
    μ {ω | ENNReal.ofReal t < A ω} ≤ μ {ω | ENNReal.ofReal t / 2 < B ω}
      + μ {ω | ENNReal.ofReal t / 2 < C ω} := by
  have hnull : μ {ω | ¬ (A ω ≤ B ω + C ω)} = 0 := MeasureTheory.ae_iff.mp h
  have hsub : {ω | ENNReal.ofReal t < A ω} ⊆
      ({ω | ENNReal.ofReal t / 2 < B ω} ∪ {ω | ENNReal.ofReal t / 2 < C ω})
        ∪ {ω | ¬ (A ω ≤ B ω + C ω)} := by
    intro ω hω
    by_contra hcon
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_lt] at hcon
    obtain ⟨⟨h1, h2⟩, h3⟩ := hcon
    have h3' : A ω ≤ B ω + C ω := not_not.mp h3
    have hle : B ω + C ω ≤ ENNReal.ofReal t :=
      le_trans (add_le_add h1 h2) (le_of_eq (ENNReal.add_halves (ENNReal.ofReal t)))
    exact absurd (le_trans h3' hle) (not_le.mpr hω)
  calc μ {ω | ENNReal.ofReal t < A ω}
      ≤ μ (({ω | ENNReal.ofReal t / 2 < B ω} ∪ {ω | ENNReal.ofReal t / 2 < C ω})
          ∪ {ω | ¬ (A ω ≤ B ω + C ω)}) := measure_mono hsub
    _ ≤ μ ({ω | ENNReal.ofReal t / 2 < B ω} ∪ {ω | ENNReal.ofReal t / 2 < C ω})
          + μ {ω | ¬ (A ω ≤ B ω + C ω)} := measure_union_le _ _
    _ = μ ({ω | ENNReal.ofReal t / 2 < B ω} ∪ {ω | ENNReal.ofReal t / 2 < C ω}) := by rw [hnull, add_zero]
    _ ≤ μ {ω | ENNReal.ofReal t / 2 < B ω} + μ {ω | ENNReal.ofReal t / 2 < C ω} :=
        measure_union_le _ _

/-- Chebyshev plus a norm bound: the distribution bound for an `ℝ≥0∞`-valued function. -/
lemma meas_gt_le_of_eLpNorm_le {W : Ω → ℝ≥0∞} (hW : Measurable W) {s t C : ℝ} (hs : 0 < s)
    (ht : 0 < t) (hC : 0 ≤ C) (h : eLpNorm W (ENNReal.ofReal s) μ ≤ ENNReal.ofReal C) :
    μ {ω | ENNReal.ofReal t < W ω} ≤ ENNReal.ofReal (C ^ s) / ENNReal.ofReal (t ^ s) := by
  have h1 : ENNReal.ofReal t ^ s * μ {ω | ENNReal.ofReal t < W ω} ≤ ∫⁻ ω, W ω ^ s ∂μ :=
    chebyshev_ennreal hW hs.le ht
  have h2 : eLpNorm W (ENNReal.ofReal s) μ = (∫⁻ ω, W ω ^ s ∂μ) ^ (1/s : ℝ) :=
    Commons.Analysis.Probability.eLpNorm_ennreal_eq W hs
  rw [h2] at h
  have h3 : ∫⁻ ω, W ω ^ s ∂μ ≤ ENNReal.ofReal C ^ s := by
    have := ENNReal.rpow_le_rpow h (le_of_lt (by positivity : (0:ℝ) < s))
    rwa [← ENNReal.rpow_mul, show (1/s : ℝ) * s = 1 by field_simp, ENNReal.rpow_one] at this
  rw [show ENNReal.ofReal C ^ s = ENNReal.ofReal (C ^ s) from
    ENNReal.ofReal_rpow_of_nonneg hC hs.le] at h3
  have h4 : ENNReal.ofReal t ^ s * μ {ω | ENNReal.ofReal t < W ω} ≤ ENNReal.ofReal (C ^ s) :=
    le_trans h1 h3
  rw [ENNReal.ofReal_rpow_of_nonneg ht.le hs.le] at h4
  rw [ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_ne_zero_iff.mpr (by positivity : (0:ℝ) < t^s)))
    (Or.inl ENNReal.ofReal_ne_top)]
  rwa [mul_comm]

/-- Strong `L^q` bound for the maximal variation, for integrable `f`. -/
lemma eLpNorm_Vsup_offdiag_integrable {r q : ℝ} (hr0 : 0 < r) (hr2 : 2 < r) (hq2 : 2 < q)
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) [SigmaFinite μ] [SigmaFiniteFiltration μ ℱ] (f : Ω → ℝ)
    (hfi : Integrable f μ) :
    eLpNorm (Vsup (fun n => condExp (ℱ n) μ f) r) (ENNReal.ofReal q) μ
      ≤ ENNReal.ofReal (8 * Real.sqrt (Commons.Analysis.Probability.lepG r * SFTest.bdgZZ q))
          * eLpNorm f (ENNReal.ofReal q) μ := by
  by_cases hf : MemLp f (ENNReal.ofReal q) μ
  · exact eLpNorm_Vsup_offdiag hr0 hr2 hq2 ℱ f hf hfi
  · have htop : eLpNorm f (ENNReal.ofReal q) μ = ⊤ := by
      by_contra h
      exact hf (MeasureTheory.memLp_iff.mpr (lt_top_iff_ne_top.mpr h))
    have hpos : (0:ℝ) < 8 * Real.sqrt (Commons.Analysis.Probability.lepG r * SFTest.bdgZZ q) := by
      have h1 := Commons.Analysis.Probability.lepG_pos hr2
      have h2 := Commons.Analysis.Probability.bdgZZ_pos hq2
      positivity
    rw [htop, ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr hpos)]
    exact le_top

/-- The `ℝ≥0∞`-valued maximal variation dominates the `ℝ`-valued one. -/
lemma ofReal_lepingleVar_le_Vsup [SigmaFinite μ] (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (f : Ω → ℝ)
    {r : ℝ} (ω : Ω) :
    ENNReal.ofReal (Commons.Analysis.Probability.lepingleVar μ ℱ r f ω)
      ≤ Vsup (fun n => condExp (ℱ n) μ f) r ω := by
  rw [← Real.enorm_eq_ofReal (Commons.Analysis.Probability.lepingleVar_nonneg μ ℱ r f ω)]
  simpa only [Commons.Analysis.Probability.lepingleVar, Vsup] using
    SFTest.pointwise_bound (μ := μ) ℱ f r ω

/-- Monotonicity step: the `ℝ`-valued maximal variation is controlled by the `ℝ≥0∞`-valued one. -/
lemma eLpNorm_lepingleVar_le_Vsup [SigmaFinite μ] (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (f : Ω → ℝ)
    {r p : ℝ} (hr0 : 0 < r) (hp : 0 < p) :
    eLpNorm (Commons.Analysis.Probability.lepingleVar μ ℱ r f) (ENNReal.ofReal p) μ
      ≤ eLpNorm (Vsup (fun n => condExp (ℱ n) μ f) r) (ENNReal.ofReal p) μ := by
  have hLm := Commons.Analysis.Probability.measurable_lepingleVar μ ℱ hr0 f
  calc eLpNorm (Commons.Analysis.Probability.lepingleVar μ ℱ r f) (ENNReal.ofReal p) μ
      = eLpNorm (fun ω => ‖Commons.Analysis.Probability.lepingleVar μ ℱ r f ω‖ₑ)
          (ENNReal.ofReal p) μ := (eLpNorm_enorm (hf := by pw_aesm) _).symm
    _ = eLpNorm (fun ω => ENNReal.ofReal (Commons.Analysis.Probability.lepingleVar μ ℱ r f ω))
          (ENNReal.ofReal p) μ := by
        rw [show (fun ω => ‖Commons.Analysis.Probability.lepingleVar μ ℱ r f ω‖ₑ)
            = (fun ω => ENNReal.ofReal (Commons.Analysis.Probability.lepingleVar μ ℱ r f ω)) from
          funext (fun ω => Real.enorm_eq_ofReal
            (Commons.Analysis.Probability.lepingleVar_nonneg μ ℱ r f ω))]
    _ ≤ eLpNorm (Vsup (fun n => condExp (ℱ n) μ f) r) (ENNReal.ofReal p) μ :=
        Commons.Analysis.Probability.eLpNorm_le_of_le hp
          (fun ω => ofReal_lepingleVar_le_Vsup ℱ f ω)

/-! ## The a.e.-congruence of the maximal variation -/

/-- Truncated variations of a.e. equal paths are a.e. equal. -/
lemma Vtr_congr_ae {g g' : ℕ → Ω → ℝ} (h : ∀ n, g n =ᵐ[μ] g' n) (r : ℝ) (N : ℕ) :
    SFTest.Vtr g r N =ᵐ[μ] SFTest.Vtr g' r N := by
  have hsum : ∀ (u : {u : ℕ → ℕ // StrictMono u}) (J : ℕ) (ω : Ω),
      (∀ i, g i ω = g' i ω) →
      (∑ j ∈ Finset.range J, |g (u.1 (j + 1)) ω - g (u.1 j) ω| ^ r)
        = (∑ j ∈ Finset.range J, |g' (u.1 (j + 1)) ω - g' (u.1 j) ω| ^ r) :=
    fun u J ω hω => Finset.sum_congr rfl (fun j _ => by rw [hω (u.1 (j+1)), hω (u.1 j)])
  filter_upwards [MeasureTheory.ae_all_iff.mpr h] with ω hω
  simp only [SFTest.Vtr]
  refine le_antisymm (iSup_le (fun u => iSup_le (fun J => ?_)))
    (iSup_le (fun u => iSup_le (fun J => ?_)))
  · by_cases hJ : u.1 J ≤ N
    · rw [if_pos hJ, hsum u J ω hω]
      exact le_iSup_of_le u (le_iSup_of_le J (le_of_eq (by rw [if_pos hJ])))
    · rw [if_neg hJ]
      exact bot_le
  · by_cases hJ : u.1 J ≤ N
    · rw [if_pos hJ, ← hsum u J ω hω]
      exact le_iSup_of_le u (le_iSup_of_le J (le_of_eq (by rw [if_pos hJ])))
    · rw [if_neg hJ]
      exact bot_le

/-- Maximal variations of a.e. equal path families are a.e. equal. -/
lemma Vsup_congr_ae {g g' : ℕ → Ω → ℝ} (h : ∀ n, g n =ᵐ[μ] g' n) (r : ℝ) :
    Vsup g r =ᵐ[μ] Vsup g' r := by
  filter_upwards [MeasureTheory.ae_all_iff.mpr (fun N => Vtr_congr_ae h r N)] with ω hω
  simp only [Vsup]
  exact iSup_congr (fun N => hω N)


/-! ## Reduction to the `σ`-finite-filtration case -/

set_option maxHeartbeats 8000000 in
open Classical in
/-- If the `L^p` bound for the maximal variation is known for every `σ`-finite filtration (with a
constant `K` uniform in the filtration), then it holds for an arbitrary filtration. -/
lemma lepingleVar_lp_le_of_key {p r K : ℝ} (hp1 : 1 < p) (hr2 : 2 < r) (hK : 0 ≤ K)
    {Ω : Type u_1} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) [SigmaFinite μ]
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (f : Ω → ℝ) (hf : MemLp f (ENNReal.ofReal p) μ)
    (key : ∀ (ℱ' : Filtration ℕ ‹MeasurableSpace Ω›), SigmaFiniteFiltration μ ℱ' →
      Integrable f μ →
      eLpNorm (Vsup (fun n => condExp (ℱ' n) μ f) r) (ENNReal.ofReal p) μ
        ≤ ENNReal.ofReal K * eLpNorm f (ENNReal.ofReal p) μ) :
    eLpNorm (Commons.Analysis.Probability.lepingleVar μ ℱ r f) (ENNReal.ofReal p) μ
      ≤ ENNReal.ofReal (1 + 2 * K) * eLpNorm f (ENNReal.ofReal p) μ := by
  have hp0 : 0 < p := by linarith
  have hr0 : 0 < r := by linarith
  have hp1e : (1 : ENNReal) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp1.le
  have hp0e : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hp0
  have hpTe : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hKle : ENNReal.ofReal K ≤ ENNReal.ofReal (1 + 2 * K) :=
    ENNReal.ofReal_le_ofReal (by linarith)
  have hCeq : ENNReal.ofReal (1 + 2 * K) = 1 + 2 * ENNReal.ofReal K := by
    rw [ENNReal.ofReal_add (by norm_num) (by positivity),
      ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
      show ENNReal.ofReal (2:ℝ) = 2 by norm_num, show ENNReal.ofReal (1:ℝ) = 1 by norm_num]
  by_cases hInt : Integrable f μ
  · by_cases hSF : SigmaFiniteFiltration μ ℱ
    · exact le_trans (le_trans (eLpNorm_lepingleVar_le_Vsup (μ := μ) ℱ f (by linarith : (0:ℝ) < r) hp0) (key ℱ hSF hInt))
        (mul_le_mul_of_nonneg_right hKle zero_le)
    · by_cases hex : ∃ n, SigmaFinite (μ.trim (ℱ.le' n))
      · let N := Nat.find hex
        have hN : SigmaFinite (μ.trim (ℱ.le' N)) := Nat.find_spec hex
        have hfail : ∀ k < N, ¬ SigmaFinite (μ.trim (ℱ.le' k)) := fun k hk => Nat.find_min hex hk
        have hzero : ∀ k < N, condExp (ℱ k) μ f = 0 := fun k hk =>
          condExp_of_not_sigmaFinite (ℱ.le' k) (hfail k hk)
        let ℱ' : Filtration ℕ ‹MeasurableSpace Ω› :=
          { seq := fun m => ℱ (N + m)
            mono' := fun i j hij => ℱ.mono (Nat.add_le_add_left hij N)
            le' := fun m => ℱ.le' (N + m) }
        have hSF' : SigmaFiniteFiltration μ ℱ' := by
          refine ⟨fun m => ?_⟩
          haveI : SigmaFinite (μ.trim (ℱ.le' N)) := hN
          exact sigmaFiniteTrim_mono (μ := μ) (ℱ.le' (N + m)) (ℱ.mono (Nat.le_add_right N m))
        have hshift : ∀ ω, Commons.Analysis.Probability.lepingleVar μ ℱ r f ω
            ≤ |condExp (ℱ N) μ f ω| + 2 * Commons.Analysis.Probability.lepingleVar μ ℱ' r f ω := by
          intro ω
          have hz : ∀ k < N, (fun n => condExp (ℱ n) μ f ω) k = 0 := fun k hk => by
            simp only [hzero k hk, Pi.zero_apply]
          have hv := Commons.Analysis.Series.variation_shift_le (fun n => condExp (ℱ n) μ f ω) hr2 N hz
          simpa only [Commons.Analysis.Probability.lepingleVar] using hv
        set Q : Ω → ENNReal := fun ω => ⨆ N', SFTest.Vtr (fun n => condExp (ℱ' n) μ f) r N' ω with hQ
        have hQmeas : Measurable Q := by
          rw [hQ]
          exact Measurable.iSup (fun N' => SFTest.measurable_Vtr ℱ'
            (fun n => condExp (ℱ' n) μ f)
            (fun n => (stronglyMeasurable_condExp (m := ℱ' n)).measurable) r N')
        have hAmeas : AEMeasurable (fun ω => ‖condExp (ℱ N) μ f ω‖ₑ) μ :=
          (((stronglyMeasurable_condExp (m := ℱ N)).measurable.mono (ℱ.le' N) le_rfl).enorm).aemeasurable
        have h2Qmeas : AEMeasurable (fun ω => 2 * Q ω) μ :=
          (measurable_const.mul hQmeas).aemeasurable
        have hpoint : ∀ ω, ‖Commons.Analysis.Probability.lepingleVar μ ℱ r f ω‖ₑ
            ≤ ‖condExp (ℱ N) μ f ω‖ₑ + 2 * Q ω := by
          intro ω
          have hnn := Commons.Analysis.Probability.lepingleVar_nonneg μ ℱ r f ω
          have hnn' := Commons.Analysis.Probability.lepingleVar_nonneg μ ℱ' r f ω
          have h1 := hshift ω
          have hQp : ENNReal.ofReal (Commons.Analysis.Probability.lepingleVar μ ℱ' r f ω) ≤ Q ω := by
            rw [hQ, ← Real.enorm_eq_ofReal hnn']
            simpa only [Commons.Analysis.Probability.lepingleVar] using
              SFTest.pointwise_bound (μ := μ) ℱ' f r ω
          calc ‖Commons.Analysis.Probability.lepingleVar μ ℱ r f ω‖ₑ
              = ENNReal.ofReal (Commons.Analysis.Probability.lepingleVar μ ℱ r f ω) :=
                Real.enorm_eq_ofReal hnn
            _ ≤ ENNReal.ofReal (|condExp (ℱ N) μ f ω|
                  + 2 * Commons.Analysis.Probability.lepingleVar μ ℱ' r f ω) :=
                ENNReal.ofReal_le_ofReal h1
            _ = ENNReal.ofReal |condExp (ℱ N) μ f ω|
                  + 2 * ENNReal.ofReal (Commons.Analysis.Probability.lepingleVar μ ℱ' r f ω) := by
                rw [ENNReal.ofReal_add (abs_nonneg _) (by positivity),
                  ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
                  show ENNReal.ofReal (2:ℝ) = 2 by norm_num]
            _ = ‖condExp (ℱ N) μ f ω‖ₑ
                  + 2 * ENNReal.ofReal (Commons.Analysis.Probability.lepingleVar μ ℱ' r f ω) := by
                rw [Real.enorm_eq_ofReal_abs]
            _ ≤ ‖condExp (ℱ N) μ f ω‖ₑ + 2 * Q ω :=
                add_le_add le_rfl (mul_le_mul_of_nonneg_left hQp (by norm_num))
        have hQV : Q = Vsup (fun n => condExp (ℱ' n) μ f) r := rfl
        have hQbound : eLpNorm Q (ENNReal.ofReal p) μ
            ≤ ENNReal.ofReal K * eLpNorm f (ENNReal.ofReal p) μ := by
          rw [hQV]
          exact key ℱ' hSF' hInt
        have hLm := Commons.Analysis.Probability.measurable_lepingleVar μ ℱ
          (by linarith : (0:ℝ) < r) f
        have hmain : eLpNorm (Commons.Analysis.Probability.lepingleVar μ ℱ r f) (ENNReal.ofReal p) μ
            ≤ eLpNorm f (ENNReal.ofReal p) μ
              + 2 * (ENNReal.ofReal K * eLpNorm f (ENNReal.ofReal p) μ) := by
          have hMink := ENNReal.lintegral_Lp_add_le (p := p) hAmeas h2Qmeas (by linarith : (1:ℝ) ≤ p)
          calc eLpNorm (Commons.Analysis.Probability.lepingleVar μ ℱ r f) (ENNReal.ofReal p) μ
              = eLpNorm (fun ω => ‖Commons.Analysis.Probability.lepingleVar μ ℱ r f ω‖ₑ)
                  (ENNReal.ofReal p) μ := (eLpNorm_enorm (hf := by pw_aesm) _).symm
            _ ≤ eLpNorm (fun ω => ‖condExp (ℱ N) μ f ω‖ₑ + 2 * Q ω) (ENNReal.ofReal p) μ :=
                Commons.Analysis.Probability.eLpNorm_le_of_le hp0 hpoint
            _ = (∫⁻ ω, (‖condExp (ℱ N) μ f ω‖ₑ + 2 * Q ω) ^ p ∂μ) ^ (1 / p) :=
                Commons.Analysis.Probability.eLpNorm_ennreal_eq _ hp0
            _ ≤ (∫⁻ ω, ‖condExp (ℱ N) μ f ω‖ₑ ^ p ∂μ) ^ (1 / p)
                  + (∫⁻ ω, (2 * Q ω) ^ p ∂μ) ^ (1 / p) := hMink
            _ = eLpNorm (fun ω => ‖condExp (ℱ N) μ f ω‖ₑ) (ENNReal.ofReal p) μ
                  + eLpNorm (fun ω => 2 * Q ω) (ENNReal.ofReal p) μ := by
                rw [Commons.Analysis.Probability.eLpNorm_ennreal_eq _ hp0,
                  Commons.Analysis.Probability.eLpNorm_ennreal_eq _ hp0]
            _ = eLpNorm (condExp (ℱ N) μ f) (ENNReal.ofReal p) μ
                  + 2 * eLpNorm Q (ENNReal.ofReal p) μ := by
                rw [eLpNorm_enorm (hf := by pw_aesm),
                  Commons.MeasureTheory.Lp.eLpNorm_const_mul_ennreal (c := 2) (by norm_num) hp0e hpTe]
            _ ≤ eLpNorm f (ENNReal.ofReal p) μ
                  + 2 * (ENNReal.ofReal K * eLpNorm f (ENNReal.ofReal p) μ) := by
                refine add_le_add ?_ (mul_le_mul_of_nonneg_left ?_ (by norm_num))
                · exact eLpNorm_condExp_le_eLpNorm (m := ℱ N) f hp1e
                · exact hQbound
        exact le_trans hmain (le_of_eq (by
          rw [hCeq]
          rw [show eLpNorm f (ENNReal.ofReal p) μ
                + 2 * (ENNReal.ofReal K * eLpNorm f (ENNReal.ofReal p) μ)
              = (1 + 2 * ENNReal.ofReal K) * eLpNorm f (ENNReal.ofReal p) μ from by ring]))
      · have h0 : ∀ n, condExp (ℱ n) μ f = 0 := fun n =>
          condExp_of_not_sigmaFinite (ℱ.le' n) (fun hsf => hex ⟨n, hsf⟩)
        rw [Commons.Analysis.Probability.lepingleVar_eq_zero μ ℱ hr0 f h0, eLpNorm_zero]
        exact zero_le
  · have h0 : ∀ n, condExp (ℱ n) μ f = 0 := fun n => condExp_of_not_integrable hInt
    rw [Commons.Analysis.Probability.lepingleVar_eq_zero μ ℱ hr0 f h0, eLpNorm_zero]
    exact zero_le


lemma ENNReal.min_add_le_min_add_min (b c k : ENNReal) :
    min (b + c) k ≤ min b k + min c k := by
  rcases le_total b k with hb | hb
  · rcases le_total c k with hc | hc
    · calc min (b + c) k ≤ b + c := min_le_left _ _
        _ ≤ min b k + min c k := add_le_add (le_min le_rfl hb) (le_min le_rfl hc)
    · have h1 : k = min c k := (min_eq_right hc).symm
      calc min (b + c) k ≤ k := min_le_right _ _
        _ = min c k := h1
        _ ≤ min b k + min c k := le_add_left (le_refl _)
  · have h1 : k = min b k := (min_eq_right hb).symm
    calc min (b + c) k ≤ k := min_le_right _ _
      _ = min b k := h1
      _ ≤ min b k + min c k := le_add_right (le_refl _)

lemma iSup_min_natCast' (a : ENNReal) : (⨆ k : ℕ, min a (k : ENNReal)) = a := by
  refine le_antisymm (iSup_le (fun k => min_le_left _ _)) ?_
  rcases eq_or_ne a ⊤ with h | h
  · rw [h]
    rw [show (fun k : ℕ => min (⊤:ENNReal) (k:ENNReal)) = (fun k : ℕ => (k:ENNReal)) from
      funext (fun k => top_inf_eq (k : ENNReal))]
    exact le_of_eq ENNReal.iSup_natCast.symm
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, a ≤ (k : ENNReal) := by
      obtain ⟨k, hk⟩ := exists_nat_gt a.toReal
      exact ⟨k, by
        rw [← ENNReal.ofReal_toReal h, ← ENNReal.ofReal_natCast]
        exact ENNReal.ofReal_le_ofReal hk.le⟩
    exact le_iSup_of_le k (by rw [min_eq_left hk])

/-! ## The small-`p` bound in the `σ`-finite-filtration case -/

set_option maxHeartbeats 8000000 in
lemma Vsup_lp_le_small_p_sf {p r A0 : ℝ} (hr2 : 2 < r) (hA0 : 0 < A0) (hp1 : 1 < p) (hp2 : p ≤ 2)
    (hweakV : ∀ {Ω : Type u_1} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) [SigmaFinite μ]
      (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) [SigmaFiniteFiltration μ ℱ] (f : Ω → ℝ),
      Integrable f μ → ∀ t : ℝ, 0 < t →
        μ {ω | ENNReal.ofReal t < Vsup (fun n => condExp (ℱ n) μ f) r ω}
          ≤ ENNReal.ofReal (A0 / t) * eLpNorm f 1 μ)
    (hinterp : ∀ {α : Type u_1} [MeasurableSpace α] {ν : MeasureTheory.Measure α}
      (T : (α → ℝ) → α → ℝ) (hTnn : ∀ f, 0 ≤ T f) (hTmeas : ∀ f, Measurable (T f))
      (hsub : ∀ f g : α → ℝ, T (f + g) ≤ᵐ[ν] T f + T g)
      {B0 B1 p' : ℝ} (hB0 : 0 < B0) (hB1 : 0 < B1) (hp1' : 1 < p') (hp4' : p' < 4)
      (hw : ∀ f : α → ℝ, Measurable f → Integrable f ν → ∀ t : ℝ, 0 < t →
        ν {ω | t < T f ω} ≤ ENNReal.ofReal (B0 / t) * eLpNorm f 1 ν)
      (hs : ∀ f : α → ℝ, Measurable f → Integrable f ν →
        eLpNorm (T f) (ENNReal.ofReal 4) ν ≤ ENNReal.ofReal B1 * eLpNorm f (ENNReal.ofReal 4) ν),
      ∀ f : α → ℝ, Measurable f → MemLp f (ENNReal.ofReal p') ν → Integrable f ν →
        eLpNorm (T f) (ENNReal.ofReal p') ν
          ≤ ENNReal.ofReal ((p' * (2 * B0 / (p' - 1) + 2 ^ (4:ℝ) * B1 ^ (4:ℝ) / ((4:ℝ) - p'))) ^ (1 / p'))
            * eLpNorm f (ENNReal.ofReal p') ν) :
    ∃ K : ℝ, 0 < K ∧ ∀ {Ω : Type u_1} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) [SigmaFinite μ]
      (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) [SigmaFiniteFiltration μ ℱ] (f : Ω → ℝ),
      Integrable f μ → MemLp f (ENNReal.ofReal p) μ →
      eLpNorm (Vsup (fun n => condExp (ℱ n) μ f) r) (ENNReal.ofReal p) μ
        ≤ ENNReal.ofReal K * eLpNorm f (ENNReal.ofReal p) μ := by
  classical
  have hp0 : 0 < p := lt_trans zero_lt_one hp1
  have hp4 : p < 4 := by linarith
  set A1 : ℝ := 8 * Real.sqrt (Commons.Analysis.Probability.lepG r * SFTest.bdgZZ 4) with hA1
  have hA1pos : 0 < A1 := by
    rw [hA1]
    have h1 := Commons.Analysis.Probability.lepG_pos hr2
    have h2 := Commons.Analysis.Probability.bdgZZ_pos (by norm_num : (2:ℝ) < 4)
    positivity
  have hKpos : 0 < (p * (2 * A0 / (p - 1) + 2 ^ (4:ℝ) * A1 ^ (4:ℝ) / ((4:ℝ) - p))) ^ (1 / p) := by
    refine Real.rpow_pos_of_pos ?_ _
    have h2 : 0 < 2 * A0 / (p - 1) := by positivity
    have h3 : 0 < 2 ^ (4:ℝ) * A1 ^ (4:ℝ) / ((4:ℝ) - p) := by positivity
    exact mul_pos hp0 (add_pos h2 h3)
  refine ⟨(p * (2 * A0 / (p - 1) + 2 ^ (4:ℝ) * A1 ^ (4:ℝ) / ((4:ℝ) - p))) ^ (1 / p), hKpos, ?_⟩
  intro Ω _ μ _ ℱ _ f hfi hf
  have hp0e : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hp0
  have hpTe : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  -- a measurable representative of `f`
  have hfm : AEMeasurable f μ := hfi.aestronglyMeasurable.aemeasurable
  set f₀ : Ω → ℝ := AEMeasurable.mk f hfm with hf₀
  have hf₀meas : Measurable f₀ := hfm.measurable_mk
  have hf₀ae : f =ᵐ[μ] f₀ := hfm.ae_eq_mk
  have hf₀i : Integrable f₀ μ := (integrable_congr hf₀ae).mp hfi
  have hf₀mp : MemLp f₀ (ENNReal.ofReal p) μ :=
    (MeasureTheory.memLp_iff.mpr (by rw [← eLpNorm_congr_ae hf₀ae]; exact hf.eLpNorm_lt_top))
  have hcong : eLpNorm (Vsup (fun n => condExp (ℱ n) μ f) r) (ENNReal.ofReal p) μ
      = eLpNorm (Vsup (fun n => condExp (ℱ n) μ f₀) r) (ENNReal.ofReal p) μ :=
    eLpNorm_congr_ae (Vsup_congr_ae (fun n => condExp_congr_ae hf₀ae) r)
  rw [hcong]
  rw [eLpNorm_congr_ae hf₀ae]
  -- monotone convergence in the truncation parameter
  have hsup_eq : eLpNorm (Vsup (fun n => condExp (ℱ n) μ f₀) r) (ENNReal.ofReal p) μ
      = ⨆ k : ℕ, eLpNorm (fun ω =>
          min (Vsup (fun n => condExp (ℱ n) μ f₀) r ω) (k : ENNReal))
          (ENNReal.ofReal p) μ := by
    rw [← Commons.Analysis.MeasureTheory.eLpNorm_iSup_of_monotone hp0e hpTe
      (fun k => (measurable_Vsup ℱ (fun n => condExp (ℱ n) μ f₀)
        (fun n => (stronglyMeasurable_condExp (m := ℱ n)).measurable) r).min measurable_const)
      (fun k l hkl ω => min_le_min le_rfl (by exact_mod_cast hkl))]
    congr 1
    funext ω
    exact (iSup_min_natCast' (Vsup (fun n => condExp (ℱ n) μ f₀) r ω)).symm
  rw [hsup_eq]
  refine iSup_le (fun k => ?_)
  -- the truncated operator, patched outside the integrable functions
  set Tk : (Ω → ℝ) → Ω → ℝ := fun g ω =>
    if Integrable g μ then (min (Vsup (fun n => condExp (ℱ n) μ g) r ω) (k : ENNReal)).toReal
    else (k : ℝ) with hTk
  have hTk_le : ∀ (g : Ω → ℝ) (ω : Ω), Tk g ω ≤ (k : ℝ) := by
    intro g ω
    by_cases hg : Integrable g μ
    · simp only [hTk, if_pos hg]
      exact ENNReal.toReal_mono (by simp) (min_le_right _ _)
    · simp only [hTk, if_neg hg]
      exact le_rfl
  have hTk_nn : ∀ (g : Ω → ℝ) (ω : Ω), 0 ≤ Tk g ω := by
    intro g ω
    by_cases hg : Integrable g μ
    · simp only [hTk, if_pos hg]
      exact ENNReal.toReal_nonneg
    · simp only [hTk, if_neg hg]
      positivity
  have hTnn : ∀ g : Ω → ℝ, 0 ≤ Tk g := fun g ω => hTk_nn g ω
  have hTmeas : ∀ g : Ω → ℝ, Measurable (Tk g) := by
    intro g
    by_cases hg : Integrable g μ
    · simp only [hTk, if_pos hg]
      exact ((measurable_Vsup ℱ (fun n => condExp (ℱ n) μ g)
        (fun n => (stronglyMeasurable_condExp (m := ℱ n)).measurable) r).min measurable_const).ennreal_toReal
    · simp only [hTk, if_neg hg]
      exact measurable_const
  -- subadditivity of the unpatched truncation, on integrable pairs
  have hVksub : ∀ g h : Ω → ℝ, Integrable g μ → Integrable h μ →
      Tk (g + h) ≤ᵐ[μ] Tk g + Tk h := by
    intro g h hg hh
    have hsub := Vsup_add_le_ae (μ := μ) ℱ (le_of_lt (by linarith : (1:ℝ) < r))
      (fun n => condExp_add hg hh (ℱ n))
    simp only [hTk, if_pos hg, if_pos hh, if_pos (hg.add hh)]
    filter_upwards [hsub] with ω hω
    have hmin : min (Vsup (fun n => condExp (ℱ n) μ (g+h)) r ω) (k : ENNReal)
        ≤ min (Vsup (fun n => condExp (ℱ n) μ g) r ω) (k : ENNReal)
          + min (Vsup (fun n => condExp (ℱ n) μ h) r ω) (k : ENNReal) :=
      le_trans (min_le_min hω le_rfl) (ENNReal.min_add_le_min_add_min _ _ _)
    calc (min (Vsup (fun n => condExp (ℱ n) μ (g+h)) r ω) (k : ENNReal)).toReal
        ≤ (min (Vsup (fun n => condExp (ℱ n) μ g) r ω) (k : ENNReal)
            + min (Vsup (fun n => condExp (ℱ n) μ h) r ω) (k : ENNReal)).toReal :=
          ENNReal.toReal_mono (by simp) hmin
      _ = (min (Vsup (fun n => condExp (ℱ n) μ g) r ω) (k : ENNReal)).toReal
            + (min (Vsup (fun n => condExp (ℱ n) μ h) r ω) (k : ENNReal)).toReal :=
          ENNReal.toReal_add (by simp) (by simp)
  have hTsub : ∀ g h : Ω → ℝ, Tk (g + h) ≤ᵐ[μ] Tk g + Tk h := by
    intro g h
    by_cases hg : Integrable g μ
    · by_cases hh : Integrable h μ
      · exact hVksub g h hg hh
      · filter_upwards with ω
        have h1 : Tk (g + h) ω ≤ (k : ℝ) := hTk_le _ _
        have h2 : Tk h ω = (k : ℝ) := by simp only [hTk, if_neg hh]
        have h3 : 0 ≤ Tk g ω := hTk_nn _ _
        simp only [Pi.add_apply]
        rw [h2]; linarith
    · filter_upwards with ω
      have h1 : Tk (g + h) ω ≤ (k : ℝ) := hTk_le _ _
      have h2 : Tk g ω = (k : ℝ) := by simp only [hTk, if_neg hg]
      have h3 : 0 ≤ Tk h ω := hTk_nn _ _
      simp only [Pi.add_apply]
      rw [h2]; linarith
  have hTweak : ∀ g : Ω → ℝ, Measurable g → Integrable g μ → ∀ t : ℝ, 0 < t →
      μ {ω | t < Tk g ω} ≤ ENNReal.ofReal (A0 / t) * eLpNorm g 1 μ := by
    intro g hgm hgi t ht
    have hfun : Tk g = fun ω => (min (Vsup (fun n => condExp (ℱ n) μ g) r ω) (k : ENNReal)).toReal := by
      funext ω; simp only [hTk, if_pos hgi]
    rw [hfun]
    refine le_trans (measure_mono ?_) (hweakV μ ℱ g hgi t ht)
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    have h1 : ENNReal.ofReal t < min (Vsup (fun n => condExp (ℱ n) μ g) r ω) (k : ENNReal) :=
      (ENNReal.ofReal_lt_iff_lt_toReal ht.le (by simp)).mpr hω
    exact lt_of_lt_of_le h1 (min_le_left _ _)
  have hTstrong : ∀ g : Ω → ℝ, Measurable g → Integrable g μ →
      eLpNorm (Tk g) (ENNReal.ofReal 4) μ ≤ ENNReal.ofReal A1 * eLpNorm g (ENNReal.ofReal 4) μ := by
    intro g hgm hgi
    have hfun : Tk g = fun ω => (min (Vsup (fun n => condExp (ℱ n) μ g) r ω) (k : ENNReal)).toReal := by
      funext ω; simp only [hTk, if_pos hgi]
    rw [hfun]
    have hbridge : ∀ ω, ‖(min (Vsup (fun n => condExp (ℱ n) μ g) r ω) (k : ENNReal)).toReal‖ₑ
        = min (Vsup (fun n => condExp (ℱ n) μ g) r ω) (k : ENNReal) := by
      intro ω
      rw [Real.enorm_eq_ofReal ENNReal.toReal_nonneg]
      exact ENNReal.ofReal_toReal (by simp)
    refine le_trans ?_ (eLpNorm_Vsup_offdiag_integrable (by linarith : (0:ℝ) < r) hr2
      (by norm_num : (2:ℝ) < 4) ℱ g hgi)
    have hTm : Measurable (fun ω => (min (Vsup (fun n => condExp (ℱ n) μ g) r ω)
        (k : ENNReal)).toReal) := hfun ▸ hTmeas g
    rw [← eLpNorm_enorm (hf := hTm.aestronglyMeasurable)]
    refine Commons.Analysis.Probability.eLpNorm_le_of_le (by norm_num : (0:ℝ) < 4) (fun ω => ?_)
    rw [hbridge ω]
    exact min_le_left _ _
  have hmain := hinterp Tk hTnn hTmeas hTsub hA0 hA1pos hp1 hp4 hTweak hTstrong f₀ hf₀meas hf₀mp hf₀i
  have hfun₀ : Tk f₀ = fun ω => (min (Vsup (fun n => condExp (ℱ n) μ f₀) r ω) (k : ENNReal)).toReal := by
    funext ω; simp only [hTk, if_pos hf₀i]
  have hbridgef : ∀ ω, ‖min (Vsup (fun n => condExp (ℱ n) μ f₀) r ω) (k : ENNReal)‖ₑ = ‖Tk f₀ ω‖ₑ := by
    intro ω
    rw [enorm_eq_self]
    simp only [hfun₀]
    rw [Real.enorm_eq_ofReal ENNReal.toReal_nonneg]
    exact (ENNReal.ofReal_toReal (by simp)).symm
  have hbridgek : eLpNorm (fun ω => min (Vsup (fun n => condExp (ℱ n) μ f₀) r ω) (k : ENNReal))
      (ENNReal.ofReal p) μ = eLpNorm (Tk f₀) (ENNReal.ofReal p) μ := by
    rw [← eLpNorm_enorm (hf := ((measurable_Vsup ℱ (fun n => condExp (ℱ n) μ f₀)
      (fun n => (stronglyMeasurable_condExp (m := ℱ n)).measurable) r).min
        measurable_const).aestronglyMeasurable)]
    rw [← eLpNorm_enorm (f := Tk f₀) (hf := (hTmeas f₀).aestronglyMeasurable)]
    exact eLpNorm_congr_ae (Filter.Eventually.of_forall (fun ω => hbridgef ω))
  exact le_trans (le_of_eq hbridgek) hmain


set_option maxHeartbeats 8000000 in
theorem final_assembly {p r : ℝ} (hp : 1 < p) (hr : 2 < r) {A0 : ℝ} (hA0 : 0 < A0)
    (hweakV : ∀ {Ω : Type u_1} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) [SigmaFinite μ]
      (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) [SigmaFiniteFiltration μ ℱ] (f : Ω → ℝ),
      Integrable f μ → ∀ t : ℝ, 0 < t →
        μ {ω | ENNReal.ofReal t < Vsup (fun n => condExp (ℱ n) μ f) r ω}
          ≤ ENNReal.ofReal (A0 / t) * eLpNorm f 1 μ)
    (hinterp : ∀ {α : Type u_1} [MeasurableSpace α] {ν : MeasureTheory.Measure α}
      (T : (α → ℝ) → α → ℝ) (hTnn : ∀ f, 0 ≤ T f) (hTmeas : ∀ f, Measurable (T f))
      (hsub : ∀ f g : α → ℝ, T (f + g) ≤ᵐ[ν] T f + T g)
      {B0 B1 p' : ℝ} (hB0 : 0 < B0) (hB1 : 0 < B1) (hp1' : 1 < p') (hp4' : p' < 4)
      (hw : ∀ f : α → ℝ, Measurable f → Integrable f ν → ∀ t : ℝ, 0 < t →
        ν {ω | t < T f ω} ≤ ENNReal.ofReal (B0 / t) * eLpNorm f 1 ν)
      (hs : ∀ f : α → ℝ, Measurable f → Integrable f ν →
        eLpNorm (T f) (ENNReal.ofReal 4) ν ≤ ENNReal.ofReal B1 * eLpNorm f (ENNReal.ofReal 4) ν),
      ∀ f : α → ℝ, Measurable f → MemLp f (ENNReal.ofReal p') ν → Integrable f ν →
        eLpNorm (T f) (ENNReal.ofReal p') ν
          ≤ ENNReal.ofReal ((p' * (2 * B0 / (p' - 1) + 2 ^ (4:ℝ) * B1 ^ (4:ℝ) / ((4:ℝ) - p'))) ^ (1 / p'))
            * eLpNorm f (ENNReal.ofReal p') ν) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type u_1} {m : MeasurableSpace Ω} (μ : MeasureTheory.Measure Ω)
      [MeasureTheory.SigmaFinite μ] (F : MeasureTheory.Filtration ℕ m) (f : Ω → ℝ),
      MeasureTheory.MemLp f (ENNReal.ofReal p) μ →
      MeasureTheory.eLpNorm (fun ω => ⨆ (u : {u : ℕ → ℕ // StrictMono u}) (J : ℕ),
        (Finset.sum (Finset.range J) (fun j =>
          |(MeasureTheory.condExp (F (u.1 (j + 1))) μ f) ω
            - (MeasureTheory.condExp (F (u.1 j)) μ f) ω| ^ r)) ^ (1 / r))
        (ENNReal.ofReal p) μ
        ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm f (ENNReal.ofReal p) μ := by
  by_cases hp2 : 2 < p
  · exact Commons.Analysis.Probability.lepingle_lp_gt_two hp2 hr
  · have hp2' : p ≤ 2 := le_of_not_gt hp2
    obtain ⟨K, hK, hKbound⟩ :=
      Vsup_lp_le_small_p_sf (p := p) (r := r) (A0 := A0) hr hA0 hp hp2' hweakV hinterp
    refine ⟨1 + 2 * K, by linarith, ?_⟩
    intro Ω _ μ _ F f hf
    change eLpNorm (Commons.Analysis.Probability.lepingleVar μ F r f) (ENNReal.ofReal p) μ
      ≤ ENNReal.ofReal (1 + 2 * K) * eLpNorm f (ENNReal.ofReal p) μ
    refine lepingleVar_lp_le_of_key hp hr (by linarith) μ F f hf ?_
    intro ℱ' hsf hin
    haveI : SigmaFiniteFiltration μ ℱ' := hsf
    exact hKbound μ ℱ' f hin hf


set_option maxHeartbeats 8000000 in
/-- The `r`-variation of the path of a martingale family agrees with `Vsup`. -/
lemma Vsup_eq_VpathR_aux {Ω : Type*} [MeasurableSpace Ω] (g : ℕ → Ω → ℝ) (r : ℝ) (ω : Ω) :
    Vsup g r ω = VpathR (fun n => g n ω) r := by
  rw [Vsup_eq_Vpath]
  rfl

/-- Arithmetic identity used to evaluate the jump-bound terms. -/
theorem jump_term_algebra_aux {θ q t Cj A : ℝ} (ht : 0 < t) (hA : 0 < A)
    (hq : q = (2:ℝ)^(1 - θ/2)) :
    ∀ k : ℕ, Cj / ((t / 2^(k+1)) * Real.sqrt (A * 2^(θ*k)))
      = (2 * Cj / (t * Real.sqrt A)) * q^k := by
  intro k
  have h2 : (0:ℝ) < 2 := two_pos
  have h2θk : (0:ℝ) < 2 ^ (θ * k) := Real.rpow_pos_of_pos h2 _
  have hY : (0:ℝ) < 2 ^ (θ * k / 2) := Real.rpow_pos_of_pos h2 _
  have hX : (0:ℝ) < 2 ^ (k - θ * k / 2) := Real.rpow_pos_of_pos h2 _
  have hsqrtθ : Real.sqrt (2 ^ (θ * k)) = 2 ^ (θ * k / 2) := by
    refine (Real.sqrt_eq_iff_mul_self_eq h2θk.le hY.le).mpr ?_
    have e : θ * k / 2 + θ * k / 2 = θ * k := by ring
    rw [← Real.rpow_add h2, e]
  have hsq : Real.sqrt (A * 2 ^ (θ * k)) = Real.sqrt A * 2 ^ (θ * k / 2) := by
    rw [Real.sqrt_mul hA.le, hsqrtθ]
  have hqk : q ^ k = 2 ^ (k - θ * k / 2) := by
    have e : (1 - θ / 2) * (k : ℝ) = (k : ℝ) - θ * k / 2 := by ring
    rw [hq, ← Real.rpow_natCast _ k, ← Real.rpow_mul h2.le, e]
  have h2k : (2:ℝ)^(k+1) = 2 * (2 ^ (k - θ * k / 2) * 2 ^ (θ * k / 2)) := by
    have e : (k : ℝ) - θ * k / 2 + θ * k / 2 = (k : ℝ) := by ring
    rw [pow_succ, ← Real.rpow_natCast 2 k, ← Real.rpow_add h2, e]
    ring
  have hS : Real.sqrt A ≠ 0 := fun h => hA.ne' ((Real.sqrt_eq_zero hA.le).mp h)
  have hd : (2:ℝ) * 2 ^ (k - θ * k / 2) * 2 ^ (θ * k / 2) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hX.ne') hY.ne'
  rw [hsq, h2k, hqk]
  field_simp [hd, ne_of_gt ht, hS, hX.ne', hY.ne']

theorem weak_type_one_Vsup_aux {r : ℝ} (hr : 2 < r) :
    ∃ A0 : ℝ, 0 < A0 ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
      [MeasureTheory.SigmaFinite μ] (ℱ : MeasureTheory.Filtration ℕ ‹MeasurableSpace Ω›)
      [MeasureTheory.SigmaFiniteFiltration μ ℱ] (f : Ω → ℝ),
      MeasureTheory.Integrable f μ →
      ∀ t : ℝ, 0 < t →
        μ {ω | ENNReal.ofReal t < Work.Analysis.Probability.Vsup (fun n => MeasureTheory.condExp (ℱ n) μ f) r ω}
          ≤ ENNReal.ofReal (A0 / t) * MeasureTheory.eLpNorm f 1 μ := by
  classical
  obtain ⟨Cj, hCjpos, hjump⟩ := jump_count_weak_one
  set θ : ℝ := (r + 2) / 2 with hθdef
  have hθ2 : 2 < θ := by rw [hθdef]; linarith
  have hθr : θ < r := by rw [hθdef]; linarith
  set A : ℝ := (1 - (2:ℝ)^(θ-r)) / 2^r with hAdef
  have hApos : 0 < A := by
    rw [hAdef]
    have h1 : (2:ℝ)^(θ-r) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    positivity
  set q : ℝ := (2:ℝ)^(1 - θ/2) with hqdef
  have hqpos : 0 < q := by rw [hqdef]; positivity
  have hqlt : q < 1 := by
    rw [hqdef]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  set A0 : ℝ := 2 + 2 * Cj / (Real.sqrt A * (1 - q)) with hA0def
  have hA0pos : 0 < A0 := by
    rw [hA0def]
    have h1 : 0 < 1 - q := by linarith
    positivity
  refine ⟨A0, hA0pos, ?_⟩
  intro Ω instΩ μ instμ ℱ instℱ f hf t ht
  set g : ℕ → Ω → ℝ := fun n => condExp (ℱ n) μ f with hg
  set Mstar : Ω → ENNReal := fun ω => ⨆ n : ℕ, ‖g n ω‖ₑ with hM
  -- Doob's inequality
  have hdoob : μ {ω | ENNReal.ofReal (t/2) < Mstar ω}
      ≤ ENNReal.ofReal ((t/2)⁻¹) * eLpNorm f 1 μ :=
    doob_maximal_weak_sigmaFinite ℱ f hf (by linarith)
  -- Decompose the level set
  have hdecomp : μ {ω | ENNReal.ofReal t < Vsup g r ω}
      ≤ μ {ω | ENNReal.ofReal (t/2) < Mstar ω}
        + μ ({ω | ENNReal.ofReal t < Vsup g r ω} ∩ {ω | Mstar ω ≤ ENNReal.ofReal (t/2)}) := by
    refine le_trans (measure_mono ?_) (measure_union_le _ _)
    intro ω hω
    by_cases h : ENNReal.ofReal (t/2) < Mstar ω
    · exact Or.inl h
    · exact Or.inr ⟨hω, not_lt.mp h⟩
  -- the second term is controlled by the jump counts
  have hkey : μ ({ω | ENNReal.ofReal t < Vsup g r ω} ∩ {ω | Mstar ω ≤ ENNReal.ofReal (t/2)})
      ≤ ∑' k : ℕ, μ {ω | ENNReal.ofReal (A * 2^(θ*k)) < Jcount g (t / 2^(k+1)) ω} := by
    refine le_trans (measure_mono ?_) (measure_iUnion_le _)
    rintro ω ⟨hV, hMω⟩
    -- the path stays in `[-t/2, t/2]`
    have hpath : ∀ n, |g n ω| ≤ t/2 := by
      intro n
      have h1 : ‖g n ω‖ₑ ≤ Mstar ω := le_iSup (fun n => ‖g n ω‖ₑ) n
      have h2 : ‖g n ω‖ₑ ≤ ENNReal.ofReal (t/2) := le_trans h1 hMω
      rw [Real.enorm_eq_ofReal_abs] at h2
      exact (ENNReal.ofReal_le_ofReal_iff (by linarith)).mp h2
    have hrange : ∀ s s', |(fun n => g n ω) s' - (fun n => g n ω) s| ≤ t := by
      intro s s'
      calc |g s' ω - g s ω| ≤ |g s' ω| + |g s ω| := by
              simpa [sub_eq_add_neg] using abs_add_le (g s' ω) (-(g s ω))
        _ ≤ t/2 + t/2 := add_le_add (hpath s') (hpath s)
        _ = t := by ring
    have hV' : ENNReal.ofReal t < VpathR (fun n => g n ω) r := by
      rw [← Vsup_eq_VpathR_aux]; exact hV
    obtain ⟨k, hk⟩ := exists_level_of_Vpath_gt_theta (fun n => g n ω) (by linarith) ht hθ2 hθr hrange hV'
    refine Set.mem_iUnion.mpr ⟨k, ?_⟩
    have : A * 2^(θ*k) = ((1 - (2:ℝ)^(θ-r)) / 2^r) * 2^(θ*k) := by rw [hAdef]
    rw [this]
    exact hk
  -- the jump bound at each level
  have hterm : ∀ k : ℕ,
      μ {ω | ENNReal.ofReal (A * 2^(θ*k)) < Jcount g (t / 2^(k+1)) ω}
        ≤ ENNReal.ofReal (2 * Cj / (t * Real.sqrt A)) * (ENNReal.ofReal q)^k * eLpNorm f 1 μ := by
    intro k
    have hlam : 0 < t / 2^(k+1) := by positivity
    have hy : 0 < A * 2^(θ*k) := by positivity
    have h1 := hjump μ ℱ f hf (t / 2^(k+1)) hlam (A * 2^(θ*k)) hy
    rw [jump_term_algebra_aux ht hApos hqdef k] at h1
    refine le_trans h1 (le_of_eq ?_)
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hqpos.le, mul_assoc]
  calc μ {ω | ENNReal.ofReal t < Vsup g r ω}
      ≤ μ {ω | ENNReal.ofReal (t/2) < Mstar ω}
        + μ ({ω | ENNReal.ofReal t < Vsup g r ω} ∩ {ω | Mstar ω ≤ ENNReal.ofReal (t/2)}) := hdecomp
    _ ≤ ENNReal.ofReal ((t/2)⁻¹) * eLpNorm f 1 μ
        + ∑' k : ℕ, μ {ω | ENNReal.ofReal (A * 2^(θ*k)) < Jcount g (t / 2^(k+1)) ω} :=
          add_le_add hdoob hkey
    _ ≤ ENNReal.ofReal ((t/2)⁻¹) * eLpNorm f 1 μ
        + ∑' k : ℕ, (ENNReal.ofReal (2 * Cj / (t * Real.sqrt A)) * (ENNReal.ofReal q)^k
            * eLpNorm f 1 μ) := by
          gcongr with k
          exact hterm k
    _ = ENNReal.ofReal ((t/2)⁻¹) * eLpNorm f 1 μ
        + (ENNReal.ofReal (2 * Cj / (t * Real.sqrt A)) * (∑' k : ℕ, (ENNReal.ofReal q)^k)
            * eLpNorm f 1 μ) := by
          rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left]
    _ = ENNReal.ofReal (A0 / t) * eLpNorm f 1 μ := by
          rw [ENNReal.tsum_geometric]
          have hsub : (1 : ENNReal) - ENNReal.ofReal q = ENNReal.ofReal (1 - q) := by
            rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 hqpos.le]
          rw [hsub, ← ENNReal.ofReal_inv_of_pos (by linarith : (0:ℝ) < 1 - q)]
          rw [← ENNReal.ofReal_mul (by positivity)]
          rw [← add_mul]
          have hadd : ENNReal.ofReal ((t/2)⁻¹)
                + ENNReal.ofReal (2 * Cj / (t * Real.sqrt A) * (1 - q)⁻¹)
              = ENNReal.ofReal (A0 / t) := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
            congr 1
            rw [hA0def, show (t/2)⁻¹ = 2/t by ring]
            field_simp
            try ring
          rw [hadd]


set_option maxHeartbeats 8000000 in
/-- **Lépingle's maximal variation inequality in `L^p`, `1 < p < ∞`, `r > 2`.** -/
theorem lepingle_variation_lp_le {p r : ℝ} (hp : 1 < p) (hr : 2 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type*} {m : MeasurableSpace Ω} (μ : MeasureTheory.Measure Ω)
      [MeasureTheory.SigmaFinite μ] (F : MeasureTheory.Filtration ℕ m) (f : Ω → ℝ),
      MeasureTheory.MemLp f (ENNReal.ofReal p) μ →
      MeasureTheory.eLpNorm (fun ω => ⨆ (u : {u : ℕ → ℕ // StrictMono u}) (J : ℕ),
        (Finset.sum (Finset.range J) (fun j =>
          |(MeasureTheory.condExp (F (u.1 (j + 1))) μ f) ω
            - (MeasureTheory.condExp (F (u.1 j)) μ f) ω| ^ r)) ^ (1 / r))
        (ENNReal.ofReal p) μ
        ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm f (ENNReal.ofReal p) μ := by
  obtain ⟨A0, hA0, hweakV⟩ := weak_type_one_Vsup_aux hr
  exact final_assembly hp hr hA0 hweakV
    (interpolation_weak_one_strong_real (q := 4) (by norm_num))

end Work.Analysis.Probability
