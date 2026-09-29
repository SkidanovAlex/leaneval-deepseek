import Mathlib
import Submission.Work.TMC7Core.Defs
import Submission.Work.TMC7Core.Rat
import Submission.Work.TMC7Core.Cocycle
import Submission.Work.TMC7Core.Solutions.lyap_periodic
import Submission.Work.TMC7Core.Solutions.iterC_qpow
import Submission.Work.TMC7Core.Lyap.lyap_eq_lim
import Submission.Work.TMC7Core.Scale.prop9_aux
import Submission.Work.TMC7Core.Scale.frob_map_ofReal_sq
import Submission.Work.TMComp.LocCantor.frob_pow_sl2_rt
import Submission.Work.TMComp.LocCantor.analytic_iterR
import Submission.Work.TMComp.LocCantor.integral_log_max_ge
import Submission.Work.TMComp.LocCantor.defect_upper
import Submission.Work.TMComp.LocCantor.defect_lower_elliptic
import Submission.Work.TMComp.LocCantor.defect_lower_hyperbolic

namespace Work.TMComp.LocCantor

open MeasureTheory Filter Topology Set

/-- The block transfer matrix over `q` steps at the rational frequency `p/q`, real energy. -/
noncomputable def blk (p : ℤ) (q : ℕ) (lam E : ℝ) : ℝ → Matrix (Fin 2) (Fin 2) ℝ :=
  fun x => Work.TMC7Core.Solutions.iterR ((p : ℝ) / (q : ℝ)) lam E q x

/-- Its complexification is the complex `q`-step transfer matrix. -/
theorem blk_map (p : ℤ) (q : ℕ) (lam E : ℝ) (x : ℝ) :
    (blk p q lam E x).map Complex.ofRealHom
      = Work.TMC7Core.iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q x :=
  (Work.TMC7Core.Solutions.iterC_eq_map _ _ _ q x).symm

/-- The block transfer matrix has determinant one. -/
theorem blk_det (p : ℤ) (q : ℕ) (lam E : ℝ) (x : ℝ) : (blk p q lam E x).det = 1 := by
  have h1 : ((blk p q lam E x).map Complex.ofRealHom).det = 1 := by
    rw [blk_map]; exact Work.TMC7Core.det_iterC _ _ _ q x
  have h2 : (((blk p q lam E x).det : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
    have h := RingHom.map_det Complex.ofRealHom (blk p q lam E x)
    rw [show (((blk p q lam E x).det : ℝ) : ℂ)
          = Complex.ofRealHom ((blk p q lam E x).det) from rfl, h]
    rw [show Complex.ofRealHom.mapMatrix (blk p q lam E x)
          = (blk p q lam E x).map Complex.ofRealHom from rfl, h1]
    norm_num
  exact Complex.ofReal_inj.mp h2

/-- `A_{kq}(x) = M(x)^k` where `M(x)` is the real `q`-block. -/
theorem iterC_blk_pow (p : ℤ) (q : ℕ) (hq : 1 ≤ q) (lam E : ℝ) (k : ℕ) (x : ℝ) :
    Work.TMC7Core.iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) (k * q) x
      = ((blk p q lam E x).map Complex.ofRealHom) ^ k := by
  rw [Nat.mul_comm k q, Work.TMC7Core.Solutions.iterC_qpow p q hq lam E k x, ← blk_map]

/-- `ρ` of the block as a function of the phase is continuous. -/
theorem continuous_rhoSL : Continuous Work.TMC7Core.rhoSL := by
  have h : Work.TMC7Core.rhoSL
      = fun τ : ℝ => max 1 ((|τ| + Real.sqrt (τ ^ 2 - 4)) / 2) := by
    funext τ
    rw [Work.TMC7Core.rhoSL]
    split_ifs with h2
    · have h3 : 1 ≤ (|τ| + Real.sqrt (τ ^ 2 - 4)) / 2 := by
        have := Real.sqrt_nonneg (τ ^ 2 - 4); linarith
      rw [max_eq_right h3]
    · push_neg at h2
      have h4 : τ ^ 2 - 4 ≤ 0 := by nlinarith [sq_abs τ, abs_nonneg τ]
      rw [Real.sqrt_eq_zero_of_nonpos h4]
      have h5 : |τ| / 2 ≤ 1 := by linarith
      rw [max_eq_left (by linarith : (|τ| + 0) / 2 ≤ 1)]
  rw [h]; fun_prop

/-- The Lyapunov exponent at rational frequency as the `x`-average of `log ρ(tr M)`. -/
theorem lam_eq (p : ℤ) (q : ℕ) (hq : 1 ≤ q) (lam E : ℝ) :
    Work.TMC7Core.lyap ((p : ℝ) / (q : ℝ)) lam (E : ℂ)
      = (1 / (q : ℝ)) *
        ∫ x in (0 : ℝ)..1,
          Real.log (Work.TMC7Core.rhoSL ((blk p q lam E x).trace)) := by
  rw [Work.TMC7Core.Solutions.lyap_periodic p q hq lam E]
  have hf : (fun x : ℝ => Real.log (Work.TMC7Core.rhoSL
        ((Work.TMC7Core.iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q x).trace.re)))
      = (fun x : ℝ => Real.log (Work.TMC7Core.rhoSL ((blk p q lam E x).trace))) := by
    funext x
    have h : (Work.TMC7Core.iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q x).trace
        = (((blk p q lam E x).trace : ℝ) : ℂ) := by
      rw [← blk_map p q lam E x, Work.TMC7Core.Solutions.trace_map_ofReal]
    rw [h, Complex.ofReal_re]
  rw [hf]

/-- Along multiples of `q`, the finite-scale averages converge to `lyap`. -/
theorem tendsto_lyapAvg_mul (p : ℤ) (q : ℕ) (hq : 1 ≤ q) (lam E : ℝ) :
    Tendsto (fun m : ℕ => Work.TMC7Core.lyapAvg ((p : ℝ) / (q : ℝ)) lam (E : ℂ) (m * q))
      atTop (nhds (Work.TMC7Core.lyap ((p : ℝ) / (q : ℝ)) lam (E : ℂ))) := by
  have hqpos : 0 < q := by omega
  have hly : Tendsto (fun n : ℕ =>
      Work.TMC7Core.lyapAvg ((p : ℝ) / (q : ℝ)) lam (E : ℂ) (n + 1)) atTop
      (nhds (Work.TMC7Core.lyap ((p : ℝ) / (q : ℝ)) lam (E : ℂ))) := by
    simpa only [Work.TMC7Core.lyapAvg, Nat.cast_add, Nat.cast_one] using
      (Work.TMC7Core.Lyap.lyap_eq_lim ((p : ℝ) / (q : ℝ)) lam (E : ℂ))
  have hφ : Tendsto (fun m : ℕ => m * q - 1) atTop atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro b
    refine ⟨b + 1, fun m hm => ?_⟩
    have h1 : m ≤ m * q := Nat.le_mul_of_pos_right m hqpos
    omega
  have hmain : Tendsto (fun m : ℕ =>
      Work.TMC7Core.lyapAvg ((p : ℝ) / (q : ℝ)) lam (E : ℂ) ((m * q - 1) + 1)) atTop
      (nhds (Work.TMC7Core.lyap ((p : ℝ) / (q : ℝ)) lam (E : ℂ))) :=
    hly.comp hφ
  refine Filter.Tendsto.congr' ?_ hmain
  filter_upwards [Filter.eventually_ge_atTop 1] with m hm
  rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)))]

/-- `Σ Aᵢⱼ² - 2 ≥ 0` for a real matrix of determinant one. -/
theorem sl2_size_nonneg (a b c d : ℝ) (h : a * d - b * c = 1) :
    0 ≤ a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 - 2 := by
  have hkey : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 - 2 = (a - d) ^ 2 + (b + c) ^ 2 := by
    nlinarith [h]
  rw [hkey]; positivity

/-- The elementary logarithmic estimate used for the elliptic lower bound. -/
theorem log_elliptic_helper (X F K : ℝ) (hX0 : 0 ≤ X) (hX2 : X ≤ 2) (hF0 : 0 ≤ F)
    (hFK : F ≤ K) (hK : 1 ≤ K) :
    -Real.log 2 + 0.5 * Real.log X - 0.5 * Real.log (2 + K)
      ≤ 0.5 * Real.log (X / (X + F)) := by
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlogK : 0 ≤ Real.log (2 + K) := Real.log_nonneg (by linarith)
  rcases eq_or_lt_of_le hX0 with hX | hX
  · rw [← hX]
    have h1 : (0 : ℝ) / (0 + F) = 0 := by simp
    rw [h1, Real.log_zero, mul_zero]
    linarith
  · have hXF : 0 < X + F := by linarith
    have hXK : 0 < X + K := by linarith
    have h2K : 0 < 2 + K := by linarith
    have hstep1 : X / (X + K) ≤ X / (X + F) :=
      div_le_div_of_nonneg_left hX0 hXF (by linarith : X + F ≤ X + K)
    have hstep2 : Real.log (X / (X + K)) ≤ Real.log (X / (X + F)) :=
      Real.log_le_log (by positivity) hstep1
    have hstep3 : Real.log X - Real.log (2 + K) ≤ Real.log (X / (X + K)) := by
      rw [Real.log_div (ne_of_gt hX) (ne_of_gt hXK)]
      have : Real.log (X + K) ≤ Real.log (2 + K) :=
        Real.log_le_log hXK (by linarith)
      linarith
    linarith

/-- Pointwise comparison bounds for the doubling defect of a real `SL₂` matrix. -/
theorem pointwise_bound (A : Matrix (Fin 2) (Fin 2) ℝ) (hdet : A.det = 1) (m : ℕ) (hm : 1 ≤ m)
    (K : ℝ) (hK : 1 ≤ K) (hFK : A 0 0 ^ 2 + A 0 1 ^ 2 + A 1 0 ^ 2 + A 1 1 ^ 2 - 2 ≤ K) :
    (Real.log (Work.TMC7Core.frob ((A.map Complex.ofRealHom) ^ (2 * m)))
        - Real.log (Work.TMC7Core.frob ((A.map Complex.ofRealHom) ^ m))
        - (m : ℝ) * Real.log (Work.TMC7Core.rhoSL A.trace) ≤ Real.log 2)
    ∧ (-Real.log 2 + (0.5 * Real.log (max (2 - A.trace ^ 2 / 2) 0) - 0.5 * Real.log (2 + K))
        ≤ Real.log (Work.TMC7Core.frob ((A.map Complex.ofRealHom) ^ (2 * m)))
          - Real.log (Work.TMC7Core.frob ((A.map Complex.ofRealHom) ^ m))
          - (m : ℝ) * Real.log (Work.TMC7Core.rhoSL A.trace)) := by
  refine ⟨defect_upper A hdet m hm, ?_⟩
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlogK : 0 ≤ Real.log (2 + K) := Real.log_nonneg (by linarith)
  have hF0 : 0 ≤ A 0 0 ^ 2 + A 0 1 ^ 2 + A 1 0 ^ 2 + A 1 1 ^ 2 - 2 := by
    have h2 : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
      simpa [Matrix.det_fin_two] using hdet
    exact sl2_size_nonneg _ _ _ _ h2
  rcases lt_or_ge |A.trace| 2 with hτ | hτ
  · have hτ' : |A.trace| ≤ 2 := le_of_lt hτ
    have hρ : Work.TMC7Core.rhoSL A.trace = 1 := by
      rw [Work.TMC7Core.rhoSL, if_neg (not_le.mpr hτ)]
    have hX0 : 0 ≤ 2 - A.trace ^ 2 / 2 := by nlinarith [sq_abs A.trace, abs_nonneg A.trace]
    have hX2 : 2 - A.trace ^ 2 / 2 ≤ 2 := by nlinarith [sq_nonneg A.trace]
    rw [max_eq_left hX0, hρ, Real.log_one, mul_zero, sub_zero]
    have h := defect_lower_elliptic A hdet m hm hτ'
    linarith [log_elliptic_helper (2 - A.trace ^ 2 / 2)
      (A 0 0 ^ 2 + A 0 1 ^ 2 + A 1 0 ^ 2 + A 1 1 ^ 2 - 2) K hX0 hX2 hF0 hFK hK]
  · have hτ2 : 2 ≤ |A.trace| := hτ
    have hX0 : 2 - A.trace ^ 2 / 2 ≤ 0 := by nlinarith [sq_abs A.trace, abs_nonneg A.trace]
    rw [max_eq_right hX0, Real.log_zero, mul_zero]
    have h := defect_lower_hyperbolic A hdet m hm hτ2
    linarith

/-- The core defect estimate: `|m Λ + b_m - b_{2m}|` is bounded, where `Λ = ∫ log ρ`, and
`b_k = ∫ log ‖M(x)^k‖_F`. -/
theorem core_defect (p : ℤ) (q : ℕ) (hq : 1 ≤ q) (lam E : ℝ) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ m : ℕ, 1 ≤ m →
      |(m : ℝ) * (∫ x in (0 : ℝ)..1,
            Real.log (Work.TMC7Core.rhoSL ((blk p q lam E x).trace)))
        + (∫ x in (0 : ℝ)..1, Real.log (Work.TMC7Core.frob
            (Work.TMC7Core.iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) (m * q) x)))
        - (∫ x in (0 : ℝ)..1, Real.log (Work.TMC7Core.frob
            (Work.TMC7Core.iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) (2 * m * q) x)))| ≤ C₀ := by
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  -- analyticity / continuity of the block trace
  have han : ∀ i j : Fin 2, AnalyticOnNhd ℝ (fun x : ℝ => (blk p q lam E x) i j) Set.univ := by
    intro i j
    have h := analytic_iterR ((p : ℝ) / (q : ℝ)) lam E q i j
    simpa [blk] using h
  have htr_eq : (fun x : ℝ => (blk p q lam E x).trace)
      = fun x : ℝ => (blk p q lam E x) 0 0 + (blk p q lam E x) 1 1 := by
    funext x; rw [Matrix.trace_fin_two]
  have han_tr : AnalyticOnNhd ℝ (fun x : ℝ => (blk p q lam E x).trace) (Set.uIcc 0 1) := by
    rw [htr_eq]
    exact ((han 0 0).add (han 1 1)).mono (Set.subset_univ _)
  have hcont_tr : Continuous (fun x : ℝ => (blk p q lam E x).trace) := by
    rw [htr_eq]
    exact (continuousOn_univ.mp (han 0 0).continuousOn).add
      (continuousOn_univ.mp (han 1 1).continuousOn)
  have han_f : AnalyticOnNhd ℝ (fun x : ℝ => 2 - (blk p q lam E x).trace ^ 2 / 2) (Set.uIcc 0 1) :=
    (analyticOnNhd_const (v := (2 : ℝ))).sub ((han_tr.pow 2).div_const (c := (2 : ℝ)))
  have hII := integral_log_max_ge (fun x : ℝ => 2 - (blk p q lam E x).trace ^ 2 / 2) han_f
  -- the size bound `K`
  have hcont_F : Continuous (fun x : ℝ => (blk p q lam E x) 0 0 ^ 2 + (blk p q lam E x) 0 1 ^ 2
      + (blk p q lam E x) 1 0 ^ 2 + (blk p q lam E x) 1 1 ^ 2 - 2) := by
    have hc : ∀ i j : Fin 2, Continuous (fun x : ℝ => (blk p q lam E x) i j) :=
      fun i j => continuousOn_univ.mp (han i j).continuousOn
    fun_prop
  obtain ⟨K₀, hK₀⟩ := isCompact_Icc.bddAbove_image hcont_F.continuousOn
  set K : ℝ := max K₀ 1 with hK
  have hK1 : 1 ≤ K := le_max_right _ _
  have hFK : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
      (blk p q lam E x) 0 0 ^ 2 + (blk p q lam E x) 0 1 ^ 2
        + (blk p q lam E x) 1 0 ^ 2 + (blk p q lam E x) 1 1 ^ 2 - 2 ≤ K := by
    intro x hx
    have hx' : x ∈ Set.Icc (0 : ℝ) 1 := by simpa [Set.uIcc_of_le h01] using hx
    have h1 : (blk p q lam E x) 0 0 ^ 2 + (blk p q lam E x) 0 1 ^ 2
        + (blk p q lam E x) 1 0 ^ 2 + (blk p q lam E x) 1 1 ^ 2 - 2 ≤ K₀ :=
      hK₀ (Set.mem_image_of_mem _ hx')
    have h2 : K₀ ≤ K := le_max_left _ _
    linarith
  set I : ℝ := ∫ x in (0 : ℝ)..1, Real.log (max (2 - (blk p q lam E x).trace ^ 2 / 2) 0) with hI
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogK : 0 ≤ Real.log (2 + K) := Real.log_nonneg (by linarith)
  refine ⟨|0.5 * I| + 0.5 * Real.log (2 + K) + Real.log 2 + 1, ?_, fun m hm => ?_⟩
  · have := abs_nonneg (0.5 * I); linarith
  · set f1 : ℝ → ℝ := fun x => Real.log (Work.TMC7Core.frob
        (Work.TMC7Core.iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) (2 * m * q) x)) with hf1
    set f2 : ℝ → ℝ := fun x => Real.log (Work.TMC7Core.frob
        (Work.TMC7Core.iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) (m * q) x)) with hf2
    set f3 : ℝ → ℝ := fun x => Real.log (Work.TMC7Core.rhoSL ((blk p q lam E x).trace)) with hf3
    set H : ℝ → ℝ := fun x => f1 x - f2 x - (m : ℝ) * f3 x with hH
    set G : ℝ → ℝ := fun x => -Real.log 2 + (0.5 * Real.log (max (2 - (blk p q lam E x).trace ^ 2 / 2) 0)
        - 0.5 * Real.log (2 + K)) with hG
    have hc1 : Continuous f1 := by
      rw [hf1]; exact Work.TMC7Core.Lyap.continuous_log_frob_iterC _ _ _ _
    have hc2 : Continuous f2 := by
      rw [hf2]; exact Work.TMC7Core.Lyap.continuous_log_frob_iterC _ _ _ _
    have hc3 : Continuous f3 := by
      rw [hf3]
      exact (continuous_rhoSL.comp hcont_tr).log
        (fun x => ne_of_gt (lt_of_lt_of_le zero_lt_one (Work.TMC7Core.rhoSL_one_le _)))
    have hcH : Continuous H := by
      rw [hH]; exact (hc1.sub hc2).sub (hc3.const_mul (m : ℝ))
    have hInt_1 : IntervalIntegrable f1 volume (0 : ℝ) 1 := hc1.intervalIntegrable _ _
    have hInt_2 : IntervalIntegrable f2 volume (0 : ℝ) 1 := hc2.intervalIntegrable _ _
    have hInt_3 : IntervalIntegrable f3 volume (0 : ℝ) 1 := hc3.intervalIntegrable _ _
    have hInt_H : IntervalIntegrable H volume (0 : ℝ) 1 := hcH.intervalIntegrable _ _
    have hInt_G : IntervalIntegrable G volume (0 : ℝ) 1 := by
      rw [hG]
      exact intervalIntegrable_const.add
        ((hII.const_mul (0.5 : ℝ)).sub intervalIntegrable_const)
    have hple : ∀ x ∈ Set.uIcc (0 : ℝ) 1, H x ≤ Real.log 2 := by
      intro x hx
      have hp := (pointwise_bound (blk p q lam E x) (blk_det p q lam E x) m hm K hK1 (hFK x hx)).1
      show f1 x - f2 x - (m : ℝ) * f3 x ≤ Real.log 2
      simp only [hf1, hf2, hf3]
      rw [iterC_blk_pow p q hq lam E (2 * m) x, iterC_blk_pow p q hq lam E m x]
      exact hp
    have hpge : ∀ x ∈ Set.uIcc (0 : ℝ) 1, G x ≤ H x := by
      intro x hx
      have hp := (pointwise_bound (blk p q lam E x) (blk_det p q lam E x) m hm K hK1 (hFK x hx)).2
      show -Real.log 2 + (0.5 * Real.log (max (2 - (blk p q lam E x).trace ^ 2 / 2) 0)
          - 0.5 * Real.log (2 + K)) ≤ f1 x - f2 x - (m : ℝ) * f3 x
      simp only [hf1, hf2, hf3]
      rw [iterC_blk_pow p q hq lam E (2 * m) x, iterC_blk_pow p q hq lam E m x]
      exact hp
    have hInt_le : (∫ x in (0 : ℝ)..1, H x) ≤ Real.log 2 := by
      rw [intervalIntegral.integral_of_le h01]
      have hconst : (∫ x in Set.Ioc (0 : ℝ) 1, (Real.log 2 : ℝ)) = Real.log 2 := by
        rw [MeasureTheory.setIntegral_const]
        norm_num
      rw [← hconst]
      apply MeasureTheory.integral_mono_ae
      · simpa [Set.uIoc_of_le h01] using hInt_H.1.integrable
      · simpa [Set.uIoc_of_le h01] using
          ((continuous_const).intervalIntegrable (0 : ℝ) 1).1.integrable
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
        exact hple x (by rw [Set.uIcc_of_le h01]; exact Set.Ioc_subset_Icc_self hx)
    have hInt_ge : (∫ x in (0 : ℝ)..1, G x) ≤ ∫ x in (0 : ℝ)..1, H x := by
      rw [intervalIntegral.integral_of_le h01, intervalIntegral.integral_of_le h01]
      apply MeasureTheory.integral_mono_ae
      · simpa [Set.uIoc_of_le h01] using hInt_G.1.integrable
      · simpa [Set.uIoc_of_le h01] using hInt_H.1.integrable
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
        exact hpge x (by rw [Set.uIcc_of_le h01]; exact Set.Ioc_subset_Icc_self hx)
    have hGval : (∫ x in (0 : ℝ)..1, G x) = -Real.log 2 + 0.5 * I - 0.5 * Real.log (2 + K) := by
      rw [hG, hI]
      rw [intervalIntegral.integral_add intervalIntegrable_const
            ((hII.const_mul (0.5 : ℝ)).sub intervalIntegrable_const),
          intervalIntegral.integral_sub (hII.const_mul (0.5 : ℝ)) intervalIntegrable_const,
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
          intervalIntegral.integral_const]
      ring
    have hC₀bd : |∫ x in (0 : ℝ)..1, H x|
        ≤ |0.5 * I| + 0.5 * Real.log (2 + K) + Real.log 2 + 1 := by
      rw [abs_le]
      constructor
      · have h1 : -Real.log 2 + 0.5 * I - 0.5 * Real.log (2 + K)
            ≤ ∫ x in (0 : ℝ)..1, H x := by rw [← hGval]; exact hInt_ge
        have h2 : -(0.5 * I) ≤ |0.5 * I| := neg_le_abs _
        linarith
      · have h2 : (0:ℝ) ≤ |0.5 * I| := abs_nonneg _
        linarith
    have hdefect : (m : ℝ) * (∫ x in (0 : ℝ)..1, f3 x) + (∫ x in (0 : ℝ)..1, f2 x)
        - (∫ x in (0 : ℝ)..1, f1 x) = -(∫ x in (0 : ℝ)..1, H x) := by
      have hs : (∫ x in (0 : ℝ)..1, H x) = (∫ x in (0 : ℝ)..1, f1 x)
          - (∫ x in (0 : ℝ)..1, f2 x) - (m : ℝ) * (∫ x in (0 : ℝ)..1, f3 x) := by
        simp only [hH]
        rw [intervalIntegral.integral_sub (hInt_1.sub hInt_2) (hInt_3.const_mul (m : ℝ)),
          intervalIntegral.integral_sub hInt_1 hInt_2, intervalIntegral.integral_const_mul]
      rw [hs]; ring
    rw [hf1, hf2, hf3, hdefect, abs_neg]
    exact hC₀bd

theorem periodic_defect_bound (p : ℤ) (q : ℕ) (hq : 1 ≤ q) (lam E : ℝ) (L : ℝ)
    (hL : Filter.Tendsto (fun k : ℕ => Work.TMC7Core.lyapAvg ((p : ℝ) / (q : ℝ)) lam (E : ℂ) (2 ^ k * q))
      Filter.atTop (nhds L)) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      |L + Work.TMC7Core.lyapAvg ((p : ℝ) / (q : ℝ)) lam (E : ℂ) (m * q)
          - 2 * Work.TMC7Core.lyapAvg ((p : ℝ) / (q : ℝ)) lam (E : ℂ) (2 * m * q)|
        ≤ C / (m : ℝ) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := core_defect p q hq lam E
  refine ⟨max C₀ 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun m hm => ?_⟩
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hmqpos : (0 : ℝ) < (m : ℝ) * (q : ℝ) := mul_pos hmpos hqpos
  -- identify `L` with `Λ / q`
  have hLlyap : L = Work.TMC7Core.lyap ((p : ℝ) / (q : ℝ)) lam (E : ℂ) := by
    have h2 : Tendsto (fun k : ℕ => (2 : ℕ) ^ k) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
    exact tendsto_nhds_unique hL ((tendsto_lyapAvg_mul p q hq lam E).comp h2)
  have hqL : (q : ℝ) * L
      = ∫ x in (0 : ℝ)..1, Real.log (Work.TMC7Core.rhoSL ((blk p q lam E x).trace)) := by
    rw [hLlyap, lam_eq p q hq lam E]
    field_simp
  set Lam : ℝ := ∫ x in (0 : ℝ)..1, Real.log (Work.TMC7Core.rhoSL ((blk p q lam E x).trace))
    with hLam
  set bM : ℝ := ∫ x in (0 : ℝ)..1, Real.log (Work.TMC7Core.frob
      (Work.TMC7Core.iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) (m * q) x)) with hbM
  set b2M : ℝ := ∫ x in (0 : ℝ)..1, Real.log (Work.TMC7Core.frob
      (Work.TMC7Core.iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) (2 * m * q) x)) with hb2M
  have hqL' : (q : ℝ) * L = Lam := hqL
  have hkey := hC₀ m hm
  have hrewrite : L + Work.TMC7Core.lyapAvg ((p : ℝ) / (q : ℝ)) lam (E : ℂ) (m * q)
        - 2 * Work.TMC7Core.lyapAvg ((p : ℝ) / (q : ℝ)) lam (E : ℂ) (2 * m * q)
      = ((m : ℝ) * Lam + bM - b2M) / ((m : ℝ) * (q : ℝ)) := by
    simp only [Work.TMC7Core.lyapAvg]
    rw [← hbM, ← hb2M]
    have h2mq : ((2 * m * q : ℕ) : ℝ) = 2 * ((m : ℝ) * (q : ℝ)) := by push_cast; ring
    have hmq : ((m * q : ℕ) : ℝ) = (m : ℝ) * (q : ℝ) := by push_cast; ring
    rw [h2mq, hmq]
    field_simp
    linear_combination (m : ℝ) * hqL'
  rw [hrewrite, abs_div, abs_of_pos hmqpos]
  have h1 : |(m : ℝ) * Lam + bM - b2M| / ((m : ℝ) * (q : ℝ)) ≤ C₀ / ((m : ℝ) * (q : ℝ)) :=
    div_le_div_of_nonneg_right hkey (le_of_lt hmqpos)
  have h2 : C₀ / ((m : ℝ) * (q : ℝ)) ≤ max C₀ 1 / (m : ℝ) := by
    have hle : (m : ℝ) ≤ (m : ℝ) * (q : ℝ) := by
      have h := mul_le_mul_of_nonneg_left hq1 (le_of_lt hmpos)
      simpa using h
    calc C₀ / ((m : ℝ) * (q : ℝ)) ≤ max C₀ 1 / ((m : ℝ) * (q : ℝ)) :=
          div_le_div_of_nonneg_right (le_max_left _ _) (le_of_lt hmqpos)
      _ ≤ max C₀ 1 / (m : ℝ) := by
          apply div_le_div_of_nonneg_left (le_of_lt (lt_of_lt_of_le hC₀pos (le_max_left _ _)))
            hmpos hle
  linarith

end Work.TMComp.LocCantor
