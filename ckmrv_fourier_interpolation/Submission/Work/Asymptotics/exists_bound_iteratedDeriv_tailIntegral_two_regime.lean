import Mathlib
import Submission.Work.Asymptotics.TailIntegral
import Submission.Work.Asymptotics.windowIntegral_bound
import Submission.Work.Asymptotics.integral_Ioi_rpow_mul_exp_neg_le

noncomputable section

open MeasureTheory Filter Topology
open scoped Topology ContDiff

namespace Work.Asymptotics

/-- **Splitting the tail integral at `B ≥ 1`.**  For an integrable `F` on `[1,∞)`,
`∫_{t ≥ 1} F t = ∫_{t ∈ [1,B]} F t + ∫_{t > B} F t`. -/
lemma setIntegral_Ici_split_at_Icc_Ioi {F : ℝ → ℂ} {B : ℝ} (hB : 1 ≤ B)
    (hF : IntegrableOn F (Set.Ici (1 : ℝ))) :
    ∫ t in Set.Ici (1 : ℝ), F t
      = (∫ t in Set.Icc (1 : ℝ) B, F t) + (∫ t in Set.Ioi B, F t) := by
  have hIoc : IntegrableOn F (Set.Ioc (1 : ℝ) B) := hF.mono_set fun t ht => ht.1.le
  have hIoi : IntegrableOn F (Set.Ioi B) := hF.mono_set fun t ht => le_trans hB ht.le
  have h2 : ∫ t in Set.Ioc (1 : ℝ) B ∪ Set.Ioi B, F t
      = (∫ t in Set.Ioc (1 : ℝ) B, F t) + (∫ t in Set.Ioi B, F t) :=
    setIntegral_union (s := Set.Ioc (1 : ℝ) B) (t := Set.Ioi B)
      (Set.disjoint_left.mpr fun t h1 h2 => absurd h1.2 (not_le.mpr h2))
      measurableSet_Ioi hIoc hIoi
  rw [integral_Ici_eq_integral_Ioi, (Set.Ioc_union_Ioi_eq_Ioi hB).symm, h2,
    integral_Icc_eq_integral_Ioc]

/-- The modulus of the amplitude factor `(-π t)^m` for `t > 0`: `‖(-πt)^m‖ = (πt)^m`. -/
private lemma norm_neg_pi_mul_pow {t : ℝ} (ht : 0 < t) (m : ℕ) :
    ‖(((-(Real.pi * t)) : ℝ) : ℂ) ^ m‖ = (Real.pi * t) ^ m := by
  rw [norm_pow, norm_ofReal_eq_abs, abs_of_neg (by nlinarith [Real.pi_pos, ht])]
  ring

/-- `1 ≤ π`. -/
private lemma one_le_pi : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]

/-- **Two-regime bound on the iterated derivatives of the tail integral.**  Let `A ≥ 1`, `N₀ ≥ 0`,
let `h` be a.e. strongly measurable on `[1,∞)` and suppose `‖h t‖ ≤ C₁ A^{N₁}(1+t)^{M₁}` on the
window `1 ≤ t ≤ A^{N₀}`, `‖h t‖ ≤ C₂ A^{N₂} t^{M₂} e^{-πt}` for `t ≥ A^{N₀}`, and a global a.e. bound
`‖h t‖ ≤ Cg t^{Mg} e^{-πt}` on `[1,∞)` (whose constants `Cg, Mg` serve only integrability and the
differentiation-under-the-integral formula and are *not* allowed in the conclusion).  Then there
are constants `c, N ≥ 0`, *independent of `h` and `A`*, with
`‖∂_λ^m (∫_{t ≥ 1} h t e^{-πλt} dt)‖ ≤ c A^N e^{-πλ}` for all `m ≤ l` and `λ ≥ 0`.
(`Work.Asymptotics.tailIntegral h λ` is the tail integral.)  A route: split the tail integral at
`B := A^{N₀} ≥ 1`, use the global bound to get the derivative formula
(`Work.Asymptotics.tailIntegral_iteratedDeriv`) and integrability
(`Work.Asymptotics.integrableOn_tailIntegral`), then bound the window part with
`Work.Asymptotics.windowIntegral_bound` + `Work.Asymptotics.setIntegral_Ici_one_split` and the tail
part with `Work.Asymptotics.integral_Ioi_rpow_mul_exp_neg_le` + `Work.Asymptotics.tailDecay_mono`.
The constants `c := C₁π^l 2^{M₁+l+1} + C₂π^l·tailDecay M₂ l` and `N := N₁ + N₀(M₁+l+1) + N₂` work. -/
theorem exists_bound_iteratedDeriv_tailIntegral_two_regime
    (l : ℕ) (N₀ C₁ N₁ M₁ C₂ N₂ M₂ : ℝ)
    (hC₁ : 0 ≤ C₁) (hN₁ : 0 ≤ N₁) (hM₁ : 0 ≤ M₁) (hC₂ : 0 ≤ C₂) (hN₂ : 0 ≤ N₂)
    (hM₂ : 0 ≤ M₂) (hN₀ : 0 ≤ N₀) :
    ∃ c N : ℝ, 0 ≤ c ∧ 0 ≤ N ∧
      ∀ (h : ℝ → ℂ) (A Cg Mg : ℝ), 1 ≤ A → 0 ≤ Cg → 0 ≤ Mg →
        MeasureTheory.AEStronglyMeasurable h (MeasureTheory.volume.restrict (Set.Ici (1 : ℝ))) →
        (∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ici (1 : ℝ))),
          ‖h t‖ ≤ Cg * t ^ Mg * Real.exp (-(Real.pi * t))) →
        (∀ t : ℝ, 1 ≤ t → t ≤ A ^ N₀ → ‖h t‖ ≤ C₁ * A ^ N₁ * (1 + t) ^ M₁) →
        (∀ t : ℝ, A ^ N₀ ≤ t → ‖h t‖ ≤ C₂ * A ^ N₂ * t ^ M₂ * Real.exp (-(Real.pi * t))) →
        ∀ m : ℕ, m ≤ l → ∀ lam : ℝ, 0 ≤ lam →
          ‖iteratedDeriv m (Work.Asymptotics.tailIntegral h) lam‖
            ≤ c * A ^ N * Real.exp (-(Real.pi * lam)) := by
  refine ⟨C₁ * Real.pi ^ l * 2 ^ (M₁ + (l : ℝ) + 1) + C₂ * Real.pi ^ l * tailDecay M₂ l,
    N₁ + N₀ * (M₁ + (l : ℝ) + 1) + N₂, ?_, ?_, ?_⟩
  · have h1 : 0 ≤ C₁ * Real.pi ^ l * 2 ^ (M₁ + (l : ℝ) + 1) :=
      mul_nonneg (mul_nonneg hC₁ (pow_nonneg Real.pi_pos.le l))
        (Real.rpow_nonneg (by norm_num) _)
    have h2 : 0 ≤ C₂ * Real.pi ^ l * tailDecay M₂ l :=
      mul_nonneg (mul_nonneg hC₂ (pow_nonneg Real.pi_pos.le l)) (tailDecay_nonneg M₂ l)
    linarith
  · have h0 : 0 ≤ N₀ * (M₁ + (l : ℝ) + 1) :=
      mul_nonneg hN₀ (by linarith)
    linarith
  intro h A Cg Mg hA hCg hMg hmeas hb hwin htail m hm lam hlam
  have hA1 : (1 : ℝ) ≤ A := hA
  have hA0 : (0 : ℝ) < A := lt_of_lt_of_le zero_lt_one hA
  set B : ℝ := A ^ N₀ with hBdef
  have hB1 : (1 : ℝ) ≤ B := by
    rw [hBdef, ← Real.one_rpow N₀]
    exact Real.rpow_le_rpow zero_le_one hA1 hN₀
  have hB0 : (0 : ℝ) < B := lt_of_lt_of_le zero_lt_one hB1
  -- the amplitude `G = h · (-π t)^m`
  set G : ℝ → ℂ := fun t => h t * (((-(Real.pi * t)) : ℝ) : ℂ) ^ m with hGdef
  have hGmeas : AEStronglyMeasurable G (volume.restrict (Set.Ici (1 : ℝ))) :=
    hmeas.mul (by fun_prop : Continuous fun t : ℝ =>
      (((-(Real.pi * t) : ℝ)) : ℂ) ^ m).aestronglyMeasurable
  have hGbound : ∀ᵐ t ∂(volume.restrict (Set.Ici (1 : ℝ))),
      ‖G t‖ ≤ Cg * Real.pi ^ m * t ^ (Mg + (m : ℝ)) * Real.exp (-(Real.pi * t)) := by
    simpa only [hGdef] using tailIntegral_amp_ae_bound h hb m
  -- the integrand `F = G · e^{-πλt}`
  set F : ℝ → ℂ := fun t => G t * (Real.exp (-(Real.pi * lam * t)) : ℂ) with hFdef
  have hFint : IntegrableOn F (Set.Ici (1 : ℝ)) := by
    rw [hFdef]
    exact integrableOn_tailIntegral G hGmeas (mul_nonneg hCg (pow_nonneg Real.pi_pos.le m))
      (add_nonneg hMg (Nat.cast_nonneg m)) hGbound (by linarith)
  -- the derivative formula
  have hderiv : iteratedDeriv m (tailIntegral h) lam = ∫ t in Set.Ici (1 : ℝ), F t := by
    rw [tailIntegral_iteratedDeriv h hmeas hCg hMg hb m lam (by linarith), tailIntegral]
  rw [hderiv, setIntegral_Ici_split_at_Icc_Ioi hB1 hFint]
  -- integrability of `‖F‖` on the two pieces
  have hnormF : IntegrableOn (fun t : ℝ => ‖F t‖) (Set.Ici (1 : ℝ)) := hFint.norm
  have hnorm_win : IntegrableOn (fun t : ℝ => ‖F t‖) (Set.Icc (1 : ℝ) B) :=
    hnormF.mono_set fun _ ht => ht.1
  have hnorm_tail : IntegrableOn (fun t : ℝ => ‖F t‖) (Set.Ioi B) :=
    hnormF.mono_set fun _ ht => le_trans hB1 ht.le
  -- the pointwise window bound
  have hwin_pt : ∀ t ∈ Set.Icc (1 : ℝ) B,
      ‖F t‖ ≤ (C₁ * A ^ N₁ * Real.pi ^ m)
        * ((1 + t) ^ M₁ * t ^ m * Real.exp (-(Real.pi * lam * t))) := by
    intro t ht
    obtain ⟨ht1, htB⟩ := ht
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht1
    have hht : ‖h t‖ ≤ C₁ * A ^ N₁ * (1 + t) ^ M₁ := hwin t ht1 htB
    have hnormG : ‖G t‖ = ‖h t‖ * (Real.pi * t) ^ m := by
      rw [hGdef]
      simp only
      rw [norm_mul, norm_neg_pi_mul_pow ht0]
    have hFt : ‖F t‖ = ‖G t‖ * Real.exp (-(Real.pi * lam * t)) := by
      rw [hFdef]
      simp only
      rw [norm_mul, norm_ofReal_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc ‖F t‖ = ‖h t‖ * (Real.pi * t) ^ m * Real.exp (-(Real.pi * lam * t)) := by
          rw [hFt, hnormG]
      _ ≤ (C₁ * A ^ N₁ * (1 + t) ^ M₁) * (Real.pi * t) ^ m
            * Real.exp (-(Real.pi * lam * t)) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hht (pow_nonneg (mul_nonneg Real.pi_pos.le ht0.le) m))
            (Real.exp_pos _).le
      _ = (C₁ * A ^ N₁ * Real.pi ^ m)
            * ((1 + t) ^ M₁ * t ^ m * Real.exp (-(Real.pi * lam * t))) := by
          rw [mul_pow]; ring
  -- the pointwise tail bound
  have htail_pt : ∀ t ∈ Set.Ioi B,
      ‖F t‖ ≤ (C₂ * A ^ N₂ * Real.pi ^ m)
        * (t ^ (M₂ + (m : ℝ)) * Real.exp (-(Real.pi * (lam + 1) * t))) := by
    intro t ht
    have ht1 : (1 : ℝ) ≤ t := le_trans hB1 ht.le
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht1
    have hht : ‖h t‖ ≤ C₂ * A ^ N₂ * t ^ M₂ * Real.exp (-(Real.pi * t)) := htail t ht.le
    have hnormG : ‖G t‖ = ‖h t‖ * (Real.pi * t) ^ m := by
      rw [hGdef]
      simp only
      rw [norm_mul, norm_neg_pi_mul_pow ht0]
    have hFt : ‖F t‖ = ‖G t‖ * Real.exp (-(Real.pi * lam * t)) := by
      rw [hFdef]
      simp only
      rw [norm_mul, norm_ofReal_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hexp : Real.exp (-(Real.pi * t)) * Real.exp (-(Real.pi * lam * t))
        = Real.exp (-(Real.pi * (lam + 1) * t)) := by
      rw [← Real.exp_add]; congr 1; ring
    have hpow : t ^ M₂ * t ^ m = t ^ (M₂ + (m : ℝ)) := by
      have h1 : (t ^ m : ℝ) = t ^ (m : ℝ) := (Real.rpow_natCast t m).symm
      rw [h1, ← Real.rpow_add ht0]
    calc ‖F t‖ = ‖h t‖ * (Real.pi * t) ^ m * Real.exp (-(Real.pi * lam * t)) := by
          rw [hFt, hnormG]
      _ ≤ (C₂ * A ^ N₂ * t ^ M₂ * Real.exp (-(Real.pi * t))) * (Real.pi * t) ^ m
            * Real.exp (-(Real.pi * lam * t)) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hht (pow_nonneg (mul_nonneg Real.pi_pos.le ht0.le) m))
            (Real.exp_pos _).le
      _ = (C₂ * A ^ N₂ * Real.pi ^ m)
            * (t ^ (M₂ + (m : ℝ)) * Real.exp (-(Real.pi * (lam + 1) * t))) := by
          rw [mul_pow, ← hpow, ← hexp]; ring
  -- integrability of the window majorant
  have hmaj_win_int : IntegrableOn
      (fun t : ℝ => (1 + t) ^ M₁ * t ^ m * Real.exp (-(Real.pi * lam * t)))
      (Set.Icc (1 : ℝ) B) := by
    refine Measure.integrableOn_of_bounded (M := (1 + B) ^ M₁ * B ^ m) ?_ ?_ ?_
    · rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
    · measurability
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      have ht1 : (1 : ℝ) ≤ t := ht.1
      have htB : t ≤ B := ht.2
      have ht0 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht1
      have h1t : (0 : ℝ) < 1 + t := by linarith
      rw [Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (mul_nonneg (Real.rpow_nonneg h1t.le _) (pow_nonneg ht0.le _))
          (Real.exp_pos _).le)]
      have h3 : (1 + t) ^ M₁ ≤ (1 + B) ^ M₁ := Real.rpow_le_rpow h1t.le (by linarith) hM₁
      have h4 : t ^ m ≤ B ^ m := pow_le_pow_left₀ ht0.le htB m
      have h5 : Real.exp (-(Real.pi * lam * t)) ≤ 1 := by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr (by
          have hπl : (0 : ℝ) ≤ Real.pi * lam := mul_nonneg Real.pi_pos.le hlam
          have h2 : (0 : ℝ) ≤ Real.pi * lam * t := mul_nonneg hπl (by linarith)
          linarith)
      have h3B : (0 : ℝ) ≤ (1 + B) ^ M₁ := Real.rpow_nonneg (by linarith) M₁
      calc (1 + t) ^ M₁ * t ^ m * Real.exp (-(Real.pi * lam * t))
          ≤ (1 + B) ^ M₁ * B ^ m * 1 :=
            mul_le_mul (mul_le_mul h3 h4 (pow_nonneg ht0.le m) h3B) h5
              (Real.exp_pos _).le (mul_nonneg h3B (pow_nonneg hB0.le m))
        _ = (1 + B) ^ M₁ * B ^ m := by ring
  -- integrability of the tail majorant
  have hmaj_tail_int : IntegrableOn
      (fun t : ℝ => t ^ (M₂ + (m : ℝ)) * Real.exp (-(Real.pi * (lam + 1) * t)))
      (Set.Ioi B) :=
    (integrableOn_rpow_mul_exp_neg (M₂ + m) (Real.pi * (lam + 1))
      (by positivity) (by positivity)).mono_set fun t ht => le_trans hB1 ht.le
  -- the window integral bound
  have hwin_bd : ∫ t in Set.Icc (1 : ℝ) B, ‖F t‖
      ≤ C₁ * A ^ N₁ * Real.pi ^ m
        * ((1 + B) ^ (M₁ + (l : ℝ) + 1) * Real.exp (-(Real.pi * lam))) := by
    have hC0 : (0 : ℝ) ≤ C₁ * A ^ N₁ * Real.pi ^ m :=
      mul_nonneg (mul_nonneg hC₁ (Real.rpow_nonneg hA0.le N₁))
        (pow_nonneg Real.pi_pos.le m)
    have h1 := setIntegral_mono_on hnorm_win (hmaj_win_int.const_mul (C₁ * A ^ N₁ * Real.pi ^ m))
      measurableSet_Icc hwin_pt
    rw [integral_const_mul] at h1
    calc ∫ t in Set.Icc (1 : ℝ) B, ‖F t‖
        ≤ (C₁ * A ^ N₁ * Real.pi ^ m)
            * ∫ t in Set.Icc (1 : ℝ) B,
                (1 + t) ^ M₁ * t ^ m * Real.exp (-(Real.pi * lam * t)) := h1
      _ ≤ (C₁ * A ^ N₁ * Real.pi ^ m)
            * ((1 + B) ^ (M₁ + (l : ℝ) + 1) * Real.exp (-(Real.pi * lam))) :=
          mul_le_mul_of_nonneg_left (windowIntegral_bound M₁ hM₁ B hB1 l hlam hm) hC0
  -- the tail integral bound
  have htail_bd : ∫ t in Set.Ioi B, ‖F t‖
      ≤ C₂ * A ^ N₂ * Real.pi ^ m * (Real.exp (-(Real.pi * lam)) * tailDecay M₂ m) := by
    have hC0 : (0 : ℝ) ≤ C₂ * A ^ N₂ * Real.pi ^ m :=
      mul_nonneg (mul_nonneg hC₂ (Real.rpow_nonneg hA0.le N₂))
        (pow_nonneg Real.pi_pos.le m)
    have h1 := setIntegral_mono_on hnorm_tail (hmaj_tail_int.const_mul (C₂ * A ^ N₂ * Real.pi ^ m))
      measurableSet_Ioi htail_pt
    rw [integral_const_mul] at h1
    calc ∫ t in Set.Ioi B, ‖F t‖
        ≤ (C₂ * A ^ N₂ * Real.pi ^ m)
            * ∫ t in Set.Ioi B,
                t ^ (M₂ + (m : ℝ)) * Real.exp (-(Real.pi * (lam + 1) * t)) := h1
      _ ≤ (C₂ * A ^ N₂ * Real.pi ^ m) * (Real.exp (-(Real.pi * lam)) * tailDecay M₂ m) :=
          mul_le_mul_of_nonneg_left (integral_Ioi_rpow_mul_exp_neg_le M₂ hM₂ hB1 hlam m) hC0
  -- the final arithmetic
  set cW : ℝ := C₁ * Real.pi ^ l * 2 ^ (M₁ + (l : ℝ) + 1) with hcWdef
  set cT : ℝ := C₂ * Real.pi ^ l * tailDecay M₂ l with hcTdef
  have hcW0 : (0 : ℝ) ≤ cW := by
    rw [hcWdef]
    exact mul_nonneg (mul_nonneg hC₁ (pow_nonneg Real.pi_pos.le l))
      (Real.rpow_nonneg (by norm_num) _)
  have hcT0 : (0 : ℝ) ≤ cT := by
    rw [hcTdef]
    exact mul_nonneg (mul_nonneg hC₂ (pow_nonneg Real.pi_pos.le l)) (tailDecay_nonneg M₂ l)
  have ht1 : C₁ * A ^ N₁ * Real.pi ^ m
        * ((1 + B) ^ (M₁ + (l : ℝ) + 1) * Real.exp (-(Real.pi * lam)))
      ≤ cW * A ^ (N₁ + N₀ * (M₁ + (l : ℝ) + 1)) * Real.exp (-(Real.pi * lam)) := by
    have hπ : Real.pi ^ m ≤ Real.pi ^ l := pow_le_pow_right₀ one_le_pi hm
    have hK : (1 + B) ^ (M₁ + (l : ℝ) + 1)
        ≤ 2 ^ (M₁ + (l : ℝ) + 1) * A ^ (N₀ * (M₁ + (l : ℝ) + 1)) := by
      have h1 : 1 + B ≤ 2 * B := by linarith
      have h2 : (1 + B) ^ (M₁ + (l : ℝ) + 1) ≤ (2 * B) ^ (M₁ + (l : ℝ) + 1) :=
        Real.rpow_le_rpow (by linarith) h1 (by linarith)
      have h3 : (2 * B) ^ (M₁ + (l : ℝ) + 1)
          = 2 ^ (M₁ + (l : ℝ) + 1) * B ^ (M₁ + (l : ℝ) + 1) :=
        Real.mul_rpow (show (0 : ℝ) ≤ 2 by norm_num) hB0.le
      have h4 : B ^ (M₁ + (l : ℝ) + 1) = A ^ (N₀ * (M₁ + (l : ℝ) + 1)) := by
        rw [hBdef]
        exact (Real.rpow_mul hA0.le N₀ (M₁ + (l : ℝ) + 1)).symm
      rw [h3, h4] at h2
      exact h2
    have hAexp : A ^ N₁ * A ^ (N₀ * (M₁ + (l : ℝ) + 1))
        = A ^ (N₁ + N₀ * (M₁ + (l : ℝ) + 1)) :=
      (Real.rpow_add hA0 N₁ _).symm
    calc C₁ * A ^ N₁ * Real.pi ^ m
          * ((1 + B) ^ (M₁ + (l : ℝ) + 1) * Real.exp (-(Real.pi * lam)))
        = (C₁ * A ^ N₁) * Real.pi ^ m
            * ((1 + B) ^ (M₁ + (l : ℝ) + 1) * Real.exp (-(Real.pi * lam))) := by ring
      _ ≤ (C₁ * A ^ N₁) * Real.pi ^ l
            * ((2 ^ (M₁ + (l : ℝ) + 1) * A ^ (N₀ * (M₁ + (l : ℝ) + 1)))
                * Real.exp (-(Real.pi * lam))) := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left hπ (mul_nonneg hC₁ (Real.rpow_nonneg hA0.le N₁))
          · exact mul_le_mul_of_nonneg_right hK (Real.exp_pos _).le
          · exact mul_nonneg (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ 1 + B) _)
              (Real.exp_pos _).le
          · exact mul_nonneg (mul_nonneg hC₁ (Real.rpow_nonneg hA0.le N₁))
              (pow_nonneg Real.pi_pos.le l)
      _ = cW * (A ^ N₁ * A ^ (N₀ * (M₁ + (l : ℝ) + 1))) * Real.exp (-(Real.pi * lam)) := by
          rw [hcWdef]; ring
      _ = cW * A ^ (N₁ + N₀ * (M₁ + (l : ℝ) + 1)) * Real.exp (-(Real.pi * lam)) := by
          rw [hAexp]
  have ht2 : C₂ * A ^ N₂ * Real.pi ^ m * (Real.exp (-(Real.pi * lam)) * tailDecay M₂ m)
      ≤ cT * A ^ N₂ * Real.exp (-(Real.pi * lam)) := by
    have hπ : Real.pi ^ m ≤ Real.pi ^ l := pow_le_pow_right₀ one_le_pi hm
    have htd : tailDecay M₂ m ≤ tailDecay M₂ l := tailDecay_mono hM₂ hm
    have hprod : Real.pi ^ m * tailDecay M₂ m ≤ Real.pi ^ l * tailDecay M₂ l :=
      mul_le_mul hπ htd (tailDecay_nonneg M₂ m) (pow_nonneg Real.pi_pos.le l)
    calc C₂ * A ^ N₂ * Real.pi ^ m * (Real.exp (-(Real.pi * lam)) * tailDecay M₂ m)
        = (C₂ * A ^ N₂) * (Real.pi ^ m * tailDecay M₂ m)
            * Real.exp (-(Real.pi * lam)) := by ring
      _ ≤ (C₂ * A ^ N₂) * (Real.pi ^ l * tailDecay M₂ l) * Real.exp (-(Real.pi * lam)) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hprod (mul_nonneg hC₂ (Real.rpow_nonneg hA0.le N₂)))
            (Real.exp_pos _).le
      _ = cT * A ^ N₂ * Real.exp (-(Real.pi * lam)) := by rw [hcTdef]; ring
  have hfin : cW * A ^ (N₁ + N₀ * (M₁ + (l : ℝ) + 1)) * Real.exp (-(Real.pi * lam))
      + cT * A ^ N₂ * Real.exp (-(Real.pi * lam))
      ≤ (cW + cT) * A ^ (N₁ + N₀ * (M₁ + (l : ℝ) + 1) + N₂) * Real.exp (-(Real.pi * lam)) := by
    have hYle : N₁ + N₀ * (M₁ + (l : ℝ) + 1) ≤ N₁ + N₀ * (M₁ + (l : ℝ) + 1) + N₂ := by
      linarith
    have hN₂le : N₂ ≤ N₁ + N₀ * (M₁ + (l : ℝ) + 1) + N₂ := by
      have : (0 : ℝ) ≤ N₁ + N₀ * (M₁ + (l : ℝ) + 1) :=
        add_nonneg hN₁ (mul_nonneg hN₀ (by linarith))
      linarith
    have h1 : cW * A ^ (N₁ + N₀ * (M₁ + (l : ℝ) + 1))
        ≤ cW * A ^ (N₁ + N₀ * (M₁ + (l : ℝ) + 1) + N₂) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hA1 hYle) hcW0
    have h2 : cT * A ^ N₂ ≤ cT * A ^ (N₁ + N₀ * (M₁ + (l : ℝ) + 1) + N₂) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hA1 hN₂le) hcT0
    have hs : cW * A ^ (N₁ + N₀ * (M₁ + (l : ℝ) + 1)) + cT * A ^ N₂
        ≤ (cW + cT) * A ^ (N₁ + N₀ * (M₁ + (l : ℝ) + 1) + N₂) := by
      have : (cW + cT) * A ^ (N₁ + N₀ * (M₁ + (l : ℝ) + 1) + N₂)
          = cW * A ^ (N₁ + N₀ * (M₁ + (l : ℝ) + 1) + N₂)
            + cT * A ^ (N₁ + N₀ * (M₁ + (l : ℝ) + 1) + N₂) := by ring
      linarith
    calc cW * A ^ (N₁ + N₀ * (M₁ + (l : ℝ) + 1)) * Real.exp (-(Real.pi * lam))
          + cT * A ^ N₂ * Real.exp (-(Real.pi * lam))
        = (cW * A ^ (N₁ + N₀ * (M₁ + (l : ℝ) + 1)) + cT * A ^ N₂)
            * Real.exp (-(Real.pi * lam)) := by ring
      _ ≤ ((cW + cT) * A ^ (N₁ + N₀ * (M₁ + (l : ℝ) + 1) + N₂))
            * Real.exp (-(Real.pi * lam)) := mul_le_mul_of_nonneg_right hs (Real.exp_pos _).le
      _ = (cW + cT) * A ^ (N₁ + N₀ * (M₁ + (l : ℝ) + 1) + N₂)
            * Real.exp (-(Real.pi * lam)) := by ring
  calc ‖(∫ t in Set.Icc (1 : ℝ) B, F t) + (∫ t in Set.Ioi B, F t)‖
      ≤ ‖∫ t in Set.Icc (1 : ℝ) B, F t‖ + ‖∫ t in Set.Ioi B, F t‖ := norm_add_le _ _
    _ ≤ (∫ t in Set.Icc (1 : ℝ) B, ‖F t‖) + (∫ t in Set.Ioi B, ‖F t‖) :=
        add_le_add (norm_integral_le_integral_norm (fun t : ℝ => F t))
          (norm_integral_le_integral_norm (fun t : ℝ => F t))
    _ ≤ C₁ * A ^ N₁ * Real.pi ^ m
          * ((1 + B) ^ (M₁ + (l : ℝ) + 1) * Real.exp (-(Real.pi * lam)))
        + C₂ * A ^ N₂ * Real.pi ^ m * (Real.exp (-(Real.pi * lam)) * tailDecay M₂ m) :=
        add_le_add hwin_bd htail_bd
    _ ≤ (cW + cT) * A ^ (N₁ + N₀ * (M₁ + (l : ℝ) + 1) + N₂)
          * Real.exp (-(Real.pi * lam)) := by linarith
    _ = (C₁ * Real.pi ^ l * 2 ^ (M₁ + (l : ℝ) + 1) + C₂ * Real.pi ^ l * tailDecay M₂ l)
          * A ^ (N₁ + N₀ * (M₁ + (l : ℝ) + 1) + N₂) * Real.exp (-(Real.pi * lam)) := by
        rw [hcWdef, hcTdef]

end Work.Asymptotics
