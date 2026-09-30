import Mathlib
import Submission.Work.BMF.halasz_defs
import Submission.Work.BMF.halasz_basic
import Submission.Work.BMF.halasz_mertens_aux
import Submission.Commons.NumberTheory.Mertens.primeRecips_sub_loglog_bound
import Submission.Work.BMF.HL.sum_log_div_prime_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Support lemmas for `Work.BMF.halasz_casdiv`

Prime-power sum estimates, elementary two-sided bounds for `Wsup`, the local bounded-difference
estimate and the scale comparison.  All constants are absolute.
-/

open scoped BigOperators MeasureTheory
open MeasureTheory intervalIntegral Finset

namespace Work.BMF

lemma Zrcp_le_max : ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
    Zrcp t ≤ max (Real.log (Real.log t)) 0 + C := by
  obtain ⟨C_Z, hC_Z, hZ⟩ := Commons.NumberTheory.Mertens.primeRecips_sub_loglog_bound
  refine ⟨C_Z + Zrcp 11 + 1, by have h := Zrcp_nonneg 11; linarith, ?_⟩
  have h11 : (0:ℝ) ≤ (∑ p ∈ (⌊(11:ℝ)⌋₊).primesLE, 1 / (p:ℝ)) :=
    Finset.sum_nonneg (fun p _ => by positivity)
  intro t
  by_cases ht : 11 ≤ t
  · have hb := (abs_le.mp (hZ t ht)).2
    have h1 : Real.log (Real.log t) ≤ max (Real.log (Real.log t)) 0 := le_max_left _ _
    unfold Zrcp at hb ⊢
    linarith
  · push_neg at ht
    have hmono : Zrcp t ≤ Zrcp 11 := Zrcp_mono ht.le
    have h1 : (0:ℝ) ≤ max (Real.log (Real.log t)) 0 := le_max_right _ _
    linarith

theorem sum_prime_rpow_le : ∃ C : ℝ, 0 < C ∧ ∀ x α : ℝ, 0 < α → α ≤ 1 →
    (∑ p ∈ (⌊x⌋₊).primesLE, (p : ℝ) ^ (-(1 + α))) ≤ Real.log (1 / α) + C := by
  obtain ⟨C₁, hC₁, hZ⟩ := Zrcp_le_max
  obtain ⟨C_t, hC_t, ht⟩ := halasz_mertens_aux.2.2
  refine ⟨C₁ + C_t + Zrcp 11 + 2, by have := Zrcp_nonneg 11; linarith, ?_⟩
  intro x α hα hα1
  have hloginv_nn : 0 ≤ Real.log (1 / α) := Real.log_nonneg (by rw [le_div_iff₀ hα]; linarith)
  have h11nn : (0:ℝ) ≤ Zrcp 11 := Zrcp_nonneg 11
  have hpt : ∀ p : ℕ, p.Prime → (p : ℝ) ^ (-(1 + α)) ≤ 1 / (p : ℝ) := by
    intro p hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    have hp0 : (0:ℝ) < p := by linarith
    rw [Real.rpow_neg hp0.le, one_div]
    rw [inv_le_inv₀ (by positivity) hp0]
    calc (p : ℝ) = (p:ℝ) ^ (1:ℝ) := (Real.rpow_one _).symm
      _ ≤ (p:ℝ) ^ (1 + α) := (Real.rpow_le_rpow_left_iff hp1).mpr (by linarith)
  set y : ℝ := Real.exp (1 / α) with hy
  have h1div1 : (1:ℝ) ≤ 1 / α := by rw [le_div_iff₀ hα]; linarith
  have hy2 : 2 < y := by
    rw [hy]
    have h2e : (2:ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    exact lt_of_lt_of_le h2e (Real.exp_le_exp.mpr h1div1)
  have hαy : α * Real.log y = 1 := by
    rw [hy, Real.log_exp]; field_simp
  have hlogy : Real.log (Real.log y) = Real.log (1 / α) := by rw [hy, Real.log_exp]
  have hlogynn : 0 ≤ Real.log (Real.log y) := by rw [hlogy]; exact hloginv_nn
  by_cases hx11 : x < 11
  · have hle : (∑ p ∈ (⌊x⌋₊).primesLE, (p : ℝ) ^ (-(1 + α))) ≤ Zrcp 11 := by
      have hsub : (⌊x⌋₊).primesLE ⊆ (⌊(11:ℝ)⌋₊).primesLE := by
        intro p hp
        rw [Nat.mem_primesLE] at hp ⊢
        exact ⟨le_trans hp.1 (Nat.floor_mono (le_of_lt hx11)), hp.2⟩
      calc (∑ p ∈ (⌊x⌋₊).primesLE, (p : ℝ) ^ (-(1 + α)))
          ≤ ∑ p ∈ (⌊x⌋₊).primesLE, 1 / (p : ℝ) :=
            Finset.sum_le_sum (fun p hp => hpt p (Nat.mem_primesLE.mp hp).2)
        _ ≤ ∑ p ∈ (⌊(11:ℝ)⌋₊).primesLE, 1 / (p : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)
        _ = Zrcp 11 := by norm_num [Zrcp]
    linarith [hle, hloginv_nn, hC₁, hC_t, h11nn]
  · push_neg at hx11
    by_cases hxy : y ≤ x
    · have hZbound : Zrcp y ≤ Real.log (1 / α) + C₁ := by
        have hthis := hZ y
        rw [max_eq_left hlogynn, hlogy] at hthis
        linarith [hthis]
      have hsplit := sum_filter_add_sum_filter_not ((⌊x⌋₊).primesLE)
        (fun p : ℕ => (p : ℝ) ≤ y) (fun p => (p : ℝ) ^ (-(1 + α)))
      rw [← hsplit]
      have h1 : (∑ p ∈ ((⌊x⌋₊).primesLE.filter (fun p : ℕ => (p : ℝ) ≤ y)),
            (p : ℝ) ^ (-(1 + α))) ≤ Zrcp y := by
        have hsub : ((⌊x⌋₊).primesLE.filter (fun p : ℕ => (p:ℝ) ≤ y)) ⊆ (⌊y⌋₊).primesLE := by
          intro p hp
          rw [Finset.mem_filter] at hp
          rw [Nat.mem_primesLE] at hp ⊢
          exact ⟨Nat.le_floor hp.2, hp.1.2⟩
        calc (∑ p ∈ ((⌊x⌋₊).primesLE.filter (fun p : ℕ => (p : ℝ) ≤ y)),
                (p : ℝ) ^ (-(1 + α)))
            ≤ ∑ p ∈ ((⌊x⌋₊).primesLE.filter (fun p : ℕ => (p : ℝ) ≤ y)), 1 / (p : ℝ) :=
              Finset.sum_le_sum (fun p hp => hpt p (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2)
          _ ≤ ∑ p ∈ (⌊y⌋₊).primesLE, 1 / (p : ℝ) :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)
          _ = Zrcp y := rfl
      have h2 : (∑ p ∈ ((⌊x⌋₊).primesLE.filter (fun p : ℕ => ¬ (p : ℝ) ≤ y)),
            (p : ℝ) ^ (-(1 + α))) ≤ C_t := by
        have hfil : ((⌊x⌋₊).primesLE.filter (fun p : ℕ => ¬ (p:ℝ) ≤ y))
            = ((⌊x⌋₊).primesLE.filter (fun p : ℕ => y < (p:ℝ))) :=
          Finset.filter_congr (fun p _ => not_le)
        rw [hfil]
        refine le_trans (le_of_eq ?_) (ht α y x hα hα1 hy2 hx11 (le_of_eq hαy.symm))
        apply Finset.sum_congr rfl
        intro p hp
        rw [Real.rpow_neg (by positivity), one_div]
      linarith [h1, h2, hZbound, h11nn]
    · push_neg at hxy
      have hle : (∑ p ∈ (⌊x⌋₊).primesLE, (p : ℝ) ^ (-(1 + α))) ≤ Zrcp x :=
        calc (∑ p ∈ (⌊x⌋₊).primesLE, (p : ℝ) ^ (-(1 + α)))
            ≤ ∑ p ∈ (⌊x⌋₊).primesLE, 1 / (p : ℝ) :=
              Finset.sum_le_sum (fun p hp => hpt p (Nat.mem_primesLE.mp hp).2)
          _ = Zrcp x := rfl
      have hZbound : Zrcp x ≤ Real.log (1 / α) + C₁ := by
        have hmono : max (Real.log (Real.log x)) 0 ≤ max (Real.log (Real.log y)) 0 := by
          refine max_le_max ?_ le_rfl
          refine Real.log_le_log ?_ ?_
          · exact Real.log_pos (by linarith)
          · have hxy' : x < Real.exp (1 / α) := by rw [← hy]; exact hxy
            have hlt := Real.log_lt_log (by linarith : (0:ℝ) < x) hxy'
            rw [Real.log_exp] at hlt
            have hval : Real.log y = 1 / α := (eq_div_iff (ne_of_gt hα)).mpr (by rw [mul_comm]; exact hαy)
            linarith [hlt, hval]
        have hthis := hZ x
        rw [hlogy, max_eq_left hloginv_nn] at hmono
        linarith [hmono, hthis]
      linarith [hle, hZbound]

/-- `Σ_{p ≤ x} (log p) p^{-(1+α)} ≤ C log x` when `α log x ≥ 1`, `3 ≤ x`. -/
theorem sum_log_prime_rpow_le : ∃ C : ℝ, 0 < C ∧ ∀ x α : ℝ, 3 ≤ x → 0 < α →
    1 ≤ α * Real.log x →
    (∑ p ∈ (⌊x⌋₊).primesLE, Real.log p * (p : ℝ) ^ (-(1 + α))) ≤ C * Real.log x := by
  obtain ⟨C_l, hC_l, hl⟩ := Work.BMF.HL.sum_log_div_prime_le
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hexp : 0 < Real.exp (-(1/2:ℝ)) := Real.exp_pos _
  refine ⟨C_l * (1/2 + Real.exp (-(1/2))) + C_l * Real.log 4 / Real.log 3 + 1, ?_, ?_⟩
  · have h1 : 0 < C_l * (1/2 + Real.exp (-(1/2))) := mul_pos hC_l (by linarith)
    have h2 : 0 < C_l * Real.log 4 / Real.log 3 := div_pos (mul_pos hC_l hlog4) hlog3
    linarith
  intro x α hx hα hαx
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hpoint : ∀ p : ℕ, Nat.Prime p → Real.log p * (p:ℝ) ^ (-(1 + α)) ≤ Real.log p / (p:ℝ) := by
    intro p hp
    have hp1 : (1:ℝ) < p := by exact_mod_cast hp.one_lt
    have hp0 : (0:ℝ) < p := by linarith
    have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
    have hle : (p:ℝ) ^ (-(1 + α)) ≤ 1 / (p:ℝ) := by
      rw [Real.rpow_neg hp0.le, one_div, inv_le_inv₀ (by positivity) hp0]
      calc (p : ℝ) = (p:ℝ) ^ (1:ℝ) := (Real.rpow_one _).symm
        _ ≤ (p:ℝ) ^ (1 + α) := (Real.rpow_le_rpow_left_iff hp1).mpr (by linarith)
    calc Real.log p * (p:ℝ) ^ (-(1 + α)) ≤ Real.log p * (1 / (p:ℝ)) :=
          mul_le_mul_of_nonneg_left hle hlogp
      _ = Real.log p / (p:ℝ) := by ring
  have hpoint2 : ∀ p : ℕ, Nat.Prime p → Real.sqrt x < (p:ℝ) →
      Real.log p * (p:ℝ) ^ (-(1 + α)) ≤ Real.exp (-(1/2)) * (Real.log p / (p:ℝ)) := by
    intro p hp hpgt
    have hp1 : (1:ℝ) < p := by exact_mod_cast hp.one_lt
    have hp0 : (0:ℝ) < p := by linarith
    have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
    have hsqrt0 : (0:ℝ) < Real.sqrt x := Real.sqrt_pos.mpr (by linarith)
    have hxα : Real.exp (1/2) ≤ Real.sqrt x ^ α := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by linarith : (0:ℝ) ≤ x)]
      rw [Real.rpow_def_of_pos (by linarith : (0:ℝ) < x)]
      rw [Real.exp_le_exp]; nlinarith [hαx]
    have hpa : (p:ℝ) ^ (-α) ≤ Real.exp (-(1/2)) := by
      have ha1 : (Real.sqrt x) ^ (-α) ≤ Real.exp (-(1/2)) := by
        rw [Real.rpow_neg hsqrt0.le, Real.exp_neg]
        exact (inv_le_inv₀ (Real.rpow_pos_of_pos hsqrt0 α) (Real.exp_pos _)).mpr hxα
      have ha2 : (p:ℝ) ^ (-α) ≤ (Real.sqrt x) ^ (-α) := by
        rw [Real.rpow_neg hp0.le, Real.rpow_neg hsqrt0.le]
        exact (inv_le_inv₀ (Real.rpow_pos_of_pos hp0 α) (Real.rpow_pos_of_pos hsqrt0 α)).mpr
          (Real.rpow_le_rpow hsqrt0.le hpgt.le hα.le)
      linarith
    calc Real.log p * (p:ℝ) ^ (-(1 + α))
        = Real.log p * ((p:ℝ)^(-α) * (p:ℝ)⁻¹) := by
          rw [show -(1 + α) = -α + (-1) by ring, Real.rpow_add hp0]
          rw [Real.rpow_neg_one]
      _ ≤ Real.log p * (Real.exp (-(1/2)) * (p:ℝ)⁻¹) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpa (by positivity)) hlogp
      _ = Real.exp (-(1/2)) * (Real.log p / (p:ℝ)) := by ring
  by_cases hx4 : x ≤ 4
  · have hle : (∑ p ∈ (⌊x⌋₊).primesLE, Real.log p * (p:ℝ)^(-(1+α))) ≤ C_l * Real.log 4 := by
      have hsub : (⌊x⌋₊).primesLE ⊆ (⌊(4:ℝ)⌋₊).primesLE := by
        intro p hp
        rw [Nat.mem_primesLE] at hp ⊢
        exact ⟨le_trans hp.1 (Nat.floor_mono hx4), hp.2⟩
      calc (∑ p ∈ (⌊x⌋₊).primesLE, Real.log p * (p:ℝ)^(-(1+α)))
          ≤ ∑ p ∈ (⌊x⌋₊).primesLE, Real.log p / (p:ℝ) :=
            Finset.sum_le_sum (fun p hp => hpoint p (Nat.mem_primesLE.mp hp).2)
        _ ≤ ∑ p ∈ (⌊(4:ℝ)⌋₊).primesLE, Real.log p / (p:ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)
        _ ≤ C_l * Real.log 4 := hl 4 (by norm_num)
    have h43 : Real.log 3 ≤ Real.log x := Real.log_le_log (by norm_num) hx
    have hkey : C_l * Real.log 4 ≤
        (C_l * (1/2 + Real.exp (-(1/2))) + C_l * Real.log 4 / Real.log 3 + 1) * Real.log x := by
      have hdecomp : C_l * Real.log 4 = (C_l * Real.log 4 / Real.log 3) * Real.log 3 := by
        field_simp
      have h1 : (C_l * Real.log 4 / Real.log 3) * Real.log 3 ≤
          (C_l * Real.log 4 / Real.log 3) * Real.log x :=
        mul_le_mul_of_nonneg_left h43 (le_of_lt (div_pos (mul_pos hC_l hlog4) hlog3))
      have h2 : (0:ℝ) ≤ C_l * (1/2 + Real.exp (-(1/2))) :=
        mul_nonneg hC_l.le (by linarith)
      nlinarith [hdecomp, h1, h2, hlogx]
    linarith [hle, hkey]
  · push_neg at hx4
    have hsqrt2 : (2:ℝ) ≤ Real.sqrt x := by
      rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith
    have hsplit := sum_filter_add_sum_filter_not ((⌊x⌋₊).primesLE)
      (fun p : ℕ => (p:ℝ) ≤ Real.sqrt x) (fun p => Real.log p * (p:ℝ)^(-(1+α)))
    rw [← hsplit]
    have hA : (∑ p ∈ ((⌊x⌋₊).primesLE.filter (fun p:ℕ => (p:ℝ) ≤ Real.sqrt x)),
          Real.log p * (p:ℝ)^(-(1+α))) ≤ C_l * Real.log (Real.sqrt x) := by
      have hsub : ((⌊x⌋₊).primesLE.filter (fun p:ℕ => (p:ℝ) ≤ Real.sqrt x)) ⊆ (⌊Real.sqrt x⌋₊).primesLE := by
        intro p hp
        rw [Finset.mem_filter] at hp
        rw [Nat.mem_primesLE] at hp ⊢
        exact ⟨Nat.le_floor hp.2, hp.1.2⟩
      have h1 : (∑ p ∈ ((⌊x⌋₊).primesLE.filter (fun p:ℕ => (p:ℝ) ≤ Real.sqrt x)),
            Real.log p * (p:ℝ)^(-(1+α))) ≤
          ∑ p ∈ ((⌊x⌋₊).primesLE.filter (fun p:ℕ => (p:ℝ) ≤ Real.sqrt x)), Real.log p / (p:ℝ) :=
        Finset.sum_le_sum (fun p hp => hpoint p (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2)
      have h2 : (∑ p ∈ ((⌊x⌋₊).primesLE.filter (fun p:ℕ => (p:ℝ) ≤ Real.sqrt x)), Real.log p / (p:ℝ))
          ≤ ∑ p ∈ (⌊Real.sqrt x⌋₊).primesLE, Real.log p / (p:ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)
      exact le_trans (le_trans h1 h2) (hl (Real.sqrt x) hsqrt2)
    have hB : (∑ p ∈ ((⌊x⌋₊).primesLE.filter (fun p:ℕ => ¬ (p:ℝ) ≤ Real.sqrt x)),
          Real.log p * (p:ℝ)^(-(1+α))) ≤ Real.exp (-(1/2)) * (C_l * Real.log x) := by
      have hfil : ((⌊x⌋₊).primesLE.filter (fun p:ℕ => ¬ (p:ℝ) ≤ Real.sqrt x))
          = ((⌊x⌋₊).primesLE.filter (fun p:ℕ => Real.sqrt x < (p:ℝ))) :=
        Finset.filter_congr (fun p _ => not_le)
      rw [hfil]
      have h1 : (∑ p ∈ ((⌊x⌋₊).primesLE.filter (fun p:ℕ => Real.sqrt x < (p:ℝ))),
            Real.log p * (p:ℝ)^(-(1+α))) ≤
          ∑ p ∈ ((⌊x⌋₊).primesLE.filter (fun p:ℕ => Real.sqrt x < (p:ℝ))),
            Real.exp (-(1/2)) * (Real.log p / (p:ℝ)) :=
        Finset.sum_le_sum (fun p hp => hpoint2 p (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2
          (Finset.mem_filter.mp hp).2)
      rw [← Finset.mul_sum] at h1
      have h2 : (∑ p ∈ ((⌊x⌋₊).primesLE.filter (fun p:ℕ => Real.sqrt x < (p:ℝ))), Real.log p / (p:ℝ))
          ≤ ∑ p ∈ (⌊x⌋₊).primesLE, Real.log p / (p:ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun p _ _ => by positivity)
      have h3 : (∑ p ∈ (⌊x⌋₊).primesLE, Real.log p / (p:ℝ)) ≤ C_l * Real.log x := hl x (by linarith)
      calc (∑ p ∈ ((⌊x⌋₊).primesLE.filter (fun p:ℕ => Real.sqrt x < (p:ℝ))),
            Real.log p * (p:ℝ)^(-(1+α)))
          ≤ Real.exp (-(1/2)) * (∑ p ∈ ((⌊x⌋₊).primesLE.filter (fun p:ℕ => Real.sqrt x < (p:ℝ))),
              Real.log p / (p:ℝ)) := h1
        _ ≤ Real.exp (-(1/2)) * (C_l * Real.log x) :=
            mul_le_mul_of_nonneg_left (le_trans h2 h3) hexp.le
    have hsqrt : Real.log (Real.sqrt x) = Real.log x / 2 := Real.log_sqrt (by linarith)
    have htot : (∑ p ∈ (⌊x⌋₊).primesLE, Real.log p * (p:ℝ)^(-(1+α)))
        ≤ C_l * (Real.log x / 2) + Real.exp (-(1/2)) * (C_l * Real.log x) := by
      rw [hsqrt] at hA; linarith [hA, hB]
    have hfin : C_l * (Real.log x / 2) + Real.exp (-(1/2)) * (C_l * Real.log x)
        ≤ (C_l * (1/2 + Real.exp (-(1/2))) + C_l * Real.log 4 / Real.log 3 + 1) * Real.log x := by
      have h2 : (0:ℝ) ≤ C_l * Real.log 4 / Real.log 3 := (div_pos (mul_pos hC_l hlog4) hlog3).le
      nlinarith [hC_l, hexp, hlogx, h2]
    linarith [htot, hfin]


/-- Lower bound for `Wsup`. -/
theorem Wsup_lower : ∃ C : ℝ, 0 < C ∧ ∀ (f : ℕ → ℂ), (∀ n, ‖f n‖ ≤ 1) → ∀ x α T : ℝ,
    0 < α → α ≤ 1 → 0 ≤ T → -(Real.log (1 / α) + C) ≤ Wsup f x α T := by
  obtain ⟨C₀, hC₀, hsum⟩ := sum_prime_rpow_le
  refine ⟨C₀, hC₀, ?_⟩
  intro f hb x α T hα hα1 hT
  have hbdd : BddAbove (Set.range (fun t : {t : ℝ // |t| ≤ T} =>
      (vF f x (((1+α:ℝ):ℂ) + t.1 * Complex.I)).re)) := by
    refine ⟨∑ p ∈ (⌊x⌋₊).primesLE, (p:ℝ)^(-(1+α)), ?_⟩
    rintro y ⟨t, rfl⟩
    calc (vF f x (((1+α:ℝ):ℂ) + t.1 * Complex.I)).re
        ≤ ∑ p ∈ (⌊x⌋₊).primesLE, ‖f p * ((p:ℂ)^(-(((1+α:ℝ):ℂ) + t.1 * Complex.I)))‖ := by
          rw [vF, Complex.re_sum]
          exact Finset.sum_le_sum (fun p _ => Complex.re_le_norm _)
      _ ≤ ∑ p ∈ (⌊x⌋₊).primesLE, (p:ℝ)^(-(1+α)) := by
          refine Finset.sum_le_sum (fun p hp => ?_)
          have hp2 : 0 < p := (Nat.mem_primesLE.mp hp).2.pos
          rw [norm_mul, Complex.norm_natCast_cpow_of_pos hp2,
            show (-(((1+α:ℝ):ℂ) + t.1 * Complex.I)).re = -(1+α) by simp]
          calc ‖f p‖ * (p:ℝ)^(-(1+α)) ≤ 1 * (p:ℝ)^(-(1+α)) :=
                mul_le_mul_of_nonneg_right (hb p) (Real.rpow_nonneg (Nat.cast_nonneg p) _)
            _ = (p:ℝ)^(-(1+α)) := one_mul _
  have h0 : (vF f x (((1+α:ℝ):ℂ) + (0:ℝ) * Complex.I)).re ≤ Wsup f x α T :=
    le_ciSup (f := fun t : {t : ℝ // |t| ≤ T} =>
        (vF f x (((1+α:ℝ):ℂ) + t.1 * Complex.I)).re) hbdd ⟨0, by rw [abs_zero]; exact hT⟩
  have hterm : ∀ p ∈ (⌊x⌋₊).primesLE,
      -((p:ℝ)^(-(1+α))) ≤ (f p * ((p:ℂ)^(-(((1+α:ℝ):ℂ) + (0:ℝ) * Complex.I)))).re := by
    intro p hp
    have hp2 : 0 < p := (Nat.mem_primesLE.mp hp).2.pos
    have h1 : -‖f p * ((p:ℂ)^(-(((1+α:ℝ):ℂ) + (0:ℝ) * Complex.I)))‖ ≤
        (f p * ((p:ℂ)^(-(((1+α:ℝ):ℂ) + (0:ℝ) * Complex.I)))).re := by
      have := Complex.re_le_norm (-(f p * ((p:ℂ)^(-(((1+α:ℝ):ℂ) + (0:ℝ) * Complex.I)))))
      rw [Complex.neg_re, norm_neg] at this; linarith
    have h2 : ‖f p * ((p:ℂ)^(-(((1+α:ℝ):ℂ) + (0:ℝ) * Complex.I)))‖ ≤ (p:ℝ)^(-(1+α)) := by
      rw [norm_mul, Complex.norm_natCast_cpow_of_pos hp2,
        show (-(((1+α:ℝ):ℂ) + (0:ℝ) * Complex.I)).re = -(1+α) by simp]
      calc ‖f p‖ * (p:ℝ)^(-(1+α)) ≤ 1 * (p:ℝ)^(-(1+α)) :=
            mul_le_mul_of_nonneg_right (hb p) (Real.rpow_nonneg (Nat.cast_nonneg p) _)
        _ = (p:ℝ)^(-(1+α)) := one_mul _
    linarith
  have hre : (vF f x (((1+α:ℝ):ℂ) + (0:ℝ) * Complex.I)).re =
      ∑ p ∈ (⌊x⌋₊).primesLE, (f p * ((p:ℂ)^(-(((1+α:ℝ):ℂ) + (0:ℝ) * Complex.I)))).re := by
    rw [vF, Complex.re_sum]
  calc -(Real.log (1/α) + C₀) ≤ - ∑ p ∈ (⌊x⌋₊).primesLE, (p:ℝ)^(-(1+α)) := by
        rw [neg_le_neg_iff]; exact hsum x α hα hα1
    _ = ∑ p ∈ (⌊x⌋₊).primesLE, -((p:ℝ)^(-(1+α))) := by rw [Finset.sum_neg_distrib]
    _ ≤ ∑ p ∈ (⌊x⌋₊).primesLE,
          (f p * ((p:ℂ)^(-(((1+α:ℝ):ℂ) + (0:ℝ) * Complex.I)))).re := Finset.sum_le_sum hterm
    _ = (vF f x (((1+α:ℝ):ℂ) + (0:ℝ) * Complex.I)).re := hre.symm
    _ ≤ Wsup f x α T := h0

/-- `exp (Wsup f x (1/log x) T) ≥ c / log x`. -/
theorem Wsup_exp_lower : ∃ c : ℝ, 0 < c ∧ ∀ (f : ℕ → ℂ), (∀ n, ‖f n‖ ≤ 1) →
    ∀ x T : ℝ, 3 ≤ x → 0 ≤ T → c / Real.log x ≤ Real.exp (Wsup f x (1 / Real.log x) T) := by
  obtain ⟨C₀, hC₀, hlow⟩ := Wsup_lower
  refine ⟨Real.exp (-C₀), Real.exp_pos _, ?_⟩
  intro f hb x T hx hT
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogx1 : 1 ≤ Real.log x := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  have hα : 0 < 1 / Real.log x := by positivity
  have hα1 : 1 / Real.log x ≤ 1 := by rw [div_le_iff₀ hlogx, one_mul]; exact hlogx1
  have h := hlow f hb x (1 / Real.log x) T hα hα1 hT
  have hval : Real.log (1 / (1 / Real.log x)) = Real.log (Real.log x) := by rw [one_div_one_div]
  have hexp : Real.exp (-(Real.log (1 / (1 / Real.log x)) + C₀)) = Real.exp (-C₀) / Real.log x := by
    rw [hval, Real.exp_neg, Real.exp_add, Real.exp_neg, Real.exp_log hlogx]
    field_simp
  calc Real.exp (-C₀) / Real.log x = Real.exp (-(Real.log (1 / (1 / Real.log x)) + C₀)) := hexp.symm
    _ ≤ Real.exp (Wsup f x (1 / Real.log x) T) := Real.exp_le_exp.mpr h


/-- Local bounded-difference estimate for `Wsup` (ratio `≤ 2`). -/
theorem Wsup_loc : ∃ C : ℝ, 0 < C ∧ ∀ (f : ℕ → ℂ), (∀ n, ‖f n‖ ≤ 1) → ∀ x β T : ℝ,
    3 ≤ x → 1 / Real.log x ≤ β → β ≤ 2 / Real.log x → 0 ≤ T →
      Wsup f x (1 / Real.log x) T ≤ Wsup f x β T + C := by
  obtain ⟨C₀, hC₀, hsum⟩ := sum_log_prime_rpow_le
  refine ⟨C₀, hC₀, ?_⟩
  intro f hb x β T hx hβ1 hβ2 hT
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hα₀ : 0 < 1 / Real.log x := by positivity
  have hα₀1 : 1 / Real.log x ≤ 1 := by
    rw [div_le_iff₀ hlogx, one_mul]
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  have hα₀log : 1 ≤ 1 / Real.log x * Real.log x := by
    rw [div_mul_cancel₀ _ (ne_of_gt hlogx)]
  have hβ0 : 0 < β := lt_of_lt_of_le hα₀ hβ1
  have hβ2' : β ≤ 2 * (1 / Real.log x) := by rw [div_eq_mul_one_div] at hβ2; exact hβ2
  set S : ℝ := ∑ p ∈ (⌊x⌋₊).primesLE,
    ((p:ℝ)^(-(1+(1/Real.log x))) - (p:ℝ)^(-(1+β))) with hS
  have hSbound : S ≤ C₀ := by
    have hterm : ∀ p ∈ (⌊x⌋₊).primesLE,
        (p:ℝ)^(-(1+(1/Real.log x))) - (p:ℝ)^(-(1+β)) ≤
          (1/Real.log x) * (Real.log p * (p:ℝ)^(-(1+(1/Real.log x)))) := by
      intro p hp
      have hp2 : 2 ≤ p := (Nat.mem_primesLE.mp hp).2.two_le
      have hp0 : (0:ℝ) < p := by exact_mod_cast (show (0:ℕ) < p by omega)
      have hp1 : (1:ℝ) ≤ p := by exact_mod_cast (show (1:ℕ) ≤ p by omega)
      have hlogp : 0 ≤ Real.log p := Real.log_nonneg hp1
      have hβα : β - 1/Real.log x ≤ 1/Real.log x := by linarith [hβ2']
      have hsplit : (p:ℝ)^(-(1+β)) = (p:ℝ)^(-(1+1/Real.log x)) * (p:ℝ)^(-(β - 1/Real.log x)) := by
        rw [← Real.rpow_add hp0]; congr 1; ring
      have h1 : 1 - (p:ℝ)^(-(β - 1/Real.log x)) ≤ (β - 1/Real.log x) * Real.log p := by
        rw [Real.rpow_neg hp0.le, Real.rpow_def_of_pos hp0, ← Real.exp_neg]
        have hA := Real.add_one_le_exp (-(Real.log p * (β - 1/Real.log x)))
        linarith [hA]
      calc (p:ℝ)^(-(1+(1/Real.log x))) - (p:ℝ)^(-(1+β))
          = (p:ℝ)^(-(1+(1/Real.log x))) * (1 - (p:ℝ)^(-(β - 1/Real.log x))) := by
            rw [hsplit]; ring
        _ ≤ (p:ℝ)^(-(1+(1/Real.log x))) * ((β - 1/Real.log x) * Real.log p) :=
            mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg (by linarith) _)
        _ ≤ (p:ℝ)^(-(1+(1/Real.log x))) * ((1/Real.log x) * Real.log p) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hβα hlogp)
              (Real.rpow_nonneg (by linarith) _)
        _ = (1/Real.log x) * (Real.log p * (p:ℝ)^(-(1+(1/Real.log x)))) := by ring
    have h1 : S ≤ (1/Real.log x) * ∑ p ∈ (⌊x⌋₊).primesLE,
        Real.log p * (p:ℝ)^(-(1+(1/Real.log x))) := by
      rw [hS, Finset.mul_sum]
      exact Finset.sum_le_sum hterm
    have h2 := hsum x (1/Real.log x) hx hα₀ hα₀log
    calc S ≤ (1/Real.log x) * ∑ p ∈ (⌊x⌋₊).primesLE,
            Real.log p * (p:ℝ)^(-(1+(1/Real.log x))) := h1
      _ ≤ (1/Real.log x) * (C₀ * Real.log x) := mul_le_mul_of_nonneg_left h2 hα₀.le
      _ = C₀ := by rw [mul_comm C₀]; field_simp
  have hbdd : BddAbove (Set.range (fun t : {t : ℝ // |t| ≤ T} =>
      (vF f x (((1+β:ℝ):ℂ) + t.1 * Complex.I)).re)) := by
    refine ⟨∑ p ∈ (⌊x⌋₊).primesLE, (p:ℝ)^(-(1+β)), ?_⟩
    rintro y ⟨t, rfl⟩
    calc (vF f x (((1+β:ℝ):ℂ) + t.1 * Complex.I)).re
        ≤ ∑ p ∈ (⌊x⌋₊).primesLE, ‖f p * ((p:ℂ)^(-(((1+β:ℝ):ℂ) + t.1 * Complex.I)))‖ := by
          rw [vF, Complex.re_sum]
          exact Finset.sum_le_sum (fun p _ => Complex.re_le_norm _)
      _ ≤ ∑ p ∈ (⌊x⌋₊).primesLE, (p:ℝ)^(-(1+β)) := by
          refine Finset.sum_le_sum (fun p hp => ?_)
          have hp2 : 0 < p := (Nat.mem_primesLE.mp hp).2.pos
          rw [norm_mul, Complex.norm_natCast_cpow_of_pos hp2,
            show (-(((1+β:ℝ):ℂ) + t.1 * Complex.I)).re = -(1+β) by simp]
          calc ‖f p‖ * (p:ℝ)^(-(1+β)) ≤ 1 * (p:ℝ)^(-(1+β)) :=
                mul_le_mul_of_nonneg_right (hb p) (Real.rpow_nonneg (Nat.cast_nonneg p) _)
            _ = (p:ℝ)^(-(1+β)) := one_mul _
  have hpt : ∀ t : {t : ℝ // |t| ≤ T},
      (vF f x (((1+(1/Real.log x):ℝ):ℂ) + t.1 * Complex.I)).re ≤
        (vF f x (((1+β:ℝ):ℂ) + t.1 * Complex.I)).re + S := by
    intro t
    have hterm2 : ∀ p ∈ (⌊x⌋₊).primesLE,
        (f p * ((p:ℂ)^(-(((1+(1/Real.log x):ℝ):ℂ) + t.1 * Complex.I)))).re
        - (f p * ((p:ℂ)^(-(((1+β:ℝ):ℂ) + t.1 * Complex.I)))).re
        ≤ (p:ℝ)^(-(1+(1/Real.log x))) - (p:ℝ)^(-(1+β)) := by
      intro p hp
      have hp0nat : 0 < p := Nat.Prime.pos (Nat.mem_primesLE.mp hp).2
      have hp0 : (0:ℝ) < p := by exact_mod_cast hp0nat
      have hp1 : (1:ℝ) ≤ p := by exact_mod_cast (show (1:ℕ) ≤ p by omega)
      have hpne' : (p:ℂ) ≠ 0 := by exact_mod_cast (Nat.Prime.ne_zero (Nat.mem_primesLE.mp hp).2)
      have hβα : β - 1/Real.log x ≤ 1/Real.log x := by linarith [hβ2']
      have hfac : (p:ℂ)^(-(((1+β:ℝ):ℂ) + t.1 * Complex.I))
          = (p:ℂ)^(-(((1+(1/Real.log x):ℝ):ℂ) + t.1 * Complex.I))
            * (p:ℂ)^(-(((β - 1/Real.log x:ℝ):ℂ))) := by
        rw [show (-(((1+β:ℝ):ℂ) + t.1 * Complex.I))
              = (-(((1+(1/Real.log x):ℝ):ℂ) + t.1 * Complex.I)) + (-(((β - 1/Real.log x:ℝ):ℂ)))
            by push_cast; ring,
          Complex.cpow_add _ _ hpne']
      have hreal : (p:ℂ)^(-(((β - 1/Real.log x:ℝ):ℂ)))
          = (((p:ℝ)^(-(β - 1/Real.log x)) : ℝ) : ℂ) := by
        rw [show (p:ℂ) = (((p:ℝ)):ℂ) by simp]
        rw [show -(((β - 1/Real.log x:ℝ):ℂ)) = (((-(β - 1/Real.log x):ℝ):ℂ)) by push_cast; ring]
        rw [← Complex.ofReal_cpow hp0.le]
      have hdiff : f p * ((p:ℂ)^(-(((1+(1/Real.log x):ℝ):ℂ) + t.1 * Complex.I)))
          - f p * ((p:ℂ)^(-(((1+β:ℝ):ℂ) + t.1 * Complex.I)))
          = (f p * ((p:ℂ)^(-(((1+(1/Real.log x):ℝ):ℂ) + t.1 * Complex.I))))
            * (1 - (((p:ℝ)^(-(β - 1/Real.log x)) : ℝ) : ℂ)) := by
        rw [hfac, hreal]; ring
      have hnorm1 : ‖(f p * ((p:ℂ)^(-(((1+(1/Real.log x):ℝ):ℂ) + t.1 * Complex.I))))‖
          ≤ (p:ℝ)^(-(1+(1/Real.log x))) := by
        rw [norm_mul, Complex.norm_natCast_cpow_of_pos hp0nat,
          show (-(((1+(1/Real.log x):ℝ):ℂ) + t.1 * Complex.I)).re = -(1+(1/Real.log x)) by simp]
        calc ‖f p‖ * (p:ℝ)^(-(1+(1/Real.log x))) ≤ 1 * (p:ℝ)^(-(1+(1/Real.log x))) :=
              mul_le_mul_of_nonneg_right (hb p) (Real.rpow_nonneg (Nat.cast_nonneg p) _)
          _ = _ := one_mul _
      have hnorm2 : ‖(1 - (((p:ℝ)^(-(β - 1/Real.log x)) : ℝ) : ℂ))‖
          = 1 - (p:ℝ)^(-(β - 1/Real.log x)) := by
        rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg]
        have hrle : (p:ℝ)^(-(β - 1/Real.log x)) ≤ 1 := by
          have h := Real.rpow_le_rpow_of_exponent_le hp1
            (show -(β - 1/Real.log x) ≤ 0 by linarith)
          rwa [Real.rpow_zero] at h
        linarith
      calc (f p * ((p:ℂ)^(-(((1+(1/Real.log x):ℝ):ℂ) + t.1 * Complex.I)))).re
            - (f p * ((p:ℂ)^(-(((1+β:ℝ):ℂ) + t.1 * Complex.I)))).re
          = ((f p * ((p:ℂ)^(-(((1+(1/Real.log x):ℝ):ℂ) + t.1 * Complex.I))))
              * (1 - (((p:ℝ)^(-(β - 1/Real.log x)) : ℝ) : ℂ))).re := by
            rw [← Complex.sub_re, hdiff]
        _ ≤ ‖(f p * ((p:ℂ)^(-(((1+(1/Real.log x):ℝ):ℂ) + t.1 * Complex.I))))
              * (1 - (((p:ℝ)^(-(β - 1/Real.log x)) : ℝ) : ℂ))‖ := Complex.re_le_norm _
        _ = ‖(f p * ((p:ℂ)^(-(((1+(1/Real.log x):ℝ):ℂ) + t.1 * Complex.I))))‖
              * ‖(1 - (((p:ℝ)^(-(β - 1/Real.log x)) : ℝ) : ℂ))‖ := norm_mul _ _
        _ ≤ (p:ℝ)^(-(1+(1/Real.log x))) * (1 - (p:ℝ)^(-(β - 1/Real.log x))) :=
            mul_le_mul hnorm1 (le_of_eq hnorm2) (by positivity) (Real.rpow_nonneg (by linarith) _)
        _ = (p:ℝ)^(-(1+(1/Real.log x))) - (p:ℝ)^(-(1+β)) := by
            rw [mul_sub, mul_one, ← Real.rpow_add hp0]
            congr 2; ring
    have hdiff_le : (vF f x (((1+(1/Real.log x):ℝ):ℂ) + t.1 * Complex.I)).re
        - (vF f x (((1+β:ℝ):ℂ) + t.1 * Complex.I)).re ≤ S := by
      rw [show (vF f x (((1+(1/Real.log x):ℝ):ℂ) + t.1 * Complex.I)).re
          - (vF f x (((1+β:ℝ):ℂ) + t.1 * Complex.I)).re
          = ∑ p ∈ (⌊x⌋₊).primesLE,
              ((f p * ((p:ℂ)^(-(((1+(1/Real.log x):ℝ):ℂ) + t.1 * Complex.I)))).re
             - (f p * ((p:ℂ)^(-(((1+β:ℝ):ℂ) + t.1 * Complex.I)))).re) by
            unfold vF; rw [Complex.re_sum, Complex.re_sum, ← Finset.sum_sub_distrib],
          hS]
      exact Finset.sum_le_sum hterm2
    linarith [hdiff_le]
  haveI : Nonempty {t : ℝ // |t| ≤ T} := ⟨⟨0, by rw [abs_zero]; exact hT⟩⟩
  unfold Wsup
  have hci : (⨆ (t : {t : ℝ // |t| ≤ T}),
        (vF f x (((1+(1/Real.log x):ℝ):ℂ) + t.1 * Complex.I)).re)
      ≤ (⨆ (t : {t : ℝ // |t| ≤ T}),
        (vF f x (((1+β:ℝ):ℂ) + t.1 * Complex.I)).re) + C₀ := by
    have hmid : (⨆ (t : {t : ℝ // |t| ≤ T}),
        (vF f x (((1+(1/Real.log x):ℝ):ℂ) + t.1 * Complex.I)).re)
        ≤ (⨆ (t : {t : ℝ // |t| ≤ T}),
          (vF f x (((1+β:ℝ):ℂ) + t.1 * Complex.I)).re) + S := by
      refine ciSup_le (fun t => ?_)
      have h1 := hpt t
      have h2 := le_ciSup (f := fun t : {t : ℝ // |t| ≤ T} =>
        (vF f x (((1+β:ℝ):ℂ) + t.1 * Complex.I)).re) hbdd t
      linarith
    linarith [hSbound, hmid]
  exact hci


/-- Raising the prime cut-off costs an absolute constant in `Wsup`. -/
theorem Wsup_scale : ∃ C : ℝ, 0 < C ∧ ∀ (f : ℕ → ℂ), (∀ n, ‖f n‖ ≤ 1) → ∀ y x α T : ℝ,
    2 < y → y ≤ x → 11 ≤ x → 0 < α → α ≤ 1 → 1 ≤ α * Real.log y → 0 ≤ T →
      Wsup f y α T ≤ Wsup f x α T + C := by
  obtain ⟨C₀, hC₀, ht⟩ := halasz_mertens_aux.2.2
  refine ⟨C₀, hC₀, ?_⟩
  intro f hb y x α T hy hyx hx11 hα hα1 hαy hT
  have hsub : (⌊y⌋₊).primesLE ⊆ (⌊x⌋₊).primesLE := by
    intro p hp
    rw [Nat.mem_primesLE] at hp ⊢
    exact ⟨le_trans hp.1 (Nat.floor_mono hyx), hp.2⟩
  have hsdiff : (⌊x⌋₊).primesLE \ (⌊y⌋₊).primesLE
      = (⌊x⌋₊).primesLE.filter (fun p : ℕ => y < (p:ℝ)) := by
    ext p
    rw [Finset.mem_sdiff, Finset.mem_filter, Nat.mem_primesLE, Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨hpx, hpp⟩, hny⟩
      refine ⟨⟨hpx, hpp⟩, ?_⟩
      by_contra h
      rw [not_lt] at h
      exact hny ⟨Nat.le_floor h, hpp⟩
    · rintro ⟨⟨hpx, hpp⟩, hyp⟩
      refine ⟨⟨hpx, hpp⟩, ?_⟩
      intro hmem
      exact absurd hyp (not_lt.mpr (le_trans (by exact_mod_cast hmem.1) (Nat.floor_le (by positivity))))
  have hS : (∑ p ∈ (⌊x⌋₊).primesLE \ (⌊y⌋₊).primesLE, (p:ℝ)^(-(1+α))) ≤ C₀ := by
    rw [hsdiff]
    refine le_trans (le_of_eq ?_) (ht α y x hα hα1 hy hx11 hαy)
    apply Finset.sum_congr rfl
    intro p hp
    rw [Real.rpow_neg (by positivity), one_div]
  have hpt : ∀ t : {t : ℝ // |t| ≤ T},
      (vF f y (((1+α:ℝ):ℂ) + t.1 * Complex.I)).re ≤
        (vF f x (((1+α:ℝ):ℂ) + t.1 * Complex.I)).re
        + ∑ p ∈ (⌊x⌋₊).primesLE \ (⌊y⌋₊).primesLE, (p:ℝ)^(-(1+α)) := by
    intro t
    have hdecomp : (vF f x (((1+α:ℝ):ℂ) + t.1 * Complex.I)).re
        = (vF f y (((1+α:ℝ):ℂ) + t.1 * Complex.I)).re
          + (∑ p ∈ (⌊x⌋₊).primesLE \ (⌊y⌋₊).primesLE,
              f p * ((p:ℂ)^(-(((1+α:ℝ):ℂ) + t.1 * Complex.I)))).re := by
      rw [vF, vF, ← Finset.sum_sdiff hsub, Complex.add_re, add_comm]
    have hterm : ∀ p ∈ (⌊x⌋₊).primesLE \ (⌊y⌋₊).primesLE,
        -((p:ℝ)^(-(1+α))) ≤ (f p * ((p:ℂ)^(-(((1+α:ℝ):ℂ) + t.1 * Complex.I)))).re := by
      intro p hp
      have hmem := Finset.mem_sdiff.mp hp
      have hp2 : 0 < p := (Nat.mem_primesLE.mp hmem.1).2.pos
      have h1 : -‖f p * ((p:ℂ)^(-(((1+α:ℝ):ℂ) + t.1 * Complex.I)))‖ ≤
          (f p * ((p:ℂ)^(-(((1+α:ℝ):ℂ) + t.1 * Complex.I)))).re := by
        have := Complex.re_le_norm (-(f p * ((p:ℂ)^(-(((1+α:ℝ):ℂ) + t.1 * Complex.I)))))
        rw [Complex.neg_re, norm_neg] at this; linarith
      have h2 : ‖f p * ((p:ℂ)^(-(((1+α:ℝ):ℂ) + t.1 * Complex.I)))‖ ≤ (p:ℝ)^(-(1+α)) := by
        rw [norm_mul, Complex.norm_natCast_cpow_of_pos hp2,
          show (-(((1+α:ℝ):ℂ) + t.1 * Complex.I)).re = -(1+α) by simp]
        calc ‖f p‖ * (p:ℝ)^(-(1+α)) ≤ 1 * (p:ℝ)^(-(1+α)) :=
              mul_le_mul_of_nonneg_right (hb p) (Real.rpow_nonneg (Nat.cast_nonneg p) _)
          _ = _ := one_mul _
      linarith
    have hsumle : (∑ p ∈ (⌊x⌋₊).primesLE \ (⌊y⌋₊).primesLE,
          f p * ((p:ℂ)^(-(((1+α:ℝ):ℂ) + t.1 * Complex.I)))).re
        ≥ - ∑ p ∈ (⌊x⌋₊).primesLE \ (⌊y⌋₊).primesLE, (p:ℝ)^(-(1+α)) := by
      rw [Complex.re_sum, ← Finset.sum_neg_distrib]
      exact Finset.sum_le_sum hterm
    linarith [hdecomp, hsumle]
  haveI : Nonempty {t : ℝ // |t| ≤ T} := ⟨⟨0, by rw [abs_zero]; exact hT⟩⟩
  have hbdd : BddAbove (Set.range (fun t : {t : ℝ // |t| ≤ T} =>
      (vF f x (((1+α:ℝ):ℂ) + t.1 * Complex.I)).re)) := by
    refine ⟨∑ p ∈ (⌊x⌋₊).primesLE, (p:ℝ)^(-(1+α)), ?_⟩
    rintro z ⟨t, rfl⟩
    calc (vF f x (((1+α:ℝ):ℂ) + t.1 * Complex.I)).re
        ≤ ∑ p ∈ (⌊x⌋₊).primesLE, ‖f p * ((p:ℂ)^(-(((1+α:ℝ):ℂ) + t.1 * Complex.I)))‖ := by
          rw [vF, Complex.re_sum]
          exact Finset.sum_le_sum (fun p _ => Complex.re_le_norm _)
      _ ≤ ∑ p ∈ (⌊x⌋₊).primesLE, (p:ℝ)^(-(1+α)) := by
          refine Finset.sum_le_sum (fun p hp => ?_)
          have hp2 : 0 < p := (Nat.mem_primesLE.mp hp).2.pos
          rw [norm_mul, Complex.norm_natCast_cpow_of_pos hp2,
            show (-(((1+α:ℝ):ℂ) + t.1 * Complex.I)).re = -(1+α) by simp]
          calc ‖f p‖ * (p:ℝ)^(-(1+α)) ≤ 1 * (p:ℝ)^(-(1+α)) :=
                mul_le_mul_of_nonneg_right (hb p) (Real.rpow_nonneg (Nat.cast_nonneg p) _)
            _ = _ := one_mul _
  unfold Wsup
  have hmid : (⨆ (t : {t : ℝ // |t| ≤ T}),
        (vF f y (((1+α:ℝ):ℂ) + t.1 * Complex.I)).re)
      ≤ (⨆ (t : {t : ℝ // |t| ≤ T}),
          (vF f x (((1+α:ℝ):ℂ) + t.1 * Complex.I)).re) + C₀ := by
    refine ciSup_le (fun t => ?_)
    have h1 := hpt t
    have h2 := le_ciSup (f := fun t : {t : ℝ // |t| ≤ T} =>
      (vF f x (((1+α:ℝ):ℂ) + t.1 * Complex.I)).re) hbdd t
    linarith [hS]
  exact hmid



end Work.BMF
