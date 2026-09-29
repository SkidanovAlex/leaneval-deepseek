import Mathlib
import Submission.Work.TMC7Core.LDT
import Submission.Work.TMC7Core.Cocycle
import Submission.Work.TMC7Core.Scale.scale_tower_step
import Submission.Work.TMC7Core.Scale.rat_excess_rate_explicit
import Submission.Work.TMC7Core.Scale.hasLEBound_Icc
import Submission.Work.TMC7Core.Scale.prop9_aux
import Submission.Work.TMComp.C7Aux.rtlSchedule
import Submission.Work.TMComp.C7Aux.rtl_run_le
import Submission.Work.TMComp.C7Aux.rtl_card_le
import Submission.Work.TMComp.C7Aux.rtl_sum_eps_le
import Submission.Work.TMComp.C7Aux.Fresh.FiniteTower

namespace Work.TMComp.C7Aux.TowerV3

open Work.TMComp.C7Aux

open MeasureTheory Filter Topology Set
open LeanEval.Analysis.TenMartini
open Work.TMC7Core
open Work.TMC7Core.Scale

set_option maxHeartbeats 64000000
noncomputable section

/-- `t^2/4 ≤ exp t` for `t ≥ 0`. -/
theorem exp_ge_sq_div_four (t : ℝ) (ht : 0 ≤ t) : t^2/4 ≤ Real.exp t := by
  have h1 : 1 + t/2 ≤ Real.exp (t/2) := by
    have := Real.add_one_le_exp (t/2); linarith
  have h2 : (1 + t/2)^2 ≤ (Real.exp (t/2))^2 := pow_le_pow_left₀ (by linarith) h1 2
  have h3 : (Real.exp (t/2))^2 = Real.exp t := by
    rw [pow_two, ← Real.exp_add]; congr 1; ring
  have h4 : t^2/4 ≤ (1 + t/2)^2 := by nlinarith
  linarith [h2, h3, h4]

/-- `∑_{i<n} r^i ≤ 1/(1-r)` for `0 ≤ r < 1`. -/
theorem geom_sum_range_le (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    ∑ i ∈ Finset.range n, r^i ≤ 1/(1-r) := by
  have hsum : Summable (fun i : ℕ => r^i) := summable_geometric_of_lt_one hr0 hr1
  have h := Summable.sum_le_tsum (Finset.range n) (fun i _ => pow_nonneg hr0 i) hsum
  rw [tsum_geometric_of_lt_one hr0 hr1] at h
  simpa [one_div] using h

/-- If `log (1/r) ≤ x` then `exp (-x) ≤ r` (for `r > 0`). -/
theorem exp_neg_le_of_log_le {x r : ℝ} (hr : 0 < r) (h : Real.log (1/r) ≤ x) :
    Real.exp (-x) ≤ r := by
  have h1 : 1/r ≤ Real.exp x := by
    calc 1/r = Real.exp (Real.log (1/r)) := (Real.exp_log (by positivity)).symm
      _ ≤ Real.exp x := Real.exp_le_exp.mpr h
  have h2 : Real.exp (-x) = 1/Real.exp x := by rw [Real.exp_neg]; ring
  rw [h2, div_le_iff₀ (Real.exp_pos x)]
  have h3 := (div_le_iff₀ hr).mp h1
  linarith [h3]

theorem rat_tower_lower_v3 (lam : ℝ) (K : Set ℝ) (c C C₀ : ℝ) (hLDT : Work.TMC7Core.HasLDTOn lam K c C)
    (hLEB : Work.TMC7Core.HasLEBound lam K C₀) (hc1 : c ≤ 1) (κ : ℝ) (hκ : 0 < κ)
    (hκ1 : κ ≤ 1/200) (b : ℝ) (hb : 0 < b) :
    ∃ B T : ℝ, 0 < B ∧ ∀ (k : ℕ) (P : ℕ → ℤ) (Q : ℕ → ℕ),
      (∀ i ≤ k, 1 ≤ Q i) → (∀ i < k, Q i < Q (i+1)) →
      (∀ i ≤ k, Nat.Coprime (Int.natAbs (P i)) (Q i)) →
      (∀ i < k, |(P k : ℝ)/(Q k) - (P i : ℝ)/(Q i)| < 1/((Q i : ℝ)^2)) →
      (∀ i < k, (Q (i+1) : ℝ) ≤ Real.exp (b * (Q i : ℝ))) →
      T ≤ (Q 0 : ℝ) →
      ∀ E ∈ K, ∀ N₀ : ℕ, C * (κ^2)⁻¹ * (Q 0 : ℝ) ≤ (N₀ : ℝ) →
      200 * κ < Work.TMC7Core.lyapAvg ((P k : ℝ)/(Q k)) lam (E : ℂ) N₀ →
      (9/10) * Work.TMC7Core.lyapAvg ((P k : ℝ)/(Q k)) lam (E : ℂ) N₀
          < Work.TMC7Core.lyapAvg ((P k : ℝ)/(Q k)) lam (E : ℂ) (2*N₀) →
      2 * Work.TMC7Core.lyapAvg ((P k : ℝ)/(Q k)) lam (E : ℂ) (2*N₀)
          - Work.TMC7Core.lyapAvg ((P k : ℝ)/(Q k)) lam (E : ℂ) N₀
        ≤ Work.TMC7Core.lyap ((P k : ℝ)/(Q k)) lam (E : ℂ)
          + B * Real.exp (-(c * κ * (Q 0 : ℝ) / 8)) := by
  have hc0 : 0 < c := hLDT.1
  have hC1 : 1 ≤ C := hLDT.2.1
  have hC₀pos : 0 < C₀ := hLEB.1
  have hLEB' : ∀ E ∈ K, ∀ (α : ℝ) (N : ℕ) (x : ℝ), uAvg α lam (E : ℂ) N x ≤ C₀ := hLEB.2
  set cκ : ℝ := c * κ with hcκdef
  have hcκ : 0 < cκ := by rw [hcκdef]; positivity
  set Sb : ℕ := Nat.ceil (4 * b / cκ) + 1 with hSbdef
  have hSb_gt : 4 * b / cκ < Sb := by
    rw [hSbdef]
    have h := Nat.le_ceil (4 * b / cκ)
    push_cast
    linarith only [h]
  have hden : 0 < 1 - Real.exp (-(cκ / 2)) := by
    have : Real.exp (-(cκ/2)) < 1 := by
      rw [Real.exp_lt_one_iff]; linarith only [hcκ]
    linarith only [this]
  set B : ℝ := 5120 * (C₀ + 1) / (9 * cκ) + 60 * C₀
      + 2 * (Sb + 1) * (76 * C₀ + 9) / (1 - Real.exp (-(cκ / 2))) + 1 with hBdef
  have hBpos : 0 < B := by
    rw [hBdef]; positivity
  set Ts : Finset ℝ := {C * (κ^2)⁻¹, 3, C₀ + 1, 4/cκ, 160/(c^2 * κ^2),
      4 * Real.log 10 / cκ,
      2 * Real.log (max (12*C₀/κ) (4*(Sb+1)*(76*C₀+9)/(κ*(1 - Real.exp (-(cκ/2)))))) / cκ,
      1} with hTsdef
  have hTsne : Ts.Nonempty := by rw [hTsdef]; exact ⟨_, Finset.mem_insert_self _ _⟩
  set T : ℝ := Ts.max' hTsne with hTdef
  refine ⟨B, T, hBpos, ?_⟩
  intro k P Q hQ1 hQmono hcop0 hclose hgrowth hTle E hE N₀ hN₀ hlev hpair

  -- ================= T conditions and elementary consequences =================
  have hT1 : (1:ℝ) ≤ T := Finset.le_max' Ts 1 (by simp [hTsdef])
  have hT3 : (3:ℝ) ≤ T := Finset.le_max' Ts 3 (by simp [hTsdef])
  have hTA : C * (κ^2)⁻¹ ≤ T := Finset.le_max' Ts (C * (κ^2)⁻¹) (by simp [hTsdef])
  have hTC₀ : C₀ + 1 ≤ T := Finset.le_max' Ts (C₀ + 1) (by simp [hTsdef])
  have hT4 : 4/cκ ≤ T := Finset.le_max' Ts (4/cκ) (by simp [hTsdef])
  have hT160 : 160/(c^2 * κ^2) ≤ T := Finset.le_max' Ts (160/(c^2 * κ^2)) (by simp [hTsdef])
  have hTlog10 : 4 * Real.log 10 / cκ ≤ T := Finset.le_max' Ts (4 * Real.log 10 / cκ) (by simp [hTsdef])
  have hTlogmax : 2 * Real.log (max (12*C₀/κ)
        (4*(Sb+1)*(76*C₀+9)/(κ*(1 - Real.exp (-(cκ/2)))))) / cκ ≤ T :=
    Finset.le_max' Ts _ (by simp [hTsdef])
  -- opaque from here on: unfolding `T := Ts.max' _` in defeq checks is catastrophic
  clear_value T Ts Sb
  -- `A`
  set A : ℝ := C * (κ^2)⁻¹ with hAdef
  have hApos : 0 < A := by rw [hAdef]; positivity
  have hA0 : A * (Q 0 : ℝ) ≤ (N₀ : ℝ) := by rw [hAdef]; exact hN₀
  -- monotonicity of `Q` on `[0,k]`
  have hQ0i : ∀ i ≤ k, Q 0 ≤ Q i := by
    intro i
    induction i with
    | zero => intro _; exact le_refl _
    | succ i ih =>
      intro hi
      exact le_trans (ih (by omega)) (le_of_lt (hQmono i (by omega)))
  have hQT : ∀ i ≤ k, T ≤ (Q i : ℝ) := fun i hi =>
    le_trans hTle (by exact_mod_cast hQ0i i hi)
  have hQ1' : ∀ i ≤ k, (1:ℝ) ≤ (Q i : ℝ) := fun i hi =>
    le_trans hT1 (hQT i hi)
  have hA_le_Q : ∀ i ≤ k, C * (κ^2)⁻¹ ≤ (Q i : ℝ) := fun i hi =>
    le_trans hTA (hQT i hi)
  have h3_le_Q : ∀ i ≤ k, (3:ℝ) ≤ (Q i : ℝ) := fun i hi => le_trans hT3 (hQT i hi)
  -- `hbig` and `hbig2`
  have hbig : ∀ i ≤ k, Real.log 10 ≤ cκ * (Q i : ℝ) / 4 := by
    intro i hi
    have h1 : 4 * Real.log 10 / cκ ≤ (Q i : ℝ) := le_trans hTlog10 (hQT i hi)
    have h2 : cκ * (4 * Real.log 10 / cκ) ≤ cκ * (Q i : ℝ) :=
      mul_le_mul_of_nonneg_left h1 (le_of_lt hcκ)
    have h3 : cκ * (4 * Real.log 10 / cκ) = 4 * Real.log 10 := by field_simp
    linarith only [h2, h3]
  have hbig2 : ∀ i ≤ k, 2 ≤ Real.exp (cκ * (Q i : ℝ) / 2) / (5 * (Q i : ℝ)) := by
    intro i hi
    have hQi : 160/(c^2 * κ^2) ≤ (Q i : ℝ) := le_trans hT160 (hQT i hi)
    have hQipos : 0 < (Q i : ℝ) := by
      have := hQT i hi; linarith only [this, hT1]
    have ht : 0 ≤ cκ * (Q i : ℝ) / 2 := by positivity
    have hexp := exp_ge_sq_div_four (cκ * (Q i : ℝ) / 2) ht
    have hsq : (cκ * (Q i : ℝ) / 2)^2/4 = c^2 * κ^2 * (Q i : ℝ)^2 / 16 := by
      rw [hcκdef]; ring
    have h10 : 10 * (Q i : ℝ) ≤ Real.exp (cκ * (Q i : ℝ) / 2) := by
      have hkey : 10 * (Q i : ℝ) ≤ c^2 * κ^2 * (Q i : ℝ)^2 / 16 := by
        have hc2 : 0 < c^2 * κ^2 := by positivity
        have hmul : (c^2 * κ^2) * (160/(c^2 * κ^2)) ≤ (c^2 * κ^2) * (Q i : ℝ) :=
          mul_le_mul_of_nonneg_left hQi (le_of_lt hc2)
        have heq : (c^2 * κ^2) * (160/(c^2 * κ^2)) = 160 := by field_simp
        rw [heq] at hmul
        nlinarith only [hmul, hQipos]
      linarith only [hexp, hsq, hkey]
    rw [le_div_iff₀ (by positivity)]
    linarith only [h10]
  -- exponential smallness of the window error
  have hlogmax_eq : Real.log (1/(κ/(12*C₀))) = Real.log (12*C₀/κ) := by
    congr 1; field_simp
  have hlogmax_le : Real.log (max (12*C₀/κ)
        (4*(Sb+1)*(76*C₀+9)/(κ*(1 - Real.exp (-(cκ/2)))))) ≤ cκ*T/2 := by
    have h := mul_le_mul_of_nonneg_left hTlogmax (le_of_lt hcκ)
    have h2 : cκ * (2 * Real.log (max (12*C₀/κ)
        (4*(Sb+1)*(76*C₀+9)/(κ*(1 - Real.exp (-(cκ/2)))))) / cκ)
        = 2 * Real.log (max (12*C₀/κ) (4*(Sb+1)*(76*C₀+9)/(κ*(1 - Real.exp (-(cκ/2)))))) := by
      field_simp
    linarith only [h, h2]
  have hbound1 : Real.exp (-(cκ*T/2)) ≤ κ/(12*C₀) := by
    refine exp_neg_le_of_log_le (by positivity) ?_
    calc Real.log (1/(κ/(12*C₀))) = Real.log (12*C₀/κ) := hlogmax_eq
      _ ≤ Real.log (max (12*C₀/κ)
            (4*(Sb+1)*(76*C₀+9)/(κ*(1 - Real.exp (-(cκ/2)))))) :=
          Real.log_le_log (by positivity) (le_max_left _ _)
      _ ≤ cκ*T/2 := hlogmax_le
  have hbound2 : Real.exp (-(cκ*T/2)) ≤ κ*(1 - Real.exp (-(cκ/2)))
        / (4*(Sb+1)*(76*C₀+9)) := by
    refine exp_neg_le_of_log_le (by positivity) ?_
    have heq : 1/(κ*(1 - Real.exp (-(cκ/2))) / (4*(Sb+1)*(76*C₀+9)))
        = 4*(Sb+1)*(76*C₀+9)/(κ*(1 - Real.exp (-(cκ/2)))) := by field_simp
    rw [heq]
    calc Real.log (4*(Sb+1)*(76*C₀+9)/(κ*(1 - Real.exp (-(cκ/2)))))
        ≤ Real.log (max (12*C₀/κ)
            (4*(Sb+1)*(76*C₀+9)/(κ*(1 - Real.exp (-(cκ/2)))))) :=
          Real.log_le_log (by positivity) (le_max_right _ _)
      _ ≤ cκ*T/2 := hlogmax_le
  have hexpQ0_le : Real.exp (-(cκ*(Q 0 : ℝ)/2)) ≤ Real.exp (-(cκ*T/2)) := by
    apply Real.exp_le_exp.mpr; nlinarith only [hTle, hcκ]
  have hsmall1 : 6 * C₀ * Real.exp (-(cκ*(Q 0 : ℝ)/2)) ≤ κ/2 := by
    calc 6 * C₀ * Real.exp (-(cκ*(Q 0 : ℝ)/2)) ≤ 6 * C₀ * Real.exp (-(cκ*T/2)) := by
          apply mul_le_mul_of_nonneg_left hexpQ0_le (by positivity)
      _ ≤ 6 * C₀ * (κ/(12*C₀)) := mul_le_mul_of_nonneg_left hbound1 (by positivity)
      _ = κ/2 := by field_simp; ring
  have hsmall2 : (Sb+1)*(76*C₀+9) * Real.exp (-(cκ*(Q 0 : ℝ)/2)) / (1 - Real.exp (-(cκ/2)))
      ≤ κ/4 := by
    have he : Real.exp (-(cκ/2)) < 1 := by rw [Real.exp_lt_one_iff]; linarith only [hcκ]
    have h1 : (Sb+1)*(76*C₀+9) * Real.exp (-(cκ*(Q 0 : ℝ)/2))
        ≤ (Sb+1)*(76*C₀+9) * Real.exp (-(cκ*T/2)) :=
      mul_le_mul_of_nonneg_left hexpQ0_le (by positivity)
    have h2 : (Sb+1)*(76*C₀+9) * Real.exp (-(cκ*T/2))
        ≤ (Sb+1)*(76*C₀+9) * (κ*(1 - Real.exp (-(cκ/2)))/(4*(Sb+1)*(76*C₀+9))) :=
      mul_le_mul_of_nonneg_left hbound2 (by positivity)
    calc (Sb+1)*(76*C₀+9) * Real.exp (-(cκ*(Q 0 : ℝ)/2)) / (1 - Real.exp (-(cκ/2)))
        ≤ (Sb+1)*(76*C₀+9) * (κ*(1 - Real.exp (-(cκ/2)))/(4*(Sb+1)*(76*C₀+9)))
            / (1 - Real.exp (-(cκ/2))) := by
          exact div_le_div_of_nonneg_right (le_trans h1 h2) (le_of_lt hden)
      _ = κ/4 := by field_simp
  set Esum0 : ℝ := (Sb+1)*(76*C₀+9) * Real.exp (-(cκ*(Q 0 : ℝ)/2))
      / (1 - Real.exp (-(cκ/2))) with hEsum0def
  have hEsum0_le : Esum0 ≤ κ/4 := hsmall2
  have hEsum0_ge : (76*C₀+9) * Real.exp (-(cκ*(Q 0 : ℝ)/2)) ≤ Esum0 := by
    rw [hEsum0def, le_div_iff₀ hden]
    have h1 : (1:ℝ) - Real.exp (-(cκ/2)) ≤ (Sb:ℝ) + 1 := by
      have := Real.exp_pos (-(cκ/2))
      have h0 : (0:ℝ) ≤ (Sb:ℝ) := Nat.cast_nonneg _
      linarith only [this, h0]
    calc (76*C₀+9) * Real.exp (-(cκ*(Q 0 : ℝ)/2)) * (1 - Real.exp (-(cκ/2)))
        ≤ (76*C₀+9) * Real.exp (-(cκ*(Q 0 : ℝ)/2)) * ((Sb:ℝ) + 1) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = ((Sb:ℝ) + 1) * (76*C₀+9) * Real.exp (-(cκ*(Q 0 : ℝ)/2)) := by ring
  set Esum : ℝ := 2 * Esum0 with hEsumdef
  have hEsum_le : Esum ≤ κ/2 := by rw [hEsumdef]; linarith only [hEsum0_le]
  have hEsum_nonneg : 0 ≤ Esum := by rw [hEsumdef]; positivity
  -- ================= the schedule =================
  have hN₀1 : 1 ≤ N₀ := by
    have h1 : (1:ℝ) ≤ A * (Q 0 : ℝ) := by
      have hA1 : (1:ℝ) ≤ A := by
        rw [hAdef]
        have h2 : (1:ℝ) ≤ C * (κ^2)⁻¹ := by
          have hκ2 : (1:ℝ) ≤ (κ^2)⁻¹ := by
            rw [one_le_inv₀ (by positivity)]
            nlinarith only [hκ.le, hκ1]
          nlinarith only [hC1, hκ2]
        exact h2
      have hQ01 : (1:ℝ) ≤ (Q 0 : ℝ) := by exact_mod_cast hQ1 0 (Nat.zero_le k)
      nlinarith only [hA1, hQ01]
    have := le_trans h1 hA0
    exact_mod_cast this
  have hrtlN_ge : ∀ s, 3^s * N₀ ≤ rtlN A cκ Q k N₀ s := by
    intro s
    induction s with
    | zero => simp
    | succ s ih =>
      rw [rtlN_succ]
      have h3 : 3 ≤ rtlMM cκ Q (rtli A cκ Q k N₀ s) :=
        rtlMM_three_le cκ Q (by
          have := h3_le_Q (rtli A cκ Q k N₀ s) (rtli_le A cκ Q k N₀ s)
          exact_mod_cast this)
      calc 3^(s+1) * N₀ = 3 * (3^s * N₀) := by ring
        _ ≤ rtlMM cκ Q (rtli A cκ Q k N₀ s) * rtlN A cκ Q k N₀ s := Nat.mul_le_mul h3 ih
        _ = rtlN A cκ Q k N₀ (s+1) := (rtlN_succ A cκ Q k N₀ s).symm
  have hrtlN1 : ∀ s, 1 ≤ rtlN A cκ Q k N₀ s := by
    intro s
    have h := hrtlN_ge s
    have h2 : 1 ≤ 3^s * N₀ := by
      have h3 : 1 ≤ 3^s := by
        have := pow_pos (show (0:ℕ) < 3 by norm_num) s; omega
      calc (1:ℕ) = 1 * 1 := by ring
        _ ≤ 3^s * N₀ := Nat.mul_le_mul h3 hN₀1
    omega
  have hexists : ∃ s, A * (Q k : ℝ) ≤ (rtlN A cκ Q k N₀ s : ℝ) := by
    have h3pow : ∀ n : ℕ, n ≤ 3^n := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => calc n+1 ≤ 3^n * 3 := by nlinarith only [ih, (by have := pow_pos (show (0:ℕ) < 3 by norm_num) n; omega : (1:ℕ) ≤ 3^n)]
                      _ = 3^(n+1) := by ring
    set r : ℝ := A * (Q k : ℝ) / N₀ with hr
    refine ⟨Nat.ceil r + 1, ?_⟩
    have hr_le : r ≤ (Nat.ceil r + 1 : ℕ) := by
      have := Nat.le_ceil r; push_cast; linarith only [this]
    have h3s : r ≤ (3 : ℝ)^(Nat.ceil r + 1) := by
      refine le_trans hr_le ?_
      have h := h3pow (Nat.ceil r + 1)
      exact_mod_cast h
    have h1 : (3:ℝ)^(Nat.ceil r + 1) * N₀ ≤ (rtlN A cκ Q k N₀ (Nat.ceil r + 1) : ℝ) := by
      exact_mod_cast hrtlN_ge (Nat.ceil r + 1)
    have hN₀pos : (0:ℝ) < (N₀ : ℝ) := by exact_mod_cast hN₀1
    have hrN : r * N₀ = A * (Q k : ℝ) := by rw [hr]; field_simp
    calc A * (Q k : ℝ) = r * N₀ := hrN.symm
      _ ≤ (3:ℝ)^(Nat.ceil r + 1) * N₀ := by
          exact mul_le_mul_of_nonneg_right h3s (by positivity)
      _ ≤ (rtlN A cκ Q k N₀ (Nat.ceil r + 1) : ℝ) := h1
  set s0 : ℕ := Nat.find hexists with hs0def
  have hs0spec : A * (Q k : ℝ) ≤ (rtlN A cκ Q k N₀ s0 : ℝ) := Nat.find_spec hexists
  set S : ℕ := s0 + 1 with hSdef
  have hiS : rtli A cκ Q k N₀ s0 = k := by
    rw [rtli_eq_idx]
    exact le_antisymm (rtlIdx_le A Q k _) (Nat.le_findGreatest (le_refl k) hs0spec)
  have hilt : ∀ t < s0, rtli A cκ Q k N₀ t < k := by
    intro t ht
    have hnot : ¬ (A * (Q k : ℝ) ≤ (rtlN A cκ Q k N₀ t : ℝ)) :=
      Nat.find_min hexists (by rw [← hs0def]; exact ht)
    by_contra hc
    push_neg at hc
    have hk : rtli A cκ Q k N₀ t = k := le_antisymm (rtli_le A cκ Q k N₀ t) hc
    have hspec := rtli_spec (A := A) (cκ := cκ) (k := k) (N₀ := N₀) (s := t)
      (le_trans hA0 (by exact_mod_cast N₀_le_rtlN A cκ Q k N₀ hQ1 t))
    rw [hk] at hspec
    exact hnot hspec
  have hrtli_mono := rtli_mono A cκ Q k N₀ hQ1 hA0
  clear_value S s0




  set ω : ℝ := (P k : ℝ)/(Q k : ℝ) with hω
  have hκ1' : κ ≤ 1/100 := by linarith only [hκ1]
  have hQk1 : 1 ≤ Q k := hQ1 k (le_refl k)
  -- ================= closing bound =================
  have hQk3 : (1:ℝ) ≤ (Q k : ℝ) := by exact_mod_cast hQk1
  have hQk4 : (4:ℝ)/cκ ≤ (Q k : ℝ) := le_trans hT4 (hQT k (le_refl k))
  have hQk_sq : (Q k : ℝ)^2 * Real.exp (-(3*cκ*(Q k : ℝ)/8)) ≤ 256/(9*c^2*κ^2) := by
    have ht : 0 ≤ 3*cκ*(Q k : ℝ)/8 := by positivity
    have hexp_ge : 9*c^2*κ^2*(Q k : ℝ)^2/256 ≤ Real.exp (3*cκ*(Q k : ℝ)/8) := by
      have h := exp_ge_sq_div_four (3*cκ*(Q k : ℝ)/8) ht
      have heq : (3*cκ*(Q k : ℝ)/8)^2/4 = 9*c^2*κ^2*(Q k : ℝ)^2/256 := by rw [hcκdef]; ring
      linarith only [h, heq]
    have h1 : Real.exp (-(3*cκ*(Q k : ℝ)/8)) ≤ 256/(9*c^2*κ^2*(Q k : ℝ)^2) := by
      rw [Real.exp_neg, ← one_div, div_le_iff₀ (Real.exp_pos _)]
      have h2 := mul_le_mul_of_nonneg_left hexp_ge
        (show (0:ℝ) ≤ 256/(9*c^2*κ^2*(Q k : ℝ)^2) by positivity)
      have heq2 : (256/(9*c^2*κ^2*(Q k : ℝ)^2)) * (9*c^2*κ^2*(Q k : ℝ)^2/256) = 1 := by
        field_simp
      linarith only [h2, heq2]
    calc (Q k : ℝ)^2 * Real.exp (-(3*cκ*(Q k : ℝ)/8))
        ≤ (Q k : ℝ)^2 * (256/(9*c^2*κ^2*(Q k : ℝ)^2)) :=
          mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
      _ = 256/(9*c^2*κ^2) := by field_simp
  have hmm_ge : Real.exp (cκ*(Q k : ℝ)/2)/10 ≤ (rtlMM cκ Q k : ℝ) :=
    rtlMM_ge cκ Q k (hbig2 k (le_refl k))
  have hmmpos : 0 < (rtlMM cκ Q k : ℝ) := by
    have := hmm_ge; have hx := Real.exp_pos (cκ*(Q k : ℝ)/2); linarith only [this, hx]
  have hNs0_1 : 1 ≤ rtlN A cκ Q k N₀ s0 := hrtlN1 s0
  have hNS' : rtlN A cκ Q k N₀ S = rtlMM cκ Q k * rtlN A cκ Q k N₀ s0 := by
    rw [hSdef, rtlN_succ, hiS]
  obtain ⟨M, hM⟩ := rtlMM_dvd cκ Q k
  have hdvd : Q k ∣ rtlN A cκ Q k N₀ S :=
    ⟨M * rtlN A cκ Q k N₀ s0, by rw [hNS', hM]; ring⟩
  obtain ⟨m, hm⟩ := hdvd
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, mul_zero] at hm
      have h1 := hrtlN1 S
      rw [hm] at h1
      omega
    · exact h
  have hscale : m * Q k = rtlN A cκ Q k N₀ S := by rw [hm, Nat.mul_comm]
  have hbound : ∀ (N : ℕ) (x : ℝ), uAvg ((P k : ℝ)/(Q k : ℝ)) lam (E : ℂ) N x ≤ C₀ :=
    fun N x => hLEB' E hE _ N x
  have hrate := rat_excess_rate_explicit (P k) (Q k) hQk1 lam E C₀ hC₀pos hbound m hm1
  have hrate' : lyapAvg ω lam (E : ℂ) (rtlN A cκ Q k N₀ (S))
      - lyap ω lam (E : ℂ)
      ≤ (C₀*((Q k : ℝ)+1)+1)*(1+Real.log (m*(Q k : ℝ)))/(m*(Q k : ℝ)) := by
    rw [← hscale]; exact hrate
  have hclose1 : (1+Real.log (m*(Q k : ℝ)))/(m*(Q k : ℝ))
      ≤ (2 + Real.log (rtlMM cκ Q k : ℝ))/(rtlMM cκ Q k : ℝ) := by
    set mmr : ℝ := (rtlMM cκ Q k : ℝ) with hmmr
    set Ns : ℝ := (rtlN A cκ Q k N₀ s0 : ℝ) with hNs
    have hmpos' : 0 < mmr := by rw [hmmr]; exact hmmpos
    have hNs1 : 1 ≤ Ns := by rw [hNs]; exact_mod_cast hNs0_1
    have hNs0pos : 0 < Ns := lt_of_lt_of_le one_pos hNs1
    have hmQk : ((m:ℝ)*(Q k : ℝ)) = mmr * Ns := by
      have h1 : (rtlN A cκ Q k N₀ S : ℝ) = mmr * Ns := by
        rw [hmmr, hNs, hNS']; push_cast; ring
      rw [show (m:ℝ)*(Q k : ℝ) = (rtlN A cκ Q k N₀ S : ℝ) by
        rw [← hscale]; push_cast; ring, h1]
    rw [hmQk, Real.log_mul (ne_of_gt hmpos') (ne_of_gt hNs0pos),
      show (1 + (Real.log mmr + Real.log Ns)) = 1 + Real.log mmr + Real.log Ns by ring]
    rw [div_le_iff₀ (by positivity : 0 < mmr * Ns)]
    have hlogNs : Real.log Ns ≤ Ns := Real.log_le_self (by positivity)
    have hlogmm : 0 < Real.log mmr := by
      have h3k : 3 ≤ rtlMM cκ Q k :=
        rtlMM_three_le cκ Q (by have := h3_le_Q k (le_refl k); exact_mod_cast this)
      rw [hmmr]; exact Real.log_pos (by exact_mod_cast (by omega : 1 < rtlMM cκ Q k))
    have hkey : ((2 + Real.log mmr)/mmr) * (mmr*Ns) = (2 + Real.log mmr)*Ns := by field_simp
    rw [hkey]
    nlinarith only [hlogNs, hNs1, hlogmm, mul_nonneg hlogmm.le (sub_nonneg.mpr hNs1)]
  have hclose2 : (2 + Real.log (rtlMM cκ Q k : ℝ))/(rtlMM cκ Q k : ℝ)
      ≤ 10 * (2 + cκ*(Q k : ℝ)/2) * Real.exp (-(cκ*(Q k : ℝ)/2)) := by
    have hmm_le : (rtlMM cκ Q k : ℝ) ≤ Real.exp (cκ*(Q k : ℝ)/2)/5 :=
      rtlMM_le cκ Q k (le_trans one_le_two (hbig2 k (le_refl k)))
    have hlog_le : Real.log (rtlMM cκ Q k : ℝ) ≤ cκ*(Q k : ℝ)/2 := by
      calc Real.log (rtlMM cκ Q k : ℝ) ≤ Real.log (Real.exp (cκ*(Q k : ℝ)/2)/5) :=
            Real.log_le_log (by positivity) hmm_le
        _ = cκ*(Q k : ℝ)/2 - Real.log 5 := by
            rw [Real.log_div (ne_of_gt (Real.exp_pos _)) (by norm_num : (5:ℝ) ≠ 0),
                Real.log_exp]
        _ ≤ cκ*(Q k : ℝ)/2 := by linarith only [Real.log_pos (by norm_num : (1:ℝ) < 5)]
    rw [div_le_iff₀ hmmpos]
    have h1 : 1 ≤ 10 * Real.exp (-(cκ*(Q k : ℝ)/2)) * (rtlMM cκ Q k : ℝ) := by
      have h2 := mul_le_mul_of_nonneg_left hmm_ge
        (show (0:ℝ) ≤ 10 * Real.exp (-(cκ*(Q k : ℝ)/2)) by positivity)
      have heq : (10 * Real.exp (-(cκ*(Q k : ℝ)/2))) * (Real.exp (cκ*(Q k : ℝ)/2)/10) = 1 := by
        rw [show (10 * Real.exp (-(cκ*(Q k : ℝ)/2))) * (Real.exp (cκ*(Q k : ℝ)/2)/10)
            = ((10 * Real.exp (-(cκ*(Q k : ℝ)/2))) * Real.exp (cκ*(Q k : ℝ)/2))/10 by ring,
          show (10 * Real.exp (-(cκ*(Q k : ℝ)/2))) * Real.exp (cκ*(Q k : ℝ)/2)
            = 10 * (Real.exp (-(cκ*(Q k : ℝ)/2)) * Real.exp (cκ*(Q k : ℝ)/2)) by ring,
          ← Real.exp_add, show -(cκ*(Q k : ℝ)/2) + cκ*(Q k : ℝ)/2 = 0 by ring, Real.exp_zero, mul_one]
        norm_num
      linarith only [h2, heq]
    have h3 : (0:ℝ) ≤ 2 + cκ*(Q k : ℝ)/2 := by positivity
    nlinarith only [h1, h3, hlog_le, mul_le_mul_of_nonneg_left h1 h3]
  have hclose_bound : (C₀*((Q k : ℝ)+1)+1)*(1+Real.log (m*(Q k : ℝ)))/(m*(Q k : ℝ))
      ≤ 5120*(C₀+1)/(9*cκ) * Real.exp (-(cκ*(Q 0 : ℝ)/8)) := by
    have hstep : (C₀*((Q k : ℝ)+1)+1)*(1+Real.log (m*(Q k : ℝ)))/(m*(Q k : ℝ))
        = (C₀*((Q k : ℝ)+1)+1) * ((1+Real.log (m*(Q k : ℝ)))/(m*(Q k : ℝ))) := by ring
    rw [hstep]
    have h2 : (1+Real.log (m*(Q k : ℝ)))/(m*(Q k : ℝ))
        ≤ 10 * (2 + cκ*(Q k : ℝ)/2) * Real.exp (-(cκ*(Q k : ℝ)/2)) := le_trans hclose1 hclose2
    have h3 : (0:ℝ) ≤ (C₀*((Q k : ℝ)+1)+1) := by positivity
    have h4 : (C₀*((Q k : ℝ)+1)+1) * (10 * (2 + cκ*(Q k : ℝ)/2) * Real.exp (-(cκ*(Q k : ℝ)/2)))
        ≤ 20*(C₀+1)*cκ*(Q k : ℝ)^2 * Real.exp (-(cκ*(Q k : ℝ)/2)) := by
      have h41 : (C₀*((Q k : ℝ)+1)+1) ≤ 2*(C₀+1)*(Q k : ℝ) := by
        nlinarith only [hQk3, hC₀pos, mul_le_mul_of_nonneg_left hQk3 hC₀pos.le]
      have h42 : (2 + cκ*(Q k : ℝ)/2) ≤ cκ*(Q k : ℝ) := by
        have h := mul_le_mul_of_nonneg_left hQk4 hcκ.le
        have heq : cκ * ((4:ℝ)/cκ) = 4 := by field_simp
        linarith only [h, heq]
      have hE0 : 0 ≤ Real.exp (-(cκ*(Q k : ℝ)/2)) := by positivity
      calc (C₀*((Q k : ℝ)+1)+1) * (10 * (2 + cκ*(Q k : ℝ)/2) * Real.exp (-(cκ*(Q k : ℝ)/2)))
          ≤ (2*(C₀+1)*(Q k : ℝ)) * (10 * (cκ*(Q k : ℝ)) * Real.exp (-(cκ*(Q k : ℝ)/2))) := by
            apply mul_le_mul h41 ?_ (by positivity) (by positivity)
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h42 (by norm_num)) hE0
        _ = 20*(C₀+1)*cκ*(Q k : ℝ)^2 * Real.exp (-(cκ*(Q k : ℝ)/2)) := by ring
    calc (C₀*((Q k : ℝ)+1)+1) * ((1+Real.log (m*(Q k : ℝ)))/(m*(Q k : ℝ)))
        ≤ (C₀*((Q k : ℝ)+1)+1) * (10 * (2 + cκ*(Q k : ℝ)/2) * Real.exp (-(cκ*(Q k : ℝ)/2))) :=
          mul_le_mul_of_nonneg_left h2 h3
      _ ≤ 20*(C₀+1)*cκ*(Q k : ℝ)^2 * Real.exp (-(cκ*(Q k : ℝ)/2)) := h4
      _ = 20*(C₀+1)*cκ * ((Q k : ℝ)^2 * Real.exp (-(3*cκ*(Q k : ℝ)/8))) * Real.exp (-(cκ*(Q k : ℝ)/8)) := by
          rw [show -(cκ*(Q k : ℝ)/2) = -(3*cκ*(Q k : ℝ)/8) + -(cκ*(Q k : ℝ)/8) by ring, Real.exp_add]
          ring
      _ ≤ 20*(C₀+1)*cκ * (256/(9*c^2*κ^2)) * Real.exp (-(cκ*(Q k : ℝ)/8)) := by
          apply mul_le_mul_of_nonneg_right ?_ (by positivity)
          apply mul_le_mul_of_nonneg_left hQk_sq (by positivity)
      _ ≤ 20*(C₀+1)*cκ * (256/(9*c^2*κ^2)) * Real.exp (-(cκ*(Q 0 : ℝ)/8)) := by
          apply mul_le_mul_of_nonneg_left ?_ (by positivity)
          apply Real.exp_le_exp.mpr
          have hQ0k : (Q 0 : ℝ) ≤ (Q k : ℝ) := by exact_mod_cast hQ0i k (le_refl k)
          nlinarith only [hQ0k, hcκ]
      _ = 5120*(C₀+1)/(9*cκ) * Real.exp (-(cκ*(Q 0 : ℝ)/8)) := by field_simp; ring
  -- ================= the per-step inequality =================
  have hmm3 : ∀ t, 3 ≤ (rtlMM cκ Q (rtli A cκ Q k N₀ (t))) := fun t => rtlMM_three_le cκ Q (by
    have := h3_le_Q _ (rtli_le A cκ Q k N₀ t); exact_mod_cast this)
  have hInv_bound : ∀ i ≤ k, ((rtlMM cκ Q i : ℝ))⁻¹ ≤ 10 * Real.exp (-(cκ*(Q i : ℝ)/2)) := by
    intro i hi
    have hmm := rtlMM_ge cκ Q i (hbig2 i hi)
    have hx : 0 < Real.exp (cκ*(Q i : ℝ)/2) := Real.exp_pos _
    have hmmpos' : 0 < (rtlMM cκ Q i : ℝ) := by linarith only [hmm, hx]
    rw [inv_eq_one_div, div_le_iff₀ hmmpos']
    have he2 : Real.exp (cκ*(Q i : ℝ)/2)/10 ≤ (rtlMM cκ Q i : ℝ) := by linarith only [hmm]
    have h2 := mul_le_mul_of_nonneg_left he2
      (show (0:ℝ) ≤ 10 * Real.exp (-(cκ*(Q i : ℝ)/2)) by positivity)
    have h3 : (10 * Real.exp (-(cκ*(Q i : ℝ)/2))) * (Real.exp (cκ*(Q i : ℝ)/2)/10) = 1 := by
      rw [show (10 * Real.exp (-(cκ*(Q i : ℝ)/2))) * (Real.exp (cκ*(Q i : ℝ)/2)/10)
          = 10 * (Real.exp (-(cκ*(Q i : ℝ)/2)) * Real.exp (cκ*(Q i : ℝ)/2))/10 by ring,
        ← Real.exp_add, show -(cκ*(Q i : ℝ)/2) + cκ*(Q i : ℝ)/2 = 0 by ring, Real.exp_zero, mul_one]
      norm_num
    linarith only [h2, h3]
  have hQQmono : ∀ i ≤ k, (Q 0 : ℝ) ≤ (Q i : ℝ) := fun i hi => by exact_mod_cast hQ0i i hi
  have he1_le : ∀ t, ((4*C₀+1)*Real.exp (-(cκ * (Q (rtli A cκ Q k N₀ (t)) : ℝ)/2)) + 4*C₀/((rtlMM cκ Q (rtli A cκ Q k N₀ (t))) : ℝ)) ≤ (44*C₀+1) * Real.exp (-(cκ*(Q 0 : ℝ)/2)) := by
    intro t
    have his := rtli_le A cκ Q k N₀ t
    have h1 : 4*C₀/((rtlMM cκ Q (rtli A cκ Q k N₀ (t))) : ℝ) ≤ 40*C₀*Real.exp (-(cκ*(Q 0 : ℝ)/2)) := by
      have hb := hInv_bound ((rtli A cκ Q k N₀ (t))) his
      have hQgt := hQQmono ((rtli A cκ Q k N₀ (t))) his
      have hexp_le : Real.exp (-(cκ*(Q (rtli A cκ Q k N₀ (t)) : ℝ)/2)) ≤ Real.exp (-(cκ*(Q 0 : ℝ)/2)) := by
        apply Real.exp_le_exp.mpr; nlinarith only [hQgt, hcκ]
      rw [div_eq_mul_inv]
      nlinarith only [hb, hexp_le, le_of_lt hC₀pos, mul_le_mul_of_nonneg_left hb (le_of_lt hC₀pos),
        mul_le_mul_of_nonneg_left hexp_le (le_of_lt hC₀pos)]
    have h2 : (4*C₀+1)*Real.exp (-(cκ*(Q (rtli A cκ Q k N₀ (t)) : ℝ)/2))
        ≤ (4*C₀+1)*Real.exp (-(cκ*(Q 0 : ℝ)/2)) := by
      apply mul_le_mul_of_nonneg_left
      · apply Real.exp_le_exp.mpr
        have := hQQmono ((rtli A cκ Q k N₀ (t))) his; nlinarith only [this, hcκ]
      · positivity
    linarith only [h1, h2]
  have he1_le' : ∀ t, ((4*C₀+1)*Real.exp (-(cκ * (Q (rtli A cκ Q k N₀ (t)) : ℝ)/2)) + 4*C₀/((rtlMM cκ Q (rtli A cκ Q k N₀ (t))) : ℝ)) ≤ Esum := by
    intro t
    have h1 := he1_le t
    have h2 : (44*C₀+1) * Real.exp (-(cκ*(Q 0 : ℝ)/2)) ≤ (76*C₀+9) * Real.exp (-(cκ*(Q 0 : ℝ)/2)) := by
      apply mul_le_mul_of_nonneg_right (by linarith only [hC₀pos]) (by positivity)
    linarith only [h1, h2, hEsum0_ge, hEsumdef, hEsum_nonneg]
  have he2_le' : ∀ t, (2*((4*C₀+1)*Real.exp (-(cκ * (Q (rtli A cκ Q k N₀ (t)) : ℝ)/2)))) ≤ Esum := by
    intro t
    have his := rtli_le A cκ Q k N₀ t
    have hQgt := hQQmono ((rtli A cκ Q k N₀ (t))) his
    have h2 : (2*((4*C₀+1)*Real.exp (-(cκ * (Q (rtli A cκ Q k N₀ (t)) : ℝ)/2)))) ≤ (8*C₀+2) * Real.exp (-(cκ*(Q 0 : ℝ)/2)) := by
      have h3 : Real.exp (-(cκ*(Q (rtli A cκ Q k N₀ (t)) : ℝ)/2)) ≤ Real.exp (-(cκ*(Q 0 : ℝ)/2)) := by
        apply Real.exp_le_exp.mpr; nlinarith only [hQgt, hcκ]
      have h4 : 2*((4*C₀+1) * Real.exp (-(cκ*(Q (rtli A cκ Q k N₀ (t)) : ℝ)/2)))
          ≤ 2*((4*C₀+1) * Real.exp (-(cκ*(Q 0 : ℝ)/2))) := by
        apply mul_le_mul_of_nonneg_left; · apply mul_le_mul_of_nonneg_left h3; positivity
        · positivity
      linarith only [h4]
    have h5 : (8*C₀+2) * Real.exp (-(cκ*(Q 0 : ℝ)/2)) ≤ (76*C₀+9) * Real.exp (-(cκ*(Q 0 : ℝ)/2)) := by
      apply mul_le_mul_of_nonneg_right (by linarith only [hC₀pos]) (by positivity)
    linarith only [h2, h5, hEsum0_ge, hEsumdef, hEsum_nonneg]
  have hstep : ∀ s, 100*κ < (lyapAvg ω lam (E : ℂ) (rtlN A cκ Q k N₀ (s))) → (9/10)*(lyapAvg ω lam (E : ℂ) (rtlN A cκ Q k N₀ (s))) < (lyapAvg ω lam (E : ℂ) (2 * (rtlN A cκ Q k N₀ (s)))) →
      (|(lyapAvg ω lam (E : ℂ) (rtlN A cκ Q k N₀ (s+1))) + (lyapAvg ω lam (E : ℂ) (rtlN A cκ Q k N₀ (s))) - 2*(lyapAvg ω lam (E : ℂ) (2 * (rtlN A cκ Q k N₀ (s))))| ≤ ((4*C₀+1)*Real.exp (-(cκ * (Q (rtli A cκ Q k N₀ (s)) : ℝ)/2)) + 4*C₀/((rtlMM cκ Q (rtli A cκ Q k N₀ (s))) : ℝ))) ∧
      (|((lyapAvg ω lam (E : ℂ) (rtlN A cκ Q k N₀ (s+1))) - (lyapAvg ω lam (E : ℂ) (2 * (rtlN A cκ Q k N₀ (s+1))))) - (1/((rtlMM cκ Q (rtli A cκ Q k N₀ (s))) : ℝ))*((lyapAvg ω lam (E : ℂ) (rtlN A cκ Q k N₀ (s))) - (lyapAvg ω lam (E : ℂ) (2 * (rtlN A cκ Q k N₀ (s)))))| ≤ (2*((4*C₀+1)*Real.exp (-(cκ * (Q (rtli A cκ Q k N₀ (s)) : ℝ)/2))))) := by
    intro s hlevs hpairs
    have his : (rtli A cκ Q k N₀ (s)) ≤ k := rtli_le A cκ Q k N₀ s
    have hα : |ω - (P ((rtli A cκ Q k N₀ (s))) : ℝ)/(Q ((rtli A cκ Q k N₀ (s))) : ℝ)| < 1/((Q ((rtli A cκ Q k N₀ (s))) : ℝ)^2) := by
      by_cases hik : (rtli A cκ Q k N₀ (s)) < k
      · exact hclose _ hik
      · have heq : (rtli A cκ Q k N₀ (s)) = k := le_antisymm his (by omega)
        rw [heq, sub_self, abs_zero]
        positivity
    have hNQ : C*(κ^2)⁻¹ * (Q ((rtli A cκ Q k N₀ (s))) : ℝ) ≤ ((rtlN A cκ Q k N₀ (s)) : ℝ) := by
      have h := rtli_spec (A := A) (cκ := cκ) (k := k) (N₀ := N₀) (s := s)
        (le_trans hA0 (by exact_mod_cast N₀_le_rtlN A cκ Q k N₀ hQ1 s))
      rw [hAdef] at h ⊢
      exact h
    have hmq : ((2 * (rtlMM cκ Q (rtli A cκ Q k N₀ (s))) : ℕ) : ℝ) < Real.exp (cκ*(Q ((rtli A cκ Q k N₀ (s))) : ℝ)/2) := by
      have hle := rtlMM_le cκ Q ((rtli A cκ Q k N₀ (s))) (le_trans one_le_two (hbig2 _ his))
      have h2 : ((2 * (rtlMM cκ Q (rtli A cκ Q k N₀ (s))) : ℕ) : ℝ) = 2 * ((rtlMM cκ Q (rtli A cκ Q k N₀ (s))) : ℝ) := by push_cast; ring
      rw [h2]
      have hx : 0 < Real.exp (cκ*(Q ((rtli A cκ Q k N₀ (s))) : ℝ)/2) := Real.exp_pos _
      linarith only [hle, hx]
    exact scale_tower_step lam K c C C₀ hLDT hLEB hc1 κ hκ hκ1' E hE ω (P ((rtli A cκ Q k N₀ (s)))) (Q ((rtli A cκ Q k N₀ (s))))
      (hQ1 _ his) (hcop0 _ his) (hA_le_Q _ his) hα ((rtlN A cκ Q k N₀ (s))) hNQ hlevs hpairs ((rtlMM cκ Q (rtli A cκ Q k N₀ (s)))) (hmm3 s) hmq
  -- ================= elementary bounds used by the invariant =================
  have hD0 : (0:ℝ) ≤ (lyapAvg ω lam (E : ℂ) (rtlN A cκ Q k N₀ (0))) - (lyapAvg ω lam (E : ℂ) (2 * (rtlN A cκ Q k N₀ (0)))) := by
    have h := lyapAvg_two_le ω lam (E : ℂ) (rtlN A cκ Q k N₀ (0))
    linarith only [h]
  have hZ0nn : 0 ≤ (lyapAvg ω lam (E : ℂ) (2 * (rtlN A cκ Q k N₀ (0)))) := by
    have h1 := lyapAvg_nonneg' ω lam (E : ℂ) (2 * (rtlN A cκ Q k N₀ (0)) - 1)
    rw [Nat.sub_add_cancel (by have := hrtlN1 0; omega : 1 ≤ 2 * (rtlN A cκ Q k N₀ (0)))] at h1
    simpa using h1
  have hL0C₀ : (lyapAvg ω lam (E : ℂ) (rtlN A cκ Q k N₀ (0))) ≤ C₀ := lyapAvg_le_of_hasLEBound hLEB hE ω (rtlN A cκ Q k N₀ (0))
  have hlev0 : 200 * κ < (lyapAvg ω lam (E : ℂ) (rtlN A cκ Q k N₀ (0))) := hlev
  have hpair0 : (9/10) * (lyapAvg ω lam (E : ℂ) (rtlN A cκ Q k N₀ (0))) < (lyapAvg ω lam (E : ℂ) (2 * (rtlN A cκ Q k N₀ (0)))) := hpair
  have hD0lt : (lyapAvg ω lam (E : ℂ) (rtlN A cκ Q k N₀ (0))) - (lyapAvg ω lam (E : ℂ) (2 * (rtlN A cκ Q k N₀ (0)))) < (1/10) * (lyapAvg ω lam (E : ℂ) (rtlN A cκ Q k N₀ (0))) := by linarith only [hpair0]
  have hD0mm0' : 6 * ((lyapAvg ω lam (E : ℂ) (rtlN A cκ Q k N₀ (0))) - (lyapAvg ω lam (E : ℂ) (2 * (rtlN A cκ Q k N₀ (0))))) / ((rtlMM cκ Q (rtli A cκ Q k N₀ (0))) : ℝ) ≤ κ/2 := by
    have h1 : (lyapAvg ω lam (E : ℂ) (rtlN A cκ Q k N₀ (0))) - (lyapAvg ω lam (E : ℂ) (2 * (rtlN A cκ Q k N₀ (0)))) ≤ C₀/10 := by linarith only [hL0C₀, hD0lt]
    have h2 : (0:ℝ) < ((rtlMM cκ Q (rtli A cκ Q k N₀ (0))) : ℝ) := by
      have hmm := rtlMM_ge cκ Q ((rtli A cκ Q k N₀ (0))) (hbig2 _ (rtli_le A cκ Q k N₀ 0))
      have hx := Real.exp_pos (cκ*(Q ((rtli A cκ Q k N₀ (0))) : ℝ)/2); linarith only [hmm, hx]
    have h3 : (((rtlMM cκ Q (rtli A cκ Q k N₀ (0))) : ℝ))⁻¹ ≤ 10 * Real.exp (-(cκ*(Q 0 : ℝ)/2)) := by
      have hb := hInv_bound ((rtli A cκ Q k N₀ (0))) (rtli_le A cκ Q k N₀ 0)
      have hQgt := hQQmono ((rtli A cκ Q k N₀ (0))) (rtli_le A cκ Q k N₀ 0)
      have hexp_le : Real.exp (-(cκ*(Q ((rtli A cκ Q k N₀ (0))) : ℝ)/2)) ≤ Real.exp (-(cκ*(Q 0 : ℝ)/2)) := by
        apply Real.exp_le_exp.mpr; nlinarith only [hQgt, hcκ]
      linarith only [hb, hexp_le]
    rw [div_eq_mul_inv]
    calc 6 * ((lyapAvg ω lam (E : ℂ) (rtlN A cκ Q k N₀ (0))) - (lyapAvg ω lam (E : ℂ) (2 * (rtlN A cκ Q k N₀ (0))))) * ((rtlMM cκ Q (rtli A cκ Q k N₀ (0))) : ℝ)⁻¹
        ≤ 6 * (C₀/10) * ((rtlMM cκ Q (rtli A cκ Q k N₀ (0))) : ℝ)⁻¹ := by
          apply mul_le_mul_of_nonneg_right (by linarith only [h1]) (by positivity)
      _ ≤ 6 * (C₀/10) * (10 * Real.exp (-(cκ*(Q 0 : ℝ)/2))) := by
          apply mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = 6 * C₀ * Real.exp (-(cκ*(Q 0 : ℝ)/2)) := by ring
      _ ≤ κ/2 := hsmall1
  have hD0mm0 : 6 * ((lyapAvg ω lam (E : ℂ) (rtlN A cκ Q k N₀ (0))) - (lyapAvg ω lam (E : ℂ) (2 * (rtlN A cκ Q k N₀ (0))))) / ((rtlMM cκ Q (rtli A cκ Q k N₀ (0))) : ℝ)
      ≤ 60 * C₀ * Real.exp (-(c*κ*(Q 0 : ℝ)/8)) := by
    have h1 : (lyapAvg ω lam (E : ℂ) (rtlN A cκ Q k N₀ (0))) - (lyapAvg ω lam (E : ℂ) (2 * (rtlN A cκ Q k N₀ (0)))) ≤ C₀ := by linarith only [hL0C₀, hZ0nn]
    have h2 : (0:ℝ) < ((rtlMM cκ Q (rtli A cκ Q k N₀ (0))) : ℝ) := by
      have hmm := rtlMM_ge cκ Q ((rtli A cκ Q k N₀ (0))) (hbig2 _ (rtli_le A cκ Q k N₀ 0))
      have hx := Real.exp_pos (cκ*(Q ((rtli A cκ Q k N₀ (0))) : ℝ)/2); linarith only [hmm, hx]
    have hQi0 : (Q 0 : ℝ) ≤ (Q ((rtli A cκ Q k N₀ (0))) : ℝ) := hQQmono ((rtli A cκ Q k N₀ (0))) (rtli_le A cκ Q k N₀ 0)
    have hmm0_ge : Real.exp (cκ*(Q ((rtli A cκ Q k N₀ (0))) : ℝ)/2)/10 ≤ ((rtlMM cκ Q (rtli A cκ Q k N₀ (0))) : ℝ) :=
      rtlMM_ge cκ Q ((rtli A cκ Q k N₀ (0))) (hbig2 _ (rtli_le A cκ Q k N₀ 0))
    have hexp2 : 1 ≤ Real.exp (cκ*(Q ((rtli A cκ Q k N₀ (0))) : ℝ)/2 - cκ*(Q 0 : ℝ)/8) := by
      apply Real.one_le_exp
      have hp1 := mul_le_mul_of_nonneg_left hQi0 hcκ.le
      have hp2 : 0 ≤ cκ * (Q 0 : ℝ) := mul_nonneg hcκ.le (Nat.cast_nonneg _)
      linarith only [hp1, hp2]
    rw [div_le_iff₀ h2]
    calc 6 * ((lyapAvg ω lam (E : ℂ) (rtlN A cκ Q k N₀ (0))) - (lyapAvg ω lam (E : ℂ) (2 * (rtlN A cκ Q k N₀ (0)))))
        ≤ 6 * C₀ := by linarith only [h1]
      _ ≤ 6 * C₀ * Real.exp (cκ*(Q ((rtli A cκ Q k N₀ (0))) : ℝ)/2 - cκ*(Q 0 : ℝ)/8) := by
          nlinarith only [hexp2, hC₀pos, mul_le_mul_of_nonneg_left hexp2 hC₀pos.le]
      _ = 60 * C₀ * Real.exp (-(c*κ*(Q 0 : ℝ)/8)) * (Real.exp (cκ*(Q ((rtli A cκ Q k N₀ (0))) : ℝ)/2)/10) := by
          rw [show Real.exp (cκ*(Q ((rtli A cκ Q k N₀ (0))) : ℝ)/2 - cκ*(Q 0 : ℝ)/8)
            = Real.exp (cκ*(Q ((rtli A cκ Q k N₀ (0))) : ℝ)/2) * Real.exp (-(c*κ*(Q 0 : ℝ)/8)) by
            rw [← Real.exp_add, hcκdef]; congr 1]
          ring
      _ ≤ 60 * C₀ * Real.exp (-(c*κ*(Q 0 : ℝ)/8)) * ((rtlMM cκ Q (rtli A cκ Q k N₀ (0))) : ℝ) := by
          apply mul_le_mul_of_nonneg_left hmm0_ge (by positivity)
  have hEsum_bound : Esum ≤ 2*(Sb+1)*(76*C₀+9)/(1 - Real.exp (-(cκ/2)))
      * Real.exp (-(c*κ*(Q 0 : ℝ)/8)) := by
    have h1 : Real.exp (-(cκ*(Q 0 : ℝ)/2)) ≤ Real.exp (-(c*κ*(Q 0 : ℝ)/8)) := by
      apply Real.exp_le_exp.mpr
      have hQ0 : 0 ≤ (Q 0 : ℝ) := by positivity
      rw [hcκdef]
      have hp := mul_nonneg (mul_nonneg hc0.le hκ.le) hQ0
      linarith only [hp]
    have h2 : (Sb+1)*(76*C₀+9) * Real.exp (-(cκ*(Q 0 : ℝ)/2))
        ≤ (Sb+1)*(76*C₀+9) * Real.exp (-(c*κ*(Q 0 : ℝ)/8)) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : (Sb+1)*(76*C₀+9) * Real.exp (-(cκ*(Q 0 : ℝ)/2)) / (1 - Real.exp (-(cκ/2)))
        ≤ (Sb+1)*(76*C₀+9) * Real.exp (-(c*κ*(Q 0 : ℝ)/8)) / (1 - Real.exp (-(cκ/2))) :=
      div_le_div_of_nonneg_right h2 (le_of_lt hden)
    rw [hEsumdef, hEsum0def]
    calc 2 * ((Sb+1)*(76*C₀+9) * Real.exp (-(cκ*(Q 0 : ℝ)/2)) / (1 - Real.exp (-(cκ/2))))
        ≤ 2 * ((Sb+1)*(76*C₀+9) * Real.exp (-(c*κ*(Q 0 : ℝ)/8)) / (1 - Real.exp (-(cκ/2)))) := by
          linarith only [h3]
      _ = 2*(Sb+1)*(76*C₀+9)/(1 - Real.exp (-(cκ/2))) * Real.exp (-(c*κ*(Q 0 : ℝ)/8)) := by ring
  -- ================= partial sums of the errors =================
  have hterm_eq : ∀ t, ((4*C₀+1)*Real.exp (-(cκ * (Q (rtli A cκ Q k N₀ (t)) : ℝ)/2)) + 4*C₀/((rtlMM cκ Q (rtli A cκ Q k N₀ (t))) : ℝ)) + 4 * (2*((4*C₀+1)*Real.exp (-(cκ * (Q (rtli A cκ Q k N₀ (t)) : ℝ)/2))))
      = (4*C₀+1) * Real.exp (-(cκ * (Q ((rtli A cκ Q k N₀ (t))) : ℝ) / 2))
          + 4 * C₀ / (rtlMM cκ Q ((rtli A cκ Q k N₀ (t))) : ℝ)
          + 4 * (2 * (4*C₀+1) * Real.exp (-(cκ * (Q ((rtli A cκ Q k N₀ (t))) : ℝ) / 2))) := by
    intro t; ring
  have hsum0 : (∑ t ∈ Finset.range s0, (((4*C₀+1)*Real.exp (-(cκ * (Q (rtli A cκ Q k N₀ (t)) : ℝ)/2)) + 4*C₀/((rtlMM cκ Q (rtli A cκ Q k N₀ (t))) : ℝ)) + 4 * (2*((4*C₀+1)*Real.exp (-(cκ * (Q (rtli A cκ Q k N₀ (t)) : ℝ)/2)))))) ≤ Esum0 := by
    have h := rtl_sum_eps_le A cκ b C₀ Q k N₀ Sb s0 hcκ hb (le_of_lt hC₀pos)
      hQ1 hQmono hgrowth hA0 hbig hbig2 hSb_gt (fun t ht => hilt t ht)
    rw [hEsum0def]
    refine le_trans (le_of_eq ?_) h
    apply Finset.sum_congr rfl
    intro t ht; exact hterm_eq t
  have hstep0 : ((4*C₀+1)*Real.exp (-(cκ * (Q (rtli A cκ Q k N₀ (s0)) : ℝ)/2)) + 4*C₀/((rtlMM cκ Q (rtli A cκ Q k N₀ (s0))) : ℝ)) + 4 * (2*((4*C₀+1)*Real.exp (-(cκ * (Q (rtli A cκ Q k N₀ (s0)) : ℝ)/2)))) ≤ (76*C₀+9) * Real.exp (-(cκ*(Q k : ℝ)/2)) := by
    have h1 : 4*C₀/(rtlMM cκ Q k : ℝ) ≤ 40*C₀*Real.exp (-(cκ*(Q k : ℝ)/2)) := by
      have hb := hInv_bound k (le_refl k)
      rw [div_eq_mul_inv]
      linarith only [mul_le_mul_of_nonneg_left hb (le_of_lt hC₀pos)]
    rw [show ((4*C₀+1)*Real.exp (-(cκ * (Q (rtli A cκ Q k N₀ (s0)) : ℝ)/2)) + 4*C₀/((rtlMM cκ Q (rtli A cκ Q k N₀ (s0))) : ℝ)) + 4 * (2*((4*C₀+1)*Real.exp (-(cκ * (Q (rtli A cκ Q k N₀ (s0)) : ℝ)/2)))) = (4*C₀+1)*Real.exp (-(cκ*(Q k : ℝ)/2))
        + 4*C₀/(rtlMM cκ Q k : ℝ) + 8*((4*C₀+1)*Real.exp (-(cκ*(Q k : ℝ)/2))) by
      rw [hterm_eq s0, hiS]; ring]
    linarith only [h1]
  have hsumS : (∑ t ∈ Finset.range S, (((4*C₀+1)*Real.exp (-(cκ * (Q (rtli A cκ Q k N₀ (t)) : ℝ)/2)) + 4*C₀/((rtlMM cκ Q (rtli A cκ Q k N₀ (t))) : ℝ)) + 4 * (2*((4*C₀+1)*Real.exp (-(cκ * (Q (rtli A cκ Q k N₀ (t)) : ℝ)/2)))))) ≤ Esum := by
    rw [hSdef, Finset.sum_range_succ]
    have h2 : ((4*C₀+1)*Real.exp (-(cκ * (Q (rtli A cκ Q k N₀ (s0)) : ℝ)/2)) + 4*C₀/((rtlMM cκ Q (rtli A cκ Q k N₀ (s0))) : ℝ)) + 4 * (2*((4*C₀+1)*Real.exp (-(cκ * (Q (rtli A cκ Q k N₀ (s0)) : ℝ)/2)))) ≤ (76*C₀+9) * Real.exp (-(cκ*(Q 0 : ℝ)/2)) :=
      le_trans hstep0 (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (by have := hQQmono k (le_refl k); nlinarith only [this, hcκ])) (by positivity))
    have h3 : (76*C₀+9) * Real.exp (-(cκ*(Q 0 : ℝ)/2)) ≤ Esum0 := hEsum0_ge
    rw [hEsumdef]
    linarith only [hsum0, h2, h3]
  have hpsum : ∀ m ≤ S, (∑ t ∈ Finset.range m, (((4*C₀+1)*Real.exp (-(cκ * (Q (rtli A cκ Q k N₀ (t)) : ℝ)/2)) + 4*C₀/((rtlMM cκ Q (rtli A cκ Q k N₀ (t))) : ℝ)) + 4 * (2*((4*C₀+1)*Real.exp (-(cκ * (Q (rtli A cκ Q k N₀ (t)) : ℝ)/2)))))) ≤ Esum := by
    intro m hm
    rcases lt_or_eq_of_le hm with hlt | heq
    · have hm0 : m ≤ s0 := by omega
      have h1 : (∑ t ∈ Finset.range m, (((4*C₀+1)*Real.exp (-(cκ * (Q (rtli A cκ Q k N₀ (t)) : ℝ)/2)) + 4*C₀/((rtlMM cκ Q (rtli A cκ Q k N₀ (t))) : ℝ)) + 4 * (2*((4*C₀+1)*Real.exp (-(cκ * (Q (rtli A cκ Q k N₀ (t)) : ℝ)/2))))))
          ≤ ∑ t ∈ Finset.range s0, (((4*C₀+1)*Real.exp (-(cκ * (Q (rtli A cκ Q k N₀ (t)) : ℝ)/2)) + 4*C₀/((rtlMM cκ Q (rtli A cκ Q k N₀ (t))) : ℝ)) + 4 * (2*((4*C₀+1)*Real.exp (-(cκ * (Q (rtli A cκ Q k N₀ (t)) : ℝ)/2))))) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro x hx; exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hm0)
        · intro x _ _; positivity
      rw [hEsumdef]
      linarith only [h1, hsum0, hEsum_nonneg, hEsumdef]
    · rw [heq]; exact hsumS
  -- ================= the tower invariants =================
  set ℓlo : ℝ := (lyapAvg ω lam (E : ℂ) (rtlN A cκ Q k N₀ (0))) - 2*((lyapAvg ω lam (E : ℂ) (rtlN A cκ Q k N₀ (0))) - (lyapAvg ω lam (E : ℂ) (2 * (rtlN A cκ Q k N₀ (0))))) - 6*((lyapAvg ω lam (E : ℂ) (rtlN A cκ Q k N₀ (0))) - (lyapAvg ω lam (E : ℂ) (2 * (rtlN A cκ Q k N₀ (0)))))/((rtlMM cκ Q (rtli A cκ Q k N₀ (0))) : ℝ) - Esum with hℓlo
  have hℓlo_gt : 100*κ < ℓlo := by
    rw [hℓlo]; linarith only [hlev0, hD0lt, hD0mm0', hEsum_le, hκ]
  have hℓlo_159 : 159*κ < ℓlo := by
    rw [hℓlo]; linarith only [hlev0, hD0lt, hD0mm0', hEsum_le, hκ]
  have hInv : ∀ s, s ≤ S → (((∀ t < s, |(lyapAvg ω lam (E : ℂ) (rtlN A cκ Q k N₀ (t+1))) + (lyapAvg ω lam (E : ℂ) (rtlN A cκ Q k N₀ (t))) - 2*(lyapAvg ω lam (E : ℂ) (2 * (rtlN A cκ Q k N₀ (t))))| ≤ ((4*C₀+1)*Real.exp (-(cκ * (Q (rtli A cκ Q k N₀ (t)) : ℝ)/2)) + 4*C₀/((rtlMM cκ Q (rtli A cκ Q k N₀ (t))) : ℝ)))
        ∧ (∀ t < s, |((lyapAvg ω lam (E : ℂ) (rtlN A cκ Q k N₀ (t+1))) - (lyapAvg ω lam (E : ℂ) (2 * (rtlN A cκ Q k N₀ (t+1))))) - (1/((rtlMM cκ Q (rtli A cκ Q k N₀ (t))) : ℝ))*((lyapAvg ω lam (E : ℂ) (rtlN A cκ Q k N₀ (t))) - (lyapAvg ω lam (E : ℂ) (2 * (rtlN A cκ Q k N₀ (t)))))| ≤ (2*((4*C₀+1)*Real.exp (-(cκ * (Q (rtli A cκ Q k N₀ (t)) : ℝ)/2))))))
        ∧ (ℓlo ≤ (lyapAvg ω lam (E : ℂ) (rtlN A cκ Q k N₀ (s)))) ∧ ((9/10)*(lyapAvg ω lam (E : ℂ) (rtlN A cκ Q k N₀ (s))) < (lyapAvg ω lam (E : ℂ) (2 * (rtlN A cκ Q k N₀ (s)))))) := by
    intro s
    induction s with
    | zero =>
      intro _
      refine ⟨⟨fun t ht => absurd ht (by omega), fun t ht => absurd ht (by omega)⟩, ?_, ?_⟩
      · have h6 : (0:ℝ) ≤ 6*((lyapAvg ω lam (E : ℂ) (rtlN A cκ Q k N₀ (0))) - (lyapAvg ω lam (E : ℂ) (2 * (rtlN A cκ Q k N₀ (0)))))/((rtlMM cκ Q (rtli A cκ Q k N₀ (0))) : ℝ) :=
          div_nonneg (by linarith only [hD0]) (Nat.cast_nonneg _)
        rw [hℓlo]; linarith only [hD0, hEsum_nonneg, h6]
      · exact hpair0
    | succ n ih =>
      intro hns
      have hnS : n ≤ S := by omega
      obtain ⟨⟨hst1, hst2⟩, hlevlo, hpairn⟩ := ih hnS
      have hlevn : 100*κ < (lyapAvg ω lam (E : ℂ) (rtlN A cκ Q k N₀ (n))) := lt_of_lt_of_le hℓlo_gt hlevlo
      obtain ⟨hs1, hs2⟩ := hstep n hlevn hpairn
      have hst1' : ∀ t < n+1, |(lyapAvg ω lam (E : ℂ) (rtlN A cκ Q k N₀ (t+1))) + (lyapAvg ω lam (E : ℂ) (rtlN A cκ Q k N₀ (t))) - 2*(lyapAvg ω lam (E : ℂ) (2 * (rtlN A cκ Q k N₀ (t))))| ≤ ((4*C₀+1)*Real.exp (-(cκ * (Q (rtli A cκ Q k N₀ (t)) : ℝ)/2)) + 4*C₀/((rtlMM cκ Q (rtli A cκ Q k N₀ (t))) : ℝ)) := by
        intro t ht
        rcases Nat.lt_succ_iff_lt_or_eq.mp ht with h | h
        · exact hst1 t h
        · rw [h]; exact hs1
      have hst2' : ∀ t < n+1, |((lyapAvg ω lam (E : ℂ) (rtlN A cκ Q k N₀ (t+1))) - (lyapAvg ω lam (E : ℂ) (2 * (rtlN A cκ Q k N₀ (t+1))))) - (1/((rtlMM cκ Q (rtli A cκ Q k N₀ (t))) : ℝ))*((lyapAvg ω lam (E : ℂ) (rtlN A cκ Q k N₀ (t))) - (lyapAvg ω lam (E : ℂ) (2 * (rtlN A cκ Q k N₀ (t)))))| ≤ (2*((4*C₀+1)*Real.exp (-(cκ * (Q (rtli A cκ Q k N₀ (t)) : ℝ)/2)))) := by
        intro t ht
        rcases Nat.lt_succ_iff_lt_or_eq.mp ht with h | h
        · exact hst2 t h
        · rw [h]; exact hs2
      refine ⟨⟨hst1', hst2'⟩, ?_, ?_⟩
      · have hft := finite_tower_bound_v3 ω lam (E:ℂ) (rtlN A cκ Q k N₀) (fun t => (rtlMM cκ Q (rtli A cκ Q k N₀ (t))))
          (fun t => ((4*C₀+1)*Real.exp (-(cκ * (Q (rtli A cκ Q k N₀ (t)) : ℝ)/2)) + 4*C₀/((rtlMM cκ Q (rtli A cκ Q k N₀ (t))) : ℝ))) (fun t => (2*((4*C₀+1)*Real.exp (-(cκ * (Q (rtli A cκ Q k N₀ (t)) : ℝ)/2))))) (n+1) (by omega) (fun t => rfl) hmm3
          (fun t _ => by positivity) (fun t _ => by positivity) hst1' hst2'
        have hsum := hpsum (n+1) hns
        have hsum_eq : (∑ t ∈ Finset.range (n+1), ((4*C₀+1)*Real.exp (-(cκ * (Q (rtli A cκ Q k N₀ (t)) : ℝ)/2)) + 4*C₀/((rtlMM cκ Q (rtli A cκ Q k N₀ (t))) : ℝ))) + 4 * (∑ t ∈ Finset.range (n+1), (2*((4*C₀+1)*Real.exp (-(cκ * (Q (rtli A cκ Q k N₀ (t)) : ℝ)/2)))))
            = ∑ t ∈ Finset.range (n+1), (((4*C₀+1)*Real.exp (-(cκ * (Q (rtli A cκ Q k N₀ (t)) : ℝ)/2)) + 4*C₀/((rtlMM cκ Q (rtli A cκ Q k N₀ (t))) : ℝ)) + 4*(2*((4*C₀+1)*Real.exp (-(cκ * (Q (rtli A cκ Q k N₀ (t)) : ℝ)/2))))) := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        rw [abs_of_nonneg hD0] at hft
        rw [hℓlo]
        have h1 := (abs_le.mp hft).1
        linarith only [h1, hsum, hsum_eq, hD0, hEsum_nonneg]
      · have h1 := (abs_le.mp hs1).1
        have h2 := (abs_le.mp hs2).2
        have hDn : (lyapAvg ω lam (E : ℂ) (rtlN A cκ Q k N₀ (n))) - (lyapAvg ω lam (E : ℂ) (2 * (rtlN A cκ Q k N₀ (n)))) < (1/10) * (lyapAvg ω lam (E : ℂ) (rtlN A cκ Q k N₀ (n))) := by linarith only [hpairn]
        have hmm3n : (3:ℝ) ≤ ((rtlMM cκ Q (rtli A cκ Q k N₀ (n))) : ℝ) := by exact_mod_cast hmm3 n
        have hb1 : (lyapAvg ω lam (E : ℂ) (rtlN A cκ Q k N₀ (n+1))) ≥ (4/5) * (lyapAvg ω lam (E : ℂ) (rtlN A cκ Q k N₀ (n))) - ((4*C₀+1)*Real.exp (-(cκ * (Q (rtli A cκ Q k N₀ (n)) : ℝ)/2)) + 4*C₀/((rtlMM cκ Q (rtli A cκ Q k N₀ (n))) : ℝ)) := by linarith only [h1, hDn]
        have hb2 : (lyapAvg ω lam (E : ℂ) (rtlN A cκ Q k N₀ (n+1))) - (lyapAvg ω lam (E : ℂ) (2 * (rtlN A cκ Q k N₀ (n+1)))) ≤ (lyapAvg ω lam (E : ℂ) (rtlN A cκ Q k N₀ (n)))/30 + (2*((4*C₀+1)*Real.exp (-(cκ * (Q (rtli A cκ Q k N₀ (n)) : ℝ)/2)))) := by
          have : (1/((rtlMM cκ Q (rtli A cκ Q k N₀ (n))) : ℝ))*((lyapAvg ω lam (E : ℂ) (rtlN A cκ Q k N₀ (n))) - (lyapAvg ω lam (E : ℂ) (2 * (rtlN A cκ Q k N₀ (n))))) ≤ (lyapAvg ω lam (E : ℂ) (rtlN A cκ Q k N₀ (n)))/30 := by
            have hmmpos : (0:ℝ) < ((rtlMM cκ Q (rtli A cκ Q k N₀ (n))) : ℝ) := by linarith only [hmm3n]
            have hinv0 : (0:ℝ) ≤ (((rtlMM cκ Q (rtli A cκ Q k N₀ (n))) : ℝ))⁻¹ := inv_nonneg.mpr hmmpos.le
            have hinv3 : (((rtlMM cκ Q (rtli A cκ Q k N₀ (n))) : ℝ))⁻¹ ≤ 1/3 := (inv_anti₀ (by norm_num) hmm3n).trans_eq (by norm_num)
            have hL0 : (0:ℝ) ≤ (lyapAvg ω lam (E : ℂ) (rtlN A cκ Q k N₀ (n))) := by linarith only [hlevn, hκ]
            calc (1/((rtlMM cκ Q (rtli A cκ Q k N₀ (n))) : ℝ))*((lyapAvg ω lam (E : ℂ) (rtlN A cκ Q k N₀ (n))) - (lyapAvg ω lam (E : ℂ) (2 * (rtlN A cκ Q k N₀ (n)))))
                = (((rtlMM cκ Q (rtli A cκ Q k N₀ (n))) : ℝ))⁻¹ * ((lyapAvg ω lam (E : ℂ) (rtlN A cκ Q k N₀ (n))) - (lyapAvg ω lam (E : ℂ) (2 * (rtlN A cκ Q k N₀ (n))))) := by rw [one_div]
              _ ≤ (((rtlMM cκ Q (rtli A cκ Q k N₀ (n))) : ℝ))⁻¹ * ((1/10) * (lyapAvg ω lam (E : ℂ) (rtlN A cκ Q k N₀ (n)))) := mul_le_mul_of_nonneg_left hDn.le hinv0
              _ ≤ (1/3) * ((1/10) * (lyapAvg ω lam (E : ℂ) (rtlN A cκ Q k N₀ (n)))) := mul_le_mul_of_nonneg_right hinv3 (by linarith only [hL0])
              _ = (lyapAvg ω lam (E : ℂ) (rtlN A cκ Q k N₀ (n)))/30 := by ring
          linarith only [h2, this]
        have hLnn : (159:ℝ)*κ ≤ (lyapAvg ω lam (E : ℂ) (rtlN A cκ Q k N₀ (n))) := by linarith only [hlevlo, hℓlo_159]
        have he1' := he1_le' n
        have he2' := he2_le' n
        have hE1E2 : ((4*C₀+1)*Real.exp (-(cκ * (Q (rtli A cκ Q k N₀ (n)) : ℝ)/2)) + 4*C₀/((rtlMM cκ Q (rtli A cκ Q k N₀ (n))) : ℝ))/10 + (2*((4*C₀+1)*Real.exp (-(cκ * (Q (rtli A cκ Q k N₀ (n)) : ℝ)/2)))) ≤ (11/10) * Esum := by linarith only [he1', he2']
        have hEsum_le' : (11/10) * Esum ≤ (11/20) * κ := by linarith only [hEsum_le]
        linarith only [hb1, hb2, hLnn, hE1E2, hEsum_le', hκ]
  -- ================= final assembly =================
  have hftS := finite_tower_bound_v3 ω lam (E:ℂ) (rtlN A cκ Q k N₀) (fun t => (rtlMM cκ Q (rtli A cκ Q k N₀ (t))))
    (fun t => ((4*C₀+1)*Real.exp (-(cκ * (Q (rtli A cκ Q k N₀ (t)) : ℝ)/2)) + 4*C₀/((rtlMM cκ Q (rtli A cκ Q k N₀ (t))) : ℝ))) (fun t => (2*((4*C₀+1)*Real.exp (-(cκ * (Q (rtli A cκ Q k N₀ (t)) : ℝ)/2))))) S (by omega) (fun t => rfl) hmm3
    (fun t _ => by positivity) (fun t _ => by positivity) (hInv S (le_refl S)).1.1 (hInv S (le_refl S)).1.2
  have hsum_eqS : (∑ t ∈ Finset.range S, ((4*C₀+1)*Real.exp (-(cκ * (Q (rtli A cκ Q k N₀ (t)) : ℝ)/2)) + 4*C₀/((rtlMM cκ Q (rtli A cκ Q k N₀ (t))) : ℝ))) + 4 * (∑ t ∈ Finset.range S, (2*((4*C₀+1)*Real.exp (-(cκ * (Q (rtli A cκ Q k N₀ (t)) : ℝ)/2)))))
      = ∑ t ∈ Finset.range S, (((4*C₀+1)*Real.exp (-(cκ * (Q (rtli A cκ Q k N₀ (t)) : ℝ)/2)) + 4*C₀/((rtlMM cκ Q (rtli A cκ Q k N₀ (t))) : ℝ)) + 4*(2*((4*C₀+1)*Real.exp (-(cκ * (Q (rtli A cκ Q k N₀ (t)) : ℝ)/2))))) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  rw [abs_of_nonneg hD0] at hftS
  have hfinal : 2 * (lyapAvg ω lam (E : ℂ) (2 * (rtlN A cκ Q k N₀ (0)))) - (lyapAvg ω lam (E : ℂ) (rtlN A cκ Q k N₀ (0))) ≤ lyap ω lam (E : ℂ) + B * Real.exp (-(c*κ*(Q 0 : ℝ)/8)) := by
    have h1 := (abs_le.mp hftS).1
    have h2 := hrate'
    have h3 := hclose_bound
    have h4 := hD0mm0
    have h5 := hEsum_bound
    have hεeq : Real.exp (-(cκ*(Q 0 : ℝ)/8)) = Real.exp (-(c*κ*(Q 0 : ℝ)/8)) := by rw [hcκdef]
    rw [hεeq] at h3
    have hε : 0 ≤ Real.exp (-(c*κ*(Q 0 : ℝ)/8)) := (Real.exp_pos _).le
    have hBexp : B * Real.exp (-(c*κ*(Q 0 : ℝ)/8))
        = 5120 * (C₀ + 1) / (9 * cκ) * Real.exp (-(c*κ*(Q 0 : ℝ)/8))
          + 60 * C₀ * Real.exp (-(c*κ*(Q 0 : ℝ)/8))
          + 2 * (Sb + 1) * (76 * C₀ + 9) / (1 - Real.exp (-(cκ / 2))) * Real.exp (-(c*κ*(Q 0 : ℝ)/8))
          + Real.exp (-(c*κ*(Q 0 : ℝ)/8)) := by
      rw [hBdef]; ring
    linarith only [h1, h2, h3, h4, h5, hBexp, hε, hsum_eqS, hsumS]
  simpa using hfinal
