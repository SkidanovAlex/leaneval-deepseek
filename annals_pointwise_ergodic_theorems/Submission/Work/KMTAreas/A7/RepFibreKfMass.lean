import Mathlib
import Submission.Work.KMTAreas.A7.hiCrudeMult
import Submission.Work.KMTAreas.A7.M0_iteratedDeriv_bound
import Submission.Work.KMTAreas.A7.bump_support_realArc
import Submission.Work.KMTAreas.A7.integral_iteratedDeriv_bumps_le
import Submission.Work.KMTPlan.A6.symD_period_contDiff

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

/-! ## 1. The elementary scale `2^{Log N}` against `N` -/

theorem repKf_lothN_le_two_mul_N {N : ℕ} (hN : 1 ≤ N) :
    Work.KMTPlan.A6.lothN N ≤ 2 * (N : ℝ) := by
  rcases eq_or_lt_of_le hN with h | h
  · subst h
    rw [Work.KMTPlan.A6.lothN,
      show Work.Analysis.EndVar.logN 1 = 1 from by norm_num [Work.Analysis.EndVar.logN]]
    norm_num
  · have h1 := Work.KMTPlan.A6.lothN_le (show 2 ≤ N by omega)
    have h2 : (0:ℝ) ≤ (N:ℝ) := by positivity
    linarith

theorem repKf_half_le_lothN_div {N : ℕ} (hN : 1 ≤ N) :
    (1/2 : ℝ) ≤ Work.KMTPlan.A6.lothN N / (N : ℝ) := by
  have hpos : (0:ℝ) < (N:ℝ) := by positivity
  rw [le_div_iff₀ hpos]
  have h := Work.KMTPlan.A6.lole_two_mul_thN N
  linarith

theorem repKf_lothN_div_le_two {N : ℕ} (hN : 1 ≤ N) :
    Work.KMTPlan.A6.lothN N / (N : ℝ) ≤ 2 := by
  have hpos : (0:ℝ) < (N:ℝ) := by positivity
  rw [div_le_iff₀ hpos]
  exact repKf_lothN_le_two_mul_N hN

/-- `2^{k-Log N} = 2^k / 2^{Log N}`. -/
theorem repKf_two_logN (N k : ℕ) :
    (2:ℝ)^((k:ℝ) - (Work.Analysis.EndVar.logN N : ℝ))
      = (2:ℝ)^k / Work.KMTPlan.A6.lothN N := by
  rw [Real.rpow_sub (by norm_num : (0:ℝ) < 2), Real.rpow_natCast]
  rfl

/-- `2^{d(k-Log N)} = 2^{dk} / (2^{Log N})^d`. -/
theorem repKf_two_logN_pow (N d k : ℕ) :
    (2:ℝ)^((d:ℝ) * ((k:ℝ) - (Work.Analysis.EndVar.logN N : ℝ)))
      = (2:ℝ)^(d*k) / (Work.KMTPlan.A6.lothN N)^d := by
  rw [show (d:ℝ) * ((k:ℝ) - (Work.Analysis.EndVar.logN N : ℝ))
      = ((k:ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) * (d:ℝ) by ring,
    Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),
    Real.rpow_natCast ((2:ℝ)^((k:ℝ) - (Work.Analysis.EndVar.logN N : ℝ))) d,
    repKf_two_logN N k, div_pow, ← pow_mul, Nat.mul_comm k d]

/-! ## 2. The real- and integer-power exponent dictionaries -/

/-- `x^((m:ℝ)-1) = x^((m:ℤ)-1)` for `m ≤ 2`. -/
theorem repKf_rpow_eq_zpow (x : ℝ) (m : ℕ) (hm : m ≤ 2) :
    x ^ ((m:ℝ)-1) = x ^ ((m:ℤ)-1) := by
  interval_cases m
  · rw [show (((0:ℕ)):ℝ)-1 = -(1:ℝ) by norm_num, show (((0:ℕ)):ℤ)-1 = -(1:ℤ) by norm_num,
      Real.rpow_neg_one, zpow_neg_one]
  · rw [show (((1:ℕ)):ℝ)-1 = (0:ℝ) by norm_num, show (((1:ℕ)):ℤ)-1 = (0:ℤ) by norm_num,
      Real.rpow_zero, zpow_zero]
  · rw [show (((2:ℕ)):ℝ)-1 = (1:ℝ) by norm_num, show (((2:ℕ)):ℤ)-1 = (1:ℤ) by norm_num,
      Real.rpow_one, zpow_one]

/-- The integer `(a:ℤ) - 1` for `a ≤ 2` is one of `-1, 0, 1`. -/
theorem repKf_int_pred_mem (a : ℕ) (ha : a ≤ 2) :
    (a:ℤ) - 1 = -1 ∨ (a:ℤ) - 1 = 0 ∨ (a:ℤ) - 1 = 1 := by omega

/-- `γ^(n:ℤ) ≤ 2^M` for `1/2 ≤ γ ≤ 2` and `n ≤ M`. -/
theorem repKf_gam_zpow_le_nat {γ : ℝ} (h1 : (1/2:ℝ) ≤ γ) (h2 : γ ≤ 2) {n M : ℕ} (hn : n ≤ M) :
    γ ^ (n:ℤ) ≤ (2:ℝ)^M := by
  have h0 : (0:ℝ) ≤ γ := by linarith
  rw [zpow_natCast]
  exact (pow_le_pow_left₀ h0 h2 n).trans (pow_le_pow_right₀ (by norm_num) hn)

/-- `γ^(-(n:ℤ)) ≤ 2^M` for `1/2 ≤ γ ≤ 2` and `n ≤ M`. -/
theorem repKf_gam_zpow_le_neg {γ : ℝ} (h1 : (1/2:ℝ) ≤ γ) (h2 : γ ≤ 2) {n M : ℕ} (hn : n ≤ M) :
    γ ^ (-(n:ℤ)) ≤ (2:ℝ)^M := by
  have h0 : (0:ℝ) < γ := by linarith
  have hγinv : γ⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ h0 (by norm_num : (0:ℝ) < 2)]
    norm_num
    linarith
  have hstep : γ ^ (-(n:ℤ)) = (γ⁻¹)^n := by
    rw [zpow_neg, zpow_natCast, inv_pow]
  rw [hstep]
  exact (pow_le_pow_left₀ (by positivity) hγinv n).trans (pow_le_pow_right₀ (by norm_num) hn)

/-- `γ ^ m ≤ 2^M` for `1/2 ≤ γ ≤ 2` and `-M ≤ m ≤ M`. -/
theorem repKf_gam_zpow_le {γ : ℝ} (h1 : (1/2:ℝ) ≤ γ) (h2 : γ ≤ 2) (m : ℤ) (M : ℕ)
    (hm : -((M:ℤ)) ≤ m) (hm' : m ≤ (M:ℤ)) : γ ^ m ≤ (2:ℝ)^M := by
  rcases lt_trichotomy m 0 with hlt | heq | hgt
  · have hpos : (0:ℤ) ≤ -m := by omega
    have hm_eq : m = -(((-m).toNat : ℕ) : ℤ) := by
      rw [Int.toNat_of_nonneg hpos]
      omega
    rw [hm_eq]
    exact repKf_gam_zpow_le_neg h1 h2 (by rw [Int.toNat_le]; omega)
  · rw [heq, zpow_zero]
    exact one_le_pow₀ (by norm_num)
  · have hm_eq : m = ((m.toNat : ℕ) : ℤ) := by rw [Int.toNat_of_nonneg (le_of_lt hgt)]
    rw [hm_eq]
    exact repKf_gam_zpow_le_nat h1 h2 (by rw [Int.toNat_le]; omega)

/-- `γ^(p+dq) ≤ 2^(d+1)` for `1/2 ≤ γ ≤ 2` and `p,q ∈ {-1,0,1}`. -/
theorem repKf_gam_pow_le {γ : ℝ} (h1 : (1/2:ℝ) ≤ γ) (h2 : γ ≤ 2) (d : ℕ) (p q : ℤ)
    (hp : p = -1 ∨ p = 0 ∨ p = 1) (hq : q = -1 ∨ q = 0 ∨ q = 1) :
    γ ^ (p + (d:ℤ) * q) ≤ (2:ℝ)^(d+1) := by
  have hγ0 : γ ≠ 0 := by linarith
  have hγpos : (0:ℝ) ≤ γ := by linarith
  have hγinv : γ⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num : (0:ℝ) < 2)]
    norm_num
    linarith
  have hle : ∀ r : ℤ, r = -1 ∨ r = 0 ∨ r = 1 → γ ^ r ≤ 2 := by
    intro r hr
    rcases hr with h | h | h
    · rw [h, zpow_neg_one]; exact hγinv
    · rw [h, zpow_zero]; norm_num
    · rw [h, zpow_one]; exact h2
  have hpq : γ ^ (p + (d:ℤ)*q) = γ^p * (γ^q)^d := by
    rw [zpow_add₀ hγ0, mul_comm (d:ℤ) q, zpow_mul, zpow_natCast]
  rw [hpq]
  have hq0 : (0:ℝ) ≤ γ^q := zpow_nonneg hγpos q
  calc γ^p * (γ^q)^d ≤ 2 * 2^d :=
        mul_le_mul (hle p hp) (pow_le_pow_left₀ hq0 (hle q hq) d) (pow_nonneg hq0 d) (by norm_num)
    _ = 2^(d+1) := by rw [pow_succ]; ring

/-! ## 3. The box derivative bound for `M₀` -/

theorem repKf_M0_dp_box (P : Polynomial ℤ) (hdeg : 2 ≤ P.natDegree) :
    ∃ C A : ℝ, 0 < C ∧ 0 ≤ A ∧
      ∀ (N q k₁ k₂ : ℕ) (α β : Circ), 1 ≤ N → 1 ≤ q → q • α = 0 → q • β = 0 →
        ∀ {j₁ j₂ : ℕ}, j₁ ≤ 2 → j₂ ≤ 2 → ∀ {x y : ℝ},
          |x| ≤ (2:ℝ)^k₁ / Work.KMTPlan.A6.lothN N →
          |y| ≤ (2:ℝ)^(P.natDegree * k₂) / (Work.KMTPlan.A6.lothN N)^(P.natDegree) →
          ‖Work.KMTPlan.A6.dp j₁ j₂ (fun a b => Work.KMTAreas.A7.M0 P N q α β a b) x y‖
            ≤ C * ((2:ℝ)^k₁ + (2:ℝ)^(P.natDegree * k₂) + 1)^A * (q:ℝ)
                * (N:ℝ)^((j₁:ℤ) + ((P.natDegree:ℤ))*(j₂:ℤ) - 1) := by
  obtain ⟨C, A, hC, hA, hb⟩ := M0DerivBound P hdeg
  refine ⟨C * (2:ℝ)^(((P.natDegree:ℝ) + 1) * A), A, by positivity, hA, ?_⟩
  intro N q k₁ k₂ α β hN hq hα hβ j₁ j₂ hj₁ hj₂ x y hx hy
  have hNpos : (0:ℝ) < N := by positivity
  have hLle : (N:ℝ) ≤ 2 * Work.KMTPlan.A6.lothN N := Work.KMTPlan.A6.lole_two_mul_thN N
  have hLpos : 0 < Work.KMTPlan.A6.lothN N := Work.KMTPlan.A6.lothN_pos N
  have hx' : |x| ≤ (2:ℝ)^(k₁+1) / (N:ℝ) := by
    have h1 : (2:ℝ)^k₁ / Work.KMTPlan.A6.lothN N ≤ (2:ℝ)^(k₁+1) / (N:ℝ) := by
      rw [div_le_div_iff₀ hLpos hNpos,
        show (2:ℝ)^(k₁+1) = 2 * (2:ℝ)^k₁ by rw [pow_succ]; ring]
      have hk : (0:ℝ) ≤ (2:ℝ)^k₁ := by positivity
      nlinarith
    exact hx.trans h1
  have hy' : |y| ≤ (2:ℝ)^(P.natDegree * (k₂+1)) / (N:ℝ)^(P.natDegree) := by
    have h1 : (2:ℝ)^(P.natDegree * k₂) / (Work.KMTPlan.A6.lothN N)^(P.natDegree)
        ≤ (2:ℝ)^(P.natDegree * (k₂+1)) / (N:ℝ)^(P.natDegree) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity),
        show (2:ℝ)^(P.natDegree * (k₂+1)) = (2:ℝ)^(P.natDegree) * (2:ℝ)^(P.natDegree * k₂) by
          rw [← pow_add]; congr 1; ring]
      have hLd : (N:ℝ)^(P.natDegree)
          ≤ (2:ℝ)^(P.natDegree) * (Work.KMTPlan.A6.lothN N)^(P.natDegree) := by
        calc (N:ℝ)^(P.natDegree) ≤ (2 * Work.KMTPlan.A6.lothN N)^(P.natDegree) :=
              pow_le_pow_left₀ (by positivity) hLle _
          _ = (2:ℝ)^(P.natDegree) * (Work.KMTPlan.A6.lothN N)^(P.natDegree) := by rw [mul_pow]
      calc (2:ℝ)^(P.natDegree * k₂) * (N:ℝ)^(P.natDegree)
          ≤ (2:ℝ)^(P.natDegree * k₂)
              * ((2:ℝ)^(P.natDegree) * (Work.KMTPlan.A6.lothN N)^(P.natDegree)) :=
            mul_le_mul_of_nonneg_left hLd (by positivity)
        _ = (2:ℝ)^(P.natDegree) * (2:ℝ)^(P.natDegree * k₂)
              * (Work.KMTPlan.A6.lothN N)^(P.natDegree) := by ring
    exact hy.trans h1
  have h1 : (1:ℝ) ≤ (2:ℝ)^(k₁+1) := one_le_pow₀ (by norm_num)
  have h2 : (1:ℝ) ≤ (2:ℝ)^(P.natDegree * (k₂+1)) := one_le_pow₀ (by norm_num)
  have hmain := hb N q α β x y ((2:ℝ)^(k₁+1)) ((2:ℝ)^(P.natDegree * (k₂+1))) j₁ j₂
    hN hq hj₁ hj₂ h1 h2 hα hβ hx' hy'
  have hdp : Work.KMTPlan.A6.dp j₁ j₂ (fun a b => Work.KMTAreas.A7.M0 P N q α β a b) x y
      = Work.KMTAreas.A7.M0deriv P N q α β x y j₁ j₂ :=
    Work.KMTPlan.A6.M0_iteratedDeriv P N q α β hj₁ hj₂ x y
  have hBr : (0:ℝ) < (2:ℝ)^k₁ + (2:ℝ)^(P.natDegree * k₂) + 1 := by positivity
  have hbracket : ((2:ℝ)^(k₁+1) + (2:ℝ)^(P.natDegree * (k₂+1)) + 1)
      ≤ (2:ℝ)^(P.natDegree+1) * ((2:ℝ)^k₁ + (2:ℝ)^(P.natDegree * k₂) + 1) := by
    have hA' : (2:ℝ)^(k₁+1) ≤ (2:ℝ)^(P.natDegree+1) * (2:ℝ)^k₁ := by
      rw [show (2:ℝ)^(k₁+1) = 2 * (2:ℝ)^k₁ by rw [pow_succ]; ring,
        show (2:ℝ)^(P.natDegree+1) = 2 * (2:ℝ)^(P.natDegree) by rw [pow_succ]; ring]
      have h3 : (1:ℝ) ≤ (2:ℝ)^(P.natDegree) := one_le_pow₀ (by norm_num)
      have hk : (0:ℝ) ≤ (2:ℝ)^k₁ := by positivity
      nlinarith
    have hB' : (2:ℝ)^(P.natDegree * (k₂+1)) ≤
        (2:ℝ)^(P.natDegree+1) * (2:ℝ)^(P.natDegree * k₂) := by
      rw [show (2:ℝ)^(P.natDegree * (k₂+1)) = (2:ℝ)^(P.natDegree) * (2:ℝ)^(P.natDegree * k₂) by
        rw [← pow_add]; congr 1; ring]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (Nat.le_succ _)) (by positivity)
    have hC' : (1:ℝ) ≤ (2:ℝ)^(P.natDegree+1) * 1 := by
      have h3 : (1:ℝ) ≤ (2:ℝ)^(P.natDegree+1) := one_le_pow₀ (by norm_num)
      linarith
    have h4 : (0:ℝ) ≤ (2:ℝ)^k₁ + (2:ℝ)^(P.natDegree*k₂) := by positivity
    nlinarith [hA', hB', hC', h4]
  have hrpow : ((2:ℝ)^(k₁+1) + (2:ℝ)^(P.natDegree * (k₂+1)) + 1)^A
      ≤ (2:ℝ)^(((P.natDegree:ℝ)+1) * A) * ((2:ℝ)^k₁ + (2:ℝ)^(P.natDegree * k₂) + 1)^A := by
    have h2d : ((2:ℝ)^(P.natDegree+1))^A = (2:ℝ)^(((P.natDegree:ℝ)+1) * A) := by
      rw [← Real.rpow_natCast (2:ℝ) (P.natDegree+1)]
      rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
      congr 1
      push_cast
      ring
    have hle := Real.rpow_le_rpow (by positivity) hbracket hA
    rw [Real.mul_rpow (by positivity) (by positivity), h2d] at hle
    exact hle
  have hexp : (N:ℝ)^j₁ * (N:ℝ)^(P.natDegree * j₂) / (N:ℝ)
      = (N:ℝ)^((j₁:ℤ) + ((P.natDegree:ℤ))*(j₂:ℤ) - 1) := by
    rw [div_eq_mul_inv, ← zpow_natCast (N:ℝ) j₁, ← zpow_natCast (N:ℝ) (P.natDegree * j₂),
      ← zpow_neg_one, ← zpow_add₀ (ne_of_gt hNpos), ← zpow_add₀ (ne_of_gt hNpos)]
    congr 1
  have hqnn : (0:ℝ) ≤ (q:ℝ) := by positivity
  have hZnn : (0:ℝ) ≤ (N:ℝ)^j₁ * (N:ℝ)^(P.natDegree * j₂) / (N:ℝ) := by positivity
  have hmain' : ‖Work.KMTAreas.A7.M0deriv P N q α β x y j₁ j₂‖
      ≤ C * ((2:ℝ)^(k₁+1) + (2:ℝ)^(P.natDegree * (k₂+1)) + 1)^A * (q:ℝ)
        * (((N:ℝ)^j₁ * (N:ℝ)^(P.natDegree * j₂)) / (N:ℝ)) := by
    refine hmain.trans (le_of_eq ?_)
    ring
  have hstep : C * ((2:ℝ)^(k₁+1) + (2:ℝ)^(P.natDegree * (k₂+1)) + 1)^A * (q:ℝ)
        * (((N:ℝ)^j₁ * (N:ℝ)^(P.natDegree * j₂)) / (N:ℝ))
      ≤ C * ((2:ℝ)^(((P.natDegree:ℝ)+1) * A)
          * ((2:ℝ)^k₁ + (2:ℝ)^(P.natDegree * k₂) + 1)^A) * (q:ℝ)
        * (((N:ℝ)^j₁ * (N:ℝ)^(P.natDegree * j₂)) / (N:ℝ)) := by
    refine mul_le_mul_of_nonneg_right ?_ hZnn
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrpow hC.le) hqnn
  calc ‖Work.KMTPlan.A6.dp j₁ j₂ (fun a b => Work.KMTAreas.A7.M0 P N q α β a b) x y‖
      = ‖Work.KMTAreas.A7.M0deriv P N q α β x y j₁ j₂‖ := by rw [hdp]
    _ ≤ C * ((2:ℝ)^(k₁+1) + (2:ℝ)^(P.natDegree * (k₂+1)) + 1)^A * (q:ℝ)
          * (((N:ℝ)^j₁ * (N:ℝ)^(P.natDegree * j₂)) / (N:ℝ)) := hmain'
    _ ≤ C * ((2:ℝ)^(((P.natDegree:ℝ)+1) * A)
          * ((2:ℝ)^k₁ + (2:ℝ)^(P.natDegree * k₂) + 1)^A) * (q:ℝ)
          * (((N:ℝ)^j₁ * (N:ℝ)^(P.natDegree * j₂)) / (N:ℝ)) := hstep
    _ = (C * (2:ℝ)^(((P.natDegree:ℝ)+1) * A)) * ((2:ℝ)^k₁ + (2:ℝ)^(P.natDegree * k₂) + 1)^A
          * (q:ℝ) * (N:ℝ)^((j₁:ℤ) + ((P.natDegree:ℤ))*(j₂:ℤ) - 1) := by
        rw [hexp]; ring

/-! ## 4. The Leibniz expansion of the symbol `φ_N ⊗ φ̃_N · M₀` -/

theorem repKf_dp_leibniz (P : Polynomial ℤ) (N q k₁ k₂ : ℕ) (α β : Circ)
    (i₁ i₂ : ℕ) (hi₁ : i₁ ≤ 2) (hi₂ : i₂ ≤ 2) (x y : ℝ) :
    Work.KMTPlan.A6.dp i₁ i₂ (fun a b => varphiN N k₁ a * varphitildeN P.natDegree N k₂ b
        * M0 P N q α β a b) x y
      = ∑ b' ∈ Finset.range (i₂ + 1), ∑ a' ∈ Finset.range (i₁ + 1),
          ((i₂.choose b' : ℂ) * (i₁.choose a' : ℂ))
            * (iteratedDeriv a' (varphiN N k₁) x)
            * (Work.KMTPlan.A6.dp (i₁ - a') b' (fun a b => M0 P N q α β a b) x y)
            * (iteratedDeriv (i₂ - b') (varphitildeN P.natDegree N k₂) y) := by
  have hφ : ContDiff ℝ 2 (varphiN N k₁) :=
    (Work.KMTPlan.A6.contDiff4_varphiN N k₁).of_le (by norm_num)
  have hψ : ContDiff ℝ 2 (varphitildeN P.natDegree N k₂) :=
    (Work.KMTPlan.A6.contDiff4_varphitildeN P.natDegree N k₂).of_le (by norm_num)
  have hσ : (fun a b => varphiN N k₁ a * varphitildeN P.natDegree N k₂ b * M0 P N q α β a b)
      = (fun a b => ∑ k ∈ ({()} : Finset Unit),
          (fun (_ : Unit) a b => M0 P N q α β a b) k a b
            * (fun (_ : Unit) a => varphiN N k₁ a) k a
            * (fun (_ : Unit) b => varphitildeN P.natDegree N k₂ b) k b) := by
    funext a b
    simp only [Finset.sum_singleton]
    ring
  rw [hσ, Work.KMTPlan.A6.lodp_finset_sum_mul_three ({()} : Finset Unit)
    (fun (_ : Unit) a b => M0 P N q α β a b) (fun (_ : Unit) a => varphiN N k₁ a)
    (fun (_ : Unit) b => varphitildeN P.natDegree N k₂ b) i₁ i₂ hi₁ hi₂ y x
    (fun _ _ a => Work.KMTPlan.A6.loM0_contDiff_two_snd P N q α β a)
    (fun _ _ i₂' _ => by
      have hfun : (fun a : ℝ => iteratedDeriv i₂' (fun b : ℝ => M0 P N q α β a b) y)
          = fun a : ℝ => M0deriv P N q α β a y 0 i₂' := by
        funext a
        rw [Work.KMTPlan.A6.loiteratedDeriv_M0_snd]
      rw [hfun]
      exact Work.KMTPlan.A6.loM0deriv_contDiff_two_fst P N q α β y 0 i₂')
    (fun _ _ => hφ) (fun _ _ => hψ)]
  simp only [Finset.sum_singleton]
  -- the `dp` form of the iterated derivative of `M₀`
  have hdp : ∀ a' b' : ℕ,
      iteratedDeriv (i₁ - a') (fun a : ℝ => iteratedDeriv b' (fun b : ℝ => M0 P N q α β a b) y) x
        = Work.KMTPlan.A6.dp (i₁ - a') b' (fun a b => M0 P N q α β a b) x y := fun a' b' => rfl
  simp only [hdp]

/-! ## 5. Vanishing of the bump derivatives outside the bump supports -/

theorem repKf_iteratedDeriv_varphiN_eq_zero (N k a : ℕ) {ξ : ℝ}
    (h : (2:ℝ)^k / Work.KMTPlan.A6.lothN N < |ξ|) :
    iteratedDeriv a (varphiN N k) ξ = 0 := by
  rw [← repKf_two_logN N k] at h
  have hset : {y : ℝ | (2:ℝ)^((k:ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) < |y|} ∈ 𝓝 ξ :=
    (isOpen_lt continuous_const continuous_abs).mem_nhds h
  refine iteratedDeriv_eq_zero_of_eventuallyEq_zero (varphiN N k) ?_ a
  filter_upwards [hset] with y hy
  exact Work.KMTPlan.A6.lovarphiN_eq_zero_of_lt hy

theorem repKf_iteratedDeriv_varphitildeN_eq_zero (d N k b : ℕ) (hd : 1 ≤ d) {ξ : ℝ}
    (h : (2:ℝ)^(d*k) / (Work.KMTPlan.A6.lothN N)^d < |ξ|) :
    iteratedDeriv b (varphitildeN d N k) ξ = 0 := by
  rw [← repKf_two_logN_pow N d k] at h
  have hset : {y : ℝ | (2:ℝ)^((d:ℝ) * ((k:ℝ) - (Work.Analysis.EndVar.logN N : ℝ))) < |y|} ∈ 𝓝 ξ :=
    (isOpen_lt continuous_const continuous_abs).mem_nhds h
  refine iteratedDeriv_eq_zero_of_eventuallyEq_zero (varphitildeN d N k) ?_ b
  filter_upwards [hset] with y hy
  by_contra hne
  exact absurd (Work.KMTPlan.A6.lovarphitildeN_ne_zero_abs_le d N k hd hne) (not_le.mpr hy)

/-! ## 6. Smoothness and compact support of the symbol -/

theorem repKf_sym_contDiff (P : Polynomial ℤ) (N q k₁ k₂ : ℕ) (α β : Circ) :
    ContDiff ℝ 4 (fun z : ℝ × ℝ => varphiN N k₁ z.1 * varphitildeN P.natDegree N k₂ z.2
      * M0 P N q α β z.1 z.2) := by
  have hφ : ContDiff ℝ 4 (varphiN N k₁) := Work.KMTPlan.A6.contDiff4_varphiN N k₁
  have hψ : ContDiff ℝ 4 (varphitildeN P.natDegree N k₂) :=
    Work.KMTPlan.A6.contDiff4_varphitildeN P.natDegree N k₂
  have hw : ContDiff ℝ 4 (fun z : ℝ × ℝ => weylAvg P N α β z.1 z.2) :=
    Work.KMTPlan.A6.contDiff4_weylAvg P N α β
  have hm : ContDiff ℝ 4 (fun z : ℝ × ℝ => mTilde P N z.1 z.2) := by
    have h := Work.KMTPlan.A6.mTildeDeriv_contDiff_aux P N (4 : ℕ∞) 0 0
    have heq : (fun z : ℝ × ℝ => mTilde P N z.1 z.2)
        = fun z => mTildeDeriv P N z.1 z.2 0 0 := by
      funext z
      rw [mTilde, mTildeDeriv]
      simp
    rw [heq]
    exact h
  have hM0 : ContDiff ℝ 4 (fun z : ℝ × ℝ => M0 P N q α β z.1 z.2) := by
    have heq : (fun z : ℝ × ℝ => M0 P N q α β z.1 z.2)
        = fun z => weylAvg P N α β z.1 z.2 - mZ P q α β * mTilde P N z.1 z.2 := rfl
    rw [heq]
    exact hw.sub (contDiff_const.mul hm)
  exact ((hφ.comp contDiff_fst).mul (hψ.comp contDiff_snd)).mul hM0

theorem repKf_sym_hasCompactSupport (P : Polynomial ℤ) (N q k₁ k₂ : ℕ) (α β : Circ) :
    HasCompactSupport (fun z : ℝ × ℝ => varphiN N k₁ z.1 * varphitildeN P.natDegree N k₂ z.2
      * M0 P N q α β z.1 z.2) := by
  refine HasCompactSupport.of_support_subset_isCompact
    (((hasCompactSupport_varphiN N k₁).isCompact).prod
      ((hasCompactSupport_varphitildeN P.natDegree N k₂).isCompact)) ?_
  intro z hz
  rw [Function.mem_support] at hz
  exact ⟨subset_closure (fun h => hz (by simp [h])),
    subset_closure (fun h => hz (by simp [h]))⟩

theorem repKf_hcs_iteratedDeriv_varphitildeN (d N k m : ℕ) (hm : m ≤ 2) :
    HasCompactSupport (iteratedDeriv m (varphitildeN d N k)) := by
  interval_cases m
  · rw [iteratedDeriv_zero]; exact hasCompactSupport_varphitildeN d N k
  · rw [iteratedDeriv_one]; exact (hasCompactSupport_varphitildeN d N k).deriv
  · rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    exact ((hasCompactSupport_varphitildeN d N k).deriv).deriv

theorem repKf_integrable_iteratedDeriv_varphitildeN (d N k m : ℕ) (hm : m ≤ 2) :
    Integrable (fun y : ℝ => ‖iteratedDeriv m (varphitildeN d N k) y‖) :=
  (((Work.KMTPlan.A6.contDiff4_varphitildeN d N k).continuous_iteratedDeriv m
      (by exact_mod_cast (by omega : m ≤ 4))).norm).integrable_of_hasCompactSupport
    ((repKf_hcs_iteratedDeriv_varphitildeN d N k m hm).norm)

/-! ## 7. The pointwise weighted bound -/

theorem repKf_pointwise (P : Polynomial ℤ) (hdeg : 2 ≤ P.natDegree) (C A : ℝ)
    (hC : 0 ≤ C)
    (hbox : ∀ (N q k₁ k₂ : ℕ) (α β : Circ), 1 ≤ N → 1 ≤ q → q • α = 0 → q • β = 0 →
        ∀ {j₁ j₂ : ℕ}, j₁ ≤ 2 → j₂ ≤ 2 → ∀ {x y : ℝ},
          |x| ≤ (2:ℝ)^k₁ / Work.KMTPlan.A6.lothN N →
          |y| ≤ (2:ℝ)^(P.natDegree * k₂) / (Work.KMTPlan.A6.lothN N)^(P.natDegree) →
          ‖Work.KMTPlan.A6.dp j₁ j₂ (fun a b => M0 P N q α β a b) x y‖
            ≤ C * ((2:ℝ)^k₁ + (2:ℝ)^(P.natDegree * k₂) + 1)^A * (q:ℝ)
                * (N:ℝ)^((j₁:ℤ) + ((P.natDegree:ℤ))*(j₂:ℤ) - 1)) :
    ∀ (N q k₁ k₂ : ℕ) (α β : Circ), 1 ≤ N → 1 ≤ q → q • α = 0 → q • β = 0 →
      ∀ {j₁ j₂ a' b' : ℕ}, j₁ ≤ 2 → j₂ ≤ 2 → ∀ x y,
        ‖iteratedDeriv a' (varphiN N k₁) x‖ * ‖Work.KMTPlan.A6.dp j₁ j₂
            (fun a b => M0 P N q α β a b) x y‖
          * ‖iteratedDeriv b' (varphitildeN P.natDegree N k₂) y‖
        ≤ (C * ((2:ℝ)^k₁ + (2:ℝ)^(P.natDegree * k₂) + 1)^A * (q:ℝ)
            * (N:ℝ)^((j₁:ℤ) + ((P.natDegree:ℤ))*(j₂:ℤ) - 1))
          * (‖iteratedDeriv a' (varphiN N k₁) x‖
              * ‖iteratedDeriv b' (varphitildeN P.natDegree N k₂) y‖) := by
  intro N q k₁ k₂ α β hN hq hα hβ j₁ j₂ a' b' hj₁ hj₂ x y
  by_cases hx : |x| ≤ (2:ℝ)^k₁ / Work.KMTPlan.A6.lothN N
  · by_cases hy : |y| ≤ (2:ℝ)^(P.natDegree * k₂) / (Work.KMTPlan.A6.lothN N)^(P.natDegree)
    · have h := hbox N q k₁ k₂ α β hN hq hα hβ hj₁ hj₂ hx hy
      calc ‖iteratedDeriv a' (varphiN N k₁) x‖
            * ‖Work.KMTPlan.A6.dp j₁ j₂ (fun a b => M0 P N q α β a b) x y‖
            * ‖iteratedDeriv b' (varphitildeN P.natDegree N k₂) y‖
          ≤ ‖iteratedDeriv a' (varphiN N k₁) x‖
              * (C * ((2:ℝ)^k₁ + (2:ℝ)^(P.natDegree * k₂) + 1)^A * (q:ℝ)
                  * (N:ℝ)^((j₁:ℤ) + ((P.natDegree:ℤ))*(j₂:ℤ) - 1))
              * ‖iteratedDeriv b' (varphitildeN P.natDegree N k₂) y‖ :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left h (norm_nonneg _)) (norm_nonneg _)
        _ = (C * ((2:ℝ)^k₁ + (2:ℝ)^(P.natDegree * k₂) + 1)^A * (q:ℝ)
              * (N:ℝ)^((j₁:ℤ) + ((P.natDegree:ℤ))*(j₂:ℤ) - 1))
            * (‖iteratedDeriv a' (varphiN N k₁) x‖
                * ‖iteratedDeriv b' (varphitildeN P.natDegree N k₂) y‖) := by ring
    · have h0 : iteratedDeriv b' (varphitildeN P.natDegree N k₂) y = 0 :=
        repKf_iteratedDeriv_varphitildeN_eq_zero P.natDegree N k₂ b'
          (le_trans (by norm_num : 1 ≤ 2) hdeg) (lt_of_not_ge hy)
      simp [h0]
  · have h0 : iteratedDeriv a' (varphiN N k₁) x = 0 :=
      repKf_iteratedDeriv_varphiN_eq_zero N k₁ a' (lt_of_not_ge hx)
    simp [h0]

/-! ## 8. The arithmetic of the two bump scales -/

theorem repKf_arith (γ : ℝ) (h1 : (1/2:ℝ) ≤ γ) (h2 : γ ≤ 2) (k₁ k₂ d : ℕ) (p q : ℤ)
    (hp : p = -1 ∨ p = 0 ∨ p = 1) (hq : q = -1 ∨ q = 0 ∨ q = 1) :
    (γ / (2:ℝ)^k₁)^p * (γ / (2:ℝ)^k₂)^((d:ℤ) * q)
      ≤ (2:ℝ)^(d+1) * (2:ℝ)^(2*k₁ + 2*d*k₂) := by
  have hγ0 : (0:ℝ) < γ := by linarith
  have hc₁ : (0:ℝ) < (2:ℝ)^k₁ := by positivity
  have hc₂ : (0:ℝ) < (2:ℝ)^k₂ := by positivity
  have h2k₁ : (1:ℝ) ≤ (2:ℝ)^k₁ := one_le_pow₀ (by norm_num)
  have h2k₂ : (1:ℝ) ≤ (2:ℝ)^k₂ := one_le_pow₀ (by norm_num)
  have h3₁ : (2:ℝ) ≤ (2:ℝ)^(k₁+1) := by
    rw [show (2:ℝ)^(k₁+1) = 2 * (2:ℝ)^k₁ by rw [pow_succ]; ring]; linarith
  have h3₂ : (2:ℝ) ≤ (2:ℝ)^(k₂+1) := by
    rw [show (2:ℝ)^(k₂+1) = 2 * (2:ℝ)^k₂ by rw [pow_succ]; ring]; linarith
  have hA : (γ / (2:ℝ)^k₁)^p ≤ (2:ℝ)^(k₁+1) := by
    rcases hp with h | h | h
    · rw [h, zpow_neg_one, inv_div]
      rw [div_le_iff₀ hγ0, show (2:ℝ)^(k₁+1) = 2 * (2:ℝ)^k₁ by rw [pow_succ]; ring]
      nlinarith
    · rw [h, zpow_zero]
      exact one_le_pow₀ (by norm_num)
    · rw [h, zpow_one, div_le_iff₀ hc₁,
        show (2:ℝ)^(k₁+1) = 2 * (2:ℝ)^k₁ by rw [pow_succ]; ring]
      nlinarith
  have hB : (γ / (2:ℝ)^k₂)^((d:ℤ) * q) ≤ (2:ℝ)^(d*(k₂+1)) := by
    rcases hq with h | h | h
    · rw [h, mul_neg, mul_one, zpow_neg, zpow_natCast,
        show (((γ / (2:ℝ)^k₂))^d)⁻¹ = ((γ / (2:ℝ)^k₂)⁻¹)^d by rw [inv_pow],
        show ((γ / (2:ℝ)^k₂))⁻¹ = (2:ℝ)^k₂ / γ by rw [inv_div],
        show (2:ℝ)^(d*(k₂+1)) = ((2:ℝ)^(k₂+1))^d by rw [mul_comm d (k₂+1), pow_mul]]
      refine pow_le_pow_left₀ (by positivity) ?_ d
      rw [div_le_iff₀ hγ0, show (2:ℝ)^(k₂+1) = 2 * (2:ℝ)^k₂ by rw [pow_succ]; ring]
      nlinarith
    · rw [h, mul_zero, zpow_zero]
      exact one_le_pow₀ (by norm_num)
    · rw [h, mul_one, zpow_natCast,
        show (2:ℝ)^(d*(k₂+1)) = ((2:ℝ)^(k₂+1))^d by rw [mul_comm d (k₂+1), pow_mul]]
      refine pow_le_pow_left₀ (by positivity) ?_ d
      rw [div_le_iff₀ hc₂]
      nlinarith [h2, h3₂, h2k₂]
  have hexp : k₁ + 1 + d*(k₂+1) ≤ d + 1 + (2*k₁ + 2*d*k₂) := by
    have hm : d*(k₂+1) = d*k₂ + d := by ring
    rw [hm]
    nlinarith [Nat.zero_le k₁, Nat.zero_le d, Nat.zero_le k₂, Nat.zero_le (d*k₂)]
  calc (γ / (2:ℝ)^k₁)^p * (γ / (2:ℝ)^k₂)^((d:ℤ) * q)
      ≤ (2:ℝ)^(k₁+1) * (2:ℝ)^(d*(k₂+1)) :=
        mul_le_mul hA hB (by positivity) (by positivity)
    _ = (2:ℝ)^(k₁+1+d*(k₂+1)) := by rw [← pow_add]
    _ ≤ (2:ℝ)^(d+1) * (2:ℝ)^(2*k₁ + 2*d*k₂) := by
        rw [← pow_add]
        exact pow_le_pow_right₀ (by norm_num) hexp

/-- **The per-term bound of the `ℓ¹` mass estimate.** -/
theorem repKf_term_le (N : ℕ) (hN : 1 ≤ N) (d k₁ k₂ i j a' b' : ℕ)
    (ha' : a' ≤ 2) (hb' : b' ≤ 2) (_hd : 1 ≤ d) (c : ℝ) (hc : 0 ≤ c) :
    c * ((Work.KMTPlan.A6.lothN N / (2:ℝ)^k₁)^((a':ℤ)-1))
      * ((Work.KMTPlan.A6.lopsN d N k₂)^((b':ℤ)-1))
      * ((N:ℝ)^(((i:ℤ)-(a':ℤ)) + ((d:ℤ))*((j:ℤ)-(b':ℤ)) - 1))
      ≤ c * (2:ℝ)^(d+1) * (2:ℝ)^(2*k₁+2*d*k₂)
        * ((N:ℝ)^((i:ℤ)-1) * (N:ℝ)^(((d:ℤ))*((j:ℤ)-1)) * (N:ℝ)⁻¹) := by
  have hNpos : (0:ℝ) < (N:ℝ) := by positivity
  have hNne : (N:ℝ) ≠ 0 := ne_of_gt hNpos
  set Λ := Work.KMTPlan.A6.lothN N with hΛ
  set γ : ℝ := Λ / (N:ℝ) with hγ
  have hγ1 : (1/2:ℝ) ≤ γ := by rw [hγ, hΛ]; exact repKf_half_le_lothN_div hN
  have hγ2 : γ ≤ 2 := by rw [hγ, hΛ]; exact repKf_lothN_div_le_two hN
  have hΛeq : Λ = γ * (N:ℝ) := by rw [hγ]; field_simp
  have hΛ₂ : Work.KMTPlan.A6.lopsN d N k₂ = (γ * (N:ℝ) / (2:ℝ)^k₂)^d := by
    rw [Work.KMTPlan.A6.lopsN_eq, ← hΛ, hΛeq]
  have h1 : (Λ / (2:ℝ)^k₁)^((a':ℤ)-1)
      = γ^((a':ℤ)-1) * (N:ℝ)^((a':ℤ)-1) / ((2:ℝ)^k₁)^((a':ℤ)-1) := by
    rw [hΛeq, div_zpow, mul_zpow]
  have h2 : (γ / (2:ℝ)^k₁)^((a':ℤ)-1)
      = γ^((a':ℤ)-1) / ((2:ℝ)^k₁)^((a':ℤ)-1) := by rw [div_zpow]
  have h3 : (Work.KMTPlan.A6.lopsN d N k₂)^((b':ℤ)-1)
      = γ^((d:ℤ)*((b':ℤ)-1)) * (N:ℝ)^((d:ℤ)*((b':ℤ)-1))
        / ((2:ℝ)^k₂)^((d:ℤ)*((b':ℤ)-1)) := by
    rw [hΛ₂,
      show (γ * (N:ℝ) / (2:ℝ)^k₂)^d = (γ * (N:ℝ) / (2:ℝ)^k₂)^((d:ℤ)) by rw [zpow_natCast],
      ← zpow_mul]
    rw [div_zpow, mul_zpow, zpow_mul, zpow_mul]
  have h4 : (γ / (2:ℝ)^k₂)^((d:ℤ)*((b':ℤ)-1))
      = γ^((d:ℤ)*((b':ℤ)-1)) / ((2:ℝ)^k₂)^((d:ℤ)*((b':ℤ)-1)) := by rw [div_zpow]
  have hNcomb : (N:ℝ)^((a':ℤ)-1) * (N:ℝ)^((d:ℤ)*((b':ℤ)-1))
      * (N:ℝ)^(((i:ℤ)-(a':ℤ)) + ((d:ℤ))*((j:ℤ)-(b':ℤ)) - 1)
      = (N:ℝ)^(((i:ℤ)-1) + ((d:ℤ))*((j:ℤ)-1) - 1) := by
    rw [← zpow_add₀ hNne, ← zpow_add₀ hNne]
    congr 1
    ring
  have harith := repKf_arith γ hγ1 hγ2 k₁ k₂ d ((a':ℤ)-1) ((b':ℤ)-1)
    (repKf_int_pred_mem a' ha') (repKf_int_pred_mem b' hb')
  have hNsplit : (N:ℝ)^(((i:ℤ)-1) + ((d:ℤ))*((j:ℤ)-1) - 1)
      = (N:ℝ)^((i:ℤ)-1) * (N:ℝ)^(((d:ℤ))*((j:ℤ)-1)) * (N:ℝ)⁻¹ := by
    rw [zpow_sub₀ hNne, zpow_add₀ hNne, zpow_one, div_eq_mul_inv]
  have key : c * (Λ / (2:ℝ)^k₁)^((a':ℤ)-1) * ((Work.KMTPlan.A6.lopsN d N k₂)^((b':ℤ)-1))
      * (N:ℝ)^(((i:ℤ)-(a':ℤ)) + ((d:ℤ))*((j:ℤ)-(b':ℤ)) - 1)
      = c * ((γ / (2:ℝ)^k₁)^((a':ℤ)-1) * (γ / (2:ℝ)^k₂)^((d:ℤ)*((b':ℤ)-1)))
        * (N:ℝ)^(((i:ℤ)-1) + ((d:ℤ))*((j:ℤ)-1) - 1) := by
    rw [h1, h3, h2, h4]
    rw [show c * (γ^((a':ℤ)-1) * (N:ℝ)^((a':ℤ)-1) / ((2:ℝ)^k₁)^((a':ℤ)-1))
          * (γ^((d:ℤ)*((b':ℤ)-1)) * (N:ℝ)^((d:ℤ)*((b':ℤ)-1))
              / ((2:ℝ)^k₂)^((d:ℤ)*((b':ℤ)-1)))
          * (N:ℝ)^(((i:ℤ)-(a':ℤ)) + ((d:ℤ))*((j:ℤ)-(b':ℤ)) - 1)
        = c * (γ^((a':ℤ)-1) / ((2:ℝ)^k₁)^((a':ℤ)-1)
            * (γ^((d:ℤ)*((b':ℤ)-1)) / ((2:ℝ)^k₂)^((d:ℤ)*((b':ℤ)-1))))
          * ((N:ℝ)^((a':ℤ)-1) * (N:ℝ)^((d:ℤ)*((b':ℤ)-1))
              * (N:ℝ)^(((i:ℤ)-(a':ℤ)) + ((d:ℤ))*((j:ℤ)-(b':ℤ)) - 1)) from by ring]
    rw [hNcomb]
  rw [key]
  calc c * ((γ / (2:ℝ)^k₁)^((a':ℤ)-1) * (γ / (2:ℝ)^k₂)^((d:ℤ)*((b':ℤ)-1)))
        * (N:ℝ)^(((i:ℤ)-1) + ((d:ℤ))*((j:ℤ)-1) - 1)
      ≤ c * ((2:ℝ)^(d+1) * (2:ℝ)^(2*k₁+2*d*k₂))
        * (N:ℝ)^(((i:ℤ)-1) + ((d:ℤ))*((j:ℤ)-1) - 1) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left harith hc) (by positivity)
    _ = c * (2:ℝ)^(d+1) * (2:ℝ)^(2*k₁+2*d*k₂)
        * ((N:ℝ)^((i:ℤ)-1) * (N:ℝ)^(((d:ℤ))*((j:ℤ)-1)) * (N:ℝ)⁻¹) := by
        rw [hNsplit]; ring

/-! ## 9. The `ℓ¹` bound for the symbol `φ_N ⊗ φ̃_N · M₀` -/

theorem repKf_hbd (P : Polynomial ℤ) (hdeg : 2 ≤ P.natDegree) :
    ∃ K A : ℝ, 0 < K ∧ 0 ≤ A ∧
      ∀ (N q k₁ k₂ : ℕ) (α β : Circ), 1 ≤ N → 1 ≤ q → q • α = 0 → q • β = 0 →
      ∀ (i j : ℕ), i ≤ 2 → j ≤ 2 →
        (∫ z : ℝ × ℝ, ‖Work.KMTPlan.A6.dp i j (fun a b => varphiN N k₁ a
            * varphitildeN P.natDegree N k₂ b * M0 P N q α β a b) z.1 z.2‖)
          ≤ K * (q:ℝ) * ((2:ℝ)^k₁ + (2:ℝ)^(P.natDegree*k₂) + 1)^A
              * (2:ℝ)^(2*k₁ + 2*P.natDegree*k₂) / (N:ℝ)
              * ((N:ℝ)^((i:ℤ)-1) * (N:ℝ)^(((P.natDegree:ℤ))*((j:ℤ)-1))) := by
  obtain ⟨C_M, A, hCM, hA, hbox⟩ := repKf_M0_dp_box P hdeg
  obtain ⟨Cφ, Cψ, hCφ, hCψ, hφbd, hψbd⟩ := integral_iteratedDeriv_bumps_le P
  refine ⟨100 * Cφ * Cψ * C_M * (2:ℝ)^((P.natDegree:ℝ) + 1), A, by positivity, hA, ?_⟩
  intro N q k₁ k₂ α β hN hq hα hβ i j hi hj
  have hNpos : (0:ℝ) < (N:ℝ) := by positivity
  have hd1 : 1 ≤ P.natDegree := le_trans (by norm_num) hdeg
  set d := P.natDegree with hd
  set Br : ℝ := (2:ℝ)^k₁ + (2:ℝ)^(d*k₂) + 1 with hBr
  set W : ℝ := (2:ℝ)^(2*k₁ + 2*d*k₂) with hW
  have hK : 100 * Cφ * Cψ * C_M * (2:ℝ)^((P.natDegree:ℝ) + 1)
      = 100 * Cφ * Cψ * C_M * (2:ℝ)^((d:ℝ) + 1) := by rw [hd]
  rw [hK, hBr, hW]
  set σ : ℝ → ℝ → ℂ := fun a b => varphiN N k₁ a * varphitildeN d N k₂ b * M0 P N q α β a b
    with hσ
  have hBrpos : (0:ℝ) < Br := by rw [hBr]; positivity
  have hWpos : (0:ℝ) < W := by rw [hW]; positivity
  have hBrA : (0:ℝ) ≤ Br^A := Real.rpow_nonneg hBrpos.le A
  have hWnn : (0:ℝ) ≤ W := hWpos.le
  have hBrnn : (0:ℝ) ≤ Br := hBrpos.le
  have hσcd : ContDiff ℝ 4 (fun z : ℝ × ℝ => σ z.1 z.2) := by
    rw [hσ]; exact repKf_sym_contDiff P N q k₁ k₂ α β
  have hσcs : HasCompactSupport (fun z : ℝ × ℝ => σ z.1 z.2) := by
    rw [hσ]; exact repKf_sym_hasCompactSupport P N q k₁ k₂ α β
  -- the majorant as a function
  set G : ℝ × ℝ → ℝ := fun z => ∑ b' ∈ Finset.range (j+1), ∑ a' ∈ Finset.range (i+1),
      ((‖((j.choose b' : ℂ) * (i.choose a' : ℂ))‖ * (C_M * Br^A * (q:ℝ)
          * (N:ℝ)^(((i-a'):ℤ) + ((d:ℤ))*((b':ℤ)) - 1)))
        * (‖iteratedDeriv a' (varphiN N k₁) z.1‖
            * ‖iteratedDeriv (j-b') (varphitildeN d N k₂) z.2‖)) with hG
  have hGint : Integrable G := by
    rw [hG]
    refine integrable_finsetSum _ (fun b' hb' => ?_)
    refine integrable_finsetSum _ (fun a' ha' => ?_)
    have ha'2 : a' ≤ 2 := by have := Finset.mem_range.mp ha'; omega
    have hb'j : b' ≤ j := by have := Finset.mem_range.mp hb'; omega
    have hjb' : j - b' ≤ 2 := by omega
    have hf : Integrable (fun x : ℝ => ‖iteratedDeriv a' (varphiN N k₁) x‖) :=
      (integrable_iteratedDeriv_varphiN N k₁ a' ha'2)
    have hg : Integrable (fun y : ℝ => ‖iteratedDeriv (j-b') (varphitildeN d N k₂) y‖) :=
      repKf_integrable_iteratedDeriv_varphitildeN d N k₂ (j-b') hjb'
    exact (hf.mul_prod hg).const_mul _
  have hpt : ∀ z : ℝ × ℝ, ‖Work.KMTPlan.A6.dp i j σ z.1 z.2‖ ≤ G z := by
    intro z
    rw [hG, hσ, repKf_dp_leibniz P N q k₁ k₂ α β i j hi hj z.1 z.2]
    refine (norm_sum_le _ _).trans ?_
    refine Finset.sum_le_sum (fun b' hb' => ?_)
    refine (norm_sum_le _ _).trans ?_
    refine Finset.sum_le_sum (fun a' ha' => ?_)
    have ha'2 : a' ≤ 2 := by have := Finset.mem_range.mp ha'; omega
    have hb'j : b' ≤ j := by have := Finset.mem_range.mp hb'; omega
    have hjb' : j - b' ≤ 2 := by omega
    have hia : i - a' ≤ 2 := by omega
    have hb'2 : b' ≤ 2 := by omega
    have hai : a' ≤ i := by have := Finset.mem_range.mp ha'; omega
    have hpw := repKf_pointwise P hdeg C_M A hCM.le hbox N q k₁ k₂ α β hN hq hα hβ
      (j₁ := i - a') (j₂ := b') (a' := a') (b' := j - b') hia hb'2 z.1 z.2
    rw [← hd] at hpw
    rw [Nat.cast_sub hai] at hpw
    rw [norm_mul, norm_mul, norm_mul]
    have hbp : ‖((j.choose b' : ℂ) * (i.choose a' : ℂ))‖
          * (‖iteratedDeriv a' (varphiN N k₁) z.1‖
            * ‖Work.KMTPlan.A6.dp (i - a') b' (fun a b => M0 P N q α β a b) z.1 z.2‖
            * ‖iteratedDeriv (j - b') (varphitildeN d N k₂) z.2‖)
        ≤ ‖((j.choose b' : ℂ) * (i.choose a' : ℂ))‖
          * ((C_M * ((2:ℝ)^k₁ + (2:ℝ)^(d * k₂) + 1)^A * (q:ℝ)
              * (N:ℝ)^(((i-a'):ℤ) + ((d:ℤ))*((b':ℤ)) - 1))
            * (‖iteratedDeriv a' (varphiN N k₁) z.1‖
                * ‖iteratedDeriv (j - b') (varphitildeN d N k₂) z.2‖)) :=
      mul_le_mul_of_nonneg_left hpw (norm_nonneg _)
    calc ‖((j.choose b' : ℂ) * (i.choose a' : ℂ))‖
            * ‖iteratedDeriv a' (varphiN N k₁) z.1‖
            * ‖Work.KMTPlan.A6.dp (i - a') b' (fun a b => M0 P N q α β a b) z.1 z.2‖
            * ‖iteratedDeriv (j - b') (varphitildeN d N k₂) z.2‖
        = ‖((j.choose b' : ℂ) * (i.choose a' : ℂ))‖
          * (‖iteratedDeriv a' (varphiN N k₁) z.1‖
            * ‖Work.KMTPlan.A6.dp (i - a') b' (fun a b => M0 P N q α β a b) z.1 z.2‖
            * ‖iteratedDeriv (j - b') (varphitildeN d N k₂) z.2‖) := by ring
      _ ≤ ‖((j.choose b' : ℂ) * (i.choose a' : ℂ))‖
          * ((C_M * ((2:ℝ)^k₁ + (2:ℝ)^(d * k₂) + 1)^A * (q:ℝ)
              * (N:ℝ)^(((i-a'):ℤ) + ((d:ℤ))*((b':ℤ)) - 1))
            * (‖iteratedDeriv a' (varphiN N k₁) z.1‖
                * ‖iteratedDeriv (j - b') (varphitildeN d N k₂) z.2‖)) := hbp
      _ = (‖((j.choose b' : ℂ) * (i.choose a' : ℂ))‖ * (C_M * Br^A * (q:ℝ)
              * (N:ℝ)^(((i-a'):ℤ) + ((d:ℤ))*((b':ℤ)) - 1)))
            * (‖iteratedDeriv a' (varphiN N k₁) z.1‖
                * ‖iteratedDeriv (j - b') (varphitildeN d N k₂) z.2‖) := by
          rw [hBr]; ring
  have hLint : Integrable (fun z : ℝ × ℝ => ‖Work.KMTPlan.A6.dp i j σ z.1 z.2‖) :=
    (integrable_dp σ i j (hσcd.of_le (by exact_mod_cast (by omega : i + j ≤ 4))) hσcs).norm
  -- ## the value of the majorant integral
  have hInt1 : ∀ a' b' : ℕ, (∫ z : ℝ × ℝ, ‖iteratedDeriv a' (varphiN N k₁) z.1‖
        * ‖iteratedDeriv b' (varphitildeN d N k₂) z.2‖)
      = (∫ x : ℝ, ‖iteratedDeriv a' (varphiN N k₁) x‖)
        * (∫ y : ℝ, ‖iteratedDeriv b' (varphitildeN d N k₂) y‖) := by
    intro a' b'
    rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
    exact MeasureTheory.integral_prod_mul (fun x : ℝ => ‖iteratedDeriv a' (varphiN N k₁) x‖)
      (fun y : ℝ => ‖iteratedDeriv b' (varphitildeN d N k₂) y‖)
  have hGval : (∫ z : ℝ × ℝ, G z)
      = ∑ b' ∈ Finset.range (j+1), ∑ a' ∈ Finset.range (i+1),
          (‖((j.choose b' : ℂ) * (i.choose a' : ℂ))‖ * (C_M * Br^A * (q:ℝ)
              * (N:ℝ)^(((i-a'):ℤ) + ((d:ℤ))*((b':ℤ)) - 1)))
            * ((∫ x : ℝ, ‖iteratedDeriv a' (varphiN N k₁) x‖)
                * (∫ y : ℝ, ‖iteratedDeriv (j-b') (varphitildeN d N k₂) y‖)) := by
    rw [hG]
    rw [integral_finsetSum _ (fun b' _ => integrable_finsetSum _ (fun a' ha' => by
      have ha'2 : a' ≤ 2 := by have := Finset.mem_range.mp ha'; omega
      have hjb' : j - b' ≤ 2 := le_trans (Nat.sub_le j b') hj
      have hf : Integrable (fun x : ℝ => ‖iteratedDeriv a' (varphiN N k₁) x‖) :=
        (integrable_iteratedDeriv_varphiN N k₁ a' ha'2)
      have hg : Integrable (fun y : ℝ => ‖iteratedDeriv (j-b') (varphitildeN d N k₂) y‖) :=
        repKf_integrable_iteratedDeriv_varphitildeN d N k₂ (j-b') hjb'
      exact (hf.mul_prod hg).const_mul _))]
    refine Finset.sum_congr rfl (fun b' hb' => ?_)
    rw [integral_finsetSum _ (fun a' ha' => by
      have ha'2 : a' ≤ 2 := by have := Finset.mem_range.mp ha'; omega
      have hb'j : b' ≤ j := by have := Finset.mem_range.mp hb'; omega
      have hjb' : j - b' ≤ 2 := by omega
      have hf : Integrable (fun x : ℝ => ‖iteratedDeriv a' (varphiN N k₁) x‖) :=
        (integrable_iteratedDeriv_varphiN N k₁ a' ha'2)
      have hg : Integrable (fun y : ℝ => ‖iteratedDeriv (j-b') (varphitildeN d N k₂) y‖) :=
        repKf_integrable_iteratedDeriv_varphitildeN d N k₂ (j-b') hjb'
      exact (hf.mul_prod hg).const_mul _)]
    refine Finset.sum_congr rfl (fun a' ha' => ?_)
    rw [MeasureTheory.integral_const_mul, hInt1 a' (j-b')]
  -- ## the per-term bound
  have hbinom : ∀ (b' a' : ℕ), b' ≤ j → a' ≤ i →
      ‖((j.choose b' : ℂ) * (i.choose a' : ℂ))‖ ≤ 4 := by
    intro b' a' hbj hai
    rw [norm_mul, Complex.norm_natCast, Complex.norm_natCast]
    have h1 : (j.choose b' : ℝ) ≤ 2 := by
      interval_cases j <;> interval_cases b' <;> norm_num
    have h2 : (i.choose a' : ℝ) ≤ 2 := by
      interval_cases i <;> interval_cases a' <;> norm_num
    nlinarith
  have hterm : ∀ (b' a' : ℕ) (hb' : b' ∈ Finset.range (j+1)) (ha' : a' ∈ Finset.range (i+1)),
      (‖((j.choose b' : ℂ) * (i.choose a' : ℂ))‖ * (C_M * Br^A * (q:ℝ)
          * (N:ℝ)^(((i-a'):ℤ) + ((d:ℤ))*((b':ℤ)) - 1)))
        * ((∫ x : ℝ, ‖iteratedDeriv a' (varphiN N k₁) x‖)
            * (∫ y : ℝ, ‖iteratedDeriv (j-b') (varphitildeN d N k₂) y‖))
      ≤ (100 * Cφ * Cψ * C_M * (2:ℝ)^((d:ℝ) + 1) / 9) * (q:ℝ) * Br^A * W * (N:ℝ)⁻¹
          * ((N:ℝ)^((i:ℤ)-1) * (N:ℝ)^(((d:ℤ))*((j:ℤ)-1))) := by
    intro b' a' hb' ha'
    have hai : a' ≤ i := by have := Finset.mem_range.mp ha'; omega
    have hbj : b' ≤ j := by have := Finset.mem_range.mp hb'; omega
    have ha'2 : a' ≤ 2 := by omega
    have hjb'2 : j - b' ≤ 2 := by omega
    have hφz : (∫ x : ℝ, ‖iteratedDeriv a' (varphiN N k₁) x‖)
        ≤ Cφ * (Work.KMTPlan.A6.lothN N / (2:ℝ)^k₁)^((a':ℤ)-1) :=
      (hφbd N k₁ a' ha'2).trans (le_of_eq (by rw [repKf_rpow_eq_zpow _ a' ha'2]))
    have hψz : (∫ y : ℝ, ‖iteratedDeriv (j-b') (varphitildeN d N k₂) y‖)
        ≤ Cψ * (Work.KMTPlan.A6.lopsN d N k₂)^(((j-b':ℕ):ℤ)-1) := by
      have h := hψbd N k₂ (j-b') hjb'2
      have h2 : Cψ * (Work.KMTPlan.A6.lopsN d N k₂)^(((j-b':ℕ):ℝ)-1)
          = Cψ * (Work.KMTPlan.A6.lopsN d N k₂)^(((j-b':ℕ):ℤ)-1) := by
        rw [repKf_rpow_eq_zpow (Work.KMTPlan.A6.lopsN d N k₂) (j-b') hjb'2]
      rwa [h2] at h
    have hc : (0:ℝ) ≤ ‖((j.choose b' : ℂ) * (i.choose a' : ℂ))‖ * C_M * Br^A * (q:ℝ)
        * Cφ * Cψ := by
      have hqnn : (0:ℝ) ≤ ((q:ℝ)) := Nat.cast_nonneg q
      exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
        (norm_nonneg _) hCM.le) hBrA) hqnn) hCφ.le) hCψ.le
    have hterm1 := repKf_term_le N hN d k₁ k₂ i j a' (j-b') ha'2 hjb'2 hd1
      (‖((j.choose b' : ℂ) * (i.choose a' : ℂ))‖ * C_M * Br^A * (q:ℝ) * Cφ * Cψ) hc
    rw [show ((j:ℤ) - (((j-b':ℕ)):ℤ)) = (b':ℤ) by rw [Nat.cast_sub hbj]; ring] at hterm1
    rw [← hW] at hterm1
    have hstep : (‖((j.choose b' : ℂ) * (i.choose a' : ℂ))‖ * (C_M * Br^A * (q:ℝ)
          * (N:ℝ)^(((i-a'):ℤ) + ((d:ℤ))*((b':ℤ)) - 1)))
        * ((∫ x : ℝ, ‖iteratedDeriv a' (varphiN N k₁) x‖)
            * (∫ y : ℝ, ‖iteratedDeriv (j-b') (varphitildeN d N k₂) y‖))
        ≤ (‖((j.choose b' : ℂ) * (i.choose a' : ℂ))‖ * C_M * Br^A * (q:ℝ) * Cφ * Cψ)
          * (Work.KMTPlan.A6.lothN N / (2:ℝ)^k₁)^((a':ℤ)-1)
          * (Work.KMTPlan.A6.lopsN d N k₂)^(((j-b':ℕ):ℤ)-1)
          * (N:ℝ)^(((i-a'):ℤ) + ((d:ℤ))*((b':ℤ)) - 1) := by
      have h0 : (0:ℝ) ≤ ‖((j.choose b' : ℂ) * (i.choose a' : ℂ))‖
          * (C_M * Br^A * (q:ℝ) * (N:ℝ)^(((i-a'):ℤ) + ((d:ℤ))*((b':ℤ)) - 1)) := by
        positivity
      have h12 : (∫ x : ℝ, ‖iteratedDeriv a' (varphiN N k₁) x‖)
          * (∫ y : ℝ, ‖iteratedDeriv (j-b') (varphitildeN d N k₂) y‖)
          ≤ (Cφ * (Work.KMTPlan.A6.lothN N / (2:ℝ)^k₁)^((a':ℤ)-1))
            * (Cψ * (Work.KMTPlan.A6.lopsN d N k₂)^(((j-b':ℕ):ℤ)-1)) :=
        mul_le_mul hφz hψz (MeasureTheory.integral_nonneg (fun y => norm_nonneg _))
          (mul_nonneg hCφ.le (zpow_nonneg
            (div_nonneg (Work.KMTPlan.A6.lothN_pos N).le (pow_nonneg (by norm_num) k₁)) _))
      calc (‖((j.choose b' : ℂ) * (i.choose a' : ℂ))‖ * (C_M * Br^A * (q:ℝ)
            * (N:ℝ)^(((i-a'):ℤ) + ((d:ℤ))*((b':ℤ)) - 1)))
          * ((∫ x : ℝ, ‖iteratedDeriv a' (varphiN N k₁) x‖)
              * (∫ y : ℝ, ‖iteratedDeriv (j-b') (varphitildeN d N k₂) y‖))
          ≤ (‖((j.choose b' : ℂ) * (i.choose a' : ℂ))‖ * (C_M * Br^A * (q:ℝ)
              * (N:ℝ)^(((i-a'):ℤ) + ((d:ℤ))*((b':ℤ)) - 1)))
            * ((Cφ * (Work.KMTPlan.A6.lothN N / (2:ℝ)^k₁)^((a':ℤ)-1))
              * (Cψ * (Work.KMTPlan.A6.lopsN d N k₂)^(((j-b':ℕ):ℤ)-1))) :=
            mul_le_mul_of_nonneg_left h12 h0
        _ = (‖((j.choose b' : ℂ) * (i.choose a' : ℂ))‖ * C_M * Br^A * (q:ℝ) * Cφ * Cψ)
              * (Work.KMTPlan.A6.lothN N / (2:ℝ)^k₁)^((a':ℤ)-1)
              * (Work.KMTPlan.A6.lopsN d N k₂)^(((j-b':ℕ):ℤ)-1)
              * (N:ℝ)^(((i-a'):ℤ) + ((d:ℤ))*((b':ℤ)) - 1) := by ring
    have hconst : (‖((j.choose b' : ℂ) * (i.choose a' : ℂ))‖ * C_M * Br^A * (q:ℝ)
          * Cφ * Cψ) * (2:ℝ)^(d+1) * W
        ≤ (100 * Cφ * Cψ * C_M * (2:ℝ)^((d:ℝ) + 1) / 9) * (q:ℝ) * Br^A * W := by
      have hb4 := hbinom b' a' hbj hai
      have hp2 : (0:ℝ) < (2:ℝ)^(d+1) := by positivity
      have hp2' : (2:ℝ)^((d:ℝ)+1) = (2:ℝ)^(d+1) := by
        rw [← Real.rpow_natCast (2:ℝ) (d+1)]
        congr 1
        push_cast
        ring
      have hkey : ‖((j.choose b' : ℂ) * (i.choose a' : ℂ))‖ * (2:ℝ)^(d+1)
          ≤ 100 / 9 * (2:ℝ)^(d+1) := by nlinarith [hb4, hp2]
      calc (‖((j.choose b' : ℂ) * (i.choose a' : ℂ))‖ * C_M * Br^A * (q:ℝ) * Cφ * Cψ)
            * (2:ℝ)^(d+1) * W
          = (‖((j.choose b' : ℂ) * (i.choose a' : ℂ))‖ * (2:ℝ)^(d+1))
              * (C_M * Br^A * (q:ℝ) * Cφ * Cψ * W) := by ring
        _ ≤ (100 / 9 * (2:ℝ)^(d+1)) * (C_M * Br^A * (q:ℝ) * Cφ * Cψ * W) :=
            mul_le_mul_of_nonneg_right hkey (by positivity)
        _ = (100 * Cφ * Cψ * C_M * (2:ℝ)^((d:ℝ) + 1) / 9) * (q:ℝ) * Br^A * W := by
            rw [hp2']; ring
    refine (hstep.trans hterm1).trans ?_
    calc (‖((j.choose b' : ℂ) * (i.choose a' : ℂ))‖ * C_M * Br^A * (q:ℝ) * Cφ * Cψ)
          * (2:ℝ)^(d+1) * W * ((N:ℝ)^((i:ℤ)-1) * (N:ℝ)^(((d:ℤ))*((j:ℤ)-1)) * (N:ℝ)⁻¹)
        ≤ (100 * Cφ * Cψ * C_M * (2:ℝ)^((d:ℝ) + 1) / 9) * (q:ℝ) * Br^A * W
            * ((N:ℝ)^((i:ℤ)-1) * (N:ℝ)^(((d:ℤ))*((j:ℤ)-1)) * (N:ℝ)⁻¹) :=
          mul_le_mul_of_nonneg_right hconst (by positivity)
      _ = (100 * Cφ * Cψ * C_M * (2:ℝ)^((d:ℝ) + 1) / 9) * (q:ℝ) * Br^A * W * (N:ℝ)⁻¹
            * ((N:ℝ)^((i:ℤ)-1) * (N:ℝ)^(((d:ℤ))*((j:ℤ)-1))) := by ring
  -- ## the assembly
  have hmono : (∫ z : ℝ × ℝ, ‖Work.KMTPlan.A6.dp i j σ z.1 z.2‖) ≤ ∫ z : ℝ × ℝ, G z :=
    MeasureTheory.integral_mono hLint hGint hpt
  rw [hGval] at hmono
  have hsum : (∑ b' ∈ Finset.range (j+1), ∑ a' ∈ Finset.range (i+1),
        (‖((j.choose b' : ℂ) * (i.choose a' : ℂ))‖ * (C_M * Br^A * (q:ℝ)
            * (N:ℝ)^(((i-a'):ℤ) + ((d:ℤ))*((b':ℤ)) - 1)))
          * ((∫ x : ℝ, ‖iteratedDeriv a' (varphiN N k₁) x‖)
              * (∫ y : ℝ, ‖iteratedDeriv (j-b') (varphitildeN d N k₂) y‖)))
      ≤ (100 * Cφ * Cψ * C_M * (2:ℝ)^((d:ℝ) + 1)) * (q:ℝ) * Br^A * W * (N:ℝ)⁻¹
          * ((N:ℝ)^((i:ℤ)-1) * (N:ℝ)^(((d:ℤ))*((j:ℤ)-1))) := by
    set T : ℝ := (100 * Cφ * Cψ * C_M * (2:ℝ)^((d:ℝ) + 1) / 9) * (q:ℝ) * Br^A * W
      * (N:ℝ)⁻¹ * ((N:ℝ)^((i:ℤ)-1) * (N:ℝ)^(((d:ℤ))*((j:ℤ)-1))) with hT
    have h1 : (∑ b' ∈ Finset.range (j+1), ∑ a' ∈ Finset.range (i+1),
          (‖((j.choose b' : ℂ) * (i.choose a' : ℂ))‖ * (C_M * Br^A * (q:ℝ)
              * (N:ℝ)^(((i-a'):ℤ) + ((d:ℤ))*((b':ℤ)) - 1)))
            * ((∫ x : ℝ, ‖iteratedDeriv a' (varphiN N k₁) x‖)
                * (∫ y : ℝ, ‖iteratedDeriv (j-b') (varphitildeN d N k₂) y‖)))
        ≤ ∑ b' ∈ Finset.range (j+1), ∑ a' ∈ Finset.range (i+1), T :=
      Finset.sum_le_sum (fun b' hb' => Finset.sum_le_sum (fun a' ha' => by
        rw [hT]; exact hterm b' a' hb' ha'))
    have h2 : (∑ b' ∈ Finset.range (j+1), ∑ a' ∈ Finset.range (i+1), T)
        = ((j+1 : ℕ) : ℝ) * ((i+1 : ℕ) : ℝ) * T := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring
    have h3 : ((j+1 : ℕ) : ℝ) * ((i+1 : ℕ) : ℝ) * T ≤ 9 * T := by
      have h9 : ((j+1 : ℕ) : ℝ) * ((i+1 : ℕ) : ℝ) ≤ 9 := by
        have h1' : ((j+1 : ℕ) : ℝ) ≤ 3 := by exact_mod_cast (by omega : j + 1 ≤ 3)
        have h2' : ((i+1 : ℕ) : ℝ) ≤ 3 := by exact_mod_cast (by omega : i + 1 ≤ 3)
        nlinarith
      have hTnn : (0:ℝ) ≤ T := by
        rw [hT]
        have hqnn : (0:ℝ) ≤ ((q:ℝ)) := Nat.cast_nonneg q
        have h2 : (0:ℝ) ≤ (N:ℝ)⁻¹ := by positivity
        have h3 : (0:ℝ) ≤ (N:ℝ)^((i:ℤ)-1) * (N:ℝ)^(((d:ℤ))*((j:ℤ)-1)) := by positivity
        exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
          (div_nonneg (by positivity) (by norm_num)) hqnn) hBrA) hWnn) h2) h3
      nlinarith
    refine h1.trans ?_
    rw [h2]
    calc ((j+1 : ℕ) : ℝ) * ((i+1 : ℕ) : ℝ) * T ≤ 9 * T := h3
      _ = (100 * Cφ * Cψ * C_M * (2:ℝ)^((d:ℝ) + 1)) * (q:ℝ) * Br^A * W * (N:ℝ)⁻¹
            * ((N:ℝ)^((i:ℤ)-1) * (N:ℝ)^(((d:ℤ))*((j:ℤ)-1))) := by rw [hT]; ring
  refine hmono.trans ?_
  rw [div_eq_mul_inv]
  exact hsum

set_option maxHeartbeats 8000000

/-! ## 10. The real-power dictionaries for the two radii -/

theorem repKf_inv_rpow (N : ℕ) (hN : 1 ≤ N) (i : ℕ) :
    ((N:ℝ)⁻¹)^((1:ℝ)-(i:ℝ)) = (N:ℝ)^((i:ℤ)-1) := by
  rw [Real.inv_rpow (by positivity),
    ← Real.rpow_neg (by positivity : (0:ℝ) ≤ (N:ℝ))]
  rw [show -((1:ℝ)-(i:ℝ)) = (((i:ℤ)-1 : ℤ) : ℝ) by push_cast; ring,
    ← Real.rpow_intCast (N:ℝ) ((i:ℤ)-1)]

theorem repKf_inv_rpow_pow (N d : ℕ) (hN : 1 ≤ N) (j : ℕ) :
    (((N:ℝ)^d)⁻¹)^((1:ℝ)-(j:ℝ)) = (N:ℝ)^((d:ℤ)*((j:ℤ)-1)) := by
  rw [show (1:ℝ)-(j:ℝ) = (((1:ℤ)-(j:ℤ) : ℤ) : ℝ) by push_cast; ring, Real.rpow_intCast]
  rw [show ((1:ℤ)-(j:ℤ)) = -((j:ℤ)-1) by ring, inv_zpow, zpow_neg, inv_inv]
  rw [show (N:ℝ)^d = (N:ℝ)^((d:ℤ)) by rw [zpow_natCast], ← zpow_mul]

/-! ## 11. The integration-by-parts identity -/

theorem repKf_ibp (P : Polynomial ℤ) (N q k₁ k₂ : ℕ) (α β : Circ)
    (i j : ℕ) (hi : i ≤ 2) (hj : j ≤ 2) (p₁ p₂ : ℤ) :
    Work.KMTAreas.A7.kf (Work.KMTPlan.A6.dp i j (fun a b => varphiN N k₁ a
        * varphitildeN P.natDegree N k₂ b * M0 P N q α β a b)) p₁ p₂
      = (2 * (Real.pi : ℂ) * Complex.I * (p₁ : ℂ)) ^ i
        * (2 * (Real.pi : ℂ) * Complex.I * (p₂ : ℂ)) ^ j
        * Work.KMTAreas.A7.kf (fun a b => varphiN N k₁ a * varphitildeN P.natDegree N k₂ b
            * M0 P N q α β a b) p₁ p₂ := by
  have hsm : ContDiff ℝ 4 (fun p : ℝ × ℝ => varphiN N k₁ p.1
      * varphitildeN P.natDegree N k₂ p.2 * M0 P N q α β p.1 p.2) :=
    repKf_sym_contDiff P N q k₁ k₂ α β
  have hc : HasCompactSupport (fun p : ℝ × ℝ => varphiN N k₁ p.1
      * varphitildeN P.natDegree N k₂ p.2 * M0 P N q α β p.1 p.2) :=
    repKf_sym_hasCompactSupport P N q k₁ k₂ α β
  exact Work.KMTAreas.A7.kf_dp
    (fun a b => varphiN N k₁ a * varphitildeN P.natDegree N k₂ b * M0 P N q α β a b)
    i j p₁ p₂
    (by simpa [Work.KMTPlan.A6.dp, Work.KMTPlan.A6.dp1, Work.KMTPlan.A6.dp2, iteratedDeriv_zero]
      using (integrable_dp (fun a b => varphiN N k₁ a * varphitildeN P.natDegree N k₂ b
        * M0 P N q α β a b) 0 0 (hsm.of_le (by norm_num)) hc))
    (by
      have h0j : ContDiff ℝ (↑(0:ℕ) + ↑j) (fun p : ℝ × ℝ => varphiN N k₁ p.1
          * varphitildeN P.natDegree N k₂ p.2 * M0 P N q α β p.1 p.2) :=
        hsm.of_le (by exact_mod_cast (by omega : 0 + j ≤ 4))
      simpa [Work.KMTPlan.A6.dp, Work.KMTPlan.A6.dp1, Work.KMTPlan.A6.dp2, iteratedDeriv_zero]
        using (integrable_dp (fun a b => varphiN N k₁ a * varphitildeN P.natDegree N k₂ b
          * M0 P N q α β a b) 0 j h0j hc))
    (by
      have hij : ContDiff ℝ (↑i + ↑j) (fun p : ℝ × ℝ => varphiN N k₁ p.1
          * varphitildeN P.natDegree N k₂ p.2 * M0 P N q α β p.1 p.2) :=
        hsm.of_le (by exact_mod_cast (by omega : i + j ≤ 4))
      exact integrable_dp (fun a b => varphiN N k₁ a * varphitildeN P.natDegree N k₂ b
        * M0 P N q α β a b) i j hij hc)
    (fun x => Work.KMTPlan.A6.cdp_fiber₂
      (fun a b => varphiN N k₁ a * varphitildeN P.natDegree N k₂ b * M0 P N q α β a b) j
      (hsm.of_le (by exact_mod_cast (by omega : j ≤ 4))) x)
    (fun x => Work.KMTAreas.A7.compSupp_fiber_snd
      (fun p : ℝ × ℝ => varphiN N k₁ p.1 * varphitildeN P.natDegree N k₂ p.2
        * M0 P N q α β p.1 p.2) hc x)
    (fun y => Work.KMTPlan.A6.cdp_fiber₁
      (Work.KMTPlan.A6.dp2 j
        (fun a b => varphiN N k₁ a * varphitildeN P.natDegree N k₂ b * M0 P N q α β a b)) i
      (Work.KMTPlan.A6.cdp_contDiff_dp2_iter
        (fun a b => varphiN N k₁ a * varphitildeN P.natDegree N k₂ b * M0 P N q α β a b)
        i j (hsm.of_le (by exact_mod_cast (by omega : i + j ≤ 4)))) y)
    (fun y => Work.KMTAreas.A7.compSupp_iteratedDeriv_fiber
      (fun p : ℝ × ℝ => varphiN N k₁ p.1 * varphitildeN P.natDegree N k₂ p.2
        * M0 P N q α β p.1 p.2) hc j y)

/-! ## 12. The main theorem -/

theorem RepFibreKfMass (P : Polynomial ℤ) (hdeg : 2 ≤ P.natDegree) :
    ∃ C A : ℝ, 0 < C ∧ 0 ≤ A ∧
      ∀ (N q k₁ k₂ : ℕ) (α β : Work.Analysis.IonescuWainger.Circle),
        1 ≤ N → 1 ≤ q → q • α = 0 → q • β = 0 →
        k₁ ≤ (Work.Analysis.EndVar.logN N).toNat →
        k₂ ≤ (Work.Analysis.EndVar.logN N).toNat →
        (∑' p : ℤ × ℤ, ‖∫ z : ℝ × ℝ,
            (Work.KMTAreas.A7.varphiN N k₁ z.1 * Work.KMTAreas.A7.varphitildeN P.natDegree N k₂ z.2
              * Work.KMTAreas.A7.M0 P N q α β z.1 z.2)
              * Work.KMTAreas.A7.ee (-((p.1 : ℝ) * z.1 + (p.2 : ℝ) * z.2))‖)
          ≤ C * (q : ℝ) * ((2 : ℝ) ^ k₁ + (2 : ℝ) ^ (P.natDegree * k₂) + 1) ^ A
              * (2 : ℝ) ^ (2 * k₁ + 2 * P.natDegree * k₂) / (N : ℝ) := by
  obtain ⟨K, A, hK, hA, hbd⟩ := repKf_hbd P hdeg
  refine ⟨100 * K, A, by positivity, hA, ?_⟩
  intro N q k₁ k₂ α β hN hq hα hβ hk₁ hk₂
  have hNpos : (0:ℝ) < (N:ℝ) := by positivity
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hr₁pos : (0:ℝ) < (N:ℝ)⁻¹ := by positivity
  have hr₁le : (N:ℝ)⁻¹ ≤ 1 := by rw [inv_le_one₀ hNpos]; exact hN1
  have hr₂pos : (0:ℝ) < ((N:ℝ)^P.natDegree)⁻¹ := by positivity
  have hr₂le : ((N:ℝ)^P.natDegree)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ (by positivity)]; exact one_le_pow₀ hN1
  have hC : (0:ℝ) ≤ K * (q:ℝ) * ((2:ℝ)^k₁ + (2:ℝ)^(P.natDegree*k₂) + 1)^A
      * (2:ℝ)^(2*k₁ + 2*P.natDegree*k₂) / (N:ℝ) := by
    have h1 : (0:ℝ) ≤ (2:ℝ)^k₁ + (2:ℝ)^(P.natDegree*k₂) + 1 := by positivity
    have h2 : (0:ℝ) ≤ (2:ℝ)^(2*k₁ + 2*P.natDegree*k₂) := by positivity
    have h3 : (0:ℝ) ≤ (q:ℝ) := Nat.cast_nonneg q
    have h4 : (0:ℝ) ≤ (N:ℝ)⁻¹ := by positivity
    have h5 : (0:ℝ) ≤ ((2:ℝ)^k₁ + (2:ℝ)^(P.natDegree*k₂) + 1)^A :=
      Real.rpow_nonneg h1 A
    rw [div_eq_mul_inv]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hK.le h3) h5) h2) h4
  have hpt : ∀ p₁ p₂ : ℤ, ‖Work.KMTAreas.A7.kf (fun a b => varphiN N k₁ a
        * varphitildeN P.natDegree N k₂ b * M0 P N q α β a b) p₁ p₂‖
      ≤ (K * (q:ℝ) * ((2:ℝ)^k₁ + (2:ℝ)^(P.natDegree*k₂) + 1)^A
          * (2:ℝ)^(2*k₁+2*P.natDegree*k₂) / (N:ℝ))
        * (Work.KMTPlan.A6.wt ((N:ℝ)⁻¹) p₁
            * Work.KMTPlan.A6.wt (((N:ℝ)^P.natDegree)⁻¹) p₂) := by
    intro p₁ p₂
    refine kf_le (fun a b => varphiN N k₁ a * varphitildeN P.natDegree N k₂ b
        * M0 P N q α β a b)
      (K * (q:ℝ) * ((2:ℝ)^k₁ + (2:ℝ)^(P.natDegree*k₂) + 1)^A
        * (2:ℝ)^(2*k₁+2*P.natDegree*k₂) / (N:ℝ)) ((N:ℝ)⁻¹) (((N:ℝ)^P.natDegree)⁻¹)
      ?_ ?_ p₁ p₂
    · intro i j hi hj q₁ q₂
      exact repKf_ibp P N q k₁ k₂ α β i j hi hj q₁ q₂
    · intro i j hi hj
      have h := hbd N q k₁ k₂ α β hN hq hα hβ i j hi hj
      rw [repKf_inv_rpow N hN i, repKf_inv_rpow_pow N P.natDegree hN j]
      exact h.trans (le_of_eq (by ring))
  have htsum := hiCrudeTsum (fun p : ℤ × ℤ => Work.KMTAreas.A7.kf (fun a b => varphiN N k₁ a
      * varphitildeN P.natDegree N k₂ b * M0 P N q α β a b) p.1 p.2)
    (K * (q:ℝ) * ((2:ℝ)^k₁ + (2:ℝ)^(P.natDegree*k₂) + 1)^A
      * (2:ℝ)^(2*k₁+2*P.natDegree*k₂) / (N:ℝ)) ((N:ℝ)⁻¹) (((N:ℝ)^P.natDegree)⁻¹)
    hC hr₁pos hr₁le hr₂pos hr₂le (fun p => by
      rw [mul_assoc]; exact hpt p.1 p.2)
  have hLHS : (∑' p : ℤ × ℤ, ‖∫ z : ℝ × ℝ,
      (Work.KMTAreas.A7.varphiN N k₁ z.1 * Work.KMTAreas.A7.varphitildeN P.natDegree N k₂ z.2
        * Work.KMTAreas.A7.M0 P N q α β z.1 z.2)
        * Work.KMTAreas.A7.ee (-((p.1 : ℝ) * z.1 + (p.2 : ℝ) * z.2))‖)
      = ∑' p : ℤ × ℤ, ‖Work.KMTAreas.A7.kf (fun a b => varphiN N k₁ a
          * varphitildeN P.natDegree N k₂ b * M0 P N q α β a b) p.1 p.2‖ :=
    tsum_congr (fun p => rfl)
  rw [hLHS]
  refine htsum.trans (le_of_eq ?_)
  ring

end

end Work.KMTAreas.A7
