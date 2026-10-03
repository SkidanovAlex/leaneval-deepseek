import Mathlib
import Submission.Work.FIPlan.Interface
import Submission.Work.FIArea4.Assembly
import Submission.Work.FIArea4.polya_vinogradov
import Mathlib.Data.Nat.Totient
import Submission.Work.FIArea4.sum_coprime_mul_eq
import Submission.Commons.NumberTheory.Nat.card_divisors_le_two_pow_card_primeFactors
import Submission.Work.FIArea4.JacobiChar
import Submission.Work.FIArea4.pv_dirichlet
import Submission.Work.FIArea4.L14.transfer
import Submission.Work.FIArea4.L14.F_bounds
import Submission.Work.FIArea4.L14.A_sieve_bound
import Submission.Work.FIArea4.L14.reduce_to_T
import Submission.Work.FIArea4.L14.T_to_U
import Submission.Work.FIArea4.jacobiChar_isPrimitive
import Submission.Work.FIArea4.SqfreeKernel
import Submission.Work.FIArea4.sqfree_kernel
import Submission.Commons.NumberTheory.DivisorBound.card_divisors_le_rpow

set_option maxHeartbeats 4000000

namespace Work.FIArea4

open scoped BigOperators
open Finset

noncomputable section

def radE (e : ℕ) : ℕ := ∏ p ∈ (Work.FIPlan.oddPart e).primeFactors, p

def jsum (q T : ℕ) : ℝ := ∑ m ∈ Finset.Icc 1 T, (jacobiSym (m : ℤ) q : ℝ)

def Usum (D R' : ℕ) : ℝ :=
  ∑ e ∈ Finset.Icc 1 D,
    ∑ b1 ∈ Finset.Icc 1 D,
    ∑ b2 ∈ (Finset.Icc 1 D).filter
          (fun b2 => Nat.sqrt (Work.FIPlan.oddPart b1 * Work.FIPlan.oddPart b2) ^ 2
                      ≠ Work.FIPlan.oddPart b1 * Work.FIPlan.oddPart b2),
      (((e * b1 * b2 : ℕ) : ℝ)⁻¹) *
          (jsum (Work.FIPlan.oddPart (e * b1) * Work.FIPlan.oddPart (e * b2)) R')^2



lemma radE_dvd (e : ℕ) : radE e ∣ e := by
  have h1 : radE e ∣ Work.FIPlan.oddPart e := by
    rw [radE]; exact Nat.prod_primeFactors_dvd _
  exact h1.trans (Work.FIArea4.oddPart_dvd e)

lemma radE_card_le (e : ℕ) (he : 1 ≤ e) : ((radE e).divisors.card : ℝ) ≤ e.divisors.card := by
  have he0 : e ≠ 0 := by omega
  have hsub : (radE e).divisors ⊆ e.divisors := by
    intro d hd
    rw [Nat.mem_divisors] at hd ⊢
    exact ⟨hd.1.trans (radE_dvd e), he0⟩
  exact_mod_cast Finset.card_le_card hsub

lemma log_le_log_of_nonneg {x y : ℝ} (hx : 0 ≤ x) (hy : 1 ≤ y) (hxy : x ≤ y) :
    Real.log x ≤ Real.log y := by
  rcases eq_or_lt_of_le hx with h | h
  · rw [← h, Real.log_zero]; exact Real.log_nonneg hy
  · exact Real.log_le_log h hxy

/-- `F_T(Q) ≤ Q · (2 C T^{3/2} (log(D²T+2)+1)²)` for `1 ≤ Q ≤ D²`. -/
lemma hMbound_aux (D T Q : ℕ) (Cfb : ℝ) (hCfb : 0 ≤ Cfb)
    (hFball : ∀ (Q R : ℕ), 1 ≤ R →
      (∑ q ∈ (Finset.Icc 1 Q).filter (fun q => Odd q ∧ Nat.sqrt q ^ 2 ≠ q),
          (∑ r ∈ Finset.Icc 1 R, (jacobiSym (r : ℤ) q : ℝ)) ^ 2)
        ≤ Cfb * (Q : ℝ) ^ 2 * (Real.log Q + 1) ^ 2 ∧
      (∑ q ∈ (Finset.Icc 1 Q).filter (fun q => Odd q ∧ Nat.sqrt q ^ 2 ≠ q),
          (∑ r ∈ Finset.Icc 1 R, (jacobiSym (r : ℤ) q : ℝ)) ^ 2)
        ≤ Cfb * ((Q : ℝ) * R + (R : ℝ) ^ 3) * (Real.log (Q * R + 2) + 1) ^ 2)
    (hT : 1 ≤ T) (hQ1 : 1 ≤ Q) (hQ : (Q : ℝ) ≤ (D : ℝ) * D) :
    (∑ q ∈ (Finset.Icc 1 Q).filter (fun q => Odd q ∧ Nat.sqrt q ^ 2 ≠ q), (jsum q T)^2)
      ≤ (Q : ℝ) * (2 * Cfb * (T : ℝ) ^ ((3:ℝ)/2)
          * (Real.log ((D : ℝ) * D * (T : ℝ) + 2) + 1) ^ 2) := by
  set L : ℝ := (Real.log ((D : ℝ) * D * (T : ℝ) + 2) + 1) ^ 2 with hLdef
  have hL0 : 0 ≤ L := by rw [hLdef]; positivity
  have hT1 : (1:ℝ) ≤ (T:ℝ) := by exact_mod_cast hT
  have hT0 : (0:ℝ) ≤ (T:ℝ) := by linarith
  have hQ0 : 0 ≤ (Q:ℝ) := by positivity
  have hTpos : (0:ℝ) < (T:ℝ) := by linarith
  have hlogpos : (1:ℝ) ≤ (D:ℝ) * D * (T:ℝ) + 2 := by nlinarith [sq_nonneg (D:ℝ), hT1]
  have hRle : (T:ℝ) ≤ (T:ℝ)^((3:ℝ)/2) := by
    have h := Real.rpow_le_rpow_of_exponent_le hT1 (by norm_num : (1:ℝ) ≤ (3:ℝ)/2)
    simpa [Real.rpow_one] using h
  have hsq : (T:ℝ)^((3:ℝ)/2) * (T:ℝ)^((3:ℝ)/2) = (T:ℝ)^3 := by
    rw [← Real.rpow_add hTpos]; norm_num
  have hs0 : (0:ℝ) ≤ (T:ℝ)^((3:ℝ)/2) := Real.rpow_nonneg hT0 _
  have hcond1 : (Real.log (Q:ℝ) + 1)^2 ≤ L := by
    rw [hLdef]; apply pow_le_pow_left₀ ?_
    · have h1 : (Q:ℝ) ≤ (D:ℝ) * D * (T:ℝ) + 2 := by nlinarith [hQ, hT1]
      have h2 := log_le_log_of_nonneg hQ0 hlogpos h1
      linarith
    · have := Real.log_nonneg (by exact_mod_cast hQ1 : (1:ℝ) ≤ (Q:ℝ)); linarith
  have hcond2 : (Real.log ((Q:ℝ) * (T:ℝ) + 2) + 1)^2 ≤ L := by
    rw [hLdef]; apply pow_le_pow_left₀ ?_
    · have h1 : (Q:ℝ) * (T:ℝ) + 2 ≤ (D:ℝ) * D * (T:ℝ) + 2 := by nlinarith [hQ, hT1]
      have h2 := log_le_log_of_nonneg (by positivity) hlogpos h1
      linarith
    · have h1 : (1:ℝ) ≤ (Q:ℝ) * (T:ℝ) + 2 := by nlinarith [hQ0, hT0]
      have := Real.log_nonneg h1; linarith
  have hL1 : (∑ q ∈ (Finset.Icc 1 Q).filter (fun q => Odd q ∧ Nat.sqrt q ^ 2 ≠ q), (jsum q T)^2)
      ≤ Cfb * (Q:ℝ)^2 * L :=
    (hFball Q T hT).1.trans (mul_le_mul_of_nonneg_left hcond1 (mul_nonneg hCfb (sq_nonneg _)))
  have hL2 : (∑ q ∈ (Finset.Icc 1 Q).filter (fun q => Odd q ∧ Nat.sqrt q ^ 2 ≠ q), (jsum q T)^2)
      ≤ Cfb * ((Q:ℝ)*(T:ℝ) + (T:ℝ)^3) * L :=
    (hFball Q T hT).2.trans (mul_le_mul_of_nonneg_left hcond2
      (mul_nonneg hCfb (add_nonneg (mul_nonneg hQ0 hT0) (pow_nonneg hT0 3))))
  by_cases hcase : (Q:ℝ) ≤ (T:ℝ)^((3:ℝ)/2)
  · refine hL1.trans ?_
    have hq2 : (Q:ℝ)^2 ≤ (Q:ℝ) * (T:ℝ)^((3:ℝ)/2) := by nlinarith [hcase, hQ0, hs0]
    calc Cfb * (Q:ℝ)^2 * L
        ≤ Cfb * ((Q:ℝ) * (T:ℝ)^((3:ℝ)/2)) * L :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq2 hCfb) hL0
      _ ≤ (Q:ℝ) * (2 * Cfb * (T:ℝ)^((3:ℝ)/2) * L) := by
          nlinarith [mul_nonneg (mul_nonneg hCfb (mul_nonneg hQ0 hs0)) hL0]
  · push_neg at hcase
    refine hL2.trans ?_
    have h3 : (T:ℝ)^3 ≤ (Q:ℝ) * (T:ℝ)^((3:ℝ)/2) := by nlinarith [hcase, hsq, hs0]
    have h2 : (Q:ℝ) * (T:ℝ) ≤ (Q:ℝ) * (T:ℝ)^((3:ℝ)/2) :=
      mul_le_mul_of_nonneg_left hRle hQ0
    have hmid : Cfb * ((Q:ℝ)*(T:ℝ) + (T:ℝ)^3) * L
        ≤ Cfb * (2 * ((Q:ℝ) * (T:ℝ)^((3:ℝ)/2))) * L := by
      apply mul_le_mul_of_nonneg_right _ hL0
      apply mul_le_mul_of_nonneg_left _ hCfb
      nlinarith [h2, h3]
    calc Cfb * ((Q:ℝ)*(T:ℝ) + (T:ℝ)^3) * L
        ≤ Cfb * (2 * ((Q:ℝ) * (T:ℝ)^((3:ℝ)/2))) * L := hmid
      _ = (Q:ℝ) * (2 * Cfb * (T:ℝ)^((3:ℝ)/2) * L) := by ring

theorem U_bound (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D R' : ℕ), 1 ≤ D →
      Usum D R' ≤ C * (D:ℝ)^(5*δ) * (R':ℝ)^((3:ℝ)/2)
          * (Real.log ((D:ℝ)^2*(R':ℝ)+2)+1)^2 := by
  obtain ⟨Ctr, hCtr, htr⟩ := L14.transfer δ hδ
  obtain ⟨Cfb, hCfb, hFball⟩ := L14.F_bounds
  obtain ⟨Cdiv, hCdiv, hdiv⟩ := Commons.NumberTheory.DivisorBound.card_divisors_le_rpow δ hδ
  have hlogle : ∃ Clog : ℝ, 0 < Clog ∧ ∀ D : ℕ, 1 ≤ D → (1 + Real.log (D:ℝ)) ≤ Clog * (D:ℝ)^δ := by
    refine ⟨1 + 1/δ, by positivity, ?_⟩
    intro D hD
    have hD0 : (0:ℝ) < (D:ℝ) := by exact_mod_cast (by omega : 0 < D)
    have hlog := Real.log_le_rpow_div hD0.le hδ
    have hDd : (1:ℝ) ≤ (D:ℝ)^δ := Real.one_le_rpow (by exact_mod_cast hD) hδ.le
    have h3 : (1:ℝ) + Real.log (D:ℝ) ≤ 1 + (D:ℝ)^δ/δ := by linarith
    have h4 : (1:ℝ) + (D:ℝ)^δ/δ ≤ (D:ℝ)^δ + (D:ℝ)^δ/δ := by linarith
    have h5 : (D:ℝ)^δ + (D:ℝ)^δ/δ = (1 + 1/δ) * (D:ℝ)^δ := by ring
    linarith
  obtain ⟨Clog, hClog, hlogb⟩ := hlogle
  refine ⟨2 * Ctr * Cfb * Cdiv^2 * Clog + 1, by positivity, ?_⟩
  intro D R' hD
  have hDpos : (0:ℝ) < (D:ℝ) := by exact_mod_cast (by omega : 0 < D)
  let Mt : ℕ → ℝ := fun T => 2 * Cfb * (T:ℝ)^((3:ℝ)/2) * (Real.log ((D:ℝ)*D*(T:ℝ)+2)+1)^2
  have hMt_nonneg : ∀ T, 0 ≤ Mt T := fun T => by simp only [Mt]; positivity
  have hMt_mono : ∀ T T' : ℕ, T ≤ T' → Mt T ≤ Mt T' := by
    intro T T' hle
    have h1 : (T:ℝ) ≤ (T':ℝ) := by exact_mod_cast hle
    have hTnn : (0:ℝ) ≤ (T:ℝ) := Nat.cast_nonneg T
    have h2 : (0:ℝ) ≤ (T':ℝ) := by positivity
    have h3 : (T:ℝ)^((3:ℝ)/2) ≤ (T':ℝ)^((3:ℝ)/2) :=
      Real.rpow_le_rpow (by positivity) h1 (by norm_num)
    have hL : (0:ℝ) ≤ Real.log ((D:ℝ)*D*(T:ℝ)+2) + 1 := by
      have : (1:ℝ) ≤ (D:ℝ)*D*(T:ℝ)+2 := by nlinarith [hDpos, hTnn]
      have := Real.log_nonneg this; linarith
    have h4 : Real.log ((D:ℝ)*D*(T:ℝ)+2) ≤ Real.log ((D:ℝ)*D*(T':ℝ)+2) := by
      apply Real.log_le_log (by nlinarith [hDpos, hTnn])
      nlinarith [h1]
    have h4' : (Real.log ((D:ℝ)*D*(T:ℝ)+2) + 1)^2 ≤ (Real.log ((D:ℝ)*D*(T':ℝ)+2) + 1)^2 :=
      pow_le_pow_left₀ hL (by linarith) 2
    have h3' : (0:ℝ) ≤ (T':ℝ)^((3:ℝ)/2) := Real.rpow_nonneg h2 _
    simp only [Mt]
    calc 2 * Cfb * (T:ℝ)^((3:ℝ)/2) * (Real.log ((D:ℝ)*D*(T:ℝ)+2)+1)^2
        ≤ 2 * Cfb * (T':ℝ)^((3:ℝ)/2) * (Real.log ((D:ℝ)*D*(T:ℝ)+2)+1)^2 := by
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
          exact mul_le_mul_of_nonneg_left h3 (by positivity)
      _ ≤ 2 * Cfb * (T':ℝ)^((3:ℝ)/2) * (Real.log ((D:ℝ)*D*(T':ℝ)+2)+1)^2 := by
          apply mul_le_mul_of_nonneg_left h4'
          positivity
  have htransf : ∀ T : ℕ, (∑ b1 ∈ Finset.Icc 1 D,
        ∑ b2 ∈ (Finset.Icc 1 D).filter (fun b2 => Nat.sqrt (Work.FIPlan.oddPart b1 * Work.FIPlan.oddPart b2) ^ 2 ≠ Work.FIPlan.oddPart b1 * Work.FIPlan.oddPart b2),
          (((b1 * b2 : ℕ) : ℝ)⁻¹) * (jsum (Work.FIPlan.oddPart b1 * Work.FIPlan.oddPart b2) T)^2)
        ≤ Ctr * (D:ℝ)^(2*δ) * Mt T := by
    intro T
    refine htr D (Mt T) (fun q => (jsum q T)^2) hD (hMt_nonneg T) (fun q => sq_nonneg _) ?_
    intro Q hQ
    rcases Nat.eq_zero_or_pos Q with hQ0 | hQpos
    · subst hQ0; simp
    · rcases Nat.eq_zero_or_pos T with hT0 | hTpos
      · subst hT0
        have h0 : ∀ q, (jsum q 0)^2 = 0 := fun q => by simp [jsum]
        have hMt0 : Mt 0 = 0 := by
          simp only [Mt]; push_cast
          rw [Real.zero_rpow (by norm_num : ((3:ℝ)/2) ≠ 0)]; ring
        rw [Finset.sum_congr rfl (fun q _ => h0 q), hMt0]; simp
      · have hQle : (Q:ℝ) ≤ (D:ℝ)*D := by
          have h' : Q ≤ D*D := hQ
          exact_mod_cast h'
        exact hMbound_aux D T Q Cfb hCfb.le hFball hTpos hQpos hQle
  have hharm : (∑ e ∈ Finset.Icc 1 D, ((e:ℝ))⁻¹) ≤ 1 + Real.log (D:ℝ) := by
    have h := harmonic_le_one_add_log D
    simpa [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] using h
  have hcard : ∀ e : ℕ, 1 ≤ e → ((radE e).divisors.card : ℝ) ≤ e.divisors.card :=
    fun e he => radE_card_le e he
  have hUsum : Usum D R' = ∑ e ∈ Finset.Icc 1 D, (e:ℝ)⁻¹ * (∑ b1 ∈ Finset.Icc 1 D,
      ∑ b2 ∈ (Finset.Icc 1 D).filter (fun b2 => Nat.sqrt (Work.FIPlan.oddPart b1 * Work.FIPlan.oddPart b2) ^ 2 ≠ Work.FIPlan.oddPart b1 * Work.FIPlan.oddPart b2),
        ((b1*b2:ℕ):ℝ)⁻¹ * (jsum (Work.FIPlan.oddPart (e*b1) * Work.FIPlan.oddPart (e*b2)) R')^2) := by
    simp only [Usum]
    apply Finset.sum_congr rfl; intro e _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro b1 _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro b2 _
    rw [show (((e*b1*b2:ℕ):ℝ)⁻¹) = (e:ℝ)⁻¹ * ((b1*b2:ℕ):ℝ)⁻¹ by
      push_cast; simp only [mul_inv]; ring]
    ring
  have hs1 : (∑ e ∈ Finset.Icc 1 D, (e:ℝ)⁻¹ * (∑ b1 ∈ Finset.Icc 1 D,
        ∑ b2 ∈ (Finset.Icc 1 D).filter (fun b2 => Nat.sqrt (Work.FIPlan.oddPart b1 * Work.FIPlan.oddPart b2) ^ 2 ≠ Work.FIPlan.oddPart b1 * Work.FIPlan.oddPart b2),
          ((b1*b2:ℕ):ℝ)⁻¹ * (jsum (Work.FIPlan.oddPart (e*b1) * Work.FIPlan.oddPart (e*b2)) R')^2))
      ≤ ∑ e ∈ Finset.Icc 1 D, (e:ℝ)⁻¹ * (∑ b1 ∈ Finset.Icc 1 D,
        ∑ b2 ∈ (Finset.Icc 1 D).filter (fun b2 => Nat.sqrt (Work.FIPlan.oddPart b1 * Work.FIPlan.oddPart b2) ^ 2 ≠ Work.FIPlan.oddPart b1 * Work.FIPlan.oddPart b2),
          ((b1*b2:ℕ):ℝ)⁻¹ * (((radE e).divisors.card : ℝ) * ∑ d ∈ (radE e).divisors,
            (jsum (Work.FIPlan.oddPart b1 * Work.FIPlan.oddPart b2) (R'/d))^2)) := by
    apply Finset.sum_le_sum; intro e he
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Finset.sum_le_sum; intro b1 _
    apply Finset.sum_le_sum; intro b2 _
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact L14.A_sieve_bound e b1 b2 R' (by simpa using (Finset.mem_Icc.mp he).1)
  have hs2 : ∀ e : ℕ, (∑ b1 ∈ Finset.Icc 1 D,
        ∑ b2 ∈ (Finset.Icc 1 D).filter (fun b2 => Nat.sqrt (Work.FIPlan.oddPart b1 * Work.FIPlan.oddPart b2) ^ 2 ≠ Work.FIPlan.oddPart b1 * Work.FIPlan.oddPart b2),
          ((b1*b2:ℕ):ℝ)⁻¹ * (((radE e).divisors.card : ℝ) * ∑ d ∈ (radE e).divisors,
            (jsum (Work.FIPlan.oddPart b1 * Work.FIPlan.oddPart b2) (R'/d))^2))
      = ((radE e).divisors.card : ℝ) * (∑ d ∈ (radE e).divisors, ∑ b1 ∈ Finset.Icc 1 D,
        ∑ b2 ∈ (Finset.Icc 1 D).filter (fun b2 => Nat.sqrt (Work.FIPlan.oddPart b1 * Work.FIPlan.oddPart b2) ^ 2 ≠ Work.FIPlan.oddPart b1 * Work.FIPlan.oddPart b2),
          ((b1*b2:ℕ):ℝ)⁻¹ * (jsum (Work.FIPlan.oddPart b1 * Work.FIPlan.oddPart b2) (R'/d))^2) := by
    intro e
    rw [show (∑ b1 ∈ Finset.Icc 1 D,
          ∑ b2 ∈ (Finset.Icc 1 D).filter (fun b2 => Nat.sqrt (Work.FIPlan.oddPart b1 * Work.FIPlan.oddPart b2) ^ 2 ≠ Work.FIPlan.oddPart b1 * Work.FIPlan.oddPart b2),
            ((b1*b2:ℕ):ℝ)⁻¹ * (((radE e).divisors.card : ℝ) * ∑ d ∈ (radE e).divisors,
              (jsum (Work.FIPlan.oddPart b1 * Work.FIPlan.oddPart b2) (R'/d))^2))
        = ∑ b1 ∈ Finset.Icc 1 D,
          ∑ b2 ∈ (Finset.Icc 1 D).filter (fun b2 => Nat.sqrt (Work.FIPlan.oddPart b1 * Work.FIPlan.oddPart b2) ^ 2 ≠ Work.FIPlan.oddPart b1 * Work.FIPlan.oddPart b2),
            ((radE e).divisors.card : ℝ) * (((b1*b2:ℕ):ℝ)⁻¹ * ∑ d ∈ (radE e).divisors,
              (jsum (Work.FIPlan.oddPart b1 * Work.FIPlan.oddPart b2) (R'/d))^2) from by
      apply Finset.sum_congr rfl; intro b1 _
      apply Finset.sum_congr rfl; intro b2 _
      ring]
    rw [show (∑ b1 ∈ Finset.Icc 1 D,
          ∑ b2 ∈ (Finset.Icc 1 D).filter (fun b2 => Nat.sqrt (Work.FIPlan.oddPart b1 * Work.FIPlan.oddPart b2) ^ 2 ≠ Work.FIPlan.oddPart b1 * Work.FIPlan.oddPart b2),
            ((radE e).divisors.card : ℝ) * (((b1*b2:ℕ):ℝ)⁻¹ * ∑ d ∈ (radE e).divisors,
              (jsum (Work.FIPlan.oddPart b1 * Work.FIPlan.oddPart b2) (R'/d))^2))
        = ∑ b1 ∈ Finset.Icc 1 D, ((radE e).divisors.card : ℝ) *
          (∑ b2 ∈ (Finset.Icc 1 D).filter (fun b2 => Nat.sqrt (Work.FIPlan.oddPart b1 * Work.FIPlan.oddPart b2) ^ 2 ≠ Work.FIPlan.oddPart b1 * Work.FIPlan.oddPart b2),
            ((b1*b2:ℕ):ℝ)⁻¹ * ∑ d ∈ (radE e).divisors, (jsum (Work.FIPlan.oddPart b1 * Work.FIPlan.oddPart b2) (R'/d))^2) from by
      apply Finset.sum_congr rfl; intro b1 _
      rw [Finset.mul_sum]]
    rw [← Finset.mul_sum]
    congr 1
    rw [show (∑ b1 ∈ Finset.Icc 1 D,
          ∑ b2 ∈ (Finset.Icc 1 D).filter (fun b2 => Nat.sqrt (Work.FIPlan.oddPart b1 * Work.FIPlan.oddPart b2) ^ 2 ≠ Work.FIPlan.oddPart b1 * Work.FIPlan.oddPart b2),
            ((b1*b2:ℕ):ℝ)⁻¹ * ∑ d ∈ (radE e).divisors, (jsum (Work.FIPlan.oddPart b1 * Work.FIPlan.oddPart b2) (R'/d))^2)
        = ∑ b1 ∈ Finset.Icc 1 D,
          ∑ b2 ∈ (Finset.Icc 1 D).filter (fun b2 => Nat.sqrt (Work.FIPlan.oddPart b1 * Work.FIPlan.oddPart b2) ^ 2 ≠ Work.FIPlan.oddPart b1 * Work.FIPlan.oddPart b2),
            ∑ d ∈ (radE e).divisors, ((b1*b2:ℕ):ℝ)⁻¹ * (jsum (Work.FIPlan.oddPart b1 * Work.FIPlan.oddPart b2) (R'/d))^2 from by
      apply Finset.sum_congr rfl; intro b1 _
      apply Finset.sum_congr rfl; intro b2 _
      rw [Finset.mul_sum]]
    rw [Finset.sum_congr rfl (fun b1 _ => Finset.sum_comm), Finset.sum_comm]
  have hs3 : (∑ e ∈ Finset.Icc 1 D, (e:ℝ)⁻¹ * (((radE e).divisors.card : ℝ) *
        (∑ d ∈ (radE e).divisors, ∑ b1 ∈ Finset.Icc 1 D,
          ∑ b2 ∈ (Finset.Icc 1 D).filter (fun b2 => Nat.sqrt (Work.FIPlan.oddPart b1 * Work.FIPlan.oddPart b2) ^ 2 ≠ Work.FIPlan.oddPart b1 * Work.FIPlan.oddPart b2),
            ((b1*b2:ℕ):ℝ)⁻¹ * (jsum (Work.FIPlan.oddPart b1 * Work.FIPlan.oddPart b2) (R'/d))^2)))
      ≤ ∑ e ∈ Finset.Icc 1 D, (e:ℝ)⁻¹ * (((radE e).divisors.card : ℝ) *
        (∑ d ∈ (radE e).divisors, (Ctr * (D:ℝ)^(2*δ) * Mt (R'/d)))) := by
    apply Finset.sum_le_sum; intro e _
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Finset.sum_le_sum; intro d _
    exact htransf (R'/d)
  have hs4 : (∑ e ∈ Finset.Icc 1 D, (e:ℝ)⁻¹ * (((radE e).divisors.card : ℝ) *
        (∑ d ∈ (radE e).divisors, (Ctr * (D:ℝ)^(2*δ) * Mt (R'/d)))))
      ≤ ∑ e ∈ Finset.Icc 1 D, (e:ℝ)⁻¹ * (((radE e).divisors.card : ℝ) *
        (((radE e).divisors.card : ℝ) * (Ctr * (D:ℝ)^(2*δ) * Mt R'))) := by
    apply Finset.sum_le_sum; intro e _
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc ∑ d ∈ (radE e).divisors, (Ctr * (D:ℝ)^(2*δ) * Mt (R'/d))
        ≤ ∑ _d ∈ (radE e).divisors, (Ctr * (D:ℝ)^(2*δ) * Mt R') := by
          apply Finset.sum_le_sum; intro d _
          exact mul_le_mul_of_nonneg_left (hMt_mono (R'/d) R' (Nat.div_le_self R' d)) (by positivity)
      _ = ((radE e).divisors.card : ℝ) * (Ctr * (D:ℝ)^(2*δ) * Mt R') := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hs5 : (∑ e ∈ Finset.Icc 1 D, (e:ℝ)⁻¹ * (((radE e).divisors.card : ℝ) *
        (((radE e).divisors.card : ℝ) * (Ctr * (D:ℝ)^(2*δ) * Mt R'))))
      ≤ (Cdiv^2 * Clog * (D:ℝ)^(3*δ)) * (Ctr * (D:ℝ)^(2*δ) * Mt R') := by
    rw [show (∑ e ∈ Finset.Icc 1 D, (e:ℝ)⁻¹ * (((radE e).divisors.card : ℝ) *
          (((radE e).divisors.card : ℝ) * (Ctr * (D:ℝ)^(2*δ) * Mt R'))))
        = (∑ e ∈ Finset.Icc 1 D, (e:ℝ)⁻¹ * (((radE e).divisors.card : ℝ))^2)
            * (Ctr * (D:ℝ)^(2*δ) * Mt R') from by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl; intro e _; ring]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    calc ∑ e ∈ Finset.Icc 1 D, (e:ℝ)⁻¹ * (((radE e).divisors.card : ℝ))^2
        ≤ ∑ e ∈ Finset.Icc 1 D, (e:ℝ)⁻¹ * (Cdiv * (D:ℝ)^δ)^2 := by
          apply Finset.sum_le_sum; intro e he
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have he1 : 1 ≤ e := (Finset.mem_Icc.mp he).1
          have heD : (e:ℝ) ≤ (D:ℝ) := by exact_mod_cast (Finset.mem_Icc.mp he).2
          have h1 : ((radE e).divisors.card : ℝ) ≤ Cdiv * (e:ℝ)^δ := (hcard e he1).trans (hdiv e)
          have h2 : (e:ℝ)^δ ≤ (D:ℝ)^δ := Real.rpow_le_rpow (by positivity) heD hδ.le
          calc (((radE e).divisors.card : ℝ))^2 ≤ (Cdiv * (e:ℝ)^δ)^2 := pow_le_pow_left₀ (by positivity) h1 2
            _ ≤ (Cdiv * (D:ℝ)^δ)^2 := by
                apply pow_le_pow_left₀ (by positivity)
                exact mul_le_mul_of_nonneg_left h2 hCdiv.le
      _ = (Cdiv * (D:ℝ)^δ)^2 * ∑ e ∈ Finset.Icc 1 D, (e:ℝ)⁻¹ := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro e _; ring
      _ ≤ (Cdiv * (D:ℝ)^δ)^2 * (1 + Real.log (D:ℝ)) :=
          mul_le_mul_of_nonneg_left hharm (by positivity)
      _ ≤ (Cdiv * (D:ℝ)^δ)^2 * (Clog * (D:ℝ)^δ) :=
          mul_le_mul_of_nonneg_left (hlogb D hD) (by positivity)
      _ = Cdiv^2 * Clog * (D:ℝ)^(3*δ) := by
          have hD3 : (D:ℝ)^δ * (D:ℝ)^δ * (D:ℝ)^δ = (D:ℝ)^(3*δ) := by
            rw [← Real.rpow_add hDpos, ← Real.rpow_add hDpos]; congr 1; ring
          calc (Cdiv * (D:ℝ)^δ)^2 * (Clog * (D:ℝ)^δ)
              = Cdiv^2 * Clog * ((D:ℝ)^δ * (D:ℝ)^δ * (D:ℝ)^δ) := by ring
            _ = Cdiv^2 * Clog * (D:ℝ)^(3*δ) := by rw [hD3]
  have hmain : Usum D R' ≤ (Cdiv^2 * Clog * (D:ℝ)^(3*δ)) * (Ctr * (D:ℝ)^(2*δ) * Mt R') := by
    rw [hUsum]
    refine hs1.trans ?_
    rw [show (∑ e ∈ Finset.Icc 1 D, (e:ℝ)⁻¹ * (∑ b1 ∈ Finset.Icc 1 D,
          ∑ b2 ∈ (Finset.Icc 1 D).filter (fun b2 => Nat.sqrt (Work.FIPlan.oddPart b1 * Work.FIPlan.oddPart b2) ^ 2 ≠ Work.FIPlan.oddPart b1 * Work.FIPlan.oddPart b2),
            ((b1*b2:ℕ):ℝ)⁻¹ * (((radE e).divisors.card : ℝ) * ∑ d ∈ (radE e).divisors,
              (jsum (Work.FIPlan.oddPart b1 * Work.FIPlan.oddPart b2) (R'/d))^2)))
        = ∑ e ∈ Finset.Icc 1 D, (e:ℝ)⁻¹ * (((radE e).divisors.card : ℝ) *
            (∑ d ∈ (radE e).divisors, ∑ b1 ∈ Finset.Icc 1 D,
              ∑ b2 ∈ (Finset.Icc 1 D).filter (fun b2 => Nat.sqrt (Work.FIPlan.oddPart b1 * Work.FIPlan.oddPart b2) ^ 2 ≠ Work.FIPlan.oddPart b1 * Work.FIPlan.oddPart b2),
                ((b1*b2:ℕ):ℝ)⁻¹ * (jsum (Work.FIPlan.oddPart b1 * Work.FIPlan.oddPart b2) (R'/d))^2)) from by
      apply Finset.sum_congr rfl; intro e _; rw [hs2 e]]
    exact hs3.trans (hs4.trans hs5)
  refine hmain.trans ?_
  have hD5 : (D:ℝ)^(3*δ) * (D:ℝ)^(2*δ) = (D:ℝ)^(5*δ) := by
    rw [← Real.rpow_add hDpos]; congr 1; ring
  have hlogeq : Real.log ((D:ℝ)*D*(R':ℝ)+2) = Real.log ((D:ℝ)^2*(R':ℝ)+2) := by
    congr 1; ring
  have hMtR : Mt R' = 2 * Cfb * (R':ℝ)^((3:ℝ)/2) * (Real.log ((D:ℝ)^2*(R':ℝ)+2)+1)^2 := by
    simp only [Mt]; rw [hlogeq]
  rw [hMtR]
  have hRnn : (0:ℝ) ≤ (R':ℝ)^((3:ℝ)/2) := Real.rpow_nonneg (by positivity) _
  have hLnn : (0:ℝ) ≤ (Real.log ((D:ℝ)^2*(R':ℝ)+2)+1)^2 := sq_nonneg _
  have hAn : (0:ℝ) ≤ 2 * Ctr * Cfb * Cdiv^2 * Clog := by positivity
  have hD5n : (0:ℝ) ≤ (D:ℝ)^(5*δ) := Real.rpow_nonneg hDpos.le _
  have heq : Cdiv^2 * Clog * (D:ℝ)^(3*δ) *
        (Ctr * (D:ℝ)^(2*δ) * (2*Cfb*(R':ℝ)^((3:ℝ)/2)*(Real.log ((D:ℝ)^2*(R':ℝ)+2)+1)^2))
      = 2 * Ctr * Cfb * Cdiv^2 * Clog *
        ((D:ℝ)^(5*δ) * ((R':ℝ)^((3:ℝ)/2)*(Real.log ((D:ℝ)^2*(R':ℝ)+2)+1)^2)) := by
    rw [← hD5]; ring
  have heq2 : (2 * Ctr * Cfb * Cdiv^2 * Clog + 1) * (D:ℝ)^(5*δ) * (R':ℝ)^((3:ℝ)/2)
        * (Real.log ((D:ℝ)^2*(R':ℝ)+2)+1)^2
      = (2 * Ctr * Cfb * Cdiv^2 * Clog + 1) *
        ((D:ℝ)^(5*δ) * ((R':ℝ)^((3:ℝ)/2)*(Real.log ((D:ℝ)^2*(R':ℝ)+2)+1)^2)) := by ring
  rw [heq, heq2]
  nlinarith [hAn, mul_nonneg hD5n (mul_nonneg hRnn hLnn)]


/-- Final assembly. -/
theorem lemma_11_4 :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ (D R : ℕ), 1 ≤ D → 1 ≤ R →
      (∑ d1 ∈ Finset.Icc 1 D,
        ∑ d2 ∈ (Finset.Icc 1 D).filter
            (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2
                        ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
          (((Nat.lcm d1 d2 : ℕ) : ℝ)⁻¹) *
            Complex.normSq (∑ r ∈ (Finset.Icc 1 R).filter (fun r => Nat.Coprime r (d1 * d2)),
              (jacobiSym (r : ℤ) (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) : ℂ)))
      ≤ C * (R : ℝ) ^ ((3 : ℝ) / 2) * (((D : ℝ) * (R : ℝ)) ^ ε) := by
  intro ε hε
  obtain ⟨Cred, hCred, hred⟩ := L14.reduce_to_T
  have hδp : 0 < ε/20 := by linarith
  obtain ⟨Cu, hCu, hUb⟩ := U_bound (ε/20) hδp
  -- general log bound
  have hloggen : ∃ Cg : ℝ, 0 < Cg ∧ ∀ x : ℝ, 1 ≤ x → (Real.log x + 1)^2 ≤ Cg * x^(ε/4) := by
    refine ⟨(8/ε + 1)^2, by positivity, ?_⟩
    intro x hx
    have hx0 : (0:ℝ) < x := by linarith
    have ha : (0:ℝ) < ε/8 := by linarith
    have hxa : (1:ℝ) ≤ x^(ε/8) := Real.one_le_rpow hx ha.le
    have hlog := Real.log_le_rpow_div hx0.le ha
    have hq : x^(ε/8)/(ε/8) = (8/ε) * x^(ε/8) := by
      rw [div_eq_mul_inv, inv_div]; ring
    have h2 : Real.log x + 1 ≤ (8/ε + 1) * x^(ε/8) := by
      have h4 : Real.log x + 1 ≤ (8/ε)*x^(ε/8) + x^(ε/8) := by linarith [hlog, hq.symm.le, hq.le, hxa]
      nlinarith [h4, hxa]
    have hlog0 : (0:ℝ) ≤ Real.log x + 1 := by
      have := Real.log_nonneg hx; linarith
    have hsq : (x^(ε/8))^2 = x^(ε/4) := by
      rw [pow_two, ← Real.rpow_add hx0]; congr 1; ring
    calc (Real.log x + 1)^2 ≤ ((8/ε + 1) * x^(ε/8))^2 := pow_le_pow_left₀ hlog0 h2 2
      _ = (8/ε + 1)^2 * x^(ε/4) := by rw [mul_pow, hsq]
  obtain ⟨Cg, hCg, hlogx⟩ := hloggen
  refine ⟨(Cred * (2 * Cu) * (Cg * 3^(ε/4)) + 1), by positivity, ?_⟩
  intro D R hD hR
  have hD1 : (1:ℝ) ≤ (D:ℝ) := by exact_mod_cast hD
  have hR1 : (1:ℝ) ≤ (R:ℝ) := by exact_mod_cast hR
  have hDnn : (0:ℝ) ≤ (D:ℝ) := by linarith
  have hRnn : (0:ℝ) ≤ (R:ℝ) := by linarith
  -- log bound for our D, R
  have hlogDR : (Real.log ((D:ℝ)^2*(R:ℝ)+2)+1)^2
      ≤ (Cg * 3^(ε/4)) * (((D:ℝ)*(R:ℝ))^(ε/2)) := by
    have hx1 : (1:ℝ) ≤ (D:ℝ)^2*(R:ℝ)+2 := by nlinarith [hD1, hR1, sq_nonneg (D:ℝ)]
    have h1 := hlogx ((D:ℝ)^2*(R:ℝ)+2) hx1
    have h2 : ((D:ℝ)^2*(R:ℝ)+2)^(ε/4) ≤ 3^(ε/4) * (((D:ℝ)*(R:ℝ))^(ε/2)) := by
      have hbase : (D:ℝ)^2*(R:ℝ)+2 ≤ 3 * ((D:ℝ)^2*(R:ℝ)) := by nlinarith [hD1, hR1, sq_nonneg (D:ℝ)]
      have hb2 : (D:ℝ)^2*(R:ℝ) ≤ ((D:ℝ)*(R:ℝ))^2 := by nlinarith [hD1, hR1]
      calc ((D:ℝ)^2*(R:ℝ)+2)^(ε/4) ≤ (3 * ((D:ℝ)^2*(R:ℝ)))^(ε/4) :=
            Real.rpow_le_rpow (by positivity) hbase (by linarith)
        _ ≤ (3 * ((D:ℝ)*(R:ℝ))^2)^(ε/4) :=
            Real.rpow_le_rpow (by positivity) (by nlinarith [hb2]) (by linarith)
        _ = 3^(ε/4) * ((((D:ℝ)*(R:ℝ))^2))^(ε/4) := Real.mul_rpow (by norm_num) (by positivity)
        _ = 3^(ε/4) * (((D:ℝ)*(R:ℝ))^(ε/2)) := by
              have hthis : ((((D:ℝ)*(R:ℝ))^2))^(ε/4) = ((D:ℝ)*(R:ℝ))^(ε/2) := by
                rw [← Real.rpow_natCast ((D:ℝ)*(R:ℝ)) 2,
                    ← Real.rpow_mul (by positivity : (0:ℝ) ≤ (D:ℝ)*(R:ℝ))]
                congr 1
                push_cast
                ring
              rw [hthis]
    calc (Real.log ((D:ℝ)^2*(R:ℝ)+2)+1)^2 ≤ Cg * ((D:ℝ)^2*(R:ℝ)+2)^(ε/4) := h1
      _ ≤ Cg * (3^(ε/4) * (((D:ℝ)*(R:ℝ))^(ε/2))) := mul_le_mul_of_nonneg_left h2 hCg.le
      _ = (Cg * 3^(ε/4)) * (((D:ℝ)*(R:ℝ))^(ε/2)) := by ring
  set X : ℝ := Cu * (D:ℝ)^(ε/4) * (R:ℝ)^((3:ℝ)/2) * (Real.log ((D:ℝ)^2*(R:ℝ)+2)+1)^2 with hXdef
  have hT1 : (∑ d1 ∈ Finset.Icc 1 D, ∑ d2 ∈ (Finset.Icc 1 D).filter
        (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2 ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
        (((Nat.lcm d1 d2 : ℕ) : ℝ)⁻¹) *
          (∑ r ∈ Finset.Icc 1 R, (jacobiSym (r : ℤ) (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) : ℝ))^2) ≤ X := by
    rw [hXdef]
    have h := le_trans (L14.T_to_U D R hD) (hUb D R hD)
    have h5 : (D:ℝ)^(5*(ε/20)) = (D:ℝ)^(ε/4) := by congr 1; ring
    rw [h5] at h
    exact h
  have hT2 : (∑ d1 ∈ Finset.Icc 1 D, ∑ d2 ∈ (Finset.Icc 1 D).filter
        (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2 ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
        (((Nat.lcm d1 d2 : ℕ) : ℝ)⁻¹) *
          (∑ r ∈ Finset.Icc 1 (R/2), (jacobiSym (r : ℤ) (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) : ℝ))^2) ≤ X := by
    rw [hXdef]
    have h := le_trans (L14.T_to_U D (R/2) hD) (hUb D (R/2) hD)
    have h5 : (D:ℝ)^(5*(ε/20)) = (D:ℝ)^(ε/4) := by congr 1; ring
    rw [h5] at h
    refine h.trans ?_
    apply mul_le_mul
    · apply mul_le_mul_of_nonneg_left _ (mul_nonneg hCu.le (Real.rpow_nonneg hDnn _))
      exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast Nat.div_le_self R 2) (by norm_num)
    · apply pow_le_pow_left₀ ?_
      · have hlog : Real.log ((D:ℝ)^2*↑(R/2)+2) ≤ Real.log ((D:ℝ)^2*(R:ℝ)+2) := by
          apply Real.log_le_log (by positivity)
          have hR2 : (↑(R/2) : ℝ) ≤ (R:ℝ) := by exact_mod_cast Nat.div_le_self R 2
          nlinarith [sq_nonneg (D:ℝ), hR2]
        linarith
      · have h1 : (1:ℝ) ≤ (D:ℝ)^2*↑(R/2)+2 := by
          have hR2 : (0:ℝ) ≤ (↑(R/2) : ℝ) := by positivity
          nlinarith [hD1, hR1, sq_nonneg (D:ℝ), hR2]
        have := Real.log_nonneg h1; linarith
    · positivity
    · exact mul_nonneg (mul_nonneg hCu.le (Real.rpow_nonneg hDnn _)) (Real.rpow_nonneg hRnn _)
  have hsum : (∑ d1 ∈ Finset.Icc 1 D,
        ∑ d2 ∈ (Finset.Icc 1 D).filter
            (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2
                        ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
          (((Nat.lcm d1 d2 : ℕ) : ℝ)⁻¹) *
            Complex.normSq (∑ r ∈ (Finset.Icc 1 R).filter (fun r => Nat.Coprime r (d1 * d2)),
              (jacobiSym (r : ℤ) (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) : ℂ)))
      ≤ Cred * (X + X) := by
    have h1 := hred D R hD hR
    have h2 : Cred * ((∑ d1 ∈ Finset.Icc 1 D, ∑ d2 ∈ (Finset.Icc 1 D).filter
          (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2 ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
          (((Nat.lcm d1 d2 : ℕ) : ℝ)⁻¹) * (∑ r ∈ Finset.Icc 1 R, (jacobiSym (r : ℤ) (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) : ℝ))^2)
        + (∑ d1 ∈ Finset.Icc 1 D, ∑ d2 ∈ (Finset.Icc 1 D).filter
          (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2 ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
          (((Nat.lcm d1 d2 : ℕ) : ℝ)⁻¹) * (∑ r ∈ Finset.Icc 1 (R/2), (jacobiSym (r : ℤ) (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) : ℝ))^2))
        ≤ Cred * (X + X) := by
      apply mul_le_mul_of_nonneg_left _ hCred.le
      linarith [hT1, hT2]
    linarith [h1, h2]
  refine hsum.trans ?_
  rw [hXdef]
  have hmono : Cred * (Cu * (D:ℝ)^(ε/4) * (R:ℝ)^((3:ℝ)/2) * (Real.log ((D:ℝ)^2*(R:ℝ)+2)+1)^2
        + Cu * (D:ℝ)^(ε/4) * (R:ℝ)^((3:ℝ)/2) * (Real.log ((D:ℝ)^2*(R:ℝ)+2)+1)^2)
      ≤ Cred * (2 * (Cu * (D:ℝ)^(ε/4) * (R:ℝ)^((3:ℝ)/2) * ((Cg * 3^(ε/4)) * (((D:ℝ)*(R:ℝ))^(ε/2))))) := by
    apply mul_le_mul_of_nonneg_left _ hCred.le
    have hinner : (0:ℝ) ≤ Cu * (D:ℝ)^(ε/4) * (R:ℝ)^((3:ℝ)/2) := by positivity
    have h2 : Cu * (D:ℝ)^(ε/4) * (R:ℝ)^((3:ℝ)/2) * (Real.log ((D:ℝ)^2*(R:ℝ)+2)+1)^2
        ≤ Cu * (D:ℝ)^(ε/4) * (R:ℝ)^((3:ℝ)/2) * ((Cg * 3^(ε/4)) * (((D:ℝ)*(R:ℝ))^(ε/2))) :=
      mul_le_mul_of_nonneg_left hlogDR hinner
    nlinarith [h2]
  refine hmono.trans ?_
  have hDR2 : (D:ℝ)^(ε/4) * (((D:ℝ)*(R:ℝ))^(ε/2)) ≤ ((D:ℝ)*(R:ℝ))^ε := by
    have h1 : ((D:ℝ)*(R:ℝ))^ε = ((D:ℝ)*(R:ℝ))^(ε/2) * ((D:ℝ)*(R:ℝ))^(ε/2) := by
      rw [← Real.rpow_add (by positivity : (0:ℝ) < (D:ℝ)*(R:ℝ))]; congr 1; ring
    rw [h1]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    calc (D:ℝ)^(ε/4) ≤ (D:ℝ)^(ε/2) := Real.rpow_le_rpow_of_exponent_le hD1 (by linarith)
      _ ≤ ((D:ℝ)*(R:ℝ))^(ε/2) :=
          Real.rpow_le_rpow (by positivity) (by nlinarith [hD1, hR1]) (by positivity)
  have hkey : Cred * (2 * (Cu * (D:ℝ)^(ε/4) * (R:ℝ)^((3:ℝ)/2) * ((Cg * 3^(ε/4)) * (((D:ℝ)*(R:ℝ))^(ε/2)))))
      = (Cred * (2 * Cu) * (Cg * 3^(ε/4))) *
          ((R:ℝ)^((3:ℝ)/2) * ((D:ℝ)^(ε/4) * (((D:ℝ)*(R:ℝ))^(ε/2)))) := by ring
  rw [hkey]
  have hA0 : (0:ℝ) ≤ Cred * (2 * Cu) * (Cg * 3^(ε/4)) := by positivity
  have hRnn' : (0:ℝ) ≤ (R:ℝ)^((3:ℝ)/2) := by positivity
  have hDRnn : (0:ℝ) ≤ ((D:ℝ)*(R:ℝ))^ε := Real.rpow_nonneg (by positivity) ε
  have hcomb : (R:ℝ)^((3:ℝ)/2) * ((D:ℝ)^(ε/4) * (((D:ℝ)*(R:ℝ))^(ε/2)))
      ≤ (R:ℝ)^((3:ℝ)/2) * (((D:ℝ)*(R:ℝ))^ε) := mul_le_mul_of_nonneg_left hDR2 hRnn'
  nlinarith [hcomb, hA0, hRnn', hDRnn, mul_nonneg hRnn' hDRnn, mul_nonneg hA0 (mul_nonneg hRnn' hDRnn)]

end
end Work.FIArea4
