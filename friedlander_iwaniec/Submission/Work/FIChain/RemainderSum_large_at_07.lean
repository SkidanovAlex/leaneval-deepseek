import Mathlib
import Submission.Work.FIChain.Defs
import Submission.ASP.S40
import Submission.ASP.S31
import Submission.ASP.S22
import Submission.ASP.S21
import Submission.ASP.S35
import Submission.ASP.S36
import Submission.ASP.S34
import Submission.ASP.S33
import Submission.ASP.S32
import Submission.ASP.S9b
import Submission.ASP.S9d
import Submission.ASP.S37
import Submission.ASP_R3

namespace Work.FIChain

open Finset



/-- `r̃_full` for the Friedlander–Iwaniec sequence, in the companion's objects. -/
local notation "rtF" =>
  Submission.ASP.rtildeFull Submission.ASP.FIr Submission.ASP.FIg Submission.ASP.FIgtil Submission.ASP.FIa

/-- `Ã(x) = ∑_{n ≤ x} ã(n)`, the squarefree-supported counting function of `FIa`. -/
local notation "AtilA" x:max =>
  Submission.ASP.Acount (Submission.ASP.atil Submission.ASP.FIa) x

/-- **The Hölder step of the `(R′)`-bound.**  From the `τ^{20/3}`-weighted remainder bound
`∑_{d ≤ D, ♭} τ(d)^{20/3}|r_d(m)| ≤ P` and the unweighted one `∑_{d ≤ D, ♭} |r_d(m)| ≤ Q`
deduce the `τ^5`-weighted bound `RemainderSum r D m ≤ P^{3/4} Q^{1/4}` (the companion's
`(R′)`-weight `τ(d)^5`).  This is Hölder with the conjugate pair `(4/3, 4)`, applied to the
pointwise identity `τ^5·r = (τ^{20/3}·r)^{3/4}·r^{1/4}`. -/
lemma RemainderSum_holderStep_at_07 {r : ℕ → ℕ → ℝ} {D m : ℕ} {P Q : ℝ}
    (hPnn : 0 ≤ P)
    (hP : (∑ d ∈ (Finset.Icc 1 D).filter Squarefree,
        ((d.divisors.card : ℝ)) ^ ((20 : ℝ) / 3) * |r d m|) ≤ P)
    (hQ : (∑ d ∈ (Finset.Icc 1 D).filter Squarefree, |r d m|) ≤ Q) :
    Submission.ASP.RemainderSum r D m ≤ P ^ ((3 : ℝ) / 4) * Q ^ ((1 : ℝ) / 4) := by
  have hholder := Commons.Analysis.MeanInequalities.sum_rpow_holder
    (F := fun d : ℕ => ((d.divisors.card : ℝ)))
    (R := fun d : ℕ => if Squarefree d then |r d m| else 0)
    (fun d => by positivity) (fun d => by positivity) D
  have hE5 : (∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℝ)) ^ 5
        * (if Squarefree d then |r d m| else 0)) = Submission.ASP.RemainderSum r D m := by
    rw [Submission.ASP.RemainderSum, Finset.sum_filter]
    exact Finset.sum_congr rfl (fun d _ => by by_cases h : Squarefree d <;> simp [h])
  have hE23 : (∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℝ)) ^ ((20 : ℝ) / 3)
        * (if Squarefree d then |r d m| else 0))
      = ∑ d ∈ (Finset.Icc 1 D).filter Squarefree,
          ((d.divisors.card : ℝ)) ^ ((20 : ℝ) / 3) * |r d m| := by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl (fun d _ => by by_cases h : Squarefree d <;> simp [h])
  have hE0 : (∑ d ∈ Finset.Icc 1 D, (if Squarefree d then |r d m| else 0))
      = ∑ d ∈ (Finset.Icc 1 D).filter Squarefree, |r d m| := by
    rw [Finset.sum_filter]
  rw [← hE5]
  refine le_trans hholder ?_
  have hb1 : 0 ≤ ∑ d ∈ Finset.Icc 1 D, ((d.divisors.card : ℝ)) ^ ((20 : ℝ) / 3)
      * (if Squarefree d then |r d m| else 0) := by
    rw [hE23]
    exact Finset.sum_nonneg (fun d _ => mul_nonneg (by positivity) (abs_nonneg _))
  have hb2 : 0 ≤ ∑ d ∈ Finset.Icc 1 D, (if Squarefree d then |r d m| else 0) := by
    rw [hE0]
    exact Finset.sum_nonneg (fun d _ => abs_nonneg _)
  refine mul_le_mul (Real.rpow_le_rpow hb1 ?_ (by norm_num))
    (Real.rpow_le_rpow hb2 ?_ (by norm_num)) (Real.rpow_nonneg hb2 _) (Real.rpow_nonneg hPnn _)
  · rw [hE23]; exact hP
  · rw [hE0]; exact hQ

theorem RemainderSum_large_at_07 (C23 lam23 CR lam : ℝ) (hC23 : 0 < C23) (hCR : 0 < CR)
    (X23 XR : ℕ)
    (h23 : ∀ x : ℕ, X23 ≤ x → ∀ m : ℕ, 2 ≤ m → m ≤ x → ∀ D : ℕ, D ≤ m →
      (∑ d ∈ (Finset.Icc 1 D).filter Squarefree,
        ((d.divisors.card : ℝ)) ^ ((20 : ℝ) / 3)
          * |Submission.ASP.rtildeFull Submission.ASP.FIr Submission.ASP.FIg Submission.ASP.FIgtil Submission.ASP.FIa d m|)
        ≤ C23 * ((Submission.Aseq x : ℝ)
            + Submission.ASP.Acount (Submission.ASP.atil Submission.ASP.FIa) (x : ℝ))
          * (Real.log (x : ℝ)) ^ lam23)
    (hR : ∀ x : ℕ, XR ≤ x → ∀ m : ℕ, ⌈(x : ℝ) ^ ((7 : ℝ) / 10)⌉₊ ≤ m → m ≤ x →
      (∑ d ∈ (Finset.Icc 1 ⌈(x : ℝ) ^ ((7 : ℝ) / 10)⌉₊).filter Squarefree,
        |Submission.ASP.rtildeFull Submission.ASP.FIr Submission.ASP.FIg Submission.ASP.FIgtil Submission.ASP.FIa d m|)
        ≤ CR * (Submission.Aseq x : ℝ) * (Real.log (x : ℝ)) ^ (-lam))
    (hlam : lam = 3 * max lam23 0 + 13) :
    ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x → ∀ m : ℕ, ⌈(x : ℝ) ^ ((7 : ℝ) / 10)⌉₊ ≤ m → m ≤ x →
      Submission.ASP.RemainderSum (Submission.ASP.rtildeFull Submission.ASP.FIr Submission.ASP.FIg Submission.ASP.FIgtil Submission.ASP.FIa)
          (⌈(x : ℝ) ^ ((7 : ℝ) / 10)⌉₊) m
        ≤ Submission.ASP.Acount (Submission.ASP.atil Submission.ASP.FIa) (x : ℝ) * (Real.log (x : ℝ)) ^ (-(3 : ℝ)) := by
  obtain ⟨Xab, hab⟩ := Submission.ASP.FI_Aseq_le_const_mul_Atil
  set Cc0 : ℝ := 2 / Submission.ASP.Gprod Submission.ASP.FIg + 1 with hCcdef
  have hCcpos : 0 < Cc0 := by
    rw [hCcdef]
    have h := Submission.ASP.Gprod_FIg_pos
    positivity
  set K : ℝ := (C23 * (Cc0 + 1)) ^ ((3 : ℝ) / 4) * (CR * Cc0) ^ ((1 : ℝ) / 4) with hKdef
  have hKpos : 0 < K := by
    rw [hKdef]
    exact mul_pos (Real.rpow_pos_of_pos (by positivity) _)
      (Real.rpow_pos_of_pos (by positivity) _)
  obtain ⟨Xl, hXl⟩ : ∃ X : ℕ, Real.exp (K ^ 4) ≤ (X : ℝ) :=
    ⟨⌈Real.exp (K ^ 4)⌉₊, Nat.le_ceil _⟩
  refine ⟨max (max (max X23 XR) (max Xab Xl)) 64, fun x hx m hmD hmx => ?_⟩
  have hx23 : X23 ≤ x := by omega
  have hxr : XR ≤ x := by omega
  have hxab : Xab ≤ x := by omega
  have hxl : Xl ≤ x := by omega
  have hx64 : 64 ≤ x := by omega
  have hx1 : 1 ≤ x := by omega
  have hx4 : 4 ≤ x := by omega
  have hx3 : (3 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (by omega : 3 ≤ x)
  have hlog1 : (1 : ℝ) ≤ Real.log x :=
    le_trans Submission.ASP.one_le_log_three (Real.log_le_log (by norm_num) hx3)
  have hlog0 : (0 : ℝ) < Real.log x := lt_of_lt_of_le zero_lt_one hlog1
  -- `D₇(x) = ⌈x^{7/10}⌉ ≥ 2`, hence `2 ≤ m`
  have hD2 : 2 ≤ ⌈(x : ℝ) ^ ((7 : ℝ) / 10)⌉₊ := by
    have hx1r : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx1
    have hx4r : (4 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx4
    have hmono : (x : ℝ) ^ ((1 : ℝ) / 2) ≤ (x : ℝ) ^ ((7 : ℝ) / 10) :=
      Real.rpow_le_rpow_of_exponent_le hx1r (by norm_num)
    have hsqrt : (2 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2) := by
      have h := Real.sqrt_le_sqrt hx4r
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow] at h
      have h4 : (4 : ℝ) ^ ((1 : ℝ) / 2) = 2 := by rw [← Real.sqrt_eq_rpow]; norm_num
      linarith [h, h4.le, h4.ge]
    have h2 : (2 : ℝ) ≤ (⌈(x : ℝ) ^ ((7 : ℝ) / 10)⌉₊ : ℝ) :=
      le_trans (le_trans hsqrt hmono) (Nat.le_ceil _)
    exact_mod_cast h2
  have hm2 : 2 ≤ m := le_trans hD2 hmD
  -- positivity of the two counting functions and the comparison `A(x) ≪ Ã(x)`
  have hAt1 : (1 : ℝ) ≤ AtilA x := Submission.ASP.one_le_Acount_atil x hx1
  have hAt0 : (0 : ℝ) < AtilA x := lt_of_lt_of_le zero_lt_one hAt1
  have hAsnn : (0 : ℝ) ≤ (Submission.Aseq x : ℝ) := by
    have h0 : (0 : ℝ) ≤ Submission.ASP.Acount Submission.ASP.FIa (x : ℝ) :=
      Finset.sum_nonneg (fun n _ => Submission.ASP.FIa_nonneg n)
    rw [Submission.ASP.FI_Acount_eq] at h0
    linarith
  have hAsle : (Submission.Aseq x : ℝ) ≤ Cc0 * AtilA x := by
    have h1 := hab x hxab
    rw [Submission.ASP.FI_Acount_eq] at h1
    have h3 : (2 / Submission.ASP.Gprod Submission.ASP.FIg) * AtilA x + 1
        ≤ (2 / Submission.ASP.Gprod Submission.ASP.FIg) * AtilA x + AtilA x := by linarith
    have h4 : (2 / Submission.ASP.Gprod Submission.ASP.FIg) * AtilA x + AtilA x
        = Cc0 * AtilA x := by rw [hCcdef]; ring
    linarith
  -- the two inputs, at the cutoff `D₇(x) = ⌈x^{7/10}⌉`
  have hR' : (∑ d ∈ (Finset.Icc 1 ⌈(x : ℝ) ^ ((7 : ℝ) / 10)⌉₊).filter Squarefree,
        |rtF d m|)
      ≤ CR * (Submission.Aseq x : ℝ) * (Real.log (x : ℝ)) ^ (-lam) := hR x hxr m hmD hmx
  have h23' : (∑ d ∈ (Finset.Icc 1 ⌈(x : ℝ) ^ ((7 : ℝ) / 10)⌉₊).filter Squarefree,
        ((d.divisors.card : ℝ)) ^ ((20 : ℝ) / 3) * |rtF d m|)
      ≤ C23 * ((Submission.Aseq x : ℝ) + AtilA x) * (Real.log (x : ℝ)) ^ lam23 :=
    h23 x hx23 m hm2 hmx ⌈(x : ℝ) ^ ((7 : ℝ) / 10)⌉₊ hmD
  set P : ℝ := C23 * ((Submission.Aseq x : ℝ) + AtilA x) * (Real.log (x : ℝ)) ^ lam23
    with hPdef
  set Q : ℝ := CR * (Submission.Aseq x : ℝ) * (Real.log (x : ℝ)) ^ (-lam) with hQdef
  have hPnn : (0 : ℝ) ≤ P := by
    rw [hPdef]
    exact mul_nonneg (mul_nonneg hC23.le (by linarith)) (Real.rpow_nonneg hlog0.le _)
  have hQnn : (0 : ℝ) ≤ Q := by
    rw [hQdef]
    exact mul_nonneg (mul_nonneg hCR.le hAsnn) (Real.rpow_nonneg hlog0.le _)
  have hH : Submission.ASP.RemainderSum rtF (⌈(x : ℝ) ^ ((7 : ℝ) / 10)⌉₊) m
      ≤ P ^ ((3 : ℝ) / 4) * Q ^ ((1 : ℝ) / 4) :=
    RemainderSum_holderStep_at_07 hPnn h23' hR'
  -- the constant bookkeeping: `(C₂₃(C+1))^{3/4}(C_R C)^{1/4}·L^{λ₂₃·3/4-λ/4+3} ≤ 1`
  have hKey : (C23 * (Cc0 + 1)) ^ ((3 : ℝ) / 4) * (CR * Cc0) ^ ((1 : ℝ) / 4)
      * (Real.log x) ^ (lam23 * ((3 : ℝ) / 4) + (-lam) * ((1 : ℝ) / 4) + (3 : ℝ)) ≤ 1 := by
    have hKle : K ≤ (Real.log x) ^ ((1 : ℝ) / 4) := by
      have hh1 : K ^ 4 ≤ Real.log x := by
        have hh2 : Real.exp (K ^ 4) ≤ (x : ℝ) := le_trans hXl (by exact_mod_cast hxl)
        have hh3 := Real.log_le_log (Real.exp_pos _) hh2
        rwa [Real.log_exp] at hh3
      have hh4 : K = (K ^ 4) ^ ((1 : ℝ) / 4) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hKpos)]
        norm_num
      rw [hh4]
      exact Real.rpow_le_rpow (by positivity) hh1 (by norm_num)
    have hexp : lam23 * ((3 : ℝ) / 4) + (-lam) * ((1 : ℝ) / 4) + (3 : ℝ) ≤ -((1 : ℝ) / 4) := by
      rw [hlam]
      nlinarith [le_max_left lam23 (0 : ℝ)]
    have h1 : (C23 * (Cc0 + 1)) ^ ((3 : ℝ) / 4) * (CR * Cc0) ^ ((1 : ℝ) / 4) = K := hKdef.symm
    rw [h1]
    calc K * (Real.log x) ^ (lam23 * ((3 : ℝ) / 4) + (-lam) * ((1 : ℝ) / 4) + (3 : ℝ))
        ≤ (Real.log x) ^ ((1 : ℝ) / 4) * (Real.log x) ^ (-((1 : ℝ) / 4)) := by
          refine mul_le_mul hKle (Real.rpow_le_rpow_of_exponent_le hlog1 hexp)
            (Real.rpow_nonneg hlog0.le _) (Real.rpow_nonneg hlog0.le _)
      _ = 1 := by
          rw [← Real.rpow_add hlog0,
            show ((1 : ℝ) / 4) + -((1 : ℝ) / 4) = 0 by norm_num, Real.rpow_zero]
  refine le_trans hH ?_
  rw [hPdef, hQdef]
  exact Submission.ASP.holder_absorb hC23 hCR hCcpos hlog0 hAt0 hAsnn hAsle hKey

end Work.FIChain
