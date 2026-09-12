import Submission.MinkBox
import Submission.Contracts
import Submission.ThreePages
import Submission.Quantile
import Submission.EnergyHalf
import Submission.NormfInterp
import Submission.WnormShift
import Submission.HilbertProd
import Submission.HilbertDeriv
import Mathlib.Tactic

/-!
# Hilbert lemma from the Minkowski upper box (Smith prop:Hilbert, GON.tex)
-/

noncomputable section

open Polynomial
open scoped Real BigOperators

namespace Submission.HilbertMink

open Submission.MinkBox
open Submission.Contracts
open Submission.EnergyHalf
open Submission.Quantile
open Submission.ThreePages
open Submission.NormfInterp
open Submission.WnormToolkit
open Submission.HilbertProd
open Submission.HilbertDeriv

/-- Hilbert's lemma (Smith prop:Hilbert): for every `n ≥ 2` there are `n+1`
ℚ-linearly-independent integer polynomials of degree `≤ n` whose product of
weighted `n`-norms is `≤ n^{C·n}·exp(½·n²·energy)`. -/
def hilbertProp : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, 2 ≤ n →
      ∃ Q : Fin (n + 1) → Polynomial ℤ,
        LinIndepInt (n + 1) Q ∧
        (∀ i, (Q i).natDegree ≤ n) ∧
        (∏ i : Fin (n + 1), wnorm n (zmap (Q i))) ≤
          (n : ℝ) ^ (C * (n : ℝ)) *
            Real.exp ((1 / 2 : ℝ) * (n : ℝ) ^ 2 * energy)

/-! ## Auxiliary exponential/power absorption -/

/-- `exp((n + 1/2)·e) ≤ n^{C·n}` for a fixed `C` and all `n ≥ 2`. -/
lemma exp_lin_bound (e : ℝ) : ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, 2 ≤ n → Real.exp (((n : ℝ) + (1 / 2 : ℝ)) * e) ≤
      (n : ℝ) ^ (C * (n : ℝ)) := by
  by_cases he : e ≤ 0
  · refine ⟨1, by norm_num, ?_⟩
    intro n hn
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
    have hn0 : 0 ≤ (n : ℝ) := le_of_lt (by exact_mod_cast (by omega : 0 < n) : 0 < (n : ℝ))
    have hle : ((n : ℝ) + (1 / 2 : ℝ)) * e ≤ 0 := by
      have hpos : 0 < (n : ℝ) + (1 / 2 : ℝ) := by positivity
      exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt hpos) he
    calc
      Real.exp (((n : ℝ) + (1 / 2 : ℝ)) * e) ≤ Real.exp 0 := Real.exp_le_exp.mpr hle
      _ = 1 := Real.exp_zero
      _ ≤ (n : ℝ) ^ (1 * (n : ℝ)) := by
        have h1 := Real.rpow_le_rpow (by norm_num : 0 ≤ (1 : ℝ))
          hnR (by positivity : 0 ≤ (n : ℝ))
        rw [Real.one_rpow] at h1
        simpa using h1
  · have hepos : 0 < e := lt_of_not_ge he
    let C : ℝ := 2 * e / Real.log 2
    have hCpos : 0 < C := by
      dsimp [C]
      positivity
    refine ⟨C, hCpos, ?_⟩
    intro n hn
    have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hn1R : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
    have hlogle : Real.log 2 ≤ Real.log (n : ℝ) := Real.log_le_log (by norm_num) hnR
    have hCeq : C * Real.log 2 = 2 * e := by
      dsimp [C]
      field_simp [ne_of_gt hlog2]
    have h2e : 2 * e ≤ C * Real.log (n : ℝ) := by
      calc
        2 * e = C * Real.log 2 := hCeq.symm
        _ ≤ C * Real.log (n : ℝ) := mul_le_mul_of_nonneg_left hlogle (le_of_lt hCpos)
    have hcoef : (n : ℝ) + (1 / 2 : ℝ) ≤ 2 * (n : ℝ) := by nlinarith
    have hle1 : ((n : ℝ) + (1 / 2 : ℝ)) * e ≤ (2 * (n : ℝ)) * e :=
      mul_le_mul_of_nonneg_right hcoef (le_of_lt hepos)
    have hineq1 : (2 * (n : ℝ)) * e ≤ (n : ℝ) * (C * Real.log (n : ℝ)) := by
      have h1 : 2 * e ≤ C * Real.log (n : ℝ) := h2e
      nlinarith
    have hineq2 : (2 * (n : ℝ)) * e ≤ Real.log (n : ℝ) * (C * (n : ℝ)) := by
      calc
        (2 * (n : ℝ)) * e ≤ (n : ℝ) * (C * Real.log (n : ℝ)) := hineq1
        _ = Real.log (n : ℝ) * (C * (n : ℝ)) := by ring
    have hmain : Real.exp ((2 * (n : ℝ)) * e) ≤ (n : ℝ) ^ (C * (n : ℝ)) := by
      rw [Real.rpow_def_of_pos hnpos]
      exact Real.exp_le_exp.mpr hineq2
    exact le_trans (Real.exp_le_exp.mpr hle1) hmain

/-- `(n+1)^{A·(n+1)} ≤ n^{C·n}` for fixed nonneg `A` and all `n ≥ 2`. -/
lemma pow_np1_bound {A : ℝ} (hA : 0 ≤ A) : ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, 2 ≤ n → ((n + 1 : ℕ) : ℝ) ^ (A * ((n + 1 : ℕ) : ℝ)) ≤
      (n : ℝ) ^ (C * (n : ℝ)) := by
  let C : ℝ := 4 * A + 1
  have hCpos : 0 < C := by dsimp [C]; nlinarith
  refine ⟨C, hCpos, ?_⟩
  intro n hn
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hnp1 : (n : ℝ) + 1 ≤ (n : ℝ) ^ (2 : ℝ) := by
    simpa using (np1_le_n2 (n := (n : ℝ)) hnR)
  have hnp1' : ((n + 1 : ℕ) : ℝ) ≤ (n : ℝ) ^ (2 : ℝ) := by
    simpa using hnp1
  have he0 : 0 ≤ A * ((n + 1 : ℕ) : ℝ) := by
    exact mul_nonneg hA (by positivity)
  have hle1 : ((n + 1 : ℕ) : ℝ) ^ (A * ((n + 1 : ℕ) : ℝ)) ≤
      ((n : ℝ) ^ (2 : ℝ)) ^ (A * ((n + 1 : ℕ) : ℝ)) := by
    have hb0 : 0 ≤ ((n + 1 : ℕ) : ℝ) := by positivity
    exact Real.rpow_le_rpow hb0 hnp1' he0
  have hmul : ((n : ℝ) ^ (2 : ℝ)) ^ (A * ((n + 1 : ℕ) : ℝ)) =
      (n : ℝ) ^ (2 * A * ((n + 1 : ℕ) : ℝ)) := by
    rw [← Real.rpow_mul (le_of_lt hnpos) (2 : ℝ) (A * ((n + 1 : ℕ) : ℝ))]
    congr 1
    ring
  have hpow := le_trans hle1 (le_of_eq hmul)
  have hnp1le : ((n + 1 : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by
    rw [show ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 by norm_num]
    nlinarith
  have hexp_le : 2 * A * ((n + 1 : ℕ) : ℝ) ≤ 4 * A * (n : ℝ) := by
    have hstep : 2 * A * (((n + 1 : ℕ) : ℝ)) ≤ 2 * A * (2 * (n : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hnp1le (mul_nonneg (by norm_num) hA)
    nlinarith
  have hpow2 : (n : ℝ) ^ (2 * A * ((n + 1 : ℕ) : ℝ)) ≤ (n : ℝ) ^ (4 * A * (n : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hn1 hexp_le
  have hpow3 : (n : ℝ) ^ (4 * A * (n : ℝ)) ≤ (n : ℝ) ^ (C * (n : ℝ)) := by
    dsimp [C]
    exact Real.rpow_le_rpow_of_exponent_le hn1 (by nlinarith)
  exact le_trans hpow (le_trans hpow2 hpow3)

/-- `n^{B·(n+1)} ≤ n^{C·n}` for fixed nonneg `B` and all `n ≥ 2`. -/
lemma pow_n_mul_bound {B : ℝ} (hB : 0 ≤ B) : ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, 2 ≤ n → (n : ℝ) ^ (B * ((n : ℝ) + 1)) ≤
      (n : ℝ) ^ (C * (n : ℝ)) := by
  let C : ℝ := 2 * B + 1
  have hCpos : 0 < C := by dsimp [C]; nlinarith
  refine ⟨C, hCpos, ?_⟩
  intro n hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hcoef : B * ((n : ℝ) + 1) ≤ (2 * B + 1) * (n : ℝ) := by
    have hstep : (n : ℝ) + 1 ≤ 2 * (n : ℝ) := by nlinarith
    nlinarith
  exact Real.rpow_le_rpow_of_exponent_le hn1 hcoef

lemma Dval_deriv_eq (d : ℕ) (hd : 2 ≤ d) :
    Dval d (fun k : Fin d => alpha d (k.val + 1))
      (fun k : Fin d =>
        |(approxPoly d).derivative.eval (alpha d (k.val + 1))|⁻¹) =
    (Vprod d)⁻¹ := by
  unfold Dval
  have hd1 : 1 ≤ d := by omega
  have hV0 : Vprod d ≠ 0 := ne_of_gt (Vprod_pos d hd1)
  have h1 : (∏ k : Fin d,
      |(approxPoly d).derivative.eval (alpha d (k.val + 1))|⁻¹) =
      (∏ k : Fin d, |(approxPoly d).derivative.eval (alpha d (k.val + 1))|)⁻¹ := by
    rw [Finset.prod_inv_distrib]
  rw [h1]
  have hPP := pairProd_eq_Vprod d hd1
  have hDS := deriv_prod_sq d hd
  rw [hPP, hDS]
  field_simp [hV0]

/-- Hilbert's lemma, assuming the Minkowski upper box. -/
theorem hilbert_of_mink (hu : MinkBox.minkUpper) : hilbertProp := by
  unfold hilbertProp
  rcases hu with ⟨C0, hC0pos, hu0⟩
  rcases normf_interp with ⟨Ci, hCipos, hCi⟩
  rcases energy_half with ⟨Cd, hCdpos, hEd⟩
  rcases exp_lin_bound energy with ⟨Cexp, hCexppos, hCexp⟩
  rcases pow_np1_bound (A := C0 + Cd) (by linarith) with ⟨Cnp, hCnppos, hCnp⟩
  rcases pow_n_mul_bound (B := Ci) (le_of_lt hCipos) with ⟨Cnm, hCnmpos, hCnm⟩
  let C : ℝ := Cnm + Cnp + Cexp
  have hCpos : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hCpos, ?_⟩
  intro n hn
  have hn2R : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hnpos0 : 0 ≤ (n : ℝ) := le_of_lt hnpos
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by linarith
  have hdR : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by simp
  let x : ℝ := ((n + 1 : ℕ) : ℝ)
  have hxpos : 0 < x := by dsimp [x]; positivity
  have hx0 : 0 ≤ x := le_of_lt hxpos
  -- quantile nodes α and weights v
  let α : Fin (n + 1) → ℝ := fun k => alpha (n + 1) (k.val + 1)
  have hαinj : Function.Injective α := by
    intro k1 k2 hkeq
    by_contra hne
    have hd1 : 1 ≤ n + 1 := by omega
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hklt : k1.val < k2.val := Fin.lt_def.mp hlt
      have hst : alpha (n + 1) (k1.val + 1) < alpha (n + 1) (k2.val + 1) :=
        alpha_strict_mono (n := n + 1) hd1 (by omega) (by omega) (by omega)
      have hvaleq : alpha (n + 1) (k1.val + 1) = alpha (n + 1) (k2.val + 1) := by
        simpa [α] using hkeq
      rw [hvaleq] at hst
      exact (lt_irrefl _) hst
    · have hkgt : k2.val < k1.val := Fin.lt_def.mp hgt
      have hst : alpha (n + 1) (k2.val + 1) < alpha (n + 1) (k1.val + 1) :=
        alpha_strict_mono (n := n + 1) hd1 (by omega) (by omega) (by omega)
      have hvaleq : alpha (n + 1) (k2.val + 1) = alpha (n + 1) (k1.val + 1) := by
        simpa [α] using hkeq.symm
      rw [hvaleq] at hst
      exact (lt_irrefl _) hst
  let v : Fin (n + 1) → ℝ := fun k => |(approxPoly (n + 1)).derivative.eval (α k)|⁻¹
  have hv : ∀ k : Fin (n + 1), 0 < v k := by
    intro k
    have hk : k.val + 1 ∈ Finset.Icc 1 (n + 1) := by
      rw [Finset.mem_Icc]
      omega
    have hne : (approxPoly (n + 1)).derivative.eval (alpha (n + 1) (k.val + 1)) ≠ 0 :=
      derivative_eval_ne_zero (n := n) (k := k.val + 1) hk
    have hne' : (approxPoly (n + 1)).derivative.eval (α k) ≠ 0 := by
      simpa [α] using hne
    have habs : 0 < |(approxPoly (n + 1)).derivative.eval (α k)| := abs_pos.mpr hne'
    dsimp [v]
    exact inv_pos.mpr habs
  -- apply the Minkowski upper box
  rcases hu0 (n + 1) (by omega : 2 ≤ n + 1) α hαinj v hv with ⟨Q, hlin, hdegQ, mu, hmu, hprod⟩
  -- degree bound for the real maps
  have hdegz : ∀ i : Fin (n + 1), (zmap (Q i)).natDegree ≤ n := by
    intro i
    have hd := hdegQ i
    have hd' : (Q i).natDegree ≤ n := by
      have hsub : (n + 1) - 1 = n := by omega
      rwa [hsub] at hd
    exact le_trans (Polynomial.natDegree_map_le (f := algebraMap ℤ ℝ) (p := Q i)) hd'
  -- per-index interpolation bound
  have hnode : ∀ i : Fin (n + 1), wnorm n (zmap (Q i)) ≤ (n : ℝ) ^ Ci * mu i := by
    intro i
    let P : Polynomial ℝ := zmap (Q i)
    have hdegP : P.natDegree ≤ n := by simpa [P] using hdegz i
    have hCi0 : 0 ≤ (n : ℝ) ^ Ci := Real.rpow_nonneg hnpos0 Ci
    have hSle : ∀ y ∈ ((fun k : ℕ =>
          |P.eval (alpha (n + 1) k)| /
            |(approxPoly (n + 1)).derivative.eval (alpha (n + 1) k)|) ''
        Set.Icc 1 (n + 1)), y ≤ mu i := by
      intro y hy
      rcases hy with ⟨k, hk, rfl⟩
      have hk1 : 1 ≤ k := (Set.mem_Icc.mp hk).1
      have hkn : k ≤ n + 1 := (Set.mem_Icc.mp hk).2
      let kf : Fin (n + 1) := ⟨k - 1, by omega⟩
      have hαk : α kf = alpha (n + 1) k := by
        dsimp [α, kf]
        congr 1
        omega
      have hvkf : v kf = |(approxPoly (n + 1)).derivative.eval (alpha (n + 1) k)|⁻¹ := by
        dsimp [v]
        rw [hαk]
      have hPev : evalInt (Q i) (α kf) = P.eval (alpha (n + 1) k) := by
        rw [hαk]
        simp [P, zmap, evalInt]
      have hmuik := hmu i kf
      have hineq : |(approxPoly (n + 1)).derivative.eval (alpha (n + 1) k)|⁻¹ *
            |P.eval (alpha (n + 1) k)| ≤ mu i := by
        rw [← hvkf, ← hPev]
        exact hmuik
      have hkfIcc : k ∈ Finset.Icc 1 (n + 1) := Finset.mem_Icc.mpr ⟨hk1, hkn⟩
      have hD : (approxPoly (n + 1)).derivative.eval (alpha (n + 1) k) ≠ 0 :=
        derivative_eval_ne_zero (n := n) (k := k) hkfIcc
      have hDabs : 0 < |(approxPoly (n + 1)).derivative.eval (alpha (n + 1) k)| := abs_pos.mpr hD
      have hZ : |P.eval (alpha (n + 1) k)| ≤ mu i *
          |(approxPoly (n + 1)).derivative.eval (alpha (n + 1) k)| := by
        have hmul := mul_le_mul_of_nonneg_right hineq (le_of_lt hDabs)
        have hcancel :
            (|(approxPoly (n + 1)).derivative.eval (alpha (n + 1) k)|⁻¹ *
              |P.eval (alpha (n + 1) k)|) *
              |(approxPoly (n + 1)).derivative.eval (alpha (n + 1) k)| =
            |P.eval (alpha (n + 1) k)| := by
          field_simp [ne_of_gt hDabs]
        rwa [hcancel] at hmul
      exact (div_le_iff₀ hDabs).mpr hZ
    have hSn : ((fun k : ℕ =>
          |P.eval (alpha (n + 1) k)| /
            |(approxPoly (n + 1)).derivative.eval (alpha (n + 1) k)|) ''
        Set.Icc 1 (n + 1)).Nonempty := by
      refine ⟨(fun k : ℕ =>
          |P.eval (alpha (n + 1) k)| /
            |(approxPoly (n + 1)).derivative.eval (alpha (n + 1) k)|) 1, ?_⟩
      refine ⟨1, ?_, rfl⟩
      simp [Set.mem_Icc]
    have hsup : sSup ((fun k : ℕ =>
          |P.eval (alpha (n + 1) k)| /
            |(approxPoly (n + 1)).derivative.eval (alpha (n + 1) k)|) ''
        Set.Icc 1 (n + 1)) ≤ mu i := csSup_le hSn hSle
    have hb := hCi n hn P hdegP
    have hb' : wnorm n P ≤ (n : ℝ) ^ Ci * mu i := by
      exact le_trans hb (mul_le_mul_of_nonneg_left hsup hCi0)
    simpa [P] using hb'
  -- product over i
  have hprod1 : (∏ i : Fin (n + 1), wnorm n (zmap (Q i))) ≤
      (∏ i : Fin (n + 1), (n : ℝ) ^ Ci * mu i) := by
    refine Finset.prod_le_prod ?_ ?_
    · intro i hi
      exact wnorm_nonneg n (zmap (Q i))
    · intro i hi
      exact hnode i
  have hnn : 0 ≤ (n : ℝ) := hnpos0
  have hstep : ((n : ℝ) ^ Ci) ^ (n + 1) = (n : ℝ) ^ (Ci * ((n + 1 : ℕ) : ℝ)) := by
    calc
      ((n : ℝ) ^ Ci) ^ (n + 1) = ((n : ℝ) ^ Ci) ^ (((n + 1 : ℕ) : ℝ)) := by
        rw [Real.rpow_natCast]
      _ = (n : ℝ) ^ (Ci * ((n + 1 : ℕ) : ℝ)) := by
        rw [Real.rpow_mul hnn Ci ((n + 1 : ℕ) : ℝ)]
  have hprod2 : (∏ i : Fin (n + 1), wnorm n (zmap (Q i))) ≤
      (n : ℝ) ^ (Ci * ((n + 1 : ℕ) : ℝ)) * (∏ i : Fin (n + 1), mu i) := by
    calc
      (∏ i : Fin (n + 1), wnorm n (zmap (Q i)))
          ≤ ∏ i : Fin (n + 1), (n : ℝ) ^ Ci * mu i := hprod1
      _ = (∏ i : Fin (n + 1), (n : ℝ) ^ Ci) * (∏ i : Fin (n + 1), mu i) := by
            rw [Finset.prod_mul_distrib]
      _ = ((n : ℝ) ^ Ci) ^ (n + 1) * (∏ i : Fin (n + 1), mu i) := by
            congr 1
            rw [Finset.prod_const, Finset.card_univ]
            simp
      _ = (n : ℝ) ^ (Ci * ((n + 1 : ℕ) : ℝ)) * (∏ i : Fin (n + 1), mu i) := by
            rw [hstep]
  have hA0 : 0 ≤ (n : ℝ) ^ (Ci * ((n + 1 : ℕ) : ℝ)) := Real.rpow_nonneg hnpos0 _
  have hchain : (∏ i : Fin (n + 1), wnorm n (zmap (Q i))) ≤
      (n : ℝ) ^ (Ci * ((n + 1 : ℕ) : ℝ)) *
        (((n + 1 : ℕ) : ℝ) ^ (C0 * ((n + 1 : ℕ) : ℝ)) * Dval (n + 1) α v) := by
    exact le_trans hprod2 (mul_le_mul_of_nonneg_left hprod hA0)
  -- Dval upper bound from energy_half
  have hVpos : 0 < Vprod (n + 1) := Vprod_pos (n + 1) (by omega : 1 ≤ n + 1)
  have hdeq : Dval (n + 1) α v = (Vprod (n + 1))⁻¹ := by
    simpa [α, v] using (Dval_deriv_eq (n + 1) (by omega : 2 ≤ n + 1))
  let L : ℝ := x ^ (-Cd * x) * Real.exp (-((1 / 2 : ℝ) * x ^ 2 * energy))
  have hL : 0 < L := by
    have h1 : 0 < x ^ (-Cd * x) := Real.rpow_pos_of_pos hxpos _
    exact mul_pos h1 (Real.exp_pos _)
  have hE : L ≤ Vprod (n + 1) := by
    have hring : -((1 / 2 : ℝ) * x ^ 2 * energy) = -(1 / 2 : ℝ) * x ^ 2 * energy := by ring
    dsimp [L]
    rw [hring]
    simpa [x, Vprod] using hEd (n + 1) (by omega : 2 ≤ n + 1)
  have hVinv : (Vprod (n + 1))⁻¹ ≤ x ^ (Cd * x) *
      Real.exp ((1 / 2 : ℝ) * x ^ 2 * energy) := by
    have hinv := (inv_le_inv₀ hVpos hL).mpr hE
    have hB : L * (x ^ (Cd * x) * Real.exp ((1 / 2 : ℝ) * x ^ 2 * energy)) = 1 := by
      dsimp [L]
      calc
        (x ^ (-Cd * x) * Real.exp (-((1 / 2 : ℝ) * x ^ 2 * energy))) *
            (x ^ (Cd * x) * Real.exp ((1 / 2 : ℝ) * x ^ 2 * energy))
            = (x ^ (-Cd * x) * x ^ (Cd * x)) *
              (Real.exp (-((1 / 2 : ℝ) * x ^ 2 * energy)) *
                Real.exp ((1 / 2 : ℝ) * x ^ 2 * energy)) := by ring
        _ = 1 := by
          rw [← Real.rpow_add hxpos (-Cd * x) (Cd * x)]
          rw [← Real.exp_add]
          have hsum1 : -Cd * x + Cd * x = 0 := by ring
          have hsum2 : -((1 / 2 : ℝ) * x ^ 2 * energy) +
              (1 / 2 : ℝ) * x ^ 2 * energy = 0 := by ring
          rw [hsum1, hsum2]
          simp
    have hLinv : L⁻¹ = x ^ (Cd * x) * Real.exp ((1 / 2 : ℝ) * x ^ 2 * energy) := by
      exact inv_eq_of_mul_eq_one_right hB
    exact le_trans hinv (le_of_eq hLinv)
  have hDval : Dval (n + 1) α v ≤ x ^ (Cd * x) *
      Real.exp ((1 / 2 : ℝ) * x ^ 2 * energy) := by
    rw [hdeq]
    exact hVinv
  -- combine: express the chain in x-form
  have hchainx : (∏ i : Fin (n + 1), wnorm n (zmap (Q i))) ≤
      (n : ℝ) ^ (Ci * x) * (x ^ (C0 * x) * Dval (n + 1) α v) := by
    simpa [x] using hchain
  have hDvalx : x ^ (C0 * x) * Dval (n + 1) α v ≤ x ^ ((C0 + Cd) * x) *
      Real.exp ((1 / 2 : ℝ) * x ^ 2 * energy) := by
    have hmul := mul_le_mul_of_nonneg_left hDval (Real.rpow_nonneg hx0 (C0 * x))
    calc
      x ^ (C0 * x) * Dval (n + 1) α v ≤ x ^ (C0 * x) * (x ^ (Cd * x) *
          Real.exp ((1 / 2 : ℝ) * x ^ 2 * energy)) := hmul
      _ = x ^ (C0 * x) * x ^ (Cd * x) * Real.exp ((1 / 2 : ℝ) * x ^ 2 * energy) := by ring
      _ = x ^ ((C0 + Cd) * x) * Real.exp ((1 / 2 : ℝ) * x ^ 2 * energy) := by
            rw [← Real.rpow_add hxpos (C0 * x) (Cd * x)]
            congr 1
            ring
  have hA0x : 0 ≤ (n : ℝ) ^ (Ci * x) := Real.rpow_nonneg hnpos0 _
  have hchain1 : (∏ i : Fin (n + 1), wnorm n (zmap (Q i))) ≤
      (n : ℝ) ^ (Ci * x) * (x ^ ((C0 + Cd) * x) *
        Real.exp ((1 / 2 : ℝ) * x ^ 2 * energy)) := by
    exact le_trans hchainx (mul_le_mul_of_nonneg_left hDvalx hA0x)
  have hprodnp : (n : ℝ) ^ (Ci * x) ≤ (n : ℝ) ^ (Cnm * (n : ℝ)) := by
    simpa [x, hdR] using hCnm n hn
  have hnp : x ^ ((C0 + Cd) * x) ≤ (n : ℝ) ^ (Cnp * (n : ℝ)) := by
    simpa [x] using hCnp n hn
  have hpow1 : (n : ℝ) ^ (Ci * x) * (x ^ ((C0 + Cd) * x)) ≤
      (n : ℝ) ^ (Cnm * (n : ℝ)) * (n : ℝ) ^ (Cnp * (n : ℝ)) := by
    exact mul_le_mul hprodnp hnp (Real.rpow_nonneg hx0 ((C0 + Cd) * x))
      (Real.rpow_nonneg hnpos0 (Cnm * (n : ℝ)))
  have hA1 : 0 ≤ Real.exp ((1 / 2 : ℝ) * x ^ 2 * energy) := Real.exp_nonneg _
  have hchain2 : (∏ i : Fin (n + 1), wnorm n (zmap (Q i))) ≤
      (n : ℝ) ^ (Cnm * (n : ℝ)) * (n : ℝ) ^ (Cnp * (n : ℝ)) *
        Real.exp ((1 / 2 : ℝ) * x ^ 2 * energy) := by
    calc
      (∏ i : Fin (n + 1), wnorm n (zmap (Q i))) ≤
          (n : ℝ) ^ (Ci * x) * (x ^ ((C0 + Cd) * x) *
            Real.exp ((1 / 2 : ℝ) * x ^ 2 * energy)) := hchain1
      _ = ((n : ℝ) ^ (Ci * x) * x ^ ((C0 + Cd) * x)) *
            Real.exp ((1 / 2 : ℝ) * x ^ 2 * energy) := by ring
      _ ≤ ((n : ℝ) ^ (Cnm * (n : ℝ)) * (n : ℝ) ^ (Cnp * (n : ℝ))) *
            Real.exp ((1 / 2 : ℝ) * x ^ 2 * energy) := by
            exact mul_le_mul_of_nonneg_right hpow1 hA1
      _ = (n : ℝ) ^ (Cnm * (n : ℝ)) * (n : ℝ) ^ (Cnp * (n : ℝ)) *
            Real.exp ((1 / 2 : ℝ) * x ^ 2 * energy) := by ring
  -- split the exponential
  have hsplit : Real.exp ((1 / 2 : ℝ) * x ^ 2 * energy) =
      Real.exp ((1 / 2 : ℝ) * (n : ℝ) ^ 2 * energy) *
        Real.exp (((n : ℝ) + (1 / 2 : ℝ)) * energy) := by
    have harg : (1 / 2 : ℝ) * x ^ 2 * energy =
        (1 / 2 : ℝ) * (n : ℝ) ^ 2 * energy + ((n : ℝ) + (1 / 2 : ℝ)) * energy := by
      dsimp [x]
      rw [hdR]
      ring
    rw [harg, Real.exp_add]
  have hCexp' : Real.exp (((n : ℝ) + (1 / 2 : ℝ)) * energy) ≤
      (n : ℝ) ^ (Cexp * (n : ℝ)) := hCexp n hn
  have hpre : 0 ≤ (n : ℝ) ^ (Cnm * (n : ℝ)) * (n : ℝ) ^ (Cnp * (n : ℝ)) *
      Real.exp ((1 / 2 : ℝ) * (n : ℝ) ^ 2 * energy) := by positivity
  have hchain3 : (∏ i : Fin (n + 1), wnorm n (zmap (Q i))) ≤
      (n : ℝ) ^ (Cnm * (n : ℝ)) * (n : ℝ) ^ (Cnp * (n : ℝ)) *
        Real.exp ((1 / 2 : ℝ) * (n : ℝ) ^ 2 * energy) *
        (n : ℝ) ^ (Cexp * (n : ℝ)) := by
    calc
      (∏ i : Fin (n + 1), wnorm n (zmap (Q i))) ≤
          (n : ℝ) ^ (Cnm * (n : ℝ)) * (n : ℝ) ^ (Cnp * (n : ℝ)) *
            Real.exp ((1 / 2 : ℝ) * x ^ 2 * energy) := hchain2
      _ = (n : ℝ) ^ (Cnm * (n : ℝ)) * (n : ℝ) ^ (Cnp * (n : ℝ)) *
            (Real.exp ((1 / 2 : ℝ) * (n : ℝ) ^ 2 * energy) *
              Real.exp (((n : ℝ) + (1 / 2 : ℝ)) * energy)) := by
            rw [hsplit]
      _ ≤ (n : ℝ) ^ (Cnm * (n : ℝ)) * (n : ℝ) ^ (Cnp * (n : ℝ)) *
            Real.exp ((1 / 2 : ℝ) * (n : ℝ) ^ 2 * energy) *
            (n : ℝ) ^ (Cexp * (n : ℝ)) := by
            -- multiply hCexp' by the nonneg prefix
            have hm := mul_le_mul_of_nonneg_left hCexp' hpre
            -- hm : prefix · exp((n+½)e) ≤ prefix · n^(Cexp n)
            nlinarith
  have hcomb : (n : ℝ) ^ (Cnm * (n : ℝ)) * (n : ℝ) ^ (Cnp * (n : ℝ)) *
        (n : ℝ) ^ (Cexp * (n : ℝ)) = (n : ℝ) ^ ((Cnm + Cnp + Cexp) * (n : ℝ)) := by
    calc
      (n : ℝ) ^ (Cnm * (n : ℝ)) * (n : ℝ) ^ (Cnp * (n : ℝ)) * (n : ℝ) ^ (Cexp * (n : ℝ))
          = (n : ℝ) ^ (Cnm * (n : ℝ) + Cnp * (n : ℝ)) * (n : ℝ) ^ (Cexp * (n : ℝ)) := by
            rw [← Real.rpow_add hnpos (Cnm * (n : ℝ)) (Cnp * (n : ℝ))]
      _ = (n : ℝ) ^ (Cnm * (n : ℝ) + Cnp * (n : ℝ) + Cexp * (n : ℝ)) := by
            rw [← Real.rpow_add hnpos (Cnm * (n : ℝ) + Cnp * (n : ℝ)) (Cexp * (n : ℝ))]
      _ = (n : ℝ) ^ ((Cnm + Cnp + Cexp) * (n : ℝ)) := by
            congr 1
            ring
  have hfin : (∏ i : Fin (n + 1), wnorm n (zmap (Q i))) ≤
      (n : ℝ) ^ (C * (n : ℝ)) *
        Real.exp ((1 / 2 : ℝ) * (n : ℝ) ^ 2 * energy) := by
    calc
      (∏ i : Fin (n + 1), wnorm n (zmap (Q i))) ≤
          (n : ℝ) ^ (Cnm * (n : ℝ)) * (n : ℝ) ^ (Cnp * (n : ℝ)) *
            Real.exp ((1 / 2 : ℝ) * (n : ℝ) ^ 2 * energy) *
            (n : ℝ) ^ (Cexp * (n : ℝ)) := hchain3
      _ = (n : ℝ) ^ (Cnm * (n : ℝ)) * (n : ℝ) ^ (Cnp * (n : ℝ)) *
            (n : ℝ) ^ (Cexp * (n : ℝ)) *
            Real.exp ((1 / 2 : ℝ) * (n : ℝ) ^ 2 * energy) := by ring
      _ = (n : ℝ) ^ ((Cnm + Cnp + Cexp) * (n : ℝ)) *
            Real.exp ((1 / 2 : ℝ) * (n : ℝ) ^ 2 * energy) := by
            rw [hcomb]
      _ = (n : ℝ) ^ (C * (n : ℝ)) *
            Real.exp ((1 / 2 : ℝ) * (n : ℝ) ^ 2 * energy) := by
            simp [C]
  refine ⟨Q, hlin, ?deg, hfin⟩
  intro i
  have hd := hdegQ i
  have hsub : (n + 1) - 1 = n := by omega
  rw [hsub] at hd
  exact hd


end Submission.HilbertMink
