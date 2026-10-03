import Mathlib
import Submission.Work.FIChain.Defs

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace Work.FIChain

open Finset MeasureTheory
open Submission.ASP

noncomputable section

/-! ## Step 1: the `y`-smoothed (3.4) with the `S₃` estimate in signed form

`Submission.ASP.abs_S_bound_y_smoothed` uses the `|S₃|`-inner bound `∫_Y^{eY}|S₃|/y ≤ E₅`.  Here the
`S₃`-term is kept **signed**: from `S_eq_y_smoothed` and `∫_Y^{eY}dy/y = 1` we write

`S(x;Z) − H·A(x) = ∫_Y^{eY}((T − H·A) − T₂ + S₂ + S₁)/y + ∫_Y^{eY} S₃/y`,

bound the first integral by the pointwise `|T−HA| + |T₂| + |S₁|` (estimates (4.5), (5.1), (6.6)) plus
`∫|S₂|/y ≤ E₄` (7.2), and the second by `|∫S₃/y| ≤ E₅` (8.5, signed). -/
private theorem abs_S_bound_y_smoothed_signed (a lam : ℕ → ℝ) (N : ℕ) (hN : 1 ≤ N)
    {Y s z H E1 E2 E3 E4 E5 : ℝ}
    (hY : 0 < Y) (hs : 1 ≤ s) (hz : 0 < z)
    (hT : ∀ y ∈ Set.Icc Y (Real.exp 1 * Y),
      |Tsum a lam (N : ℝ) y - H * Acount a (N : ℝ)| ≤ E1)
    (hT2 : ∀ y ∈ Set.Icc Y (Real.exp 1 * Y), |Tsum2 a lam (N : ℝ) y z| ≤ E2)
    (hS1 : ∀ y ∈ Set.Icc Y (Real.exp 1 * Y), |S1 a lam N (s * y) (s * z)| ≤ E3)
    (hS2 : (∫ y in Y..Real.exp 1 * Y, |S2 a lam N y z (s * y)| / y) ≤ E4)
    (hS3 : |(∫ y in Y..Real.exp 1 * Y, S3 a lam N z (s * y) (s * z) / y)| ≤ E5)
    (hE : 0 ≤ E1 + E2 + E3) (hE4 : 0 ≤ E4) (hE5 : 0 ≤ E5) :
    |(∑ n ∈ Finset.Icc 1 N, a n * rhoOf lam n *
        (if z < (n : ℝ) then ArithmeticFunction.vonMangoldt n else 0))
      - H * Acount a (N : ℝ)| ≤ E1 + E2 + E3 + E4 + E5 := by
  have hYa : Y ≤ Real.exp 1 * Y := le_exp_mul_self hY
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hL := S_eq_y_smoothed a lam N hN hY hs hz
  have hHA : H * Acount a (N : ℝ)
      = ∫ y in Y..Real.exp 1 * Y, (H * Acount a (N : ℝ)) / y := by
    have hfun : (fun y : ℝ => H * Acount a (N : ℝ) / y)
        = fun y => (H * Acount a (N : ℝ)) * (1 / y) := by funext y; ring
    rw [hfun, intervalIntegral.integral_const_mul, integral_one_div_exp_mul Y hY, mul_one]
  set F : ℝ → ℝ := fun y => (Tsum a lam (N : ℝ) y - Tsum2 a lam (N : ℝ) y z
        + S2 a lam N y z (s * y) + S3 a lam N z (s * y) (s * z)
        + S1 a lam N (s * y) (s * z)) / y with hF
  set g1 : ℝ → ℝ := fun y => ((Tsum a lam (N : ℝ) y - H * Acount a (N : ℝ))
        - Tsum2 a lam (N : ℝ) y z + S2 a lam N y z (s * y)
        + S1 a lam N (s * y) (s * z)) / y with hg1
  set g2 : ℝ → ℝ := fun y => S3 a lam N z (s * y) (s * z) / y with hg2
  have hT' := intervalIntegrable_Tsum_div a lam N hY
  have hT2' := intervalIntegrable_Tsum2_div a lam N z hY
  have hS2' := intervalIntegrable_S2_div (z := z) a lam N hs hY
  have hS3' := intervalIntegrable_S3_div (z := z) a lam N hs hY
  have hS1' := intervalIntegrable_S1_div (z := z) a lam N hs hY
  have hHAint : IntervalIntegrable (fun y : ℝ => (H * Acount a (N : ℝ)) / y)
      volume Y (Real.exp 1 * Y) :=
    intervalIntegrable_div_of_bound' (C := |H * Acount a (N : ℝ)|)
      (f := fun _ : ℝ => H * Acount a (N : ℝ)) measurable_const hY (fun u _ => le_rfl)
  have hFint : IntervalIntegrable F volume Y (Real.exp 1 * Y) := by
    rw [hF]
    have hcongr : (fun y : ℝ => (Tsum a lam (N : ℝ) y - Tsum2 a lam (N : ℝ) y z
          + S2 a lam N y z (s * y) + S3 a lam N z (s * y) (s * z)
          + S1 a lam N (s * y) (s * z)) / y)
        = fun y => Tsum a lam (N : ℝ) y / y - Tsum2 a lam (N : ℝ) y z / y
          + S2 a lam N y z (s * y) / y + S3 a lam N z (s * y) (s * z) / y
          + S1 a lam N (s * y) (s * z) / y := by
      funext y; ring
    rw [hcongr]
    exact (((hT'.sub hT2').add hS2').add hS3').add hS1'
  have hg1int : IntervalIntegrable g1 volume Y (Real.exp 1 * Y) := by
    rw [hg1]
    have hcongr : (fun y : ℝ => ((Tsum a lam (N : ℝ) y - H * Acount a (N : ℝ))
          - Tsum2 a lam (N : ℝ) y z + S2 a lam N y z (s * y)
          + S1 a lam N (s * y) (s * z)) / y)
        = fun y => (Tsum a lam (N : ℝ) y - H * Acount a (N : ℝ)) / y
          - Tsum2 a lam (N : ℝ) y z / y + S2 a lam N y z (s * y) / y
          + S1 a lam N (s * y) (s * z) / y := by
      funext y; ring
    rw [hcongr]
    have hTsub : IntervalIntegrable
        (fun y : ℝ => (Tsum a lam (N : ℝ) y - H * Acount a (N : ℝ)) / y)
        volume Y (Real.exp 1 * Y) := by
      have hcongr2 : (fun y : ℝ => (Tsum a lam (N : ℝ) y - H * Acount a (N : ℝ)) / y)
          = fun y => Tsum a lam (N : ℝ) y / y - (H * Acount a (N : ℝ)) / y := by
        funext y; ring
      rw [hcongr2]
      exact hT'.sub hHAint
    exact ((hTsub.sub hT2').add hS2').add hS1'
  have hg2int : IntervalIntegrable g2 volume Y (Real.exp 1 * Y) := by
    rw [hg2]; exact hS3'
  have hmain : (∑ n ∈ Finset.Icc 1 N, a n * rhoOf lam n *
        (if z < (n : ℝ) then ArithmeticFunction.vonMangoldt n else 0))
      - H * Acount a (N : ℝ)
      = (∫ y in Y..Real.exp 1 * Y, g1 y) + (∫ y in Y..Real.exp 1 * Y, g2 y) := by
    rw [hL, hHA]
    change (∫ y in Y..Real.exp 1 * Y, F y)
        - (∫ y in Y..Real.exp 1 * Y, (H * Acount a (N : ℝ)) / y)
      = (∫ y in Y..Real.exp 1 * Y, g1 y) + (∫ y in Y..Real.exp 1 * Y, g2 y)
    rw [← intervalIntegral.integral_sub hFint hHAint]
    have hcongr : (fun y : ℝ => F y - (H * Acount a (N : ℝ)) / y) = fun y => g1 y + g2 y := by
      simp only [hF, hg1, hg2]
      funext y; ring
    rw [hcongr]
    exact intervalIntegral.integral_add hg1int hg2int
  have hg1absint : IntervalIntegrable (fun y => |g1 y|) volume Y (Real.exp 1 * Y) :=
    hg1int.abs
  have iA : IntervalIntegrable (fun y : ℝ => (E1 + E2 + E3) / y) volume Y (Real.exp 1 * Y) :=
    intervalIntegrable_div_of_bound' (C := |E1 + E2 + E3|)
      (f := fun _ : ℝ => E1 + E2 + E3) measurable_const hY (fun u _ => le_rfl)
  have iB : IntervalIntegrable (fun y : ℝ => |S2 a lam N y z (s * y)| / y)
      volume Y (Real.exp 1 * Y) :=
    intervalIntegrable_div_of_bound' ((measurable_S2_y a lam N hs0).abs) hY
      (fun u _ => by simpa using abs_S2_bd a lam N u z (s * u))
  have imaj : IntervalIntegrable
      (fun y : ℝ => (E1 + E2 + E3) / y + |S2 a lam N y z (s * y)| / y)
      volume Y (Real.exp 1 * Y) := iA.add iB
  have hmono : (∫ y in Y..Real.exp 1 * Y, |g1 y|)
      ≤ ∫ y in Y..Real.exp 1 * Y, ((E1 + E2 + E3) / y + |S2 a lam N y z (s * y)| / y) := by
    refine intervalIntegral.integral_mono_ae_restrict hYa hg1absint imaj ?_
    change ∀ᵐ x ∂(volume.restrict (Set.Icc Y (Real.exp 1 * Y))),
      |g1 x| ≤ (E1 + E2 + E3) / x + |S2 a lam N x z (s * x)| / x
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    refine Filter.Eventually.of_forall (fun y hy => ?_)
    have hy0 : 0 < y := lt_of_lt_of_le hY hy.1
    have hT1 : |Tsum a lam (N : ℝ) y - H * Acount a (N : ℝ)| ≤ E1 := hT y hy
    have hT22 : |Tsum2 a lam (N : ℝ) y z| ≤ E2 := hT2 y hy
    have hS11 : |S1 a lam N (s * y) (s * z)| ≤ E3 := hS1 y hy
    have h1 : |(Tsum a lam (N : ℝ) y - H * Acount a (N : ℝ)) - Tsum2 a lam (N : ℝ) y z
          + S2 a lam N y z (s * y) + S1 a lam N (s * y) (s * z)|
        ≤ E1 + E2 + |S2 a lam N y z (s * y)| + E3 := by
      have e1 := abs_add_le
        ((Tsum a lam (N : ℝ) y - H * Acount a (N : ℝ)) - Tsum2 a lam (N : ℝ) y z
          + S2 a lam N y z (s * y)) (S1 a lam N (s * y) (s * z))
      have e2 := abs_add_le
        ((Tsum a lam (N : ℝ) y - H * Acount a (N : ℝ)) - Tsum2 a lam (N : ℝ) y z)
        (S2 a lam N y z (s * y))
      have e3 : |(Tsum a lam (N : ℝ) y - H * Acount a (N : ℝ)) - Tsum2 a lam (N : ℝ) y z|
          ≤ |Tsum a lam (N : ℝ) y - H * Acount a (N : ℝ)| + |Tsum2 a lam (N : ℝ) y z| := by
        have := abs_add_le (Tsum a lam (N : ℝ) y - H * Acount a (N : ℝ))
          (-(Tsum2 a lam (N : ℝ) y z))
        rwa [abs_neg, sub_eq_add_neg] at this
      linarith
    rw [hg1, abs_div, abs_of_pos hy0]
    rw [div_le_iff₀ hy0]
    have hb : ((E1 + E2 + E3) / y + |S2 a lam N y z (s * y)| / y) * y
        = E1 + E2 + E3 + |S2 a lam N y z (s * y)| := by
      rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hy0), div_mul_cancel₀ _ (ne_of_gt hy0)]
    rw [hb]
    linarith
  have hvalA : (∫ y in Y..Real.exp 1 * Y, (E1 + E2 + E3) / y) = E1 + E2 + E3 := by
    have hfun : (fun y : ℝ => (E1 + E2 + E3) / y)
        = fun y => (E1 + E2 + E3) * (1 / y) := by funext y; ring
    rw [hfun, intervalIntegral.integral_const_mul, integral_one_div_exp_mul Y hY, mul_one]
  have hval : (∫ y in Y..Real.exp 1 * Y,
        ((E1 + E2 + E3) / y + |S2 a lam N y z (s * y)| / y))
      = (E1 + E2 + E3) + (∫ y in Y..Real.exp 1 * Y, |S2 a lam N y z (s * y)| / y) := by
    rw [intervalIntegral.integral_add iA iB, hvalA]
  have hInt1 : (∫ y in Y..Real.exp 1 * Y, |g1 y|) ≤ (E1 + E2 + E3) + E4 := by
    calc (∫ y in Y..Real.exp 1 * Y, |g1 y|)
        ≤ ∫ y in Y..Real.exp 1 * Y, ((E1 + E2 + E3) / y + |S2 a lam N y z (s * y)| / y) := hmono
      _ = (E1 + E2 + E3) + (∫ y in Y..Real.exp 1 * Y, |S2 a lam N y z (s * y)| / y) := hval
      _ ≤ (E1 + E2 + E3) + E4 := by linarith [hS2]
  rw [hmain]
  calc |(∫ y in Y..Real.exp 1 * Y, g1 y) + (∫ y in Y..Real.exp 1 * Y, g2 y)|
      ≤ |(∫ y in Y..Real.exp 1 * Y, g1 y)| + |(∫ y in Y..Real.exp 1 * Y, g2 y)| := abs_add_le _ _
    _ ≤ (∫ y in Y..Real.exp 1 * Y, |g1 y|) + E5 := by
        refine add_le_add (intervalIntegral.abs_integral_le_integral_abs hYa) ?_
        exact hS3
    _ ≤ ((E1 + E2 + E3) + E4) + E5 := by linarith [hInt1]
    _ = E1 + E2 + E3 + E4 + E5 := by ring

/-! ## Step 2: the companion's Theorem 1 with the signed (8.5)

This is `Submission.ASP.TheoremOne_of_estimates` with `abs_S_bound_y_smoothed` replaced by the signed
version above; the completion step (3.5) `S(x) − S(x;Z) ≤ log Z · A(Z)` is unchanged. -/
private theorem TheoremOne_of_estimates_signed (a lam : ℕ → ℝ) (N Z Δ : ℕ)
    {H Y s z E1 E2 E3 E4 E5 E6 : ℝ}
    (hN : 1 ≤ N) (hY : 0 < Y) (hs : 1 ≤ s) (hz : 0 < z) (hzz : z = (Z : ℝ))
    (hZ1 : 1 ≤ Z) (hZN : Z ≤ N) (hΔZ : Δ ≤ Z)
    (ha_sq : ∀ n : ℕ, ¬ Squarefree n → a n = 0) (ha0 : ∀ n : ℕ, 0 ≤ a n)
    (hlam1 : lam 1 = 1) (hlam_supp : ∀ ν : ℕ, Δ < ν → lam ν = 0)
    (hT : ∀ y ∈ Set.Icc Y (Real.exp 1 * Y),
      |Tsum a lam (N : ℝ) y - H * Acount a (N : ℝ)| ≤ E1)
    (hT2 : ∀ y ∈ Set.Icc Y (Real.exp 1 * Y), |Tsum2 a lam (N : ℝ) y z| ≤ E2)
    (hS1 : ∀ y ∈ Set.Icc Y (Real.exp 1 * Y), |S1 a lam N (s * y) (s * z)| ≤ E3)
    (hS2 : (∫ y in Y..Real.exp 1 * Y, |S2 a lam N y z (s * y)| / y) ≤ E4)
    (hS3 : |(∫ y in Y..Real.exp 1 * Y, S3 a lam N z (s * y) (s * z) / y)| ≤ E5)
    (hE : 0 ≤ E1 + E2 + E3) (hE4 : 0 ≤ E4) (hE5 : 0 ≤ E5)
    (hE6 : Real.log (Z : ℝ) * Acount a (Z : ℝ) ≤ E6) :
    |(∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, Real.log (p : ℝ) * a p)
        - H * Acount a (N : ℝ)|
      ≤ (E1 + E2 + E3 + E4 + E5) + E6 := by
  have hS := abs_S_bound_y_smoothed_signed a lam N hN hY hs hz hT hT2 hS1 hS2 hS3 hE hE4 hE5
  have hS' : |(∑ n ∈ Finset.Icc 1 N, a n * rhoOf lam n
      * (if Z < n then ArithmeticFunction.vonMangoldt n else 0)) - H * Acount a (N : ℝ)|
      ≤ E1 + E2 + E3 + E4 + E5 := by
    rw [hzz] at hS
    have heq : (∑ n ∈ Finset.Icc 1 N, a n * rhoOf lam n
        * (if (Z : ℝ) < (n : ℝ) then ArithmeticFunction.vonMangoldt n else 0))
        = ∑ n ∈ Finset.Icc 1 N, a n * rhoOf lam n
        * (if Z < n then ArithmeticFunction.vonMangoldt n else 0) := by
      refine Finset.sum_congr rfl fun n _ => ?_
      by_cases h : Z < n
      · rw [if_pos h, if_pos (by rw [Nat.cast_lt]; exact h)]
      · rw [if_neg h, if_neg (by rw [Nat.cast_lt]; exact h)]
    rwa [heq] at hS
  have hmain := primeSum_bound_of_S_bound a lam N Z Δ hZ1 hZN hΔZ ha_sq ha0 hlam1 hlam_supp hS'
  linarith [hmain, hE6]

/-- **The companion's Theorem 2 for the FI sequence, with the `S₃` estimate in *signed* form.**

This is `Submission.ASP.FI_primeSum_of_estimates` (`Submission/ASP/S27.lean`) verbatim, except
that the `(8.5)` hypothesis is the *signed* integral bound
`|∫_Y^{eY} S₃(a,λ,N,z,s·y,s·z)/y| ≤ E5` instead of the `|S₃|`-inner bound
`∫_Y^{eY} |S₃(...)|/y ≤ E5`.  The conclusion has the *same* right-hand side
`(E1+E2+E3+E4+E5) + E6 + |Htil|·G·Acount FIa N·δ`.

The proof is the mechanical copy of the three-step chain
`Submission.ASP.Smooth.abs_S_bound_y_smoothed` → `Submission.ASP.S12.TheoremOne_of_estimates` →
`Submission.ASP.S27.FI_primeSum_of_estimates` with the signed `hS3`.  In
`abs_S_bound_y_smoothed` the `S₃`-term is used only in the last step; the signed version instead
writes the identity
`∑_{n≤N} aₙρₙΛ(n>z) − H·A(N) = ∫_Y^{eY}((T−H·A) − T2 + S2 + S1)/y + ∫_Y^{eY} S₃/y`
(from `S_eq_y_smoothed` and `∫_Y^{eY} dy/y = 1`), bounds the first integral by `E1+E2+E3+E4`
(pointwise `|T−HA|+|T2|+|S1|` plus `∫|S2|/y ≤ E4`) via
`intervalIntegral.abs_integral_le_integral_abs`, and the second by `E5`.  Everything needed is
public in `Submission.ASP` (`S_eq_y_smoothed`, `abs_S3_bd`, `intervalIntegrable_S3_div`,
`integral_one_div_exp_mul`, `primeSum_bound_of_S_bound`, `transfer_abs`, …); the three
intermediate signed statements may be private lemmas in the same file. -/
theorem FI_primeSum_of_estimates_signed (lam : ℕ → ℝ) (N Z Δ : ℕ)
    {Htil G H E1 E2 E3 E4 E5 E6 δ Y s z : ℝ}
    (hN : 1 ≤ N) (hY : 0 < Y) (hs : 1 ≤ s) (hz : 0 < z) (hzz : z = (Z : ℝ))
    (hZ1 : 1 ≤ Z) (hZN : Z ≤ N) (hΔZ : Δ ≤ Z)
    (hlam1 : lam 1 = 1) (hlam_supp : ∀ ν : ℕ, Δ < ν → lam ν = 0)
    (hT : ∀ y ∈ Set.Icc Y (Real.exp 1 * Y),
      |Submission.ASP.Tsum (Submission.ASP.atil Submission.ASP.FIa) lam (N : ℝ) y
        - Htil * Submission.ASP.Acount (Submission.ASP.atil Submission.ASP.FIa) (N : ℝ)| ≤ E1)
    (hT2 : ∀ y ∈ Set.Icc Y (Real.exp 1 * Y),
      |Submission.ASP.Tsum2 (Submission.ASP.atil Submission.ASP.FIa) lam (N : ℝ) y z| ≤ E2)
    (hS1 : ∀ y ∈ Set.Icc Y (Real.exp 1 * Y),
      |Submission.ASP.S1 (Submission.ASP.atil Submission.ASP.FIa) lam N (s * y) (s * z)| ≤ E3)
    (hS2 : (∫ y in Y..Real.exp 1 * Y,
      |Submission.ASP.S2 (Submission.ASP.atil Submission.ASP.FIa) lam N y z (s * y)| / y) ≤ E4)
    (hS3 : |(∫ y in Y..Real.exp 1 * Y,
      Submission.ASP.S3 (Submission.ASP.atil Submission.ASP.FIa) lam N z (s * y) (s * z) / y)| ≤ E5)
    (hE : 0 ≤ E1 + E2 + E3) (hE4 : 0 ≤ E4) (hE5 : 0 ≤ E5)
    (hE6 : Real.log (Z : ℝ) * Submission.ASP.Acount (Submission.ASP.atil Submission.ASP.FIa) (Z : ℝ)
      ≤ E6)
    (hH : Htil * G = H)
    (h912 : |Submission.ASP.Acount (Submission.ASP.atil Submission.ASP.FIa) (N : ℝ)
        - G * Submission.ASP.Acount Submission.ASP.FIa (N : ℝ)|
      ≤ G * Submission.ASP.Acount Submission.ASP.FIa (N : ℝ) * δ) :
    |(∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, Real.log (p : ℝ) * Submission.ASP.FIa p)
        - H * Submission.ASP.Acount Submission.ASP.FIa (N : ℝ)|
      ≤ (E1 + E2 + E3 + E4 + E5) + E6
        + |Htil| * G * Submission.ASP.Acount Submission.ASP.FIa (N : ℝ) * δ := by
  have hsq : ∀ n : ℕ, ¬ Squarefree n → (Submission.ASP.atil Submission.ASP.FIa) n = 0 := by
    intro n hn
    rw [Submission.ASP.atil,
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree hn]
    ring
  have hT1 := TheoremOne_of_estimates_signed (Submission.ASP.atil Submission.ASP.FIa) lam N Z Δ
    hN hY hs hz hzz hZ1 hZN hΔZ hsq
    (Submission.ASP.atil_nonneg Submission.ASP.FIa_nonneg) hlam1 hlam_supp
    hT hT2 hS1 hS2 hS3 hE hE4 hE5 hE6
  have hprime : (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
        Real.log (p : ℝ) * Submission.ASP.atil Submission.ASP.FIa p)
      = ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, Real.log (p : ℝ) * Submission.ASP.FIa p := by
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mem_filter] at hp
    have hμ : ArithmeticFunction.moebius p = -1 := ArithmeticFunction.moebius_apply_prime hp.2
    rw [Submission.ASP.atil, hμ]
    ring
  rw [hprime] at hT1
  exact Submission.ASP.transfer_abs hT1 hH h912

end

end Work.FIChain
