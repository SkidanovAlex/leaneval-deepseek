/-
# The core estimate `A(N) - N L(1,χ) = O(√q log q √N)`
-/
import Mathlib
import Submission.Work.LinnikAreas.efunAux
import Submission.Work.LinnikAreas.efunAsumDiv
import Submission.Work.LinnikAreas.efunHyperbola

namespace Work.LinnikAreas

open DirichletCharacter
open scoped BigOperators

noncomputable section

variable {q : ℕ} [NeZero q]

theorem asum_sub_LFunction_bound (χ : DirichletCharacter ℂ q) (hq : 2 ≤ q) {B₁ B₂ : ℝ}
    (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hPV : ∀ y : ℕ, ‖chiPrefix χ y‖ ≤ B₁ * Real.sqrt (q:ℝ) * Real.log (2*(q:ℝ)+2))
    (hLS : ∀ M : ℕ, 1 ≤ M →
      ‖(∑ n ∈ Finset.Icc 1 M, (χ (n : ZMod q) : ℂ) / (n:ℂ)) - LFunction χ 1‖
        ≤ B₂ * Real.sqrt (q:ℝ) * Real.log (2*(q:ℝ)+2) / (M:ℝ))
    {N : ℕ} (hN : 1 ≤ N) :
    ‖Asum χ (N:ℝ) - (N:ℂ) * LFunction χ 1‖
      ≤ (1 + 2*B₁ + 2*B₂) * Real.sqrt (q:ℝ) * Real.log (2*(q:ℝ)+2) * Real.sqrt (N:ℝ) := by
  obtain ⟨D, hD⟩ : ∃ D : ℕ, Nat.sqrt N = D := ⟨Nat.sqrt N, rfl⟩
  have hq1R : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast (by omega : 1 ≤ q)
  have hq2R : (2:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
  have hsq0 : (0:ℝ) ≤ Real.sqrt (q:ℝ) := Real.sqrt_nonneg _
  have hlog0 : (0:ℝ) ≤ Real.log (2*(q:ℝ)+2) := Real.log_nonneg (by linarith)
  have hsq1 : (1:ℝ) ≤ Real.sqrt (q:ℝ) := by
    calc (1:ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt (q:ℝ) := Real.sqrt_le_sqrt hq1R
  have hlog1 : (1:ℝ) ≤ Real.log (2*(q:ℝ)+2) := by
    have h4 : (4:ℝ) ≤ 2*(q:ℝ)+2 := by linarith
    have hlog4 : Real.log 4 ≤ Real.log (2*(q:ℝ)+2) := Real.log_le_log (by norm_num) h4
    have h24 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
    rw [h24] at hlog4
    nlinarith [Real.log_two_gt_d9]
  have hRL1 : (1:ℝ) ≤ Real.sqrt (q:ℝ) * Real.log (2*(q:ℝ)+2) := by nlinarith
  have hB1RL0 : (0:ℝ) ≤ B₁ * Real.sqrt (q:ℝ) * Real.log (2*(q:ℝ)+2) :=
    mul_nonneg (mul_nonneg hB₁ hsq0) hlog0
  have hB2RL0 : (0:ℝ) ≤ B₂ * Real.sqrt (q:ℝ) * Real.log (2*(q:ℝ)+2) :=
    mul_nonneg (mul_nonneg hB₂ hsq0) hlog0
  have hD1 : 1 ≤ D := by
    have h : 0 < Nat.sqrt N := Nat.sqrt_pos.mpr (by omega)
    omega
  have hDpos : (0:ℝ) < (D:ℝ) := by exact_mod_cast hD1
  have hDsq : ((D:ℝ))^2 ≤ (N:ℝ) := by
    have h := Nat.sqrt_le' N
    rw [hD] at h
    exact_mod_cast h
  have hDle : (D:ℝ) ≤ Real.sqrt (N:ℝ) := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    exact hDsq
  have hNlt : N < (D+1)^2 := by
    have h := Nat.lt_succ_sqrt N
    rw [hD] at h
    simpa [pow_two, Nat.succ_eq_add_one] using h
  have hD1R : (1:ℝ) ≤ (D:ℝ) := by exact_mod_cast hD1
  have hsqrt_lt : Real.sqrt (N:ℝ) < 2*(D:ℝ) := by
    have h1 : (N:ℝ) < ((D:ℝ)+1)^2 := by exact_mod_cast hNlt
    have h2 : Real.sqrt (N:ℝ) < Real.sqrt (((D:ℝ)+1)^2) := Real.sqrt_lt_sqrt (by positivity) h1
    rw [Real.sqrt_sq (by positivity)] at h2
    linarith
  have hNDle : (N:ℝ)/(D:ℝ) ≤ 2*Real.sqrt (N:ℝ) := by
    rw [div_le_iff₀ hDpos]
    have hsq : (N:ℝ) = Real.sqrt (N:ℝ)*Real.sqrt (N:ℝ) :=
      (Real.mul_self_sqrt (by positivity : (0:ℝ) ≤ (N:ℝ))).symm
    nlinarith [hsqrt_lt, Real.sqrt_nonneg (N:ℝ)]
  have hNdiv : N/(D+1) ≤ D := by
    have h : N/(D+1) < D+1 :=
      (Nat.div_lt_iff_lt_mul (k := D+1) (x := N) (y := D+1) (by omega)).mpr (by
        simpa [pow_two] using hNlt)
    omega
  let S : ℂ := ∑ d ∈ Finset.Icc 1 D, (χ (d:ZMod q) : ℂ) * ((N/d:ℕ):ℂ)
  let S' : ℂ := ∑ d ∈ Finset.Icc 1 D, (χ (d:ZMod q) : ℂ) * ((N:ℂ)/(d:ℂ))
  let T : ℂ := ∑ e ∈ Finset.Icc 1 (N/(D+1)), (chiPrefix χ (N/e) - chiPrefix χ D)
  have hS : S = ∑ d ∈ Finset.Icc 1 D, (χ (d:ZMod q) : ℂ) * ((N/d:ℕ):ℂ) := rfl
  have hS' : S' = ∑ d ∈ Finset.Icc 1 D, (χ (d:ZMod q) : ℂ) * ((N:ℂ)/(d:ℂ)) := rfl
  have hT : T = ∑ e ∈ Finset.Icc 1 (N/(D+1)), (chiPrefix χ (N/e) - chiPrefix χ D) := rfl
  have hAT : Asum χ (N:ℝ) = S + T := by
    have hA1 := efunAsumDiv χ N
    have hB1 := efunHyperbola χ N
    rw [hD] at hB1
    rw [hA1, hB1, hS, hT]
    congr 1
  have h1 : ‖S - S'‖ ≤ (D:ℝ) := by
    rw [hS, hS', ← Finset.sum_sub_distrib]
    have hterm : ∀ d ∈ Finset.Icc 1 D,
        ‖(χ (d:ZMod q) : ℂ) * ((N/d:ℕ):ℂ) - (χ (d:ZMod q) : ℂ) * ((N:ℂ)/(d:ℂ))‖ ≤ 1 := by
      intro d hd
      rw [Finset.mem_Icc] at hd
      rw [← mul_sub, norm_mul]
      calc ‖(χ (d:ZMod q) : ℂ)‖ * ‖((N/d:ℕ):ℂ) - (N:ℂ)/(d:ℂ)‖ ≤ 1 * 1 :=
            mul_le_mul (DirichletCharacter.norm_le_one χ _) (norm_div_sub_floor_le_one N d hd.1)
              (norm_nonneg _) (by norm_num)
        _ = 1 := by ring
    calc ‖∑ d ∈ Finset.Icc 1 D,
          ((χ (d:ZMod q) : ℂ) * ((N/d:ℕ):ℂ) - (χ (d:ZMod q) : ℂ) * ((N:ℂ)/(d:ℂ)))‖
        ≤ ∑ d ∈ Finset.Icc 1 D,
            ‖(χ (d:ZMod q) : ℂ) * ((N/d:ℕ):ℂ) - (χ (d:ZMod q) : ℂ) * ((N:ℂ)/(d:ℂ))‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _d ∈ Finset.Icc 1 D, (1:ℝ) := Finset.sum_le_sum hterm
      _ = (D:ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.card_Icc, Nat.add_sub_cancel]
  have h2 : ‖S' - (N:ℂ) * LFunction χ 1‖
      ≤ 2*B₂*Real.sqrt (q:ℝ)*Real.log (2*(q:ℝ)+2)*Real.sqrt (N:ℝ) := by
    have hSL : S' - (N:ℂ) * LFunction χ 1
        = (N:ℂ) * ((∑ d ∈ Finset.Icc 1 D, (χ (d:ZMod q):ℂ)/(d:ℂ)) - LFunction χ 1) := by
      rw [hS', mul_sub, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl (fun d hd => ?_)
      rw [Finset.mem_Icc] at hd
      have hdne : (d:ℂ) ≠ 0 := by
        have : d ≠ 0 := by omega
        exact_mod_cast this
      field_simp
    rw [hSL, norm_mul, Complex.norm_natCast]
    have htail := hLS D hD1
    have hstep : (N:ℝ) * (B₂ * Real.sqrt (q:ℝ) * Real.log (2*(q:ℝ)+2) / (D:ℝ))
        ≤ 2*B₂*Real.sqrt (q:ℝ)*Real.log (2*(q:ℝ)+2)*Real.sqrt (N:ℝ) := by
      have hrew : (N:ℝ) * (B₂ * Real.sqrt (q:ℝ) * Real.log (2*(q:ℝ)+2) / (D:ℝ))
          = B₂ * Real.sqrt (q:ℝ) * Real.log (2*(q:ℝ)+2) * ((N:ℝ)/(D:ℝ)) := by
        field_simp
      rw [hrew]
      calc B₂ * Real.sqrt (q:ℝ) * Real.log (2*(q:ℝ)+2) * ((N:ℝ)/(D:ℝ))
          ≤ B₂ * Real.sqrt (q:ℝ) * Real.log (2*(q:ℝ)+2) * (2*Real.sqrt (N:ℝ)) :=
            mul_le_mul_of_nonneg_left hNDle hB2RL0
        _ = 2*B₂*Real.sqrt (q:ℝ)*Real.log (2*(q:ℝ)+2)*Real.sqrt (N:ℝ) := by ring
    calc (N:ℝ) * ‖(∑ d ∈ Finset.Icc 1 D, (χ (d:ZMod q):ℂ)/(d:ℂ)) - LFunction χ 1‖
        ≤ (N:ℝ) * (B₂ * Real.sqrt (q:ℝ) * Real.log (2*(q:ℝ)+2) / (D:ℝ)) :=
          mul_le_mul_of_nonneg_left htail (Nat.cast_nonneg N)
      _ ≤ 2*B₂*Real.sqrt (q:ℝ)*Real.log (2*(q:ℝ)+2)*Real.sqrt (N:ℝ) := hstep
  have h3 : ‖T‖ ≤ 2*B₁*Real.sqrt (q:ℝ)*Real.log (2*(q:ℝ)+2)*Real.sqrt (N:ℝ) := by
    rw [hT]
    have hterm : ∀ e ∈ Finset.Icc 1 (N/(D+1)),
        ‖chiPrefix χ (N/e) - chiPrefix χ D‖
          ≤ 2*B₁*Real.sqrt (q:ℝ)*Real.log (2*(q:ℝ)+2) := by
      intro e _
      have h1' : ‖chiPrefix χ (N/e)‖ ≤ B₁ * Real.sqrt (q:ℝ) * Real.log (2*(q:ℝ)+2) := hPV _
      have h2' : ‖chiPrefix χ D‖ ≤ B₁ * Real.sqrt (q:ℝ) * Real.log (2*(q:ℝ)+2) := hPV _
      calc ‖chiPrefix χ (N/e) - chiPrefix χ D‖ ≤ ‖chiPrefix χ (N/e)‖ + ‖chiPrefix χ D‖ :=
            norm_sub_le _ _
        _ ≤ B₁ * Real.sqrt (q:ℝ) * Real.log (2*(q:ℝ)+2)
              + B₁ * Real.sqrt (q:ℝ) * Real.log (2*(q:ℝ)+2) := add_le_add h1' h2'
        _ = 2*B₁*Real.sqrt (q:ℝ)*Real.log (2*(q:ℝ)+2) := by ring
    have hcard : ((Finset.Icc 1 (N/(D+1))).card : ℝ) = ((N/(D+1) : ℕ) : ℝ) := by
      rw [Nat.card_Icc]
      simp
    have hNdivR : ((N/(D+1) : ℕ) : ℝ) ≤ (D:ℝ) := by exact_mod_cast hNdiv
    have h2B : (0:ℝ) ≤ 2*B₁*Real.sqrt (q:ℝ)*Real.log (2*(q:ℝ)+2) :=
      mul_nonneg (mul_nonneg (by linarith) hsq0) hlog0
    calc ‖∑ e ∈ Finset.Icc 1 (N/(D+1)), (chiPrefix χ (N/e) - chiPrefix χ D)‖
        ≤ ∑ e ∈ Finset.Icc 1 (N/(D+1)), ‖chiPrefix χ (N/e) - chiPrefix χ D‖ := norm_sum_le _ _
      _ ≤ ∑ _e ∈ Finset.Icc 1 (N/(D+1)), (2*B₁*Real.sqrt (q:ℝ)*Real.log (2*(q:ℝ)+2)) :=
          Finset.sum_le_sum hterm
      _ = ((N/(D+1) : ℕ) : ℝ) * (2*B₁*Real.sqrt (q:ℝ)*Real.log (2*(q:ℝ)+2)) := by
          rw [Finset.sum_const, nsmul_eq_mul, hcard]
      _ ≤ (D:ℝ) * (2*B₁*Real.sqrt (q:ℝ)*Real.log (2*(q:ℝ)+2)) :=
          mul_le_mul_of_nonneg_right hNdivR h2B
      _ ≤ 2*B₁*Real.sqrt (q:ℝ)*Real.log (2*(q:ℝ)+2)*Real.sqrt (N:ℝ) := by
          calc (D:ℝ) * (2*B₁*Real.sqrt (q:ℝ)*Real.log (2*(q:ℝ)+2))
              ≤ Real.sqrt (N:ℝ) * (2*B₁*Real.sqrt (q:ℝ)*Real.log (2*(q:ℝ)+2)) :=
                mul_le_mul_of_nonneg_right hDle h2B
            _ = 2*B₁*Real.sqrt (q:ℝ)*Real.log (2*(q:ℝ)+2)*Real.sqrt (N:ℝ) := by ring
  have hmain : Asum χ (N:ℝ) - (N:ℂ) * LFunction χ 1
      = (S - S') + (S' - (N:ℂ) * LFunction χ 1) + T := by
    rw [hAT]; ring
  calc ‖Asum χ (N:ℝ) - (N:ℂ) * LFunction χ 1‖
      = ‖(S - S') + (S' - (N:ℂ) * LFunction χ 1) + T‖ := by rw [hmain]
    _ ≤ ‖S - S'‖ + ‖S' - (N:ℂ) * LFunction χ 1‖ + ‖T‖ := by
        have ha := norm_add_le ((S - S') + (S' - (N:ℂ) * LFunction χ 1)) T
        have hb := norm_add_le (S - S') (S' - (N:ℂ) * LFunction χ 1)
        linarith
    _ ≤ (D:ℝ) + 2*B₂*Real.sqrt (q:ℝ)*Real.log (2*(q:ℝ)+2)*Real.sqrt (N:ℝ)
          + 2*B₁*Real.sqrt (q:ℝ)*Real.log (2*(q:ℝ)+2)*Real.sqrt (N:ℝ) := by
        linarith [h1, h2, h3]
    _ ≤ (1 + 2*B₁ + 2*B₂) * Real.sqrt (q:ℝ) * Real.log (2*(q:ℝ)+2) * Real.sqrt (N:ℝ) := by
        have hDle' : (D:ℝ) ≤ Real.sqrt (q:ℝ) * Real.log (2*(q:ℝ)+2) * Real.sqrt (N:ℝ) := by
          calc (D:ℝ) ≤ Real.sqrt (N:ℝ) := hDle
            _ ≤ Real.sqrt (q:ℝ) * Real.log (2*(q:ℝ)+2) * Real.sqrt (N:ℝ) := by nlinarith
        have hE : (1 + 2*B₁ + 2*B₂) * Real.sqrt (q:ℝ) * Real.log (2*(q:ℝ)+2) * Real.sqrt (N:ℝ)
            = Real.sqrt (q:ℝ) * Real.log (2*(q:ℝ)+2) * Real.sqrt (N:ℝ)
              + (2*B₂*Real.sqrt (q:ℝ)*Real.log (2*(q:ℝ)+2)*Real.sqrt (N:ℝ)
                + 2*B₁*Real.sqrt (q:ℝ)*Real.log (2*(q:ℝ)+2)*Real.sqrt (N:ℝ)) := by ring
        rw [hE]
        linarith [hDle']

end

end Work.LinnikAreas
