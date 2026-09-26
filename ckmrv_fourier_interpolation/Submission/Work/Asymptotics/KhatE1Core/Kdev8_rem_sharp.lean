import Mathlib
import Submission.Work.Asymptotics.KhatE1Defs
import Submission.Work.Asymptotics.funnelTailBasic
import Submission.Work.Asymptotics.KhatE1.KdevRemDefs
import Submission.Work.Asymptotics.KhatE1.E1combo8_bound
import Submission.Work.Asymptotics.KhatE1.Kdev8CoeffAux
import Submission.Work.Asymptotics.KhatE1.KdevE2fun_funnel
import Submission.Work.Asymptotics.KhatE1Core.Kdev8_matching_bridge
import Submission.Work.Asymptotics.KhatE1Core.KdevBracket_tail_bound

namespace Work.Asymptotics.KhatE1Core

open UpperHalfPlane

private lemma mono_expand (X S T E : ℝ) (hX : 0 ≤ X) (hS : 1 ≤ S) (hT : 1 ≤ T) (hE : 0 ≤ E)
    (C : ℝ) (hC : 0 ≤ C) {n n' m m' : ℝ} (hn : n ≤ n') (hm : m ≤ m') :
    C * X * S ^ n * T ^ m * E ≤ C * X * S ^ n' * T ^ m' * E := by
  have hS0 : (0:ℝ) ≤ S := le_trans zero_le_one hS
  have hT0 : (0:ℝ) ≤ T := le_trans zero_le_one hT
  have h1 : S ^ n ≤ S ^ n' := Real.rpow_le_rpow_of_exponent_le hS hn
  have h2 : T ^ m ≤ T ^ m' := Real.rpow_le_rpow_of_exponent_le hT hm
  have hS0' : (0:ℝ) ≤ S ^ n' := Real.rpow_nonneg hS0 _
  have hT0' : (0:ℝ) ≤ T ^ m' := Real.rpow_nonneg hT0 _
  have hT0m : (0:ℝ) ≤ T ^ m := Real.rpow_nonneg hT0 _
  have hCX : (0:ℝ) ≤ C * X := mul_nonneg hC hX
  calc C * X * S ^ n * T ^ m * E
      = (C * X) * (S ^ n * T ^ m) * E := by ring
    _ ≤ (C * X) * (S ^ n' * T ^ m') * E :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 hT0m hS0') hCX) hE
    _ = C * X * S ^ n' * T ^ m' * E := by ring

theorem Kdev8_rem_sharp (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        0 ≤ z.re → z.re ≤ 1 → z.im = t →
        ‖Work.Asymptotics.KhatE1.KdevRem ℓ τ z‖
          ≤ C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
              * Real.exp (-(2 * Real.pi * t)) := by
  obtain ⟨Cc, Nc, Mc, hCc, hNc, hMc, hbc⟩ := KdevBracket_tail_bound ℓ
  obtain ⟨Ce, Ne, Me, hCe, hNe, hMe, hbe⟩ := Work.Asymptotics.KhatE1.KdevE2fun_funnel ℓ
  refine ⟨Cc + 2 * Ce + 1, max Nc Ne, max Mc Me, by positivity,
    le_trans hNc (le_max_left _ _), le_trans hMc (le_max_left _ _), ?_⟩
  intro τ z t hF ht h0 h1 hzim
  have hτ2 : 2 ≤ τ.im := hF.2
  have hSh : Work.Asymptotics.Compact.Sh τ z ≠ 0 :=
    Work.Asymptotics.KhatE1.Sh_ne_zero_of_im_ge τ z hτ2 (by rw [hzim]; exact ht)
  have hJ : Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z := by
    intro h0'
    have hD : Work.Kernels.DeltaFun z ≠ 0 := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z
    have hS : Work.Asymptotics.Compact.Sh τ z = 0 := by
      rw [Work.Asymptotics.Compact.Sh, h0']
      rw [← Work.Kernels.ClassicalFacts.DeltaFun_mul_jInvariantFun z]
      ring
    exact hSh hS
  have hbridge : Work.Asymptotics.KhatE1.KdevRem ℓ τ z
      = Work.Asymptotics.KhatE1Core.Kdev8Bracket ℓ τ z / 2 := by
    rw [Work.Asymptotics.KhatE1Core.Kdev8Bracket_eq_two_KdevRem ℓ τ z hJ hSh]
    ring
  set X : ℝ := ‖Work.Kernels.qParamFun τ‖ with hXdef
  set S : ℝ := Work.Kernels.scale τ with hSdef
  set T : ℝ := 1 + t with hTdef
  set E : ℝ := Real.exp (-(2 * Real.pi * t)) with hEdef
  have hX0 : (0:ℝ) ≤ X := by rw [hXdef]; positivity
  have hS1 : (1:ℝ) ≤ S := by rw [hSdef]; exact Work.Kernels.one_le_scale τ
  have hT1 : (1:ℝ) ≤ T := by rw [hTdef]; linarith
  have hE0 : (0:ℝ) ≤ E := by rw [hEdef]; positivity
  have hE2 : ‖(Work.Residues.Ept z) ^ 2‖ = E := by
    rw [hEdef, norm_pow, Work.Residues.norm_Ept, hzim]
    rw [show Real.exp (-(Real.pi * t)) ^ 2 = Real.exp (-(2 * Real.pi * t)) by
      rw [sq, ← Real.exp_add]; congr 1; ring]
  have hb_c := hbc τ z t hF ht h0 h1 hzim
  have hb_e := hbe τ z t hF ht (by linarith) (by linarith) hzim
  have hsub : ‖2 * Work.Asymptotics.KhatE1.KdevE2 ℓ τ z * (Work.Residues.Ept z) ^ 2‖
      ≤ 2 * Ce * X * S ^ (max Nc Ne) * T ^ (max Mc Me) * E := by
    rw [show ‖2 * Work.Asymptotics.KhatE1.KdevE2 ℓ τ z * (Work.Residues.Ept z) ^ 2‖
        = 2 * (‖Work.Asymptotics.KhatE1.KdevE2 ℓ τ z‖ * E) by
          rw [norm_mul, norm_mul, hE2, show ‖(2:ℂ)‖ = 2 by norm_num]; ring]
    calc 2 * (‖Work.Asymptotics.KhatE1.KdevE2 ℓ τ z‖ * E)
        ≤ 2 * (Ce * X * S ^ Ne * T ^ Me * E) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          rw [hXdef, hSdef, hTdef, hEdef]
          exact mul_le_mul_of_nonneg_right hb_e (Real.exp_nonneg _)
      _ = 2 * Ce * X * S ^ Ne * T ^ Me * E := by ring
      _ ≤ 2 * Ce * X * S ^ (max Nc Ne) * T ^ (max Mc Me) * E :=
          mono_expand X S T E hX0 hS1 hT1 hE0 (2 * Ce) (by positivity)
            (le_max_right Nc Ne) (le_max_right Mc Me)
  have hmain : Cc * X * S ^ Nc * T ^ Mc * E
      ≤ Cc * X * S ^ (max Nc Ne) * T ^ (max Mc Me) * E :=
    mono_expand X S T E hX0 hS1 hT1 hE0 Cc hCc.le (le_max_left Nc Ne) (le_max_left Mc Me)
  have htri : ‖Work.Asymptotics.KhatE1Core.Kdev8Bracket ℓ τ z‖
      ≤ ‖Work.Asymptotics.KhatE1Core.Kdev8Bracket ℓ τ z
            - 2 * Work.Asymptotics.KhatE1.KdevE2 ℓ τ z * (Work.Residues.Ept z) ^ 2‖
          + ‖2 * Work.Asymptotics.KhatE1.KdevE2 ℓ τ z * (Work.Residues.Ept z) ^ 2‖ := by
    have h := norm_add_le (Work.Asymptotics.KhatE1Core.Kdev8Bracket ℓ τ z
          - 2 * Work.Asymptotics.KhatE1.KdevE2 ℓ τ z * (Work.Residues.Ept z) ^ 2)
      (2 * Work.Asymptotics.KhatE1.KdevE2 ℓ τ z * (Work.Residues.Ept z) ^ 2)
    have he : (Work.Asymptotics.KhatE1Core.Kdev8Bracket ℓ τ z
          - 2 * Work.Asymptotics.KhatE1.KdevE2 ℓ τ z * (Work.Residues.Ept z) ^ 2)
        + 2 * Work.Asymptotics.KhatE1.KdevE2 ℓ τ z * (Work.Residues.Ept z) ^ 2
        = Work.Asymptotics.KhatE1Core.Kdev8Bracket ℓ τ z := by ring
    rwa [he] at h
  have hbc' : ‖Work.Asymptotics.KhatE1Core.Kdev8Bracket ℓ τ z
            - 2 * Work.Asymptotics.KhatE1.KdevE2 ℓ τ z * (Work.Residues.Ept z) ^ 2‖
      ≤ Cc * X * S ^ Nc * T ^ Mc * E := by
    rw [hXdef, hSdef, hTdef, hEdef]; exact hb_c
  have hsum : ‖Work.Asymptotics.KhatE1Core.Kdev8Bracket ℓ τ z
            - 2 * Work.Asymptotics.KhatE1.KdevE2 ℓ τ z * (Work.Residues.Ept z) ^ 2‖
          + ‖2 * Work.Asymptotics.KhatE1.KdevE2 ℓ τ z * (Work.Residues.Ept z) ^ 2‖
      ≤ (Cc + 2 * Ce) * (X * S ^ (max Nc Ne) * T ^ (max Mc Me) * E) := by
    refine le_trans (add_le_add hbc' hsub) ?_
    calc Cc * X * S ^ Nc * T ^ Mc * E
          + 2 * Ce * X * S ^ (max Nc Ne) * T ^ (max Mc Me) * E
        ≤ Cc * X * S ^ (max Nc Ne) * T ^ (max Mc Me) * E
          + 2 * Ce * X * S ^ (max Nc Ne) * T ^ (max Mc Me) * E := by linarith
      _ = (Cc + 2 * Ce) * (X * S ^ (max Nc Ne) * T ^ (max Mc Me) * E) := by ring
  have hF0 : (0:ℝ) ≤ X * S ^ (max Nc Ne) * T ^ (max Mc Me) * E := by positivity
  have hgoal : ‖Work.Asymptotics.KhatE1Core.Kdev8Bracket ℓ τ z‖
      ≤ ((Cc + 2 * Ce + 1) * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ (max Nc Ne)
          * (1 + t) ^ (max Mc Me) * Real.exp (-(2 * Real.pi * t))) * 2 := by
    have h1 : ‖Work.Asymptotics.KhatE1Core.Kdev8Bracket ℓ τ z‖
        ≤ (Cc + 2 * Ce) * (X * S ^ (max Nc Ne) * T ^ (max Mc Me) * E) :=
      le_trans htri hsum
    have h2 : (Cc + 2 * Ce) ≤ 2 * (Cc + 2 * Ce + 1) := by linarith
    refine le_trans h1 ?_
    calc (Cc + 2 * Ce) * (X * S ^ (max Nc Ne) * T ^ (max Mc Me) * E)
        ≤ (2 * (Cc + 2 * Ce + 1)) * (X * S ^ (max Nc Ne) * T ^ (max Mc Me) * E) :=
          mul_le_mul_of_nonneg_right h2 hF0
      _ = ((Cc + 2 * Ce + 1) * X * S ^ (max Nc Ne) * T ^ (max Mc Me) * E) * 2 := by ring
      _ = ((Cc + 2 * Ce + 1) * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ (max Nc Ne)
          * (1 + t) ^ (max Mc Me) * Real.exp (-(2 * Real.pi * t))) * 2 := by
          rw [hXdef, hSdef, hTdef, hEdef]
  rw [hbridge, norm_div, show ‖(2:ℂ)‖ = 2 by norm_num, div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
  exact hgoal

end Work.Asymptotics.KhatE1Core
