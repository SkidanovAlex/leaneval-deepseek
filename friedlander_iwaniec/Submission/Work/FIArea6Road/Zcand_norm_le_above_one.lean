import Mathlib
import Submission.Work.FIArea6Road.ZcontExistsBoundUniform
import Submission.Work.FIArea6Road.QfacBoundRatioGeOne

namespace Work.FIArea6Road

noncomputable section

/-- **The growth factor `C^{σ-1}` on the line `σ ≤ 1 + 1/log N` is bounded by `e`.**

For `C ≥ 1`, `N ≥ 1` with `C ≤ N^{1-η}` and `σ - 1 ≤ 1/log N`: since `log C ≤ (1-η)log N`,
`C^{σ-1} = exp((σ-1)log C) ≤ exp((1/log N)(1-η) log N) = exp(1-η) ≤ e`.
(For `N = 1` the hypothesis `σ - 1 ≤ 1/log 1 = 0` holds vacuously and `C = 1`.) -/
lemma Cpow_le_exp_one (η C σ N : ℝ) (hη : 0 < η) (hN : 1 ≤ N) (hC : 1 ≤ C)
    (hCN : C ≤ N ^ (1 - η)) (hσ : σ - 1 ≤ 1 / Real.log N) :
    C ^ (σ - 1) ≤ Real.exp 1 := by
  rcases eq_or_lt_of_le hN with hN1 | hNgt
  · rw [← hN1, Real.one_rpow] at hCN
    have hCeq : C = 1 := le_antisymm hCN hC
    rw [hCeq, Real.one_rpow]
    exact Real.one_le_exp (by norm_num)
  · have hNpos : 0 < N := by linarith
    have hlogNpos : 0 < Real.log N := Real.log_pos hNgt
    have hlogne : Real.log N ≠ 0 := ne_of_gt hlogNpos
    have hstep1 : C ^ (σ - 1) ≤ C ^ (1 / Real.log N) :=
      Real.rpow_le_rpow_of_exponent_le hC hσ
    have hCnn : (0 : ℝ) ≤ C := le_trans zero_le_one hC
    have hexpnn : (0 : ℝ) ≤ 1 / Real.log N := by positivity
    have hstep2 : C ^ (1 / Real.log N) ≤ (N ^ (1 - η)) ^ (1 / Real.log N) :=
      Real.rpow_le_rpow hCnn hCN hexpnn
    have hstep3 : (N ^ (1 - η)) ^ (1 / Real.log N) = Real.exp (1 - η) := by
      rw [← Real.rpow_mul (le_of_lt hNpos) (1 - η) (1 / Real.log N)]
      rw [Real.rpow_def_of_pos hNpos]
      congr 1
      field_simp
    have hstep4 : Real.exp (1 - η) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by linarith)
    linarith [hstep1, hstep2, hstep3, hstep4]

/-- **Log-of-a-sum bookkeeping.**  With `A = |m| + |Im s| + 3 ≥ 3` and `N ≥ 1`,
`log(A + N) ≤ log N + log A + 2`: indeed `A + N ≤ (N+1)A`, `log(N+1) ≤ log N + 1`, and
`log A ≥ 0`. -/
lemma log_arg_le (m : ℤ) (s : ℂ) (N : ℝ) (hN : 1 ≤ N) :
    Real.log (|(m : ℝ)| + |s.im| + N + 3)
      ≤ Real.log N + Real.log (|(m : ℝ)| + |s.im| + 3) + 2 := by
  have hkey : Real.log (|(m : ℝ)| + |s.im| + 3 + N)
      ≤ Real.log N + Real.log (|(m : ℝ)| + |s.im| + 3) + 2 := by
    set A : ℝ := |(m : ℝ)| + |s.im| + 3 with hA
    have hA3 : 3 ≤ A := by
      rw [hA]
      have h1 := abs_nonneg (m : ℝ)
      have h2 := abs_nonneg s.im
      linarith
    have hA0 : 0 < A := by linarith
    have hNpos : 0 < N := by linarith
    have h1 : N * 1 ≤ N * A :=
      mul_le_mul_of_nonneg_left (by linarith : (1 : ℝ) ≤ A) (by linarith : (0 : ℝ) ≤ N)
    have hWN : A + N ≤ (N + 1) * A := by nlinarith [h1]
    have hlog1 : Real.log (A + N) ≤ Real.log ((N + 1) * A) :=
      Real.log_le_log (by linarith) hWN
    have hlog2 : Real.log ((N + 1) * A) = Real.log (N + 1) + Real.log A :=
      Real.log_mul (by linarith) (ne_of_gt hA0)
    have hlogN1 : Real.log (N + 1) ≤ Real.log N + 1 := by
      have h2 : N + 1 ≤ 2 * N := by linarith
      have h3 : Real.log (N + 1) ≤ Real.log (2 * N) := Real.log_le_log (by linarith) h2
      rw [Real.log_mul (by norm_num) (ne_of_gt hNpos)] at h3
      have hlog2le : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
        linarith
      linarith
    calc Real.log (A + N) ≤ Real.log ((N + 1) * A) := hlog1
      _ = Real.log (N + 1) + Real.log A := hlog2
      _ ≤ (Real.log N + 1) + Real.log A := by linarith
      _ ≤ Real.log N + Real.log A + 2 := by linarith
  rw [show (|(m : ℝ)| + |s.im| + N + 3) = (|(m : ℝ)| + |s.im| + 3 + N) by ring]
  exact hkey

theorem Zcand_norm_le_above_one (ε c_h C_h : ℝ) (hε : 0 < ε) (hc_h : 0 < c_h) (hC_h : 0 < C_h) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ) (d : ℕ) (Lam : ℂ → ℂ),
        1 ≤ d → chi 1 = 1 →
        (∀ z w : GaussianInt, chi (z * w) = chi z * chi w) →
        (∀ z : GaussianInt, ‖chi z‖ ≤ 1) →
        (∀ s : ℂ,
          1 - c_h / ((d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3)) < s.re → s.re ≤ 2 →
          ‖(Lam s / Work.FITop4.Bridge.heckeArch d m s)⁻¹‖
            ≤ C_h * (d : ℝ) * (Real.log (|(m : ℝ)| + |s.im| + 3)) ^ (2 : ℕ)) →
        4 ≤ Real.log (Pa.Pz : ℝ) →
        ∀ s : ℂ, 1 < s.re → s.re ≤ 1 + 1 / Real.log Pa.N → s.re ≤ 2 →
          ‖Work.FIArea6.TauPieces.Zcand Pa chi m d Lam s‖
            ≤ K * (d : ℝ) * (Real.log Pa.N + Real.log (|(m : ℝ)| + |s.im| + 3) + 2) ^ (6 : ℕ) := by
  obtain ⟨KΦ, hKΦpos, hKΦ⟩ := PhifacBoundUniform
  obtain ⟨KP, hKPpos, hKP⟩ := Work.FIArea6Road.ZT.PfacBoundSharpZT
  obtain ⟨KQ, hKQpos, hKQ⟩ := QfacBoundRatioGeOne
  obtain ⟨Cz, hCzpos, hCz⟩ := ZcBoundArith_proved
  refine ⟨KΦ * C_h * KP * KQ * Real.exp 1 * Cz, by positivity, ?_⟩
  intro Pa chi m d Lam hd hchi1 hchimul hchibd hinv hlogPz s hs1 hs2 hs3
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  set W : ℝ := |(m : ℝ)| + |s.im| + 3 with hW
  have hW3 : 3 ≤ W := by
    rw [hW]
    have h1 := abs_nonneg (m : ℝ)
    have h2 := abs_nonneg s.im
    linarith
  have hW1 : 1 < W := by linarith
  have hlogWpos : 0 < Real.log W := Real.log_pos hW1
  have hlogWnn : 0 ≤ Real.log W := le_of_lt hlogWpos
  set T : ℝ := Real.log Pa.N + Real.log W + 2 with hT
  have hT1 : 1 ≤ T := by
    rw [hT]
    have h1 : 0 ≤ Real.log Pa.N := Real.log_nonneg Pa.hN1
    have h2 : (1.08 : ℝ) ≤ Real.log W :=
      zcub_log_three_ge.trans (Real.log_le_log (by norm_num) hW3)
    linarith
  have hLT : Real.log (|(m : ℝ)| + |s.im| + (Pa.N : ℝ) + 3) ≤ T := by
    rw [hT]
    exact log_arg_le m s Pa.N Pa.hN1
  have h34 : (3 : ℝ) / 4 ≤ s.re := by linarith
  have hone : 1 - 1 / Real.log (Pa.Pz : ℝ) ≤ s.re := by
    have h : 0 ≤ 1 / Real.log (Pa.Pz : ℝ) := by positivity
    linarith
  have hΦ := hKΦ chi m hchi1 hchimul hchibd s h34
  have hInv := hinv s (by
    have hden : 0 < (d : ℝ) ^ ε * Real.log W :=
      mul_pos (Real.rpow_pos_of_pos hdR ε) hlogWpos
    have hquo : 0 < c_h / ((d : ℝ) ^ ε * Real.log W) := div_pos hc_h hden
    linarith) hs3
  have hP := hKP Pa chi m hchi1 hchimul hchibd hlogPz s hone
  have hQ := hKQ Pa chi m hchi1 hchimul hchibd Pa.hC1 hlogPz s (by linarith) hone hs3
  have hCpos : (0 : ℝ) < Pa.C := lt_of_lt_of_le zero_lt_one Pa.hC1
  set Cpow : ℝ := Pa.C ^ (s.re - 1) with hCpowdef
  have hCpow : Cpow ≤ Real.exp 1 := by
    rw [hCpowdef]
    exact Cpow_le_exp_one Pa.η Pa.C s.re Pa.N Pa.hη Pa.hN1 Pa.hC1 Pa.hC2 (by linarith)
  have hCpownn : 0 ≤ Cpow := by
    rw [hCpowdef]
    exact Real.rpow_nonneg (le_of_lt hCpos) _
  have hstep : ‖Work.FIArea6.TauPieces.Zcand Pa chi m d Lam s‖
      = ‖Work.FIArea6.TauPieces.Phifac chi m s‖
        * ‖(Lam s / Work.FITop4.Bridge.heckeArch d m s)⁻¹‖
        * ‖Work.FIArea6.TauPieces.Pfac Pa chi m s‖
        * ‖Work.FIArea6.TauPieces.Qfac Pa chi m s‖ := by
    rw [Work.FIArea6.TauPieces.Zcand_apply, norm_mul, norm_mul, norm_mul]
  rw [hstep]
  have hgc : ‖Work.FIArea6.TauPieces.Phifac chi m s‖
        * ‖(Lam s / Work.FITop4.Bridge.heckeArch d m s)⁻¹‖
        * ‖Work.FIArea6.TauPieces.Pfac Pa chi m s‖
        * ‖Work.FIArea6.TauPieces.Qfac Pa chi m s‖
      ≤ KΦ * (C_h * (d : ℝ) * (Real.log W) ^ (2 : ℕ))
        * (KP * (Real.log (Pa.Pz : ℝ) + 2) ^ (3 : ℕ))
        * (KQ * Cpow * (1 + Real.log (Pa.C + 2) / Real.log (Pa.Pz : ℝ)) ^ (2 : ℕ)) := by
    rw [hCpowdef]
    gcongr
  have hGn : 0 ≤ (Real.log (Pa.Pz : ℝ) + 2) ^ (3 : ℕ)
      * (1 + Real.log (Pa.C + 2) / Real.log (Pa.Pz : ℝ)) ^ (2 : ℕ) * (Real.log W) ^ (2 : ℕ) := by
    have h2 : 0 ≤ 1 + Real.log (Pa.C + 2) / Real.log (Pa.Pz : ℝ) := by
      have hc2 : 0 ≤ Real.log (Pa.C + 2) := Real.log_nonneg (by linarith [Pa.hC1])
      have h := div_nonneg hc2 (by linarith : (0 : ℝ) ≤ Real.log (Pa.Pz : ℝ))
      linarith
    positivity
  have hLnn : 0 ≤ Real.log (|(m : ℝ)| + |s.im| + (Pa.N : ℝ) + 3) := by
    apply Real.log_nonneg
    have h1 := abs_nonneg (m : ℝ)
    have h2 := abs_nonneg s.im
    linarith [Pa.hN1]
  have hLT6 : (Real.log (|(m : ℝ)| + |s.im| + (Pa.N : ℝ) + 3)) ^ (6 : ℕ) ≤ T ^ (6 : ℕ) :=
    pow_le_pow_left₀ hLnn hLT 6
  have hX := hCz Pa m s Pa.hC1 hlogPz
  have hG : (Real.log (Pa.Pz : ℝ) + 2) ^ (3 : ℕ)
      * (1 + Real.log (Pa.C + 2) / Real.log (Pa.Pz : ℝ)) ^ (2 : ℕ) * (Real.log W) ^ (2 : ℕ)
      ≤ Cz * T ^ (6 : ℕ) := by
    calc (Real.log (Pa.Pz : ℝ) + 2) ^ (3 : ℕ)
          * (1 + Real.log (Pa.C + 2) / Real.log (Pa.Pz : ℝ)) ^ (2 : ℕ) * (Real.log W) ^ (2 : ℕ)
        ≤ Cz * (Real.log (|(m : ℝ)| + |s.im| + (Pa.N : ℝ) + 3)) ^ (6 : ℕ) := hX
      _ ≤ Cz * T ^ (6 : ℕ) := mul_le_mul_of_nonneg_left hLT6 (le_of_lt hCzpos)
  have hCzT : 0 ≤ Cz * T ^ (6 : ℕ) := by positivity
  have harith : (Real.log (Pa.Pz : ℝ) + 2) ^ (3 : ℕ)
      * (1 + Real.log (Pa.C + 2) / Real.log (Pa.Pz : ℝ)) ^ (2 : ℕ) * (Real.log W) ^ (2 : ℕ) * Cpow
      ≤ Real.exp 1 * (Cz * T ^ (6 : ℕ)) := by
    calc (Real.log (Pa.Pz : ℝ) + 2) ^ (3 : ℕ)
          * (1 + Real.log (Pa.C + 2) / Real.log (Pa.Pz : ℝ)) ^ (2 : ℕ) * (Real.log W) ^ (2 : ℕ) * Cpow
        ≤ (Cz * T ^ (6 : ℕ)) * Real.exp 1 := mul_le_mul hG hCpow hCpownn hCzT
      _ = Real.exp 1 * (Cz * T ^ (6 : ℕ)) := by ring
  have hKd : 0 ≤ (KΦ * C_h * KP * KQ) * (d : ℝ) := by positivity
  have hcomb : KΦ * (C_h * (d : ℝ) * (Real.log W) ^ (2 : ℕ))
        * (KP * (Real.log (Pa.Pz : ℝ) + 2) ^ (3 : ℕ))
        * (KQ * Cpow * (1 + Real.log (Pa.C + 2) / Real.log (Pa.Pz : ℝ)) ^ (2 : ℕ))
      ≤ (KΦ * C_h * KP * KQ * Real.exp 1 * Cz) * (d : ℝ) * T ^ (6 : ℕ) := by
    calc KΦ * (C_h * (d : ℝ) * (Real.log W) ^ (2 : ℕ))
          * (KP * (Real.log (Pa.Pz : ℝ) + 2) ^ (3 : ℕ))
          * (KQ * Cpow * (1 + Real.log (Pa.C + 2) / Real.log (Pa.Pz : ℝ)) ^ (2 : ℕ))
        = (KΦ * C_h * KP * KQ) * (d : ℝ)
            * (((Real.log (Pa.Pz : ℝ) + 2) ^ (3 : ℕ)
                * (1 + Real.log (Pa.C + 2) / Real.log (Pa.Pz : ℝ)) ^ (2 : ℕ)
                * (Real.log W) ^ (2 : ℕ)) * Cpow) := by ring
      _ ≤ (KΦ * C_h * KP * KQ) * (d : ℝ) * (Real.exp 1 * (Cz * T ^ (6 : ℕ))) :=
          mul_le_mul_of_nonneg_left harith hKd
      _ = (KΦ * C_h * KP * KQ * Real.exp 1 * Cz) * (d : ℝ) * T ^ (6 : ℕ) := by ring
  exact hgc.trans hcomb

end

end Work.FIArea6Road
