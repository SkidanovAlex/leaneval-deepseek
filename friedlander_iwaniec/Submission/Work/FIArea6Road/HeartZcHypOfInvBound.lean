import Mathlib
import Submission.Work.FIArea6Road.HeartZcDefs
import Submission.Work.FIArea6Road.ZcontExistsBoundUniform
import Submission.Work.FIArea6Road.QfacBoundRatioGeOne
import Submission.Work.FIArea6Road.PhifacBoundUniform
import Submission.Work.FIArea6Road.PfacSharpZT
import Submission.Work.FIArea6Road.Zcand_eq_Zsfun_of_one_lt_re
import Submission.Work.FIArea6Road.Zcand_norm_le_above_one

namespace Work.FIArea6Road

theorem HeartZcHypOfInvBound (ε c_h C_h : ℝ) (hε : 0 < ε) (hc_h : 0 < c_h) (hC_h : 0 < C_h) :
    ∃ K_z : ℝ, 0 < K_z ∧
      ∀ (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ) (d : ℕ) (Lam : ℂ → ℂ),
        1 ≤ d → Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi →
        4 ≤ Real.log (Pa.Pz : ℝ) →
        AnalyticOn ℂ Lam Set.univ →
        (∀ s : ℂ, 1 + |(m : ℝ)| / 2 < s.re →
          Lam s = Work.FITop4.Bridge.heckeArch d m s *
            Work.FIArea5.S16Hecke.heckeLSeries chi m s) →
        (∀ s : ℂ,
          1 - c_h / ((d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3)) < s.re → s.re ≤ 2 →
          ‖(Lam s / Work.FITop4.Bridge.heckeArch d m s)⁻¹‖
            ≤ C_h * (d : ℝ) * (Real.log (|(m : ℝ)| + |s.im| + 3)) ^ (2 : ℕ)) →
        ∃ (C_z : ℝ) (Zc : ℂ → ℂ), C_z ≤ K_z ∧
          Work.FIArea6Road.heartZcHyp Pa chi m d ε c_h C_z Zc := by
  obtain ⟨C_A, hC_A_pos, Huni⟩ := ZcontExistsBoundUniform ε c_h C_h hε hc_h hC_h
  obtain ⟨K_B, hK_B_pos, HB⟩ := Zcand_norm_le_above_one ε c_h C_h hε hc_h hC_h
  refine ⟨max C_A K_B, lt_of_lt_of_le hC_A_pos (le_max_left _ _), ?_⟩
  intro Pa chi m d Lam hd hchi hlogPz hLam hag hinv
  obtain ⟨hchi1, hchimul, hchibd, -, -⟩ := hchi.1
  obtain ⟨Zc, hagree, hana, hbndA⟩ :=
    Huni Pa chi m d Lam hd hchi1 hchimul hchibd hLam hag hinv Pa.hN1 Pa.hC1 hlogPz
  have hCpos : (0 : ℝ) < Pa.C := lt_of_lt_of_le zero_lt_one Pa.hC1
  have hlogPzpos : (0 : ℝ) < Real.log (Pa.Pz : ℝ) := by linarith
  refine ⟨max C_A K_B, Zc, le_refl _,
    lt_of_lt_of_le hC_A_pos (le_max_left _ _), hagree, hana, ?_, ?_⟩
  · -- clause 1: the bound with the saving `C^{1-σ}` in the region (16.32), `σ ≤ 1`
    intro s h12 hr hc hs1
    have h34 : (3 : ℝ) / 4 ≤ s.re := by
      have h4 : 1 / Real.log (Pa.Pz : ℝ) ≤ 1 / 4 :=
        one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4) hlogPz
      linarith
    have hb := hbndA s h34 hr hs1 hc
    have hlog_le : Real.log (|(m : ℝ)| + |s.im| + (Pa.N : ℝ) + 3)
        ≤ Real.log (Pa.N) + Real.log (|(m : ℝ)| + |s.im| + 3) + 2 :=
      heart_logN_add_three_le Pa m s
    have hlog_nn : 0 ≤ Real.log (|(m : ℝ)| + |s.im| + (Pa.N : ℝ) + 3) := by
      apply Real.log_nonneg
      have h1 := abs_nonneg (m : ℝ)
      have h2 := abs_nonneg s.im
      have h3 : (1 : ℝ) ≤ (Pa.N : ℝ) := Pa.hN1
      linarith
    have hpow : (Real.log (|(m : ℝ)| + |s.im| + (Pa.N : ℝ) + 3)) ^ (6 : ℕ)
        ≤ (Real.log (Pa.N) + Real.log (|(m : ℝ)| + |s.im| + 3) + 2) ^ (6 : ℕ) :=
      pow_le_pow_left₀ hlog_nn hlog_le 6
    have hdnn : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    have hCnn : 0 ≤ Pa.C ^ (1 - s.re) := Real.rpow_nonneg (le_of_lt hCpos) _
    have hred : C_A * (d : ℝ) * Pa.C ^ (1 - s.re)
          * (Real.log (|(m : ℝ)| + |s.im| + (Pa.N : ℝ) + 3)) ^ (6 : ℕ)
        ≤ max C_A K_B * (d : ℝ) * Pa.C ^ (1 - s.re)
          * (Real.log (Pa.N) + Real.log (|(m : ℝ)| + |s.im| + 3) + 2) ^ (6 : ℕ) := by
      have h1 : C_A * (d : ℝ) * Pa.C ^ (1 - s.re)
            * (Real.log (|(m : ℝ)| + |s.im| + (Pa.N : ℝ) + 3)) ^ (6 : ℕ)
          ≤ max C_A K_B * (d : ℝ) * Pa.C ^ (1 - s.re)
            * (Real.log (|(m : ℝ)| + |s.im| + (Pa.N : ℝ) + 3)) ^ (6 : ℕ) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left C_A K_B) hdnn) hCnn)
          (pow_nonneg hlog_nn 6)
      have h2 : max C_A K_B * (d : ℝ) * Pa.C ^ (1 - s.re)
            * (Real.log (|(m : ℝ)| + |s.im| + (Pa.N : ℝ) + 3)) ^ (6 : ℕ)
          ≤ max C_A K_B * (d : ℝ) * Pa.C ^ (1 - s.re)
            * (Real.log (Pa.N) + Real.log (|(m : ℝ)| + |s.im| + 3) + 2) ^ (6 : ℕ) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      exact h1.trans h2
    exact hb.trans hred
  · -- clause 2: the bound without the `C`-factor on the thin strip `1 < σ ≤ 1 + 1/log N`
    intro s hs1 hsN hs2
    have hb := HB Pa chi m d Lam hd hchi1 hchimul hchibd hinv hlogPz s hs1 hsN hs2
    have heq : Zc s = Work.FIArea6.TauPieces.Zcand Pa chi m d Lam s :=
      (hagree s hs1).trans
        (Zcand_eq_Zsfun_of_one_lt_re Pa chi m d Lam hd hchi1 hchimul hchibd hLam hag hs1).symm
    rw [heq]
    refine hb.trans ?_
    have hKB : K_B ≤ max C_A K_B := le_max_right _ _
    have hdnn : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    have hLnn : (0 : ℝ) ≤ (Real.log Pa.N + Real.log (|(m : ℝ)| + |s.im| + 3) + 2) ^ (6 : ℕ) :=
      pow_nonneg (by
        have h1 : 0 ≤ Real.log Pa.N := Real.log_nonneg Pa.hN1
        have h2 : 0 ≤ Real.log (|(m : ℝ)| + |s.im| + 3) := by
          apply Real.log_nonneg
          have h3 := abs_nonneg (m : ℝ)
          have h4 := abs_nonneg s.im
          linarith
        linarith) 6
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKB hdnn) hLnn

end Work.FIArea6Road
