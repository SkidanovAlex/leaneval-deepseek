import Mathlib
import Submission.Work.FIArea6Hecke.R.heckeArch_inv_exp_growth
import Submission.Work.FIArea6Hecke.R.heckeLambda_eq_LambdaHecke
import Submission.Work.FIArea6Hecke.R.mellin_thetaHol_strip_bound
import Submission.Work.FIArea6Hecke.R.mellin_thetaHol_analyticOn
import Submission.Work.FIArea6Hecke.ZFRDefs

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIArea6Hecke.R

open scoped BigOperators

noncomputable section

/-- **Phragmén–Lindelöf growth condition for the canonical Hecke completion.**  For a strict `χ`
mod `4d` with `‖χ‖ ≤ 1`, nonzero unit sum and vanishing `0`-th Gauss sum, every entire `Lam`
agreeing with `heckeArch d 0 s · heckeLSeries χ 0 s` on `re s > 1` satisfies the linear-exponential
growth bound `‖Lval d 0 Lam z‖ ≤ exp (K·(1+|im z|))` on the strip `-1/2 ≤ re z ≤ 3/2`.

Route: `Lam = (4d)^z·mellin (thetaHol χ 0) z` (identified with the given `Lam` by
`Work.FIArea6Hecke.eq_of_agrees_right`, the Mellin identity on `re s > 1` being
`Work.FIArea6Hecke.R.mellin_thetaHol_eq`), and `mellin` of the theta series is *bounded* on the
closed strip (`Work.FIArea6Hecke.R.mellin_thetaHol_strip_bound`), while the reciprocal archimedean
factor `(heckeArch d 0 z)⁻¹` grows at most like `exp (C(1+|im z|))` on the strip
(`Work.FIArea6Hecke.R.heckeArch_inv_exp_growth`). -/
theorem heckeLval_strip_growth :
    ∀ (d : ℕ) (hd : 1 ≤ d) (chi : GaussianInt → ℂ),
      Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi →
      (∀ z : GaussianInt, ‖chi z‖ ≤ 1) →
      Work.FIArea5.S16Hecke.unitSum chi 0 ≠ 0 →
      Work.FIArea5.S16Hecke.gaussSum d chi 0 = 0 →
      ∀ (Lam : ℂ → ℂ), AnalyticOn ℂ Lam Set.univ →
      (∀ s : ℂ, 1 < s.re →
        Lam s = Work.FITop4.Bridge.heckeArch d 0 s *
          Work.FIArea5.S16Hecke.heckeLSeries chi 0 s) →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℂ, -1 / 2 ≤ z.re → z.re ≤ 3 / 2 →
        ‖Work.FIArea6Hecke.Lval d 0 Lam z‖ ≤ Real.exp (K * (1 + |z.im|)) := by
  intro d hd chi hchi hb hU h0 Lam hAn hagr
  have hfourd_pos : (0 : ℝ) < 4 * (d : ℝ) := by
    have h1 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    linarith
  have hfourd_one : (1 : ℝ) ≤ 4 * (d : ℝ) := by
    have h1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  -- ### the canonical completion `G`
  set G : ℂ → ℂ := fun z => (((4 * d : ℕ) : ℂ)) ^ z *
      mellin (Work.FIArea5.S16Hecke.thetaHol chi 0) z with hGdef
  have hG_an : AnalyticOn ℂ G Set.univ :=
    (Work.FIArea5.S16Hecke.analyticOn_fourd_cpow d hd).mul
      (mellin_thetaHol_analyticOn d hd chi hchi hU h0)
  have hbase2 : ((4 * ((d : ℝ) : ℂ) / ((Real.pi : ℝ) : ℂ))) =
      ((↑(4 * (d : ℝ) / Real.pi) : ℂ)) := by
    rw [Complex.ofReal_div, Complex.ofReal_mul]
    norm_num
  have hpow : ∀ s : ℂ, (((4 * d : ℕ) : ℂ)) ^ s * (Real.pi : ℂ) ^ (-s) =
      ((4 * ((d : ℝ) : ℂ) / ((Real.pi : ℝ) : ℂ))) ^ s := by
    intro s
    have h := Work.FIArea5.S16Hecke.fourd_pow_pi_pow d hd 0 s
    simp only [Nat.cast_zero, zero_div, add_zero, Complex.cpow_zero, mul_one] at h
    rw [hbase2]
    exact h
  have hG_agr : ∀ s : ℂ, 1 < s.re → G s =
      Work.FITop4.Bridge.heckeArch d 0 s * Work.FIArea5.S16Hecke.heckeLSeries chi 0 s := by
    intro s hs
    have hm := Work.FIArea6Hecke.R.mellin_thetaHol_eq chi 0 hb (s := s) (by simpa using hs)
    simp only [Nat.cast_zero, zero_div, sub_zero] at hm
    rw [hGdef]
    calc (((4 * d : ℕ) : ℂ)) ^ s * mellin (Work.FIArea5.S16Hecke.thetaHol chi 0) s
        = ((((4 * d : ℕ) : ℂ)) ^ s * (Real.pi : ℂ) ^ (-s)) * Complex.Gamma s *
            Work.FIArea5.S16Hecke.heckeLSeries chi 0 s := by rw [hm]; ring
      _ = ((4 * ((d : ℝ) : ℂ) / ((Real.pi : ℝ) : ℂ))) ^ s * Complex.Gamma s *
            Work.FIArea5.S16Hecke.heckeLSeries chi 0 s := by rw [hpow]
      _ = Work.FITop4.Bridge.heckeArch d 0 s * Work.FIArea5.S16Hecke.heckeLSeries chi 0 s := by
          rw [Work.FITop4.Bridge.heckeArch]
          simp only [Int.cast_zero, abs_zero, zero_div, Complex.ofReal_zero, add_zero]
  have hLamG : Lam = G :=
    Work.FIArea6Hecke.eq_of_agrees_right G Lam hG_an hAn
      (fun s hs => by rw [hagr s hs, hG_agr s hs])
  -- ### the strip bound for the Mellin transform and for `1/heckeArch`
  obtain ⟨M, hM0, hM⟩ := mellin_thetaHol_strip_bound d hd chi hchi hU h0
  obtain ⟨c, C, hc, hC, hArch⟩ := heckeArch_inv_exp_growth d hd
  set M' : ℝ := (4 * (d : ℝ)) ^ (3 / 2 : ℝ) * M * c with hM'def
  have hM'0 : 0 ≤ M' := by
    rw [hM'def]
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hfourd_pos.le _) hM0) hc.le
  have hfourd_norm : ∀ z : ℂ, z.re ≤ 3 / 2 →
      ‖(((4 * d : ℕ) : ℂ)) ^ z‖ ≤ (4 * (d : ℝ)) ^ (3 / 2 : ℝ) := by
    intro z hz
    have hb' : (((4 * d : ℕ) : ℂ)) = (((4 * (d : ℝ)) : ℝ) : ℂ) := by push_cast; ring
    rw [hb', Complex.norm_cpow_eq_rpow_re_of_pos hfourd_pos]
    exact Real.rpow_le_rpow_of_exponent_le hfourd_one hz
  have hstep : ∀ z : ℂ, -1 / 2 ≤ z.re → z.re ≤ 3 / 2 →
      ‖Work.FIArea6Hecke.Lval d 0 Lam z‖ ≤ M' * Real.exp (C * (1 + |z.im|)) := by
    intro z hz1 hz2
    have hLamz : ‖Lam z‖ ≤ (4 * (d : ℝ)) ^ (3 / 2 : ℝ) * M := by
      rw [hLamG, hGdef]
      exact (norm_mul _ _).le.trans (mul_le_mul (hfourd_norm z hz2) (hM z hz1 hz2)
        (norm_nonneg _) (Real.rpow_nonneg hfourd_pos.le _))
    have hArchz : ‖(Work.FITop4.Bridge.heckeArch d 0 z)⁻¹‖ ≤
        c * Real.exp (C * (1 + |z.im|)) := hArch z hz1 hz2
    rw [Work.FIArea6Hecke.Lval, div_eq_mul_inv]
    calc ‖Lam z * (Work.FITop4.Bridge.heckeArch d 0 z)⁻¹‖
        = ‖Lam z‖ * ‖(Work.FITop4.Bridge.heckeArch d 0 z)⁻¹‖ := norm_mul _ _
      _ ≤ ((4 * (d : ℝ)) ^ (3 / 2 : ℝ) * M) * (c * Real.exp (C * (1 + |z.im|))) :=
          mul_le_mul hLamz hArchz (norm_nonneg _) (mul_nonneg (Real.rpow_nonneg hfourd_pos.le _) hM0)
      _ = M' * Real.exp (C * (1 + |z.im|)) := by rw [hM'def]; ring
  -- ### the linear-exponential growth
  refine ⟨Real.log (max 1 M') + C + 1, ?_, ?_⟩
  · have h1 : 0 ≤ Real.log (max 1 M') := Real.log_nonneg (le_max_left 1 M')
    linarith
  · intro z hz1 hz2
    have hL : 0 ≤ Real.log (max 1 M') := Real.log_nonneg (le_max_left 1 M')
    have ht : 0 ≤ |z.im| := abs_nonneg _
    have hlog : M' ≤ Real.exp (Real.log (max 1 M')) := by
      have hmax : 0 < max 1 M' := lt_of_lt_of_le zero_lt_one (le_max_left 1 M')
      rw [Real.exp_log hmax]
      exact le_max_right 1 M'
    have hlin : Real.log (max 1 M') + C * (1 + |z.im|) ≤
        (Real.log (max 1 M') + C + 1) * (1 + |z.im|) := by
      nlinarith [hL, ht, hC, mul_nonneg (add_nonneg hL zero_le_one) ht]
    calc ‖Work.FIArea6Hecke.Lval d 0 Lam z‖ ≤ M' * Real.exp (C * (1 + |z.im|)) :=
          hstep z hz1 hz2
      _ ≤ Real.exp (Real.log (max 1 M')) * Real.exp (C * (1 + |z.im|)) :=
          mul_le_mul_of_nonneg_right hlog (Real.exp_nonneg _)
      _ = Real.exp (Real.log (max 1 M') + C * (1 + |z.im|)) := by rw [Real.exp_add]
      _ ≤ Real.exp ((Real.log (max 1 M') + C + 1) * (1 + |z.im|)) :=
          Real.exp_le_exp.mpr hlin

end

end Work.FIArea6Hecke.R
