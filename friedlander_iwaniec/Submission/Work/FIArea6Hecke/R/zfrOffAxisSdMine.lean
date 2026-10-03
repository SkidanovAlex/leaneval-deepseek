/-
# `Submission.Work.FIArea6Hecke.R.zfrOffAxisSdMine`

**The de la Vallée Poussin zero-free region off the real axis (*FI* (16.20)) with the corrected
(self-dual) exceptional set**: `Work.FIArea6Hecke.R.ZFRoffAxisSd`.

* **Self-dual case** (`SelfDual d chi m`: the Hecke eigenvalues are real): transfer to a real
  strict character with the same eigenvalues (`Work.FIArea6Hecke.R.selfDualRealTransfer`; the
  weight is forced to `0`) and apply the proved complex zero-free region for real characters
  `Work.FIArea6Hecke.R.realPsiComplexZeroFree`.
* **Non-self-dual case**: the classical `(3,4,1)` argument
  `0 ≤ 3 Re(-L_1'/L_1)(σ) + 4 Re(-L_χ'/L_χ)(σ+iγ) + Re(-L_{χ²}'/L_{χ²})(σ+2iγ)`
  (`Work.FIArea6Hecke.R.HeckeLDerivRe341`) at `σ = 1 + cp/L` with
  * the sharp pole bound `Work.FIArea6Hecke.R.HeckeAxisLogDerivBound` for the first term,
  * the *upper* one-sided bound `Work.FIArea6Hecke.R.lseriesNegLogDerivLeGtOne` for the third
    term (non-self-duality makes `ψ²` non-trivial, so `L(·,χ²)` has no pole at `1`),
  * the near-zero bound `Work.FIArea6Hecke.R.logDerivNearZeroPF` for the middle term, applied at
    the zero `β + iγ` itself and transported from the completion to the `L`-series by
    `Work.FIArea6Hecke.R.neg_re_L_eq` and `Work.FIArea6Hecke.R.logDeriv_heckeArch_re_le`.
  The arithmetic of the four inequalities is `Work.FIArea6Hecke.R.nearZeroArithB`.
-/
import Mathlib
import Submission.Work.FIArea6Hecke.R.heckeStripLogDerivConductor
import Submission.Work.FIArea6Hecke.R.realPsiComplexZeroFree
import Submission.Work.FIArea6Hecke.R.m_eq_zero_of_selfDual
import Submission.Work.FIArea6Hecke.R.selfDualRealTransfer
import Submission.Work.FIArea6Hecke.R.logDerivNearZeroPF
import Submission.Work.FIArea6Hecke.R.lseriesNegLogDerivLeGtOne
import Submission.Work.FIArea6Hecke.R.nearZeroArithB
import Submission.Work.FIArea6Hecke.R.HeckeLDerivRe341
import Submission.Work.FIArea6Hecke.R.HeckeAxisLogDerivBound
import Submission.Work.FIArea6Hecke.R.HeckeZFRCoreMain
import Submission.Work.FIArea6Hecke.R.HeckeLambdaLogDerivBounds
import Submission.Work.FIArea6Hecke.R.Lam_one_ne_zero_case_nonreal

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIArea6Hecke.R

open Complex Metric Filter
open scoped Topology BigOperators

noncomputable section

theorem zfrOffAxisSdMine : Work.FIArea6Hecke.R.ZFRoffAxisSd := by
  obtain ⟨cSD, hcSDpos, hSD⟩ := Work.FIArea6Hecke.R.realPsiComplexZeroFree
  obtain ⟨C1, hC1nn, hAxis⟩ := Work.FIArea6Hecke.R.HeckeAxisLogDerivBound
  obtain ⟨Cnear, hCnearpos, hNear⟩ := Work.FIArea6Hecke.R.logDerivNearZeroPF
  obtain ⟨Csq, hCsqpos, hSq⟩ := Work.FIArea6Hecke.R.lseriesNegLogDerivLeGtOne
  set K : ℝ := max 1 (3 * C1 + 2 * Csq + 4 * (Cnear + 7)) with hKdef
  have hKpos : 0 < K := by
    rw [hKdef]; exact lt_of_lt_of_le one_pos (le_max_left _ _)
  set cp : ℝ := min 1 (1 / (4 * K)) with hcpdef
  have hcppos : 0 < cp := by rw [hcpdef]; exact lt_min one_pos (by positivity)
  have hcple1 : cp ≤ 1 := by rw [hcpdef]; exact min_le_left _ _
  have hcpK : cp * K ≤ 1 / 4 := by
    have h : cp ≤ 1 / (4 * K) := by rw [hcpdef]; exact min_le_right _ _
    have hKnn : 0 ≤ K := le_of_lt hKpos
    have hmul := mul_le_mul_of_nonneg_right h hKnn
    have hval : (1 / (4 * K)) * K = 1 / 4 := by field_simp
    rw [hval] at hmul
    exact hmul
  refine ⟨min cSD (min (cp / 16) 1), lt_min hcSDpos (lt_min (by positivity) one_pos), ?_⟩
  intro d chi m Lam hd hchi hAn hagr s hreg hsle2 hnotex
  by_cases hsd : Work.FIArea6Hecke.R.SelfDual d chi m
  · -- ## self-dual case: transfer to a real character
    have hsim : s.im ≠ 0 := fun h => hnotex ⟨h, hsd⟩
    obtain ⟨chi', hchi', hre', hlam⟩ := Work.FIArea6Hecke.R.selfDualRealTransfer hd hchi hsd
    have hm0 : m = 0 := Work.FIArea6Hecke.R.m_eq_zero_of_selfDual hd hchi hsd
    subst hm0
    have hL : Work.FIArea5.S16Hecke.heckeLSeries chi' 0
        = Work.FIArea5.S16Hecke.heckeLSeries chi 0 := by
      unfold Work.FIArea5.S16Hecke.heckeLSeries
      exact funext (fun z => LSeries_congr (fun {n} _ => hlam n) z)
    have hreal' : ∀ z : GaussianInt, chi' z = star (chi' z) := fun z => (hre' z).symm
    have hagr' : ∀ t : ℂ, 1 < t.re →
        Lam t = Work.FITop4.Bridge.heckeArch d 0 t *
          Work.FIArea5.S16Hecke.heckeLSeries chi' 0 t := by
      intro t ht
      rw [hL]
      exact hagr t (by simpa using ht)
    have hreg' : 1 - cSD / Real.log (4 * (d : ℝ) + |s.im|) < s.re := by
      have hLpos : 0 < Real.log (4 * (d : ℝ) + |s.im|) := by
        refine Real.log_pos ?_
        have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
        nlinarith [abs_nonneg s.im]
      have hcc : (min cSD (min (cp / 16) 1)) / Real.log (4 * (d : ℝ) + |s.im|)
          ≤ cSD / Real.log (4 * (d : ℝ) + |s.im|) :=
        div_le_div_of_nonneg_right (min_le_left _ _) hLpos.le
      have hreg'' := hreg
      simp only [Int.cast_zero, abs_zero, add_zero] at hreg''
      linarith
    exact hSD d chi' Lam hd hchi' hreal' hAn hagr' s hsim hreg' hsle2
  · -- ## non-self-dual case: the `(3,4,1)` argument
    intro hval
    obtain ⟨h1c, hmulc, hbc, hperc, hvdc⟩ := hchi.1
    have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    set L : ℝ := Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |s.im| + 3)) with hLdef
    set L₀ : ℝ := Real.log (4 * (d : ℝ) + |(m : ℝ)| + |s.im|) with hL₀def
    have hLpos : 0 < L := by
      rw [hLdef]
      refine Real.log_pos ?_
      have h4 : (4 : ℝ) ≤ 4 * (d : ℝ) := by linarith [hd1]
      have hX : (3 : ℝ) ≤ |(m : ℝ)| + |s.im| + 3 := by
        have ha := abs_nonneg (m : ℝ); have hb := abs_nonneg s.im; linarith
      have h12 : (12 : ℝ) ≤ 4 * (d : ℝ) * (|(m : ℝ)| + |s.im| + 3) := by
        calc (12 : ℝ) = 4 * 3 := by norm_num
          _ ≤ (4 * (d : ℝ)) * (|(m : ℝ)| + |s.im| + 3) :=
              mul_le_mul h4 hX (by norm_num) (by positivity)
          _ = 4 * (d : ℝ) * (|(m : ℝ)| + |s.im| + 3) := by ring
      linarith
    have hL1 : 1 ≤ L := by
      rw [hLdef]
      have hprod : (12 : ℝ) ≤ 4 * (d : ℝ) * (|(m : ℝ)| + |s.im| + 3) := by
        have h1 : (4 : ℝ) ≤ 4 * (d : ℝ) := by linarith
        have h2 : (3 : ℝ) ≤ |(m : ℝ)| + |s.im| + 3 := by
          have ha := abs_nonneg (m : ℝ); have hb := abs_nonneg s.im; linarith
        calc (12 : ℝ) = (4 : ℝ) * 3 := by norm_num
          _ ≤ (4 * (d : ℝ)) * (|(m : ℝ)| + |s.im| + 3) :=
              mul_le_mul h1 h2 (by norm_num) (by linarith)
          _ = 4 * (d : ℝ) * (|(m : ℝ)| + |s.im| + 3) := by ring
      have hlog12 : (1 : ℝ) ≤ Real.log 12 := by
        have h : (1 : ℝ) < Real.log 12 := by
          rw [← Real.log_exp 1]
          exact Real.log_lt_log (Real.exp_pos 1)
            (lt_trans Real.exp_one_lt_three (by norm_num))
        linarith
      exact le_trans hlog12 (Real.log_le_log (by norm_num) hprod)
    have hL₀pos : 0 < L₀ := by
      rw [hL₀def]
      refine Real.log_pos ?_
      nlinarith [hd1, abs_nonneg (m : ℝ), abs_nonneg s.im]
    have hL₀1 : (1 : ℝ) ≤ L₀ := by
      rw [hL₀def]
      have h4 : (4 : ℝ) ≤ 4 * (d : ℝ) + |(m : ℝ)| + |s.im| := by
        nlinarith [hd1, abs_nonneg (m : ℝ), abs_nonneg s.im]
      have hlog4 : (1 : ℝ) ≤ Real.log 4 := by
        have h : (1 : ℝ) < Real.log 4 := by
          rw [← Real.log_exp 1]
          exact Real.log_lt_log (Real.exp_pos 1)
            (lt_trans Real.exp_one_lt_three (by norm_num))
        linarith
      exact le_trans hlog4 (Real.log_le_log (by norm_num) h4)
    have hL2' : L ≤ 2 * L₀ := by
      rw [hLdef, hL₀def]
      have harg : 4 * (d : ℝ) * (|(m : ℝ)| + |s.im| + 3)
          ≤ (4 * (d : ℝ) + |(m : ℝ)| + |s.im|) ^ 2 := by
        nlinarith [hd1, abs_nonneg (m : ℝ), abs_nonneg s.im]
      have hle := Real.log_le_log (by positivity) harg
      rw [Real.log_pow] at hle
      simpa using hle
    have hsrpos : 0 < s.re := by
      have hcle : min cSD (min (cp / 16) 1) ≤ 1 :=
        le_trans (min_le_right _ _) (min_le_right _ _)
      have hc : min cSD (min (cp / 16) 1) / L₀ ≤ 1 := by
        rw [div_le_one hL₀pos]
        exact le_trans hcle hL₀1
      linarith [hreg]
    have hzero : Lam s = 0 := by
      have hval' : Lam s / Work.FITop4.Bridge.heckeArch d m s = 0 := by
        simpa only [Work.FIArea6Hecke.Lval] using hval
      rcases div_eq_zero_iff.mp hval' with h | h
      · exact h
      · exact absurd h (Work.FIArea6Hecke.R.heckeArch_ne_zero_of_pos_re d hd m hsrpos)
    by_cases hgt : 1 < s.re
    · exact (Work.FIArea6Hecke.R.lam_ne_zero_of_one_lt_re_zz hd hAn h1c hmulc hbc hagr hgt) hzero
    · push_neg at hgt
      -- the point `σ = 1 + x`
      set x : ℝ := cp / L with hxdef
      have hxpos : 0 < x := by rw [hxdef]; exact div_pos hcppos hLpos
      have hxle : x ≤ 1 := by
        rw [hxdef, div_le_one hLpos]
        exact le_trans hcple1 hL1
      set σ : ℝ := 1 + x with hσdef
      have hσ1 : 1 < σ := by rw [hσdef]; linarith
      have hσ2 : σ ≤ 2 := by rw [hσdef]; linarith
      -- the three objects of the `(3,4,1)` inequality
      set A0 : ℝ := (-deriv (Work.FIArea5.S16Hecke.heckeLSeries
            (Work.FIArea6Hecke.principalStrict d) 0) ((σ : ℂ))
          / Work.FIArea5.S16Hecke.heckeLSeries (Work.FIArea6Hecke.principalStrict d) 0
            ((σ : ℂ))).re with hA0
      set B0 : ℝ := (-deriv (Work.FIArea5.S16Hecke.heckeLSeries chi m)
            (((σ : ℂ) + (s.im : ℂ) * Complex.I))
          / Work.FIArea5.S16Hecke.heckeLSeries chi m
            (((σ : ℂ) + (s.im : ℂ) * Complex.I))).re with hB0
      set C0 : ℝ := (-deriv (Work.FIArea5.S16Hecke.heckeLSeries
            (fun z : GaussianInt => chi z * chi z) (2 * m))
            (((σ : ℂ) + ((2 * s.im : ℝ) : ℂ) * Complex.I))
          / Work.FIArea5.S16Hecke.heckeLSeries (fun z : GaussianInt => chi z * chi z) (2 * m)
            (((σ : ℂ) + ((2 * s.im : ℝ) : ℂ) * Complex.I))).re with hC0
      have h341 : 0 ≤ 3 * A0 + 4 * B0 + C0 := by
        rw [hA0, hB0, hC0]
        exact Work.FIArea6Hecke.R.HeckeLDerivRe341 d chi m hd hchi (σ := σ) (t := s.im) hσ1
      -- first term: the sharp pole bound
      have hAub : A0 ≤ 1 / x + C1 := by
        rw [hA0]
        have h := hAxis d hd σ hσ1 hσ2
        have hx' : 1 / (σ - 1) = 1 / x := by rw [hσdef]; ring_nf
        linarith [h]
      -- third term: the one-sided bound for the square
      have hchi2 : Work.FIArea5.S16Hecke.IsCharMod4dStrict d
          (fun z : GaussianInt => chi z * chi z) :=
        Work.FIArea6Hecke.R.isCharMod4dStrict_mul_self hchi
      have hnt2 : ∃ z : GaussianInt, Work.FIPlan.IsPrimary z ∧
          Work.FIArea5.S16Hecke.IsUnitMod4d d z ∧
          Work.FIArea5.S16Hecke.psi (fun z : GaussianInt => chi z * chi z) (2 * m) z ≠ 1 := by
        unfold Work.FIArea6Hecke.R.SelfDual at hsd
        push_neg at hsd
        obtain ⟨z, hzp, hzu, hz2⟩ := hsd
        refine ⟨z, hzp, hzu, ?_⟩
        rw [Work.FIArea6Hecke.R.psi_sq]
        intro hcon
        exact hz2 (by rw [pow_two, hcon])
      have hCub : C0 ≤ 2 * Csq * L := by
        have hC := hSq d (fun z : GaussianInt => chi z * chi z) (2 * m) hd hchi2 hnt2 σ
          (2 * s.im) hσ1 hσ2
        rw [hC0]
        have heq : ((-deriv (Work.FIArea5.S16Hecke.heckeLSeries
              (fun z : GaussianInt => chi z * chi z) (2 * m))
              (((σ : ℂ) + ((2 * s.im : ℝ) : ℂ) * Complex.I))
            / Work.FIArea5.S16Hecke.heckeLSeries (fun z : GaussianInt => chi z * chi z) (2 * m)
              (((σ : ℂ) + ((2 * s.im : ℝ) : ℂ) * Complex.I))).re)
            = -((deriv (Work.FIArea5.S16Hecke.heckeLSeries
                (fun z : GaussianInt => chi z * chi z) (2 * m))
                (((σ : ℂ) + ((2 * s.im : ℝ) : ℂ) * Complex.I))
              / Work.FIArea5.S16Hecke.heckeLSeries (fun z : GaussianInt => chi z * chi z) (2 * m)
                (((σ : ℂ) + ((2 * s.im : ℝ) : ℂ) * Complex.I))).re) := by
          rw [neg_div, Complex.neg_re]
        rw [heq]
        have hlog : Real.log (4 * (d : ℝ) * (|(((2 * m : ℤ)) : ℝ)| + |((2 * s.im : ℝ))| + 3))
            ≤ 2 * L := by
          have h2m : |(((2 * m : ℤ)) : ℝ)| = 2 * |(m : ℝ)| := by
            rw [show (((2 * m : ℤ)) : ℝ) = (2 : ℝ) * (m : ℝ) by push_cast; ring, abs_mul,
              abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
          have h2i : |((2 * s.im : ℝ))| = 2 * |s.im| := by
            rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
          rw [h2m, h2i]
          have harg : 4 * (d : ℝ) * (2 * |(m : ℝ)| + 2 * |s.im| + 3)
              ≤ 2 * (4 * (d : ℝ) * (|(m : ℝ)| + |s.im| + 3)) := by
            nlinarith [hd1, abs_nonneg (m : ℝ), abs_nonneg s.im]
          have hpos : 0 < 4 * (d : ℝ) * (|(m : ℝ)| + |s.im| + 3) := by
            have h2 : (0 : ℝ) < |(m : ℝ)| + |s.im| + 3 := by positivity
            have h1 : (0 : ℝ) < (d : ℝ) := by linarith
            positivity
          have hstep : Real.log (4 * (d : ℝ) * (2 * |(m : ℝ)| + 2 * |s.im| + 3))
              ≤ Real.log (2 * (4 * (d : ℝ) * (|(m : ℝ)| + |s.im| + 3))) :=
            Real.log_le_log (by positivity) harg
          have hsplit : Real.log (2 * (4 * (d : ℝ) * (|(m : ℝ)| + |s.im| + 3)))
              = Real.log 2 + L := by
            rw [Real.log_mul (by norm_num) (ne_of_gt hpos), hLdef]
          have hlog2 : Real.log 2 ≤ 1 := by
            have := Real.log_two_lt_d9
            linarith
          rw [hsplit] at hstep
          linarith [hstep, hlog2, hL1]
        have hmul := mul_le_mul_of_nonneg_left hlog hCsqpos.le
        linarith [hC, hmul]
      -- second term: the near-zero bound at the zero itself
      have hzero' : Lam ((s.re : ℂ) + (s.im : ℂ) * Complex.I) = 0 := by
        rw [Complex.re_add_im]
        exact hzero
      have hnear := hNear d chi m Lam ⟨hd, hchi, hAn, hagr⟩ σ s.re s.im hσ1 hσ2 hsrpos hgt hzero'
      have hB := Work.FIArea6Hecke.R.neg_re_L_eq d hd (chi := chi) (m := m) (Λ := Lam) hAn
        h1c hmulc hbc hagr (s := ((σ : ℂ) + (s.im : ℂ) * Complex.I)) (by
          rw [show ((σ : ℂ) + (s.im : ℂ) * Complex.I).re = σ from by simp]
          exact hσ1)
      have harch := Work.FIArea6Hecke.R.logDeriv_heckeArch_re_le d hd m
        (s := ((σ : ℂ) + (s.im : ℂ) * Complex.I)) (by
          rw [show ((σ : ℂ) + (s.im : ℂ) * Complex.I).re = σ from by simp]; linarith)
        (by rw [show ((σ : ℂ) + (s.im : ℂ) * Complex.I).re = σ from by simp]; exact hσ2)
      have hBub : B0 ≤ -(1 / (x + (1 - s.re))) + (Cnear + 7) * L := by
        rw [hB0]
        have hσβ : σ - s.re = x + (1 - s.re) := by rw [hσdef]; ring
        have h1 : 1 / (σ - s.re) = 1 / (x + (1 - s.re)) := by rw [hσβ]
        have h2 : Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |s.im| + 3)) = L := hLdef.symm
        rw [hB]
        have him : ((σ : ℂ) + (s.im : ℂ) * Complex.I).im = s.im := by simp
        rw [him] at harch
        rw [h2] at hnear harch
        linarith [hnear, harch, h1]
      -- the arithmetic
      have hcpK' : cp * max 1 (3 * C1 + 2 * Csq + 4 * (Cnear + 7)) ≤ 1 / 4 := by
        rw [← hKdef]; exact hcpK
      have hbeta := Work.FIArea6Hecke.R.nearZeroArithB hC1nn hCsqpos hCnearpos hcppos hcpK'
        hL1 hL2' hL₀pos hxdef hgt h341 hAub hCub hBub
      have hcle : min cSD (min (cp / 16) 1) ≤ cp / 16 :=
        le_trans (min_le_right _ _) (min_le_left _ _)
      have h1 : 1 - s.re < (min cSD (min (cp / 16) 1)) / L₀ := by linarith [hreg]
      have h3 : (min cSD (min (cp / 16) 1)) / L₀ ≤ cp / (16 * L₀) := by
        have h := div_le_div_of_nonneg_right hcle hL₀pos.le
        have heq : cp / 16 / L₀ = cp / (16 * L₀) := by field_simp
        rwa [heq] at h
      linarith [hbeta, h1, h3]

end

end Work.FIArea6Hecke.R
