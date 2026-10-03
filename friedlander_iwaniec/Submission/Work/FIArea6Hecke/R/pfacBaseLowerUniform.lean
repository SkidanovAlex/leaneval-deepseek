import Mathlib
import Submission.Work.FIArea6Hecke.R.baseLowerNegTwoUniform
import Submission.Work.FIArea6Hecke.R.HasConductorFEDefs
import Submission.Work.FIArea6Hecke.R.ConductorThetaDefs
import Submission.Work.FIArea6Hecke.R.heckeLval_logDeriv_norm_le_of_one_lt_re
import Submission.Work.FIArea6Hecke.R.HeckeLSeriesLogDerivEuler
import Submission.Work.FIArea6Hecke.R.noCompletion_of_primaryTrivial
import Submission.Work.FIArea5.HeckeZFR.FELogDeriv
import Submission.Work.FIArea5.HeckeZFR.DigammaShift
import Submission.Port.LogDerivCompat

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIArea6Hecke.R

open Complex Filter
open scoped BigOperators Topology

noncomputable section

/-- **The uniform lower bound for `Re (Λ'/Λ)` at the base point `re s = -2`**, given the
conductor-normalised functional equation as a hypothesis. -/
theorem pfacBaseLowerUniform
    (condFE : ∀ (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ), 1 ≤ d →
      Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi →
      (∃ z : GaussianInt, Work.FIPlan.IsPrimary z ∧ Work.FIArea5.S16Hecke.IsUnitMod4d d z ∧
        Work.FIArea5.S16Hecke.psi chi m z ≠ 1) →
      HasConductorFE d chi m) :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ) (Lam : ℂ → ℂ),
      IsCompleted d chi m Lam → ∀ γ : ℝ,
        -(C * Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |γ| + 3)))
          ≤ (deriv Lam ((-2 : ℂ) + (γ : ℂ) * Complex.I)
              / Lam ((-2 : ℂ) + (γ : ℂ) * Complex.I)).re := by
  obtain ⟨C3, hC3pos, hC3⟩ := logDerivCompletionUniformAtThree
  refine ⟨C3 + 8, by linarith, ?_⟩
  intro d chi m Lam hadm γ
  obtain ⟨hd, hchi, hAn, hagr⟩ := hadm
  by_cases hne : ∃ z : GaussianInt, Work.FIPlan.IsPrimary z ∧
      Work.FIArea5.S16Hecke.IsUnitMod4d d z ∧ Work.FIArea5.S16Hecke.psi chi m z ≠ 1
  · obtain ⟨X, c₁, c₂, S, Phi, W, hX1, hX4, hS, hW, hPhian, hFE, hPagr⟩ :=
      condFE d chi m hd hchi hne
    obtain ⟨h1, hmul, hb, -, -⟩ := hchi.1
    have hS' : ∀ p ∈ S, Nat.Prime p ∧ (‖c₁ p‖ = 1 ∨ c₁ p = 0) ∧ (‖c₂ p‖ = 1 ∨ c₂ p = 0) :=
      fun p hp => ⟨(hS p hp).1, (hS p hp).2.2.1, (hS p hp).2.2.2⟩
    have hSpos : ∀ p ∈ S, p ≠ 0 := fun p hp => (hS p hp).1.pos.ne'
    have hXpos : (0 : ℝ) < X := lt_of_lt_of_le one_pos hX1
    set A : ℝ := 4 * (d : ℝ) / X with hAdef
    have hApos : 0 < A := by rw [hAdef]; positivity
    have hAne : (A : ℂ) ≠ 0 := by rw [Complex.ofReal_ne_zero]; exact ne_of_gt hApos
    have hlogpos : 0 ≤ Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |γ| + 3)) := by
      refine Real.log_nonneg ?_
      have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
      have hm0 : (0 : ℝ) ≤ |(m : ℝ)| := abs_nonneg _
      have hg0 : (0 : ℝ) ≤ |γ| := abs_nonneg _
      nlinarith
    have hlog4d : Real.log (4 * (d : ℝ)) ≤ Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |γ| + 3)) := by
      refine Real.log_le_log (by positivity) ?_
      have hm0 : (0 : ℝ) ≤ |(m : ℝ)| := abs_nonneg _
      have hg0 : (0 : ℝ) ≤ |γ| := abs_nonneg _
      nlinarith
    have hPhi_diff : Differentiable ℂ Phi := differentiableOn_univ.mp hPhian.differentiableOn
    have hGdiff : Differentiable ℂ (corrFac c₁ c₂ S) :=
      fun u => differentiableAt_corrFac c₁ c₂ S hSpos u
    have hAcpdiff : Differentiable ℂ (fun z : ℂ => (A : ℂ) ^ z) :=
      fun u => (hasStrictDerivAt_const_cpow (Or.inl hAne)).hasDerivAt.differentiableAt
    have hLamfac : Lam = fun s : ℂ => Phi s * ((A : ℂ) ^ s) * corrFac c₁ c₂ S s :=
      Lam_eq_Phi_mul_corrFac ⟨hd, hchi, hAn, hagr⟩ hX1 hX4 hS hPhian hPagr
    have hsplit : ∀ s : ℂ, Lam s ≠ 0 → corrFac c₁ c₂ S s ≠ 0 → Phi s ≠ 0 →
        logDeriv Lam s = Complex.log (A : ℂ) + logDeriv (corrFac c₁ c₂ S) s + logDeriv Phi s := by
      intro s hLs hgs hPs
      have hAs : ((A : ℂ) ^ s) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hAne)
      let P : ℂ → ℂ := fun z : ℂ => Phi z * ((A : ℂ) ^ z)
      have hPne : P s ≠ 0 := by
        show Phi s * ((A : ℂ) ^ s) ≠ 0
        exact mul_ne_zero hPs hAs
      have hPdiff : DifferentiableAt ℂ P s := (hPhi_diff s).mul (hAcpdiff s)
      have h1 : logDeriv Lam s = logDeriv (fun z : ℂ => P z * corrFac c₁ c₂ S z) s := by
        rw [hLamfac]
      have hsplit1 := Submission.Port.logDeriv_mul_fun (f := P) (g := corrFac c₁ c₂ S) s hPne hgs hPdiff (hGdiff s)
      have hPsplit : logDeriv P s = Complex.log (A : ℂ) + logDeriv Phi s := by
        show logDeriv (fun z : ℂ => Phi z * ((A : ℂ) ^ z)) s
          = Complex.log (A : ℂ) + logDeriv Phi s
        rw [Submission.Port.logDeriv_mul_fun s hPs (show (fun z : ℂ => (A : ℂ) ^ z) s ≠ 0 from hAs)
          (hPhi_diff s) (hAcpdiff s), logDeriv_const_cpow A hAne s]
        ring
      rw [h1, hsplit1, hPsplit]
      ring
    set w : ℂ := (-2 : ℂ) + (γ : ℂ) * Complex.I with hw
    set z : ℂ := (3 : ℂ) + (γ : ℂ) * Complex.I with hz
    have hwz : star (1 - w) = z := by
      rw [hw, hz]; apply Complex.ext <;> simp [Complex.star_def] <;> ring
    have hw_re : w.re = -2 := by simp [hw]
    have hz_re : z.re = 3 := by simp [hz]
    by_cases hw0 : Lam w = 0
    · have h0 : deriv Lam ((-2 : ℂ) + (γ : ℂ) * Complex.I)
            / Lam ((-2 : ℂ) + (γ : ℂ) * Complex.I) = 0 := by
        rw [show Lam ((-2 : ℂ) + (γ : ℂ) * Complex.I) = 0 from hw0, div_zero]
      rw [h0, Complex.zero_re]
      exact neg_nonpos.mpr (mul_nonneg (by linarith) hlogpos)
    · have hg_w : corrFac c₁ c₂ S w ≠ 0 :=
        corrFac_ne_zero_of_re_le_neg_one hS' (by rw [hw_re]; norm_num)
      have hg_z : corrFac c₁ c₂ S z ≠ 0 :=
        corrFac_ne_zero_of_one_lt_re hS' (by rw [hz_re]; norm_num)
      have hLamz : Lam z ≠ 0 := by
        rw [Lam_eq_heckeArch_mul_of_one_lt_re hd hAn hb hagr (by rw [hz_re]; norm_num)]
        exact mul_ne_zero (heckeArch_ne_zero_of_one_lt_re hd m (by rw [hz_re]; norm_num))
          (Work.FIArea5.S16Hecke.heckeLSeries_ne_zero_of_one_lt_re chi m h1 hmul hb
            (by rw [hz_re]; norm_num))
      have hprod_w : Phi w * ((A : ℂ) ^ w) * corrFac c₁ c₂ S w ≠ 0 := by
        rw [← congrFun hLamfac w]; exact hw0
      have hPhi_w : Phi w ≠ 0 := fun h0 => hprod_w (by rw [h0, zero_mul, zero_mul])
      have hPhi_z : Phi z ≠ 0 := by
        intro h0
        have hz0 : Phi z * ((A : ℂ) ^ z) * corrFac c₁ c₂ S z = 0 := by
          rw [h0, zero_mul, zero_mul]
        exact hLamz (by rw [congrFun hLamfac z, hz0])
      have hFEΦ : deriv Phi w / Phi w = -star (deriv Phi z / Phi z) := by
        have h := Work.FIArea5.S16Hecke.logDeriv_FE (Lam := Phi) hW hFE hPhi_diff (s := w)
          hPhi_w (by rw [hwz]; exact hPhi_z)
        rw [hwz] at h
        exact h
      have hsw := hsplit w hw0 hg_w hPhi_w
      have hsz := hsplit z hLamz hg_z hPhi_z
      have hrew : (logDeriv Lam w).re = (Complex.log (A : ℂ)).re
          + (logDeriv (corrFac c₁ c₂ S) w).re + (logDeriv Phi w).re := by
        rw [hsw, Complex.add_re, Complex.add_re]
      have hrez : (logDeriv Lam z).re = (Complex.log (A : ℂ)).re
          + (logDeriv (corrFac c₁ c₂ S) z).re + (logDeriv Phi z).re := by
        rw [hsz, Complex.add_re, Complex.add_re]
      have hreFE : (deriv Phi w / Phi w).re = -(deriv Phi z / Phi z).re := by
        rw [hFEΦ]
        simp only [Complex.neg_re, Complex.star_def, Complex.conj_re]
      have hPhi_w_eq : (logDeriv Phi w).re = -(logDeriv Phi z).re := by
        rw [logDeriv_apply, logDeriv_apply]
        exact hreFE
      -- bounds on the two `corrFac` terms
      have hB := corrFacLogDerivReBound d c₁ c₂ S hd hS
      have hbw : -(3 * Real.log (4 * (d : ℝ)))
          ≤ (logDeriv (corrFac c₁ c₂ S) w).re := by
        have h := (abs_le.mp (hB.1 γ)).1
        simpa only [hw] using h
      have hbz : -(3 * Real.log (4 * (d : ℝ)))
          ≤ (logDeriv (corrFac c₁ c₂ S) z).re := by
        have h := (abs_le.mp (hB.2 γ)).1
        simpa only [hz] using h
      have hlogA : (Complex.log (A : ℂ)).re ≤ Real.log (4 * (d : ℝ)) := by
        rw [Complex.log_re, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hApos]
        refine Real.log_le_log hApos ?_
        rw [hAdef, div_le_iff₀ hXpos]
        nlinarith [hX1]
      have hlogA0 : 0 ≤ (Complex.log (A : ℂ)).re := by
        rw [Complex.log_re, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hApos]
        refine Real.log_nonneg ?_
        rw [hAdef, le_div_iff₀ hXpos]
        nlinarith [hX4]
      have hC3z := hC3 d chi m Lam ⟨hd, hchi, hAn, hagr⟩ γ
      rw [← logDeriv_apply] at hC3z
      have hkey : (logDeriv Lam w).re
          = 2 * (Complex.log (A : ℂ)).re + (logDeriv (corrFac c₁ c₂ S) w).re
            + (logDeriv (corrFac c₁ c₂ S) z).re - (logDeriv Lam z).re := by
        rw [hrew, hPhi_w_eq, hrez]
        ring
      have hgoal : -((C3 + 8) * Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |γ| + 3)))
          ≤ (logDeriv Lam w).re := by
        have h1 : (logDeriv Lam w).re
            ≥ -(6 * Real.log (4 * (d : ℝ)))
              - C3 * Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |γ| + 3)) := by
          rw [hkey]
          linarith [hlogA0, hbw, hbz, hC3z]
        have h2 : -(6 * Real.log (4 * (d : ℝ)))
              - C3 * Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |γ| + 3))
            ≥ -((C3 + 8) * Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |γ| + 3))) := by
          have h40 : 0 ≤ Real.log (4 * (d : ℝ)) := by
            refine Real.log_nonneg ?_
            have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
            linarith
          nlinarith [hlogpos, hlog4d, h40, hC3pos]
        linarith [h1, h2]
      rw [logDeriv_apply] at hgoal
      exact hgoal
  · push_neg at hne
    exact absurd
      (noCompletion_of_primaryTrivial d chi m hd hchi hne)
      (fun h => h ⟨Lam, hAn, hagr⟩)

end

end Work.FIArea6Hecke.R
