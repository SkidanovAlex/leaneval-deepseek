import Mathlib
import Submission.Work.FIArea6Hecke.R.logDerivCore
import Submission.Work.FIArea6Hecke.R.baseLowerNegTwoUniform
import Submission.Work.FIArea6Hecke.R.baseLowerTwoUniform
import Submission.Work.FIArea6Hecke.R.zerosInStrip
import Submission.Work.FIArea6Hecke.R.lamGrowth
import Submission.Work.FIArea6Hecke.R.lamPartialFraction
import Submission.Work.FIArea6Hecke.R.HeckeLambdaLogDerivBounds
import Submission.Work.FIArea6Hecke.R.LogDerivStatementDefs
import Submission.Work.FIArea6Hecke.R.ZFRStatementDefs
import Submission.Work.FIArea6Hecke.R.HasConductorFEDefs
import Submission.Port.LogDerivCompat

/-!
# `Submission.Work.FIArea6Hecke.R.heckeStripLogDerivConductor`

Conductor-parameterised forms of the two analytic inputs of `logDerivReLower_of_baseBounds`, so that
the logarithmic-derivative chain of `R/heckeStripLogDeriv` can be closed against the *clean*
general-conductor functional equation `Work.FIArea6Hecke.R.conductorFEClean`
(`R/conductorFEClean.lean`) instead of the two stubs `R/levelHeckeFE` + `R/heckePartnerThetaLaw`
that the older `R/heckeFEStrictConductorUni` rests on.

* `baseLowerNegTwoUniform_of_conductorFE` — the uniform lower bound for `Re (Λ'/Λ)` at `re s = -2`
  (the input of the weighted zero sum `wzsOfPfDiff`), with the conductor-normalised functional
  equation supplied as a hypothesis.  This is `R/baseLowerNegTwoUniform.baseLowerNegTwoUniform`
  with its single call to `heckeFEStrictConductorUni` replaced by the hypothesis.
* `logDerivReLower_of_conductorFE` — the one-sided bound `LogDerivReLower ε` (*FI*
  (16.20)/(16.23)) assembled from that input, `R/zerosInStrip.zerosInStrip_of_conductorFE`,
  `R/baseLowerTwoUniform`, the Hadamard partial fraction `R/lamPartialFraction` (via the circle
  growth `R/lamGrowth`) and the upper bound at `re = 2`, together with the two zero-free-region
  inputs.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIArea6Hecke.R

/-! ## The corrected exceptional set of the zero-free region

`ZFRStatementDefs.ZFRoffAxis` excludes the pairs whose `psi` is real-valued on *all* of `ℤ[i]`.
That exceptional set is too narrow: the classical de la Vallée Poussin region (16.20) excludes only
the *self-dual* `L`-series, i.e. those with real Hecke eigenvalues; `psi` can be `±1` on the primary
units (all that the eigenvalues see, `heckeLam`) while taking non-real values on the other units, and
then the pair has an exceptional real zero all the same.  See `R/NOTES_zfrInterfaceFix.md`. -/

/-- **Self-duality of a strict-character pair**: `psi_{χ,m}(z) = χ(z)(z/|z|)^m` is `±1` on the
primary units, i.e. the Hecke eigenvalues `heckeLam χ m n` are real. -/
def SelfDual (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ) : Prop :=
  ∀ z : GaussianInt, Work.FIPlan.IsPrimary z → Work.FIArea5.S16Hecke.IsUnitMod4d d z →
    (Work.FIArea5.S16Hecke.psi chi m z) ^ 2 = 1

/-- **The de la Vallée Poussin region off the real axis, with the corrected exceptional set**
(*FI* (16.20)).  This is `ZFRStatementDefs.ZFRoffAxis` with `PsiReal` replaced by `SelfDual`; with
this exception the statement is the classical theorem (and is *provable*), while the
`PsiReal`-version is not (see `R/NOTES_zfrInterfaceFix.md`). -/
def ZFRoffAxisSd : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ) (Lam : ℂ → ℂ), 1 ≤ d →
      Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi →
      AnalyticOn ℂ Lam Set.univ →
      (∀ s : ℂ, 1 + |(m : ℝ)| / 2 < s.re →
        Lam s = Work.FITop4.Bridge.heckeArch d m s *
          Work.FIArea5.S16Hecke.heckeLSeries chi m s) →
      ∀ s : ℂ,
        1 - c / Real.log (4 * (d : ℝ) + |(m : ℝ)| + |s.im|) < s.re → s.re ≤ 2 →
          ¬ (s.im = 0 ∧ SelfDual d chi m) → Work.FIArea6Hecke.Lval d m Lam s ≠ 0

/-- **Lemma 16.1 (Landau–Siegel) on the real axis, with the corrected exceptional set**: this is
`ZFRStatementDefs.ZFRrealAxis ε` with `PsiReal` replaced by `SelfDual`. -/
def ZFRrealAxisSd (ε : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ) (Lam : ℂ → ℂ), 1 ≤ d →
      Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi →
      AnalyticOn ℂ Lam Set.univ →
      (∀ s : ℂ, 1 + |(m : ℝ)| / 2 < s.re →
        Lam s = Work.FITop4.Bridge.heckeArch d m s *
          Work.FIArea5.S16Hecke.heckeLSeries chi m s) →
      SelfDual d chi m →
      ∀ s : ℂ, s.im = 0 →
        1 - c / (d : ℝ) ^ ε < s.re → s.re ≤ 2 → Work.FIArea6Hecke.Lval d m Lam s ≠ 0


open Complex
open scoped BigOperators Topology

noncomputable section

theorem baseLowerNegTwoUniform_of_conductorFE
    (hFE0 : ∀ (d : ℕ) (hd : 1 ≤ d) (chi : GaussianInt → ℂ) (m : ℤ),
      Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi →
      (∃ z : GaussianInt, Work.FIPlan.IsPrimary z ∧ Work.FIArea5.S16Hecke.IsUnitMod4d d z ∧
        Work.FIArea5.S16Hecke.psi chi m z ≠ 1) →
      Work.FIArea6Hecke.R.HasConductorFE d chi m) :
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
      hFE0 d hd chi m hchi hne
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

/-- **The one-sided logarithmic-derivative bound in the zero-free region, from the
conductor-normalised functional equation.**  Identical to `R/logDerivReLower.logDerivReLower`
except that the functional-equation input is the clean
`Work.FIArea6Hecke.R.conductorFEClean` (through the hypothesis `hFE0`) rather than
`heckeFEStrictConductorUni`. -/
theorem logDerivReLower_of_conductorFE (ε : ℝ) (hε : 0 < ε) (hε4 : ε ≤ 1 / 4)
    (hFE0 : ∀ (d : ℕ) (hd : 1 ≤ d) (chi : GaussianInt → ℂ) (m : ℤ),
      Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi →
      (∃ z : GaussianInt, Work.FIPlan.IsPrimary z ∧ Work.FIArea5.S16Hecke.IsUnitMod4d d z ∧
        Work.FIArea5.S16Hecke.psi chi m z ≠ 1) →
      Work.FIArea6Hecke.R.HasConductorFE d chi m)
    (hoff : ZFRoffAxis) (hreal : ZFRrealAxis ε) :
    LogDerivReLower ε := by
  have hBase2u : ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ) (Lam : ℂ → ℂ),
      IsCompleted d chi m Lam → ∀ γ : ℝ,
        (deriv Lam ((2 : ℂ) + (γ : ℂ) * Complex.I) / Lam ((2 : ℂ) + (γ : ℂ) * Complex.I)).re
          ≤ C * Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |γ| + 3)) := by
    obtain ⟨Cu, hCu, hle⟩ := lam_logDeriv_re_at_two_le_uniform
    refine ⟨Cu, hCu, ?_⟩
    intro d chi m Lam hadm γ
    obtain ⟨hd, hchi, hAn, hagr⟩ := hadm
    obtain ⟨h1, hmul, hb, -, -⟩ := hchi.1
    have h := hle d chi m Lam hd h1 hmul hb hAn hagr γ
    rw [mul_comm Complex.I] at h
    exact h
  refine logDerivReLower_of_baseBounds ε hε hε4 ?_ hBase2u baseLowerTwoUniform
    (baseLowerNegTwoUniform_of_conductorFE (fun d hd chi m hchi hnt => hFE0 d hd chi m hchi hnt))
    (zerosInStrip_of_conductorFE (fun d chi m hd hchi hnt => hFE0 d hd chi m hchi hnt)) hoff hreal
  intro d chi m Lam hadm
  exact lamPartialFraction d chi m Lam hadm (lamGrowth d chi m Lam hadm)


/-! ## The `L'/L` assembly with the corrected exceptional set

Below are `R/logDerivCore.logDerivReLower_of` and `R/logDerivCore.logDerivReLower_of_baseBounds`
copied verbatim with the two zero-free-region inputs `ZFRoffAxis` / `ZFRrealAxis ε` replaced by the
corrected statements `ZFRoffAxisSd` / `ZFRrealAxisSd ε` (whose exceptional set is the self-dual one
— see `R/NOTES_zfrInterfaceFix.md`).  The only other change is the case split in `hleft`, which is
now on `SelfDual` instead of `PsiReal`.  Everything else (the Hadamard partial fraction, the kernel
bounds, the weighted zero sum, the archimedean conversion) is unchanged.
-/

theorem logDerivReLowerSd_of (ε : ℝ) (hε : 0 < ε) (hε4 : ε ≤ 1 / 4)
    (hpf : ∀ (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ) (Lam : ℂ → ℂ),
      IsCompleted d chi m Lam → ∀ s s₁ : ℂ, Lam s ≠ 0 → Lam s₁ ≠ 0 →
        Filter.Tendsto (fun R : ℝ => ∑ᶠ u : ℂ, (((divR Lam R u : ℤ) : ℂ)
          * (1 / (s - u) - 1 / (s₁ - u)))) Filter.atTop
          (nhds (deriv Lam s / Lam s - deriv Lam s₁ / Lam s₁)))
    (hWZS : ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ) (Lam : ℂ → ℂ),
      IsCompleted d chi m Lam → ∀ (t R : ℝ), 1 ≤ R →
        ∑ᶠ u : ℂ, ((divR Lam R u : ℤ) : ℝ) / (1 + (t - u.im) ^ 2)
          ≤ C * Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |t| + 3)))
    (hBase : ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ) (Lam : ℂ → ℂ),
      IsCompleted d chi m Lam → ∀ γ : ℝ,
        -(C * Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |γ| + 3)))
          ≤ (deriv Lam ((2 : ℂ) + (γ : ℂ) * Complex.I) / Lam ((2 : ℂ) + (γ : ℂ) * Complex.I)).re)
    (hZeros : ∀ (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ) (Lam : ℂ → ℂ),
      IsCompleted d chi m Lam → ∀ u : ℂ, Lam u = 0 → -1 ≤ u.re ∧ u.re ≤ 1)
    (hoff : ZFRoffAxisSd) (hreal : ZFRrealAxisSd ε) :
    LogDerivReLower ε := by
  obtain ⟨c₁, hc₁, hoff'⟩ := hoff
  obtain ⟨c₂, hc₂, hreal'⟩ := hreal
  obtain ⟨CW, hCW, hWZS'⟩ := hWZS
  obtain ⟨CB, hCB, hBase'⟩ := hBase
  refine ⟨min (min c₁ c₂ / 4) (1 / 4), CB + 12 * CW + 7, lt_min (by positivity) (by norm_num),
    by positivity, ?_⟩
  intro d chi m Lam hd hchi hAn hagr s hlo hhi
  have hadm : IsCompleted d chi m Lam := ⟨hd, hchi, hAn, hagr⟩
  have hcpos : 0 < min (min c₁ c₂ / 4) (1 / 4) := lt_min (by positivity) (by norm_num)
  have hc₁' : min (min c₁ c₂ / 4) (1 / 4) ≤ c₁ := by
    have h1 : min c₁ c₂ ≤ c₁ := min_le_left _ _
    have h2 : min c₁ c₂ / 4 ≤ min c₁ c₂ := by
      have : (0 : ℝ) < min c₁ c₂ := lt_min hc₁ hc₂
      linarith
    have h3 : min (min c₁ c₂ / 4) (1 / 4) ≤ min c₁ c₂ / 4 := min_le_left _ _
    linarith
  have hc₂' : min (min c₁ c₂ / 4) (1 / 4) ≤ c₂ := by
    have h1 : min c₁ c₂ ≤ c₂ := min_le_right _ _
    have h2 : min c₁ c₂ / 4 ≤ min c₁ c₂ := by
      have : (0 : ℝ) < min c₁ c₂ := lt_min hc₁ hc₂
      linarith
    have h3 : min (min c₁ c₂ / 4) (1 / 4) ≤ min c₁ c₂ / 4 := min_le_left _ _
    linarith
  have hLpos : 0 < Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |s.im| + 3)) := by
    refine Real.log_pos ?_
    have h1 := abs_nonneg (m : ℝ); have h2 := abs_nonneg s.im
    have hd' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    nlinarith
  have hLnn : 0 ≤ Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |s.im| + 3)) := hLpos.le
  by_cases hLv : Lval d m Lam s = 0
  · rw [hLv, div_zero]
    simp only [Complex.zero_re]
    exact neg_nonpos.mpr (mul_nonneg (by positivity) hLnn)
  · have hσ_half : (1 : ℝ) / 2 ≤ s.re := by
      have hden : (0 : ℝ) < (d : ℝ) ^ ε := Real.rpow_pos_of_pos (by exact_mod_cast hd) ε
      have hmin1 : min (1 / Real.log (4 * (d : ℝ) + |(m : ℝ)| + |s.im| + 1))
          (1 / (d : ℝ) ^ ε) ≤ 1 := by
        refine le_trans (min_le_right _ _) ?_
        rw [div_le_one hden]
        exact Real.one_le_rpow (by exact_mod_cast hd) hε.le
      have hcm : min (min c₁ c₂ / 4) (1 / 4)
          * min (1 / Real.log (4 * (d : ℝ) + |(m : ℝ)| + |s.im| + 1)) (1 / (d : ℝ) ^ ε)
          ≤ min (min c₁ c₂ / 4) (1 / 4) := by
        calc min (min c₁ c₂ / 4) (1 / 4)
            * min (1 / Real.log (4 * (d : ℝ) + |(m : ℝ)| + |s.im| + 1)) (1 / (d : ℝ) ^ ε)
            ≤ min (min c₁ c₂ / 4) (1 / 4) * 1 :=
              mul_le_mul_of_nonneg_left hmin1 hcpos.le
          _ = min (min c₁ c₂ / 4) (1 / 4) := mul_one _
      have hquarter : min (min c₁ c₂ / 4) (1 / 4) ≤ 1 / 4 := min_le_right _ _
      linarith
    have hA : Work.FITop4.Bridge.heckeArch d m s ≠ 0 :=
      heckeArch_ne_zero_of_pos_re d hd m (by linarith)
    have hLs : Lam s ≠ 0 := by
      intro h0
      exact hLv (by rw [Lval, h0, zero_div])
    have hs₁_ne : Lam ((2 : ℂ) + (s.im : ℂ) * Complex.I) ≠ 0 := by
      intro h0
      have hz2 := (hZeros d chi m Lam hadm _ h0).2
      have hre : ((2 : ℂ) + (s.im : ℂ) * Complex.I).re = 2 := by simp
      rw [hre] at hz2
      norm_num at hz2
    have hleft : ∀ u : ℂ, Lam u = 0 → |s.im - u.im| < 1 → u.re ≤ s.re := by
      intro u hu hlt
      by_cases hA0 : Work.FITop4.Bridge.heckeArch d m u = 0
      · have := heckeArch_eq_zero_imp_re_le_zero d hd hA0
        linarith
      · have hLval_u : Lval d m Lam u = 0 := by rw [Lval, hu, zero_div]
        by_cases hexc : u.im = 0 ∧ SelfDual d chi m
        · have hzr : u.re ≤ 1 - c₂ * (1 / (d : ℝ) ^ ε) := by
            by_contra hcon
            push Not at hcon
            have hcon' : 1 - c₂ / (d : ℝ) ^ ε < u.re := by
              have he : c₂ * (1 / (d : ℝ) ^ ε) = c₂ / (d : ℝ) ^ ε := by
                rw [div_eq_mul_inv]; ring
              linarith
            exact (hreal' d chi m Lam hd hchi hAn hagr hexc.2 u hexc.1 hcon'
              (by have := (hZeros d chi m Lam hadm u hu).2; linarith)) hLval_u
          have hcmp : min (min c₁ c₂ / 4) (1 / 4)
              * min (1 / Real.log (4 * (d : ℝ) + |(m : ℝ)| + |s.im| + 1)) (1 / (d : ℝ) ^ ε)
              ≤ c₂ * (1 / (d : ℝ) ^ ε) := by
            have h2 : min (min c₁ c₂ / 4) (1 / 4) * (1 / (d : ℝ) ^ ε)
                ≤ c₂ * (1 / (d : ℝ) ^ ε) :=
              mul_le_mul_of_nonneg_right hc₂' (by positivity)
            have h3 : min (min c₁ c₂ / 4) (1 / 4)
                * min (1 / Real.log (4 * (d : ℝ) + |(m : ℝ)| + |s.im| + 1)) (1 / (d : ℝ) ^ ε)
                ≤ min (min c₁ c₂ / 4) (1 / 4) * (1 / (d : ℝ) ^ ε) :=
              mul_le_mul_of_nonneg_left (min_le_right _ _) hcpos.le
            linarith
          linarith
        · have hzr : u.re ≤ 1 - c₁ * (1 / Real.log (4 * (d : ℝ) + |(m : ℝ)| + |u.im|)) := by
            by_contra hcon
            push Not at hcon
            have hcon' : 1 - c₁ / Real.log (4 * (d : ℝ) + |(m : ℝ)| + |u.im|) < u.re := by
              have he : c₁ * (1 / Real.log (4 * (d : ℝ) + |(m : ℝ)| + |u.im|))
                  = c₁ / Real.log (4 * (d : ℝ) + |(m : ℝ)| + |u.im|) := by
                rw [div_eq_mul_inv]; ring
              linarith
            exact (hoff' d chi m Lam hd hchi hAn hagr u hcon'
              (by have := (hZeros d chi m Lam hadm u hu).2; linarith) hexc) hLval_u
          have hlogpos' : 0 < Real.log (4 * (d : ℝ) + |(m : ℝ)| + |u.im|) := by
            refine Real.log_pos ?_
            have h1 := abs_nonneg (m : ℝ); have h2 := abs_nonneg u.im
            have hd' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
            nlinarith
          have hlogpos'' : 0 < Real.log (4 * (d : ℝ) + |(m : ℝ)| + |s.im| + 1) := by
            refine Real.log_pos ?_
            have h1 := abs_nonneg (m : ℝ); have h2 := abs_nonneg s.im
            have hd' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
            nlinarith
          have hlog1 : Real.log (4 * (d : ℝ) + |(m : ℝ)| + |u.im|)
              ≤ Real.log (4 * (d : ℝ) + |(m : ℝ)| + |s.im| + 1) := by
            refine Real.log_le_log (by positivity) ?_
            have h1 : |u.im| ≤ |u.im - s.im| + |s.im| := by
              have := abs_add_le (u.im - s.im) s.im
              simpa using this
            have h2 : |u.im - s.im| < 1 := by rw [abs_sub_comm]; exact hlt
            linarith
          have hcmp : min (min c₁ c₂ / 4) (1 / 4)
              * min (1 / Real.log (4 * (d : ℝ) + |(m : ℝ)| + |s.im| + 1)) (1 / (d : ℝ) ^ ε)
              ≤ c₁ * (1 / Real.log (4 * (d : ℝ) + |(m : ℝ)| + |u.im|)) := by
            have h3 : min (min c₁ c₂ / 4) (1 / 4)
                * min (1 / Real.log (4 * (d : ℝ) + |(m : ℝ)| + |s.im| + 1)) (1 / (d : ℝ) ^ ε)
                ≤ min (min c₁ c₂ / 4) (1 / 4)
                  * (1 / Real.log (4 * (d : ℝ) + |(m : ℝ)| + |s.im| + 1)) :=
              mul_le_mul_of_nonneg_left (min_le_left _ _) hcpos.le
            have h5 : min (min c₁ c₂ / 4) (1 / 4)
                * (1 / Real.log (4 * (d : ℝ) + |(m : ℝ)| + |s.im| + 1))
                ≤ c₁ * (1 / Real.log (4 * (d : ℝ) + |(m : ℝ)| + |s.im| + 1)) :=
              mul_le_mul_of_nonneg_right hc₁' (by positivity)
            have h6 : (1 : ℝ) / Real.log (4 * (d : ℝ) + |(m : ℝ)| + |s.im| + 1)
                ≤ 1 / Real.log (4 * (d : ℝ) + |(m : ℝ)| + |u.im|) := by
              rw [one_div, one_div]
              exact inv_anti₀ hlogpos' hlog1
            have h7 : c₁ * (1 / Real.log (4 * (d : ℝ) + |(m : ℝ)| + |s.im| + 1))
                ≤ c₁ * (1 / Real.log (4 * (d : ℝ) + |(m : ℝ)| + |u.im|)) :=
              mul_le_mul_of_nonneg_left h6 hc₁.le
            linarith
          linarith
    have hmain := logDeriv_re_ge_of_pf (Λ := Lam) hAn (hpf d chi m Lam hadm)
      (hZeros d chi m Lam hadm) (s := s) (σ := s.re) (t := s.im)
      (W := CW * Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |s.im| + 3)))
      (by apply Complex.ext <;> simp) hleft
      (fun R hR => hWZS' d chi m Lam hadm s.im R hR) (by linarith) hhi hLs hs₁_ne
    have hbasei := hBase' d chi m Lam hadm s.im
    have harch := logDeriv_heckeArch_re_le d hd m (s := s) hσ_half hhi
    rw [logDeriv_apply] at harch
    have hident := lval_logDeriv_eq (m := m) d hd hAn (s := s) (by linarith) hLs
    rw [hident, Complex.sub_re]
    linarith


/-- **The one-sided bound from the Hadamard partial fraction and the base bounds.**  This is
`logDerivReLower_of` with its weighted-zero-sum hypothesis *derived* (via `wzsOfPfDiff`) from the
partial fraction and the bounds on `Re (Λ'/Λ)` at the two vertical lines `re = 2`, `re = -2`;
the three bound functions are those of the genuinely classical inputs (the base bounds of *FI*
§16, available from the absolutely convergent Euler product and the functional equation). -/
theorem logDerivReLowerSd_of_baseBounds (ε : ℝ) (hε : 0 < ε) (hε4 : ε ≤ 1 / 4)
    (hpf : ∀ (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ) (Lam : ℂ → ℂ),
      IsCompleted d chi m Lam → ∀ s s₁ : ℂ, Lam s ≠ 0 → Lam s₁ ≠ 0 →
        Filter.Tendsto (fun R : ℝ => ∑ᶠ u : ℂ, (((divR Lam R u : ℤ) : ℂ)
          * (1 / (s - u) - 1 / (s₁ - u)))) Filter.atTop
          (nhds (deriv Lam s / Lam s - deriv Lam s₁ / Lam s₁)))
    (hBase2u : ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ) (Lam : ℂ → ℂ),
      IsCompleted d chi m Lam → ∀ γ : ℝ,
        (deriv Lam ((2 : ℂ) + (γ : ℂ) * Complex.I) / Lam ((2 : ℂ) + (γ : ℂ) * Complex.I)).re
          ≤ C * Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |γ| + 3)))
    (hBase2l : ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ) (Lam : ℂ → ℂ),
      IsCompleted d chi m Lam → ∀ γ : ℝ,
        -(C * Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |γ| + 3)))
          ≤ (deriv Lam ((2 : ℂ) + (γ : ℂ) * Complex.I) / Lam ((2 : ℂ) + (γ : ℂ) * Complex.I)).re)
    (hBasem2l : ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ) (Lam : ℂ → ℂ),
      IsCompleted d chi m Lam → ∀ γ : ℝ,
        -(C * Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |γ| + 3)))
          ≤ (deriv Lam ((-2 : ℂ) + (γ : ℂ) * Complex.I) / Lam ((-2 : ℂ) + (γ : ℂ) * Complex.I)).re)
    (hZeros : ∀ (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ) (Lam : ℂ → ℂ),
      IsCompleted d chi m Lam → ∀ u : ℂ, Lam u = 0 → -1 ≤ u.re ∧ u.re ≤ 1)
    (hoff : ZFRoffAxisSd) (hreal : ZFRrealAxisSd ε) :
    LogDerivReLower ε := by
  obtain ⟨C1, hC1, hB2u⟩ := hBase2u
  obtain ⟨C2, hC2, hB2l⟩ := hBase2l
  obtain ⟨C3, hC3, hBm2l⟩ := hBasem2l
  have hlogpos : ∀ (d : ℕ) (m : ℤ) (t : ℝ), 1 ≤ d →
      0 < Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |t| + 3)) := by
    intro d m t hd
    refine Real.log_pos ?_
    have h1 := abs_nonneg (m : ℝ); have h2 := abs_nonneg t
    have hd' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    nlinarith
  have hWZS : ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ) (Lam : ℂ → ℂ),
      IsCompleted d chi m Lam → ∀ (t R : ℝ), 1 ≤ R →
        ∑ᶠ u : ℂ, ((divR Lam R u : ℤ) : ℝ) / (1 + (t - u.im) ^ 2)
          ≤ C * Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |t| + 3)) := by
    refine ⟨13 * (C1 + (C2 + C3)), by positivity, ?_⟩
    intro d chi m Lam hadm t R hR
    have hd : 1 ≤ d := hadm.1
    have hL := hlogpos d m t hd
    have hDiff : Differentiable ℂ Lam :=
      differentiableOn_univ.mp hadm.2.2.1.differentiableOn
    have hBm2' : ∀ γ : ℝ,
        -((C2 + C3) * Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |γ| + 3)))
          ≤ (deriv Lam ((-2 : ℂ) + (γ : ℂ) * Complex.I)
              / Lam ((-2 : ℂ) + (γ : ℂ) * Complex.I)).re := by
      intro γ
      have hb := hBm2l d chi m Lam hadm γ
      have hle : C3 * Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |γ| + 3))
          ≤ (C2 + C3) * Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |γ| + 3)) := by
        have hgamma := hlogpos d m γ hd
        nlinarith [hgamma.le, hC2]
      linarith
    have hw := wzsOfPfDiff Lam hDiff (hpf d chi m Lam hadm) (hZeros d chi m Lam hadm)
      (fun γ : ℝ => C1 * Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |γ| + 3)))
      (fun γ : ℝ => (C2 + C3) * Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |γ| + 3)))
      (fun γ => hB2u d chi m Lam hadm γ) hBm2' t R hR
    simp only [divR] at hw ⊢
    have hgoal : 13 * (C1 * Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |t| + 3))
        + (C2 + C3) * Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |t| + 3)))
        = 13 * (C1 + (C2 + C3)) * Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |t| + 3)) := by
      ring
    linarith [hw, hgoal.le, hgoal.ge]
  exact logDerivReLowerSd_of ε hε hε4 hpf hWZS ⟨C2, hC2, hB2l⟩ hZeros hoff hreal

/-- **The one-sided logarithmic-derivative bound in the zero-free region, from the corrected
zero-free-region inputs and the conductor-normalised functional equation.**  This is
`R/logDerivCore.logDerivReLower_of_baseBounds` with

* the two zero-free-region inputs replaced by the corrected statements `ZFRoffAxisSd` and
  `ZFRrealAxisSd ε` (self-dual exceptional set) and
* the two analytic inputs at `re s = 2` and `re s = -2` taken in their clean form
  (`baseLowerTwoUniform`, `baseLowerNegTwoUniform_of_conductorFE hFE0`), so that the only
  non-elementary ingredient is the conductor-normalised functional equation supplied through
  `hFE0` (e.g. `Work.FIArea6Hecke.R.conductorFEClean`). -/
theorem logDerivReLower_of_conductorFESd (ε : ℝ) (hε : 0 < ε) (hε4 : ε ≤ 1 / 4)
    (hFE0 : ∀ (d : ℕ) (hd : 1 ≤ d) (chi : GaussianInt → ℂ) (m : ℤ),
      Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi →
      (∃ z : GaussianInt, Work.FIPlan.IsPrimary z ∧ Work.FIArea5.S16Hecke.IsUnitMod4d d z ∧
        Work.FIArea5.S16Hecke.psi chi m z ≠ 1) →
      Work.FIArea6Hecke.R.HasConductorFE d chi m)
    (hoff : ZFRoffAxisSd) (hreal : ZFRrealAxisSd ε) :
    LogDerivReLower ε := by
  have hBase2u : ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ) (Lam : ℂ → ℂ),
      IsCompleted d chi m Lam → ∀ γ : ℝ,
        (deriv Lam ((2 : ℂ) + (γ : ℂ) * Complex.I) / Lam ((2 : ℂ) + (γ : ℂ) * Complex.I)).re
          ≤ C * Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |γ| + 3)) := by
    obtain ⟨Cu, hCu, hle⟩ := lam_logDeriv_re_at_two_le_uniform
    refine ⟨Cu, hCu, ?_⟩
    intro d chi m Lam hadm γ
    obtain ⟨hd, hchi, hAn, hagr⟩ := hadm
    obtain ⟨h1, hmul, hb, -, -⟩ := hchi.1
    have h := hle d chi m Lam hd h1 hmul hb hAn hagr γ
    rw [mul_comm Complex.I] at h
    exact h
  refine logDerivReLowerSd_of_baseBounds ε hε hε4 ?_ hBase2u baseLowerTwoUniform
    (baseLowerNegTwoUniform_of_conductorFE (fun d hd chi m hchi hnt => hFE0 d hd chi m hchi hnt))
    (zerosInStrip_of_conductorFE (fun d chi m hd hchi hnt => hFE0 d hd chi m hchi hnt)) hoff hreal
  intro d chi m Lam hadm
  exact lamPartialFraction d chi m Lam hadm (lamGrowth d chi m Lam hadm)

private lemma hbr_ballOffAxisRegion {ε cA κ : ℝ} (hcA : 0 < cA) (hκ : 0 ≤ κ) (hκcA : κ ≤ cA)
    (d : ℕ) (hd : 1 ≤ d) (m : ℤ) (t gre : ℝ) (w : ℂ)
    (hUt : |w.im| ≤ |t| + 1)
    (hreg : 1 - (κ / 2) * min (1 / Real.log (4 * (d : ℝ) + |(m : ℝ)| + |t| + 1))
        (1 / (d : ℝ) ^ ε) ≤ gre)
    (hgre : gre < w.re) :
    1 - cA / Real.log (4 * (d : ℝ) + |(m : ℝ)| + |w.im|) < w.re := by
  set Lt := Real.log (4 * (d : ℝ) + |(m : ℝ)| + |t| + 1) with hLtdef
  set Lw := Real.log (4 * (d : ℝ) + |(m : ℝ)| + |w.im|) with hLwdef
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hMnn : (0 : ℝ) ≤ |(m : ℝ)| := abs_nonneg _
  have hUnn : (0 : ℝ) ≤ |w.im| := abs_nonneg _
  have hSnn : (0 : ℝ) ≤ |t| := abs_nonneg _
  have hAwpos : 0 < 4 * (d : ℝ) + |(m : ℝ)| + |w.im| := by linarith
  have hAtpos : 0 < 4 * (d : ℝ) + |(m : ℝ)| + |t| + 1 := by linarith
  have hLwpos : 0 < Lw := by
    rw [hLwdef]; exact Real.log_pos (by linarith)
  have hLtpos : 0 < Lt := by
    rw [hLtdef]; exact Real.log_pos (by linarith)
  have hLwle : Lw ≤ Lt := by
    rw [hLwdef, hLtdef]
    exact Real.log_le_log hAwpos (by linarith)
  have hminle : min (1 / Lt) (1 / (d : ℝ) ^ ε) ≤ 1 / Lw :=
    le_trans (min_le_left _ _) (one_div_le_one_div_of_le hLwpos hLwle)
  have hstep1 : (κ / 2) * min (1 / Lt) (1 / (d : ℝ) ^ ε) ≤ (κ / 2) * (1 / Lw) :=
    mul_le_mul_of_nonneg_left hminle (by linarith)
  have hstep2 : (κ / 2) * (1 / Lw) < cA * (1 / Lw) := by
    have h1 : κ / 2 < cA := by linarith
    exact mul_lt_mul_of_pos_right h1 (one_div_pos.mpr hLwpos)
  have hmain : 1 - cA * (1 / Lw) < w.re := by linarith
  have hconv : cA * (1 / Lw) = cA / Lw := by ring
  linarith [hmain, hconv]

/-- **Containment in the Siegel region on the real axis.**  If `gre` dominates the left edge and
`w.re > gre`, then `1 - cB/d^ε < w.re`, provided `κ ≤ cB`. -/
private lemma hbr_ballRealAxisRegion {ε cB κ : ℝ} (_hε : 0 < ε) (hcB : 0 < cB) (hκ : 0 ≤ κ)
    (hκcB : κ ≤ cB) (d : ℕ) (hd : 1 ≤ d) (m : ℤ) (t gre : ℝ) (w : ℂ)
    (hreg : 1 - (κ / 2) * min (1 / Real.log (4 * (d : ℝ) + |(m : ℝ)| + |t| + 1))
        (1 / (d : ℝ) ^ ε) ≤ gre)
    (hgre : gre < w.re) :
    1 - cB / (d : ℝ) ^ ε < w.re := by
  set X := (d : ℝ) ^ ε with hXdef
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < (d : ℝ) := by linarith
  have hXpos : 0 < X := by rw [hXdef]; exact Real.rpow_pos_of_pos hdpos ε
  have hminle : min (1 / Real.log (4 * (d : ℝ) + |(m : ℝ)| + |t| + 1)) (1 / X) ≤ 1 / X :=
    min_le_right _ _
  have hstep1 : (κ / 2) * min (1 / Real.log (4 * (d : ℝ) + |(m : ℝ)| + |t| + 1)) (1 / X)
      ≤ (κ / 2) * (1 / X) :=
    mul_le_mul_of_nonneg_left hminle (by linarith)
  have hstep2 : (κ / 2) * (1 / X) < cB * (1 / X) := by
    have h1 : κ / 2 < cB := by linarith
    exact mul_lt_mul_of_pos_right h1 (one_div_pos.mpr hXpos)
  have hmain : 1 - cB * (1 / X) < w.re := by linarith
  have hconv : cB * (1 / X) = cB / X := by ring
  linarith [hmain, hconv]

/-- **Containment in the region of the one-sided logarithmic-derivative input.**  If
`|w.im| ≤ |t| + 1` and `w.re > gre` with `gre` dominating the left edge of the target region, then
`w` satisfies `1 - c1·min(1/log(4d+|m|+|w.im|+1), d^{-ε}) ≤ w.re`, provided `κ ≤ c1`. -/
private lemma hbr_ballLogDerivRegion {ε c1 κ : ℝ} (_hε : 0 < ε) (_hc1 : 0 < c1) (hκ : 0 ≤ κ)
    (hκc1 : κ ≤ c1) (d : ℕ) (hd : 1 ≤ d) (m : ℤ) (t gre : ℝ) (w : ℂ)
    (hUt : |w.im| ≤ |t| + 1)
    (hreg : 1 - (κ / 2) * min (1 / Real.log (4 * (d : ℝ) + |(m : ℝ)| + |t| + 1))
        (1 / (d : ℝ) ^ ε) ≤ gre)
    (hgre : gre < w.re) :
    1 - c1 * min (1 / Real.log (4 * (d : ℝ) + |(m : ℝ)| + |w.im| + 1)) (1 / (d : ℝ) ^ ε)
        ≤ w.re := by
  set Lt := Real.log (4 * (d : ℝ) + |(m : ℝ)| + |t| + 1) with hLtdef
  set Ltw := Real.log (4 * (d : ℝ) + |(m : ℝ)| + |w.im| + 1) with hLtwdef
  set X := (d : ℝ) ^ ε with hXdef
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < (d : ℝ) := by linarith
  have hMnn : (0 : ℝ) ≤ |(m : ℝ)| := abs_nonneg _
  have hUnn : (0 : ℝ) ≤ |w.im| := abs_nonneg _
  have hSnn : (0 : ℝ) ≤ |t| := abs_nonneg _
  have hAtpos : 0 < 4 * (d : ℝ) + |(m : ℝ)| + |t| + 1 := by linarith
  have hAtwpos : 0 < 4 * (d : ℝ) + |(m : ℝ)| + |w.im| + 1 := by linarith
  have hXpos : 0 < X := by rw [hXdef]; exact Real.rpow_pos_of_pos hdpos ε
  have hLtpos : 0 < Lt := by
    rw [hLtdef]; exact Real.log_pos (by linarith)
  have hLtwpos : 0 < Ltw := by
    rw [hLtwdef]; exact Real.log_pos (by linarith)
  have hLtw_le : Ltw ≤ 2 * Lt := by
    rw [hLtwdef, hLtdef]
    exact log_le_two_mul_log hAtwpos (by linarith) (by linarith)
  have h1Ltwpos : 0 < 1 / Ltw := one_div_pos.mpr hLtwpos
  have h1Xpos : 0 < 1 / X := one_div_pos.mpr hXpos
  -- the key comparison `min(1/Lt, 1/X) ≤ 2 · min(1/Ltw, 1/X)`
  have hmin2 : min (1 / Lt) (1 / X) ≤ 2 * min (1 / Ltw) (1 / X) := by
    have h2a : (1 / Lt) ≤ 2 * (1 / Ltw) := by
      have h := one_div_le_one_div_of_le hLtwpos hLtw_le
      have h4 := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 2)
      have heq : 2 * (1 / (2 * Lt)) = 1 / Lt := by ring
      linarith [h4, heq]
    have h2b : (1 / X) ≤ 2 * (1 / X) := by linarith
    have hmul : min (2 * (1 / Ltw)) (2 * (1 / X)) = 2 * min (1 / Ltw) (1 / X) := by
      rcases le_total (1 / Ltw) (1 / X) with hle | hle
      · rw [min_eq_left hle, min_eq_left (mul_le_mul_of_nonneg_left hle (by norm_num))]
      · rw [min_eq_right hle, min_eq_right (mul_le_mul_of_nonneg_left hle (by norm_num))]
    calc min (1 / Lt) (1 / X) ≤ min (2 * (1 / Ltw)) (2 * (1 / X)) := min_le_min h2a h2b
      _ = 2 * min (1 / Ltw) (1 / X) := hmul
  have hmin_ge : (1 / 2) * min (1 / Lt) (1 / X) ≤ min (1 / Ltw) (1 / X) := by
    have hpos : 0 ≤ min (1 / Ltw) (1 / X) := le_of_lt (lt_min h1Ltwpos h1Xpos)
    linarith [hmin2, hpos]
  have hstep : (κ / 2) * min (1 / Lt) (1 / X) ≤ c1 * min (1 / Ltw) (1 / X) := by
    have h1 : (κ / 2) * min (1 / Lt) (1 / X) = κ * ((1 / 2) * min (1 / Lt) (1 / X)) := by ring
    have h2 : κ * ((1 / 2) * min (1 / Lt) (1 / X)) ≤ κ * min (1 / Ltw) (1 / X) :=
      mul_le_mul_of_nonneg_left hmin_ge hκ
    have h3 : κ * min (1 / Ltw) (1 / X) ≤ c1 * min (1 / Ltw) (1 / X) :=
      mul_le_mul_of_nonneg_right hκc1 (le_of_lt (lt_min h1Ltwpos h1Xpos))
    linarith [h1, h2, h3]
  have hgoal : 1 - c1 * min (1 / Ltw) (1 / X) ≤ w.re := by linarith
  exact hgoal

/-- **The right-hand log scale.**  `log(4d(|m|+|w.im|+3)) ≤ 2·log(4d(|m|+|t|+3))` when
`|w.im| ≤ |t| + 1` and `d ≥ 1`. -/
private lemma hbr_ballRhsScale (d : ℕ) (hd : 1 ≤ d) (m : ℤ) (t : ℝ) (w : ℂ)
    (hUt : |w.im| ≤ |t| + 1) :
    Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |w.im| + 3))
      ≤ 2 * Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |t| + 3)) := by
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < (d : ℝ) := by linarith
  have hMnn : (0 : ℝ) ≤ |(m : ℝ)| := abs_nonneg _
  have hUnn : (0 : ℝ) ≤ |w.im| := abs_nonneg _
  have hSnn : (0 : ℝ) ≤ |t| := abs_nonneg _
  have hApos : 0 < 4 * (d : ℝ) * (|(m : ℝ)| + |w.im| + 3) := by positivity
  have hstep : |(m : ℝ)| + |w.im| + 3 ≤ 2 * (|(m : ℝ)| + |t| + 3) := by linarith
  have hmult : 4 * (d : ℝ) * (|(m : ℝ)| + |w.im| + 3)
      ≤ 4 * (d : ℝ) * (2 * (|(m : ℝ)| + |t| + 3)) :=
    mul_le_mul_of_nonneg_left hstep (by positivity)
  have hab : 4 * (d : ℝ) * (|(m : ℝ)| + |w.im| + 3)
      ≤ 2 * (4 * (d : ℝ) * (|(m : ℝ)| + |t| + 3)) := by
    have heq : 4 * (d : ℝ) * (2 * (|(m : ℝ)| + |t| + 3))
        = 2 * (4 * (d : ℝ) * (|(m : ℝ)| + |t| + 3)) := by ring
    linarith [hmult, heq]
  have hB2 : (2 : ℝ) ≤ 4 * (d : ℝ) * (|(m : ℝ)| + |t| + 3) := by nlinarith
  exact log_le_two_mul_log hApos hB2 hab

/-! ## The ball-region lemma with the corrected exceptional set

`R/heckeStripBallRegions.heckeStripBallRegions` with `ZFRoffAxis` / `ZFRrealAxis ε` replaced by the
corrected `ZFRoffAxisSd` / `ZFRrealAxisSd ε` (case split on `SelfDual` instead of `PsiReal`).  The
containment lemmas `ballOffAxisRegion`, `ballRealAxisRegion`, `ballLogDerivRegion`, `ballRhsScale`
of `R/heckeStripBallRegions` are reused verbatim; only the exceptional-set case split changes.  This
is the same statement as the stub `R/heckeStripBallRegionsSd`, kept here so that the chain of
`R/heckeStripLogDeriv` does not depend on that file. -/

theorem heckeStripBallRegionsSdMine (ε : ℝ) (hε : 0 < ε)
    (hOne : Work.FIArea6Hecke.R.LogDerivReLower ε)
    (hA : Work.FIArea6Hecke.R.ZFRoffAxisSd)
    (hB : Work.FIArea6Hecke.R.ZFRrealAxisSd ε) :
    ∃ κ C : ℝ, 0 < κ ∧ κ ≤ 1 / 8 ∧ 0 < C ∧
      ∀ (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ) (Lam : ℂ → ℂ) (t γ R : ℝ), 1 ≤ d →
        Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi →
        AnalyticOn ℂ Lam Set.univ →
        (∀ s : ℂ, 1 + |(m : ℝ)| / 2 < s.re →
          Lam s = Work.FITop4.Bridge.heckeArch d m s *
            Work.FIArea5.S16Hecke.heckeLSeries chi m s) →
        1 < γ → γ + R ≤ 2 → 0 < R → R ≤ 1 →
        1 - (κ / 2) * min (1 / Real.log (4 * (d : ℝ) + |(m : ℝ)| + |t| + 1))
            (1 / (d : ℝ) ^ ε) ≤ γ - R →
        (∀ w : ℂ, ‖w - ((γ : ℂ) + (t : ℂ) * Complex.I)‖ < R →
            Work.FIArea6Hecke.Lval d m Lam w ≠ 0) ∧
        (∀ w : ℂ, ‖w - ((γ : ℂ) + (t : ℂ) * Complex.I)‖ < R →
            -(C * Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |t| + 3)))
              ≤ (deriv (Work.FIArea6Hecke.Lval d m Lam) w
                  / Work.FIArea6Hecke.Lval d m Lam w).re) := by
  obtain ⟨c1, C1, hc1pos, hC1pos, hone⟩ := hOne
  obtain ⟨cA, hcApos, hoff⟩ := hA
  obtain ⟨cB, hcBpos, hreal⟩ := hB
  have hκpos0 : 0 < min (min c1 cA) (min cB (1 / 8)) :=
    lt_min (lt_min hc1pos hcApos) (lt_min hcBpos (by norm_num))
  have hκ8 : min (min c1 cA) (min cB (1 / 8)) ≤ 1 / 8 :=
    le_trans (min_le_right _ _) (min_le_right _ _)
  have hCpos : 0 < 2 * C1 := by linarith
  refine ⟨min (min c1 cA) (min cB (1 / 8)), 2 * C1, hκpos0, hκ8, hCpos, ?_⟩
  intro d chi m Lam t γ R hd hchi hAn hagr _hγ1 hγR _hRpos hR1 hregion
  set κ : ℝ := min (min c1 cA) (min cB (1 / 8)) with hκdef
  set C : ℝ := 2 * C1 with hCdef
  have hκpos : 0 < κ := hκpos0
  have hκnn : 0 ≤ κ := le_of_lt hκpos
  have hκc1 : κ ≤ c1 := by rw [hκdef]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hκcA : κ ≤ cA := by rw [hκdef]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hκcB : κ ≤ cB := by rw [hκdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  constructor
  · intro w hw
    have hre_abs : |w.re - γ| < R := by
      have h := Complex.abs_re_le_norm (w - ((γ : ℂ) + (t : ℂ) * Complex.I))
      have h2 : (w - ((γ : ℂ) + (t : ℂ) * Complex.I)).re = w.re - γ := by simp
      rw [h2] at h
      linarith
    have him_abs : |w.im - t| < R := by
      have h := Complex.abs_im_le_norm (w - ((γ : ℂ) + (t : ℂ) * Complex.I))
      have h2 : (w - ((γ : ℂ) + (t : ℂ) * Complex.I)).im = w.im - t := by simp
      rw [h2] at h
      linarith
    have hwre_gt : γ - R < w.re := by
      have := (abs_lt.mp hre_abs).1; linarith
    have hwre_le2 : w.re ≤ 2 := by
      have := (abs_lt.mp hre_abs).2; linarith
    have hUt : |w.im| ≤ |t| + 1 := by
      have h1 := abs_sub_abs_le_abs_sub w.im t
      have h2 := him_abs
      linarith
    by_cases hrc : w.im = 0 ∧ SelfDual d chi m
    · have hlt : 1 - cB / (d : ℝ) ^ ε < w.re :=
        hbr_ballRealAxisRegion hε hcBpos hκnn hκcB d hd m t (γ - R) w hregion hwre_gt
      exact hreal d chi m Lam hd hchi hAn hagr hrc.2 w hrc.1 hlt hwre_le2
    · have hlt : 1 - cA / Real.log (4 * (d : ℝ) + |(m : ℝ)| + |w.im|) < w.re :=
        hbr_ballOffAxisRegion hcApos hκnn hκcA d hd m t (γ - R) w hUt hregion hwre_gt
      exact hoff d chi m Lam hd hchi hAn hagr w hlt hwre_le2 hrc
  · intro w hw
    have hre_abs : |w.re - γ| < R := by
      have h := Complex.abs_re_le_norm (w - ((γ : ℂ) + (t : ℂ) * Complex.I))
      have h2 : (w - ((γ : ℂ) + (t : ℂ) * Complex.I)).re = w.re - γ := by simp
      rw [h2] at h
      linarith
    have him_abs : |w.im - t| < R := by
      have h := Complex.abs_im_le_norm (w - ((γ : ℂ) + (t : ℂ) * Complex.I))
      have h2 : (w - ((γ : ℂ) + (t : ℂ) * Complex.I)).im = w.im - t := by simp
      rw [h2] at h
      linarith
    have hwre_gt : γ - R < w.re := by
      have := (abs_lt.mp hre_abs).1; linarith
    have hwre_le2 : w.re ≤ 2 := by
      have := (abs_lt.mp hre_abs).2; linarith
    have hUt : |w.im| ≤ |t| + 1 := by
      have h1 := abs_sub_abs_le_abs_sub w.im t
      have h2 := him_abs
      linarith
    have hreg_w : 1 - c1 * min (1 / Real.log (4 * (d : ℝ) + |(m : ℝ)| + |w.im| + 1))
        (1 / (d : ℝ) ^ ε) ≤ w.re :=
      hbr_ballLogDerivRegion hε hc1pos hκnn hκc1 d hd m t (γ - R) w hUt hregion hwre_gt
    have h1 := hone d chi m Lam hd hchi hAn hagr w hreg_w hwre_le2
    have hscale : Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |w.im| + 3))
        ≤ 2 * Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |t| + 3)) :=
      hbr_ballRhsScale d hd m t w hUt
    have hC1log : C1 * Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |w.im| + 3))
        ≤ C * Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |t| + 3)) := by
      rw [hCdef]
      have h := mul_le_mul_of_nonneg_left hscale (le_of_lt hC1pos)
      have heq : C1 * (2 * Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |t| + 3)))
          = (2 * C1) * Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |t| + 3)) := by ring
      linarith [h, heq]
    linarith [h1, hC1log]
end

end Work.FIArea6Hecke.R
