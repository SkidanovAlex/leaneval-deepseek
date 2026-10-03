
import Mathlib
import Submission.Work.FIArea6Hecke.R.logDerivCore
import Submission.Work.FIArea6Hecke.R.zerosInStrip
import Submission.Work.FIArea6Hecke.R.baseLowerNegTwo
import Submission.Work.FIArea5.S16Hecke.ThetaDefs
import Submission.Work.FIArea5.S16Hecke.GaussFourier
import Submission.Work.FIArea5.S16Hecke.thetaOdd_poisson
import Submission.Work.FIArea5.S16Hecke.thetaOdd_eq_unitSum_mul_thetaHol
import Submission.Work.FIArea5.S16Hecke.mellin_thetaHol
import Submission.Work.FIArea5.S16Hecke.heckeFE_of_theta
import Submission.Work.FIArea5.S16Hecke.Defs
import Submission.Work.FIArea5.S16Hecke.h1166TwistDefs
import Submission.Work.FIArea5.S16Hecke.thetaHol_twist_eq
import Submission.Work.FIArea5.S16Hecke.twist_unitSum
import Submission.Work.FIArea5.S16Hecke.twistAux
import Submission.Work.FIArea5.S16Hecke.GaussBasic
import Submission.Work.FIArea5.S16Hecke.primaryWeightDefs
import Submission.Work.FIArea5.S16Hecke.primaryAux
import Submission.Commons.NumberTheory.GaussianInt.primary_associate_exists_unique
import Submission.Work.FIArea6Hecke.R.HeckeCompletionAll
import Submission.Work.FIArea5.S16Hecke.heckeLam_localRec
import Submission.Work.FIArea5.S16Hecke.heckeLSeries_eulerProduct
import Submission.Work.FIArea5.S16Hecke.heckeLSeries_conj
import Submission.Work.FIArea6Hecke.R.heckeCompletionImprimitive
import Submission.Work.FIArea6Hecke.R.localFactor_eq_decomp
import Submission.Work.FIArea5.S16Hecke.existsPrimarySplit
import Submission.Work.FIArea6Hecke.R.HasConductorFEDefs
import Submission.Work.FIArea5.S16Hecke.heckeFE_defs
import Submission.Work.FIPlan.Interface
import Submission.Work.FIArea6Hecke.R.noCompletion_of_primaryTrivial
import Submission.Work.FIArea6Hecke.R.heckeLval_logDeriv_norm_le_of_one_lt_re
import Submission.Work.FIArea6Hecke.R.HeckeLSeriesLogDerivEuler
import Submission.Work.FIArea5.HeckeZFR.FELogDeriv
import Submission.Work.FIArea5.HeckeZFR.DigammaShift
import Submission.Work.FIArea6Hecke.R.heckeStripNearOne
import Submission.Port.LogDerivCompat

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIArea6Hecke.R

open Complex Filter
open scoped BigOperators Topology

noncomputable section

/-! ## 1.  A uniform logarithmic-derivative bound for the Hecke `L`-series on `re s ≥ 2` -/

/-- **Uniform bound for `L'/L` on the half plane `re s ≥ 2`**, independent of `d`, `χ` and `m`:
the Euler product gives `L'/L = Σ_𝔭 (local factor)'/(local factor)` and each local term is
`≤ C₂·log p · p^{-σ}` (`heckeFp_logDeriv_bound`), while `Σ_p log p · p^{-σ} ≤ Σ_p log p · p^{-2}
≤ C₃` (`sum_primes_log_mul_rpow_le` at `σ = 2`). -/
theorem logDerivLSeriesUniformReGeTwo :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ), 1 ≤ d →
      Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi → ∀ s : ℂ, 2 ≤ s.re →
        ‖deriv (Work.FIArea5.S16Hecke.heckeLSeries chi m) s
          / Work.FIArea5.S16Hecke.heckeLSeries chi m s‖ ≤ C := by
  obtain ⟨C₂, hC₂pos, hC₂⟩ := heckeFp_logDeriv_bound
  obtain ⟨C₃, hC₃pos, hC₃⟩ := sum_primes_log_mul_rpow_le
  refine ⟨C₂ * C₃, by positivity, ?_⟩
  intro d chi m hd hchi s hs
  obtain ⟨h1, hmul, hb, -, -⟩ := hchi.1
  have hs1 : 1 < s.re := by linarith
  have hsumm2 : Summable (fun p : Nat.Primes =>
      Real.log ((p : ℕ) : ℝ) * (((p : ℕ) : ℝ) ^ (-(2 : ℝ)))) :=
    summable_primes_log_mul_rpow (by norm_num : (1 : ℝ) < 2)
  have hsummC : Summable (fun p : Nat.Primes =>
      C₂ * Real.log ((p : ℕ) : ℝ) * (((p : ℕ) : ℝ) ^ (-s.re))) := by
    have h := (summable_primes_log_mul_rpow hs1).mul_left C₂
    refine h.congr (fun p => ?_)
    ring
  have hsumm : Summable (fun p : Nat.Primes =>
      logDeriv (Work.FIArea5.S16Hecke.heckeFp chi m p) s) :=
    Summable.of_norm_bounded hsummC (fun p => hC₂ chi m p s h1 hmul hb hs1)
  rw [← logDeriv_apply, HeckeLSeriesLogDerivEuler chi m h1 hmul hb hs1]
  have hstep1 : ‖∑' p : Nat.Primes, logDeriv (Work.FIArea5.S16Hecke.heckeFp chi m p) s‖
      ≤ ∑' p : Nat.Primes, ‖logDeriv (Work.FIArea5.S16Hecke.heckeFp chi m p) s‖ :=
    norm_tsum_le_tsum_norm hsumm.norm
  have hstep2 : (∑' p : Nat.Primes, ‖logDeriv (Work.FIArea5.S16Hecke.heckeFp chi m p) s‖)
      ≤ ∑' p : Nat.Primes, C₂ * Real.log ((p : ℕ) : ℝ) * (((p : ℕ) : ℝ) ^ (-s.re)) :=
    Summable.tsum_le_tsum (fun p => hC₂ chi m p s h1 hmul hb hs1) hsumm.norm hsummC
  have hstep3 : (∑' p : Nat.Primes, C₂ * Real.log ((p : ℕ) : ℝ) * (((p : ℕ) : ℝ) ^ (-s.re)))
      = C₂ * ∑' p : Nat.Primes, Real.log ((p : ℕ) : ℝ) * (((p : ℕ) : ℝ) ^ (-s.re)) := by
    rw [show (∑' p : Nat.Primes, C₂ * Real.log ((p : ℕ) : ℝ) * (((p : ℕ) : ℝ) ^ (-s.re)))
        = ∑' p : Nat.Primes,
            C₂ * (Real.log ((p : ℕ) : ℝ) * (((p : ℕ) : ℝ) ^ (-s.re))) from
          tsum_congr (fun p => by ring), tsum_mul_left]
  have hstep4 : (∑' p : Nat.Primes, Real.log ((p : ℕ) : ℝ) * (((p : ℕ) : ℝ) ^ (-s.re)))
      ≤ C₃ := by
    have hle : ∀ p : Nat.Primes, Real.log ((p : ℕ) : ℝ) * (((p : ℕ) : ℝ) ^ (-s.re))
        ≤ Real.log ((p : ℕ) : ℝ) * (((p : ℕ) : ℝ) ^ (-(2 : ℝ))) := by
      intro p
      have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by
        have := p.prop.two_le; exact_mod_cast this
      refine mul_le_mul_of_nonneg_left ?_ (Real.log_nonneg (by linarith))
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    calc (∑' p : Nat.Primes, Real.log ((p : ℕ) : ℝ) * (((p : ℕ) : ℝ) ^ (-s.re)))
        ≤ ∑' p : Nat.Primes, Real.log ((p : ℕ) : ℝ) * (((p : ℕ) : ℝ) ^ (-(2 : ℝ))) :=
          Summable.tsum_le_tsum hle (summable_primes_log_mul_rpow hs1) hsumm2
      _ ≤ C₃ := by
          have h2 := hC₃ 2 (by norm_num) le_rfl
          have h21 : (2 : ℝ) - 1 = 1 := by norm_num
          rw [h21, div_one] at h2
          exact h2
  calc ‖∑' p : Nat.Primes, logDeriv (Work.FIArea5.S16Hecke.heckeFp chi m p) s‖
      ≤ ∑' p : Nat.Primes, ‖logDeriv (Work.FIArea5.S16Hecke.heckeFp chi m p) s‖ := hstep1
    _ ≤ ∑' p : Nat.Primes, C₂ * Real.log ((p : ℕ) : ℝ) * (((p : ℕ) : ℝ) ^ (-s.re)) := hstep2
    _ = C₂ * ∑' p : Nat.Primes, Real.log ((p : ℕ) : ℝ) * (((p : ℕ) : ℝ) ^ (-s.re)) := hstep3
    _ ≤ C₂ * C₃ := mul_le_mul_of_nonneg_left hstep4 hC₂pos.le

/-! ## 2.  The uniform bound for the completion at `re s = 3` -/

/-- **Uniform upper bound for `Re (Λ'/Λ)` on the line `re s = 3`**: from the uniform
`L`-series bound of §1 and the digamma bound for the archimedean factor. -/
theorem logDerivCompletionUniformAtThree :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ) (Lam : ℂ → ℂ),
      IsCompleted d chi m Lam → ∀ γ : ℝ,
        (deriv Lam ((3 : ℂ) + (γ : ℂ) * Complex.I) / Lam ((3 : ℂ) + (γ : ℂ) * Complex.I)).re
          ≤ C * Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |γ| + 3)) := by
  obtain ⟨CL, hCLpos, hCL⟩ := logDerivLSeriesUniformReGeTwo
  refine ⟨CL + 20, by linarith, ?_⟩
  intro d chi m Lam hadm γ
  obtain ⟨hd, hchi, hAn, hagr⟩ := hadm
  obtain ⟨h1, hmul, hb, -, -⟩ := hchi.1
  have hCL' : ∀ s : ℂ, 2 ≤ s.re →
      ‖deriv (Work.FIArea5.S16Hecke.heckeLSeries chi m) s
        / Work.FIArea5.S16Hecke.heckeLSeries chi m s‖ ≤ CL :=
    fun s hs => hCL d chi m hd hchi s hs
  set s : ℂ := (3 : ℂ) + (γ : ℂ) * Complex.I with hs
  have hsre : s.re = 3 := by simp [s]
  have hs1 : (1 : ℝ) < s.re := by rw [hsre]; norm_num
  have hlogpos : 0 ≤ Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |γ| + 3)) := by
    refine Real.log_nonneg ?_
    have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    have hm0 : (0 : ℝ) ≤ |(m : ℝ)| := abs_nonneg _
    have hg0 : (0 : ℝ) ≤ |γ| := abs_nonneg _
    nlinarith
  by_cases hzero : Lam s = 0
  · rw [hzero, div_zero]
    simp only [Complex.zero_re]
    have : (0:ℝ) ≤ (CL + 20) * Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |γ| + 3)) :=
      mul_nonneg (by linarith) hlogpos
    linarith
  · have hmodel : Lam s = Work.FITop4.Bridge.heckeArch d m s *
        Work.FIArea5.S16Hecke.heckeLSeries chi m s :=
      Lam_eq_heckeArch_mul_of_one_lt_re hd hAn hb hagr hs1
    have hev : Lam =ᶠ[𝓝 s] (fun z => Work.FITop4.Bridge.heckeArch d m z *
        Work.FIArea5.S16Hecke.heckeLSeries chi m z) := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs1] with z hz
      exact Lam_eq_heckeArch_mul_of_one_lt_re hd hAn hb hagr hz
    have hder : deriv Lam s = deriv (fun z => Work.FITop4.Bridge.heckeArch d m z *
        Work.FIArea5.S16Hecke.heckeLSeries chi m z) s := Filter.EventuallyEq.deriv_eq hev
    rw [hder, hmodel]
    have hfne : Work.FITop4.Bridge.heckeArch d m s ≠ 0 :=
      heckeArch_ne_zero_of_one_lt_re hd m hs1
    have hgne : Work.FIArea5.S16Hecke.heckeLSeries chi m s ≠ 0 :=
      Work.FIArea5.S16Hecke.heckeLSeries_ne_zero_of_one_lt_re chi m h1 hmul hb hs1
    have hdf : DifferentiableAt ℂ (Work.FITop4.Bridge.heckeArch d m) s :=
      heckeArch_differentiableAt_of_pos hd m (by linarith)
    have habs : LSeries.abscissaOfAbsConv (Work.FIArea5.S16Hecke.heckeLam chi m) < (s.re : EReal) :=
      lt_of_le_of_lt (Work.FIArea5.S16Hecke.heckeLSeries_absc_le_one chi m hb)
        (EReal.coe_lt_coe_iff.mpr (by rw [hsre]; norm_num))
    have hdg : DifferentiableAt ℂ (Work.FIArea5.S16Hecke.heckeLSeries chi m) s :=
      (LSeries_hasDerivAt (f := Work.FIArea5.S16Hecke.heckeLam chi m) (s := s) habs).differentiableAt
    have hsplit' : deriv (fun z => Work.FITop4.Bridge.heckeArch d m z *
          Work.FIArea5.S16Hecke.heckeLSeries chi m z) s
          / (Work.FITop4.Bridge.heckeArch d m s * Work.FIArea5.S16Hecke.heckeLSeries chi m s)
        = logDeriv (Work.FITop4.Bridge.heckeArch d m) s
          + logDeriv (Work.FIArea5.S16Hecke.heckeLSeries chi m) s := by
      rw [← logDeriv_apply, Submission.Port.logDeriv_mul_fun s hfne hgne hdf hdg]
    rw [hsplit']
    have hne : ∀ n : ℕ, s + ((|(m : ℝ)| / 2 : ℝ) : ℂ) ≠ -((n : ℕ) : ℂ) := by
      intro n hn
      have hre := congrArg Complex.re hn
      simp only [Complex.add_re, Complex.neg_re, Complex.ofReal_re, Complex.natCast_re] at hre
      have hmm : (0 : ℝ) ≤ |(m : ℝ)| / 2 := by positivity
      have hn' : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      rw [hsre] at hre
      linarith
    have harch : logDeriv (Work.FITop4.Bridge.heckeArch d m) s
        = Complex.log (4 * (d : ℂ) / (Real.pi : ℂ))
          + Complex.digamma (s + ((|(m : ℝ)| / 2 : ℝ) : ℂ)) :=
      logDeriv_heckeArch d hd m hne
    rw [harch, Complex.add_re, Complex.add_re]
    have hlogarch : (Complex.log (4 * (d : ℂ) / (Real.pi : ℂ))).re ≤ Real.log (4 * (d : ℝ)) := by
      rw [Complex.log_re]
      have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
      have hnorm : ‖(4 * (d : ℂ) / (Real.pi : ℂ))‖ = 4 * (d : ℝ) / Real.pi := by
        rw [show (4 * (d : ℂ) / (Real.pi : ℂ)) = ((4 * (d : ℝ) / Real.pi : ℝ) : ℂ) by
          push_cast; ring, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by positivity)]
      rw [hnorm]
      refine Real.log_le_log (by positivity) ?_
      rw [div_le_iff₀ Real.pi_pos]
      have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
      nlinarith [Real.pi_gt_three]
    have hdig : (Complex.digamma (s + ((|(m : ℝ)| / 2 : ℝ) : ℂ))).re
        ≤ Real.log (2 + |γ|) + 2 * Real.log (12 + 2 * |(m : ℝ)|) + 6 := by
      have harg : s + ((|(m : ℝ)| / 2 : ℝ) : ℂ)
          = (((3 + |(m : ℝ)| / 2 : ℝ)) : ℂ) + (γ : ℂ) * Complex.I := by
        rw [hs]; push_cast; ring
      rw [harg]
      have h := Work.FIArea5.S16Hecke.digamma_re_le_of_half_le (3 + |(m : ℝ)| / 2) γ
        (by have h := abs_nonneg (m : ℝ); linarith)
      have hlog : Real.log (4 * (3 + |(m : ℝ)| / 2)) = Real.log (12 + 2 * |(m : ℝ)|) := by
        congr 1; ring
      rw [hlog] at h
      exact h
    have hLd : (logDeriv (Work.FIArea5.S16Hecke.heckeLSeries chi m) s).re ≤ CL := by
      rw [logDeriv_apply]
      have h1' : ‖deriv (Work.FIArea5.S16Hecke.heckeLSeries chi m) s
          / Work.FIArea5.S16Hecke.heckeLSeries chi m s‖ ≤ CL := hCL' s (by rw [hsre]; norm_num)
      have h2 := (abs_le.mp (Complex.abs_re_le_norm (deriv
        (Work.FIArea5.S16Hecke.heckeLSeries chi m) s
        / Work.FIArea5.S16Hecke.heckeLSeries chi m s))).2
      linarith
    have habsorb := log_absorb_three d m γ CL hd hCLpos
    linarith

/-! ## 3.  The logarithmic derivative of a constant power -/

/-- `logDeriv (fun z => A^z) s = log A` for `A ≠ 0`. -/
lemma logDeriv_const_cpow (A : ℂ) (hA : A ≠ 0) (s : ℂ) :
    logDeriv (fun z : ℂ => A ^ z) s = Complex.log A := by
  rw [logDeriv_apply,
    (hasStrictDerivAt_const_cpow (Or.inl hA)).hasDerivAt.deriv]
  have hne : A ^ s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hA)
  field_simp

/-! ## 4.  Uniform factorisation of an admissible completion along the conductor-normalised
functional equation -/

/-- **The completion is the conductor-normalised one times `(4d/X)^s·corrFac`**: given the data of
`heckeFEStrictConductorUni`, the identity theorem gives the global factorisation
`Λ = Φ · (4d/X)^s · corrFac` of admissible completions. -/
theorem Lam_eq_Phi_mul_corrFac {d : ℕ} {chi : GaussianInt → ℂ} {m : ℤ} {Lam : ℂ → ℂ}
    (hadm : IsCompleted d chi m Lam)
    {X : ℝ} {c₁ c₂ : ℕ → ℂ} {S : Finset ℕ} {Phi : ℂ → ℂ}
    (hX1 : 1 ≤ X) (hX4 : X ≤ 4 * (d : ℝ))
    (hS : ∀ p ∈ S, Nat.Prime p ∧ p ∣ 4 * d ∧
      (‖c₁ p‖ = 1 ∨ c₁ p = 0) ∧ (‖c₂ p‖ = 1 ∨ c₂ p = 0))
    (hPhian : AnalyticOn ℂ Phi Set.univ)
    (hPagr : ∀ s : ℂ, 1 + |(m : ℝ)| / 2 < s.re →
      Phi s = ((X / Real.pi : ℝ) : ℂ) ^ s *
        Complex.Gamma (s + ((|(m : ℝ)| / 2 : ℝ) : ℂ)) *
        Work.FIArea5.S16Hecke.heckeLSeries chi m s *
        ∏ p ∈ S, ((1 - c₁ p * ((p : ℂ) ^ (-s))) * (1 - c₂ p * ((p : ℂ) ^ (-s))))⁻¹) :
    Lam = fun s : ℂ => Phi s * (((4 * (d : ℝ) / X : ℝ)) : ℂ) ^ s * corrFac c₁ c₂ S s := by
  obtain ⟨hd, hchi, hAn, hagr⟩ := hadm
  have hS' : ∀ p ∈ S, Nat.Prime p ∧ (‖c₁ p‖ = 1 ∨ c₁ p = 0) ∧ (‖c₂ p‖ = 1 ∨ c₂ p = 0) :=
    fun p hp => ⟨(hS p hp).1, (hS p hp).2.2.1, (hS p hp).2.2.2⟩
  have hSpos : ∀ p ∈ S, p ≠ 0 := fun p hp => (hS p hp).1.pos.ne'
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le one_pos hX1
  set A : ℝ := 4 * (d : ℝ) / X with hAdef
  have hApos : 0 < A := by rw [hAdef]; positivity
  have hAne : (A : ℂ) ≠ 0 := by rw [Complex.ofReal_ne_zero]; exact ne_of_gt hApos
  have hCorDiff : Differentiable ℂ (corrFac c₁ c₂ S) :=
    fun u => differentiableAt_corrFac c₁ c₂ S hSpos u
  have hb : ∀ z : GaussianInt, ‖chi z‖ ≤ 1 := hchi.1.2.2.1
  have hGan : AnalyticOn ℂ (fun s : ℂ => ((X / Real.pi : ℝ) : ℂ) ^ s *
      Complex.Gamma (s + ((|(m : ℝ)| / 2 : ℝ) : ℂ)) *
      Work.FIArea5.S16Hecke.heckeLSeries chi m s) {z : ℂ | (1 : ℝ) < z.re} := by
    refine AnalyticOn.mul (AnalyticOn.mul ?_ ?_) ?_
    · refine DifferentiableOn.analyticOn ?_ (isOpen_lt continuous_const Complex.continuous_re)
      intro z _
      exact (DifferentiableAt.const_cpow differentiableAt_id
        (Or.inl (Complex.ofReal_ne_zero.mpr (ne_of_gt (by positivity : (0:ℝ) < X / Real.pi))))).differentiableWithinAt
    · refine DifferentiableOn.analyticOn ?_ (isOpen_lt continuous_const Complex.continuous_re)
      intro z hz
      have hzne : ∀ n : ℕ, z + ((|(m : ℝ)| / 2 : ℝ) : ℂ) ≠ -((n : ℕ) : ℂ) := by
        intro n hn
        have hre := congrArg Complex.re hn
        simp at hre
        have h1' : (1 : ℝ) < z.re := hz
        have hmm : (0 : ℝ) ≤ |(m : ℝ)| / 2 := by positivity
        have hn' : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      exact ((Complex.differentiableAt_Gamma _ hzne).comp z
        (differentiableAt_id.add_const _)).differentiableWithinAt
    · refine DifferentiableOn.analyticOn ?_ (isOpen_lt continuous_const Complex.continuous_re)
      intro z hz
      refine (LSeries_differentiableOn (Work.FIArea5.S16Hecke.heckeLam chi m) z ?_).mono ?_
      · show LSeries.abscissaOfAbsConv (Work.FIArea5.S16Hecke.heckeLam chi m) < (z.re : EReal)
        exact lt_of_le_of_lt (Work.FIArea5.S16Hecke.heckeLSeries_absc_le_one chi m hb)
          (EReal.coe_lt_coe_iff.mpr hz)
      · intro w hw
        exact lt_of_le_of_lt (Work.FIArea5.S16Hecke.heckeLSeries_absc_le_one chi m hb)
          (EReal.coe_lt_coe_iff.mpr hw)
  have hagree : ∀ s : ℂ, 1 + |(m : ℝ)| / 2 < s.re →
      Phi s * corrFac c₁ c₂ S s = ((X / Real.pi : ℝ) : ℂ) ^ s *
        Complex.Gamma (s + ((|(m : ℝ)| / 2 : ℝ) : ℂ)) *
        Work.FIArea5.S16Hecke.heckeLSeries chi m s := by
    intro s hs
    have hne : (∏ p ∈ S, ((1 - c₁ p * ((p : ℂ) ^ (-s))) * (1 - c₂ p * ((p : ℂ) ^ (-s))))) ≠ 0 := by
      simpa only [corrFac] using
        corrFac_ne_zero_of_one_lt_re hS' (s := s) (by linarith [abs_nonneg (m : ℝ)])
    rw [hPagr s hs, Finset.prod_inv_distrib]
    simp only [corrFac]
    exact mul_inv_cancel_mul' hne
  have hident : ∀ s : ℂ, (1 : ℝ) < s.re →
      Phi s * corrFac c₁ c₂ S s = ((X / Real.pi : ℝ) : ℂ) ^ s *
        Complex.Gamma (s + ((|(m : ℝ)| / 2 : ℝ) : ℂ)) *
        Work.FIArea5.S16Hecke.heckeLSeries chi m s :=
    eqOn_of_agrees_halfplane (T := 1) (T' := 1 + |(m : ℝ)| / 2)
      (by linarith [abs_nonneg (m : ℝ)])
      ((hPhian.mono (Set.subset_univ _)).mul
        (hCorDiff.differentiableOn.analyticOn (isOpen_lt continuous_const Complex.continuous_re)))
      hGan hagree
  have hRHSan : AnalyticOn ℂ
      (fun s : ℂ => Phi s * ((A : ℂ) ^ s) * corrFac c₁ c₂ S s) Set.univ := by
    refine AnalyticOn.mul (AnalyticOn.mul hPhian ?_) ?_
    · refine (show Differentiable ℂ (fun z : ℂ => (A : ℂ) ^ z) from
        fun u => (hasStrictDerivAt_const_cpow (Or.inl hAne)).hasDerivAt.differentiableAt)
          |>.differentiableOn.analyticOn isOpen_univ
    · exact hCorDiff.differentiableOn.analyticOn isOpen_univ
  refine eq_of_agrees_right_local (T := 1 + |(m : ℝ)| / 2) hRHSan hAn (fun s hs => ?_)
  rw [hagr s hs]
  have hs1 : (1 : ℝ) < s.re := by linarith [abs_nonneg (m : ℝ)]
  have hid := hident s hs1
  have hkey : Phi s * ((A : ℂ) ^ s) * corrFac c₁ c₂ S s
      = (((X / Real.pi : ℝ) : ℂ) ^ s * ((A : ℂ) ^ s)) *
          Complex.Gamma (s + ((|(m : ℝ)| / 2 : ℝ) : ℂ)) *
          Work.FIArea5.S16Hecke.heckeLSeries chi m s := by
    rw [show Phi s * ((A : ℂ) ^ s) * corrFac c₁ c₂ S s
        = (Phi s * corrFac c₁ c₂ S s) * ((A : ℂ) ^ s) by ring, hid]
    ring
  rw [hkey, ofReal_cpow_mul_ofReal (by positivity : (0 : ℝ) < X / Real.pi) hApos,
    heckeArch_eq]
  have hbase_real : (X / Real.pi) * A = 4 * (d : ℝ) / Real.pi := by
    have hX0 : X ≠ 0 := ne_of_gt hXpos
    rw [hAdef]
    field_simp
  have hbase_eq : (((X / Real.pi) * A : ℝ) : ℂ) = 4 * (d : ℂ) / (Real.pi : ℂ) := by
    rw [hbase_real]
    push_cast
    ring
  rw [hbase_eq]

/-! ## 5.  The uniform lower bound at `re s = -2` -/

end

end Work.FIArea6Hecke.R
