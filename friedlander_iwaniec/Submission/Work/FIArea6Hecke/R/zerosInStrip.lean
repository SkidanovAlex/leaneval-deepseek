/-
# `Submission.Work.FIArea6Hecke.R.zerosInStrip`

**All zeros of an admissible completion lie in the critical strip `-1 ≤ re s ≤ 1`.**

The target of this file is

  `Work.FIArea6Hecke.R.zerosInStrip` : for every `d ≥ 1`, every strict character `χ` mod `4d`,
  every `m : ℤ` and every entire completion `Λ` of `Λ(s,ψ) = heckeArch d m s · L(s,ψ_χ)` (the
  predicate `IsCompleted`), every zero `u` of `Λ` satisfies `-1 ≤ u.re ≤ 1`.

This is the hypothesis `hZeros` of `Work.FIArea6Hecke.R.logDerivReLower_of_baseBounds` (the kernel
bound `Re (1/(s-u) - 1/(s₁-u)) ≥ -C/(1+δ_u²)` for `s` in the region of *FI* (16.20) needs every
zero to lie to the left of `1/2` up to the bounded amount `1`).

## The two cases

* `ψ_m` is trivial on the primary units modulo `4d`: then **no** entire completion exists
  (`Work.FIArea6Hecke.R.noCompletion_of_primaryTrivial`), so the statement is vacuous;
* otherwise, the conductor-normalised functional equation
  `Work.FIArea6Hecke.R.heckeFEStrictConductorUni` writes the completion as
  `Λ = Φ · (4d/X)^s · corrFac`, where `Φ s = W·conj(Φ(conj(1-s)))` and `Φ` agrees on the half plane
  `re s > 1 + |m|/2` with `(X/π)^s Γ(s+|m|/2) L(s,ψ) · corrFac⁻¹`.  On `re s > 1` the identity
  theorem upgrades this to an identity of analytic functions; both `L(s,ψ)` (Euler product) and
  `corrFac` (every local factor is nonzero when `re s > 1`) are nonzero there, so `Φ ≠ 0` for
  `re s > 1`; the functional equation reflects this to `re s ≥ 0`.  Finally
  `corrFac(u) = 0` forces `re u = 0`, because `1 - c p^{-u} = 0` with `‖c‖ ≤ 1` gives
  `p^{-re u} = 1`.

The reduction from the functional-equation data is `zerosInStrip_of_FEdata`; it is stated as a
separate lemma so that its (purely analytic) content is independent of the analytic input proving
the conductor-normalised functional equation.
-/
import Mathlib
import Submission.Work.FIArea6Hecke.R.logDerivCore
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
import Submission.Work.FIArea6Hecke.R.baseLowerNegTwo
import Submission.Work.FIArea5.HeckeZFR.HeckeNonvanishing

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIArea6Hecke.R

open Complex Filter
open scoped BigOperators Topology

noncomputable section

/-! ## 0. Elementary helpers -/

/-- **The identity theorem on a half-plane**: two functions analytic on `{re s > T}`, agreeing on
the sub-half-plane `{re s > T'}` with `T ≤ T'`, agree on `{re s > T}`. -/
lemma eqOn_of_agrees_halfplane {F G : ℂ → ℂ} {T T' : ℝ} (hTT : T ≤ T')
    (hF : AnalyticOn ℂ F {z : ℂ | T < z.re}) (hG : AnalyticOn ℂ G {z : ℂ | T < z.re})
    (h : ∀ s : ℂ, T' < s.re → F s = G s) :
    ∀ s : ℂ, T < s.re → F s = G s := by
  set U : Set ℂ := {z : ℂ | T < z.re} with hU
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUconv : Convex ℝ U := by
    have h := (convex_Ioi T).linear_preimage (Complex.reCLM : ℂ →ₗ[ℝ] ℝ)
    have h2 : (Complex.reCLM : ℂ →ₗ[ℝ] ℝ) ⁻¹' (Set.Ioi T) = U := by
      ext z; simp [hU]
    rwa [h2] at h
  have hUpre : IsPreconnected U := hUconv.isPreconnected
  have hF' : AnalyticOnNhd ℂ F U := hF.differentiableOn.analyticOnNhd hUopen
  have hG' : AnalyticOnNhd ℂ G U := hG.differentiableOn.analyticOnNhd hUopen
  have hz₀ : (((T' + 1 : ℝ)) : ℂ) ∈ U := by
    simp only [hU, Set.mem_ofPred_eq, Complex.ofReal_re]; linarith
  have hev : F =ᶠ[𝓝 (((T' + 1 : ℝ)) : ℂ)] G := by
    refine Filter.eventually_of_mem
      (show {z : ℂ | T' < z.re} ∈ 𝓝 (((T' + 1 : ℝ)) : ℂ) from
        (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by
          simp only [Set.mem_ofPred_eq, Complex.ofReal_re]; linarith)) ?_
    intro z hz
    exact h z hz
  intro s hs
  exact AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hF' hG' hUpre hz₀ hev hs

/-- **A local correction factor vanishes only on the imaginary axis**: if `1 - c p^{-u} = 0` with
`p > 1` and `‖c‖ = 1` or `c = 0`, then `re u = 0`. -/
lemma re_eq_zero_of_one_sub_mul_cpow_eq_zero {c : ℂ} {p : ℕ} (hp : 1 < p)
    (hc : ‖c‖ = 1 ∨ c = 0) {u : ℂ} (hu : 1 - c * (p : ℂ) ^ (-u) = 0) : u.re = 0 := by
  have hcw : c * (p : ℂ) ^ (-u) = 1 := (sub_eq_zero.mp hu).symm
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hpR : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hnorm : (p : ℝ) ^ (-u.re) = 1 := by
    have h := congrArg norm hcw
    rw [norm_one, norm_mul, Complex.norm_natCast_cpow_of_pos (by omega : 0 < p)] at h
    rcases hc with hc | hc
    · rwa [hc, one_mul] at h
    · rw [hc, norm_zero, zero_mul] at h
      exact absurd h.symm (by norm_num)
  rcases lt_trichotomy u.re 0 with h | h | h
  · exact absurd hnorm (ne_of_gt (Real.one_lt_rpow hpR (by linarith)))
  · exact h
  · have hlt : (p : ℝ) ^ (-u.re) < 1 :=
      (Real.rpow_lt_one_iff_of_pos hp0).mpr (Or.inl ⟨hpR, by linarith⟩)
    exact absurd hnorm (ne_of_lt hlt)

/-- `x * d⁻¹ * d = x` for `d ≠ 0` (associativity-friendly cancellation). -/
lemma mul_inv_cancel_mul' {x d : ℂ} (hd : d ≠ 0) : x * d⁻¹ * d = x := by
  rw [mul_assoc, inv_mul_cancel₀ hd, mul_one]

/-- `(star (1 - u)).re = 1 - u.re`. -/
lemma re_star_one_sub (u : ℂ) : (star (1 - u)).re = 1 - u.re := by
  simp [Complex.conj_re]

/-- **The correction product vanishes only on the imaginary axis.** -/
lemma re_eq_zero_of_corrFac_eq_zero {c₁ c₂ : ℕ → ℂ} {S : Finset ℕ}
    (hS : ∀ p ∈ S, Nat.Prime p ∧ (‖c₁ p‖ = 1 ∨ c₁ p = 0) ∧ (‖c₂ p‖ = 1 ∨ c₂ p = 0))
    {u : ℂ} (hu : corrFac c₁ c₂ S u = 0) : u.re = 0 := by
  simp only [corrFac] at hu
  obtain ⟨p, hp, hzero⟩ := Finset.prod_eq_zero_iff.mp hu
  rcases mul_eq_zero.mp hzero with h | h
  · exact re_eq_zero_of_one_sub_mul_cpow_eq_zero (hS p hp).1.one_lt (hS p hp).2.1 h
  · exact re_eq_zero_of_one_sub_mul_cpow_eq_zero (hS p hp).1.one_lt (hS p hp).2.2 h

/-- **`(a : ℂ)^s · (b : ℂ)^s = (ab : ℂ)^s`** for `a,b > 0` (used to identify the rescaled
archimedean factor). -/
lemma ofReal_cpow_mul_ofReal {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (s : ℂ) :
    ((a : ℂ) ^ s) * ((b : ℂ) ^ s) = (((a * b : ℝ)) : ℂ) ^ s := by
  rw [Complex.ofReal_mul,
    ← Complex.mul_cpow_ofReal_nonneg ha.le hb.le s]

/-! ## 1. The reduction from the conductor-normalised functional equation -/

/-- **Zeros of an admissible completion lie in `[-1,1]`**, given the conductor-normalised
functional equation of *FI* (16.17): an entire `Φ` with `Φ s = W·conj(Φ(conj(1-s)))` (`W ≠ 0`)
agreeing on `re s > 1 + |m|/2` with
`(X/π)^s Γ(s+|m|/2) L(s,ψ) ∏_{p∈S}((1-c₁(p)p^{-s})(1-c₂(p)p^{-s}))^{-1}`, `1 ≤ X ≤ 4d`. -/
theorem zerosInStrip_of_FEdata (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ) (Lam : ℂ → ℂ)
    (hadm : IsCompleted d chi m Lam)
    (X : ℝ) (c₁ c₂ : ℕ → ℂ) (S : Finset ℕ) (Phi : ℂ → ℂ) (W : ℂ)
    (hX1 : 1 ≤ X) (hX4 : X ≤ 4 * (d : ℝ))
    (hS : ∀ p ∈ S, Nat.Prime p ∧ p ∣ 4 * d ∧
      (‖c₁ p‖ = 1 ∨ c₁ p = 0) ∧ (‖c₂ p‖ = 1 ∨ c₂ p = 0))
    (hW : W ≠ 0) (hPhian : AnalyticOn ℂ Phi Set.univ)
    (hFE : ∀ s : ℂ, Phi s = W * star (Phi (star (1 - s))))
    (hPagr : ∀ s : ℂ, 1 + |(m : ℝ)| / 2 < s.re →
      Phi s = ((X / Real.pi : ℝ) : ℂ) ^ s *
        Complex.Gamma (s + ((|(m : ℝ)| / 2 : ℝ) : ℂ)) *
        Work.FIArea5.S16Hecke.heckeLSeries chi m s *
        ∏ p ∈ S, ((1 - c₁ p * ((p : ℂ) ^ (-s))) * (1 - c₂ p * ((p : ℂ) ^ (-s))))⁻¹) :
    ∀ u : ℂ, Lam u = 0 → -1 ≤ u.re ∧ u.re ≤ 1 := by
  obtain ⟨hd, hchi, hAn, hagr⟩ := hadm
  obtain ⟨h1, hmul, hb, -, -⟩ := hchi.1
  have hS' : ∀ p ∈ S, Nat.Prime p ∧ (‖c₁ p‖ = 1 ∨ c₁ p = 0) ∧ (‖c₂ p‖ = 1 ∨ c₂ p = 0) :=
    fun p hp => ⟨(hS p hp).1, (hS p hp).2.2.1, (hS p hp).2.2.2⟩
  have hSpos : ∀ p ∈ S, p ≠ 0 := fun p hp => (hS p hp).1.pos.ne'
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le one_pos hX1
  set U : Set ℂ := {z : ℂ | (1 : ℝ) < z.re} with hU
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  -- the model function
  have hbase : (((X / Real.pi : ℝ)) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; positivity
  have hGan : AnalyticOn ℂ (fun s : ℂ => ((X / Real.pi : ℝ) : ℂ) ^ s *
      Complex.Gamma (s + ((|(m : ℝ)| / 2 : ℝ) : ℂ)) *
      Work.FIArea5.S16Hecke.heckeLSeries chi m s) U := by
    refine AnalyticOn.mul (AnalyticOn.mul ?_ ?_) ?_
    · refine DifferentiableOn.analyticOn ?_ hUopen
      intro z _
      exact (DifferentiableAt.const_cpow differentiableAt_id (Or.inl hbase)).differentiableWithinAt
    · refine DifferentiableOn.analyticOn ?_ hUopen
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
    · refine DifferentiableOn.analyticOn ?_ hUopen
      intro z hz
      refine (LSeries_differentiableOn (Work.FIArea5.S16Hecke.heckeLam chi m) z ?_).mono ?_
      · show LSeries.abscissaOfAbsConv (Work.FIArea5.S16Hecke.heckeLam chi m) < (z.re : EReal)
        exact lt_of_le_of_lt (Work.FIArea5.S16Hecke.heckeLSeries_absc_le_one chi m hb)
          (EReal.coe_lt_coe_iff.mpr hz)
      · intro w hw
        exact lt_of_le_of_lt (Work.FIArea5.S16Hecke.heckeLSeries_absc_le_one chi m hb)
          (EReal.coe_lt_coe_iff.mpr hw)
  have hCorDiff : Differentiable ℂ (corrFac c₁ c₂ S) :=
    fun u => differentiableAt_corrFac c₁ c₂ S hSpos u
  have hCorAn : AnalyticOn ℂ (corrFac c₁ c₂ S) U :=
    hCorDiff.differentiableOn.analyticOn hUopen
  -- agreement of `Φ · corrFac` with the model on `re s > 1`
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
      ((hPhian.mono (Set.subset_univ _)).mul hCorAn) hGan hagree
  -- `Φ` does not vanish for `re s > 1`
  have hPhine : ∀ s : ℂ, (1 : ℝ) < s.re → Phi s ≠ 0 := by
    intro s hs h0
    have hG0 : ((X / Real.pi : ℝ) : ℂ) ^ s *
        Complex.Gamma (s + ((|(m : ℝ)| / 2 : ℝ) : ℂ)) *
        Work.FIArea5.S16Hecke.heckeLSeries chi m s = 0 := by
      rw [← hident s hs, h0, zero_mul]
    have hgam : Complex.Gamma (s + ((|(m : ℝ)| / 2 : ℝ) : ℂ)) ≠ 0 := by
      refine Complex.Gamma_ne_zero (fun n hn => ?_)
      have hre := congrArg Complex.re hn
      simp at hre
      have hmm : (0 : ℝ) ≤ |(m : ℝ)| / 2 := by positivity
      have hn' : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hLne := Work.FIArea5.S16Hecke.heckeLSeries_ne_zero_of_one_lt_re chi m h1 hmul hb hs
    exact absurd hG0
      (mul_ne_zero (mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl hbase)) hgam) hLne)
  -- the global factorisation `Λ = Φ · (4d/X)^s · corrFac`
  set A : ℝ := 4 * (d : ℝ) / X with hAdef
  have hApos : 0 < A := by rw [hAdef]; positivity
  have hAne : (A : ℂ) ≠ 0 := by rw [Complex.ofReal_ne_zero]; exact ne_of_gt hApos
  have hLamfac : ∀ s : ℂ, Lam s = Phi s * ((A : ℂ) ^ s) * corrFac c₁ c₂ S s := by
    have hRHSan : AnalyticOn ℂ
        (fun s : ℂ => Phi s * ((A : ℂ) ^ s) * corrFac c₁ c₂ S s) Set.univ := by
      refine AnalyticOn.mul (AnalyticOn.mul hPhian ?_) ?_
      · refine (show Differentiable ℂ (fun z : ℂ => (A : ℂ) ^ z) from
          fun u => (hasStrictDerivAt_const_cpow (Or.inl hAne)).hasDerivAt.differentiableAt)
            |>.differentiableOn.analyticOn isOpen_univ
      · exact hCorDiff.differentiableOn.analyticOn isOpen_univ
    have hEq : Lam = fun s : ℂ => Phi s * ((A : ℂ) ^ s) * corrFac c₁ c₂ S s := by
      refine eq_of_agrees_right_local (T := 1 + |(m : ℝ)| / 2) hRHSan hAn (fun s hs => ?_)
      rw [hagr s hs]
      have hs1 : (1 : ℝ) < s.re := by
        have hmm : (0 : ℝ) ≤ |(m : ℝ)| / 2 := by positivity
        linarith
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
    intro s
    rw [hEq]
  intro u hu
  have hfac0 : Phi u * ((A : ℂ) ^ u) * corrFac c₁ c₂ S u = 0 := by
    rw [← hLamfac u, hu]
  have hAu : ((A : ℂ) ^ u) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hAne)
  rcases mul_eq_zero.mp hfac0 with h | h
  · rcases mul_eq_zero.mp h with hp | ha
    · have hle1 : u.re ≤ 1 := by
        by_contra hc
        push_neg at hc
        exact hPhine u hc hp
      have hge0 : 0 ≤ u.re := by
        by_contra hc
        push_neg at hc
        have hconj : Phi (star (1 - u)) = 0 := by
          have h := hFE u
          rw [hp] at h
          have h2 : star (Phi (star (1 - u))) = 0 := (mul_eq_zero.mp h.symm).resolve_left hW
          have h3 := congrArg star h2
          simpa using h3
        have hre : (1 : ℝ) < (star (1 - u)).re := by
          rw [re_star_one_sub]; linarith
        exact hPhine _ hre hconj
      exact ⟨by linarith, hle1⟩
    · exact absurd ha hAu
  · have h0 : u.re = 0 := re_eq_zero_of_corrFac_eq_zero hS' h
    exact ⟨by linarith, by linarith⟩

/-! ## 2. The unconditional statement -/

/-! ## 3.  The unconditional statement from the *current* conductor-normalised functional equation

`zerosInStrip_of_conductorFE` is `zerosInStrip` with `heckeFEStrictConductorUni` replaced by a
hypothesis of the (production) form `∀ d χ m, 1 ≤ d → IsCharMod4dStrict d χ → (ψ nontrivial on the
primary units) → HasConductorFE d χ m`; it is the statement of `R/conductorFEClean`
(`Work.FIArea6Hecke.R.conductorFEClean`), the repaired conductor-normalised functional equation that
replaces the two stubs `R/levelHeckeFE` + `R/heckePartnerThetaLaw`.  Keeping it as a separate lemma
means the switch is a one-line change at the call site below. -/
theorem zerosInStrip_of_conductorFE
    (hFE : ∀ (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ), 1 ≤ d →
      Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi →
      (∃ z : GaussianInt, Work.FIPlan.IsPrimary z ∧ Work.FIArea5.S16Hecke.IsUnitMod4d d z ∧
        Work.FIArea5.S16Hecke.psi chi m z ≠ 1) →
      Work.FIArea6Hecke.R.HasConductorFE d chi m)
    (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ) (Lam : ℂ → ℂ)
    (hadm : IsCompleted d chi m Lam) :
    ∀ u : ℂ, Lam u = 0 → -1 ≤ u.re ∧ u.re ≤ 1 := by
  obtain ⟨hd, hchi, hAn, hagr⟩ := hadm
  by_cases htriv : ∀ z : GaussianInt, Work.FIPlan.IsPrimary z →
      Work.FIArea5.S16Hecke.IsUnitMod4d d z → Work.FIArea5.S16Hecke.psi chi m z = 1
  · exact absurd ⟨Lam, hAn, hagr⟩ (noCompletion_of_primaryTrivial d chi m hd hchi htriv)
  · push Not at htriv
    obtain ⟨X, c₁, c₂, S, Phi, W, hX1, hX4, hS, hW, hPhian, hFE', hPagr⟩ :=
      hFE d chi m hd hchi htriv
    exact zerosInStrip_of_FEdata d chi m Lam ⟨hd, hchi, hAn, hagr⟩ X c₁ c₂ S Phi W
      hX1 hX4 hS hW hPhian hFE' hPagr

end

end Work.FIArea6Hecke.R
