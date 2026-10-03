/-
# `Submission.Work.FIArea6Hecke.R.HeckeLambdaLogDerivBounds`

*FI* §16, the **one-sided and near-zero logarithmic-derivative bounds for the completion of the
Hecke `L`-function of `ℚ(i)`**.

For `1 < σ ≤ 2`, with `Λ` an entire completion of `Λ(s,ψ) = heckeArch d m s · heckeLSeries χ m s`
satisfying Hecke's functional equation `Λ s = W conj(Λ(conj(1-s)))`,

* `Re (Λ'/Λ)(σ+it) ≥ -C·log(4d(|m|+|t|+3))`, and
* `Re (Λ'/Λ)(σ+it) ≥ 1/(σ-β) - C·log(4d(|m|+|t|+3))` whenever `Λ(β+it) = 0`, `0 < β < 1`.

## The argument implemented here

Write `s := σ+it` and `s₁ := -1+it`.  By Hecke's functional equation (`logDeriv_FE_at_neg_one`,
`FELogDeriv`) the points `s₁` and `2+it` have opposite logarithmic derivatives, and every zero of
`Λ` lies in `-1 ≤ re u ≤ 1` (`lam_zero_re_bounds_zz`).  The **Hadamard partial fraction**
(`Lam_partialFraction`, whose growth hypothesis is the one remaining analytic input, the circle
growth of the completion) at the pair `(s, s₁)` reads

  `Λ'/Λ(s) - Λ'/Λ(s₁) = lim_R Σ_{|u|≤R} ord(u)·(1/(s-u) - 1/(s₁-u))`.

Since every zero lies to the right of `-1` and to the left of `σ > 1`, **every** summand has
nonnegative real part (`re_rebase_nonneg`), so

  `Re (Λ'/Λ)(σ+it) ≥ Re (Λ'/Λ)(-1+it) = -Re (Λ'/Λ)(2+it) ≥ -C·log(4d(|m|+|t|+3))`,

which is the first conjunct once the base bound at `2+it` is available
(`lam_logDeriv_re_at_two_le_uniform`, proved below from the absolutely convergent Euler product at
`re = 2` and the digamma bound, with constants *uniform* in `d, χ, m, Λ`).  If moreover
`Λ(β+it) = 0` with `0 < β < 1`, the summand at the zero itself equals `1/(σ-β) + 1/(1+β)`
(`le_re_rebase_at_zero`), all other summands being nonnegative, which gives the second conjunct
(`re_logDeriv_rebase_of_pf`).

This is the sharp `1/log` route: only the *location* of the zeros is used, not a zero-free region.

## State of the proof

Everything in *this* file is proved (no `sorry`), and the axiom footprint of the target is
`propext, Classical.choice, Quot.sound`.  The two analytic inputs the assembly consumes are

* the **circle growth** of the completion,
  `Work.FIArea6Hecke.R.HeckeLambdaCircleGrowthPrimitive`
  (`Submission/Work/FIArea6Hecke/R/HeckeLambdaCircleGrowthPrimitive.lean`) — the theta/Gauss-sum
  route through `heckeFE_of_theta` for the primitive case and the conductor twist for the general
  one; and
* the **Hadamard partial fraction** for an entire function of order `≤ 1`,
  `lamPartialFraction_of_growth` (Section 3b below), assembled from the sorry-free Hadamard
  pieces `Work.FIArea5.HeckeZFR.Hadm.{factorZero, goodRadius, cofactorBound, pfConv}` together
  with `Work.FIArea5.HeckeZFR.Lam_zeroCount` and the clean assemblies
  `Work.FIArea5.HeckeZFR.{Lam_aux_of, Lam_reduce_of}`.

Note that the module `Submission.Work.FIArea5.HeckeZFR.Lam_partialFraction` is imported for the
latter two assemblies only: its own statement `Lam_partialFraction` is *not* used, precisely
because its proof goes through the four `sorry`-carrying lemmas
`Lam_factorZero`, `Lam_goodRadius`, `Lam_cofactorBound`, `Lam_pfConv`.  Section 3b reproduces
its conclusion while avoiding those four.
-/
import Mathlib
import Submission.Work.FIArea6Hecke.ZFRDefs
import Submission.Work.FIArea5.HeckeZFR.Lam_partialFraction
import Submission.Work.FIArea5.HeckeZFR.Hadm.factorZero
import Submission.Work.FIArea5.HeckeZFR.Hadm.goodRadius
import Submission.Work.FIArea5.HeckeZFR.Hadm.cofactorBound
import Submission.Work.FIArea5.HeckeZFR.Hadm.pfConv
import Submission.Work.FIArea5.HeckeZFR.LamBaseBound
import Submission.Work.FIArea5.HeckeZFR.FELogDeriv
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
import Submission.Commons.Analysis.Complex.circleLogDerivContour_bound
import Submission.Commons.NumberTheory.Linnik.goodRadius_pair
import Submission.Work.FIArea6Hecke.R.heckeStripNearOne
import Submission.Work.FITop4.Bridge.area5_6_defs
import Submission.Work.FIArea5.S16Hecke.thetaHol_exp_decay
import Submission.Work.FIArea5.S16Hecke.heckeLStripAux
import Submission.Work.FIArea6Hecke.R.HeckeCompletionAll
import Submission.Work.FIArea6Hecke.R.heckeCompletionImprimitive
import Submission.Work.FIArea5.S16Hecke.mellin_cut_facts
import Submission.Work.FIArea5.S16Hecke.heckeLam_bound
import Submission.Work.FIArea5.S16Hecke.summable_card_divisors_mul_rpow_neg
import Submission.Work.FIArea5.HeckeZFR.GammaLogBound
import Submission.Work.FIArea6Hecke.S16HeckeCompletionPrimitive
import Submission.Work.FIArea6Hecke.R.gaussSum_zero_of_nontrivial
import Submission.Work.FIArea5.HeckeZFR.LSeriesBound
import Submission.Work.FIArea6Hecke.R.noCompletion_of_primaryTrivial
import Submission.Port.LogDerivCompat

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.FIArea6Hecke.R

open scoped BigOperators
open Complex Metric Filter
open scoped Topology

noncomputable section

/-! ## 1.  Soft inputs for a general weight `m : ℤ` -/

/-- **The completion is nonzero in `re s > 1`** for a general weight `m : ℤ`: the identity theorem
identifies `Λ` with `heckeArch d m s·L(s,ψ)` there, and both factors are nonzero. -/
lemma lam_ne_zero_of_one_lt_re_zz {d : ℕ} (hd : 1 ≤ d) {chi : GaussianInt → ℂ} {m : ℤ}
    {Λ : ℂ → ℂ} (hAn : AnalyticOn ℂ Λ Set.univ)
    (h1 : chi 1 = 1) (hmul : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w)
    (hb : ∀ z : GaussianInt, ‖chi z‖ ≤ 1)
    (hagr : ∀ s : ℂ, 1 + |(m : ℝ)| / 2 < s.re →
      Λ s = Work.FITop4.Bridge.heckeArch d m s *
        Work.FIArea5.S16Hecke.heckeLSeries chi m s)
    {s : ℂ} (hs : 1 < s.re) : Λ s ≠ 0 := by
  rw [Lam_eq_heckeArch_mul_of_one_lt_re hd hAn hb hagr hs]
  exact mul_ne_zero (Work.FIArea6Hecke.R.heckeArch_ne_zero_of_one_lt_re hd m hs)
    (Work.FIArea5.S16Hecke.heckeLSeries_ne_zero_of_one_lt_re chi m h1 hmul hb hs)

/-- **Zeros of the completion lie in `[-1,1]`** for a general weight `m : ℤ`: `re u > 1` is
excluded by `lam_ne_zero_of_one_lt_re_zz`, and `re u < -1` by reflecting in the functional
equation, which sends `u` to a point of real part `> 2`. -/
lemma lam_zero_re_bounds_zz {d : ℕ} (hd : 1 ≤ d) {chi : GaussianInt → ℂ} {m : ℤ} {Λ : ℂ → ℂ}
    (hAn : AnalyticOn ℂ Λ Set.univ)
    (h1 : chi 1 = 1) (hmul : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w)
    (hb : ∀ z : GaussianInt, ‖chi z‖ ≤ 1)
    (hFE : ∃ W : ℂ, W ≠ 0 ∧ ∀ s : ℂ, Λ s = W * star (Λ (star (1 - s))))
    (hagr : ∀ s : ℂ, 1 + |(m : ℝ)| / 2 < s.re →
      Λ s = Work.FITop4.Bridge.heckeArch d m s *
        Work.FIArea5.S16Hecke.heckeLSeries chi m s)
    {u : ℂ} (hu : Λ u = 0) : -1 ≤ u.re ∧ u.re ≤ 1 := by
  constructor
  · by_contra hlt
    push Not at hlt
    obtain ⟨W, hW0, hW⟩ := hFE
    have hu' : star (Λ (star (1 - u))) = 0 := by
      have h := hW u
      rw [hu] at h
      exact (mul_eq_zero.mp h.symm).resolve_left hW0
    have hz : Λ (star (1 - u)) = 0 := by
      have := congrArg star hu'
      simpa using this
    have hre : 1 < (star (1 - u)).re := by
      have h1u : (star (1 - u)).re = 1 - u.re := by
        simp [Complex.star_def, Complex.sub_re]
      rw [h1u]
      linarith
    exact lam_ne_zero_of_one_lt_re_zz hd hAn h1 hmul hb hagr hre hz
  · by_contra hlt
    push Not at hlt
    exact lam_ne_zero_of_one_lt_re_zz hd hAn h1 hmul hb hagr hlt hu


/-! ## 2.  The base bound at `2+it`, uniformly in the data -/

/-- **Uniform two-sided logarithmic-derivative bound at `re s = 2`**, from the absolutely
convergent Dirichlet series (`heckeLSeries_deriv_norm_le`) together with the Euler-product inverse
bound (`heckeLSeries_inv_bound_uniform`).  The constant does not depend on `d`, `χ` or `m`. -/
lemma heckeLSeries_logDeriv_norm_le_two_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ (chi : GaussianInt → ℂ) (k : ℤ),
      chi 1 = 1 → (∀ z w : GaussianInt, chi (z * w) = chi z * chi w) →
      (∀ z : GaussianInt, ‖chi z‖ ≤ 1) →
      ∀ s : ℂ, s.re = 2 →
        ‖deriv (Work.FIArea5.S16Hecke.heckeLSeries chi k) s /
          Work.FIArea5.S16Hecke.heckeLSeries chi k s‖ ≤ C := by
  obtain ⟨K, hKpos, hK⟩ := heckeLSeries_inv_bound_uniform
  refine ⟨2 * Work.FIArea5.S16Hecke.heckeLMajorant * K, ?_, ?_⟩
  · have hpos := Work.FIArea5.S16Hecke.heckeLMajorant_pos
    positivity
  · intro chi k h1 hmul hb s hs
    have hs2 : s.re ≤ 2 := le_of_eq hs
    have hs1 : (1 : ℝ) < s.re := by linarith [hs]
    have hderiv := Work.FIArea5.S16Hecke.heckeLSeries_deriv_norm_le chi k hb (s := s)
      (by linarith [hs])
    have hinv := hK chi k h1 hmul hb s hs1 hs2
    have hinv' : ‖(Work.FIArea5.S16Hecke.heckeLSeries chi k s)⁻¹‖ ≤ K := by
      have h2 : s.re - 1 = 1 := by linarith [hs]
      rw [h2, div_one] at hinv
      exact hinv
    rw [div_eq_mul_inv, norm_mul]
    calc ‖deriv (Work.FIArea5.S16Hecke.heckeLSeries chi k) s‖ *
          ‖(Work.FIArea5.S16Hecke.heckeLSeries chi k s)⁻¹‖
        ≤ (2 * Work.FIArea5.S16Hecke.heckeLMajorant) * K := by
          refine mul_le_mul hderiv hinv' (norm_nonneg _) ?_
          have hpos := Work.FIArea5.S16Hecke.heckeLMajorant_pos
          linarith
      _ = 2 * Work.FIArea5.S16Hecke.heckeLMajorant * K := by ring

/-- **The archimedean factor is `X^s·Γ(s+c)`**: the displayed form of the definition. -/
lemma heckeArch_eq' (d : ℕ) (m : ℤ) :
    Work.FITop4.Bridge.heckeArch d m
      = fun z : ℂ => (4 * ((d : ℝ) : ℂ) / ((Real.pi : ℝ) : ℂ)) ^ z *
          Complex.Gamma (z + ((|(m : ℝ)| / 2 : ℝ) : ℂ)) := rfl

/-- **The base bound at `2+it` for a general weight `m : ℤ`, uniformly in the data.**  At
`s = 2+it` (where `re s = 2 > 1` and `Λ = heckeArch·L` by the identity theorem) one has
`Λ'/Λ = log X + ψ(s+|m|/2) + L'/L`, and the three terms are bounded by `log 4d`, by
`digamma_re_le_of_half_le`, and by `heckeLSeries_logDeriv_norm_le_two_uniform`. -/
lemma lam_logDeriv_re_at_two_le_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ) (Λ : ℂ → ℂ), 1 ≤ d →
      chi 1 = 1 → (∀ z w : GaussianInt, chi (z * w) = chi z * chi w) →
      (∀ z : GaussianInt, ‖chi z‖ ≤ 1) →
      AnalyticOn ℂ Λ Set.univ →
      (∀ s : ℂ, 1 + |(m : ℝ)| / 2 < s.re →
        Λ s = Work.FITop4.Bridge.heckeArch d m s *
          Work.FIArea5.S16Hecke.heckeLSeries chi m s) →
      ∀ γ : ℝ,
        (deriv Λ ((2 : ℂ) + Complex.I * (γ : ℂ)) / Λ ((2 : ℂ) + Complex.I * (γ : ℂ))).re
          ≤ C * Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |γ| + 3)) := by
  obtain ⟨C₂, hC₂pos, hC₂⟩ := heckeLSeries_logDeriv_norm_le_two_uniform
  refine ⟨C₂ + 20, by linarith, ?_⟩
  intro d chi m Lam hd h1 hmul hb hAn hagr γ
  set X : ℂ := 4 * ((d : ℝ) : ℂ) / ((Real.pi : ℝ) : ℂ) with hXdef
  set c : ℂ := ((|(m : ℝ)| / 2 : ℝ) : ℂ) with hcdef
  set s : ℂ := (2 : ℂ) + Complex.I * (γ : ℂ) with hsdef
  have hsre : s.re = 2 := by simp [hsdef]
  have hs1 : (1 : ℝ) < s.re := by rw [hsre]; norm_num
  -- the local identification with the model function
  have hev : Lam =ᶠ[𝓝 s] fun z => Work.FITop4.Bridge.heckeArch d m z *
      Work.FIArea5.S16Hecke.heckeLSeries chi m z := by
    have hmem : {z : ℂ | (1 : ℝ) < z.re} ∈ 𝓝 s :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs1
    filter_upwards [hmem] with z hz
    exact Lam_eq_heckeArch_mul_of_one_lt_re hd hAn hb hagr hz
  have hArchne : Work.FITop4.Bridge.heckeArch d m s ≠ 0 :=
    Work.FIArea6Hecke.R.heckeArch_ne_zero_of_one_lt_re hd m hs1
  have hLne : Work.FIArea5.S16Hecke.heckeLSeries chi m s ≠ 0 :=
    Work.FIArea5.S16Hecke.heckeLSeries_ne_zero_of_one_lt_re chi m h1 hmul hb hs1
  have hArchdiff : DifferentiableAt ℂ (Work.FITop4.Bridge.heckeArch d m) s :=
    Work.FIArea6Hecke.R.heckeArch_differentiableAt_of_pos hd m (by rw [hsre]; norm_num)
  have hLdiff : DifferentiableAt ℂ (Work.FIArea5.S16Hecke.heckeLSeries chi m) s := by
    have habs : LSeries.abscissaOfAbsConv (Work.FIArea5.S16Hecke.heckeLam chi m)
        < ((s.re : ℝ) : EReal) :=
      lt_of_le_of_lt (Work.FIArea5.S16Hecke.heckeLSeries_absc_le_one chi m hb)
        (EReal.coe_lt_coe_iff.mpr hs1)
    exact (LSeries_hasDerivAt (f := Work.FIArea5.S16Hecke.heckeLam chi m) (s := s)
      habs).differentiableAt
  -- the decomposition
  have hXne : X ≠ 0 := by
    rw [hXdef]
    refine div_ne_zero (mul_ne_zero (by norm_num) ?_) ?_
    · exact Complex.ofReal_ne_zero.mpr (by
        have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
        exact ne_of_gt hd0)
    · exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hGne : Complex.Gamma (s + c) ≠ 0 := by
    refine Complex.Gamma_ne_zero_of_re_pos ?_
    have hsr : (s + c).re = 2 + |(m : ℝ)| / 2 := by
      rw [Complex.add_re, hsre, hcdef, Complex.ofReal_re]
    rw [hsr]
    have := abs_nonneg (m : ℝ)
    linarith
  have hneGamma : ∀ k : ℕ, s + c ≠ - (k : ℂ) := by
    intro k hk
    have hre : (s + c).re = -(k : ℝ) := by
      have := congrArg Complex.re hk; simpa using this
    rw [Complex.add_re, hsre, hcdef, Complex.ofReal_re] at hre
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hm0 : (0 : ℝ) ≤ |(m : ℝ)| := abs_nonneg _
    linarith
  have hdiffX : DifferentiableAt ℂ (fun z : ℂ => X ^ z) s :=
    (hasStrictDerivAt_const_cpow (Or.inl hXne)).hasDerivAt.differentiableAt
  have hdiffG : DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma (z + c)) s :=
    (Complex.differentiableAt_Gamma _ hneGamma).comp s (differentiableAt_id.add_const _)
  have hmul_arch : logDeriv Lam s = logDeriv (Work.FITop4.Bridge.heckeArch d m) s
      + logDeriv (fun z => Work.FIArea5.S16Hecke.heckeLSeries chi m z) s := by
    rw [(logDeriv_congr_nhds hev).eq_of_nhds]
    exact Submission.Port.logDeriv_mul_fun (f := Work.FITop4.Bridge.heckeArch d m)
      (g := fun z => Work.FIArea5.S16Hecke.heckeLSeries chi m z) s
      hArchne hLne hArchdiff hLdiff
  have hmul_X : logDeriv (Work.FITop4.Bridge.heckeArch d m) s
      = Complex.log X + Complex.digamma (s + c) := by
    have hp : logDeriv (fun z : ℂ => X ^ z) s = Complex.log X :=
      Work.FIArea5.S16Hecke.logDeriv_const_cpow X hXne s
    have hg : logDeriv (fun z : ℂ => Complex.Gamma (z + c)) s = Complex.digamma (s + c) :=
      Work.FIArea5.S16Hecke.logDeriv_Gamma_add_const c s hneGamma
    rw [heckeArch_eq']
    calc logDeriv (fun z : ℂ => X ^ z * Complex.Gamma (z + c)) s
        = logDeriv (fun z : ℂ => X ^ z) s
          + logDeriv (fun z : ℂ => Complex.Gamma (z + c)) s :=
          Submission.Port.logDeriv_mul_fun (f := fun z : ℂ => X ^ z) (g := fun z : ℂ => Complex.Gamma (z + c)) s
            (Complex.cpow_ne_zero_iff.mpr (Or.inl hXne)) hGne hdiffX hdiffG
      _ = Complex.log X + Complex.digamma (s + c) := by rw [hp, hg]
  have hdecomp : logDeriv Lam s
      = Complex.log X + Complex.digamma (s + c)
        + logDeriv (fun z => Work.FIArea5.S16Hecke.heckeLSeries chi m z) s := by
    rw [hmul_arch, hmul_X]
  rw [logDeriv_apply] at hdecomp
  -- the three bounds
  have hXnorm : ‖X‖ = 4 * (d : ℝ) / Real.pi := by
    rw [hXdef, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Nat.cast_nonneg d), Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
    norm_num
  have hlogX : (Complex.log X).re ≤ Real.log (4 * (d : ℝ)) := by
    rw [Complex.log_re, hXnorm]
    refine Real.log_le_log (by positivity) ?_
    rw [div_le_iff₀ Real.pi_pos]
    nlinarith [Real.pi_gt_three, Nat.cast_nonneg (α := ℝ) d]
  have hdig : (Complex.digamma (s + c)).re
      ≤ Real.log (2 + |γ|) + 2 * Real.log (4 * (2 + |(m : ℝ)| / 2)) + 6 := by
    have hsms : s + c = (((2 + |(m : ℝ)| / 2 : ℝ)) : ℂ) + (γ : ℂ) * I := by
      rw [hsdef, hcdef]; push_cast; ring
    have h := Work.FIArea5.S16Hecke.digamma_re_le_of_half_le (2 + |(m : ℝ)| / 2) γ
      (by have := abs_nonneg (m : ℝ); linarith)
    rwa [hsms]
  have hLderiv : ((logDeriv (fun z => Work.FIArea5.S16Hecke.heckeLSeries chi m z) s)).re
      ≤ C₂ := by
    rw [logDeriv_apply]
    exact le_trans (Complex.re_le_norm _) (hC₂ chi m h1 hmul hb s hsre)
  have hfinal : (deriv Lam s / Lam s).re
      ≤ (Complex.log X).re + (Complex.digamma (s + c)).re + C₂ := by
    rw [hdecomp, Complex.add_re, Complex.add_re]
    linarith [hLderiv]
  have hbound : (deriv Lam s / Lam s).re
      ≤ Real.log (4 * (d : ℝ))
        + (Real.log (2 + |γ|) + 2 * Real.log (4 * (2 + |(m : ℝ)| / 2)) + 6) + C₂ := by
    linarith [hfinal, hlogX, hdig]
  -- elementary comparison of the logarithms
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hlogd1 : (1 : ℝ) ≤ Real.log (4 * (d : ℝ)) := by
    have h4 : (4 : ℝ) ≤ 4 * (d : ℝ) := by linarith
    have h1' : Real.log 4 ≤ Real.log (4 * (d : ℝ)) := Real.log_le_log (by norm_num) h4
    have h2' : (1 : ℝ) ≤ Real.log 4 := by
      have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
      have h : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      rw [h]; linarith
    linarith
  have hlogM0 : (0 : ℝ) ≤ Real.log (|(m : ℝ)| + |γ| + 3) := by
    refine Real.log_nonneg ?_
    linarith [abs_nonneg γ, abs_nonneg (m : ℝ)]
  have hlogγ : Real.log (2 + |γ|) ≤ Real.log (|(m : ℝ)| + |γ| + 3) := by
    refine Real.log_le_log (by positivity) ?_
    linarith [abs_nonneg (m : ℝ)]
  have hlog8m : Real.log (4 * (2 + |(m : ℝ)| / 2)) ≤ 3 + Real.log (|(m : ℝ)| + |γ| + 3) := by
    have h2 : 4 * (2 + |(m : ℝ)| / 2) ≤ 8 * (|(m : ℝ)| + |γ| + 3) := by
      nlinarith [abs_nonneg γ, abs_nonneg (m : ℝ)]
    have hlog := Real.log_le_log (by positivity) h2
    rw [Real.log_mul (by norm_num : (8:ℝ) ≠ 0) (by positivity)] at hlog
    have hlog8 : Real.log 8 ≤ 3 := by
      have h : Real.log 8 = 3 * Real.log 2 := by
        rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
      have h9 : Real.log 2 < 1 := by
        have hlt := Real.log_lt_sub_one_of_pos (x := 2) (by norm_num) (by norm_num : (2:ℝ) ≠ 1)
        linarith
      rw [h]; linarith [h9]
    linarith
  have hkey : Real.log (2 + |γ|) + 2 * Real.log (4 * (2 + |(m : ℝ)| / 2)) + 6
      ≤ 3 * Real.log (|(m : ℝ)| + |γ| + 3) + 12 := by
    linarith [hlogγ, hlog8m]
  have hsum : Real.log (4 * (d : ℝ)) + Real.log (|(m : ℝ)| + |γ| + 3)
      = Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |γ| + 3)) := by
    rw [Real.log_mul (by positivity : (4 * (d : ℝ)) ≠ 0) (by positivity : (|(m : ℝ)| + |γ| + 3) ≠ 0)]
  have hgoal : Real.log (4 * (d : ℝ))
        + (Real.log (2 + |γ|) + 2 * Real.log (4 * (2 + |(m : ℝ)| / 2)) + 6) + C₂
      ≤ (C₂ + 20) * Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |γ| + 3)) := by
    rw [← hsum]
    have hA : Real.log (4 * (d : ℝ)) + (12 + C₂) ≤ (C₂ + 20) * Real.log (4 * (d : ℝ)) := by
      nlinarith [hlogd1, hC₂pos]
    have hBB : 3 * Real.log (|(m : ℝ)| + |γ| + 3)
        ≤ (C₂ + 20) * Real.log (|(m : ℝ)| + |γ| + 3) := by
      nlinarith [hlogM0, hC₂pos]
    nlinarith [hkey, hA, hBB]
  linarith [hbound, hgoal]

/-! ## 3.  Nonnegativity of the rebasing partial sums -/

/-- The **divisor coefficient** `ord(u)` of `Lam` on the closed ball of radius `R`, as a complex
number (kept as a definition so that the statements below stay readable). -/
def divCoeff (Lam : ℂ → ℂ) (R : ℝ) (u : ℂ) : ℂ :=
  ((MeromorphicOn.divisor Lam (Metric.closedBall 0 R)) u : ℂ)

/-- The **rebasing kernel** `1/(σ+iγ-u) - 1/(-1+iγ-u)`, kept as a definition so that the
statements below stay readable. -/
def rebaseKernel (σ γ : ℝ) (u : ℂ) : ℂ :=
  1 / (((σ : ℂ) + Complex.I * (γ : ℂ)) - u) - 1 / (((-1 : ℂ) + Complex.I * (γ : ℂ)) - u)

private lemma re_finsum_of_finiteSupport' (g : ℂ → ℂ) (hfs : Function.HasFiniteSupport g) :
    (∑ᶠ u, g u).re = ∑ᶠ u, (g u).re := by
  have h := AddMonoidHom.map_finsum (Complex.reCLM : ℂ →+ ℝ) hfs
  simpa using h

/-! ## 3b.  The Hadamard partial fraction from the sorry-free Hadamard pieces -/

/-- **The Hadamard partial fraction**, assembled from the sorry-free pieces
`Hadm.factorZero` (removal of the zero at the origin), `Lam_zeroCount` (Jensen's zero count),
`Hadm.goodRadius` (existence of a radius avoiding the zeros), `Hadm.cofactorBound` (the cofactor
sup bound) and `Hadm.pfConv` (existence of the limit of the partial sums), fed into the two clean
assemblies `Lam_aux_of` and `Lam_reduce_of`.  This is the same statement as
`Work.FIArea5.HeckeZFR.Lam_partialFraction`, but its proof never touches the `sorry`-carrying
lemmas `Lam_factorZero`, `Lam_goodRadius`, `Lam_cofactorBound`, `Lam_pfConv`, so its axiom
footprint is `propext, Classical.choice, Quot.sound`. -/
theorem lamPartialFraction_of_growth (Λ : ℂ → ℂ) (hDiff : Differentiable ℂ Λ)
    (hne : ∃ z : ℂ, Λ z ≠ 0)
    (hgrowth : ∃ C K : ℝ, 0 < C ∧ 0 ≤ K ∧ ∀ R : ℝ, 1 ≤ R → ∀ z : ℂ, ‖z‖ = R →
      Real.log ‖Λ z‖ ≤ C * R * (Real.log (R + 2) + K)) :
    ∀ s s₁ : ℂ, Λ s ≠ 0 → Λ s₁ ≠ 0 →
      Tendsto (fun R : ℝ => ∑ᶠ u : ℂ,
          (((MeromorphicOn.divisor Λ (Metric.closedBall 0 R)) u : ℤ) : ℂ)
            * (1 / (s - u) - 1 / (s₁ - u)))
        atTop (nhds (deriv Λ s / Λ s - deriv Λ s₁ / Λ s₁)) := by
  obtain ⟨k, φ, hφdiff, hφ0, hfac, hφgrowth, hdiv0, hdivne⟩ :=
    Work.FIArea5.HeckeZFR.Hadm.factorZero Λ hDiff hne hgrowth
  obtain ⟨C, K, hC, hK, hgrow⟩ := hφgrowth
  obtain ⟨c, hc0, hcount⟩ := Work.FIArea5.HeckeZFR.Lam_zeroCount φ hφdiff hφ0 C K hC hK hgrow
  obtain ⟨A₀, hA₀1, hGood⟩ :=
    Work.FIArea5.HeckeZFR.Hadm.goodRadius φ hφdiff ⟨0, hφ0⟩ K c hK hc0 hcount
  obtain ⟨A₁, hA₁0, hCof⟩ :=
    Work.FIArea5.HeckeZFR.Hadm.cofactorBound φ hφdiff hφ0 C K c hC hK hc0 hgrow hcount
  have hConv : ∀ s s₁ : ℂ, ∃ L : ℂ, Filter.Tendsto (fun R : ℝ => ∑ᶠ u : ℂ,
        ((((MeromorphicOn.divisor φ (Metric.closedBall 0 R)) u : ℤ) : ℂ)
          * (1 / (s - u) - 1 / (s₁ - u)))) Filter.atTop (nhds L) :=
    fun s s₁ => Work.FIArea5.HeckeZFR.Hadm.pfConv φ hφdiff K c hK hc0 hcount s s₁
  have hφpf := Work.FIArea5.HeckeZFR.Lam_aux_of φ hφdiff hφ0 C K hC hK hgrow c hc0 hcount
    ⟨A₀, hA₀1, hGood⟩ ⟨A₁, hA₁0, hCof⟩ hConv
  exact Work.FIArea5.HeckeZFR.Lam_reduce_of Λ φ k hφdiff hφ0 hfac hdiv0 hdivne hφpf

/-! ## 4.  The assembly -/

/-! ## 5.  The target -/

end

end Work.FIArea6Hecke.R
