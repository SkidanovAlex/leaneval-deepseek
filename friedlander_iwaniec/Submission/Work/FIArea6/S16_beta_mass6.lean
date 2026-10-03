/-
# `Submission.Work.FIArea6.S16_beta_mass6` — the §16 β-mass is `O((θN+√N+1)(log N)^9)`

*FI* §16 needs the total mass of a round-6 coefficient, `Σ_{z ∈ boxN} ‖β z‖`.  Exactly as in the
round-3/round-4 case (`FIArea6/beta_mass_le.lean`), the only inputs are

* the pointwise size bound (4.13): on its support `‖β z‖ ≤ τ(|z|²)` (from `0 ≤ q, p ≤ 1` and
  `|γ(n;C)| ≤ τ(n)`), and
* the shape of the support: the polar box (5.14) with `N < |z|² ≤ (1+θ)N`, freedom of small
  primes (5.8), `τ(|z|²) ≤ τ` (5.9) and squarefree norm (the Möbius factor of (5.13)),

so that the support sits inside the index set of the sector τ-sum
`Work.FIArea6b.sector_tau_sum` (the only arithmetic input, `O((√N + θN) log^9(2+N))`).

The round-6 predicate `IsBetaCoeff6` has the same structural clauses as round 4's `IsBetaCoeff`
(the same existentially quantified mollifiers `q`, `p` and the same defining formula for `β z`);
what is new is the (5.7) class restriction `SameClass8` and the axis restriction `IsAxisFree`.
Both are *conjunctions added to the if-condition* defining `β z`, hence they can only shrink the
support and never touch the size bound.  We therefore redo the two elementary support lemmas for
`IsBetaCoeff6` (`beta6_norm_le_divisors`, `beta6_support`) — `IsBetaCoeff6.squarefree_gnorm` is
already in `FITop4.Defs6` — and replay the `beta_mass_le` computation.  Finally the harmless `+1`
inside the parenthesis is added; since `N ≥ 1`, `log(2+N) ≥ log 3 > 0`, so this only weakens the
inequality.
-/
import Mathlib
import Submission.Work.FIArea6.S16UDefs
import Submission.Work.FITop4.Defs6
import Submission.Work.FITop3.Defs3
import Submission.Work.FITop3.Smooth
import Submission.Work.FITop3.Smooth.sm_props
import Submission.Work.FITop3.Majorant.majorant_props
import Submission.Work.FITop3.Witness.exists_primary_norm
import Submission.Work.FIArea6.elem_helpers
import Submission.Work.FIArea6b.sector_tau_sum

namespace Work.FIArea6

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. The elementary API of the round-6 coefficient -/

/-- `θ ≤ 1` for the smoothing parameter of (4.15): `θ = (log x)^{-A'}`, `log x ≥ 1`, `A' ≥ 0`. -/
private lemma theta_le_one_of_params (Pa : Work.FITop.Params) : Pa.θ ≤ 1 := by
  rw [Pa.hθ]
  have hx3 : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
  have hlog : 1 ≤ Real.log (Pa.x : ℝ) := by
    have h3 : (1 : ℝ) < Real.log 3 := by
      have h := Real.log_lt_log (Real.exp_pos 1) Real.exp_one_lt_three
      rwa [Real.log_exp] at h
    exact le_of_lt (lt_of_lt_of_le h3 (Real.log_le_log (by norm_num) hx3))
  have hA'0 : (0 : ℝ) ≤ Pa.A' := by
    have h2 : (0 : ℝ) < 2 * Pa.A + 2 ^ (20 : ℕ) := by
      have := Pa.hA; positivity
    linarith [Pa.hA']
  exact Real.rpow_le_one_of_one_le_of_nonpos hlog (by linarith)

/-- **On the support of a round-6 coefficient, `‖β z‖ ≤ τ(|z|²)`** — the elementary size bound
(4.13): `β z = q(arg z − φ)·p(|z|²)·μ(|z|²)·γ(|z|²;C)` with `0 ≤ q, p ≤ 1` and
`|γ(n;C)| ≤ τ(n)`. -/
private lemma beta6_norm_le_divisors {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ} (hβ : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) (z : GaussianInt) :
    ‖β z‖ ≤ (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) := by
  obtain ⟨q, p, -, -, hq0, hq1, -, -, hp0, hp1, -, -, hform⟩ := hβ
  rw [hform z]
  split_ifs with hz
  · have hqp : ‖(((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ)) : ℂ)‖
        ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (hq0 _) (hp0 _))]
      have h2 : q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) ≤ 1 * 1 :=
        mul_le_mul (hq1 _) (hp1 _) (hp0 _) (by norm_num)
      linarith
    have hμ : ‖(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)‖ ≤ 1 :=
      Work.FITop3.norm_moebius_le_one _
    have hγ : ‖((Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℝ) : ℂ)‖
        ≤ ((Work.FIPlan.gnorm z).divisors.card : ℝ) := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact Work.FITop3.abs_gammaTrunc_le _ _
    calc ‖(((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ)) : ℂ)
            * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)
            * ((Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℝ) : ℂ)‖
        = ‖(((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ)) : ℂ)‖
            * ‖(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)‖
            * ‖((Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℝ) : ℂ)‖ := by
          rw [norm_mul, norm_mul]
      _ ≤ 1 * 1 * ((Work.FIPlan.gnorm z).divisors.card : ℝ) := by
          gcongr
      _ = ((Work.FIPlan.gnorm z).divisors.card : ℝ) := by ring
  · simp

/-- **The support of a round-6 coefficient.**  If `β z ≠ 0` then `z` lies in the polar box (5.14)
— in particular `Pa.N < |z|² ≤ (1+Pa.θ) * Pa.N` — it is free of the primes `≤ Pa.Pz` (5.8), and
`τ(|z|²) ≤ Pa.τ` (5.9).  (The two extra conjuncts of `IsBetaCoeff6`, `SameClass8` and
`IsAxisFree`, are irrelevant here; they only make the hypothesis harder to satisfy.) -/
private lemma beta6_support {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ} (hβ : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) {z : GaussianInt}
    (hz : β z ≠ 0) :
    Work.FITop3.InPolarBox Pa φ z ∧ Work.FITop3.NoSmallPrimes Pa z
      ∧ (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) ≤ Pa.τ := by
  obtain ⟨q, p, -, -, -, -, -, -, -, -, -, -, hform⟩ := hβ
  have hcond : Work.FITop4.InPolarBox Pa φ z ∧ Work.FITop4.NoSmallPrimes Pa z
      ∧ (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) ≤ Pa.τ
      ∧ Work.FITop4.SameClass8 z z0 ∧ Work.FITop4.IsAxisFree Pa z := by
    by_contra hc
    rw [hform z, if_neg hc] at hz
    exact hz rfl
  exact ⟨hcond.1, hcond.2.1, hcond.2.2.1⟩

/-- Membership in the box `gBox R`: the coordinate box. -/
private lemma mem_gBox_iff {R : ℤ} {z : GaussianInt} :
    z ∈ Work.FIPlan.gBox R ↔ z.re ∈ Finset.Icc (-R) R ∧ z.im ∈ Finset.Icc (-R) R := by
  rw [Work.FIPlan.gBox, Finset.mem_image]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨(Finset.mem_product.mp hp).1, (Finset.mem_product.mp hp).2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(z.re, z.im), Finset.mem_product.mpr ⟨h1, h2⟩,
      Zsqrtd.ext (by simp) (by simp)⟩

/-- Monotonicity of the box `gBox`. -/
private lemma gBox_mono {R₁ R₂ : ℤ} (h : R₁ ≤ R₂) :
    Work.FIPlan.gBox R₁ ⊆ Work.FIPlan.gBox R₂ := by
  intro z hz
  rw [mem_gBox_iff] at hz ⊢
  obtain ⟨h11, h12⟩ := Finset.mem_Icc.mp hz.1
  obtain ⟨h21, h22⟩ := Finset.mem_Icc.mp hz.2
  exact ⟨Finset.mem_Icc.mpr ⟨by linarith, by linarith⟩,
         Finset.mem_Icc.mpr ⟨by linarith, by linarith⟩⟩

/-- `log (2 + N) ≥ 0` for the §16 parameters (`N ≥ 1`). -/
private lemma log_two_add_N_nonneg (Pa : Work.FITop.Params) : 0 ≤ Real.log (2 + Pa.N) := by
  refine Real.log_nonneg ?_
  linarith [Pa.hN1]

/-! ## 2. The mass estimate -/

theorem S16_beta_mass6 : ∃ C : ℝ, 0 < C ∧
    ∀ (Pa : Work.FITop.Params) (φ : ℝ) (z0 : GaussianInt) (β : GaussianInt → ℂ),
      Work.FITop4.IsBetaCoeff6 Pa φ z0 β →
      ∑ z ∈ Work.FITop.boxN Pa, ‖β z‖
        ≤ C * (Pa.θ * Pa.N + Real.sqrt Pa.N + 1) * (Real.log (2 + Pa.N)) ^ (9 : ℕ) := by
  obtain ⟨Cc, hCcpos, hCc⟩ := Work.FIArea6b.sector_tau_sum
  refine ⟨Cc, hCcpos, ?_⟩
  intro Pa φ z0 β hβ
  have hN1 : (1 : ℝ) ≤ Pa.N := Pa.hN1
  have hθ0 : 0 ≤ Pa.θ := le_of_lt Pa.hθ0
  have hθ1 : Pa.θ ≤ 1 := theta_le_one_of_params Pa
  -- Step 1: bound the box sum by the τ-sum over the support of `β`.
  have hstep1 : ∑ z ∈ Work.FITop.boxN Pa, ‖β z‖
      ≤ ∑ z ∈ (Work.FITop.boxN Pa).filter (fun z => β z ≠ 0),
          (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) := by
    rw [Finset.sum_filter]
    refine Finset.sum_le_sum (fun z _ => ?_)
    by_cases h : β z ≠ 0
    · rw [if_pos h]; exact beta6_norm_le_divisors hβ z
    · rw [if_neg h]
      simp only [norm_le_zero_iff]
      exact not_not.mp h
  -- Step 2: the support lies in the index set of the sector τ-sum.
  have hRle : Work.FITop.radN Pa ≤ (⌈Real.sqrt (4 * Pa.N * (1 + Pa.θ))⌉₊ : ℤ) := by
    have h4 : 4 * Pa.N ≤ 4 * Pa.N * (1 + Pa.θ) := by nlinarith
    have hc : ⌈Real.sqrt (4 * Pa.N)⌉₊ ≤ ⌈Real.sqrt (4 * Pa.N * (1 + Pa.θ))⌉₊ :=
      Nat.ceil_mono (Real.sqrt_le_sqrt h4)
    rw [Work.FITop.radN]
    exact_mod_cast hc
  have hsub : (Work.FITop.boxN Pa).filter (fun z => β z ≠ 0)
      ⊆ ((Work.FIPlan.gBox (⌈Real.sqrt (4 * Pa.N * (1 + Pa.θ))⌉₊ : ℤ)).filter
          (fun z => Pa.N < ((Work.FIPlan.gnorm z : ℕ) : ℝ) ∧
                    ((Work.FIPlan.gnorm z : ℕ) : ℝ) ≤ (1 + Pa.θ) * Pa.N ∧
                    φ < Complex.arg z.toComplex ∧
                    Complex.arg z.toComplex ≤ φ + 2 * Real.pi * Pa.θ ∧
                    Squarefree (Work.FIPlan.gnorm z))) := by
    intro z hz
    rw [Finset.mem_filter] at hz
    obtain ⟨hzb, hzβ⟩ := hz
    obtain ⟨hpol, -, -⟩ := beta6_support hβ hzβ
    obtain ⟨-, hlo, hhi, hang1, hang2⟩ := hpol
    rw [Finset.mem_filter]
    refine ⟨?_, hlo, hhi, hang1, hang2, Work.FITop4.IsBetaCoeff6.squarefree_gnorm hβ hzβ⟩
    have hid : Work.FITop.boxN Pa = Work.FIPlan.gBox (Work.FITop.radN Pa) := rfl
    rw [hid] at hzb
    exact gBox_mono hRle hzb
  have hlog : 0 ≤ (Real.log (2 + Pa.N)) ^ (9 : ℕ) :=
    pow_nonneg (log_two_add_N_nonneg Pa) 9
  calc ∑ z ∈ Work.FITop.boxN Pa, ‖β z‖
      ≤ ∑ z ∈ (Work.FITop.boxN Pa).filter (fun z => β z ≠ 0),
          (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) := hstep1
    _ ≤ ∑ z ∈ ((Work.FIPlan.gBox (⌈Real.sqrt (4 * Pa.N * (1 + Pa.θ))⌉₊ : ℤ)).filter
            (fun z => Pa.N < ((Work.FIPlan.gnorm z : ℕ) : ℝ) ∧
                      ((Work.FIPlan.gnorm z : ℕ) : ℝ) ≤ (1 + Pa.θ) * Pa.N ∧
                      φ < Complex.arg z.toComplex ∧
                      Complex.arg z.toComplex ≤ φ + 2 * Real.pi * Pa.θ ∧
                      Squarefree (Work.FIPlan.gnorm z))),
          (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun z _ _ => by positivity)
    _ ≤ Cc * (Real.sqrt Pa.N + Pa.θ * Pa.N) * (Real.log (2 + Pa.N)) ^ (9 : ℕ) :=
        hCc Pa.N Pa.θ φ hN1 hθ0 hθ1
    _ ≤ Cc * (Pa.θ * Pa.N + Real.sqrt Pa.N + 1) * (Real.log (2 + Pa.N)) ^ (9 : ℕ) := by
        refine mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by linarith :
            Real.sqrt Pa.N + Pa.θ * Pa.N
              ≤ Pa.θ * Pa.N + Real.sqrt Pa.N + 1) hCcpos.le) hlog

end

end Work.FIArea6
