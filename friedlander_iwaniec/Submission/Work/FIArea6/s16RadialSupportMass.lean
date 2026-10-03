/-
# `Submission.Work.FIArea6.s16RadialSupportMass`

The radial support mass of §16: for a function `F` on the Gaussian integers whose support is
contained in the polar box (5.14) — norm in `(N, (1+θ)N]`, argument in a sector of width `2πθ`,
squarefree norm — and whose pointwise size obeys the coefficient bound `‖F z‖ ≤ τ(|z|²)` (4.13),
the total mass `Σ_{z ∈ boxN} ‖F z‖` is `O((√N + θN) log^9(2+N))`.

The analytic content is the sector τ-sum `Work.FIArea6b.sector_tau_sum`; here we only

* convert `Σ ‖F z‖` into the sum of `τ(|z|²)` over the support `{z : F z ≠ 0}` (using the
  pointwise hypothesis, which is exactly the size bound of a §16 coefficient), and
* observe that the support of `F` is contained in the index set of the sector τ-sum: it lies in
  the polar box (5.14) and hence in the box `gBox ⌈√(4N(1+θ))⌉` which contains `boxN`.
-/
import Mathlib
import Submission.Work.FIArea6b.sector_tau_sum
import Submission.Work.FITop.Defs
import Submission.Work.FIPlan.Interface

namespace Work.FIArea6

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 0. The elementary facts used to place the support in the sector sum -/

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

/-! ## 1. The mass estimate -/

theorem s16RadialSupportMass :
    ∃ C : ℝ, 0 < C ∧ ∀ (Pa : Work.FITop.Params) (φ : ℝ) (F : GaussianInt → ℂ),
      (∀ z : GaussianInt, F z ≠ 0 →
        Pa.N < ((Work.FIPlan.gnorm z : ℕ) : ℝ) ∧
        ((Work.FIPlan.gnorm z : ℕ) : ℝ) ≤ (1 + Pa.θ) * Pa.N ∧
        φ < Complex.arg z.toComplex ∧ Complex.arg z.toComplex ≤ φ + 2 * Real.pi * Pa.θ ∧
        Squarefree (Work.FIPlan.gnorm z)) →
      (∀ z : GaussianInt, F z ≠ 0 → ‖F z‖ ≤ (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)) →
      ∑ z ∈ Work.FITop.boxN Pa, ‖F z‖
        ≤ C * (Real.sqrt Pa.N + Pa.θ * Pa.N) * (Real.log (2 + Pa.N)) ^ (9 : ℕ) := by
  obtain ⟨Cc, hCcpos, hCc⟩ := Work.FIArea6b.sector_tau_sum
  refine ⟨Cc, hCcpos, ?_⟩
  intro Pa φ F hsupp hF
  have hN1 : (1 : ℝ) ≤ Pa.N := Pa.hN1
  have hθ0 : 0 ≤ Pa.θ := le_of_lt Pa.hθ0
  have hθ1 : Pa.θ ≤ 1 := theta_le_one_of_params Pa
  -- Step 1: bound `Σ ‖F z‖` by the divisor sum over the support `{z : F z ≠ 0}`.
  have hstep1 : ∑ z ∈ Work.FITop.boxN Pa, ‖F z‖
      ≤ ∑ z ∈ (Work.FITop.boxN Pa).filter (fun z => F z ≠ 0),
          (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) := by
    rw [Finset.sum_filter]
    refine Finset.sum_le_sum (fun z _ => ?_)
    by_cases h : F z ≠ 0
    · rw [if_pos h]; exact hF z h
    · rw [if_neg h]
      simp only [norm_le_zero_iff]
      exact not_not.mp h
  -- Step 2: the support is contained in the index set of the sector τ-sum.
  have hRle : Work.FITop.radN Pa ≤ (⌈Real.sqrt (4 * Pa.N * (1 + Pa.θ))⌉₊ : ℤ) := by
    have h4 : 4 * Pa.N ≤ 4 * Pa.N * (1 + Pa.θ) := by nlinarith
    have hc : ⌈Real.sqrt (4 * Pa.N)⌉₊ ≤ ⌈Real.sqrt (4 * Pa.N * (1 + Pa.θ))⌉₊ :=
      Nat.ceil_mono (Real.sqrt_le_sqrt h4)
    rw [Work.FITop.radN]
    exact_mod_cast hc
  have hsub : (Work.FITop.boxN Pa).filter (fun z => F z ≠ 0)
      ⊆ ((Work.FIPlan.gBox (⌈Real.sqrt (4 * Pa.N * (1 + Pa.θ))⌉₊ : ℤ)).filter
          (fun z => Pa.N < ((Work.FIPlan.gnorm z : ℕ) : ℝ) ∧
                    ((Work.FIPlan.gnorm z : ℕ) : ℝ) ≤ (1 + Pa.θ) * Pa.N ∧
                    φ < Complex.arg z.toComplex ∧
                    Complex.arg z.toComplex ≤ φ + 2 * Real.pi * Pa.θ ∧
                    Squarefree (Work.FIPlan.gnorm z))) := by
    intro z hz
    rw [Finset.mem_filter] at hz
    obtain ⟨hzb, hzF⟩ := hz
    obtain ⟨hlo, hhi, hang1, hang2, hsf⟩ := hsupp z hzF
    rw [Finset.mem_filter]
    refine ⟨?_, hlo, hhi, hang1, hang2, hsf⟩
    have hid : Work.FITop.boxN Pa = Work.FIPlan.gBox (Work.FITop.radN Pa) := rfl
    rw [hid] at hzb
    exact gBox_mono hRle hzb
  have hlog : 0 ≤ (Real.log (2 + Pa.N)) ^ (9 : ℕ) :=
    pow_nonneg (Real.log_nonneg (by linarith)) 9
  calc ∑ z ∈ Work.FITop.boxN Pa, ‖F z‖
      ≤ ∑ z ∈ (Work.FITop.boxN Pa).filter (fun z => F z ≠ 0),
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

end

end Work.FIArea6
