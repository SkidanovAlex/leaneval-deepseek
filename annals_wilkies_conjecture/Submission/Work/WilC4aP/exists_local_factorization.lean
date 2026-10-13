import Mathlib
import Submission.Work.WilC4aP.Basic
import Submission.Work.WilC4aP.prod_eq_of_distinct_roots
import Submission.Work.WilC4aP.exists_root_enum
import Submission.Work.WilC4aP.exists_ball_injective
import Submission.Work.WilC4aP.analytic_bivariate_Pz_eval
import Submission.Work.WilC4aP.fderiv_snd_Pz_eval

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
open scoped BigOperators ContDiff

namespace Work.WilC4aP

open Polynomial

/-! ### Tools

Tools used in the assembly below:
* `isInvertible_smul_one`: multiplication by a nonzero complex number is an invertible
  continuous linear endomorphism of `ℂ`;
* `exists_analytic_zero_of_invertible_partial`: the (one-dimensional) analytic implicit
  function theorem, deduced from Mathlib's `C^ω` implicit function theorem;
* `exists_analytic_root_at`: the latter applied to `(z, Y) ↦ (Pz P z).eval Y` — a simple root
  `α` of the fibre at `z₀` lifts to a holomorphic root function on a ball around `z₀`. -/

lemma isInvertible_smul_one {c : ℂ} (hc : c ≠ 0) :
    ((c • (1 : ℂ →L[ℂ] ℂ))).IsInvertible := by
  refine ContinuousLinearMap.IsInvertible.of_inverse
    (g := (c⁻¹ : ℂ) • (1 : ℂ →L[ℂ] ℂ)) ?_ ?_
  · ext x
    simp [smul_eq_mul, mul_inv_cancel₀ hc, inv_mul_cancel₀ hc]
  · ext x
    simp [smul_eq_mul, mul_inv_cancel₀ hc, inv_mul_cancel₀ hc]

/-- **Analytic implicit function theorem in one complex variable.** If `f` is holomorphic at
`(z₀, α)`, vanishes there, and its derivative in the second variable is invertible, then the zero
set of `f` is locally a graph of a holomorphic function of the first variable. -/
lemma exists_analytic_zero_of_invertible_partial {f : ℂ × ℂ → ℂ} {z₀ α : ℂ}
    (hf : AnalyticAt ℂ f (z₀, α)) (h0 : f (z₀, α) = 0)
    (hinv : (fderiv ℂ f (z₀, α) ∘L ContinuousLinearMap.inr ℂ ℂ ℂ).IsInvertible) :
    ∃ (ζ : ℂ → ℂ) (ρ : ℝ), 0 < ρ ∧ AnalyticOnNhd ℂ ζ (Metric.ball z₀ ρ) ∧ ζ z₀ = α ∧
      ∀ z ∈ Metric.ball z₀ ρ, f (z, ζ z) = 0 := by
  -- Mathlib's `C^ω` implicit function theorem
  have hcd : ContDiffAt ℂ ω f (z₀, α) := hf.contDiffAt
  have hω0 : (ω : ℕ∞ω) ≠ 0 := by decide
  let ψ : ℂ → ℂ := hcd.implicitFunction hω0 hinv
  have hψval : ψ z₀ = α := hcd.implicitFunction_apply_self hω0 hinv
  have hψev : {z : ℂ | f (z, ψ z) = 0} ∈ 𝓝 z₀ := by
    filter_upwards [hcd.eventually_apply_implicitFunction hω0 hinv] with z hz
    rw [hz, h0]
  have hψcd : ContDiffAt ℂ ω ψ z₀ := hcd.contDiffAt_implicitFunction hω0 hinv
  -- `C^ω` at a point means analytic on a neighbourhood
  obtain ⟨u, hu, hAn⟩ := ContDiffWithinAt.analyticOn hψcd
  have hu_mem : u ∈ 𝓝 z₀ := by simpa using hu
  have hmem : u ∩ {z : ℂ | f (z, ψ z) = 0} ∈ 𝓝 z₀ := Filter.inter_mem hu_mem hψev
  obtain ⟨ρ, hρ, hsub⟩ := Metric.mem_nhds_iff.mp hmem
  refine ⟨ψ, ρ, hρ, ?_, hψval, fun z hz => (hsub hz).2⟩
  exact ((hAn.differentiableOn).mono (fun z hz => (hsub hz).1)).analyticOnNhd Metric.isOpen_ball

/-- **Analytic implicit function theorem for the fibre polynomial.** If all coefficients of `P`
are holomorphic at `z₀` and `α` is a simple root of the fibre `Pz P z₀`, then `α` lifts to a
holomorphic root function `ζ` on a ball around `z₀`, with `ζ z₀ = α`. -/
lemma exists_analytic_root_at (P : Polynomial (ℂ → ℂ)) {z₀ : ℂ}
    (han : HolCoeffs P z₀) {α : ℂ} (hα : (Pz P z₀).eval α = 0)
    (hder : (Pz P z₀).derivative.eval α ≠ 0) :
    ∃ (ζ : ℂ → ℂ) (ρ : ℝ), 0 < ρ ∧ AnalyticOnNhd ℂ ζ (Metric.ball z₀ ρ) ∧ ζ z₀ = α ∧
      ∀ z ∈ Metric.ball z₀ ρ, (Pz P z).eval (ζ z) = 0 := by
  have hana := analytic_bivariate_Pz_eval P z₀ α han
  refine exists_analytic_zero_of_invertible_partial hana ?_ ?_
  · exact hα
  · rw [fderiv_snd_Pz_eval P z₀ α (AnalyticAt.differentiableAt hana)]
    exact isInvertible_smul_one hder

/-! ### The factorization -/

/-- Local factorization of a monic polynomial with holomorphic coefficients at a point of the
base where all roots are simple.

PROOF HINT: the fibre at `z₀` is monic of degree `m` with `m` distinct roots; lift each root
by `exists_analytic_root_of_simple` (a sibling hole in the same area) to a holomorphic `η j`.
The `η j` stay distinct near `z₀`, so `∏ j, (X - C (η j z))` divides `Pz P z` (divide, then
use that a polynomial of degree `< m` vanishing at `m` distinct points is zero); both are
monic of degree `m`, hence equal. -/
theorem exists_local_factorization {m : ℕ} (P : Polynomial (ℂ → ℂ)) (hmon : P.Monic)
    (hdeg : P.natDegree = m) (z₀ : ℂ) (han : Work.WilC4aP.HolCoeffs P z₀)
    (hsep : ∀ w : ℂ, (Work.WilC4aP.Pz P z₀).eval w = 0 →
      (Work.WilC4aP.Pz P z₀).derivative.eval w ≠ 0) :
    ∃ (ρ : ℝ) (η : Fin m → ℂ → ℂ), 0 < ρ ∧
      (∀ j, AnalyticOnNhd ℂ (η j) (Metric.ball z₀ ρ)) ∧
      ∀ z ∈ Metric.ball z₀ ρ, Work.WilC4aP.Pz P z = ∏ j, (Polynomial.X - Polynomial.C (η j z)) := by
  classical
  -- the fibre at `z₀` is monic of degree `m` and has `m` distinct roots: enumerate them
  obtain ⟨r, hrinj, hroot⟩ :=
    exists_root_enum (monic_Pz hmon z₀) (by rw [natDegree_Pz hmon z₀, hdeg]) hsep
  -- lift each root to a holomorphic branch
  have key : ∀ j : Fin m, ∃ (ζ : ℂ → ℂ) (ρ : ℝ), 0 < ρ ∧
      AnalyticOnNhd ℂ ζ (Metric.ball z₀ ρ) ∧ ζ z₀ = r j ∧
      ∀ z ∈ Metric.ball z₀ ρ, (Work.WilC4aP.Pz P z).eval (ζ z) = 0 :=
    fun j => exists_analytic_root_at P han (hroot j) (hsep (r j) (hroot j))
  choose ζ ρj hρj hζan hζ0 hζroot using key
  -- a common radius of analyticity and of vanishing
  have hmem : (⋂ j, Metric.ball z₀ (ρj j)) ∈ 𝓝 z₀ :=
    Filter.iInter_mem.mpr fun j => Metric.ball_mem_nhds z₀ (hρj j)
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hmem
  -- the branches stay distinct near `z₀`
  have hcont : ∀ j, ContinuousAt (ζ j) z₀ := fun j =>
    (hζan j).continuousOn.continuousAt (Metric.ball_mem_nhds z₀ (hρj j))
  have hinj0 : Function.Injective (fun j => ζ j z₀) := by
    intro j k hjk
    apply hrinj
    rw [← hζ0 j, ← hζ0 k]
    exact hjk
  obtain ⟨ρI, hρI, hinjI⟩ := exists_ball_injective hcont hinj0
  refine ⟨min ε ρI, ζ, lt_min hε hρI, ?_, ?_⟩
  · intro j
    exact (hζan j).mono fun z hz => by
      have h1 : z ∈ Metric.ball z₀ ε := Metric.ball_subset_ball (min_le_left _ _) hz
      exact Set.mem_iInter.mp (hεsub h1) j
  · intro z hz
    -- on the common ball, `z ↦ ζ j z` are distinct roots of the monic fibre of degree `m`
    have h1 : z ∈ Metric.ball z₀ ε := Metric.ball_subset_ball (min_le_left _ _) hz
    have hzU : z ∈ ⋂ j, Metric.ball z₀ (ρj j) := hεsub h1
    have hzρ : ∀ j, z ∈ Metric.ball z₀ (ρj j) := fun j => Set.mem_iInter.mp hzU j
    have hzI : z ∈ Metric.ball z₀ ρI := Metric.ball_subset_ball (min_le_right _ _) hz
    exact prod_eq_of_distinct_roots (monic_Pz hmon z) (by rw [natDegree_Pz hmon z, hdeg])
      (hinjI z hzI) (fun j => hζroot j z (hzρ j))

end Work.WilC4aP
