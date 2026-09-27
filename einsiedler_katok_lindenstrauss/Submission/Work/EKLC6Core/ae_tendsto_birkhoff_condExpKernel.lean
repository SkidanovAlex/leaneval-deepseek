import Mathlib
import Submission.Work.EKLC6Core.ae_forall_pos_exists_lt_of_tendsto_integral
import Submission.Work.EKLC6Core.integral_sq_sub_const
import Submission.Work.EKLC6Core.memLp_birkhoffAverage
import Submission.Work.EKLC6Core.ae_condExp_eq_const_condExpKernel

/-!
# `Work.EKLC6Core.ae_tendsto_birkhoff_condExpKernel`

A.e.-in-`x` transfer of the `L²` mean ergodic statement (von Neumann) to the conditional measures
`ν_x = condExpKernel μ (invariants T) x`.

The mathematical content is the following.  Let `T` preserve a probability `μ` on a standard Borel
space, let `f ∈ L²(μ)`, put `m := invariants T`, `g := μ[f | m]`, `A n := birkhoffAverage ℝ T f n`
and  `Ψ n := μ[(fun y => (A n y - g y)^2) | m]`.

* `∫ Ψ n ∂μ = ∫ (A n - g)^2 ∂μ → 0` by `MeasureTheory.integral_condExp` and the hypothesis `hB`;
  since `Ψ n ≥ 0` a.e. this forces, for `μ`-a.e. `x`, `Ψ n x < ε` for some `n`
  (lemma `ae_forall_pos_exists_lt_of_tendsto_integral`, proved by Markov's inequality).
* For `μ`-a.e. `x` and every `n` the identity `∫ y, (A n y - g y)^2 ∂ν_x = Ψ n x` holds, because
  both sides are the two sides of `ProbabilityTheory.condExp_ae_eq_integral_condExpKernel` for the
  integrable function `(A n - g)^2`.
* Finally `∫ z, f z ∂ν_x = g x` a.e. and, by `ae_condExp_eq_const_condExpKernel`, `g` is `ν_x`-a.e.
  equal to the constant `g x`; hence `∫ y, (A n y - ∫ z, f z ∂ν_x)^2 ∂ν_x = Ψ n x` a.e.

Main auxiliary results (each in its own file, for reuse):
* `Work.EKLC6Core.ae_forall_pos_exists_lt_of_tendsto_integral`,
* `Work.EKLC6Core.integral_sq_sub_const`,
* `Work.EKLC6Core.memLp_birkhoffAverage`,
* `Work.EKLC6Core.ae_condExp_eq_const_condExpKernel`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory
open Filter

namespace Work.EKLC6Core

set_option linter.unusedVariables false

/-- **Abstract a.e.-transfer of an `L²`-statement through the conditional kernel.**

Let `m ≤ mX` be a sub-σ-algebra of the ambient σ-algebra of a standard Borel space `X`, `μ` a
finite measure, `F : ℕ → X → ℝ` a sequence of `L²`-functions and `h ∈ L²(μ)`.  Assume

* `hFh`: for every `n`, `(F n - μ[h|m])^2` is integrable, and
* `hB`: the integrals `∫ (F n - μ[h|m])^2 ∂μ` tend to `0`.

Then for `μ`-a.e. `x` and every `ε > 0` there is `n` with
`∫ y, (F n y - ∫ z, h z ∂ν_x)^2 ∂ν_x < ε`, where `ν_x = condExpKernel μ m x` is the conditional
measure of `μ` on the atom of `x` in `m`. -/
theorem ae_transfer_condExpKernel_aux {X : Type*} (m : MeasurableSpace X)
    [mX : MeasurableSpace X] [StandardBorelSpace X] (μ : MeasureTheory.Measure X)
    [MeasureTheory.IsFiniteMeasure μ] (hm : m ≤ mX) (F : ℕ → X → ℝ)
    (hF : ∀ n, MeasureTheory.MemLp (F n) 2 μ) (h : X → ℝ) (hh : MeasureTheory.MemLp h 2 μ)
    (hFh : ∀ n, MeasureTheory.Integrable (fun y => (F n y - MeasureTheory.condExp m μ h y)^2) μ)
    (hB : Filter.Tendsto (fun n => ∫ x, (F n x - MeasureTheory.condExp m μ h x)^2 ∂μ)
      Filter.atTop (nhds (0 : ℝ))) :
    ∀ᵐ x ∂μ, ∀ ε : ℝ, 0 < ε → ∃ n : ℕ,
      ∫ y, (F n y - ∫ z, h z ∂(ProbabilityTheory.condExpKernel μ m x))^2
        ∂(ProbabilityTheory.condExpKernel μ m x) < ε := by
  -- The `m`-conditional expectations of `(F n - g)^2` are measurable representatives of the
  -- `ν_x`-integrals of `(F n - g)^2`.
  have step1 : ∀ᵐ x ∂μ, ∀ n, ∫ y, (F n y - MeasureTheory.condExp m μ h y)^2
      ∂(ProbabilityTheory.condExpKernel μ m x)
        = MeasureTheory.condExp m μ (fun y => (F n y - MeasureTheory.condExp m μ h y)^2) x := by
    rw [MeasureTheory.ae_all_iff]
    intro n
    filter_upwards [ProbabilityTheory.condExp_ae_eq_integral_condExpKernel (μ := μ) (m := m) hm
      (hFh n)] with x hx
    exact hx.symm
  -- The `L¹`-convergence of those conditional expectations gives the pointwise estimate.
  have step2 : ∀ᵐ x ∂μ, ∀ ε : ℝ, 0 < ε → ∃ n,
      MeasureTheory.condExp m μ (fun y => (F n y - MeasureTheory.condExp m μ h y)^2) x < ε := by
    refine ae_forall_pos_exists_lt_of_tendsto_integral μ
      (fun n => MeasureTheory.condExp m μ (fun y => (F n y - MeasureTheory.condExp m μ h y)^2))
      ?_ ?_ ?_
    · intro n
      exact MeasureTheory.integrable_condExp
    · rw [MeasureTheory.ae_all_iff]
      intro n
      exact MeasureTheory.condExp_nonneg (Filter.Eventually.of_forall fun y => sq_nonneg _)
    · exact hB.congr (fun n => (MeasureTheory.integral_condExp (μ := μ) hm).symm)
  -- `μ[h|m]` is `ν_x`-a.e. constant.
  have step3 : ∀ᵐ x ∂μ, MeasureTheory.condExp m μ h
      =ᵐ[ProbabilityTheory.condExpKernel μ m x] (fun _ => MeasureTheory.condExp m μ h x) :=
    ae_condExp_eq_const_condExpKernel m μ hm h hh
  -- and its value is `∫ z, h z ∂ν_x`.
  have step4 : ∀ᵐ x ∂μ, ∫ z, h z ∂(ProbabilityTheory.condExpKernel μ m x)
      = MeasureTheory.condExp m μ h x := by
    filter_upwards [ProbabilityTheory.condExp_ae_eq_integral_condExpKernel (μ := μ) (m := m) hm
      (hh.integrable (by norm_num))] with x hx
    exact hx.symm
  filter_upwards [step1, step2, step3, step4] with x hx1 hx2 hx3 hx4
  intro ε hε
  obtain ⟨n, hn⟩ := hx2 ε hε
  refine ⟨n, ?_⟩
  have heq : (fun y => (F n y - MeasureTheory.condExp m μ h x)^2)
      =ᵐ[ProbabilityTheory.condExpKernel μ m x]
      (fun y => (F n y - MeasureTheory.condExp m μ h y)^2) := by
    filter_upwards [hx3] with y hy
    rw [hy]
  rw [hx4, MeasureTheory.integral_congr_ae heq, hx1 n]
  exact hn

/-- **A.e.-in-`x` transfer of the mean ergodic statement to the conditional measures `ν_x`.**

Let `T` preserve a probability `μ` on a standard Borel space, `f ∈ L²(μ)`, and assume the `L²`
mean ergodic statement at `f` (`hB`: the Birkhoff averages `A_n f` converge to
`MeasureTheory.condExp (invariants T) μ f` in `L²(μ)`).  Then for `μ`-a.e. `x` the Birkhoff averages
of `f` approximate the *constant* `∫ z, f z ∂ν_x` arbitrarily well in `L²(ν_x)`, where
`ν_x := ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x`.

Proof sketch.  Write `m := MeasurableSpace.invariants T`, `ν_x := condExpKernel μ m x`,
`g := condExp m μ f` and `Ψ_n := condExp m μ (fun y => (A_n f y - g y)^2)`; all the functions
involved are integrable, so every `condExp` below is the ordinary one.

1. `∫ Ψ_n ∂μ = ∫ (A_n f - g)^2 ∂μ → 0` (`MeasureTheory.integral_condExp` and `hB`).
2. Since `Ψ_n ≥ 0` a.e., this forces `inf_n Ψ_n(x) = 0` for `μ`-a.e. `x`: for `k ≥ 1` the sets
   `{x | 1/k ≤ Ψ_n x}` satisfy `μ {1/k ≤ Ψ_n} ≤ k * ∫ Ψ_n → 0`, so their (decreasing in `n`)
   intersection is null by continuity from above (`tendsto_measure_iInter_atTop`), and the union
   over `k` of these null intersections is exactly `{x | inf_n Ψ_n(x) > 0}`.
3. For `μ`-a.e. `x` and every `n`, `Ψ_n(x) = ∫ y, (A_n f y - ∫ z, f z ∂ν_x)^2 ∂ν_x`:
   by `ProbabilityTheory.condExp_ae_eq_integral_condExpKernel` (applied to `f`, `(A_n f)^2`,
   `A_n f`, `g * A_n f` and `g^2`),
   `∫ (A_n f)^2 ∂ν_x = condExp m μ ((A_n f)^2) x`, `∫ A_n f ∂ν_x = condExp m μ (A_n f) x`,
   `∫ f ∂ν_x = g x` and `ν_x univ = 1`, whence
   `∫ (A_n f - g x)^2 ∂ν_x = condExp m μ ((A_n f)^2) x - 2 (g x) * condExp m μ (A_n f) x + (g x)^2`,
   while `Ψ_n(x) = condExp m μ ((A_n f)^2) x - 2 * condExp m μ (g * A_n f) x + condExp m μ (g^2) x`
   and `condExp m μ (g * A_n f) = g * condExp m μ (A_n f)`, `condExp m μ (g^2) = g^2`
   (`MeasureTheory.condExp_mul_of_stronglyMeasurable_left`, which needs
   `Integrable (g * A_n f)` — valid by Hölder since `g, A_n f ∈ L²` — and
   `MeasureTheory.stronglyMeasurable_condExp`).
4. Combining 2 and 3 gives the claim. -/
theorem ae_tendsto_birkhoff_condExpKernel {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    (μ : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ]
    (T : X → X) (hT : Measurable T) (hmp : MeasureTheory.MeasurePreserving T μ μ)
    (f : X → ℝ) (hf : MeasureTheory.MemLp f 2 μ)
    (hB : Filter.Tendsto (fun n : ℕ => ∫ x, (birkhoffAverage ℝ T f n x
        - MeasureTheory.condExp (MeasurableSpace.invariants T) μ f x)^2 ∂μ)
        Filter.atTop (nhds (0 : ℝ))) :
    ∀ᵐ x ∂μ, ∀ ε : ℝ, 0 < ε → ∃ n : ℕ,
      ∫ y, (birkhoffAverage ℝ T f n y - ∫ z, f z
          ∂(ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x))^2
        ∂(ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x) < ε := by
  have hF : ∀ n, MeasureTheory.MemLp (birkhoffAverage ℝ T f n) 2 μ :=
    fun n => memLp_birkhoffAverage μ T hmp f hf n
  -- `(A n - g)^2` is integrable for every `n`
  have hFh : ∀ n, MeasureTheory.Integrable (fun y => (birkhoffAverage ℝ T f n y
      - MeasureTheory.condExp (MeasurableSpace.invariants T) μ f y)^2) μ := by
    intro n
    have hA2 : MeasureTheory.Integrable (fun y => (birkhoffAverage ℝ T f n y)^2) μ :=
      (hF n).integrable_sq
    have hg2 : MeasureTheory.Integrable
        (fun y => (MeasureTheory.condExp (MeasurableSpace.invariants T) μ f y)^2) μ :=
      (MeasureTheory.MemLp.condExp (by norm_num) hf).integrable_sq
    have hsm : MeasureTheory.AEStronglyMeasurable (fun y => (birkhoffAverage ℝ T f n y
        - MeasureTheory.condExp (MeasurableSpace.invariants T) μ f y)^2) μ :=
      (((hF n).aestronglyMeasurable).sub
        ((MeasureTheory.MemLp.condExp (by norm_num) hf).aestronglyMeasurable)).pow 2
    refine MeasureTheory.Integrable.mono' ((hA2.const_mul 2).add (hg2.const_mul 2)) hsm ?_
    filter_upwards with y
    have hbound : (birkhoffAverage ℝ T f n y
        - MeasureTheory.condExp (MeasurableSpace.invariants T) μ f y)^2
        ≤ 2 * (birkhoffAverage ℝ T f n y)^2
          + 2 * (MeasureTheory.condExp (MeasurableSpace.invariants T) μ f y)^2 := by
      nlinarith [sq_nonneg (birkhoffAverage ℝ T f n y
        + MeasureTheory.condExp (MeasurableSpace.invariants T) μ f y)]
    rw [Pi.add_apply, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hbound
  exact ae_transfer_condExpKernel_aux (MeasurableSpace.invariants T) μ
    (MeasurableSpace.invariants_le T) (fun n => birkhoffAverage ℝ T f n) hF f hf hFh hB

end Work.EKLC6Core
