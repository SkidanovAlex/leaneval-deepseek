/-
Copyright: work module for the Elgindi finite-time singularity project.

# The `α`-uniform `ℋ⁴`-bound for the clean operator `𝓛̂ = Lhat`

`Work.FTS.GalFields.Norm.HkSq_Lhat_le_uniform` is the **α-uniform** companion of
`Work.FTS.StrongPersist.H6Aux.HkSq_Lhat_le`: the clean operator `Lhat = 𝓛 − Transport`
(`Work.FTS.CoercivityFix.Basic`) satisfies

  `HkSq α 4 (Lhat g) ≤ C · HkSq α 5 g`

for **one** constant `C` valid for *every* `α > 0` (and every `SmoothOpen` `g ∈ ℋ⁵`).

## Why uniformity is free here

The delivered proof chain of `HkSq_Lhat_le α hα m` already produces a constant that is a
closed-form expression in `m` alone:

* the pointwise integrand domination `Lhat_integrand_le α hα m` is assembled from
  * the multiplier estimate `L3Aux.zmul_open` (constant `zmulConst m·(1+K)²`, independent
    of `α`; the `α` is carried along only through the two weights of `HkIntegrand`, which are
    the same on both sides),
  * the index shifts `L3Aux.HkIntegrand_mixed_shift`, whose constant is `1`,
  * the subadditivity/homogeneity of the integrand (`HkIntegrand_add_le_domain`,
    `HkIntegrand_const_mul`) and the monotonicity `HkIntegrand_le_of_le`;

  the only role of `hα : 0 < α` in that proof is to supply the hypothesis `α > 0` of the shift
  lemmas (which is needed because `HkIntegrand_mixed_shift` compares the two weights
  `w/sin^{η/2} ≤ Wt α` through `η ≤ γ(α)`), never to produce a constant;
* the extension to the closed quadrant `HkIntegrand_le_Izθ_of_Ioo` and the final integration
  `MeasureTheory.integral_mono_of_nonneg` introduce no `α`-dependence either.

So the same proof, with the quantifier over `α` *inside* the `∃ C`, gives a single constant.
That is what this file does: `Lhat_integrand_le_uniform` (the pointwise bound, uniform in
`α`), its closed-quadrant form, the integrated form `HkSq_Lhat_le_uniform_aux`, and finally
the requested theorem at level `4 ↗ 5`.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.H6Aux.LhatFacts
import Submission.Work.FTS.StrongPersist.H6Aux.Lhat_integrand_le
import Submission.Work.FTS.StrongPersist.L3Aux.ZmulBound
import Submission.Work.FTS.StrongPersist.L3Aux.ZmulCore

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalFields.Norm

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The pointwise integrand bound, uniform in `α` -/

/-- **The `ℋ^m`-integrand of `𝓛̂g` is dominated by the `ℋ^{m+1}`-integrand of `g`, with a
constant independent of `α`.**  This is `Lhat_integrand_le` with the quantifier over `α`
moved inside the existential: the proof is verbatim the same, because every ingredient of it
carries a constant that does not mention `α`. -/
theorem Lhat_integrand_le_uniform (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → ∀ g : ℝ → ℝ → ℝ,
      Work.FTS.EllipticEst.SmoothOpen g →
      ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        Work.Spaces.HkIntegrand α m (Work.FTS.CoercivityFix.Lhat g) z θ
          ≤ C * Work.Spaces.HkIntegrand α (m + 1) g z θ := by
  obtain ⟨K, hKpos, hKb⟩ := Work.FTS.StrongPersist.H6Aux.three_div_zop_bound m
  have hK : (0 : ℝ) ≤ K := hKpos.le
  refine ⟨8 * (Work.FTS.StrongPersist.L3Aux.zmulConst m * (1 + K) ^ 2) + 9, ?_, ?_⟩
  · have h1 : 0 ≤ Work.FTS.StrongPersist.L3Aux.zmulConst m * (1 + K) ^ 2 :=
      mul_nonneg (Work.FTS.StrongPersist.L3Aux.zmulConst_pos m).le (sq_nonneg _)
    linarith
  · intro α hα g hg z hz θ hθ
    have hzIz : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr (le_of_lt hz)
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hZnn : 0 ≤ Work.FTS.StrongPersist.L3Aux.zmulConst m * (1 + K) ^ 2 :=
      mul_nonneg (Work.FTS.StrongPersist.L3Aux.zmulConst_pos m).le (sq_nonneg _)
    have hRnn : 0 ≤ Work.Spaces.HkIntegrand α (m + 1) g z θ :=
      Work.Spaces.HkIntegrand_nonneg α (m + 1) g z θ
    have hφsm : ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => 3 / (1 + z))
        (Set.Ioi (-1)) :=
      contDiffOn_iff_forall_nat_le.mpr (fun k _ => Work.FTS.FinalClock.contDiffOn_phiThree k)
    -- the multiplier estimate for `φ(z) = 3/(1+z)`, for an arbitrary `SmoothOpen` factor
    have hmul (X : ℝ → ℝ → ℝ) (hX : Work.FTS.EllipticEst.SmoothOpen X) :
        Work.Spaces.HkIntegrand α m (fun z θ => (fun z : ℝ => 3 / (1 + z)) z * X z θ) z θ
          ≤ (Work.FTS.StrongPersist.L3Aux.zmulConst m * (1 + K) ^ 2)
              * Work.Spaces.HkIntegrand α m X z θ :=
      Work.FTS.StrongPersist.L3Aux.zmul_open α m (fun z : ℝ => 3 / (1 + z)) X hK hKb hφsm hX
        z hz θ hθ
    -- the index shifts
    have hshiftZ : Work.Spaces.HkIntegrand α m (Work.Spaces.Dz g) z θ
        ≤ Work.Spaces.HkIntegrand α (m + 1) g z θ := by
      have h := Work.FTS.StrongPersist.L3Aux.HkIntegrand_mixed_shift α hα m 0 1 hg z hzIz θ hθI
      simpa only [Work.Spaces.mixed_zero_right, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero,
        Nat.reduceAdd] using h
    have hshiftT : Work.Spaces.HkIntegrand α m (Work.Spaces.Dth g) z θ
        ≤ Work.Spaces.HkIntegrand α (m + 1) g z θ := by
      have h := Work.FTS.StrongPersist.L3Aux.HkIntegrand_mixed_shift α hα m 1 0 hg z hzIz θ hθI
      simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero,
        Nat.reduceAdd, Nat.add_zero] using h
    have hmono : Work.Spaces.HkIntegrand α m g z θ ≤ Work.Spaces.HkIntegrand α (m + 1) g z θ :=
      Work.FTS.StrongPersist.HkIntegrand_le_of_le α (Nat.le_succ m) g z θ
    -- smoothness of the three new summands of the decomposition
    have hφopen : Work.FTS.EllipticEst.SmoothOpen (fun z θ : ℝ => (fun z : ℝ => 3 / (1 + z)) z) :=
      Work.FTS.StrongPersist.linMem_radial hφsm
    have hBsm : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => (-(2 / 3)) * ((fun z : ℝ => 3 / (1 + z)) z * g z θ)) :=
      Work.FTS.StrongPersist.linMem_const_mul (-(2 / 3))
        (Work.FTS.StrongPersist.linMem_mul hφopen hg)
    have hDsm : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => (-1) * ((fun z : ℝ => 3 / (1 + z)) z * Work.Spaces.Dth g z θ)) :=
      Work.FTS.StrongPersist.linMem_const_mul (-1)
        (Work.FTS.StrongPersist.linMem_mul hφopen hg.Dth)
    -- the bound for each of the three summands
    have hA : Work.Spaces.HkIntegrand α m (fun z θ => g z θ + Work.Spaces.Dz g z θ) z θ
        ≤ 4 * Work.Spaces.HkIntegrand α (m + 1) g z θ := by
      have h := Work.FTS.EllipticEst.Cores.AlphaRateEstEllT.HkIntegrand_add_le_domain α m
        (f := g) (g := Work.Spaces.Dz g) (hg.forall m) ((hg.Dz).forall m) z hzIz θ hθI
      linarith [h, hmono, hshiftZ]
    have hB : Work.Spaces.HkIntegrand α m
        (fun z θ => (-(2 / 3)) * ((fun z : ℝ => 3 / (1 + z)) z * g z θ)) z θ
        ≤ (4 / 9) * ((Work.FTS.StrongPersist.L3Aux.zmulConst m * (1 + K) ^ 2)
            * Work.Spaces.HkIntegrand α (m + 1) g z θ) := by
      rw [Work.FTS.LocData.HkIntegrand_const_mul]
      have hsq : (-(2 / 3) : ℝ) ^ 2 = 4 / 9 := by norm_num
      rw [hsq]
      have h2 : Work.Spaces.HkIntegrand α m
            (fun z θ => (fun z : ℝ => 3 / (1 + z)) z * g z θ) z θ
          ≤ (Work.FTS.StrongPersist.L3Aux.zmulConst m * (1 + K) ^ 2)
              * Work.Spaces.HkIntegrand α (m + 1) g z θ :=
        le_trans (hmul g hg) (mul_le_mul_of_nonneg_left hmono hZnn)
      exact mul_le_mul_of_nonneg_left h2 (by norm_num)
    have hD : Work.Spaces.HkIntegrand α m
        (fun z θ => (-1) * ((fun z : ℝ => 3 / (1 + z)) z * Work.Spaces.Dth g z θ)) z θ
        ≤ (Work.FTS.StrongPersist.L3Aux.zmulConst m * (1 + K) ^ 2)
            * Work.Spaces.HkIntegrand α (m + 1) g z θ := by
      rw [Work.FTS.LocData.HkIntegrand_const_mul]
      have h2 : Work.Spaces.HkIntegrand α m
            (fun z θ => (fun z : ℝ => 3 / (1 + z)) z * Work.Spaces.Dth g z θ) z θ
          ≤ (Work.FTS.StrongPersist.L3Aux.zmulConst m * (1 + K) ^ 2)
              * Work.Spaces.HkIntegrand α (m + 1) g z θ :=
        le_trans (hmul (Work.Spaces.Dth g) hg.Dth)
          (mul_le_mul_of_nonneg_left hshiftT hZnn)
      norm_num
      exact h2
    have hBD : Work.Spaces.HkIntegrand α m
        (fun z θ => (-(2 / 3)) * ((fun z : ℝ => 3 / (1 + z)) z * g z θ)
          + (-1) * ((fun z : ℝ => 3 / (1 + z)) z * Work.Spaces.Dth g z θ)) z θ
        ≤ 2 * ((4 / 9) * ((Work.FTS.StrongPersist.L3Aux.zmulConst m * (1 + K) ^ 2)
              * Work.Spaces.HkIntegrand α (m + 1) g z θ))
          + 2 * ((Work.FTS.StrongPersist.L3Aux.zmulConst m * (1 + K) ^ 2)
              * Work.Spaces.HkIntegrand α (m + 1) g z θ) := by
      have h := Work.FTS.EllipticEst.Cores.AlphaRateEstEllT.HkIntegrand_add_le_domain α m
        (f := fun z θ => (-(2 / 3)) * ((fun z : ℝ => 3 / (1 + z)) z * g z θ))
        (g := fun z θ => (-1) * ((fun z : ℝ => 3 / (1 + z)) z * Work.Spaces.Dth g z θ))
        (hBsm.forall m) (hDsm.forall m) z hzIz θ hθI
      linarith [h, hB, hD]
    -- assemble along `𝓛̂g = (g + D_z g) + [(−2/3)·(φ g) + (−1)·(φ D_θ g)]`
    have hLhat : Work.FTS.CoercivityFix.Lhat g
        = fun z θ => (g z θ + Work.Spaces.Dz g z θ)
            + ((-(2 / 3)) * ((fun z : ℝ => 3 / (1 + z)) z * g z θ)
               + (-1) * ((fun z : ℝ => 3 / (1 + z)) z * Work.Spaces.Dth g z θ)) := by
      funext z θ
      rw [Work.FTS.CoercivityFix.Lhat_eq]
      ring
    rw [hLhat]
    have hfinal := Work.FTS.EllipticEst.Cores.AlphaRateEstEllT.HkIntegrand_add_le_domain α m
      (f := fun z θ => g z θ + Work.Spaces.Dz g z θ)
      (g := fun z θ => (-(2 / 3)) * ((fun z : ℝ => 3 / (1 + z)) z * g z θ)
        + (-1) * ((fun z : ℝ => 3 / (1 + z)) z * Work.Spaces.Dth g z θ))
      ((hg.forall m).add ((hg.Dz).forall m)) ((hBsm.forall m).add (hDsm.forall m)) z hzIz θ hθI
    have hkey : 2 * (4 * Work.Spaces.HkIntegrand α (m + 1) g z θ)
        + 2 * (2 * ((4 / 9) * ((Work.FTS.StrongPersist.L3Aux.zmulConst m * (1 + K) ^ 2)
                * Work.Spaces.HkIntegrand α (m + 1) g z θ))
          + 2 * ((Work.FTS.StrongPersist.L3Aux.zmulConst m * (1 + K) ^ 2)
              * Work.Spaces.HkIntegrand α (m + 1) g z θ))
        ≤ (8 * (Work.FTS.StrongPersist.L3Aux.zmulConst m * (1 + K) ^ 2) + 9)
            * Work.Spaces.HkIntegrand α (m + 1) g z θ := by
      nlinarith [hRnn, hZnn]
    linarith [hfinal, hA, hBD, hkey]

/-! ## The closed-quadrant form -/

/-- The closed-quadrant form of `Lhat_integrand_le_uniform`, with the same constant: the two
boundary lines `z = 0` and `sin(2θ) = 0` are trivial because both integrands vanish there. -/
theorem Lhat_HkIntegrand_le_uniform (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → ∀ g : Fn,
      Work.FTS.EllipticEst.SmoothOpen g →
        ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α m (Work.FTS.CoercivityFix.Lhat g) z θ
            ≤ C * Work.Spaces.HkIntegrand α (m + 1) g z θ := by
  obtain ⟨C, hC, h⟩ := Lhat_integrand_le_uniform m
  exact ⟨C, hC, fun α hα g hs => Work.FTS.StrongPersist.H6Aux.HkIntegrand_le_Izθ_of_Ioo
    (α := α) (m := m) (l := m + 1) (X := Work.FTS.CoercivityFix.Lhat g) (Y := g) (C := C)
    hα hC.le (h α hα g hs)⟩

/-! ## The integrated bound -/

/-- **The `α`-uniform `ℋᵐ`-bound for `𝓛̂`.**  One constant works for every `α > 0`:

  `HkSq α m (Lhat g) ≤ C · HkSq α (m+1) g`. -/
theorem HkSq_Lhat_le_uniform_aux (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → ∀ g : Fn,
      Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α (m + 1) g →
        Work.Spaces.HkSq α m (Work.FTS.CoercivityFix.Lhat g)
          ≤ C * Work.Spaces.HkSq α (m + 1) g := by
  obtain ⟨C, hC, h⟩ := Lhat_HkIntegrand_le_uniform m
  refine ⟨C, hC, fun α hα g hs hm => ?_⟩
  rw [Work.Spaces.HkSq, Work.Spaces.HkSq]
  have hout : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α m
          (Work.FTS.CoercivityFix.Lhat g) z θ)
        ≤ C * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (m + 1) g z θ) := by
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => ?_
    have hinner : (∫ θ in Work.Spaces.Iθ, C * Work.Spaces.HkIntegrand α (m + 1) g z θ)
        = C * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (m + 1) g z θ) :=
      MeasureTheory.integral_const_mul (μ := volume.restrict Work.Spaces.Iθ) C _
    rw [← hinner]
    refine MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α m
        (Work.FTS.CoercivityFix.Lhat g) z θ) ((hm.1 z hz).const_mul C) ?_
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ =>
      h α hα g hs z hz θ hθ
  refine le_trans (MeasureTheory.integral_mono_of_nonneg
    (Eventually.of_forall fun z => MeasureTheory.integral_nonneg fun θ =>
      Work.Spaces.HkIntegrand_nonneg α m (Work.FTS.CoercivityFix.Lhat g) z θ)
    (hm.2.const_mul C) hout) ?_
  exact le_of_eq (MeasureTheory.integral_const_mul (μ := volume.restrict Work.Spaces.Iz) C
    (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (m + 1) g z θ))

/-! ## The requested theorem -/

/-- **`HkSq_Lhat_le_uniform`**: the `ℋ⁴`-norm of `𝓛̂g` is bounded by a *single* constant
times the `ℋ⁵`-norm of `g`, uniformly over all `α > 0`. -/
theorem HkSq_Lhat_le_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → ∀ g : Work.FTS.Galerkin.Fn,
      Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 5 g →
        Work.Spaces.HkSq α 4 (Work.FTS.CoercivityFix.Lhat g)
          ≤ C * Work.Spaces.HkSq α 5 g := by
  obtain ⟨C, hC, h⟩ := HkSq_Lhat_le_uniform_aux 4
  exact ⟨C, hC, fun α hα g hs hm => h α hα g hs (by simpa using hm)⟩

end Work.FTS.GalFields.Norm
