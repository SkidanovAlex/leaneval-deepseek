/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/EpsEngine/PerzAssemblyGen.lean` — the per-`z` slab assembly, generic in
# the level `k`

The per-`z` energy bound of the level-`k` `ℋ`-integrand,

  `∫_θ HkIntegrand α k f z θ ≤ C (1 + w z ^ 2) (1 + |f|_{ℋ^{k+2}})^2`   `(z ∈ Iz)`,

is, for every level, the sum of two independent halves:

* the **pure `z`-slots** `(D_z^i f · w z / sin(2θ)^{η/2})²`, `i ≤ k`, estimated by the radial
  window bound against `HkIntegrand α (k+2)` (the two extra derivatives of `HkMem α (k+2)` buy
  the Hardy gain `D_z^{i+1}` and the far-window average);
* the **mixed slots** `(D_z^jD_θ^if · W)²`, `1 ≤ i`, `i + j ≤ k`, estimated by the angular
  window bound (`sliceAng`) against `HkSq α (k+2)`.

This module performs the assembly *once*, as a function of the two halves and of the level: the
only `k`-dependence is the range `Finset.range (k+1)` of the slots and the cardinal constants
`(k+1)`, `(k+1)²` of the two finite sums.  Instantiated at `k = 4` it reproduces the delivered
`Work.FTS.EpsEngine.HkIntegrand_perz_le_noTraces`; instantiated at `k = 6` it is the assembly of
`Work.FTS.EpsEngine.HkIntegrand_perz_six_noTraces`.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS.GalBasis.cc.intervalIntegrable_mixed_div_sin
import Submission.Work.Spaces.aesm_HkIntegrand_quad

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EpsEngine

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Integrability of the level-`k` summands -/

/-- A finite sum of integrable functions is integrable. -/
private lemma integrable_finsetSum_perz {ι : Type*} (s : Finset ι) {g : ι → ℝ → ℝ}
    {μ : MeasureTheory.Measure ℝ} (h : ∀ i ∈ s, MeasureTheory.Integrable (g i) μ) :
    MeasureTheory.Integrable (fun x => ∑ i ∈ s, g i x) μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using MeasureTheory.integrable_zero ℝ ℝ μ
  | insert a s ha ih =>
      have h1 : MeasureTheory.Integrable (g a) μ := h a (Finset.mem_insert_self a s)
      have h2 : MeasureTheory.Integrable (fun x => ∑ i ∈ s, g i x) μ :=
        ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
      rw [show (fun x : ℝ => ∑ i ∈ insert a s, g i x)
          = fun x : ℝ => g a x + ∑ i ∈ s, g i x from by
        funext x; rw [Finset.sum_insert ha]]
      exact h1.add h2

/-- The `if`-guarded mixed slot of the level-`k` integrand is integrable on the angular slice,
from the level-`k` honesty of the datum. -/
private lemma integrableOn_if_mixed_perz (α : ℝ) (k : ℕ) {f : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α k f)
    (i j : ℕ) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ : ℝ => (if 1 ≤ i ∧ i + j ≤ k
        then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
      Work.Spaces.Iθ := by
  by_cases h : 1 ≤ i ∧ i + j ≤ k
  · rw [show (fun θ : ℝ => (if 1 ≤ i ∧ i + j ≤ k
        then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
        = fun θ : ℝ => (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 from by
      funext θ; rw [if_pos h]]
    refine MeasureTheory.Integrable.mono' (hmem.1 z (Set.mem_Ici.mpr hz.le))
      (Work.FTS.GalBasis.cc.aesm_slice_mixed_Wt_sq hF α j i hz) ?_
    rw [MeasureTheory.ae_restrict_iff' (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)]
    exact Filter.Eventually.of_forall fun θ _ => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact Work.Spaces.sq_le_HkIntegrand_mixed α k f z θ i j h.1 h.2
  · rw [show (fun θ : ℝ => (if 1 ≤ i ∧ i + j ≤ k
        then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
        = fun _ : ℝ => (0 : ℝ) from by
      funext θ; rw [if_neg h]]
    exact MeasureTheory.integrableOn_zero

/-! ## The generic assembly -/

/-- **The per-`z` slab assembly, generic in the level.**  Given the two half-bounds — the
`z`-slots (`Cz`) and the mixed slots (`Cm`) of the level-`k` integrand, both at honesty
`ℋ^{k+2}` — the level-`k` per-`z` energy bound holds with constant `(k+1)·Cz + (k+1)²·Cm`. -/
theorem HkIntegrand_perz_le_of_halves (k : ℕ) (Cz Cm : ℝ) (hCz : 0 < Cz) (hCm : 0 < Cm)
    (hzslot : ∀ (α : ℝ), α ∈ Set.Ioc 0 1 → ∀ {f : ℝ → ℝ → ℝ},
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α (k + 2) f →
      ∀ i : ℕ, i ≤ k → ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ Cz * (1 + (Work.Spaces.w z) ^ 2) * (1 + Work.Spaces.HkNorm α (k + 2) f) ^ 2)
    (hmixed : ∀ (α : ℝ), α ∈ Set.Ioc 0 1 → ∀ {f : ℝ → ℝ → ℝ},
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α (k + 2) f →
      ∀ (i j : ℕ), 1 ≤ i → i + j ≤ k → ∀ {z : ℝ}, 0 < z →
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2)
        ≤ Cm * (1 + (Work.Spaces.w z) ^ 2) * Work.Spaces.HkSq α (k + 2) f) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), α ∈ Set.Ioc 0 1 → ∀ {f : ℝ → ℝ → ℝ},
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α (k + 2) f →
      ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
        ≤ C * (1 + (Work.Spaces.w z) ^ 2) * (1 + Work.Spaces.HkNorm α (k + 2) f) ^ 2 := by
  refine ⟨((k + 1 : ℕ) : ℝ) * Cz + ((k + 1 : ℕ) : ℝ) ^ 2 * Cm, by positivity, ?_⟩
  intro α hα f hF hmem z hz
  obtain ⟨hα0, hα1⟩ := hα
  have hαI : α ∈ Set.Ioc 0 1 := ⟨hα0, hα1⟩
  have hmemk : Work.Spaces.HkMem α k f :=
    Work.FTS.OpenPkg.HkMem_mono_open hF k (by omega) hmem
  have hXsq : Work.Spaces.HkSq α (k + 2) f
      ≤ (1 + Work.Spaces.HkNorm α (k + 2) f) ^ 2 := by
    have h2 : 0 ≤ Work.Spaces.HkSq α (k + 2) f := Work.Spaces.HkSq_nonneg α (k + 2) f
    have h3 : 0 ≤ Work.Spaces.HkNorm α (k + 2) f := Work.Spaces.HkNorm_nonneg α (k + 2) f
    have h4 : Work.Spaces.HkNorm α (k + 2) f = Real.sqrt (Work.Spaces.HkSq α (k + 2) f) := rfl
    rw [h4]
    nlinarith [Real.sq_sqrt h2, h3, h2]
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · -- the degenerate case `z = 0`
    subst hz0
    have hzero : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f 0 θ) = 0 := by
      rw [show (fun θ : ℝ => Work.Spaces.HkIntegrand α k f 0 θ) = fun _ => (0 : ℝ) from
        funext fun θ => Work.Spaces.HkIntegrand_zero_z α k f θ]
      simp
    rw [hzero]
    have hw0 : (Work.Spaces.w 0) ^ 2 = 0 := by rw [Work.Spaces.w]; norm_num
    rw [hw0]
    have hX0 : 0 ≤ Work.Spaces.HkNorm α (k + 2) f := Work.Spaces.HkNorm_nonneg α (k + 2) f
    have hcoef : 0 < ((k + 1 : ℕ) : ℝ) * Cz + ((k + 1 : ℕ) : ℝ) ^ 2 * Cm := by positivity
    nlinarith [hX0, sq_nonneg (1 + Work.Spaces.HkNorm α (k + 2) f)]
  · -- the main case `z > 0`
    have hPint : MeasureTheory.Integrable
        (fun θ : ℝ => ∑ i ∈ Finset.range (k + 1), (Work.Spaces.DzIter i f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      integrable_finsetSum_perz _ (fun i hi => Work.FTS.EllipticEst.integrableOn_zSummand α k hF
        hmemk i (by rw [Finset.mem_range] at hi; omega) (Set.mem_Ici.mpr hzpos.le))
    have hMint : MeasureTheory.Integrable
        (fun θ : ℝ => ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k
            then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      integrable_finsetSum_perz _
        (fun i _ => integrable_finsetSum_perz _
          (fun j _ => integrableOn_if_mixed_perz α k hF hmemk i j hzpos))
    have hdef : (fun θ : ℝ => Work.Spaces.HkIntegrand α k f z θ)
        = fun θ : ℝ => (∑ i ∈ Finset.range (k + 1), (Work.Spaces.DzIter i f z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
              (if 1 ≤ i ∧ i + j ≤ k
                then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) := by
      funext θ; rw [Work.Spaces.HkIntegrand]
    rw [hdef, MeasureTheory.integral_add hPint hMint]
    -- the bound for the pure-`z` part
    have hPbound : (∫ θ in Work.Spaces.Iθ, ∑ i ∈ Finset.range (k + 1),
          (Work.Spaces.DzIter i f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ ((k + 1 : ℕ) : ℝ) * (Cz * (1 + (Work.Spaces.w z) ^ 2)
            * (1 + Work.Spaces.HkNorm α (k + 2) f) ^ 2) := by
      rw [MeasureTheory.integral_finsetSum (s := Finset.range (k + 1)) (hf := fun i hi =>
        Work.FTS.EllipticEst.integrableOn_zSummand α k hF hmemk i
          (by rw [Finset.mem_range] at hi; omega) (Set.mem_Ici.mpr hzpos.le))]
      calc ∑ i ∈ Finset.range (k + 1), (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          ≤ ∑ _i ∈ Finset.range (k + 1), (Cz * (1 + (Work.Spaces.w z) ^ 2)
              * (1 + Work.Spaces.HkNorm α (k + 2) f) ^ 2) :=
            Finset.sum_le_sum fun i hi => hzslot α hαI hF hmem i
              (by rw [Finset.mem_range] at hi; omega) z hz
        _ = ((k + 1 : ℕ) : ℝ) * (Cz * (1 + (Work.Spaces.w z) ^ 2)
              * (1 + Work.Spaces.HkNorm α (k + 2) f) ^ 2) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    -- the bound for the mixed part
    have hMbound : (∫ θ in Work.Spaces.Iθ, ∑ i ∈ Finset.range (k + 1),
          ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k
            then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
        ≤ ((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) * (Cm * (1 + (Work.Spaces.w z) ^ 2)
            * Work.Spaces.HkSq α (k + 2) f)) := by
      rw [MeasureTheory.integral_finsetSum (s := Finset.range (k + 1)) (hf := fun i _ =>
        integrable_finsetSum_perz _
          (fun j _ => integrableOn_if_mixed_perz α k hF hmemk i j hzpos))]
      calc ∑ i ∈ Finset.range (k + 1), (∫ θ in Work.Spaces.Iθ, ∑ j ∈ Finset.range (k + 1),
              (if 1 ≤ i ∧ i + j ≤ k
                then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
          ≤ ∑ _i ∈ Finset.range (k + 1), (((k + 1 : ℕ) : ℝ) * (Cm * (1 + (Work.Spaces.w z) ^ 2)
              * Work.Spaces.HkSq α (k + 2) f)) := by
            refine Finset.sum_le_sum fun i _ => ?_
            rw [MeasureTheory.integral_finsetSum (s := Finset.range (k + 1)) (hf := fun j _ =>
              integrableOn_if_mixed_perz α k hF hmemk i j hzpos)]
            calc ∑ j ∈ Finset.range (k + 1), (∫ θ in Work.Spaces.Iθ,
                    (if 1 ≤ i ∧ i + j ≤ k
                      then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
                ≤ ∑ _j ∈ Finset.range (k + 1), (Cm * (1 + (Work.Spaces.w z) ^ 2)
                    * Work.Spaces.HkSq α (k + 2) f) := by
                  refine Finset.sum_le_sum fun j _ => ?_
                  by_cases hij : 1 ≤ i ∧ i + j ≤ k
                  · simp only [if_pos hij]
                    exact hmixed α hαI hF hmem i j hij.1 (by omega) hzpos
                  · simp only [if_neg hij]
                    have h1 : 0 ≤ Cm * (1 + (Work.Spaces.w z) ^ 2)
                        * Work.Spaces.HkSq α (k + 2) f := by
                      have := Work.Spaces.HkSq_nonneg α (k + 2) f
                      positivity
                    simpa using h1
              _ = ((k + 1 : ℕ) : ℝ) * (Cm * (1 + (Work.Spaces.w z) ^ 2)
                    * Work.Spaces.HkSq α (k + 2) f) := by
                  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        _ = ((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) * (Cm * (1 + (Work.Spaces.w z) ^ 2)
              * Work.Spaces.HkSq α (k + 2) f)) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    refine le_trans (add_le_add hPbound hMbound) ?_
    have hYsq : Work.Spaces.HkSq α (k + 2) f
        ≤ (1 + Work.Spaces.HkNorm α (k + 2) f) ^ 2 := hXsq
    have hstep : ((k + 1 : ℕ) : ℝ) * (Cm * (1 + (Work.Spaces.w z) ^ 2)
          * Work.Spaces.HkSq α (k + 2) f)
        ≤ ((k + 1 : ℕ) : ℝ) * (Cm * (1 + (Work.Spaces.w z) ^ 2)
          * (1 + Work.Spaces.HkNorm α (k + 2) f) ^ 2) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact mul_le_mul_of_nonneg_left hYsq (by positivity)
    have hsum : ((k + 1 : ℕ) : ℝ) * (Cz * (1 + (Work.Spaces.w z) ^ 2)
          * (1 + Work.Spaces.HkNorm α (k + 2) f) ^ 2)
        + ((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) * (Cm * (1 + (Work.Spaces.w z) ^ 2)
          * (1 + Work.Spaces.HkNorm α (k + 2) f) ^ 2))
        = (((k + 1 : ℕ) : ℝ) * Cz + ((k + 1 : ℕ) : ℝ) ^ 2 * Cm)
          * (1 + (Work.Spaces.w z) ^ 2) * (1 + Work.Spaces.HkNorm α (k + 2) f) ^ 2 := by
      ring
    have hstep2 : ((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) * (Cm * (1 + (Work.Spaces.w z) ^ 2)
          * Work.Spaces.HkSq α (k + 2) f))
        ≤ ((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) * (Cm * (1 + (Work.Spaces.w z) ^ 2)
          * (1 + Work.Spaces.HkNorm α (k + 2) f) ^ 2)) :=
      mul_le_mul_of_nonneg_left hstep (by positivity)
    refine le_trans (add_le_add le_rfl hstep2) ?_
    rw [hsum]

end Work.FTS.EpsEngine
