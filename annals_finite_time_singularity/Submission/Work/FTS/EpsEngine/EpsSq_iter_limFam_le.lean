/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/EpsEngine/EpsSq_iter_limFam_le.lean`

**The geometric tail bound of the Picard iteration of the `ε`-scheme.**  Assume that every
*difference of two Picard iterates* is a member of the weighted space `X = (EpsMem, EpsSq)` of
`StrongEps/EpsSpace.lean` with the geometric size bound

  `EpsSq α (slice (iter M) τ − slice (iter K) τ) ≤ q ^ (K + 1)`   (`1 ≤ K ≤ M`, `τ ∈ [0,δ]`),

and that the iterates converge pointwise to the limit family `limFam F h₀` on the open quadrant.
Then the difference of the `N`-th iterate from the limit is in `X` with size `≤ q ^ N`: the tail
bound needed to identify `limFam` with the limit of the Picard curves in the weighted metric.

The mathematics is:

* `slice (iter F h₀ (m + N)) τ − slice (iter F h₀ N) τ` is a sequence of profiles with
  `EpsSq ≤ q ^ (N+1)` (`hBK`) converging, a.e. on the domain, to
  `slice (limFam F h₀) τ − slice (iter F h₀ N) τ` (`hconv`, restricted to the a.e. open quadrant
  by `EpsLocalPStar.ae_of_forall_open`);
* Fatou's lemma then bounds the `EpsSq` of that limit by `q ^ (N+1)` and yields its `EpsMem`;
  this is the delegated measure-theoretic step `EpsMem_and_EpsSq_le_of_ae_tendsto_mem`;
* finally `q ^ (N+1) ≤ q ^ N` for `0 ≤ q ≤ 1`, and the difference is negated/symmetrised to match
  the requested orientation (`EpsMem_neg2`, `EpsSq_sub_comm`).

Everything is `sorry`-free.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Submission.Work.FTS.EpsEngine.IterContMeas
import Submission.Work.FTS.EpsEngine.EpsMem_and_EpsSq_le_of_ae_tendsto_mem

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology ENNReal
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.StrongEps.EpsLocalPStar (iter limFam)

namespace Work.FTS.EpsEngine

set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem EpsSq_iter_limFam_le {α q δ : ℝ} {F : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {h₀ : Work.FTS.Galerkin.Fn}
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hconv : ∀ τ : ℝ, τ ∈ Set.Icc 0 δ → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Filter.Tendsto (fun N : ℕ => Work.FTS.Galerkin.slice
          (Work.FTS.StrongEps.EpsLocalPStar.iter F h₀ N) τ z θ)
        Filter.atTop (nhds (Work.FTS.Galerkin.slice
          (Work.FTS.StrongEps.EpsLocalPStar.limFam F h₀) τ z θ)))
    (hBK : ∀ M K : ℕ, 1 ≤ K → K ≤ M → ∀ τ : ℝ, τ ∈ Set.Icc 0 δ →
      Work.FTS.StrongEps.EpsMem α (fun z θ =>
        Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.iter F h₀ M) τ z θ
          - Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.iter F h₀ K) τ z θ) ∧
      Work.FTS.StrongEps.EpsSq α (fun z θ =>
        Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.iter F h₀ M) τ z θ
          - Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.iter F h₀ K) τ z θ)
        ≤ q ^ (K + 1)) :
    ∀ N : ℕ, 1 ≤ N → ∀ τ : ℝ, τ ∈ Set.Icc 0 δ →
      Work.FTS.StrongEps.EpsMem α (fun z θ =>
        Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.iter F h₀ N) τ z θ
          - Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.limFam F h₀) τ z θ) ∧
      Work.FTS.StrongEps.EpsSq α (fun z θ =>
        Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.iter F h₀ N) τ z θ
          - Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.limFam F h₀) τ z θ)
        ≤ q ^ N := by
  intro N hN τ hτ
  -- The Fatou step: the differences `slice (iter (m+N)) − slice (iter N)` converge a.e. to
  -- `slice (limFam) − slice (iter N)`, and all of them have `EpsSq ≤ q ^ (N+1)`.
  obtain ⟨hmemL, hsqL⟩ := EpsMem_and_EpsSq_le_of_ae_tendsto_mem (B := q ^ (N + 1))
    (pow_nonneg hq0 (N + 1))
    (A := fun m z θ => slice (iter F h₀ (m + N)) τ z θ - slice (iter F h₀ N) τ z θ)
    (Alim := fun z θ => slice (limFam F h₀) τ z θ - slice (iter F h₀ N) τ z θ)
    (fun m => (hBK (m + N) N hN (Nat.le_add_left N m) τ hτ).1)
    (fun m => (hBK (m + N) N hN (Nat.le_add_left N m) τ hτ).2)
    (Work.FTS.StrongEps.EpsLocalPStar.ae_of_forall_open (fun z hz θ hθ0 hθ1 =>
      ((hconv τ hτ z θ hz hθ0 hθ1).comp (tendsto_add_atTop_nat N)).sub tendsto_const_nhds))
  -- `q ^ (N+1) ≤ q ^ N` for `0 ≤ q ≤ 1`.
  have hpow : q ^ (N + 1) ≤ q ^ N :=
    mul_le_of_le_one_right (pow_nonneg hq0 N) hq1.le
  refine ⟨?_, ?_⟩
  · -- `EpsMem` is invariant under negation, and the two differences are negatives of each other.
    refine Work.FTS.StrongEps.EpsLocalPStar.EpsMem_congr_ae
      (f := fun z θ => -(slice (limFam F h₀) τ z θ - slice (iter F h₀ N) τ z θ)) ?_
      (Work.FTS.StrongEps.EpsLocalPStar.EpsMem_neg2 hmemL)
    filter_upwards with p
    ring
  · -- `EpsSq` is invariant under swapping the two entries of a difference.
    rw [Work.FTS.StrongEps.EpsLocalPStar.EpsSq_sub_comm]
    exact le_trans hsqL hpow

end Work.FTS.EpsEngine
