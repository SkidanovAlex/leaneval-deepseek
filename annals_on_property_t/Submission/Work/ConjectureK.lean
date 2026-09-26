import Submission.Work.FallTwoGlobal
import Submission.Work.NielsenResidual
import Submission.Work.ResidualExact
import Submission.Work.AggregateCoordinate

open Submission.Nielsen
open Submission.FreeGroupAut
open FreeGroup
set_option autoImplicit false

/-!
# Conjecture K: reduction to its residual core (KJ3 step)

**Conjecture K** (`ConjectureKStrict`, open): every balanced
(`FallTwoConfig`) configuration of half-length `k ≥ 2` admits a strict
closure move (`∃ γ ∈ AutClosure n, N (α·γ) < N α`).  `FallTwoGlobal.lean`
closed the pipeline `AggregateJunctionConjecture → ConjectureKStrict`
(unbalanced aggregate junction ⟹ attached strict move).  This module takes
the first *residual* step of the KJ3 analysis, and splits K at exactly the
residual hypothesis:

1. **Non-residual states need no balanced analysis.**  The residual
   hypothesis is `NoEndCancel` (local minimum of `N` under the four
   elementary move families), and `NielsenResidual.noEndCancel_iff_local_min`
   characterizes it: `¬ NoEndCancel α` means some single elementary move
   (`rho`/`rhoNeg`/`lam`/`lamNeg`) strictly decreases `N` —
   `nonresidual_strict_move`.

2. **Residual states have no unbalanced aggregate junction.**  In a
   residual state every adjacent junction of every image aggregate is
   *balanced* (the product shortens neither factor) — the direct
   application of `ResidualExact.junction_ge_left/right` (itself derived
   from `ResidualBalanced.noEndCancel_no_*_strict`) to the aggregate
   factors, whose coordinates are read off
   (`aggregate_factor_coordinate`) and proved distinct by the strictness
   selectors (`strict_left_coord_ne` / `strict_right_coord_ne`):
   `residual_no_unbalanced_junction`.

3. **The residual core.**  Conjecture K's only residual content is

       ConjectureKResidual n := ∀ α, NoEndCancel n α → ¬ HasK2FallTwo α

   ("a residual state carries no balanced element of half-length ≥ 2").
   *** THIS STATEMENT IS FALSE (found this session, machine counterexample):
   the `F₃` basis `[a₀a₀A₂A₁, a₁a₂a₀A₂, a₂A₀A₀A₀a₁]` is residual and has a
   confined `k = 2` balanced configuration in the aggregate of `a₁`; see
   `Submission/Status.lean`, "THE PIN `ConjectureKResidual` IS FALSE".  The
   earlier "0 residual `k ≥ 2` configurations" machine evidence was produced by
   a search helper with an early-`return []` bug (fixed), so it must be
   disregarded.***  `conjectureKResidual_implies_KStrict` closes the
   reduction: a `k ≥ 2` balanced configuration of a non-residual state is
   killed by the single elementary move of 1; of a residual state is
   impossible by `ConjectureKResidual`.

4. **KJ3 → the residual core.**  Since residual states have no unbalanced
   aggregate junction (2), the aggregate-junction conjecture
   `AggregateJunctionConjecture` (KJ3) implies `ConjectureKResidual`
   (`aggregateJunctionConjecture_implies_conjectureKResidual`).  Hence the
   chain `KJ3 ⟹ KResidual ⟹ KStrict` is the entire remaining mathematics of
   the `k ≥ 2` branch of the strict-descent pin `hF`.

All lemmas kernel-checked; axioms `[propext, Classical.choice, Quot.sound]`.
-/

namespace Submission.Nielsen

/-- Helper: a failed `rho` inequality gives a strict closure move. -/
private lemma strict_from_rho {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (i j : Fin n) (hij : i ≠ j)
    (hlt : ¬ N α ≤ N (α * rho i j hij)) :
    ∃ γ : MulAut (FreeGroup (Fin n)), γ ∈ AutClosure n ∧ N (α * γ) < N α := by
  refine ⟨rho i j hij, Subgroup.subset_closure (rho_mem_AutGen n hij), lt_of_not_ge hlt⟩

/-- Helper: a failed `rhoNeg` inequality gives a strict closure move. -/
private lemma strict_from_rhoNeg {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (i j : Fin n) (hij : i ≠ j)
    (hlt : ¬ N α ≤ N (α * rhoNeg i j hij)) :
    ∃ γ : MulAut (FreeGroup (Fin n)), γ ∈ AutClosure n ∧ N (α * γ) < N α := by
  refine ⟨rhoNeg i j hij, Subgroup.subset_closure (rhoNeg_mem_AutGen n hij), lt_of_not_ge hlt⟩

/-- Helper: a failed `lam` inequality gives a strict closure move. -/
private lemma strict_from_lam {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (i j : Fin n) (hij : i ≠ j)
    (hlt : ¬ N α ≤ N (α * lam i j hij)) :
    ∃ γ : MulAut (FreeGroup (Fin n)), γ ∈ AutClosure n ∧ N (α * γ) < N α := by
  refine ⟨lam i j hij, Subgroup.subset_closure (lam_mem_AutGen n hij), lt_of_not_ge hlt⟩

/-- Helper: a failed `lamNeg` inequality gives a strict closure move. -/
private lemma strict_from_lamNeg {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (i j : Fin n) (hij : i ≠ j)
    (hlt : ¬ N α ≤ N (α * lamNeg i j hij)) :
    ∃ γ : MulAut (FreeGroup (Fin n)), γ ∈ AutClosure n ∧ N (α * γ) < N α := by
  refine ⟨lamNeg i j hij, Subgroup.subset_closure
    (lamNeg_mem_AutGen n (i := j) (j := i) (hij.symm)), lt_of_not_ge hlt⟩

/-- **Non-residual states have a strict elementary move.**  If `α` is not
residual (`¬ NoEndCancel`), the local-minimum characterization
(`noEndCancel_iff_local_min`) yields a single elementary move
(`rho`/`rhoNeg`/`lam`/`lamNeg`) whose right composition strictly decreases
the total length `N`; the move lies in the closure (`*_mem_AutGen` +
`Subgroup.subset_closure`). -/
theorem nonresidual_strict_move {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (h : ¬ NoEndCancel n α) :
    ∃ γ : MulAut (FreeGroup (Fin n)), γ ∈ AutClosure n ∧ N (α * γ) < N α := by
  classical
  have hC : ¬ ((∀ i j (hij : i ≠ j), N α ≤ N (α * rho i j hij)) ∧
      (∀ i j (hij : i ≠ j), N α ≤ N (α * rhoNeg i j hij)) ∧
      (∀ i j (hij : i ≠ j), N α ≤ N (α * lam i j hij)) ∧
      (∀ i j (hij : i ≠ j), N α ≤ N (α * lamNeg i j hij))) := by
    intro hC
    exact h ((noEndCancel_iff_local_min n α).mpr hC)
  by_cases h1 : ∀ i j (hij : i ≠ j), N α ≤ N (α * rho i j hij)
  · by_cases h2 : ∀ i j (hij : i ≠ j), N α ≤ N (α * rhoNeg i j hij)
    · by_cases h3 : ∀ i j (hij : i ≠ j), N α ≤ N (α * lam i j hij)
      · by_cases h4 : ∀ i j (hij : i ≠ j), N α ≤ N (α * lamNeg i j hij)
        · exact False.elim (hC ⟨h1, h2, h3, h4⟩)
        · -- lamNeg family fails
          rcases (Classical.not_forall.mp h4) with ⟨i, hi⟩
          rcases (Classical.not_forall.mp hi) with ⟨j, hj⟩
          rcases (Classical.not_forall.mp hj) with ⟨hij, hlt⟩
          exact strict_from_lamNeg α i j hij hlt
      · -- lam family fails
        rcases (Classical.not_forall.mp h3) with ⟨i, hi⟩
        rcases (Classical.not_forall.mp hi) with ⟨j, hj⟩
        rcases (Classical.not_forall.mp hj) with ⟨hij, hlt⟩
        exact strict_from_lam α i j hij hlt
    · -- rhoNeg family fails
      rcases (Classical.not_forall.mp h2) with ⟨i, hi⟩
      rcases (Classical.not_forall.mp hi) with ⟨j, hj⟩
      rcases (Classical.not_forall.mp hj) with ⟨hij, hlt⟩
      exact strict_from_rhoNeg α i j hij hlt
  · -- rho family fails
    rcases (Classical.not_forall.mp h1) with ⟨i, hi⟩
    rcases (Classical.not_forall.mp hi) with ⟨j, hj⟩
    rcases (Classical.not_forall.mp hj) with ⟨hij, hlt⟩
    exact strict_from_rho α i j hij hlt

/-- **Residual states have no unbalanced aggregate junction.**  In a
residual (`NoEndCancel`) state, for every generator `a_m` and every adjacent
pair of factors of its image aggregate, the junction product shortens
neither factor — `ResidualExact.junction_ge_left/right` applied to the two
factors (coordinates read off by `aggregate_factor_coordinate`, distinct by
the strictness selectors `strict_left_coord_ne`/`strict_right_coord_ne`). -/
theorem residual_no_unbalanced_junction {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (hres : NoEndCancel n α) :
    ¬ HasUnbalancedAggregateJunction α := by
  classical
  intro h
  rcases h with ⟨m, t, ht, ht1, hL | hR⟩
  · -- left factor shortened at the (t, t+1) junction
    let es : List (FreeGroup (Fin n)) := imageAggregate α m
    have himg : ImageAggregate α es := by
      dsimp [es]
      exact imageAggregate_isImageAggregate α m
    have hred : SystemReduced es := by
      dsimp [es]
      exact SystemReduced_imageAggregate α m
    have het : t < es.length := by
      dsimp [es]
      exact ht
    have het1 : t + 1 < es.length := by
      dsimp [es]
      exact ht1
    have hstrict : FreeGroup.norm (es[t] * es[t + 1]) < FreeGroup.norm es[t] := by
      simpa [es] using hL
    rcases aggregate_factor_coordinate α es himg het with ⟨p, hp⟩
    rcases aggregate_factor_coordinate α es himg het1 with ⟨q, hq⟩
    have hpq : p ≠ q := strict_left_coord_ne α es hred het1 (by omega) (by omega) hp hq
      (by simpa [show (t + 1) - 1 = t by omega] using hstrict)
    have hge : FreeGroup.norm es[t] ≤ FreeGroup.norm (es[t] * es[t + 1]) :=
      junction_ge_left α hres hpq hp hq
    exact (not_lt_of_ge hge) hstrict
  · -- right factor shortened at the (t, t+1) junction
    let es : List (FreeGroup (Fin n)) := imageAggregate α m
    have himg : ImageAggregate α es := by
      dsimp [es]
      exact imageAggregate_isImageAggregate α m
    have hred : SystemReduced es := by
      dsimp [es]
      exact SystemReduced_imageAggregate α m
    have het : t < es.length := by
      dsimp [es]
      exact ht
    have het1 : t + 1 < es.length := by
      dsimp [es]
      exact ht1
    have hstrict : FreeGroup.norm (es[t] * es[t + 1]) < FreeGroup.norm es[t + 1] := by
      simpa [es] using hR
    rcases aggregate_factor_coordinate α es himg het with ⟨p, hp⟩
    rcases aggregate_factor_coordinate α es himg het1 with ⟨q, hq⟩
    have hpq : p ≠ q := strict_right_coord_ne α es hred het het1 hp hq hstrict
    have hge : FreeGroup.norm es[t + 1] ≤ FreeGroup.norm (es[t] * es[t + 1]) :=
      junction_ge_right α hres hpq hp hq
    exact (not_lt_of_ge hge) hstrict

/-- **The residual core of Conjecture K (FALSE).**  A residual (`NoEndCancel`)
state carries no `k ≥ 2` balanced configuration (`HasK2FallTwo`).  *This
predicate is false*: `ConjectureKResidual 3` is refuted by the residual `F₃`
basis `[a₀a₀A₂A₁, a₁a₂a₀A₂, a₂A₀A₀A₀a₁]`, whose `a₁`-aggregate `[w₀,w₁,w₂]`
has the confined balanced middle factor `w₁ = (a₁a₂)++(a₀A₂)` with exact seams
and excesses `≥ 2`; see `Submission/Status.lean` (the machine searches that
suggested otherwise used a buggy detector that discarded configurations
whenever some inverse word was not found).  Theorems below that *assume* this
predicate stay valid as conditionals; the predicate is not provable. -/
def ConjectureKResidual (n : ℕ) : Prop :=
  ∀ α : MulAut (FreeGroup (Fin n)), NoEndCancel n α → ¬ HasK2FallTwo α

/-- **Conjecture K reduces to its residual core.**  If no residual state
carries a `k ≥ 2` balanced configuration, then every `k ≥ 2` balanced
configuration has a strict closure move: a non-residual state is killed by
the single elementary move of `nonresidual_strict_move`; a residual state is
impossible by the residual core. -/
theorem conjectureKResidual_implies_KStrict (n : ℕ)
    (hres : ConjectureKResidual n) : ConjectureKStrict (n := n) := by
  intro α hK2
  classical
  by_cases hnec : NoEndCancel n α
  · -- residual: the residual core contradicts the k ≥ 2 configuration
    exact False.elim (hres α hnec hK2)
  · -- non-residual: a single elementary move strictly decreases N
    exact nonresidual_strict_move α hnec

/-- **KJ3 implies the residual core.**  Residual states have no unbalanced
aggregate junction (`residual_no_unbalanced_junction`), so the
aggregate-junction conjecture (`AggregateJunctionConjecture`, KJ3) forces
every `k ≥ 2` balanced configuration out of the residual class. -/
theorem aggregateJunctionConjecture_implies_conjectureKResidual (n : ℕ)
    (hKJ3 : AggregateJunctionConjecture (n := n)) : ConjectureKResidual n := by
  intro α hnec hK2
  exact residual_no_unbalanced_junction α hnec (hKJ3 α hK2)

end Submission.Nielsen
