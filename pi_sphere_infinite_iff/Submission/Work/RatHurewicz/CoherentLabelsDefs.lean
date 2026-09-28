import Mathlib
import Submission.Work.Serre.liftSurjectiveSerreFibration
import Submission.Work.Cohomology.Chains
import Submission.Work.Serre.Defs
import Submission.Work.Serre.E0Defs

/-!
# The scaffold shared by the labelled transfer and its proof

`Simp`, `Chn`, `qC`, `simMap`, `simChainMap`, `gen` (the singular simplices / chains of a space over
`ℚ` and the chain generator attached to a simplex) and the structure `CoherentLabels` describing a
coherently `Fin m`-labelled system of lifts of the simplices of the base of a map.  These live in
their own module so that both `Submission.Work.RatHurewicz.serre_transfer_vanishing` (the labelled
transfer consuming a `CoherentLabels`) and the proof of the crux
`Submission.Work.RatHurewicz.coherentLiftIndexedExists` (which produces one) can import them without
a cycle.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Simplicial
open scoped Simplicial

set_option maxHeartbeats 1600000

namespace Work.RatHurewicz

noncomputable section

/-- The singular `n`-simplices of a space. -/
abbrev Simp (Y : Type) [TopologicalSpace Y] (n : ℕ) : Type _ :=
  (Work.Serre.singSSet Y).obj (Opposite.op (SimplexCategory.mk n))

/-- The `ℚ`-module of singular `n`-chains of a space. -/
abbrev Chn (Y : Type) [TopologicalSpace Y] (n : ℕ) : ModuleCat ℚ :=
  ((Work.Serre.singSSet Y).chainComplex (ModuleCat.of ℚ ℚ)).X n

/-- Coefficients. -/
abbrev qC : ModuleCat ℚ := ModuleCat.of ℚ ℚ

/-- The map induced by a continuous map on the `n`-simplices of the singular simplicial sets. -/
def simMap {E X : Type} [TopologicalSpace E] [TopologicalSpace X] (f : C(E, X)) (n : ℕ) :
    Simp E n → Simp X n :=
  (TopCat.toSSet.map (TopCat.ofHom f)).app (Opposite.op (SimplexCategory.mk n))

/-- The chain map induced by a continuous map. -/
def simChainMap {E X : Type} [TopologicalSpace E] [TopologicalSpace X] (f : C(E, X)) (n : ℕ) :
    Chn E n ⟶ Chn X n :=
  (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f)) qC).f n

/-- The generator of the `n`-chains attached to a simplex. -/
def gen {Y : Type} [TopologicalSpace Y] (n : ℕ) (σ : Simp Y n) : Chn Y n :=
  ((Work.Serre.singSSet Y).ιChainComplex (R := qC) σ).hom 1

variable {m M : ℕ}

/-- A **coherently labelled system of lifts** of the simplices of the base: `u n hn σ a` is the
`a`-th lift of `σ`, and the `i`-th face of the `a`-th lift of an `(n+1)`-simplex is the
`w a`-th lift of the `i`-th face. -/
structure CoherentLabels {E X : Type} [TopologicalSpace E] [TopologicalSpace X]
    (p : C(E, X)) (m M : ℕ) where
  /-- the `a`-th lift of an `n`-simplex of the base -/
  u : ∀ (n : ℕ), n ≤ M + 1 → Simp X n → Fin m → Simp E n
  /-- the reindexing of the labels along a face -/
  w : ∀ (n : ℕ), n ≤ M → Simp X (n + 1) → (i : Fin (n + 2)) → Fin m ≃ Fin m
  /-- each chosen lift lies over its simplex -/
  lift : ∀ (n : ℕ) (hn : n ≤ M + 1) (σ : Simp X n) (a : Fin m), simMap p n (u n hn σ a) = σ
  /-- the faces of a lift are the lifts of the faces, with the labels reindexed by `w` -/
  face : ∀ (n : ℕ) (hn : n ≤ M) (σ : Simp X (n + 1)) (a : Fin m) (i : Fin (n + 2)),
    (Work.Serre.singSSet E).δ i (u (n + 1) (Nat.succ_le_succ hn) σ a)
      = u n (le_trans hn (Nat.le_succ M)) ((Work.Serre.singSSet X).δ i σ)
          (w n hn σ i a)


end

end Work.RatHurewicz
