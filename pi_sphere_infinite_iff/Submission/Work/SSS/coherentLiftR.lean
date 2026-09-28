import Mathlib
import Submission.Work.SSS.coherentLiftDefs
import Submission.Work.SSS.sigmaVert_face
import Submission.Work.SSS.singularFibration

/-!
# The "right-handed" coherent lift family of a Serre fibration

For the proof of `Work.SSS.exists_coherentLiftFamily` it is convenient to work with the
tensor product in the order `sSing (fibre p b') ⊗ Δ[n]` rather than `Δ[n] ⊗ sSing (fibre p b')`:
in that order the internal-hom adjunction `Hom(F ⊗ X, Y) ≃ Hom(X, F ⟶[SSet] Y)` lets us glue a
matching family of pieces over a horn using `SSet.horn.IsCompatible.desc`.

The two formulations are related by the braiding of the (symmetric) monoidal structure on `SSet`,
see `Work.SSS.exists_coherentLiftFamily`.

This file only contains the vocabulary; the construction of the family is in
`Work.SSS.exists_coherentLiftFamily`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped Simplicial

noncomputable section

/-- The standard `n`-simplex, as a simplicial set. -/
abbrev stdSimp (n : ℕ) : SSet.{0} := (SSet.stdSimplex.obj (SimplexCategory.mk n) : SSet.{0})

/-- **The inclusion `sSing (p⁻¹b') ⟶ sSing (p⁻¹b') ⊗ Δ[n]`, `τ ↦ (τ, v₀)`** (the right-handed
version of `Work.SSS.vertIncl`). -/
def vertInclR {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (b' : B) (n : ℕ) :
    sSing (Work.StemsB.fibre p b') ⟶
      (sSing (Work.StemsB.fibre p b') ⊗ stdSimp n) :=
  CartesianMonoidalCategory.lift (𝟙 _) (SSet.const (ssetVertex n))

@[simp]
lemma vertInclR_fst {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (b' : B) (n : ℕ) :
    vertInclR p b' n ≫ SemiCartesianMonoidalCategory.fst _ _ = 𝟙 _ :=
  CartesianMonoidalCategory.lift_fst _ _

@[simp]
lemma vertInclR_snd {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (b' : B) (n : ℕ) :
    vertInclR p b' n ≫ SemiCartesianMonoidalCategory.snd _ _ =
      SSet.const (X := sSing (Work.StemsB.fibre p b')) (ssetVertex n) :=
  CartesianMonoidalCategory.lift_snd _ _

/-- **The condition on a family of pieces `F ⊗ Δ[n] ⟶ Y` indexed by the faces of the horn
`Λ[n+1,i]` for them to be the faces of a single morphism `F ⊗ Λ[n+1,i] ⟶ Y`.**

This is the "tensored" version of `SSet.horn.IsCompatible`: because the tensor product with `F`
preserves colimits, the same compatibility condition (read along the faces of the pieces) is what
is needed; see `Work.SSS.exists_hornGlue_tensor`. -/
def HornTensorCompatible {F Y : SSet.{0}} {n : ℕ} {i : Fin (n + 2)}
    (P : ∀ (j : Fin (n + 2)) (_ : j ≠ i), (F ⊗ stdSimp n) ⟶ Y) : Prop :=
  match n with
  | 0 => True
  | (n + 1) => ∀ (j k : Fin (n + 3)) (hj : j ≠ i) (hk : k ≠ i) (hjk : j < k),
      (F ◁ SSet.stdSimplex.δ (n := n) (k.pred (Fin.ne_zero_of_lt hjk))) ≫ P j hj =
      (F ◁ SSet.stdSimplex.δ (n := n) (j.castPred (Fin.ne_last_of_lt hjk))) ≫ P k hk

/-- **Level `n` data of the right-handed coherent lift family**: for every simplex
`σ : Δ[n] ⟶ Sing B` and every `b' : B` a morphism `sSing (p⁻¹b') ⊗ Δ[n] ⟶ sSing E` lifting
`snd ≫ σ` along `Sing p` and restricting to the inclusion of the fibre on the slice `v₀`.

The properties are only required for the *based* pairs `(b', σ)`, i.e. when `sigmaVert σ = b'`;
for the other pairs the value of `Φ` is irrelevant. -/
structure RLevel {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (n : ℕ) where
  /-- the lift attached to a simplex of the base -/
  Φ : ∀ (b' : B) (σ : stdSimp n ⟶ sSing B),
        (sSing (Work.StemsB.fibre p b') ⊗ stdSimp n) ⟶ sSing E
  /-- `Φ` lifts the given simplex -/
  lift : ∀ (b' : B) (σ : stdSimp n ⟶ sSing B), sigmaVert σ = b' →
      Φ b' σ ≫ sSingP p = SemiCartesianMonoidalCategory.snd _ _ ≫ σ
  /-- `Φ` restricts to the inclusion of the fibre on the `v₀`-slice -/
  vert : ∀ (b' : B) (σ : stdSimp n ⟶ sSing B), sigmaVert σ = b' →
      vertInclR p b' n ≫ Φ b' σ = sSingP (Work.StemsB.fibreIncl p b')

/-- **Coherence of two consecutive levels** of the right-handed family: the restriction of the
`(n+1)`-st level to the `i`-th face (`i ≠ 0`) is the `n`-th level of the corresponding face
simplex. -/
def RCoh {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (n : ℕ) (d : RLevel p n) (d' : RLevel p (n + 1)) : Prop :=
  ∀ (b' : B) (σ : stdSimp (n + 1) ⟶ sSing B) (_ : sigmaVert σ = b')
    (i : Fin (n + 2)) (_ : i ≠ 0) (_ : sigmaVert (SSet.stdSimplex.δ (n := n) i ≫ σ) = b'),
    (sSing (Work.StemsB.fibre p b') ◁ SSet.stdSimplex.δ (n := n) i) ≫ d'.Φ b' σ =
      d.Φ b' (SSet.stdSimplex.δ (n := n) i ≫ σ)

/-- The condition on the level `M` data which is needed to build the level `M+1` data.  For
`M = 0` it is vacuous (the horn `Λ[1,0]` has a single face); for `M = M'+1` it is the
compatibility of the pieces indexed by the faces of `Λ[M+2,0]`, restricted to the pairwise
intersections of those faces.  As for `RCoh` and `RLevel`, only the *based* simplices
`σ` (those with `sigmaVert σ = b'`) are constrained. -/
def HComp {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (M : ℕ) (D : RLevel p M) : Prop :=
  match M with
  | 0 => True
  | (M + 1) => ∀ (b' : B) (σ : stdSimp (M + 2) ⟶ sSing B), sigmaVert σ = b' →
      HornTensorCompatible (F := sSing (Work.StemsB.fibre p b')) (Y := sSing E) (i := 0)
        (fun (j : Fin (M + 3)) (_ : j ≠ 0) =>
          D.Φ b' (SSet.stdSimplex.δ (n := M + 1) j ≫ σ))

/-- The result of one step of the recursion: the next level together with the coherence. -/
structure RStep {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (N : ℕ) (D : RLevel p N) where
  /-- the level `N+1` data -/
  D' : RLevel p (N + 1)
  /-- coherence with the previous level -/
  coh : RCoh p N D D'

end

end Work.SSS
