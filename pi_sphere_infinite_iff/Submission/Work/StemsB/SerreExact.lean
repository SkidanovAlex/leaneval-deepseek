import Mathlib
import Submission.Work.Cohomology.localHomology
import Submission.Work.StemsB.Fibrations
import Submission.Work.StemsB.HurewiczFibration
import Submission.Work.StemsB.SphLoopModel

/-!
# The Serre exact sequence in the stable range (homological form): vocabulary

**Assignment (from the project lead, for area STEMS/route B).**  Deliver, as a theorem in
`Submission/Work/StemsB/`, the *Serre exact sequence in the stable range* in its homological form:

> for a fibration `F → E → B` with `B` `(b-1)`-connected and `F` `(f-1)`-connected, the map
> `H_i(E, F; ℤ) → H_i(B, *; ℤ)` induced by the projection is an isomorphism for `i < b + f`,

first for `B` a sphere (the two-disc decomposition of `Submission/Work/StemsB/SphLoopModel.lean`),
then for bases obtained by attaching cells.  This is the Serre-type input that the subproject
**RATHUREWICZ** (`Submission/Work/RatHurewicz/`) needs for the rational Hurewicz theorem: applied to
the path–loop fibration `ΩX → PX → X` of a `(k-1)`-connected space `X` it gives the *transgression
isomorphism* `H_{i-1}(ΩX) ≅ H_i(X)` for `1 ≤ i ≤ 2k-2`, and hence (by induction on `k`) the full
rational Hurewicz theorem in the stable range.

## What this file contains

Only *vocabulary* — no `sorry`, nothing to prove:

* `Work.StemsB.relPairMap p b₀` — the map of relative chain complexes
  `C_*(E, p⁻¹(b₀)) → C_*(B, {b₀})` induced by `p` (a map of pairs);
* `Work.StemsB.SerreExactRange` — the statement for a **Hurewicz** fibration over an arbitrary base;
* `Work.StemsB.SerreExactRangeHom` — the same with the connectivity of the fibre replaced by the
  *homological* vanishing `H_j(F;ℤ) = 0` (`0 < j < f`), which is the form actually used and which
  is what the Hurewicz lower bound would supply from `(f-1)`-connectedness;
* `Work.StemsB.SerreExactSphere` — the case `B = S^b` (`B = SphModel b`), the first deliverable;
* `Work.StemsB.SerreExactTransgression` — the specialisation to the path–loop fibration
  `evalOne X x₀` that the rational Hurewicz theorem consumes.

## Why Hurewicz fibrations here

The proof of the sphere case (and of the cell-attachment step) needs the **triviality of the
fibration over a contractible base**, in the sharp form that the trivialisation *commutes with the
projection* (so that it restricts to the preimage of any subset of the base).  For a Hurewicz
fibration this is immediate from the HLP w.r.t. the total space, and it is available in this
workspace for the only fibration that matters for the application: the path–loop fibration
`Work.StemsB.evalOne X x₀`, which is a Hurewicz fibration
(`Work.StemsB.isHurewiczFibration_evalOne`, proved in `Submission/Work/StemsB/HurewiczFibration.lean`).
For a *Serre* fibration the same trivialisation needs the HLP w.r.t. the total space; it can be
supplied as an extra hypothesis when needed.
-/

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

namespace Work.StemsB

noncomputable section

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]


/-- The constant map from the fibre `p⁻¹{b₀}` to the singleton `{b₀}`, as the second component of
the pair map `(E, p⁻¹{b₀}) → (B, {b₀})`. -/
def fibreMap (p : C(E, B)) (b₀ : B) :
    TopCat.of ↥(p ⁻¹' {b₀}) ⟶ TopCat.of ↥({b₀} : Set B) :=
  TopCat.ofHom ⟨fun _ => ⟨b₀, rfl⟩, continuous_const⟩

/-- **The map of pairs `(E, p⁻¹(b₀)) → (B, {b₀})`** induced by `p`, on relative singular chains:
`Work.Cohomology.relChainsMapOf` for the pair map whose second component is the constant map
`p⁻¹(b₀) → {b₀}`. -/
def relPairMap (p : C(E, B)) (b₀ : B) :
    Work.Cohomology.relChains (TopCat.of E) (p ⁻¹' {b₀}) ⟶
      Work.Cohomology.relChains (TopCat.of B) ({b₀} : Set B) :=
  Work.Cohomology.relChainsMapOf (TopCat.of E) (TopCat.of B) (p ⁻¹' {b₀}) {b₀}
    (TopCat.ofHom p) (fibreMap p b₀)
    (by ext x; exact x.2)

/-- **The Serre exact sequence in the stable range** (homological form), for a Hurewicz fibration
and an arbitrary base.

Let `p : E → B` be a Hurewicz fibration, `b₀ ∈ B`, `e₀ ∈ p⁻¹(b₀)`.  If `B` is `(b-1)`-connected
and the fibre `F = p⁻¹(b₀)` is `(f-1)`-connected (cube-based homotopy groups
`Work.StemsB.HomotopyGroup`, `π₀` included), then `p` induces an isomorphism
`H_i(E, F; ℤ) → H_i(B, {b₀}; ℤ)` for every `i < b + f`. -/
def SerreExactRange : Prop :=
  ∀ (E : Type) [TopologicalSpace E] (B : Type) [TopologicalSpace B] (p : C(E, B)),
    IsHurewiczFibration p → ∀ (e₀ : E) (b₀ : B) (he₀ : p e₀ = b₀) (b f : ℕ),
      (∀ i < b, Subsingleton (HomotopyGroup (Fin i) B b₀)) →
      (∀ i < f, Subsingleton (HomotopyGroup (Fin i) (↥{x : E | p x = b₀}) ⟨e₀, he₀⟩)) →
      ∀ i : ℕ, i < b + f → IsIso (HomologicalComplex.homologyMap (relPairMap p b₀) i)

/-- **The Serre exact sequence in the stable range** with the fibre's connectivity replaced by the
*homological* vanishing in the range: `H_j(F;ℤ) = 0` for `0 < j < f`.

**The extra hypothesis `hFconn` (the fibre is *path connected*, i.e. its `π₀` is trivial) is
necessary**: the homological vanishing `H_j(F) = 0` for `0 < j < f` alone does not force `F` to be
connected when `f = 1` (the hypotheses are then vacuous), and the statement is false without it —
the double cover `S² × {1,2} → S²` has `b = 1`, `f = 1` and `H_2(E,F) = ℤ² ↠ H_2(S²,*) = ℤ` not
injective.  Path connectedness of the fibre is exactly what `(f-1)`-connectedness supplies for
`f ≥ 1`, and it is what the proof uses at `i = b` (where `H_b(E,F) ≅ H_0(F) ≅ ℤ`). -/
def SerreExactRangeHom : Prop :=
  ∀ (E : Type) [TopologicalSpace E] (B : Type) [TopologicalSpace B] (p : C(E, B)),
    IsHurewiczFibration p → ∀ (e₀ : E) (b₀ : B) (he₀ : p e₀ = b₀) (b f : ℕ),
      (∀ i < b, Subsingleton (HomotopyGroup (Fin i) B b₀)) →
      Subsingleton (HomotopyGroup (Fin 0) (↥{x : E | p x = b₀}) ⟨e₀, he₀⟩) →
      (∀ j : ℕ, 0 < j → j < f →
        IsZero ((Work.Cohomology.singularChains ℤ (TopCat.of ↥{x : E | p x = b₀})).homology j)) →
      ∀ i : ℕ, i < b + f → IsIso (HomologicalComplex.homologyMap (relPairMap p b₀) i)

/-- **The sphere case**: `B = S^b`, in the one-point-compactification model `SphModel b` of
`Submission/Work/StemsB/SphLoopModel.lean`, whose base point is `∞`.  This is the first
deliverable; the general case is then reached by attaching cells. -/
def SerreExactSphere : Prop :=
  ∀ (b : ℕ) (E : Type) [TopologicalSpace E] (p : C(E, SphModel b)) (eInf : E)
      (heInf : p eInf = OnePoint.infty) (f : ℕ),
    IsHurewiczFibration p →
    Subsingleton (HomotopyGroup (Fin 0) (↥{x : E | p x = OnePoint.infty}) ⟨eInf, heInf⟩) →
    (∀ j : ℕ, 0 < j → j < f →
      IsZero ((Work.Cohomology.singularChains ℤ
        (TopCat.of ↥{x : E | p x = OnePoint.infty})).homology j)) →
    ∀ i : ℕ, i < b + f →
      IsIso (HomologicalComplex.homologyMap (relPairMap p OnePoint.infty) i)

/-- **The transgression isomorphism for the path–loop fibration**, the form that the rational
Hurewicz theorem consumes: for a `(k-1)`-connected `X` (`k ≥ 2`), the projection
`evalOne X x₀ : PathSpace X x₀ → X` induces an isomorphism
`H_i(PX, ΩX; ℤ) → H_i(X, {x₀}; ℤ)` for `i ≤ 2k - 2`.  Combined with
`H_i(PX, ΩX) ≅ H_{i-1}(ΩX)` (the path space is contractible) this is the classical
`H_{i-1}(ΩX) ≅ H_i(X)` in the stable range. -/
def SerreExactTransgression : Prop :=
  ∀ (X : Type) [TopologicalSpace X] (x₀ : X) (k : ℕ), 2 ≤ k →
    (∀ i < k, Subsingleton (HomotopyGroup (Fin i) X x₀)) →
    ∀ i : ℕ, 1 ≤ i → i ≤ 2 * k - 2 →
      IsIso (HomologicalComplex.homologyMap (relPairMap (evalOne X x₀) x₀) i)

end

end Work.StemsB
