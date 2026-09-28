import Submission.Work.StemsB.WangCohSphereShifted
import Submission.Work.Cohomology.CupRing

/-!
# The derivation property of the Wang transgression: the interface

*(Area STEMSB.  See `E4_CORRECTION.md` for the correction of `Work.Serre.SerreE4`, and
`D2_PLAN.md` / `WANG_PLAN.md` for the route.)*

For a Hurewicz fibration `p : E → SphModel b` with fibre `F = p ⁻¹' {∞}` and the two fibrewise
trivialities over the outer piece (`sphLoopOuter b`) and the inner cube (`sphLoopBig b`),
`WangCohSphereShifted.lean` proves the **exactness** of the Wang sequence

  `H^n(F) --β_n--> H^{n+b}(E) --α_(n+b)--> H^{n+b}(F) --θ_n--> H^{n+1}(F) --β_n^S--> H^{n+b+1}(E)`

with

* `α := wangCohShiftα … (wangGammaSphereOuter …)`,
* `β := wangCohShiftβ …`,
* `θ := wangCohShiftθ … (wangGammaSphereOuter …) (wangTauCohShiftS …)`.

As a map `H^k(F) → H^{k-b+1}(F)` (i.e. `θ_n` with `k = n + b`), `θ` has **degree `-(b-1)`**: the
classical Wang transgression.  This file records the **derivation property**

  `θ(a ⌣ b) = θ(a) ⌣ b + (-1)^{(b-1)·|a|} · a ⌣ θ(b)`

(`|a|` the cohomological degree of `a`), both in the degree-normalised form (`wangThetaOf`, no
truncated subtraction) and in the `n`-shifted form used by `WangCohSphereShifted`
(`WangCohShiftDerivation`).

The proof of the derivation property is **not** a formal property of the connecting map of a pair:
for a general pair `(X,A)` the products in `H^*(A)` are not accessible to the pair machinery when
`H^*(X) → H^*(A)` is not surjective (there need not be *lifts* of the factors to `H^*(X)`, and the
naive "δ is a derivation" with the `H^*(X)`-module structure is only available for products where
one factor is in the image — `Work.Sph3Disc.pairDelta_mixedCup_general`).  The correct route is the
**clutching map** (the project lead's formulation (b) of E4):

* the transgression is, up to sign, the `s`-component of `λ^*`, where `λ : C × F → F`,
  `λ (x, y) = snd (Φ_O (Φ_G⁻¹ (x, y)))` is the clutching map (the two trivialisations over the
  outer piece and the inner cube, read on the collar `C = sphLoopCollar b ≃ S^{b-1}`), i.e.
  `λ^*(a) = 1 ⊗ a + s ⊗ θ(a)` in the Künneth decomposition `H^*(C × F) ≅ H^*(F)[s]/(s²)`,
  `|s| = b - 1`;
* `λ^*` is a ring map (it is induced by a continuous map), `s ⌣ s = 0` for `b ≥ 2`, and the
  `s`-component map `p₂ : H^*(F)[s]/(s²) → H^*(F)` is then a derivation by the computation
  carried out in `D2_PLAN.md` §1(b).  So `θ` is a derivation.

The remaining ingredients of that route are the subject of the delegated lemmas recorded in
`WANG_PLAN.md` / `D2_PLAN.md`.
-/

open scoped Topology
open CategoryTheory CategoryTheory.Limits

set_option linter.unusedVariables false

namespace Work.StemsB

noncomputable section

/-- **Transport of a cohomology object along an equality of degrees.**  All the degree shifts
below are taken with this isomorphism, so that no `ℤ`-graded bookkeeping (and no truncated
subtraction in a *type*) is needed. -/
noncomputable def cohEqIso (Fsp : TopCat) {k l : ℕ} (h : k = l) :
    Work.Cohomology.singularCohomology ℤ k Fsp ≅
      Work.Cohomology.singularCohomology ℤ l Fsp :=
  eqToIso (congrArg (fun t => Work.Cohomology.singularCohomology ℤ t Fsp) h)

/-- **The Wang transgression, degree-normalised.**  `wangCohShiftθ … n : H^{n+m}(F) → H^{n+1}(F)`
is the degree-`-(m-1)` transgression `H^k(F) → H^{k+1-m}(F)` evaluated at `k = n + m`; this
definition writes it directly as a map `H^k → H^{k+1-m}` for `m ≤ k`, with no truncated
subtraction (so that the derivation property needs no degree bookkeeping). -/
noncomputable def wangThetaOf (X : TopCat) (A : Set X) (Fsp : TopCat) (m : ℕ)
    (γ : ∀ k : ℕ, Work.Cohomology.singularCohomology ℤ k (TopCat.of A) ≅
      Work.Cohomology.singularCohomology ℤ k Fsp)
    (τS : ∀ n : ℕ, (Work.Cohomology.relComplex ℤ X A).homology (n + m + 1) ≅
      Work.Cohomology.singularCohomology ℤ (n + 1) Fsp)
    (k : ℕ) (hk : m ≤ k) :
    Work.Cohomology.singularCohomology ℤ k Fsp ⟶
      Work.Cohomology.singularCohomology ℤ (k + 1 - m) Fsp :=
  (cohEqIso Fsp (Nat.sub_add_cancel hk).symm).hom ≫ wangCohShiftθ X A Fsp m γ τS (k - m) ≫
    (cohEqIso Fsp (by omega)).hom

/-- **The derivation property of the Wang transgression** (the target of D2 of E4), in the
`n`-shifted form used by `WangCohSphereShifted`.  With `θ_n := wangCohShiftθ … n` of degree
`-(m-1)` (source `H^{n+m}`, target `H^{n+1}`) this is

  `θ_{n+n'+m}(a ⌣ b) = θ_n(a) ⌣ b + (-1)^{(m-1)(n+m)} · a ⌣ θ_{n'}(b)`

for `a ∈ H^{n+m}`, `b ∈ H^{n'+m}`; the sign `(-1)^{(m-1)·|a|}` with `|a| = n + m` is the Koszul
sign of the derivation of degree `-(m-1)` (see `D2_PLAN.md` §1(b)). -/
def WangCohShiftDerivation (X : TopCat) (A : Set X) (Fsp : TopCat) (m : ℕ)
    (γ : ∀ k : ℕ, Work.Cohomology.singularCohomology ℤ k (TopCat.of A) ≅
      Work.Cohomology.singularCohomology ℤ k Fsp)
    (τS : ∀ n : ℕ, (Work.Cohomology.relComplex ℤ X A).homology (n + m + 1) ≅
      Work.Cohomology.singularCohomology ℤ (n + 1) Fsp) : Prop :=
  ∀ (n n' : ℕ)
    (a : Work.Cohomology.singularCohomology ℤ (n + m) Fsp)
    (b : Work.Cohomology.singularCohomology ℤ (n' + m) Fsp),
    (wangCohShiftθ X A Fsp m γ τS (n + n' + m)).hom
        ((cohEqIso Fsp (by omega)).hom
          (Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj Fsp) (n + m) (n' + m) a b))
      = (cohEqIso Fsp (by omega)).hom
            (Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj Fsp) (n + 1) (n' + m)
              ((wangCohShiftθ X A Fsp m γ τS n).hom a) b)
        + ((-1 : ℤ) ^ ((m - 1) * (n + m))) •
            (cohEqIso Fsp (by omega)).hom
              (Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj Fsp) (n + m) (n' + 1)
                a ((wangCohShiftθ X A Fsp m γ τS n').hom b))

/-- **The Wang transgression for the sphere model**, degree-normalised.  The family `τS` is the
one of `WangCohSphereShifted.wangTauCohShiftS`. -/
noncomputable def wangThetaSphereOf (b : ℕ) (hb : 1 ≤ b) (E : Type) [TopologicalSpace E]
    (p : C(E, SphModel b)) (hp : IsHurewiczFibration p)
    (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b))
    (d_G : ↥(sphLoopBig b)) (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G)
    (k : ℕ) (hk : b ≤ k) :
    Work.Cohomology.singularCohomology ℤ k (wangCohFsp b p) ⟶
      Work.Cohomology.singularCohomology ℤ (k + 1 - b) (wangCohFsp b p) :=
  wangThetaOf (TopCat.of E) (p ⁻¹' sphLoopOuter b) (wangCohFsp b p) b
    (wangGammaSphereOuter b hb E p hT_O)
    (wangTauCohShiftS b hb E p hp d_G hT_G) k hk

/-- **The derivation property of the Wang transgression over a sphere.**  This is the statement to
be handed to subproject SERRE: it is the derivation half of E4 of
`Submission/Work/Drive/SERRE_BLUEPRINT.md`, in the classical (degree `-(b-1)`) indexing. -/
def WangSphereDerivation (b : ℕ) (hb : 1 ≤ b) (E : Type) [TopologicalSpace E]
    (p : C(E, SphModel b)) (hp : IsHurewiczFibration p)
    (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b))
    (d_G : ↥(sphLoopBig b)) (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G) : Prop :=
  WangCohShiftDerivation (TopCat.of E) (p ⁻¹' sphLoopOuter b) (wangCohFsp b p) b
    (wangGammaSphereOuter b hb E p hT_O)
    (wangTauCohShiftS b hb E p hp d_G hT_G)

/-! ## The remaining geometric input of the derivation property

The derivation property is proved from the **suspension class** of the collar: a class
`s ∈ H^{b-1}(sphLoopCollar b × Y; ℤ)` whose cup square vanishes and whose `δ`-image is the Thom
class — equivalently, `x ↦ δ(pr^*(x) ⌣ s)` is a bijection `H^k(Y) ≅ H^{k+b}(G × Y, C × Y)`.

The two properties of `CollarSuspension` are exactly what the computation of `D2_PLAN.md` §2 uses:
`s ⌣ s = 0` kills the `s ⌣ s` term of the expansion of `λ^*(a ⌣ b)`, and the bijectivity says that
`δ(s ⌣ −)` is a *section* of `δ`, i.e. that (v) the `s`-component of `λ^*a` has `δ`-image `θ(a)`.
The companion statement (that the collar isomorphism is `H^*(Y)`-linear, i.e. that the inverse of
`x ↦ pr^*(x) ⌣ τ` is a module map) is `Work.StemsB.collar_thomClass`, which gives the Thom class
`τ` underlying this one. -/

/-- **The suspension class of the collar** (`G = sphLoopBig b`, `C = sphLoopCollar b`): a class in
degree `b - 1` (`2 ≤ b`, so that `b - 1 ≥ 1` and `s ⌣ s` can vanish) whose cup square
vanishes and whose image under the connecting map —
`x ↦ δ(pr^*(x) ⌣ s)` — is the Thom isomorphism `H^k(Y) ≅ H^{k+b}(G × Y, C × Y)`.  This is the
remaining geometric input of `Work.StemsB.WangCohShiftDerivation` (see `D2_PLAN.md` STATE UPDATE 1
§2, item 2, and `WANG_PLAN.md`). -/
def CollarSuspension (b : ℕ) (hb : 2 ≤ b) (Y : Type) [TopologicalSpace Y] : Prop :=
  ∃ s : Work.Cohomology.singularCohomology ℤ (b - 1)
      (TopCat.of (sphLoopCollarProd b Y)),
    (Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of (sphLoopCollarProd b Y)))
        (b - 1) (b - 1) s s = 0) ∧
      ∀ k : ℕ, Function.Bijective (fun x : Work.Cohomology.singularCohomology ℤ k (TopCat.of Y) =>
        (Work.Cohomology.pairδ ℤ (TopCat.of (↥(sphLoopBig b) × Y)) (sphLoopCollarProd b Y)
            (k + (b - 1))).hom
          (Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of (sphLoopCollarProd b Y)))
            k (b - 1)
            ((Work.Cohomology.singularCohomologyMap ℤ (TopCat.of (sphLoopCollarProd b Y))
                (TopCat.of Y)
                (TopCat.ofHom (⟨fun q : ↥(sphLoopCollarProd b Y) => q.1.2, by fun_prop⟩ :
                  C(↥(sphLoopCollarProd b Y), Y))) k).hom x) s))

/-- The projection of the collar product onto the collar. -/
def collarProdToCollar (b : ℕ) (Y : Type) [TopologicalSpace Y] :
    C(↥(sphLoopCollarProd b Y), ↥(sphLoopCollar b)) :=
  ⟨fun q => (⟨q.1.1, q.2⟩ : ↥(sphLoopCollar b)), by fun_prop⟩

/-- The projection of the collar product onto the parameter space. -/
def collarProdToParam (b : ℕ) (Y : Type) [TopologicalSpace Y] :
    C(↥(sphLoopCollarProd b Y), Y) :=
  ⟨fun q => q.1.2, by fun_prop⟩

/-- The pullback `H^{b-1}(sphLoopCollar b) → H^{b-1}(sphLoopCollar b × Y)`. -/
noncomputable def collarPull (b : ℕ) (Y : Type) [TopologicalSpace Y] :
    Work.Cohomology.singularCohomology ℤ (b - 1) (TopCat.of ↥(sphLoopCollar b)) →ₗ[ℤ]
      Work.Cohomology.singularCohomology ℤ (b - 1) (TopCat.of (sphLoopCollarProd b Y)) :=
  (Work.Cohomology.singularCohomologyMap ℤ (TopCat.of (sphLoopCollarProd b Y))
    (TopCat.of ↥(sphLoopCollar b)) (TopCat.ofHom (collarProdToCollar b Y)) (b - 1)).hom

/-- The pullback `H^k(Y) → H^k(sphLoopCollar b × Y)`. -/
noncomputable def collarPullParam (b : ℕ) (Y : Type) [TopologicalSpace Y] (k : ℕ) :
    Work.Cohomology.singularCohomology ℤ k (TopCat.of Y) →ₗ[ℤ]
      Work.Cohomology.singularCohomology ℤ k (TopCat.of (sphLoopCollarProd b Y)) :=
  (Work.Cohomology.singularCohomologyMap ℤ (TopCat.of (sphLoopCollarProd b Y)) (TopCat.of Y)
    (TopCat.ofHom (collarProdToParam b Y)) k).hom

/-- **The suspension class of the collar, in the strong (pullback) form.**  This is
`CollarSuspension` together with the *normalisation* used by the lead's plan
(`D2_PLAN.md` STATE UPDATE 2, step 2): the class is the pullback of a class on the collar itself.
Consequently its restriction to any slice `{d} × Y ⊆ C × Y` vanishes (the composite
`Y → {d} × Y ↪ C × Y → C` is constant and `H^{b-1}(pt) = 0` for `b ≥ 2`), which is what makes the
first coefficient `x` of the decomposition of `λ^*a` equal to `a`. -/
def CollarSuspensionStrong (b : ℕ) (hb : 2 ≤ b) (Y : Type) [TopologicalSpace Y] : Prop :=
  ∃ u : Work.Cohomology.singularCohomology ℤ (b - 1) (TopCat.of ↥(sphLoopCollar b)),
    (Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of (sphLoopCollarProd b Y)))
        (b - 1) (b - 1) (collarPull b Y u) (collarPull b Y u) = 0) ∧
      ∀ k : ℕ, Function.Bijective (fun x : Work.Cohomology.singularCohomology ℤ k (TopCat.of Y) =>
        (Work.Cohomology.pairδ ℤ (TopCat.of (↥(sphLoopBig b) × Y)) (sphLoopCollarProd b Y)
            (k + (b - 1))).hom
          (Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of (sphLoopCollarProd b Y)))
            k (b - 1) (collarPullParam b Y k x) (collarPull b Y u)))

end

end Work.StemsB
