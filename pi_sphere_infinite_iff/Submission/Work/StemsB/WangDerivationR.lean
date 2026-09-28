import Mathlib
import Submission.Work.StemsB.WangSequenceShiftedR
import Submission.Work.StemsB.SerreSphereCollar
import Submission.Work.Cohomology.CupRing

/-!
# The derivation property of the Wang transgression, over an arbitrary coefficient ring

`Submission/Work/StemsB/WangDerivation.lean` records, over `ℤ`, the interface of `D2` of E4
(`Submission/Work/Drive/SERRE_BLUEPRINT.md`): the derivation property
`θ(a ⌣ b) = θ(a) ⌣ b + (-1)^{(b-1)·|a|} · a ⌣ θ(b)` of the Wang transgression of a Hurewicz
fibration over the sphere, together with the "suspension class of the collar" that is its geometric
input.

Every ingredient of that interface is stated for an arbitrary `CommRing R` in the workspace's
cohomology API (`Work.Cohomology.singularCohomology R`, `cupH' R`, `pairδ R`, `relComplex R`,
`singularCohomologyMap R`, `Work.Serre.ratCoh = singularCohomology ℚ`), and the transgression itself
is `Work.StemsB.wangCohShiftθR` (`WangSequenceShiftedR.lean`).  This file therefore records the same
interface with the coefficient ring as an explicit parameter, so that the **ℚ-coefficient** form
demanded by the blueprint's C2 odd step is a *statement* today:

* `Work.StemsB.CollarSuspensionR` / `CollarSuspensionStrongR` — over `R`: the suspension class `s`
  of the collar (`s ⌣ s = 0`, and `x ↦ δ(pr^*(x) ⌣ s)` bijective);
* `Work.StemsB.WangCohShiftDerivationR` — over `R`: the derivation property of the transgression.

The *proofs* are the remaining work; over `ℤ` they exist
(`Work.StemsB.wangSphereDerivation_exists`).  See `QCOEFF_PLAN.md` for why the ℚ proofs must not be
obtained by porting the ℤ chapter naively (the ℤ collar Thom class comes from the ℤ-only
`Work.Thom.ModelThom`), and for the route that avoids it.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false

namespace Work.StemsB

noncomputable section

variable (R : Type) [CommRing R]

/-- **Transport of a cohomology object along an equality of degrees** (coefficient-generic form of
`Work.StemsB.cohEqIso`). -/
noncomputable def cohEqIsoR (Fsp : TopCat) {k l : ℕ} (h : k = l) :
    Work.Cohomology.singularCohomology R k Fsp ≅
      Work.Cohomology.singularCohomology R l Fsp :=
  eqToIso (congrArg (fun t => Work.Cohomology.singularCohomology R t Fsp) h)

/-- **The Wang transgression, degree-normalised, over `R`.**  `wangCohShiftθR … n` is the
degree-`-(m-1)` transgression `H^k(F) → H^{k+1-m}(F)` evaluated at `k = n + m`; this definition
writes it directly as a map `H^k → H^{k+1-m}` for `m ≤ k`, with no truncated subtraction. -/
noncomputable def wangThetaOfR (X : TopCat) (A : Set X) (Fsp : TopCat) (m : ℕ)
    (γ : ∀ k : ℕ, Work.Cohomology.singularCohomology R k (TopCat.of A) ≅
      Work.Cohomology.singularCohomology R k Fsp)
    (τS : ∀ n : ℕ, (Work.Cohomology.relComplex R X A).homology (n + m + 1) ≅
      Work.Cohomology.singularCohomology R (n + 1) Fsp)
    (k : ℕ) (hk : m ≤ k) :
    Work.Cohomology.singularCohomology R k Fsp ⟶
      Work.Cohomology.singularCohomology R (k + 1 - m) Fsp :=
  (cohEqIsoR R Fsp (Nat.sub_add_cancel hk).symm).hom ≫
    wangCohShiftθR R X A Fsp m γ τS (k - m) ≫ (cohEqIsoR R Fsp (by omega)).hom

/-- **The derivation property of the Wang transgression, over `R`** (the target of E4's `D2`), in
the `n`-shifted form of `WangSequenceShiftedR.lean`: with `θ_n` of degree `-(m-1)`,
`θ_{n+n'+m}(a ⌣ b) = θ_n(a) ⌣ b + (-1)^{(m-1)(n+m)} · a ⌣ θ_{n'}(b)`. -/
def WangCohShiftDerivationR (X : TopCat) (A : Set X) (Fsp : TopCat) (m : ℕ)
    (γ : ∀ k : ℕ, Work.Cohomology.singularCohomology R k (TopCat.of A) ≅
      Work.Cohomology.singularCohomology R k Fsp)
    (τS : ∀ n : ℕ, (Work.Cohomology.relComplex R X A).homology (n + m + 1) ≅
      Work.Cohomology.singularCohomology R (n + 1) Fsp) : Prop :=
  ∀ (n n' : ℕ)
    (a : Work.Cohomology.singularCohomology R (n + m) Fsp)
    (b : Work.Cohomology.singularCohomology R (n' + m) Fsp),
    (wangCohShiftθR R X A Fsp m γ τS (n + n' + m)).hom
        ((cohEqIsoR R Fsp (by omega)).hom
          (Work.Cohomology.cupH' R (TopCat.toSSet.obj Fsp) (n + m) (n' + m) a b))
      = (cohEqIsoR R Fsp (by omega)).hom
            (Work.Cohomology.cupH' R (TopCat.toSSet.obj Fsp) (n + 1) (n' + m)
              ((wangCohShiftθR R X A Fsp m γ τS n).hom a) b)
        + ((-1 : R) ^ ((m - 1) * (n + m))) •
            (cohEqIsoR R Fsp (by omega)).hom
              (Work.Cohomology.cupH' R (TopCat.toSSet.obj Fsp) (n + m) (n' + 1)
                a ((wangCohShiftθR R X A Fsp m γ τS n').hom b))

/-! ## The suspension class of the collar, over `R` -/

/-- The projection of the collar product onto the collar. -/
def collarProdToCollarR (b : ℕ) (Y : Type) [TopologicalSpace Y] :
    C(↥(sphLoopCollarProd b Y), ↥(sphLoopCollar b)) :=
  ⟨fun q => (⟨q.1.1, q.2⟩ : ↥(sphLoopCollar b)), by fun_prop⟩

/-- The projection of the collar product onto the parameter space. -/
def collarProdToParamR (b : ℕ) (Y : Type) [TopologicalSpace Y] :
    C(↥(sphLoopCollarProd b Y), Y) :=
  ⟨fun q => q.1.2, by fun_prop⟩

/-- The pullback `H^{b-1}(sphLoopCollar b) → H^{b-1}(sphLoopCollar b × Y)`, over `R`. -/
noncomputable def collarPullR (b : ℕ) (Y : Type) [TopologicalSpace Y] :
    Work.Cohomology.singularCohomology R (b - 1) (TopCat.of ↥(sphLoopCollar b)) →ₗ[R]
      Work.Cohomology.singularCohomology R (b - 1) (TopCat.of (sphLoopCollarProd b Y)) :=
  (Work.Cohomology.singularCohomologyMap R (TopCat.of (sphLoopCollarProd b Y))
    (TopCat.of ↥(sphLoopCollar b)) (TopCat.ofHom (collarProdToCollarR b Y)) (b - 1)).hom

/-- The pullback `H^k(Y) → H^k(sphLoopCollar b × Y)`, over `R`. -/
noncomputable def collarPullParamR (b : ℕ) (Y : Type) [TopologicalSpace Y] (k : ℕ) :
    Work.Cohomology.singularCohomology R k (TopCat.of Y) →ₗ[R]
      Work.Cohomology.singularCohomology R k (TopCat.of (sphLoopCollarProd b Y)) :=
  (Work.Cohomology.singularCohomologyMap R (TopCat.of (sphLoopCollarProd b Y)) (TopCat.of Y)
    (TopCat.ofHom (collarProdToParamR b Y)) k).hom

/-- **The suspension class of the collar, over `R`**: a class `s` in degree `b - 1` whose cup square
vanishes and for which `x ↦ δ(pr^*(x) ⌣ s)` is the Thom isomorphism of the collar pair
(`H^k(Y;R) ≅ H^{k+b}(Q,C;R)`). -/
def CollarSuspensionR (b : ℕ) (hb : 2 ≤ b) (Y : Type) [TopologicalSpace Y] : Prop :=
  ∃ s : Work.Cohomology.singularCohomology R (b - 1)
      (TopCat.of (sphLoopCollarProd b Y)),
    (Work.Cohomology.cupH' R (TopCat.toSSet.obj (TopCat.of (sphLoopCollarProd b Y)))
        (b - 1) (b - 1) s s = 0) ∧
      ∀ k : ℕ, Function.Bijective (fun x : Work.Cohomology.singularCohomology R k (TopCat.of Y) =>
        (Work.Cohomology.pairδ R (TopCat.of (↥(sphLoopBig b) × Y)) (sphLoopCollarProd b Y)
            (k + (b - 1))).hom
          (Work.Cohomology.cupH' R (TopCat.toSSet.obj (TopCat.of (sphLoopCollarProd b Y)))
            k (b - 1)
            ((Work.Cohomology.singularCohomologyMap R (TopCat.of (sphLoopCollarProd b Y))
                (TopCat.of Y)
                (TopCat.ofHom (collarProdToParamR b Y)) k).hom x) s))

/-- **The suspension class of the collar, in the strong (pullback) form, over `R`.** -/
def CollarSuspensionStrongR (b : ℕ) (hb : 2 ≤ b) (Y : Type) [TopologicalSpace Y] : Prop :=
  ∃ u : Work.Cohomology.singularCohomology R (b - 1) (TopCat.of ↥(sphLoopCollar b)),
    (Work.Cohomology.cupH' R (TopCat.toSSet.obj (TopCat.of (sphLoopCollarProd b Y)))
        (b - 1) (b - 1) (collarPullR R b Y u) (collarPullR R b Y u) = 0) ∧
      ∀ k : ℕ, Function.Bijective (fun x : Work.Cohomology.singularCohomology R k (TopCat.of Y) =>
        (Work.Cohomology.pairδ R (TopCat.of (↥(sphLoopBig b) × Y)) (sphLoopCollarProd b Y)
            (k + (b - 1))).hom
          (Work.Cohomology.cupH' R (TopCat.toSSet.obj (TopCat.of (sphLoopCollarProd b Y)))
            k (b - 1) (collarPullParamR R b Y k x) (collarPullR R b Y u)))

end

end Work.StemsB
