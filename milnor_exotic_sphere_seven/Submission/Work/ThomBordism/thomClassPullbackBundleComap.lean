import Mathlib
import Submission.Work.Thom.IsoPunct
import Submission.Work.Tubular.exists_euclidean_normalBundle
import Submission.Work.Tubular.nonempty_thomClass_of_bundleIso
import Submission.Work.Thom.complexPullback
import Submission.Work.Thom.comapAux
import Submission.Work.Thom.Glue

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `thomClassPullbackBundleComap` is FALSE as stated

## The requested statement

```lean
theorem thomClassPullbackBundleComap {B B' : Type} [TopologicalSpace B] [TopologicalSpace B']
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type} {n : ℕ}
    (Z : Work.TangentClasses.RealBundle B F ι) (f : C(B', B)) (T : Work.Thom.ThomClass Z n) :
    ∃ ψ : C((Work.Thom.bundleComap Z f).TotalSpace, Z.TotalSpace),
      (∀ p, (ψ p).1 = f p.1) ∧ (∀ p, (ψ p).2 = p.2) ∧
      ∃ (hf : ∀ x ∈ Work.Thom.zeroComplement (Work.Thom.bundleComap Z f),
            ψ x ∈ Work.Thom.zeroComplement Z)
        (T' : Work.Thom.ThomClass (Work.Thom.bundleComap Z f) n),
        T'.τ = (Work.Thom.relCohMap ψ (Work.Thom.zeroComplement (Work.Thom.bundleComap Z f))
          (Work.Thom.zeroComplement Z) hf ℤ n).hom T.τ := by sorry
```

**It is false**, for the following reason.

`Work.Thom.ThomClass Z n` asks only that the cup map `x ↦ π^*(x) ⌣ τ` be bijective in *every*
degree (`Work.Thom.ThomClass.isThom`); it does **not** force `n = Z.rank`.  The degree of the class
can be shifted by any class `u ∈ H^d(B;ℤ)` (`d > 0`) with `x ↦ x ⌣ u` bijective on `H^*(B;ℤ)`, e.g.
the hyperplane class of an infinite-dimensional base, because

  `π^*(x) ⌣ (π^*(u) ⌣ gen) = π^*(x ⌣ u) ⌣ gen`,

so the cup map of `π^*(u) ⌣ gen` is the composite of the (bijective) cup map of the rank-one model
class `gen` with `(· ⌣ u)`.  Such a `u` exists iff `H^*(B;ℤ)` has infinite cohomological dimension
(if `· ⌣ u` is bijective then `u^j ≠ 0` for all `j`).

## Counterexample

* `B := ℂP^∞` (so `H^*(B;ℤ) = ℤ[u]`, `|u| = 2`, and `x ↦ x ⌣ u` is bijective on all of `H^*`),
  `F := ℝ`, `ι := PUnit`, `Z` the **trivial** real line bundle over `B` (one chart, transition
  `1`), and `n := 3`.
* `E = B × ℝ`, `A = B × (ℝ∖{0})`, and `H^m(E,A;ℤ) ≅ H^{m-1}(B;ℤ)` (the relative cohomology of
  `(ℝ, ℝ∖{0})` is `ℤ` in degree `1` only).  Let `gen ∈ H^1(E,A)` be the model Thom class
  (`Work.Thom.Mpun 1 B`, whose cup map is bijective by `Work.Thom.Mpun_isModel`).  Then

  `τ := π^*(u) ⌣ gen ∈ H^3(E,A)`,  and  `thomMap Z 3 τ k = thomMap Z 1 gen (k+2) ∘ (· ⌣ u)`

  is bijective in every `k`; so `⟨τ, ·⟩ : Work.Thom.ThomClass Z 3` **exists**.
* Take `B' := PUnit` and `f : C(PUnit, B)` the constant map.  Then `bundleComap Z f` is the trivial
  real line bundle over the point, so `H^3((bundleComap Z f).TotalSpace, ·∖0;ℤ) = H^3(ℝ,ℝ∖{0}) = 0`
  while `H^0(pt;ℤ) = ℤ`.  Hence the cup map of *every* class of degree `3` over `B'` is
  `ℤ → 0`, which is not bijective, and `Work.Thom.ThomClass (bundleComap Z f) 3` is **empty**.
  The requested conclusion therefore fails.

(The same example with the *zero*-dimensional fibre — `F := EuclideanSpace ℝ (Fin 0)`, the trivial
bundle over `ℂP^∞`, `n := 2`, `τ := u` — also works: there `A = ∅`, `OpenThom Z 2 = H^2(B)`, the
cup map is `· ⌣ u`, and over a point `OpenThom Z' 2 = 0`.)

## The repair

Add the rank hypothesis, e.g. `[FiniteDimensional ℝ F]` together with `Module.finrank ℝ F = n`
(equivalently `Z.rank = n`).  With it, the statement is the classical "the pullback of a Thom class
is a Thom class", whose content is genuinely *not* in the tree (see the note in
`Submission/Work/ThomBordism/paddedTubeData.lean`, item (B2)); the missing machinery is the
local-to-global step: compatible local Thom data over the pieces of an arbitrary open cover
(in particular: the restriction of a Thom class to a chart piece is a local Thom class, i.e. the
model class times a *unit* of `H^0`, not merely a non-zero-divisor).

The easy half — the total-space map `ψ`, its two defining properties, the induced map of
Thom pairs, and the **naturality of the Thom map** `ψ^* ∘ thomMap_Z = thomMap_{Z'} ∘ f^*` — is
proved below, together with the formal reduction of the requested statement to the single assertion
that the pulled-back class is a Thom class.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

namespace Work.ThomBordism

open Work.TangentClasses

/-- **The total-space map of the pullback bundle** `⟨x, v⟩ ↦ ⟨f x, v⟩`: this is
`Work.Thom.totalMap`. -/
noncomputable def thomComapMap {B B' : Type} [TopologicalSpace B] [TopologicalSpace B']
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type}
    (Z : RealBundle B F ι) (f : C(B', B)) :
    C((Work.Thom.bundleComap Z f).TotalSpace, Z.TotalSpace) :=
  Work.Thom.totalMap Z f

@[simp] theorem thomComapMap_apply {B B' : Type} [TopologicalSpace B] [TopologicalSpace B']
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type}
    (Z : RealBundle B F ι) (f : C(B', B)) (p : (Work.Thom.bundleComap Z f).TotalSpace) :
    (thomComapMap Z f p : Z.TotalSpace) = ⟨f p.1, p.2⟩ := rfl

theorem thomComapMap_fst {B B' : Type} [TopologicalSpace B] [TopologicalSpace B']
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type}
    (Z : RealBundle B F ι) (f : C(B', B)) (p : (Work.Thom.bundleComap Z f).TotalSpace) :
    (thomComapMap Z f p).1 = f p.1 := rfl

theorem thomComapMap_snd {B B' : Type} [TopologicalSpace B] [TopologicalSpace B']
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type}
    (Z : RealBundle B F ι) (f : C(B', B)) (p : (Work.Thom.bundleComap Z f).TotalSpace) :
    (show F from (thomComapMap Z f p).2) = (show F from p.2) := rfl

theorem thomComapMap_mem {B B' : Type} [TopologicalSpace B] [TopologicalSpace B']
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type}
    (Z : RealBundle B F ι) (f : C(B', B)) :
    ∀ p ∈ Work.Thom.zeroComplement (Work.Thom.bundleComap Z f),
      thomComapMap Z f p ∈ Work.Thom.zeroComplement Z :=
  fun _ hp => hp

end Work.ThomBordism

namespace Work.ThomBordism

open Work.TangentClasses

variable {B B' : Type} [TopologicalSpace B] [TopologicalSpace B']
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type} {n : ℕ}

/-- **Naturality of the Thom map under a pullback of the bundle.**  For the map `ψ = totalMap Z f`
of total spaces, the Thom map of the pullback bundle with the pulled-back class is the pullback of
the Thom map of `Z` along `ψ`, over the pullback `f^*` of the base:

  `ψ^*(π^*(x) ⌣ τ) = π'^*(f^*(x)) ⌣ ψ^*(τ)`. -/
theorem thomMap_pullback {Z : RealBundle B F ι} {f : C(B', B)} (T : Work.Thom.ThomClass Z n)
    (k : ℕ) (x : Work.Thom.Coh ℤ k B) :
    (Work.Thom.relCohMap (thomComapMap Z f)
        (Work.Thom.zeroComplement (Work.Thom.bundleComap Z f)) (Work.Thom.zeroComplement Z)
        (thomComapMap_mem Z f) ℤ (k + n)).hom (Work.Thom.thomMap Z n T.τ k x)
      = Work.Thom.thomMap (Work.Thom.bundleComap Z f) n
          ((Work.Thom.relCohMap (thomComapMap Z f)
            (Work.Thom.zeroComplement (Work.Thom.bundleComap Z f))
            (Work.Thom.zeroComplement Z) (thomComapMap_mem Z f) ℤ n).hom T.τ) k
          ((Work.Thom.CohMap f ℤ k).hom x) := by
  rw [Work.Thom.thomMap_apply, Work.Thom.thomMap_apply]
  rw [Work.Thom.mixedCupC_pairNatural (thomComapMap Z f)
    (Work.Thom.zeroComplement (Work.Thom.bundleComap Z f)) (Work.Thom.zeroComplement Z)
    (thomComapMap_mem Z f) k n ((Work.Thom.CohMap (Work.Thom.bundleProj Z) ℤ k).hom x) T.τ]
  have hcomp : (Work.Thom.bundleProj Z).comp (thomComapMap Z f)
      = f.comp (Work.Thom.bundleProj (Work.Thom.bundleComap Z f)) := by
    ext p
    rfl
  have h1 : ((Work.Thom.CohMap (thomComapMap Z f) ℤ k).hom).comp
        ((Work.Thom.CohMap (Work.Thom.bundleProj Z) ℤ k).hom)
      = (Work.Thom.CohMap ((Work.Thom.bundleProj Z).comp (thomComapMap Z f)) ℤ k).hom := by
    rw [Work.Thom.CohMap_comp (thomComapMap Z f) (Work.Thom.bundleProj Z) ℤ k,
      ModuleCat.hom_comp]
  have h2 : ((Work.Thom.CohMap (Work.Thom.bundleProj (Work.Thom.bundleComap Z f)) ℤ k).hom).comp
        ((Work.Thom.CohMap f ℤ k).hom)
      = (Work.Thom.CohMap (f.comp (Work.Thom.bundleProj (Work.Thom.bundleComap Z f))) ℤ k).hom := by
    rw [Work.Thom.CohMap_comp (Work.Thom.bundleProj (Work.Thom.bundleComap Z f)) f ℤ k,
      ModuleCat.hom_comp]
  have hkey : (Work.Thom.CohMap (thomComapMap Z f) ℤ k).hom
        ((Work.Thom.CohMap (Work.Thom.bundleProj Z) ℤ k).hom x)
      = (Work.Thom.CohMap (Work.Thom.bundleProj (Work.Thom.bundleComap Z f)) ℤ k).hom
        ((Work.Thom.CohMap f ℤ k).hom x) := by
    calc (Work.Thom.CohMap (thomComapMap Z f) ℤ k).hom
            ((Work.Thom.CohMap (Work.Thom.bundleProj Z) ℤ k).hom x)
        = (Work.Thom.CohMap ((Work.Thom.bundleProj Z).comp (thomComapMap Z f)) ℤ k).hom x :=
          LinearMap.congr_fun h1 x
      _ = (Work.Thom.CohMap (f.comp (Work.Thom.bundleProj (Work.Thom.bundleComap Z f))) ℤ k).hom x := by
          rw [hcomp]
      _ = (Work.Thom.CohMap (Work.Thom.bundleProj (Work.Thom.bundleComap Z f)) ℤ k).hom
            ((Work.Thom.CohMap f ℤ k).hom x) := (LinearMap.congr_fun h2 x).symm
  rw [hkey]

end Work.ThomBordism

namespace Work.ThomBordism

open Work.TangentClasses

/-- The class of the Thom pair of the pullback obtained by pulling back a Thom class of `Z`. -/
noncomputable def thomComapClass {B B' : Type} [TopologicalSpace B] [TopologicalSpace B']
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type} {n : ℕ}
    (Z : RealBundle B F ι) (f : C(B', B)) (T : Work.Thom.ThomClass Z n) :
    Work.Thom.OpenThom (Work.Thom.bundleComap Z f) n :=
  (Work.Thom.relCohMap (thomComapMap Z f) (Work.Thom.zeroComplement (Work.Thom.bundleComap Z f))
    (Work.Thom.zeroComplement Z) (thomComapMap_mem Z f) ℤ n).hom T.τ

/-- **The target, reduced to the single statement that the pulled-back class is a Thom class.** -/
theorem thomClassPullbackBundleComap_of_isThom {B B' : Type} [TopologicalSpace B]
    [TopologicalSpace B'] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type}
    {n : ℕ} (Z : RealBundle B F ι) (f : C(B', B)) (T : Work.Thom.ThomClass Z n)
    (h : ∀ k, Function.Bijective
      (Work.Thom.thomMap (Work.Thom.bundleComap Z f) n (thomComapClass Z f T) k)) :
    ∃ ψ : C((Work.Thom.bundleComap Z f).TotalSpace, Z.TotalSpace),
      (∀ p, (ψ p).1 = f p.1) ∧ (∀ p, (ψ p).2 = p.2) ∧
      ∃ (hf : ∀ x ∈ Work.Thom.zeroComplement (Work.Thom.bundleComap Z f),
            ψ x ∈ Work.Thom.zeroComplement Z)
        (T' : Work.Thom.ThomClass (Work.Thom.bundleComap Z f) n),
        T'.τ = (Work.Thom.relCohMap ψ (Work.Thom.zeroComplement (Work.Thom.bundleComap Z f))
          (Work.Thom.zeroComplement Z) hf ℤ n).hom T.τ :=
  ⟨thomComapMap Z f, thomComapMap_fst Z f, thomComapMap_snd Z f, thomComapMap_mem Z f,
    ⟨thomComapClass Z f T, h⟩, rfl⟩

end Work.ThomBordism
