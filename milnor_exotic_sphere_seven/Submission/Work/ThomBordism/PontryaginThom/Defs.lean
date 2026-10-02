import Mathlib
import Submission.Work.ThomBordism.Interface
import Submission.Work.Stems.Hurewicz
import Submission.Work.Stems.hurewiczChain_eq_of_homotopic
import Submission.Work.SignatureBordism.Bordism
import Submission.Work.Drive.RationalHurewicz

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The Pontryagin–Thom chapter: the model

This file fixes the objects on which the Pontryagin–Thom chapter of `Work.ThomBordism` is stated,
so that the pieces compose and the two geometric inputs (the universal Thom space of the oriented
Grassmannian, and transversality) enter at exactly one place each.

## The setting

`Work.ThomBordism.Man8` is a closed oriented smooth `8`-manifold (as the target model of the
project).  For the Pontryagin–Thom construction one

* embeds `V ⊂ ℝ^{8+k}` (`k` the codimension, `k ≥ 10` for the stable range; Mathlib's
  `exists_embedding_euclidean_of_compact` gives a closed `C^∞` embedding into `EuclideanSpace ℝ
  (Fin n)` for *some* `n`, with injective derivative),
* takes the normal bundle `ν` of the embedding and a tubular neighbourhood of `V`,
* collapses `S^{8+k} → Th(ν)` along the tubular neighbourhood, and
* classifies `ν` by the Gauss map `V → G̃r_k(ℝ^{k+m})`, inducing `Th(ν) → T := Th(γ_k)`,

obtaining the class `α_V ∈ π_{8+k}(T)`.  Items 1–4 need the embedding theorem, the tubular
neighbourhood theorem and the collapse, none of which is in Mathlib; they are *data* here (the
structure `PTRep`), not constructions.  What the proof of `TransversalityCore` uses about them is
recorded in the same structure:

* the **Hurewicz pairing** of `α_V` with the two degree-`8+k` classes `p₁²U`, `p₂U` of the Thom
  space is the **normal** Pontryagin numbers of the embedding (`PTRep.hurewicz_p1sq`,
  `PTRep.hurewicz_p2`) — the content of the Thom isomorphism;
* the normal Pontryagin classes are related to the tangent ones by the **Whitney formula** applied
  to `TV ⊕ ν ≅ ε^{8+k}` (`NormalBundlData`).

The *algebra* performed here (`Normal.lean`, `Hurewicz.lean`) turns those into the number
identities used by the assembly, and `Assembly.lean` proves `TransversalityCore` and
`TransversalityCoreFamily` from the two geometric inputs and `Work.Drive.RationalHurewiczStable`.

## The universal Thom space (`ThomTarget`)

`ThomTarget k` is the *interface of the Grassmann chapter*: a based space `T` — in the application
`T = Th(γ_k)` for the universal oriented `k`-plane bundle over `G̃r_k(ℝ^{k+m})` — together with the
Thom classes `p₁²U`, `p₂U ∈ H^{8+k}(T;ℤ)` and the two properties of `T` used by the argument:

* `ThomTarget.connected` — `T` is `(k-1)`-connected (true for the Thom space of a rank-`k` bundle
  over a connected base), which is what `Work.Drive.RationalHurewiczStable` needs;
* `ThomTarget.detects_torsion` — a homology class of degree `8+k` whose two pairings with `p₁²U`
  and `p₂U` vanish is torsion.  This is the coefficient-free form of the Grassmann chapter's
  `H^{8+k}(T;ℚ) = ℚ{p₁²U, p₂U}`: over `ℚ` the two classes are a basis of the dual, and a class
  killed by tensoring with `ℚ` is torsion (localisation).

The Grassmann chapter does not need to be *edited* to use this file: it instantiates `ThomTarget`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicTopology
open scoped Manifold ContDiff

namespace Work.ThomBordism.PontryaginThom

noncomputable section

open Work.Cohomology

/-! ## The Hurewicz class of a homotopy class

`Work.Stems.hurewiczChain` attaches the Hurewicz class to a *cube* (a representative); its descent
to `HomotopyGroup` is `Work.Stems.hurewiczMap`, in a module whose import closure is incompatible
with `Work.ThomBordism.Interface` (both pull in a conflicting declaration
`Work.Cohomology.homologyBiprodIso`).  We therefore descend it here, in the same way and from the
same two lemmas: nothing is redefined, and `hurewiczClassOf_mk` records that the value on the class
of a cube is exactly `Work.Stems.hurewiczChain`. -/

/-- The singular simplicial set of a space: the object whose cohomology is used below. -/
abbrev ssetOf (T : Type) [TopologicalSpace T] : SSet := TopCat.toSSet.obj (TopCat.of T)

/-- **The Hurewicz class of a homotopy class** `α ∈ πₙ(T,t₀)`: the class of `Work.Stems.hurewiczChain`
of a cube representative, well defined by `Work.Stems.hurewiczChain_eq_of_homotopic`.

(The codomain is written in the `chainC` form so that the Kronecker pairing `kronH` applies
syntactically; it is *definitionally* `(Work.Stems.chains (TopCat.of T)).homology n`.) -/
def hurewiczClassOf (n : ℕ) (hn : 1 ≤ n) {T : Type} [TopologicalSpace T] (t₀ : T)
    (α : HomotopyGroup (Fin n) T t₀) : (chainC ℤ (ssetOf T)).homology n :=
  Quotient.lift (fun p => Work.Stems.hurewiczChain n hn t₀ p)
    (fun _ _ h => Work.Stems.hurewiczChain_eq_of_homotopic n hn h) α

/-- On the class of a cube, `hurewiczClassOf` is `Work.Stems.hurewiczChain`. -/
theorem hurewiczClassOf_mk (n : ℕ) (hn : 1 ≤ n) {T : Type} [TopologicalSpace T] {t₀ : T}
    (p : GenLoop (Fin n) T t₀) :
    hurewiczClassOf n hn t₀ (Quotient.mk _ p) = Work.Stems.hurewiczChain n hn t₀ p := rfl

/-! ## The universal Thom space -/

/-- **The Thom space of the universal oriented `k`-plane bundle, as an interface.**

* `T` is the Thom space, `t₀` its base point (the point at infinity of the one-point
  compactification, i.e. the class of the complement of the zero section);
* `p1sqU`, `p2U ∈ H^{8+k}(T;ℤ)` are `p₁(γ)² ⌣ U` and `p₂(γ) ⌣ U` (`U` the Thom class);
* `connected` is the `(k-1)`-connectedness of the Thom space of a rank-`k` bundle over a connected
  base;
* `detects_torsion` is the coefficient-free form of `H^{8+k}(T;ℚ) = ℚ{p₁²U, p₂U}`. -/
structure ThomTarget (k : ℕ) where
  /-- the Thom space -/
  T : Type
  [topologicalSpace : TopologicalSpace T]
  /-- the base point -/
  t₀ : T
  /-- the class `p₁(γ)² ⌣ U` in degree `8 + k` -/
  p1sqU : (cochainC ℤ (ssetOf T)).homology (k + 8)
  /-- the class `p₂(γ) ⌣ U` in degree `8 + k` -/
  p2U : (cochainC ℤ (ssetOf T)).homology (k + 8)
  /-- `T` is `(k-1)`-connected -/
  connected : ∀ i < k, Subsingleton (HomotopyGroup (Fin i) T t₀)
  /-- the two classes detect torsion in degree `8 + k`: a homology class pairings to `0` with both
  is torsion. -/
  detects_torsion : ∀ y : (chainC ℤ (ssetOf T)).homology (k + 8),
    kronH ℤ (ssetOf T) (k + 8) p1sqU y = 0 →
    kronH ℤ (ssetOf T) (k + 8) p2U y = 0 →
    ∃ N : ℕ, 0 < N ∧ (N : ℤ) • y = 0

attribute [instance] ThomTarget.topologicalSpace

/-- `1 ≤ k + 8`, for the degree bookkeeping. -/
theorem one_le_add_eight (k : ℕ) : 1 ≤ k + 8 := by omega

/-- The Kronecker pairing of a homology class with `p₁²U`. -/
def ThomTarget.pair1 {k : ℕ} (D : ThomTarget k) (y : (chainC ℤ (ssetOf D.T)).homology (k + 8)) : ℤ :=
  kronH ℤ (ssetOf D.T) (k + 8) D.p1sqU y

/-- The Kronecker pairing of a homology class with `p₂U`. -/
def ThomTarget.pair2 {k : ℕ} (D : ThomTarget k) (y : (chainC ℤ (ssetOf D.T)).homology (k + 8)) : ℤ :=
  kronH ℤ (ssetOf D.T) (k + 8) D.p2U y

/-- `detects_torsion`, in terms of `pair1`/`pair2`. -/
theorem ThomTarget.torsion_of_pairs_zero {k : ℕ} (D : ThomTarget k)
    (y : (chainC ℤ (ssetOf D.T)).homology (k + 8))
    (h1 : D.pair1 y = 0) (h2 : D.pair2 y = 0) :
    ∃ N : ℕ, 0 < N ∧ (N : ℤ) • y = 0 :=
  D.detects_torsion y h1 h2

/-! ## The normal bundle of an embedding -/

/-- **The normal Pontryagin classes of an embedding `V ⊂ ℝ^{8+k}`**, with the Whitney relation.

`q1`, `q2` are the first and second Pontryagin classes of the normal bundle `ν`, and the two fields
are the degree-`4` and degree-`8` coefficients of the identity `p(ν) ⌣ p(TV) = 1` in `H^*(V;ℤ)`
(which holds because `TV ⊕ ν ≅ ε^{8+k}` and `p(E ⊕ F) = p(E) ⌣ p(F)`, the **Whitney formula** of
`Submission/Work/Whitney/`):

`(1 + q1 + q2) ⌣ (1 + p1 + p2) = 1`,

truncated at degree `8` (the manifold has dimension `8`, so all higher products vanish):

* `whitney4` : `q1 + p1 = 0`;
* `whitney8` : `q2 + q1 ⌣ p1 + p2 = 0`.

No higher coefficients are needed: `Normal.lean` derives `q1 = -p1` and `q2 = p1² - p2` from these
two alone, hence the normal numbers `p̄₁² = p₁²` and `p̄₂ = p₁² - p₂` in terms of the tangent ones. -/
structure NormalBundlData (V : Man8) where
  /-- the first Pontryagin class of the normal bundle -/
  q1 : (cochainC ℤ (TopCat.toSSet.obj V.X)).homology 4
  /-- the second Pontryagin class of the normal bundle -/
  q2 : (cochainC ℤ (TopCat.toSSet.obj V.X)).homology 8
  /-- the degree-`4` coefficient of `p(ν) ⌣ p(TV) = 1` -/
  whitney4 : q1 + V.p1 = 0
  /-- the degree-`8` coefficient of `p(ν) ⌣ p(TV) = 1` -/
  whitney8 : q2 + cupH' ℤ (TopCat.toSSet.obj V.X) 4 4 q1 V.p1 + V.p2 = 0

/-- **The normal `p₁²`-number** `⟨q₁ ⌣ q₁, [V]⟩` of an embedding. -/
def NormalBundlData.normalP1Sq {V : Man8} (N : NormalBundlData V) : ℤ :=
  kronH ℤ (TopCat.toSSet.obj V.X) 8
    (cupH' ℤ (TopCat.toSSet.obj V.X) 4 4 N.q1 N.q1) V.c

/-- **The normal `p₂`-number** `⟨q₂, [V]⟩` of an embedding. -/
def NormalBundlData.normalP2 {V : Man8} (N : NormalBundlData V) : ℤ :=
  kronH ℤ (TopCat.toSSet.obj V.X) 8 N.q2 V.c

/-! ## The Pontryagin–Thom class of a manifold -/

/-- **The Pontryagin–Thom data of `V` relative to a universal Thom target `D`.**

The geometric content (embedding, normal bundle, tubular neighbourhood, collapse, Gauss map) enters
through `α` and the two pairing fields; `normal` is the normal bundle of the embedding, with the
Whitney relation to the tangent bundle.  Everything else in this chapter is proved from this data.

* `α` is the class of the composite `S^{8+k} → Th(ν) → T` of the collapse along the tubular
  neighbourhood with the map induced by the Gauss map `V → G̃r_k(ℝ^{k+m})` classifying `ν`;
* `hurewicz_p1sq`, `hurewicz_p2` say that the Hurewicz pairing of `α` with `p₁²U` and `p₂U` computes
  the **normal** Pontryagin numbers — this is the Thom isomorphism, and it is the reason the
  Pontryagin numbers enter *on the manifold itself*, so no topological invariance of Pontryagin
  classes is needed. -/
structure PTRep (V : Man8) (k : ℕ) (D : ThomTarget k) where
  /-- the normal bundle of the embedding -/
  normal : NormalBundlData V
  /-- the **collapse map** `S^{k+8} → T` of the construction (collapse along a tubular
  neighbourhood of `V ⊂ ℝ^{8+k}`, composed with the map `Th(ν) → T` induced by the Gauss map
  classifying `ν`), recorded in the cube model of the homotopy groups: `GenLoop (Fin (k+8)) D.T D.t₀`
  is a continuous map `I^{k+8} → T` which is constant at `t₀` on the boundary — i.e. a based map
  from the `(k+8)`-sphere. -/
  collapse : GenLoop (Fin (k + 8)) D.T D.t₀
  /-- the Hurewicz pairing of `α_V` with `p₁²U` is the normal `p₁²`-number -/
  hurewicz_p1sq : kronH ℤ (ssetOf D.T) (k + 8) D.p1sqU
      (hurewiczClassOf (k + 8) (one_le_add_eight k) D.t₀ (Quotient.mk _ collapse))
    = normal.normalP1Sq
  /-- the Hurewicz pairing of `α_V` with `p₂U` is the normal `p₂`-number -/
  hurewicz_p2 : kronH ℤ (ssetOf D.T) (k + 8) D.p2U
      (hurewiczClassOf (k + 8) (one_le_add_eight k) D.t₀ (Quotient.mk _ collapse))
    = normal.normalP2

/-- The **Pontryagin–Thom class** `α_V ∈ π_{k+8}(T)`: the class of the collapse map. -/
def PTRep.α {V : Man8} {k : ℕ} {D : ThomTarget k} (r : PTRep V k D) :
    HomotopyGroup (Fin (k + 8)) D.T D.t₀ :=
  Quotient.mk _ r.collapse

/-- `PTRep.α` is the class of the collapse map (definitional unfolding). -/
theorem PTRep.α_eq {V : Man8} {k : ℕ} {D : ThomTarget k} (r : PTRep V k D) :
    r.α = Quotient.mk _ r.collapse := rfl

/-! ## Families -/

/-- **The Pontryagin–Thom class of a finite family of manifolds.**

`additivity` (item 3 of the chapter): the collapse class of the disjoint union of the family is the
"sum" of the classes of the pieces, so the Hurewicz pairings *add*.  No manifold structure on a
disjoint union is needed — exactly as in `Work.ThomBordism.NullBordismFamily`, the disjoint union
is represented by the *index type*. -/
structure PTFamilyRep (ι : Type) [Fintype ι] (F : ι → Man8) (k : ℕ) (D : ThomTarget k) where
  /-- the collapse map of the disjoint union of the family (in the cube model) -/
  collapse : GenLoop (Fin (k + 8)) D.T D.t₀
  /-- the pairing with `p₁²U` is the sum of the normal `p₁²`-numbers -/
  hurewicz_p1sq : kronH ℤ (ssetOf D.T) (k + 8) D.p1sqU
      (hurewiczClassOf (k + 8) (one_le_add_eight k) D.t₀ (Quotient.mk _ collapse))
    = ∑ i, (F i).p1Sq
  /-- the pairing with `p₂U` is the sum of the normal `p₂`-numbers -/
  hurewicz_p2 : kronH ℤ (ssetOf D.T) (k + 8) D.p2U
      (hurewiczClassOf (k + 8) (one_le_add_eight k) D.t₀ (Quotient.mk _ collapse))
    = ∑ i, ((F i).p1Sq - (F i).p2Num)

/-- The **Pontryagin–Thom class of the family**: the class of the collapse map of the disjoint
union. -/
def PTFamilyRep.α {ι : Type} [Fintype ι] {F : ι → Man8} {k : ℕ} {D : ThomTarget k}
    (r : PTFamilyRep ι F k D) : HomotopyGroup (Fin (k + 8)) D.T D.t₀ :=
  Quotient.mk _ r.collapse

/-- `PTFamilyRep.α` is the class of the collapse map (definitional unfolding). -/
theorem PTFamilyRep.α_eq {ι : Type} [Fintype ι] {F : ι → Man8} {k : ℕ} {D : ThomTarget k}
    (r : PTFamilyRep ι F k D) : r.α = Quotient.mk _ r.collapse := rfl

/-! ## The two geometric inputs, and the assembly's hypotheses -/

/-- **Item 1: the Pontryagin–Thom construction exists.**  For every closed oriented smooth
`8`-manifold `V` there is an embedding `V ↪ ℝ^{8+k}`, normal bundle, tubular neighbourhood, Gauss
map and collapse, with the two Hurewicz pairings computing the normal numbers.  (The embedding
theorem for compact manifolds is in Mathlib; the tubular neighbourhood theorem and the collapse are
not, so this is stated as a hypothesis — the *only* place the construction enters.) -/
def PTExists (k : ℕ) (D : ThomTarget k) : Prop := ∀ V : Man8, Nonempty (PTRep V k D)

/-- **Item 3 (additivity over families).**  The class of a finite family exists as soon as each
piece has one: the collapse class of the disjoint union is the sum of the collapse classes of the
pieces, and the Hurewicz pairing is additive. -/
def PTAdditivity (k : ℕ) (D : ThomTarget k) : Prop :=
  ∀ (ι : Type) [Fintype ι] (F : ι → Man8),
    (∀ i, Nonempty (PTRep (F i) k D)) → Nonempty (PTFamilyRep ι F k D)

/-- **(c) Transversality, single manifold.**  If a positive multiple of the Pontryagin–Thom class
of `V` is null-homotopic, then a positive multiple of the family consisting of `V` alone bounds:
the null-homotopy `D^{9+k} → T` of a multiple of the collapse map, made transverse to the zero
section of the universal bundle, pulls back a compact oriented `9`-manifold `W` with `∂W = N·V`
(and its relative fundamental class).  This is the sibling chapter `Transversality`'s output. -/
def Transversality (k : ℕ) (D : ThomTarget k) : Prop :=
  ∀ (V : Man8) (r : PTRep V k D),
    (∃ N : ℕ, 0 < N ∧ r.α ^ N = 1) →
      ∃ N : ℕ, 0 < N ∧ Nonempty (NullBordismFamily (Fin N) (fun _ => V))

/-- **(c) Transversality, family form**: the same for the Pontryagin–Thom class of a finite family,
giving a null-bordism of a positive multiple of the family. -/
def TransversalityFamily (k : ℕ) (D : ThomTarget k) : Prop :=
  ∀ (ι : Type) [Fintype ι] (F : ι → Man8) (r : PTFamilyRep ι F k D),
    (∃ N : ℕ, 0 < N ∧ r.α ^ N = 1) →
      ∃ N : ℕ, 0 < N ∧ Nonempty (NullBordismFamily (Fin N × ι) (fun x => F x.2))

/-- The three geometric inputs of the chapter, bundled: item 1 (`PTExists`), item 3
(`PTAdditivity`) and the transversality chapter (`Transversality`, `TransversalityFamily`). -/
structure PTInputs (k : ℕ) (D : ThomTarget k) where
  /-- item 1 -/
  exists_rep : PTExists k D
  /-- item 3 -/
  additivity : PTAdditivity k D
  /-- transversality, single -/
  transversality : Transversality k D
  /-- transversality, families -/
  transversalityFamily : TransversalityFamily k D

end

end Work.ThomBordism.PontryaginThom
