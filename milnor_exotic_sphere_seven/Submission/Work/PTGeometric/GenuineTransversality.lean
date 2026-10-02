import Submission.Work.PTGeometric.Genuine
import Submission.Work.ThomBordism.familyAssembly

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# PTGEOMETRIC: the genuine transversality statement (G6), and its two forms

This file contains the two equivalent shapes of the geometric input of the crux, and the reductions
between them and the chapter's `TransversalityFamily`.

## The genuine statement (G6)

`Work.PTGeometric.GenuineTransversality k D` is the honest form of "the null-homotopy of the genuine
collapse map of a multiple of the family gives a null-bordism":

> for every finite family `Fam : ι → Man8`, every choice of normal-bundle data `Nd` of the pieces,
> every choice of the **genuine** Pontryagin–Thom collapse data `Work.Tubular.TubeThomRep` of the
> pieces (i.e. the collapse map of the tubular neighbourhood of the embedding `Fam i ⊂ ℝ^{8+k}`
> followed by the Gauss map into `Th(γ_k)`, with its two Hurewicz pairings), and every `m > 0`, if
> the `m`-th power of the **product** of the pieces' collapse classes (the class of the `m`-fold
> collapse map of the disjoint union — the Pontryagin–Thom class of `m` copies of the family, see
> `Work.ThomBordism.PontryaginThom.ptAdditivity`) is trivial in `π_{8+k}(T)`, then a positive
> multiple of the family bounds.

The crucial difference from `Work.ThomBordism.PontryaginThom.TransversalityFamily k D` is that the
latter quantifies over an **arbitrary** `PTFamilyRep` — an arbitrary loop in `π_{8+k}(T)` whose two
Hurewicz pairings happen to be those of the family — so as a hypothesis it is as strong as the target
itself (the project lead's note in `familyAssembly.lean`).  Here the class is that of the *genuine*
collapse data, which is what the geometric construction actually produces.  Formally
`genuineTransversality_of_family` shows that `TransversalityFamily k D → GenuineTransversality k D`,
so the hypothesis below is *weaker* (hence more honest) than the chapter's.

## The geometric realisation

`Work.PTGeometric.GenuineRealisation n k D` realises the statement geometrically: the manifold part
`X` of the Thom space with its zero section as core (a `LocalCoreTarget`, which for the non-trivial
universal bundle is *not* a `CoreTarget` — see `Defs.lean`), and, for every family, every choice of
genuine collapse data and every `m > 0` with trivial `m`-th power, the smooth null-homotopy
(`GenuineNullBordismData`): the smooth map from the disk with holes, transverse to the zero section,
with the ends identified with the pieces and with the orientation datum of the situation.
`genuineTransversality_of_realisation` derives G6 from it — via the local preimage theorem and the
orientation theory (`exists_nullBordismFamily_of_genuineData`).

## Main definitions

* `Work.PTGeometric.tubeAlpha` — the class of a `TubeThomRep` in `π_{8+k}(T)`
* `Work.PTGeometric.GenuineTransversality` — G6, the class form of the geometric input
* `Work.PTGeometric.GenuineRealisation` — the geometric (data) form

## Main results

* `Work.PTGeometric.exists_ptFamilyRep_of_parts` — additivity with an *explicit* input, so that the
  class of the family rep is visibly the product of the pieces' classes
* `Work.PTGeometric.genuineTransversality_of_realisation` — the geometric form implies G6
* `Work.PTGeometric.genuineTransversality_of_family` — the chapter's `TransversalityFamily` implies
  G6 (G6 is the weaker, honest hypothesis)
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open scoped Manifold ContDiff Topology Topology.Homotopy unitInterval
open Function Set Topology Manifold Filter
open CategoryTheory AlgebraicTopology
open Work.ThomBordism.PontryaginThom

namespace Work.PTGeometric

noncomputable section

open Work.ThomBordism
open Work.Cohomology

/-- **The Pontryagin–Thom class of a genuine collapse datum** (a `Work.Tubular.TubeThomRep`): the
class in `π_{8+k}(T)` of the collapse map of the tubular neighbourhood composed with the Gauss map. -/
def tubeAlpha {k : ℕ} {D : ThomTarget k} {V : Man8}
    {Nd : NormalBundlData V} (r : Work.Tubular.TubeThomRep k D V Nd) :
    HomotopyGroup (Fin (k + 8)) D.T D.t₀ :=
  Quotient.mk _ r.collapse

/-- `tubeAlpha` of a genuine collapse datum is the Pontryagin–Thom class of the `PTRep` it
determines. -/
theorem tubeAlpha_eq_ptRep {k : ℕ} {D : ThomTarget k} {V : Man8}
    {Nd : NormalBundlData V} (r : Work.Tubular.TubeThomRep k D V Nd) :
    tubeAlpha r = (Work.ThomBordism.ptRepOfTubeThomRep r).α := rfl

/-- **G6 — the genuine transversality statement of the Pontryagin–Thom construction.**

For a finite family of closed oriented `8`-manifolds, genuine normal-bundle and collapse data of its
members (the tubular neighbourhood of each piece in `ℝ^{8+k}` and its collapse map, from TUBULAR) and
`m > 0`: if the `m`-th power of the product of the pieces' collapse classes — i.e. the Pontryagin–Thom
class of the `m`-fold disjoint union, `ptAdditivity` — is trivial in `π_{8+k}(T)`, then a positive
multiple of the family is a boundary.

This is the statement the geometric construction has to supply: make the null-homotopy of the `m`-fold
genuine collapse map smooth and transverse to the zero section of `γ_k`, and take the preimage
(G0–G5 of the blueprint).  Since the class is that of the *genuine* collapse data, this is strictly
weaker than `Work.ThomBordism.PontryaginThom.TransversalityFamily` (see
`genuineTransversality_of_family`). -/
def GenuineTransversality (k : ℕ) (D : ThomTarget k) : Prop :=
  letI : Nonempty (Fin (k + 8)) := ⟨⟨0, by omega⟩⟩
  letI : Nontrivial (Fin (k + 8)) := ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp⟩
  letI : CommMonoid (Quotient (GenLoop.Homotopic.setoid (Fin (k + 8)) D.t₀)) :=
    inferInstanceAs (CommMonoid (HomotopyGroup (Fin (k + 8)) D.T D.t₀))
  ∀ (ι : Type) [Fintype ι] (Fam : ι → Man8)
    (Nd : ∀ i, NormalBundlData (Fam i))
    (r : ∀ i, Work.Tubular.TubeThomRep k D (Fam i) (Nd i))
    (m : ℕ), 0 < m → (∏ i, tubeAlpha (r i)) ^ m = 1 →
      ∃ N' : ℕ, 0 < N' ∧ Nonempty (NullBordismFamily (Fin N' × ι) (fun x => Fam x.2))

/-! ## Additivity with an explicit input

`Work.ThomBordism.PontryaginThom.ptAdditivity` is proved with a `Nonempty` input, so the class of its
output is the product of `Classical.choice`s of the pieces' data.  For the assembly below we need the
same construction with the pieces' data supplied *explicitly*, so that the class of the family
representative is *visibly* the product of the pieces' classes (the hypothesis of
`GenuineTransversality`).  The proof is the one of `ptAdditivity`. -/

/-- **Additivity over families, with an explicit input.**  Given a Pontryagin–Thom representative of
every member of a finite family, there is one for the disjoint union whose class is the product of the
pieces' classes. -/
theorem exists_ptFamilyRep_of_parts {k : ℕ} {D : ThomTarget k} {ι : Type} [Fintype ι]
    {F : ι → Man8} (r : ∀ i, PTRep (F i) k D) :
    ∃ ρ : PTFamilyRep ι F k D, ρ.α = ∏ i, (r i).α := by
  classical
  haveI : Nonempty (Fin (k + 8)) := ⟨⟨0, by omega⟩⟩
  haveI : Nontrivial (Fin (k + 8)) := ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp⟩
  haveI : CommMonoid (Quotient (GenLoop.Homotopic.setoid (Fin (k + 8)) D.t₀)) :=
    inferInstanceAs (CommMonoid (HomotopyGroup (Fin (k + 8)) D.T D.t₀))
  let α : HomotopyGroup (Fin (k + 8)) D.T D.t₀ := ∏ i, (r i).α
  refine ⟨{ collapse := Quotient.out α, hurewicz_p1sq := ?_, hurewicz_p2 := ?_ }, ?_⟩
  · rw [show (Quotient.mk _ (Quotient.out α) : HomotopyGroup (Fin (k + 8)) D.T D.t₀) = α from
        Quotient.out_eq α,
      hurewiczClassOf_prod (T := D.T) (t₀ := D.t₀) (n := k + 8) (one_le_add_eight k)
        (fun i => (r i).α), map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show kronH ℤ (ssetOf D.T) (k + 8) D.p1sqU
          (hurewiczClassOf (k + 8) (one_le_add_eight k) D.t₀ (r i).α)
        = (r i).normal.normalP1Sq from (r i).hurewicz_p1sq]
    exact (r i).normal.normalP1Sq_eq
  · rw [show (Quotient.mk _ (Quotient.out α) : HomotopyGroup (Fin (k + 8)) D.T D.t₀) = α from
        Quotient.out_eq α,
      hurewiczClassOf_prod (T := D.T) (t₀ := D.t₀) (n := k + 8) (one_le_add_eight k)
        (fun i => (r i).α), map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show kronH ℤ (ssetOf D.T) (k + 8) D.p2U
          (hurewiczClassOf (k + 8) (one_le_add_eight k) D.t₀ (r i).α)
        = (r i).normal.normalP2 from (r i).hurewicz_p2]
    exact (r i).normal.normalP2_eq
  · exact (Quotient.out_eq α).trans rfl

/-! ## The geometric realisation -/

/-- **The geometric realisation of the genuine Pontryagin–Thom class of a family.**

* `X` — the manifold part of the universal Thom space `T = Th(γ_k)` away from the base point, with
  the zero section as core, as a `LocalCoreTarget` (the honest local form: for the non-trivial
  universal bundle there is *no* global defining function of the core, see `Defs.lean`);
* `collapse` — for every finite family, every choice of normal-bundle data and of **genuine** collapse
  data of the pieces (TUBULAR's `TubeThomRep`), and every `m > 0` with the `m`-th power of the product
  of the pieces' classes trivial, the geometric null-homotopy: the smooth map from the disk with `m·|ι|`
  holes into `X.E`, transverse to the core, with the ends identified with the pieces and with the
  orientation datum of the situation (`GenuineNullBordismData`).

This is G0–G5 of the blueprint in the form of *data*: G0 (the `m`-fold disjoint union as one embedded
manifold, whose collapse class is the product) is what produces the index set `Fin m × ι`, G1–G3 are
what produce the smooth transverse representative, and G4–G5 are the preimage and its orientation. -/
structure GenuineRealisation (n k : ℕ) (D : ThomTarget k) where
  /-- the manifold part of the Thom space, with the zero section as core -/
  X : LocalCoreTarget n k
  /-- the geometric realisation of a null-homotopy of a multiple of the genuine collapse class -/
  collapse : ∀ (ι : Type) [Fintype ι] (Fam : ι → Man8)
      (Nd : ∀ i, NormalBundlData (Fam i))
      (r : ∀ i, Work.Tubular.TubeThomRep k D (Fam i) (Nd i)) (m : ℕ),
    0 < m → (∏ i, tubeAlpha (r i)) ^ m = 1 →
      GenuineNullBordismData n k X (Fin m × ι) (fun x => Fam x.2)

/-- **G6 from the geometric realisation.**  The smooth transverse null-homotopy of the `m`-fold
genuine collapse map, together with the local preimage theorem and the orientation datum of the
situation, gives the null-bordism: `exists_nullBordismFamily_of_genuineData` applied to the
realisation. -/
theorem genuineTransversality_of_realisation (hpre : LocalPreimageTheorem) {n k : ℕ}
    {D : ThomTarget k} (R : GenuineRealisation n k D) : GenuineTransversality k D := by
  intro ι _ Fam Nd r m hm hpow
  exact ⟨m, hm,
    exists_nullBordismFamily_of_genuineData hpre (R.collapse ι Fam Nd r m hm hpow)⟩

/-- **The chapter's `TransversalityFamily` implies G6.**  The genuine statement quantifies over the
genuine collapse data only, so it is a *specialisation* of the chapter's (which quantifies over an
arbitrary loop with the family's pairings) — i.e. G6 is the weaker, honest hypothesis, and the
assembly below is not circular. -/
theorem genuineTransversality_of_family {k : ℕ} {D : ThomTarget k}
    (h : TransversalityFamily k D) : GenuineTransversality k D := by
  intro ι _ Fam Nd r m hm hpow
  haveI : Nonempty (Fin (k + 8)) := ⟨⟨0, by omega⟩⟩
  haveI : Nontrivial (Fin (k + 8)) := ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp⟩
  obtain ⟨ρ, hρα⟩ := exists_ptFamilyRep_of_parts (fun i => ptRepOfTubeThomRep (r i))
  have hpow' : ρ.α ^ m = 1 := by
    rw [hρα]
    exact hpow
  exact h ι Fam ρ ⟨m, hm, hpow'⟩

end

end Work.PTGeometric
