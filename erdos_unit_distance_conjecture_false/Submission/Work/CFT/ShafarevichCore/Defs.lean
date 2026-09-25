import Mathlib
import Submission.Work.CFT.Kummer.All
import Submission.Work.Tower.Shafarevich.Estimate

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-!
# `Work.CFT.ShafarevichCore`: the primitive arithmetic facts of Shafarevich's estimate

This area contains the **core** of Shafarevich's relation-rank estimate: the two classical
arithmetic facts of Koch's *Galois theory of p-extensions*, Chapter 11, from which the estimate
`Work.Tower.Shafarevich.H2Estimate` is deduced, together with everything that can be proved
without them.

The whole project (see `Submission/Work/CFT/README.md`) is reduced, sorry-free, to the single
statement `Work.CFT.ShafarevichTarget : Prop = ∃ C₀, H2Estimate C₀`.  The areas `CFT/Local`,
`CFT/Kummer`, `CFT/MainTheorem` and `CFT/IdeleClassGroup` have already carried out the
*linear-algebra* and *cohomological* reductions; what they leave open is exactly the pair of
arithmetic facts isolated here, **stated for the maximal everywhere-unramified pro-`p` group
`G = Gal(F_∅(p)/F)` of a number field `F`**:

* **(a) `ShafarevichInjection F p G`** — Koch's *Shafarevich injection*
  `Ш²_∅ = H²(G, 𝔽_p) ↪ 𝓒_∅` of the `H²` of `G` into the Kummer character group
  `𝓒_∅ = Hom(V_∅/F^{×p}, 𝔽_p)`
  (Koch, *Galois theory of p-extensions*, Ch. 11; Neukirch–Schmidt–Wingberg, *Cohomology of
  Number Fields*, Ch. X §10; equivalently the Hasse principle for the `p`-torsion of the Brauer
  group of `F` restricted to classes unramified everywhere);

* **(b′) `ClassRankFormula F p G`** — the *class-group rank formula*
  `dim_{𝔽_p} H¹(G, 𝔽_p) = dim_{𝔽_p} Cl_F[p]`, i.e. the Hilbert class field correspondence for
  everywhere-unramified abelian `p`-extensions (Artin reciprocity in the unramified case,
  Hilbert's theorem 94): the maximal everywhere-unramified abelian `p`-extension of `F` has
  Galois group `Cl_F ⊗ ℤ_p`.

Given (a) and (b′) the estimate follows by the *already proved* Kummer computation
`Work.CFT.Kummer.finrank_kummerDual_empty`
(`dim 𝓒_∅ = dim Cl_F[p] + (r₁+r₂-1) + δ_{F,p}`) and elementary linear algebra — see
`Work.CFT.ShafarevichCore.finrank_H2Fp_le_H1Fp_add`.  The rank formula (b) of Koch is *not* an
additional input: it is equivalent to (b′) given that computation
(`Work.CFT.ShafarevichCore.classRank_iff_kummerRank`).

## Main definitions

* `Work.CFT.ShafarevichCore.ShafarevichInjection` — Koch's fact (a).
* `Work.CFT.ShafarevichCore.ClassRankFormula` — Koch's fact (b′).
* `Work.CFT.ShafarevichCore.KummerRankFormula` — Koch's H¹ rank formula (b).
* `Work.CFT.ShafarevichCore.CoreFacts` — (a) together with (b′).
* `Work.CFT.ShafarevichCore.ArtinAbelianRank` — the finer form of (b′): the maximal unramified
  abelian `p`-quotient of `G` is the `p`-part of the class group.
* `Work.CFT.ShafarevichCore.pTorsion` — the `p`-torsion subgroup of a commutative group.
* `Work.CFT.ShafarevichCore.SplittingCut` — the cutting of the Frobenius elements at a splitting
  set `T` (the group-theoretic form of the `+ |T|` term).
* `Work.CFT.ShafarevichCore.ShafarevichCoreInput` — the full localized input of the tower.

## Convention

Throughout, `F` is a number field and `G` an abstract group modelling the **maximal**
everywhere-unramified pro-`p` group `Gal(F_∅(p)/F)`.  All the `Prop`s below are stated only for
that maximal group: the estimate is *false* without maximality (see `README.md`).
-/

open NumberField
open scoped Classical nonZeroDivisors

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Work.CFT.ShafarevichCore

/-! ## Re-exported vocabulary -/

/-- `H¹(G, 𝔽_p)` with trivial coefficients (re-export of `Work.Tower.Shafarevich.H1Fp`). -/
abbrev H1Fp (p : ℕ) (G : Type) [Group G] : ModuleCat (ZMod p) :=
  Work.Tower.Shafarevich.H1Fp p G

/-- `H²(G, 𝔽_p)` with trivial coefficients (re-export of `Work.Tower.Shafarevich.H2Fp`). -/
abbrev H2Fp (p : ℕ) (G : Type) [Group G] : ModuleCat (ZMod p) :=
  Work.Tower.Shafarevich.H2Fp p G

/-- The Kummer character group `𝓒_∅ = Hom(V_∅/F^{×p}, 𝔽_p)`
(re-export of `Work.CFT.Kummer.kummerDual`). -/
abbrev kummerDual (F : Type*) [Field F] [NumberField F] (p : ℕ)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) : Type _ :=
  Work.CFT.Kummer.kummerDual F p S

/-- The `p`-torsion `Cl_F[p]` of the class group (re-export of
`Work.CFT.Kummer.classGroupTorsion`). -/
abbrev classGroupTorsion (F : Type*) [Field F] [NumberField F] (p : ℕ) : Type _ :=
  Work.CFT.Kummer.classGroupTorsion F p

/-! ## The `p`-torsion of a commutative group -/

/-- The **`p`-torsion subgroup** `A[p] = {a | p • a = 0}` of an additive commutative group. -/
def pTorsion (p : ℕ) (A : Type*) [AddCommGroup A] : AddSubgroup A where
  carrier := {a | p • a = 0}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [smul_add, ha, hb, add_zero]
  zero_mem' := by simp only [Set.mem_ofPred_eq, smul_zero]
  neg_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at ha ⊢
    rw [smul_neg, ha, neg_zero]

theorem mem_pTorsion {p : ℕ} {A : Type*} [AddCommGroup A] {a : A} :
    a ∈ pTorsion p A ↔ p • a = 0 := Iff.rfl

/-- The `𝔽_p`-vector space structure on the `p`-torsion subgroup. -/
instance instModulePTorsion (p : ℕ) (A : Type*) [AddCommGroup A] :
    Module (ZMod p) (pTorsion p A) :=
  AddCommGroup.zmodModule (fun x => by
    have h : p • (x : A) = 0 := x.2
    exact Subtype.ext h)

/-! ## Koch's two arithmetic facts -/

/-- **(a) Koch's Shafarevich injection.**  The second cohomology of the maximal
everywhere-unramified pro-`p` group `G = Gal(F_∅(p)/F)` with trivial `𝔽_p` coefficients injects
into the Kummer character group `𝓒_∅ = Hom(V_∅/F^{×p}, 𝔽_p)`:

`Ш²_∅ = H²(G, 𝔽_p) ↪ 𝓒_∅`.

(Koch, *Galois theory of p-extensions*, Ch. 11; Neukirch–Schmidt–Wingberg, *Cohomology of number
fields*, Ch. X §10.)  This is a classical theorem; it is isolated here as the *first* of the two
primitive inputs of the estimate. -/
def ShafarevichInjection (F : Type*) [Field F] [NumberField F] (p : ℕ) (G : Type) [Group G] :
    Prop :=
  ∃ (sha : H2Fp p G →ₗ[ZMod p] kummerDual F p ∅), Function.Injective sha

/-- **(b′) The class-group rank formula.**  The generator rank of the maximal
everywhere-unramified pro-`p` group `G = Gal(F_∅(p)/F)` is the `p`-rank of the class group:

`dim_{𝔽_p} H¹(G, 𝔽_p) = dim_{𝔽_p} Cl_F[p]`.

Equivalently (Hilbert's theorem 94 / Artin reciprocity for unramified abelian extensions), the
maximal everywhere-unramified abelian `p`-extension of `F` has Galois group `Cl_F ⊗ ℤ_p`, and its
generator rank is `dim_{𝔽_p} Cl_F[p]`.  This is a classical theorem; it is isolated here as the
*second* primitive input of the estimate. -/
def ClassRankFormula (F : Type*) [Field F] [NumberField F] (p : ℕ) (G : Type) [Group G] :
    Prop :=
  Module.finrank (ZMod p) (H1Fp p G) = Module.finrank (ZMod p) (classGroupTorsion F p)

/-- **(b) Koch's H¹ rank formula.**  With `S = ∅` Koch's Chapter 11 formula reads

`dim_{𝔽_p} 𝓒_∅ = dim_{𝔽_p} H¹(G, 𝔽_p) + (r₁ + r₂ - 1) + δ_{F,p}`,

where `r₁ + r₂ - 1 = NumberField.Units.rank F` and `δ_{F,p} = Work.CFT.Kummer.deltaK F p`.  The
Kummer half of this (`dim 𝓒_∅ = dim Cl_F[p] + (r₁+r₂-1) + δ_{F,p}`) is *proved* in
`Work.CFT.Kummer.finrank_kummerDual_empty`; the formula itself is equivalent to (b′)
(`classRank_iff_kummerRank`). -/
def KummerRankFormula (F : Type*) [Field F] [NumberField F] (p : ℕ) (G : Type) [Group G] :
    Prop :=
  Module.finrank (ZMod p) (kummerDual F p ∅) =
    Module.finrank (ZMod p) (H1Fp p G) + NumberField.Units.rank F +
      Work.CFT.Kummer.deltaK F p

/-- **The core hypothesis**: Koch's facts (a) and (b′) for the maximal everywhere-unramified
pro-`p` group `G` of `F`.  This is the whole arithmetic content of Shafarevich's relation-rank
estimate at `S = ∅`; everything else is proved in this development. -/
def CoreFacts (F : Type*) [Field F] [NumberField F] (p : ℕ) (G : Type) [Group G] : Prop :=
  ShafarevichInjection F p G ∧ ClassRankFormula F p G

theorem CoreFacts.injection {F : Type*} [Field F] [NumberField F] {p : ℕ} {G : Type} [Group G]
    (h : CoreFacts F p G) : ShafarevichInjection F p G := h.1

theorem CoreFacts.classRank {F : Type*} [Field F] [NumberField F] {p : ℕ} {G : Type} [Group G]
    (h : CoreFacts F p G) : ClassRankFormula F p G := h.2

/-- **(b′), finer form (the Artin / Hilbert class field statement).**  The generator rank of `G`
equals the number of generators of the `p`-part of the class group, equivalently the `𝔽_p`-rank of
the dual `Hom(Cl_F, 𝔽_p)`:

`dim_{𝔽_p} H¹(G, 𝔽_p) = dim_{𝔽_p} Hom(Cl_F, 𝔽_p)`.

The passage between this and `ClassRankFormula` is pure finite-abelian-group theory
(`Work.CFT.ShafarevichCore.finrank_hom_zmod_eq_finrank_pTorsion`), so `ArtinAbelianRank` isolates
the *arithmetic* content of (b′) — the Hilbert class field correspondence — from the group theory. -/
def ArtinAbelianRank (F : Type*) [Field F] [NumberField F] (p : ℕ) (G : Type) [Group G] : Prop :=
  Module.finrank (ZMod p) (H1Fp p G) =
    Module.finrank (ZMod p) (Additive (ClassGroup (𝓞 F)) →+ ZMod p)

end Work.CFT.ShafarevichCore
