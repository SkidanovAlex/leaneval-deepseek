import Mathlib
import Submission.Work.Cohomology.relCapH_kronH_cup
import Submission.Work.Cohomology.sph3DiscMixedDefs
import Submission.Work.Cohomology.gradedComm
import Submission.Work.Cohomology.cup1Cast
import Submission.Work.Cohomology.capPair_cup

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The mixed cap/cup adjunction (piece B1 of the Pontryagin–Thom pairing)

`Work.Cohomology.relCapH_kronH_cup` proves the *relative × relative* cap/cup adjunction

  `⟨β, α ⌢ c⟩ = ⟨α ⌣ β, c⟩`

on a pair `(X,A)`.  The Pontryagin–Thom pairing of the tubular chapter
(`Work.Tubular.kronH_alphaV_pairings`, `Submission/Work/Tubular/Pairing.lean`) instead needs the
**mixed** form, in which the cohomology factor paired with the cap product is an **absolute** class
`x ∈ H^q(X)`, while the cap product is taken with a **relative** class `β ∈ H^p(X,A)` and a relative
homology class `c ∈ H_{p+q}(X,A)` (the fundamental class of the disc bundle pair):

  `⟨x, β ⌢ c⟩ = ⟨x ⌣ β, c⟩`.

The two products `β ⌣ x` and `x ⌣ β` differ by the graded sign `(-1)^{p·q}`
(`Work.Cohomology.cup1Identity` / `Work.Cohomology.gradedComm`), so the statement carries the
hypothesis `Even (p * q)`; the application has `q = 8`.  This is the general form of
`Work.Cohomology.sph3Disc_relCapPair_kronH_mixed` (there `p = 4`, `q = 3`, both degrees numeric).

## Contents

* `Work.Tubular.kronH_cast_left` / `kronH_cast_sing` — the Kronecker pairing commutes with the
  transport of its arguments along an equality of degrees.
* **`Work.Tubular.kronecker_cap_cup_comm_gen`** — the chain-level mixed cap/cup identity in general
  degrees.
* **`Work.Tubular.kronH_mixedCup_relCapPair`** — the adjunction.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Tubular

noncomputable section

open Work.Cohomology

/-! ## Transport of the Kronecker pairing along a change of degrees -/

/-- **The Kronecker pairing commutes with the transport of its arguments along an equality of
degrees.** -/
lemma kronH_cast_left {X : SSet} {a b : ℕ} (h : a = b)
    (γ : (cochainC ℤ X).homology a) (z : (chainC ℤ X).homology b) :
    kronH ℤ X b (h ▸ γ) z = kronH ℤ X a γ (h.symm ▸ z) := by
  cases h
  rfl

/-- The same, in the spelling of the singular chains of a topological space. -/
lemma kronH_cast_sing {X : TopCat} {a b : ℕ} (h : a = b)
    (γ : (singularCochainComplex ℤ X).homology a) (z : (singularChains ℤ X).homology b) :
    kronH ℤ (TopCat.toSSet.obj X) b (h ▸ γ) z
      = kronH ℤ (TopCat.toSSet.obj X) a γ (h.symm ▸ z) :=
  kronH_cast_left h γ z

section Transport

/-- The cycle inclusion commutes with the transport of cycles along an equality of degrees
(the `singularChains` spelling of `Work.Cohomology.iCycles_cycles_cast`). -/
lemma iCycles_cast_sing {X : TopCat} {a b : ℕ} (h : a = b)
    (w : (singularChains ℤ X).cycles a) :
    ((singularChains ℤ X).iCycles b) (h ▸ w) = h ▸ (((singularChains ℤ X).iCycles a) w) :=
  iCycles_cycles_cast ℤ (TopCat.toSSet.obj X) h w

/-- The homology projection commutes with the transport of cycles along an equality of degrees
(the `singularChains` spelling of `Work.Cohomology.homologyπ_cycles_cast`). -/
lemma homologyπ_cast_sing {X : TopCat} {a b : ℕ} (h : a = b)
    (w : (singularChains ℤ X).cycles a) :
    h ▸ (((singularChains ℤ X).homologyπ a) w)
      = ((singularChains ℤ X).homologyπ b) (h ▸ w) :=
  homologyπ_cycles_cast ℤ (TopCat.toSSet.obj X) h w

end Transport

/-! ## The chain-level mixed cap/cup identity -/

/-- **The mixed cap/cup identity in general degrees, on the chain level.**  For an absolute cocycle
`a` of degree `q`, a relative cocycle `u` of degree `p` and a *cycle* `w` of degree `p+q`, the
Kronecker pairing of `a` with the cap product of `u.1` with `w` equals the evaluation of the mixed
product `a ⌣ u.1` at `w` (transported to degree `p+q`).

The two products `u.1 ⌣ a` and `a ⌣ u.1` differ by the graded sign `(-1)^{p·q}`
(`Work.Cohomology.gradedComm`), which is `+1` under the hypothesis `Even (p * q)`. -/
lemma kronecker_cap_cup_comm_gen (X : TopCat) (A : Set X) (p q : ℕ) (hpq : Even (p * q))
    (a : Cochain ℤ (TopCat.toSSet.obj X) q) (ha : cochainDiff ℤ (TopCat.toSSet.obj X) a = 0)
    (u : relKern ℤ X A p) (hu : relDiffLM ℤ X A p u = 0)
    (w : (singularChains ℤ X).cycles (p + q)) :
    kronecker ℤ (TopCat.toSSet.obj X) a
        (cap ℤ (TopCat.toSSet.obj X) (u.1 : Cochain ℤ (TopCat.toSSet.obj X) p) q
          (((singularChains ℤ X).iCycles (p + q)) w))
      = kronecker ℤ (TopCat.toSSet.obj X)
          ((Nat.add_comm q p) ▸
            (cup ℤ (TopCat.toSSet.obj X) a (u.1 : Cochain ℤ (TopCat.toSSet.obj X) p)))
          (((singularChains ℤ X).iCycles (p + q)) w) := by
  have hud : cochainDiff ℤ (TopCat.toSSet.obj X)
      (u.1 : Cochain ℤ (TopCat.toSSet.obj X) p) = 0 :=
    relClassOf_cochainDiff ℤ X A u hu
  have hab : cochainDiff ℤ (TopCat.toSSet.obj X)
      (cup ℤ (TopCat.toSSet.obj X) (u.1 : Cochain ℤ (TopCat.toSSet.obj X) p) a) = 0 :=
    cochainDiff_cup_of_cocycles ℤ (TopCat.toSSet.obj X) _ a hud ha
  have hba : cochainDiff ℤ (TopCat.toSSet.obj X)
      (cup ℤ (TopCat.toSSet.obj X) a (u.1 : Cochain ℤ (TopCat.toSSet.obj X) p)) = 0 :=
    cochainDiff_cup_of_cocycles ℤ (TopCat.toSSet.obj X) a _ ha hud
  have hba' : cochainDiff ℤ (TopCat.toSSet.obj X)
      ((Nat.add_comm q p) ▸
        (cup ℤ (TopCat.toSSet.obj X) a (u.1 : Cochain ℤ (TopCat.toSSet.obj X) p))) = 0 :=
    cochainDiff_cast ℤ (TopCat.toSSet.obj X) (Nat.add_comm q p) _ hba
  -- the cohomology classes of the two products differ by the graded sign
  have hgc := gradedComm ℤ (TopCat.toSSet.obj X) p q
    (cohomologyClassOf ℤ (TopCat.toSSet.obj X) (u.1 : Cochain ℤ (TopCat.toSSet.obj X) p) hud)
    (cohomologyClassOf ℤ (TopCat.toSSet.obj X) a ha)
  rw [cupH'_apply' ℤ (TopCat.toSSet.obj X) (u.1 : Cochain ℤ (TopCat.toSSet.obj X) p) a hud ha,
      cupH'_apply' ℤ (TopCat.toSSet.obj X) a (u.1 : Cochain ℤ (TopCat.toSSet.obj X) p) ha hud]
    at hgc
  rw [hpq.neg_one_pow, one_smul] at hgc
  -- so the two classes are equal after transporting to degree `p + q`
  have hcl : cohomologyClassOf ℤ (TopCat.toSSet.obj X)
        (cup ℤ (TopCat.toSSet.obj X) (u.1 : Cochain ℤ (TopCat.toSSet.obj X) p) a) hab
      = cohomologyClassOf ℤ (TopCat.toSSet.obj X)
        ((Nat.add_comm q p) ▸
          (cup ℤ (TopCat.toSSet.obj X) a (u.1 : Cochain ℤ (TopCat.toSSet.obj X) p))) hba' := by
    have h2 : cohomologyClassOf ℤ (TopCat.toSSet.obj X)
          (cup ℤ (TopCat.toSSet.obj X) (u.1 : Cochain ℤ (TopCat.toSSet.obj X) p) a) hab
        = (Nat.add_comm q p) ▸ cohomologyClassOf ℤ (TopCat.toSSet.obj X)
            (cup ℤ (TopCat.toSSet.obj X) a (u.1 : Cochain ℤ (TopCat.toSSet.obj X) p)) hba := by
      have h1 : (Nat.add_comm p q).symm ▸
            ((Nat.add_comm p q) ▸ cohomologyClassOf ℤ (TopCat.toSSet.obj X)
              (cup ℤ (TopCat.toSSet.obj X) (u.1 : Cochain ℤ (TopCat.toSSet.obj X) p) a) hab)
          = (Nat.add_comm p q).symm ▸ cohomologyClassOf ℤ (TopCat.toSSet.obj X)
              (cup ℤ (TopCat.toSSet.obj X) a (u.1 : Cochain ℤ (TopCat.toSSet.obj X) p)) hba := by
        rw [hgc]
      rw [eqRec_symm_eqRec_self3
        (M := fun k => (SSetCochainComplex ℤ (TopCat.toSSet.obj X)).homology k)
        (Nat.add_comm p q) _] at h1
      rw [show (Nat.add_comm p q).symm = (Nat.add_comm q p) from Subsingleton.elim _ _] at h1
      exact h1
    rw [cohomologyClassOf_cast ℤ (TopCat.toSSet.obj X) (Nat.add_comm q p) _ hba] at h2
    exact h2
  rw [kronecker_cap_cup]
  rw [show kronecker ℤ (TopCat.toSSet.obj X)
        (cup ℤ (TopCat.toSSet.obj X) (u.1 : Cochain ℤ (TopCat.toSSet.obj X) p) a)
        (((singularChains ℤ X).iCycles (p + q)) w)
      = kronH ℤ (TopCat.toSSet.obj X) (p + q)
          (cohomologyClassOf ℤ (TopCat.toSSet.obj X)
            (cup ℤ (TopCat.toSSet.obj X) (u.1 : Cochain ℤ (TopCat.toSSet.obj X) p) a) hab)
          (((singularChains ℤ X).homologyπ (p + q)) w)
    from (kronH_apply_sing X _ hab w).symm]
  rw [show kronecker ℤ (TopCat.toSSet.obj X)
        ((Nat.add_comm q p) ▸
          (cup ℤ (TopCat.toSSet.obj X) a (u.1 : Cochain ℤ (TopCat.toSSet.obj X) p)))
        (((singularChains ℤ X).iCycles (p + q)) w)
      = kronH ℤ (TopCat.toSSet.obj X) (p + q)
          (cohomologyClassOf ℤ (TopCat.toSSet.obj X)
            ((Nat.add_comm q p) ▸
              (cup ℤ (TopCat.toSSet.obj X) a (u.1 : Cochain ℤ (TopCat.toSSet.obj X) p))) hba')
          (((singularChains ℤ X).homologyπ (p + q)) w)
    from (kronH_apply_sing X _ hba' w).symm]
  rw [hcl]

/-! ## The cap/cup adjunction -/

/-- **The mixed cap/cup adjunction.**  For a pair `(X,A)`, an absolute class `x` of degree `q`, a
relative cohomology class `β` of degree `p`, and `c ∈ H_{p+q}(X,A)` a relative homology class with
absolute lift `c'` (i.e. `π c' = c` under the cokernel projection `C_*(X) → C_*(X,A)`):

`⟨x, β ⌢ c⟩ = ⟨x ⌣ β, c'⟩`

(the graded sign `(-1)^{pq}` is `+1` because `p*q` is even).  With `x` a characteristic class of
`V`, `β = U_ν` the Thom class of the normal bundle and `c` the fundamental class of the disc bundle
pair, this is step 5 of the classical chain in `PairingNotes.md` §2. -/
theorem kronH_mixedCup_relCapPair (X : TopCat) (A : Set X) (p q : ℕ) (hpq : Even (p * q))
    (x : (singularCochainComplex ℤ X).homology q)
    (beta : (relComplex ℤ X A).homology p)
    (c : (relChains X A).homology (p + q))
    (c' : (singularChains ℤ X).homology (p + q))
    (hc : HomologicalComplex.homologyMap
        (CategoryTheory.Limits.cokernel.π (inclChains X A)) (p + q) c' = c) :
    kronH ℤ (TopCat.toSSet.obj X) q x (relCapPair X A p q beta c)
      = kronH ℤ (TopCat.toSSet.obj X) (p + q)
          ((Nat.add_comm q p) ▸
            (HomologicalComplex.homologyMap (relIncl ℤ X A) (q + p)
              (mixedCup X A q p x beta))) c' := by
  suffices key : kronH ℤ (TopCat.toSSet.obj X) q x (relCapPair X A p q beta c)
      = kronH ℤ (TopCat.toSSet.obj X) (q + p)
          (HomologicalComplex.homologyMap (relIncl ℤ X A) (q + p)
            (mixedCup X A q p x beta))
          ((Nat.add_comm q p).symm ▸ c') by
    rw [key, kronH_cast_sing (Nat.add_comm q p)
      (HomologicalComplex.homologyMap (relIncl ℤ X A) (q + p) (mixedCup X A q p x beta)) c']
  obtain ⟨a, ha, rfl⟩ := exists_cohomologyClassOf ℤ (TopCat.toSSet.obj X) q x
  obtain ⟨u, hu, rfl⟩ := exists_relClassOf ℤ X A p beta
  obtain ⟨z', rfl⟩ :=
    (ModuleCat.epi_iff_surjective ((singularChains ℤ X).homologyπ (p + q))).mp inferInstance c'
  let zα : (relComplex ℤ X A).cycles p := relCocycleOf ℤ X A u hu
  let cc : (relChains X A).cycles (p + q) :=
    (HomologicalComplex.cyclesMap (CategoryTheory.Limits.cokernel.π (inclChains X A))
      (p + q)).hom z'
  have hza : ((relComplex ℤ X A).iCycles p).hom zα = u := iCycles_relCocycleOf ℤ X A u hu
  have hc_eq : c = ((relChains X A).homologyπ (p + q)) cc := by
    rw [← hc]
    exact homologyMap_homologyπ_chain (CategoryTheory.Limits.cokernel.π (inclChains X A)) (p + q) z'
  have hcyc : ((relChains X A).iCycles (p + q)) cc
      = ((CategoryTheory.Limits.cokernel.π (inclChains X A)).f (p + q))
          (((singularChains ℤ X).iCycles (p + q)) z') := by
    have h := congrArg
      (fun (g : (singularChains ℤ X).cycles (p + q) ⟶ (relChains X A).X (p + q)) =>
        (ModuleCat.Hom.hom g) z')
      (HomologicalComplex.cyclesMap_i (CategoryTheory.Limits.cokernel.π (inclChains X A)) (p + q))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
    exact h
  have hcap : ((singularChains ℤ X).iCycles q) (relCapPairZ X A p q zα cc)
      = (cap ℤ (TopCat.toSSet.obj X) (u.1 : Cochain ℤ (TopCat.toSSet.obj X) p) q)
          (((singularChains ℤ X).iCycles (p + q)) z') := by
    rw [relCapPairZ_iCycles X A p q zα cc]
    rw [hza, hcyc, relChains_cokernelIso_canon_apply X A (p + q)
      (((singularChains ℤ X).iCycles (p + q)) z')]
    exact relCapHalf_apply_incl X A (m := q) u (((singularChains ℤ X).iCycles (p + q)) z')
  have hL : kronH ℤ (TopCat.toSSet.obj X) q
      (cohomologyClassOf ℤ (TopCat.toSSet.obj X) a ha)
      (relCapPair X A p q (relClassOf ℤ X A u hu)
        (((relChains X A).homologyπ (p + q)) cc))
      = kronecker ℤ (TopCat.toSSet.obj X) a
          ((cap ℤ (TopCat.toSSet.obj X) (u.1 : Cochain ℤ (TopCat.toSSet.obj X) p) q)
            (((singularChains ℤ X).iCycles (p + q)) z')) := by
    rw [show relClassOf ℤ X A u hu = ((relComplex ℤ X A).homologyπ p) zα from rfl]
    rw [relCapPair_apply X A p q zα cc]
    rw [kronH_apply_sing X a ha (relCapPairZ X A p q zα cc)]
    rw [hcap]
    rfl
  have hz'cast : (Nat.add_comm q p).symm ▸
        (((singularChains ℤ X).homologyπ (p + q)) z')
      = ((singularChains ℤ X).homologyπ (q + p)) ((Nat.add_comm q p).symm ▸ z') :=
    homologyπ_cast_sing (Nat.add_comm q p).symm z'
  have hR : kronH ℤ (TopCat.toSSet.obj X) (q + p)
      (HomologicalComplex.homologyMap (relIncl ℤ X A) (q + p)
        (mixedCup X A q p (cohomologyClassOf ℤ (TopCat.toSSet.obj X) a ha)
          (relClassOf ℤ X A u hu)))
      ((Nat.add_comm q p).symm ▸ (((singularChains ℤ X).homologyπ (p + q)) z'))
      = kronecker ℤ (TopCat.toSSet.obj X)
          ((Nat.add_comm q p) ▸
            (cup ℤ (TopCat.toSSet.obj X) a (u.1 : Cochain ℤ (TopCat.toSSet.obj X) p)))
          (((singularChains ℤ X).iCycles (p + q)) z') := by
    rw [hz'cast]
    obtain ⟨hmem, hmem2, hmixed⟩ := mixedCup_apply X A q p a u ha hu
    rw [hmixed]
    rw [relIncl_homologyMap_relClassOf ℤ X A ⟨cup ℤ (TopCat.toSSet.obj X) a
      (u.1 : Cochain ℤ (TopCat.toSSet.obj X) p), hmem⟩ hmem2]
    rw [kronH_apply_sing X (cup ℤ (TopCat.toSSet.obj X) a
        (u.1 : Cochain ℤ (TopCat.toSSet.obj X) p))
      (relClassOf_cochainDiff ℤ X A ⟨cup ℤ (TopCat.toSSet.obj X) a
        (u.1 : Cochain ℤ (TopCat.toSSet.obj X) p), hmem⟩ hmem2)
      ((Nat.add_comm q p).symm ▸ z')]
    rw [iCycles_cast_sing (Nat.add_comm q p).symm z']
    rw [← cast_linearMap_apply (Nat.add_comm q p)
      (cup ℤ (TopCat.toSSet.obj X) a (u.1 : Cochain ℤ (TopCat.toSSet.obj X) p))
      (((singularChains ℤ X).iCycles (p + q)) z')]
    rfl
  rw [hc_eq, hL, hR]
  exact kronecker_cap_cup_comm_gen X A p q hpq a ha u hu z'

end

end Work.Tubular
