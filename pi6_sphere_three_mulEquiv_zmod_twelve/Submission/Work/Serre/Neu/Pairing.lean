-- PORTED COPY (neutral island) of `Submission/Work/Serre/pairingIdentity.lean`.
-- The only changes are: the imports of ratShuffle-island modules are redirected to the
-- copies in `Submission/Work/Serre/Neu/`, and the abbrev `singSSet` is renamed to
-- `singSSetN` (same body) so that this module can coexist with `Work.Serre.E0Defs`,
-- which declares the same name.  Declarations and proofs are unchanged.
import Mathlib
import Submission.Work.Serre.Neu.Defs
import Submission.Work.Serre.relKronEquiv
-- NOTE: `Submission.Work.Serre.shufRat_relCycle` is not needed for this proof (and its current
-- state is work in progress elsewhere); the import is therefore omitted.
import Submission.Work.Serre.Neu.CupDual
import Submission.Work.Serre.homologyMap_cohomologyClassOf
import Submission.Work.Cohomology.mixedRelCupH
import Submission.Work.Cohomology.relCupHNatural

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option maxHeartbeats 4000000

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace Work.Serre

noncomputable section

/-- The computation rule for the mixed cup product, in the vocabulary of `Work.Thom`. -/
lemma mixedCupC_apply (R : Type) [CommRing R] {B : Type} [TopologicalSpace B] (A : Set B)
    (m n : ℕ) (a : Work.Cohomology.Cochain R (singSSetN B) m)
    (b : Work.Cohomology.relKern R (TopCat.of B) A n)
    (ha : Work.Cohomology.cochainDiff R (singSSetN B) a = 0)
    (hb : Work.Cohomology.relDiffLM R (TopCat.of B) A n b = 0) :
    ∃ (hmem : Work.Cohomology.cup R (singSSetN B) a b.1 ∈
        Work.Cohomology.relKern R (TopCat.of B) A (m + n))
      (h : Work.Cohomology.relDiffLM R (TopCat.of B) A (m + n)
        ⟨Work.Cohomology.cup R (singSSetN B) a b.1, hmem⟩ = 0),
      Work.Thom.mixedCupC R A m n (Work.Cohomology.cohomologyClassOf R (singSSetN B) a ha)
        (Work.Cohomology.relClassOf R (TopCat.of B) A b hb)
      = Work.Cohomology.relClassOf R (TopCat.of B) A
          ⟨Work.Cohomology.cup R (singSSetN B) a b.1, hmem⟩ h :=
  Classical.choose_spec (Work.Cohomology.mixedRelCupH R (TopCat.of B) A) m n a b ha hb

/-- The relative Kronecker pairing of the class of a relative cocycle, computed on a lift. -/
lemma relKronEquiv_apply (X : TopCat) (A : Set X) (n : ℕ)
    (φ : Work.Cohomology.relKern ℚ X A n) (hφ : Work.Cohomology.relDiffLM ℚ X A n φ = 0)
    (c : ↥((Work.StemsB.relChainsR ℚ X A).cycles n))
    (x : ↥((Work.Cohomology.singularChains ℚ X).X n))
    (hx : (Work.StemsB.rdRProj ℚ X A n) x = (Work.StemsB.relChainsR ℚ X A).iCycles n c) :
    (Classical.choose (relKronEquiv X A n))
        (Work.Cohomology.relClassOf ℚ X A φ hφ)
        ((Work.StemsB.relChainsR ℚ X A).homologyπ n c)
      = Work.StemsB.rdRLM ℚ X n φ.1 x :=
  Classical.choose_spec (relKronEquiv X A n) φ hφ c x hx

/-! ## The Serre pairing identity for the product pair

`pairingIdentity` is the chain-level form of the multiplicativity of the Kronecker pairing for the
exterior (mixed) cup product on the product pair `(W × P, W × Q)`: if `c` is a relative cycle of
`(W × P, W × Q)` which is the Eilenberg–Zilber shuffle `shufRat u vt` of an absolute cycle `u` of
`W` with a lift `vt` of a relative cycle of `(P,Q)`, and if the relative cocycle `b` evaluates to
`1` on `vt`, then the relative Kronecker pairing of the mixed cup product of the pullbacks of the
cohomology class of the cocycle `α` and of the relative cohomology class of `b` with `c` equals the
absolute Kronecker pairing of the class of `α` with `u`.

The proof is the chain-level Kronecker rule `Work.Serre.cup_dualChainMap_shufRat`
(`⟨π₁^*α ⌣ π₂^*b, shufRat u vt⟩ = α(u) · b(vt)`), transported to cohomology through the
computation rules of the (relative) Kronecker isomorphisms
(`Work.Serre.relKronEquiv`, `Work.Cohomology.kronH_apply`), together with the naturality of the
pullbacks on the classes of cocycles (`Work.Cohomology.singularCohomologyMap_classOf`,
`Work.Cohomology.homologyMap_relComplexMap_relClassOf`) and of the mixed cup product
(`Work.Cohomology.mixedRelCupH`). -/

/-- **The Serre pairing identity for the product pair.** -/
theorem pairingIdentity (W : Type) [TopologicalSpace W] (P : Type) [TopologicalSpace P]
    (Q : Set P) (m r : ℕ)
    (α : Work.Cohomology.Cochain ℚ (Work.Serre.singSSetN W) m)
    (hα : Work.Cohomology.cochainDiff ℚ (Work.Serre.singSSetN W) α = 0)
    (b : Work.Cohomology.relKern ℚ (TopCat.of P) Q (r + 1))
    (hb : Work.Cohomology.relDiffLM ℚ (TopCat.of P) Q (r + 1) b = 0)
    (hbdeg : ∀ x ∈ (Work.Serre.singSSetN P).degenerate (r + 1),
      Work.Cohomology.genEval ℚ (Work.Serre.singSSetN P) b.1 x = 0)
    (u : ↥((Work.Cohomology.singularChains ℚ (TopCat.of W)).cycles m))
    (v : ↥((Work.Serre.relPA_rat P Q).cycles (r + 1)))
    (vt : (Work.Cohomology.singularChains ℚ (TopCat.of P)).X (r + 1))
    (hvt : (Work.StemsB.rdRProj ℚ (TopCat.of P) Q (r + 1)) vt
            = (Work.Serre.relPA_rat P Q).iCycles (r + 1) v)
    (hvt1 : Work.StemsB.rdRLM ℚ (TopCat.of P) (r + 1) b.1 vt = 1)
    (c : ↥((Work.Serre.relBBA_rat W P Q).cycles (m + r + 1)))
    (hc : (Work.StemsB.rdRProj ℚ (TopCat.of (W × P)) {x : W × P | x.2 ∈ Q} (m + r + 1))
            (Work.Serre.shufRat W P m (r + 1)
              (((Work.Cohomology.singularChains ℚ (TopCat.of W)).iCycles m).hom u) vt)
          = (Work.Serre.relBBA_rat W P Q).iCycles (m + r + 1) c) :
    (Classical.choose (Work.Serre.relKronEquiv (TopCat.of (W × P)) {x : W × P | x.2 ∈ Q}
        (m + r + 1)))
      (Work.Thom.mixedCupC ℚ {x : W × P | x.2 ∈ Q} m (r + 1)
        ((Work.Thom.CohMap (⟨Prod.fst, continuous_fst⟩ : C(W × P, W)) ℚ m).hom
          (Work.Cohomology.cohomologyClassOf ℚ (Work.Serre.singSSetN W) α hα))
        (Work.Thom.relCohMap (⟨Prod.snd, continuous_snd⟩ : C(W × P, P))
          {x : W × P | x.2 ∈ Q} Q (fun _ hx => hx) ℚ (r + 1)
          (Work.Cohomology.relClassOf ℚ (TopCat.of P) Q b hb)))
      ((Work.Serre.relBBA_rat W P Q).homologyπ (m + r + 1) c)
      = Work.Cohomology.kronH ℚ (Work.Serre.singSSetN W) m
          (Work.Cohomology.cohomologyClassOf ℚ (Work.Serre.singSSetN W) α hα)
          ((Work.Cohomology.singularChains ℚ (TopCat.of W)).homologyπ m u) := by
  -- the two pulled-back cochains
  have hα₁c := Work.Cohomology.cochainDiff_dualMap_chainComplexMap ℚ
    (TopCat.toSSet.map (TopCat.ofHom (⟨Prod.fst, continuous_fst⟩ : C(W × P, W)))) α hα
  have hb₁c := @Work.Cohomology.relDiffLM_relMapLM ℚ _ (TopCat.of (W × P)) (TopCat.of P)
    {x : W × P | x.2 ∈ Q} Q (TopCat.ofHom (⟨Prod.snd, continuous_snd⟩ : C(W × P, P))) (fun _ hx => hx) (r + 1) b hb
  -- their classes
  have hcl1 : (Work.Thom.CohMap (⟨Prod.fst, continuous_fst⟩ : C(W × P, W)) ℚ m).hom
        (Work.Cohomology.cohomologyClassOf ℚ (singSSetN W) α hα)
      = Work.Cohomology.cohomologyClassOf ℚ (singSSetN (W × P)) ((ModuleCat.Hom.hom ((Work.Cohomology.dualChainMap ℚ (TopCat.of (W × P)) (TopCat.of W) (TopCat.ofHom (⟨Prod.fst, continuous_fst⟩ : C(W × P, W)))).f m)) α) hα₁c :=
    Work.Cohomology.singularCohomologyMap_classOf ℚ (TopCat.ofHom (⟨Prod.fst, continuous_fst⟩ : C(W × P, W))) α hα
  have hcl2 : (Work.Thom.relCohMap (⟨Prod.snd, continuous_snd⟩ : C(W × P, P)) {x : W × P | x.2 ∈ Q} Q (fun _ hx => hx) ℚ (r + 1)).hom
        (Work.Cohomology.relClassOf ℚ (TopCat.of P) Q b hb)
      = Work.Cohomology.relClassOf ℚ (TopCat.of (W × P)) {x : W × P | x.2 ∈ Q} (Work.Cohomology.relMapLM ℚ {x : W × P | x.2 ∈ Q} Q (TopCat.ofHom (⟨Prod.snd, continuous_snd⟩ : C(W × P, P))) (fun _ hx => hx) (r + 1) b) hb₁c :=
    @Work.Cohomology.homologyMap_relComplexMap_relClassOf ℚ _ (TopCat.of (W × P)) (TopCat.of P)
      {x : W × P | x.2 ∈ Q} Q (TopCat.ofHom (⟨Prod.snd, continuous_snd⟩ : C(W × P, P))) (fun _ hx => hx) (r + 1) b hb
  -- the mixed cup product
  obtain ⟨hmem, hd, hcup⟩ :=
    mixedCupC_apply (R := ℚ) (B := W × P) {x : W × P | x.2 ∈ Q} m (r + 1) ((ModuleCat.Hom.hom ((Work.Cohomology.dualChainMap ℚ (TopCat.of (W × P)) (TopCat.of W) (TopCat.ofHom (⟨Prod.fst, continuous_fst⟩ : C(W × P, W)))).f m)) α) (Work.Cohomology.relMapLM ℚ {x : W × P | x.2 ∈ Q} Q (TopCat.ofHom (⟨Prod.snd, continuous_snd⟩ : C(W × P, P))) (fun _ hx => hx) (r + 1) b) hα₁c hb₁c
  have hfirst : Work.Thom.mixedCupC ℚ {x : W × P | x.2 ∈ Q} m (r + 1)
        ((Work.Thom.CohMap (⟨Prod.fst, continuous_fst⟩ : C(W × P, W)) ℚ m).hom (Work.Cohomology.cohomologyClassOf ℚ (singSSetN W) α hα))
        ((Work.Thom.relCohMap (⟨Prod.snd, continuous_snd⟩ : C(W × P, P)) {x : W × P | x.2 ∈ Q} Q (fun _ hx => hx) ℚ (r + 1)).hom
          (Work.Cohomology.relClassOf ℚ (TopCat.of P) Q b hb))
      = Work.Cohomology.relClassOf ℚ (TopCat.of (W × P)) {x : W × P | x.2 ∈ Q}
          ⟨Work.Cohomology.cup ℚ (singSSetN (W × P)) (n := m) (m := r + 1) ((ModuleCat.Hom.hom ((Work.Cohomology.dualChainMap ℚ (TopCat.of (W × P)) (TopCat.of W) (TopCat.ofHom (⟨Prod.fst, continuous_fst⟩ : C(W × P, W)))).f m)) α) (Work.Cohomology.relMapLM ℚ {x : W × P | x.2 ∈ Q} Q (TopCat.ofHom (⟨Prod.snd, continuous_snd⟩ : C(W × P, P))) (fun _ hx => hx) (r + 1) b).1, hmem⟩ hd := by
    rw [hcl1, hcl2, hcup]
  -- the chain-level Kronecker rule
  have hchain : Work.StemsB.rdRLM ℚ (TopCat.of (W × P)) (m + r + 1)
        (↑⟨Work.Cohomology.cup ℚ (singSSetN (W × P)) (n := m) (m := r + 1) ((ModuleCat.Hom.hom ((Work.Cohomology.dualChainMap ℚ (TopCat.of (W × P)) (TopCat.of W) (TopCat.ofHom (⟨Prod.fst, continuous_fst⟩ : C(W × P, W)))).f m)) α) (Work.Cohomology.relMapLM ℚ {x : W × P | x.2 ∈ Q} Q (TopCat.ofHom (⟨Prod.snd, continuous_snd⟩ : C(W × P, P))) (fun _ hx => hx) (r + 1) b).1, hmem⟩ : Work.Cohomology.relKern ℚ (TopCat.of (W × P)) {x : W × P | x.2 ∈ Q} (m + r + 1))
        (Work.Serre.shufRat W P m (r + 1) (((Work.Cohomology.singularChains ℚ (TopCat.of W)).iCycles m).hom u) vt) = α (((Work.Cohomology.singularChains ℚ (TopCat.of W)).iCycles m).hom u) := by
    show Work.Cohomology.cup ℚ (singSSetN (W × P)) (n := m) (m := r + 1) ((ModuleCat.Hom.hom ((Work.Cohomology.dualChainMap ℚ (TopCat.of (W × P)) (TopCat.of W) (TopCat.ofHom (⟨Prod.fst, continuous_fst⟩ : C(W × P, W)))).f m)) α) (Work.Cohomology.relMapLM ℚ {x : W × P | x.2 ∈ Q} Q (TopCat.ofHom (⟨Prod.snd, continuous_snd⟩ : C(W × P, P))) (fun _ hx => hx) (r + 1) b).1 (Work.Serre.shufRat W P m (r + 1) (((Work.Cohomology.singularChains ℚ (TopCat.of W)).iCycles m).hom u) vt) = α (((Work.Cohomology.singularChains ℚ (TopCat.of W)).iCycles m).hom u)
    rw [Work.Cohomology.relMapLM_coe]
    rw [Work.Serre.cup_dualChainMap_shufRat W P m (r + 1) α b.1 hbdeg
      (((Work.Cohomology.singularChains ℚ (TopCat.of W)).iCycles m).hom u) vt]
    have hbvt : (Work.StemsB.rdRLM ℚ (TopCat.of P) (r + 1) b.1) vt = 1 := hvt1
    change α (((Work.Cohomology.singularChains ℚ (TopCat.of W)).iCycles m).hom u) *
        (Work.StemsB.rdRLM ℚ (TopCat.of P) (r + 1) b.1) vt
      = α (((Work.Cohomology.singularChains ℚ (TopCat.of W)).iCycles m).hom u)
    rw [hbvt, mul_one]
  have hkron : Work.Cohomology.kronH ℚ (singSSetN W) m
        (Work.Cohomology.cohomologyClassOf ℚ (singSSetN W) α hα)
        ((Work.Cohomology.singularChains ℚ (TopCat.of W)).homologyπ m u) = α (((Work.Cohomology.singularChains ℚ (TopCat.of W)).iCycles m).hom u) :=
    Work.Cohomology.kronH_apply ℚ (singSSetN W) α hα u
  rw [hfirst]
  rw [relKronEquiv_apply (TopCat.of (W × P)) {x : W × P | x.2 ∈ Q} (m + r + 1)
    ⟨Work.Cohomology.cup ℚ (singSSetN (W × P)) (n := m) (m := r + 1) ((ModuleCat.Hom.hom ((Work.Cohomology.dualChainMap ℚ (TopCat.of (W × P)) (TopCat.of W) (TopCat.ofHom (⟨Prod.fst, continuous_fst⟩ : C(W × P, W)))).f m)) α) (Work.Cohomology.relMapLM ℚ {x : W × P | x.2 ∈ Q} Q (TopCat.ofHom (⟨Prod.snd, continuous_snd⟩ : C(W × P, P))) (fun _ hx => hx) (r + 1) b).1, hmem⟩ hd c (Work.Serre.shufRat W P m (r + 1) (((Work.Cohomology.singularChains ℚ (TopCat.of W)).iCycles m).hom u) vt) hc]
  rw [hchain, hkron]

end

end Work.Serre
