import Submission.Work.Tubular.ThomComparison
import Submission.Work.Tubular.Pairing

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology Limits
open scoped Topology

open Work.ThomBordism.PontryaginThom

namespace Work.Tubular

noncomputable section

open Work.Cohomology

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-! ## Degree bookkeeping for the relative pairing -/

/-- **The relative Kronecker pairing is compatible with a change of degrees.** -/
lemma relKronH_cast {X : TopCat} {A : Set X} {a b : ℕ} (h : a = b)
    (β : (relComplex ℤ X A).homology a) (c : (relChains X A).homology a) :
    relKronH X A b (h ▸ β) (h ▸ c) = relKronH X A a β c := by
  cases h
  rfl

/-- **A generator survives a change of degrees.** -/
lemma span_cast_singleton_eq_top {M : ℕ → Type*} [∀ n, AddCommGroup (M n)]
    [∀ n, Module ℤ (M n)] {a b : ℕ} (h : a = b) {x : M a}
    (hx : Submodule.span ℤ ({x} : Set (M a)) = ⊤) :
    Submodule.span ℤ ({(h ▸ x)} : Set (M b)) = ⊤ := by
  cases h
  simpa using hx

/-- **A surjective linear map sends a generator to a generator.** -/
lemma span_singleton_map_eq_top {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] (f : M →ₗ[ℤ] N) (hf : Function.Surjective f) {x : M}
    (hx : Submodule.span ℤ ({x} : Set M) = ⊤) :
    Submodule.span ℤ ({f x} : Set N) = ⊤ := by
  rw [← Set.image_singleton, ← Submodule.map_span, hx, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr hf

/-- **`homologyMap` is compatible with a change of degrees.** -/
lemma homologyMap_cast_nat {K L : ChainComplex (ModuleCat ℤ) ℕ} (φ : K ⟶ L) {a b : ℕ} (h : a = b)
    (x : K.homology a) :
    (HomologicalComplex.homologyMap φ b).hom (h ▸ x)
      = h ▸ ((HomologicalComplex.homologyMap φ a).hom x) := by
  cases h
  rfl

/-- **The Kronecker pairing across a change of degree, first form.** -/
lemma kronH_bridge1 {X : TopCat} {a b : ℕ} (h : a = b)
    (γ : (Work.Cohomology.singularCochainComplex ℤ X).homology b)
    (z : (Work.Cohomology.singularChains ℤ X).homology a) :
    kronH ℤ (TopCat.toSSet.obj X) b γ (h ▸ z)
      = kronH ℤ (TopCat.toSSet.obj X) a (h.symm ▸ γ) z := by
  cases h
  rfl

/-- **The Kronecker pairing across a change of degree, second form.** -/
lemma kronH_bridge2 {X : TopCat} {a b : ℕ} (h : a = b)
    (γ : (Work.Cohomology.singularCochainComplex ℤ X).homology a)
    (z : (Work.Cohomology.singularChains ℤ X).homology a) :
    kronH ℤ (TopCat.toSSet.obj X) a γ z
      = kronH ℤ (TopCat.toSSet.obj X) b (h ▸ γ) (h ▸ z) := by
  cases h
  rfl

/-! ## The class of the collapse in `H_{k+8}(ν, ν∖0)` -/

/-- **The class of the Pontryagin–Thom collapse in `H_{k+8}(ν, ν∖0)`**, at the degree `k+8` of the
interface `Work.Tubular.TubeThomRep`: the star of the degree-`(8+k)` Hurewicz class of the
metric-free collapse under the comparison `Work.Tubular.compIso`. -/
noncomputable def collapseRelK8 {V : Work.ThomBordism.Man8} {k : ℕ}
    {E : EmbeddingData V (8 + k)} {ε : ℝ} (C : TubeChart E ε)
    (g : C(OnePoint (Euc (8 + k)), OnePoint (NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
    {R : ℝ} (hR : 0 ≤ R) (hbox : ∀ y ∈ C.U, ∀ i : Fin (8 + k), |y i| < R) :
    (relChains (TopCat.of (NormalTotal E)) (normalNonzero E)).homology (k + 8) :=
  (compIso E (k + 8)).inv
    ((HomologicalComplex.homologyMap (CategoryTheory.Limits.cokernel.π
      (inclChains (TopCat.of (OnePoint (NormalTotal E))) (onePointNonzero E))) (k + 8)).hom
      ((Nat.add_comm 8 k) ▸ (Work.Stems.hurewiczChain (8 + k) (by omega) OnePoint.infty
        (tubeGenLoopOnePoint C g hg hR hbox))))

/-- **The transfer for `collapseRelK8`.** -/
theorem relKronH_collapseRelK8 {V : Work.ThomBordism.Man8} {k : ℕ}
    {E : EmbeddingData V (8 + k)} {ε : ℝ} (C : TubeChart E ε)
    (g : C(OnePoint (Euc (8 + k)), OnePoint (NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
    {R : ℝ} (hR : 0 ≤ R) (hbox : ∀ y ∈ C.U, ∀ i : Fin (8 + k), |y i| < R)
    (β : Work.Thom.RelCoh ℤ (k + 8) (OnePoint (NormalTotal E)) (onePointNonzero E)) :
    relKronH (TopCat.of (OnePoint (NormalTotal E))) (onePointNonzero E) (k + 8) β
        ((HomologicalComplex.homologyMap (CategoryTheory.Limits.cokernel.π
          (inclChains (TopCat.of (OnePoint (NormalTotal E))) (onePointNonzero E))) (k + 8)).hom
          ((Nat.add_comm 8 k) ▸ (Work.Stems.hurewiczChain (8 + k) (by omega) OnePoint.infty
            (tubeGenLoopOnePoint C g hg hR hbox))))
      = relKronH (TopCat.of (NormalTotal E)) (normalNonzero E) (k + 8)
          (compPull E (k + 8) β) (collapseRelK8 C g hg hR hbox) := by
  haveI h1 := isIso_homeoChain E (k + 8)
  haveI h2 := isIso_excChain E (k + 8)
  have hc : (compIso E (k + 8)).hom (collapseRelK8 C g hg hR hbox)
      = (HomologicalComplex.homologyMap (CategoryTheory.Limits.cokernel.π
          (inclChains (TopCat.of (OnePoint (NormalTotal E))) (onePointNonzero E))) (k + 8)).hom
          ((Nat.add_comm 8 k) ▸ (Work.Stems.hurewiczChain (8 + k) (by omega) OnePoint.infty
            (tubeGenLoopOnePoint C g hg hR hbox))) := by
    rw [collapseRelK8]
    exact Iso.inv_hom_id_apply (compIso E (k + 8)) _
  rw [← hc]
  exact relKronH_comparison E (k + 8) β (collapseRelK8 C g hg hR hbox)

/-- **The collapse class generates `H_{k+8}(ν, ν∖0)`.** -/
theorem collapseRelK8_span_top {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt] {k : ℕ}
    {E : EmbeddingData V (8 + k)} {ε : ℝ} (C : TubeChart E ε) (q : NormalSphSub E ε)
    (hU : IsCompact C.U) {R : ℝ} (hR : 0 ≤ R)
    (hbox : ∀ y ∈ C.U, ∀ i : Fin (8 + k), |y i| < R)
    (g : C(OnePoint (Euc (8 + k)), OnePoint (NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
    (hg2 : ∀ y, y ∈ C.openTube → g (OnePoint.some y)
      = OnePoint.some (normalBlowUp E ε (C.inv y))) :
    Submodule.span ℤ ({collapseRelK8 C g hg hR hbox} : Set _) = ⊤ := by
  haveI h1 := isIso_homeoChain E (k + 8)
  haveI h2 := isIso_excChain E (k + 8)
  -- the degree-`8 + k` Hurewicz class of the collapse, in the pair `(ν⁺, A)`
  have h0 : Submodule.span ℤ
      ({((HomologicalComplex.homologyMap (CategoryTheory.Limits.cokernel.π
        (inclChains (TopCat.of (OnePoint (NormalTotal E))) (onePointNonzero E))) (8 + k)).hom
        (Work.Stems.hurewiczChain (8 + k) (by omega) OnePoint.infty
          (tubeGenLoopOnePoint C g hg hR hbox)))} : Set _) = ⊤ :=
    tubeCollapseClass_span_top C q hU hR hbox g hg hg2
  -- its image under the change of degrees
  have h0' : Submodule.span ℤ
      ({((HomologicalComplex.homologyMap (CategoryTheory.Limits.cokernel.π
        (inclChains (TopCat.of (OnePoint (NormalTotal E))) (onePointNonzero E))) (k + 8)).hom
        ((Nat.add_comm 8 k) ▸ (Work.Stems.hurewiczChain (8 + k) (by omega) OnePoint.infty
          (tubeGenLoopOnePoint C g hg hR hbox))))} : Set _) = ⊤ := by
    rw [homologyMap_cast_nat (CategoryTheory.Limits.cokernel.π
      (inclChains (TopCat.of (OnePoint (NormalTotal E))) (onePointNonzero E))) (Nat.add_comm 8 k)]
    exact span_cast_singleton_eq_top
      (M := fun n => (relChains (TopCat.of (OnePoint (NormalTotal E)))
        (onePointNonzero E)).homology n) (Nat.add_comm 8 k) h0
  rw [collapseRelK8]
  exact span_singleton_map_eq_top
    ((compIso E (k + 8)).inv.hom)
    ((ModuleCat.epi_iff_surjective (compIso E (k + 8)).inv).mp inferInstance) h0'

/-! ## The wiring: `Work.Tubular.TubeThomRep` from the ν-side pairings -/

/-- **The wiring of the ν-side pairing to the interface `Work.Tubular.TubeThomRep`.**

For an embedding `E : V ↪ ℝ^{8+k}` of a closed oriented smooth `8`-manifold, a tube chart, its
metric-free collapse `g`, and a based map `J : Th(ν) → D.T` out of the Thom space of the normal
bundle, the two Hurewicz pairings of the Pontryagin–Thom class
`α = J ∘ (collapse) ∈ π_{8+k}(D.T, D.t₀)` — written in the degree `k + 8` of the interface
`Work.Tubular.TubeThomRep` — are the ν-side pairings

  `⟨compPull (J^*(p)), c⟩_{ν, ν∖0}`,   `p = p₁²U` or `p₂U`,

with `c = Work.Tubular.collapseRelK8` the collapse class of
`Work.Tubular.relKronH_collapseRelK8`.  The two hypotheses are the **ν-side statements**: the
pairing of the pulled-back universal class with the collapse class is the normal Pontryagin number.
Everything *except* those two identities is proved here (the degree bookkeeping `8 + k ↔ k + 8`,
the factorization `Work.Tubular.kronH_hurewiczChain_alphaV` of the pairing through the Thom space of
the normal bundle, and the comparison `Work.Tubular.relKronH_collapseRelK8` with the world
`(ν, ν∖0)` where the local degree lives). -/
theorem tubeThomRep_of_nuPairing {k : ℕ} {D : ThomTarget k} {V : Work.ThomBordism.Man8}
    {N : NormalBundlData V} (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε)
    {R : ℝ} (hR : 0 ≤ R) (hbox : ∀ y ∈ C.U, ∀ i : Fin (8 + k), |y i| < R)
    (J : C(OnePoint (NormalTotal E), D.T)) (hJ : J OnePoint.infty = D.t₀)
    (g : C(OnePoint (Euc (8 + k)), OnePoint (NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
    (hν1 : relKronH (TopCat.of (NormalTotal E)) (normalNonzero E) (k + 8)
        (compPull E (k + 8) (relCoh_of_abs E ((Nat.add_comm 8 k) ▸
          ((Work.Thom.CohMap J ℤ (8 + k)).hom ((Nat.add_comm 8 k).symm ▸ D.p1sqU)))))
        (collapseRelK8 C g hg hR hbox) = N.normalP1Sq)
    (hν2 : relKronH (TopCat.of (NormalTotal E)) (normalNonzero E) (k + 8)
        (compPull E (k + 8) (relCoh_of_abs E ((Nat.add_comm 8 k) ▸
          ((Work.Thom.CohMap J ℤ (8 + k)).hom ((Nat.add_comm 8 k).symm ▸ D.p2U)))))
        (collapseRelK8 C g hg hR hbox) = N.normalP2) :
    Nonempty (TubeThomRep k D V N) := by
  classical
  set α := alphaV C hR hbox D.t₀ J hJ g hg with hα
  have hre : hurewiczClassOf (k + 8) (one_le_add_eight k) D.t₀
        (Quotient.mk _ (GenLoop.congr D.t₀ (finCongr (Nat.add_comm 8 k)) α))
      = (Nat.add_comm 8 k) ▸ hurewiczClassOf (8 + k) (by omega) D.t₀ (Quotient.mk _ α) :=
    (hurewiczClassOf_proof_irrel (one_le_add_eight k) (by omega) D.t₀ _).trans
      (hurewiczClassOf_add_comm D.t₀ α)
  refine ⟨{ collapse := GenLoop.congr D.t₀ (finCongr (Nat.add_comm 8 k)) α
            hurewicz_p1sq := ?_
            hurewicz_p2 := ?_ }⟩
  · calc kronH ℤ (ssetOf D.T) (k + 8) D.p1sqU
          (hurewiczClassOf (k + 8) (one_le_add_eight k) D.t₀
            (Quotient.mk _ (GenLoop.congr D.t₀ (finCongr (Nat.add_comm 8 k)) α)))
        = kronH ℤ (ssetOf D.T) (k + 8) D.p1sqU
            ((Nat.add_comm 8 k) ▸ hurewiczClassOf (8 + k) (by omega) D.t₀ (Quotient.mk _ α)) := by
          rw [hre]
      _ = kronH ℤ (ssetOf D.T) (8 + k) ((Nat.add_comm 8 k).symm ▸ D.p1sqU)
            (hurewiczClassOf (8 + k) (by omega) D.t₀ (Quotient.mk _ α)) :=
          kronH_bridge1 (Nat.add_comm 8 k) D.p1sqU _
      _ = kronH ℤ (ssetOf (OnePoint (NormalTotal E))) (8 + k)
            ((Work.Thom.CohMap J ℤ (8 + k)).hom ((Nat.add_comm 8 k).symm ▸ D.p1sqU))
            (hurewiczClassOf (8 + k) (by omega) OnePoint.infty
              (Quotient.mk _ (tubeGenLoopOnePoint C g hg hR hbox))) :=
          kronH_hurewiczChain_alphaV C hR hbox D.t₀ J hJ g hg
            ((Nat.add_comm 8 k).symm ▸ D.p1sqU)
      _ = kronH ℤ (ssetOf (OnePoint (NormalTotal E))) (k + 8)
            ((Nat.add_comm 8 k) ▸ ((Work.Thom.CohMap J ℤ (8 + k)).hom
              ((Nat.add_comm 8 k).symm ▸ D.p1sqU)))
            ((Nat.add_comm 8 k) ▸ (hurewiczClassOf (8 + k) (by omega) OnePoint.infty
              (Quotient.mk _ (tubeGenLoopOnePoint C g hg hR hbox)))) :=
          kronH_bridge2 (Nat.add_comm 8 k)
            ((Work.Thom.CohMap J ℤ (8 + k)).hom ((Nat.add_comm 8 k).symm ▸ D.p1sqU)) _
      _ = relKronH (TopCat.of (OnePoint (NormalTotal E))) (onePointNonzero E) (k + 8)
            (relCoh_of_abs E ((Nat.add_comm 8 k) ▸ ((Work.Thom.CohMap J ℤ (8 + k)).hom
              ((Nat.add_comm 8 k).symm ▸ D.p1sqU))))
            ((HomologicalComplex.homologyMap (CategoryTheory.Limits.cokernel.π
              (inclChains (TopCat.of (OnePoint (NormalTotal E))) (onePointNonzero E))) (k + 8)).hom
              ((Nat.add_comm 8 k) ▸ (hurewiczClassOf (8 + k) (by omega) OnePoint.infty
                (Quotient.mk _ (tubeGenLoopOnePoint C g hg hR hbox))))) :=
          kronH_eq_relKronH_onePoint' E _ _
      _ = relKronH (TopCat.of (NormalTotal E)) (normalNonzero E) (k + 8)
            (compPull E (k + 8) (relCoh_of_abs E ((Nat.add_comm 8 k) ▸
              ((Work.Thom.CohMap J ℤ (8 + k)).hom ((Nat.add_comm 8 k).symm ▸ D.p1sqU)))))
            (collapseRelK8 C g hg hR hbox) :=
          relKronH_collapseRelK8 C g hg hR hbox _
      _ = N.normalP1Sq := hν1
  · calc kronH ℤ (ssetOf D.T) (k + 8) D.p2U
          (hurewiczClassOf (k + 8) (one_le_add_eight k) D.t₀
            (Quotient.mk _ (GenLoop.congr D.t₀ (finCongr (Nat.add_comm 8 k)) α)))
        = kronH ℤ (ssetOf D.T) (k + 8) D.p2U
            ((Nat.add_comm 8 k) ▸ hurewiczClassOf (8 + k) (by omega) D.t₀ (Quotient.mk _ α)) := by
          rw [hre]
      _ = kronH ℤ (ssetOf D.T) (8 + k) ((Nat.add_comm 8 k).symm ▸ D.p2U)
            (hurewiczClassOf (8 + k) (by omega) D.t₀ (Quotient.mk _ α)) :=
          kronH_bridge1 (Nat.add_comm 8 k) D.p2U _
      _ = kronH ℤ (ssetOf (OnePoint (NormalTotal E))) (8 + k)
            ((Work.Thom.CohMap J ℤ (8 + k)).hom ((Nat.add_comm 8 k).symm ▸ D.p2U))
            (hurewiczClassOf (8 + k) (by omega) OnePoint.infty
              (Quotient.mk _ (tubeGenLoopOnePoint C g hg hR hbox))) :=
          kronH_hurewiczChain_alphaV C hR hbox D.t₀ J hJ g hg
            ((Nat.add_comm 8 k).symm ▸ D.p2U)
      _ = kronH ℤ (ssetOf (OnePoint (NormalTotal E))) (k + 8)
            ((Nat.add_comm 8 k) ▸ ((Work.Thom.CohMap J ℤ (8 + k)).hom
              ((Nat.add_comm 8 k).symm ▸ D.p2U)))
            ((Nat.add_comm 8 k) ▸ (hurewiczClassOf (8 + k) (by omega) OnePoint.infty
              (Quotient.mk _ (tubeGenLoopOnePoint C g hg hR hbox)))) :=
          kronH_bridge2 (Nat.add_comm 8 k)
            ((Work.Thom.CohMap J ℤ (8 + k)).hom ((Nat.add_comm 8 k).symm ▸ D.p2U)) _
      _ = relKronH (TopCat.of (OnePoint (NormalTotal E))) (onePointNonzero E) (k + 8)
            (relCoh_of_abs E ((Nat.add_comm 8 k) ▸ ((Work.Thom.CohMap J ℤ (8 + k)).hom
              ((Nat.add_comm 8 k).symm ▸ D.p2U))))
            ((HomologicalComplex.homologyMap (CategoryTheory.Limits.cokernel.π
              (inclChains (TopCat.of (OnePoint (NormalTotal E))) (onePointNonzero E))) (k + 8)).hom
              ((Nat.add_comm 8 k) ▸ (hurewiczClassOf (8 + k) (by omega) OnePoint.infty
                (Quotient.mk _ (tubeGenLoopOnePoint C g hg hR hbox))))) :=
          kronH_eq_relKronH_onePoint' E _ _
      _ = relKronH (TopCat.of (NormalTotal E)) (normalNonzero E) (k + 8)
            (compPull E (k + 8) (relCoh_of_abs E ((Nat.add_comm 8 k) ▸
              ((Work.Thom.CohMap J ℤ (8 + k)).hom ((Nat.add_comm 8 k).symm ▸ D.p2U)))))
            (collapseRelK8 C g hg hR hbox) :=
          relKronH_collapseRelK8 C g hg hR hbox _
      _ = N.normalP2 := hν2

/-- **The ν-side obligation in the consumer's own vocabulary.**  If for every closed oriented smooth
`8`-manifold `V` and every normal-bundle datum `N` there are an embedding of `V` in `ℝ^{8+k}`, a tube
chart, a based map `J : Th(ν) → D.T` out of the Thom space of the normal bundle, its collapse, and
the two **ν-side** pairing identities of `Work.Tubular.tubeThomRep_of_nuPairing`, then the
Pontryagin–Thom construction is available for every `V`: `TubularThomIso k D` =`PTGeomMin k D`, the
obligation of the Pontryagin–Thom chapter (`Work.ThomBordism.PontryaginThom.TubularThomIso`), holds.

This is the exact form of the remaining obligation: the two ν-side identities are
`⟨compPull (J^* p), c⟩_{ν,ν∖0} = N.normalP..`, i.e. Thom-class naturality ("`c^*(U_ν)` is Poincaré
dual to `V`") in the world `(ν, ν∖0)`. -/
theorem tubularThomIso_of_nuPairing {k : ℕ} {D : ThomTarget k}
    (h : ∀ (V : Work.ThomBordism.Man8) (N : NormalBundlData V),
      ∃ (E : EmbeddingData V (8 + k)) (ε : ℝ) (C : TubeChart E ε) (R : ℝ) (hR : 0 ≤ R)
        (hbox : ∀ y ∈ C.U, ∀ i : Fin (8 + k), |y i| < R)
        (J : C(OnePoint (NormalTotal E), D.T)) (hJ : J OnePoint.infty = D.t₀)
        (g : C(OnePoint (Euc (8 + k)), OnePoint (NormalTotal E)))
        (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty),
        relKronH (TopCat.of (NormalTotal E)) (normalNonzero E) (k + 8)
            (compPull E (k + 8) (relCoh_of_abs E ((Nat.add_comm 8 k) ▸
              ((Work.Thom.CohMap J ℤ (8 + k)).hom ((Nat.add_comm 8 k).symm ▸ D.p1sqU)))))
            (collapseRelK8 C g hg hR hbox) = N.normalP1Sq ∧
        relKronH (TopCat.of (NormalTotal E)) (normalNonzero E) (k + 8)
            (compPull E (k + 8) (relCoh_of_abs E ((Nat.add_comm 8 k) ▸
              ((Work.Thom.CohMap J ℤ (8 + k)).hom ((Nat.add_comm 8 k).symm ▸ D.p2U)))))
            (collapseRelK8 C g hg hR hbox) = N.normalP2) :
    TubularThomIso k D :=
  tubularThomIso_of_rep fun V N => by
    obtain ⟨E, ε, C, R, hR, hbox, J, hJ, g, hg, h1, h2⟩ := h V N
    exact tubeThomRep_of_nuPairing E C hR hbox J hJ g hg h1 h2

/-- The same obligation in the spelling of `Work.ThomBordism.PontryaginThom.PTGeomMin`. -/
theorem ptGeomMin_of_nuPairing {k : ℕ} {D : ThomTarget k}
    (h : ∀ (V : Work.ThomBordism.Man8) (N : NormalBundlData V),
      ∃ (E : EmbeddingData V (8 + k)) (ε : ℝ) (C : TubeChart E ε) (R : ℝ) (hR : 0 ≤ R)
        (hbox : ∀ y ∈ C.U, ∀ i : Fin (8 + k), |y i| < R)
        (J : C(OnePoint (NormalTotal E), D.T)) (hJ : J OnePoint.infty = D.t₀)
        (g : C(OnePoint (Euc (8 + k)), OnePoint (NormalTotal E)))
        (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty),
        relKronH (TopCat.of (NormalTotal E)) (normalNonzero E) (k + 8)
            (compPull E (k + 8) (relCoh_of_abs E ((Nat.add_comm 8 k) ▸
              ((Work.Thom.CohMap J ℤ (8 + k)).hom ((Nat.add_comm 8 k).symm ▸ D.p1sqU)))))
            (collapseRelK8 C g hg hR hbox) = N.normalP1Sq ∧
        relKronH (TopCat.of (NormalTotal E)) (normalNonzero E) (k + 8)
            (compPull E (k + 8) (relCoh_of_abs E ((Nat.add_comm 8 k) ▸
              ((Work.Thom.CohMap J ℤ (8 + k)).hom ((Nat.add_comm 8 k).symm ▸ D.p2U)))))
            (collapseRelK8 C g hg hR hbox) = N.normalP2) :
    PTGeomMin k D :=
  tubularThomIso_of_nuPairing h


end

end Work.Tubular
