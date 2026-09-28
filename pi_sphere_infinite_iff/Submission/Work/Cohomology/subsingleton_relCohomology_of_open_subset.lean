import Mathlib
import Submission.Work.Cohomology.pd_good
import Submission.Work.Cohomology.relChainsMap_quasiIso
import Submission.Work.Cohomology.relComplexIsoDual
import Submission.Work.Cohomology.dualComplexMap_quasiIso
import Submission.Work.Cohomology.relChainsProjective
import Submission.Work.Cohomology.relChainsHomeomorphCompat
import Submission.Work.Cohomology.RelCup

/-!
# Vanishing of `H^p(I, I∖C)` from the vanishing of `H^p(W, W∖C)` for `C ⊆ W ⊆ I`

Let `M` be a Hausdorff space, `W ⊆ I ⊆ M` with `W` open, and `C ⊆ W` compact.  Then the relative
cohomology `H^p(I, I∖C)` is a quotient (indeed isomorphic) to `H^p(W, W∖C)`: the pair `(I, I∖C)`
only sees the part of `I` close to `C`, which lies inside the open set `W`.  Consequently, if
`H^p(W, W∖C) = 0` then `H^p(I, I∖C) = 0`.

The proof is excision in its cohomological form, assembled here from pieces that can be imported
together with `pd_good` (the `dualZ` of `Submission.Work.Cohomology.dualZ` clashes with the one of
`Submission.Work.Cohomology.localCohomology`, and `pd_good` pulls in the latter, so we cannot use
`Submission.Work.Cohomology.cohomologicalExcision` here).

1. `W` is open in `I` and `I∖C` is open in `I` (as `C` is closed in `M`), and `W ∪ (I∖C) = I`
   because `C ⊆ W`; so the open-cover quasi-isomorphism of relative chains
   `relChainsMap_quasiIso` gives a quasi-isomorphism
   `C_*(W, W∖C) ⟶ C_*(I, I∖C)`.
2. Dualising a quasi-isomorphism between degreewise projective `ℤ`-chain complexes is a
   quasi-isomorphism (`dualComplexMap_quasiIso`), and `relComplex ≅ dualComplex (relChains)`
   (`relComplexIsoDual`); hence the above induces an isomorphism `H^p(I, I∖C) ≅ H^p(W, W∖C)`,
   where the left-hand pair is really `(S, S∩(I∖C))` for the subspace `S = I ∩ W` of `I`.
3. `S` is homeomorphic to `W` as a pair (both are `{m : M | m ∈ W}` with the relative part
   `{m | m ∈ W, m ∉ C}`), and relative cohomology is invariant under a homeomorphism of pairs
   (`relCohomology_homeomorph_pairs`).
-/

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

/-! ## Auxiliary lemmas -/

/-- **Dualising a quasi-isomorphism of relative chain complexes.**  A chain map between two
degreewise projective relative chain complexes which is a quasi-isomorphism induces, via
`C^*(X,A) ≅ Hom_ℤ(C_*(X,A), ℤ)`, an isomorphism of relative cohomology groups. -/
theorem relCohomology_iso_of_relChains_quasiIso {X Y : TopCat} (A : Set X) (B : Set Y)
    (φ : relChains X A ⟶ relChains Y B)
    (hφ : ∀ k, IsIso (HomologicalComplex.homologyMap φ k)) (n : ℕ) :
    Nonempty ((relComplex ℤ X A).homology n ≅ (relComplex ℤ Y B).homology n) := by
  obtain ⟨eX⟩ := relComplexIsoDual X A
  obtain ⟨eY⟩ := relComplexIsoDual Y B
  haveI : IsIso (HomologicalComplex.homologyMap
      (dualComplexMap ℤ (relChains X A) (relChains Y B) φ) n) :=
    dualComplexMap_quasiIso φ (relChainsProjective X A) (relChainsProjective Y B) hφ n
  exact ⟨(HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.up ℕ) n).mapIso eX ≪≫
    (asIso (HomologicalComplex.homologyMap
      (dualComplexMap ℤ (relChains X A) (relChains Y B) φ) n)).symm ≪≫
    ((HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.up ℕ) n).mapIso eY).symm⟩

/-- **The relative chain complex is invariant under a homeomorphism of pairs**, at the level of
chain complexes: a homeomorphism `e : X ≃ₜ Y` carrying `A ⊆ X` onto `B ⊆ Y` induces an isomorphism
`C_*(X,A) ≅ C_*(Y,B)`.  (This is the chain-complex-level lift of
`Work.Cohomology.relChainsHomeomorphCompat`.) -/
theorem relChainsHomeomorphIso (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (e : X ≃ₜ Y) (he : ∀ x, x ∈ A ↔ e x ∈ B) :
    Nonempty (relChains (TopCat.of X) A ≅ relChains (TopCat.of Y) B) := by
  set E := TopCat.isoOfHomeo (X := TopCat.of X) (Y := TopCat.of Y) e with hE
  have hEf : ∀ x : X, (E.hom : X → Y) x = e x := by
    intro x
    rw [hE, TopCat.isoOfHomeo_hom, TopCat.ofHom_apply]
    rfl
  have he' : ∀ x, x ∈ A ↔ (E.hom : X → Y) x ∈ B := by
    intro x; rw [hEf x]; exact he x
  have hev : ∀ a : ↥A, (E.hom : X → Y) a.1 ∈ B := fun a => (he' a.1).mp a.2
  have hev' : ∀ b : ↥B, (E.inv : Y → X) b.1 ∈ A := by
    intro b
    refine (he' ((E.inv : Y → X) b.1)).mpr ?_
    have h : (TopCat.Hom.hom E.hom) ((TopCat.Hom.hom E.inv) b.1) = b.1 := by
      have h2 : TopCat.Hom.hom (E.inv ≫ E.hom) = TopCat.Hom.hom (𝟙 (TopCat.of Y)) := by
        rw [E.inv_hom_id]
      exact DFunLike.congr_fun h2 b.1
    rw [h]; exact b.2
  let hA : ↥A ≃ₜ ↥B :=
    { toFun := fun a => ⟨(E.hom : X → Y) a.1, hev a⟩
      invFun := fun b => ⟨(E.inv : Y → X) b.1, hev' b⟩
      left_inv := by
        intro a
        apply Subtype.ext
        have h2 : TopCat.Hom.hom (E.hom ≫ E.inv) = TopCat.Hom.hom (𝟙 (TopCat.of X)) := by
          rw [E.hom_inv_id]
        exact DFunLike.congr_fun h2 a.1
      right_inv := by
        intro b
        apply Subtype.ext
        have h2 : TopCat.Hom.hom (E.inv ≫ E.hom) = TopCat.Hom.hom (𝟙 (TopCat.of Y)) := by
          rw [E.inv_hom_id]
        exact DFunLike.congr_fun h2 b.1
      continuous_toFun := ((TopCat.Hom.hom E.hom).continuous.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := ((TopCat.Hom.hom E.inv).continuous.comp continuous_subtype_val).subtype_mk _ }
  have hsq : inclChains (TopCat.of X) A ≫ chainMap ℤ (TopCat.of X) (TopCat.of Y) E.hom =
      chainMap ℤ (TopCat.of ↥A) (TopCat.of ↥B) (TopCat.isoOfHomeo hA).hom ≫
        inclChains (TopCat.of Y) B := by
    have h2 : (subtypeIncl (TopCat.of X) A ≫ E.hom) =
        ((TopCat.isoOfHomeo hA).hom ≫ subtypeIncl (TopCat.of Y) B) := by
      apply TopCat.hom_ext
      ext a
      rfl
    show chainMap ℤ (TopCat.of ↥A) (TopCat.of X) (subtypeIncl (TopCat.of X) A) ≫
        chainMap ℤ (TopCat.of X) (TopCat.of Y) E.hom = _
    rw [← CategoryTheory.Functor.map_comp, h2, CategoryTheory.Functor.map_comp]
  exact ⟨cokernel.mapIso (f := inclChains (TopCat.of X) A) (f' := inclChains (TopCat.of Y) B)
    (((singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).mapIso
      (TopCat.isoOfHomeo hA))
    (((singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).mapIso E) hsq⟩

/-- **Relative cohomology is invariant under a homeomorphism of pairs.** -/
theorem relCohomology_homeomorph_pairs {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (e : X ≃ₜ Y) (he : ∀ x, x ∈ A ↔ e x ∈ B) (n : ℕ) :
    Nonempty ((relComplex ℤ (TopCat.of X) A).homology n ≅
      (relComplex ℤ (TopCat.of Y) B).homology n) := by
  obtain ⟨Ψ⟩ := relChainsHomeomorphIso X Y A B e he
  refine relCohomology_iso_of_relChains_quasiIso (X := TopCat.of X) (Y := TopCat.of Y)
    A B Ψ.hom ?_ n
  intro k
  exact Functor.map_isIso
    (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) k) Ψ.hom

/-- A subsingleton transfers across an isomorphism of `ℤ`-modules. -/
theorem subsingleton_of_iso {P Q : ModuleCat ℤ} (e : P ≅ Q) (h : Subsingleton P) :
    Subsingleton Q :=
  (Equiv.subsingleton_congr e.toLinearEquiv.toEquiv).mp h

/-! ## The main lemma -/

theorem subsingleton_relCohomology_of_open_subset {M : TopCat} [T2Space M] {W I : Set M}
    (hW : IsOpen W) (hWI : W ⊆ I) {C : Set M} (hC : C ⊆ W) (hCc : IsCompact C) (p : ℕ)
    (h : Subsingleton ((relComplex ℤ (TopCat.of W) (pdRelSub W C)).homology p)) :
    Subsingleton ((relComplex ℤ (TopCat.of I) (pdRelSub I C)).homology p) := by
  set A : Set ↥I := pdRelSub I C with hAdef
  set U : Set ↥I := {y : ↥I | (y : M) ∈ W} with hUdef
  -- `W` and `I∖C` form an open cover of `I`
  have hUopen : IsOpen U := hW.preimage continuous_subtype_val
  have hAopen : IsOpen A := hCc.isClosed.isOpen_compl.preimage continuous_subtype_val
  have hcov : U ∪ A = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    by_cases hy : (y : M) ∈ C
    · exact Or.inl (hC hy)
    · exact Or.inr hy
  -- excision: the open-cover quasi-isomorphism `C_*(W, W∖C) ⟶ C_*(I, I∖C)`
  have hqiso : ∀ k, IsIso (HomologicalComplex.homologyMap (relChainsMap (TopCat.of I) U A) k) :=
    fun k => relChainsMap_quasiIso (TopCat.of I) U A hUopen hAopen hcov k
  let A' : Set ↥U := {y | (y : ↥I) ∈ A}
  obtain ⟨ebig⟩ := relCohomology_iso_of_relChains_quasiIso (X := TopCat.of U) (Y := TopCat.of I)
    A' A (relChainsMap (TopCat.of I) U A) hqiso p
  -- the spaces `↥W` and `↥U = {y : ↥I | (y : M) ∈ W}` are homeomorphic as pairs
  let B : Set ↥W := pdRelSub W C
  let eS : ↥W ≃ₜ ↥U :=
    { toFun := fun x => ⟨⟨(x : M), hWI x.2⟩, x.2⟩
      invFun := fun y => ⟨(y.1 : M), y.2⟩
      left_inv := by intro x; exact Subtype.ext rfl
      right_inv := by intro y; exact Subtype.ext (Subtype.ext rfl)
      continuous_toFun := Continuous.subtype_mk
        (Continuous.subtype_mk continuous_subtype_val (fun x => hWI x.2)) (fun x => x.2)
      continuous_invFun := Continuous.subtype_mk
        (continuous_subtype_val.comp continuous_subtype_val) (fun y => y.2) }
  have heS : ∀ x : ↥W, x ∈ B ↔ eS x ∈ A' := by
    intro x
    show (x : M) ∈ Cᶜ ↔ ((eS x : ↥U) : ↥I) ∈ A
    simp only [A, pdRelSub_mem_iff]
    exact Iff.rfl
  obtain ⟨ehom⟩ := relCohomology_homeomorph_pairs B A' eS heS p
  have hB : Subsingleton ((relComplex ℤ (TopCat.of W) B).homology p) := h
  exact subsingleton_of_iso ebig (subsingleton_of_iso ehom hB)

end

end Work.Cohomology
