import Mathlib
import Submission.Work.ThreeConnected.Excision.isZero_homology_relSmallChains_of_deformationRetractPair
import Submission.Work.Cohomology.homologyContractible
import Submission.Work.Cohomology.isZero_dualComplex_empty

/-!
# The connecting map of the relative Mayer–Vietoris sequence for a cover with a contractible piece

Let `X` be a space, `A, U, V ⊆ X` with `U, V` open and `U ∪ V = X`.  Suppose

* `A` is a deformation retract of `U` (so `Hₙ(U, U ∩ A) = 0` for `n ≥ 1`), and
* `V` is contractible and disjoint from `A` (so `V ∩ A = ∅` and `Hₙ(V, V ∩ A) = Hₙ(V) = 0` for
  `n ≥ 1`).

Then the two middle terms `Hₙ(U, U∩A) ⊕ Hₙ(V, V∩A)` of the relative Mayer–Vietoris sequence
vanish for every `n ≥ 1`, and since the sequence is exact, the connecting homomorphism

`relMVδ : Hₙ₊₁(X, A) ⟶ Hₙ(U ∩ V, U ∩ V ∩ A)`

is an isomorphism for every `n ≥ 1`.

Because the middle term is only known to vanish in *positive* degrees, the existing
`relMV_iso_of_acyclic` (which asks for vanishing in all degrees) does not apply; the argument here
only uses `relMV_exact₁` at degree `n` and `relMV_exact₃` at degree `n + 1`, both of which are
positive when `n ≥ 1`.

## Main result

* `isIso_relMVdelta_of_coverData` — the connecting map is an isomorphism under the cover data.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open CategoryTheory Limits
open scoped Simplicial

namespace Work.ThreeConnected.Excision

open Work.Cohomology

noncomputable section

/-! ## The homology of a biproduct of chain complexes -/

/-- The decomposition of an element of the homology of a biproduct of two chain complexes into its
two summands. -/
theorem homologyBiprod_total {C D : ChainComplex (ModuleCat ℤ) ℕ} (n : ℕ)
    (y : (C ⊞ D).homology n) :
    (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (biprod.inl : C ⟶ C ⊞ D) n))
        ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap (biprod.fst : C ⊞ D ⟶ C) n)) y)
      + (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (biprod.inr : D ⟶ C ⊞ D) n))
        ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap (biprod.snd : C ⊞ D ⟶ D) n)) y)
      = y := by
  have hmor : HomologicalComplex.homologyMap (biprod.fst : C ⊞ D ⟶ C) n
        ≫ HomologicalComplex.homologyMap (biprod.inl : C ⟶ C ⊞ D) n
      + HomologicalComplex.homologyMap (biprod.snd : C ⊞ D ⟶ D) n
        ≫ HomologicalComplex.homologyMap (biprod.inr : D ⟶ C ⊞ D) n
      = 𝟙 ((C ⊞ D).homology n) := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
      ← HomologicalComplex.homologyMap_add, biprod.total, HomologicalComplex.homologyMap_id]
  have h := congrArg (fun (f : (C ⊞ D).homology n ⟶ (C ⊞ D).homology n) =>
    ModuleCat.Hom.hom f y) hmor
  simpa only [ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.hom_id, LinearMap.id_apply] using h

/-- **The homology of a biproduct vanishes when both summands do.** -/
theorem isZero_homology_biprod {C D : ChainComplex (ModuleCat ℤ) ℕ} {n : ℕ}
    (hC : IsZero (C.homology n)) (hD : IsZero (D.homology n)) :
    IsZero ((C ⊞ D).homology n) := by
  haveI : Subsingleton ↥(C.homology n) := ModuleCat.subsingleton_of_isZero hC
  haveI : Subsingleton ↥(D.homology n) := ModuleCat.subsingleton_of_isZero hD
  have hzero : ∀ y : (C ⊞ D).homology n, y = 0 := by
    intro y
    have htot := homologyBiprod_total (C := C) (D := D) n y
    have h1 : (ModuleCat.Hom.hom
        (HomologicalComplex.homologyMap (biprod.fst : C ⊞ D ⟶ C) n)) y = 0 :=
      Subsingleton.elim _ _
    have h2 : (ModuleCat.Hom.hom
        (HomologicalComplex.homologyMap (biprod.snd : C ⊞ D ⟶ D) n)) y = 0 :=
      Subsingleton.elim _ _
    rw [h1, h2] at htot
    simpa using htot.symm
  haveI : Subsingleton ↥((C ⊞ D).homology n) := ⟨fun y z => by rw [hzero y, hzero z]⟩
  exact ModuleCat.isZero_of_subsingleton _

/-! ## The vanishing of the `V`-part of the middle term -/

/-- **The small chains of `(V, V ∩ A)` are acyclic in positive degrees when `V` is contractible
and disjoint from `A`.**  Disjointness forces `V ∩ A = ∅`, so the relative complex is the cokernel
of the zero map out of the zero complex `C^{U,V}(V ∩ A)`; hence it is the small chains of `V`,
which are the singular chains of the contractible space `V`. -/
theorem isZero_relSmallChains_inter_subset_of_contractible
    {X : TopCat.{0}} {U V A : Set X} [ContractibleSpace ↥V]
    (hdisj : Disjoint V A) (n : ℕ) (hn : 1 ≤ n) :
    IsZero ((relSmallChains U V V (V ∩ A) Set.inter_subset_left).homology n) := by
  -- Every component of the small chains lying in `V ∩ A` is a coproduct over an empty type.
  have hzeroX : ∀ k, IsZero ((smallInChains U V (V ∩ A)).X k) := by
    intro k
    haveI : IsEmpty ((smallInSSet U V (V ∩ A)).obj (Opposite.op ⦋k⦌)) :=
      IsEmpty.mk (fun σ =>
        Set.disjoint_left.mp hdisj
          (σ.2.2 ⟨Classical.arbitrary (stdSimplex ℝ (Fin (k+1))), rfl⟩).1
          (σ.2.2 ⟨Classical.arbitrary (stdSimplex ℝ (Fin (k+1))), rfl⟩).2)
    exact isZero_coproduct_of_isEmpty
      (fun _ : ((smallInSSet U V (V ∩ A)).obj (Opposite.op ⦋k⦌)) => ModuleCat.of ℤ ℤ)
  -- so the small chains lying in `V ∩ A` are a zero object.
  have hZ : IsZero (smallInChains U V (V ∩ A)) := by
    rw [IsZero.iff_id_eq_zero]
    apply HomologicalComplex.hom_ext
    intro k
    rw [HomologicalComplex.id_f, HomologicalComplex.zero_f]
    exact (IsZero.iff_id_eq_zero ((smallInChains U V (V ∩ A)).X k)).mp (hzeroX k)
  -- hence the inclusion `C^{U,V}(V ∩ A) ⟶ C^{U,V}(V)` is zero and the quotient projection is an
  -- isomorphism.
  have hsub0 : subInclChain U V (Set.inter_subset_left : V ∩ A ⊆ V) = 0 :=
    hZ.eq_zero_of_src _
  haveI : IsIso (cokernel.π (subInclChain U V (Set.inter_subset_left : V ∩ A ⊆ V))) :=
    cokernel.π_of_zero hsub0
  -- the small chains of `V` are the singular chains of `V`, which are acyclic.
  haveI : IsIso (smallInLift U V V) :=
    Work.Cohomology.Endgame.isIso_smallInLift_of_subset U V V (Or.inr (subset_refl V))
  let eS : smallInChains U V V ≅ singularChains ℤ (TopCat.of ↥V) :=
    Functor.mapIso ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ))
      (asIso (smallInLift U V V))
  have hsmall : IsZero ((smallInChains U V V).homology n) :=
    IsZero.of_iso (homologyContractible (X := TopCat.of ↥V) n (by omega))
      ((HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n).mapIso eS)
  exact IsZero.of_iso hsmall
    (asIso (HomologicalComplex.homologyMap (cokernel.π (subInclChain U V
      (Set.inter_subset_left : V ∩ A ⊆ V))) n)).symm

/-! ## The connecting map is an isomorphism when the middle term vanishes in positive degrees -/

/-- **The relative Mayer–Vietoris connecting map is an isomorphism when the middle term vanishes in
positive degrees.**  Only the exactness of the sequence at the third term (degree `n + 1`) and at
the first term (degree `n`) is used, so vanishing of the middle term is needed only for the two
positive indices `n` and `n + 1`. -/
theorem relMV_iso_of_isZero_pos {X : TopCat} (A U V : Set X)
    (h₂ : ∀ m, 1 ≤ m → IsZero (relMVH₂ X A U V m)) (n : ℕ) (hn : 1 ≤ n) :
    IsIso (relMVδ X A U V n) := by
  -- Exactness at the third spot: `im G = ker δ`, and `G = 0` since its source is zero.
  have hmono : Mono (relMVδ X A U V n) :=
    (relMV_exact₃ X A U V n).mono_g
      (IsZero.eq_zero_of_src (h₂ (n + 1) (by omega))
        (HomologicalComplex.homologyMap (relMVG X A U V) (n + 1)))
  -- Exactness at the first spot: `im δ = ker F`, and `F = 0` since its target is zero.
  have hepi : Epi (relMVδ X A U V n) :=
    (relMV_exact₁ X A U V n).epi_f
      (IsZero.eq_zero_of_tgt (h₂ n hn)
        (HomologicalComplex.homologyMap (relMVF X A U V) n))
  exact isIso_of_mono_of_epi (relMVδ X A U V n)

/-! ## The main theorem -/

/-- **The connecting map of the relative Mayer–Vietoris sequence is an isomorphism given the cover
data.**  For an open cover `U ∪ V = X`, if `A` is a deformation retract of `U` and `V` is
contractible and disjoint from `A`, then `relMVδ : Hₙ₊₁(X, A) ⟶ Hₙ(U ∩ V, U ∩ V ∩ A)` is an
isomorphism for every `n ≥ 1`. -/
theorem isIso_relMVdelta_of_coverData
    {X : TopCat.{0}} {A U V : Set X} (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ)
    (hAU : Work.ThreeConnected.IsDeformationRetractPair (X := X) U A)
    [ContractibleSpace ↥V] (hdisjV : Disjoint V A) (n : ℕ) (hn : 1 ≤ n) :
    CategoryTheory.IsIso (Work.Cohomology.relMVδ X A U V n) := by
  refine relMV_iso_of_isZero_pos A U V (fun m hm => ?_) n hn
  have hUpart : IsZero ((relSmallChains U V U (U ∩ A) Set.inter_subset_left).homology m) :=
    isZero_homology_relSmallChains_of_deformationRetractPair hAU hU hV hcov m hm
  have hVpart : IsZero ((relSmallChains U V V (V ∩ A) Set.inter_subset_left).homology m) :=
    isZero_relSmallChains_inter_subset_of_contractible hdisjV m hm
  exact isZero_homology_biprod hUpart hVpart

end

end Work.ThreeConnected.Excision
