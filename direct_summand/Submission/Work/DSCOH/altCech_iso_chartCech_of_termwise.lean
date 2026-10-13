import Mathlib
import Submission.Work.DSCOH.AltCechComplex
import Submission.Work.DSCOH.Chart

namespace Work.DSCOH

open CategoryTheory

set_option linter.style.haveILetI false

/-- A `(q+1)`-element finset of `Fin n` is nonempty. -/
private lemma nonempty_of_card_eq {n q : ℕ} (S : {S : Finset (Fin n) // S.card = q + 1}) :
    S.1.Nonempty :=
  Finset.card_pos.mp (by rw [S.2]; exact Nat.succ_pos q)

private lemma altCech_d {X : Type*} [TopologicalSpace X] {A : Type*} [CommRing A]
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (P : (TopologicalSpace.Opens X)ᵒᵖ ⥤ ModuleCat A) (U : ι → TopologicalSpace.Opens X) (q : ℕ) :
    (altCech P U).d q (q + 1) = ModuleCat.ofHom (altCechDiff P U q) := by
  simp only [altCech, CochainComplex.of_d]

private lemma chartCech_d {A : Type*} [CommRing A] {n : ℕ} {M : Type*} [AddCommGroup M]
    [Module A M] [Module (Poly A n) M] [IsScalarTower A (Poly A n) M]
    (ℳ : ℕ → Submodule A M) [SetLike.GradedSMul (homSub A n) ℳ] (q : ℕ) :
    (chartCech (A := A) (n := n) (M := M) ℳ).d q (q + 1) =
      ModuleCat.ofHom (cechDiff (A := A) (n := n) (M := M) ℳ q) := by
  simp only [chartCech, chartCechOf, CochainComplex.of_d]

/-- In a poset category all morphisms between two fixed objects are equal. -/
private lemma map_homOfLE_proof_irrel {X : Type*} [TopologicalSpace X] {A : Type*} [CommRing A]
    (P : (TopologicalSpace.Opens X)ᵒᵖ ⥤ ModuleCat A) {U V : TopologicalSpace.Opens X}
    (h1 h2 : U ≤ V) :
    P.map (CategoryTheory.homOfLE h1).op = P.map (CategoryTheory.homOfLE h2).op :=
  congrArg (fun h => P.map (CategoryTheory.homOfLE h).op) (Subsingleton.elim h1 h2)

/-- The value of `degPartRestrict` at an element: the underlying element of the localization is
`ψ` applied to the underlying element of `x`. -/
private lemma degPartRestrict_coe {A : Type*} [CommRing A] {n : ℕ} {M : Type*} [AddCommGroup M]
    [Module A M] [Module (Poly A n) M] [IsScalarTower A (Poly A n) M]
    {ℳ : ℕ → Submodule A M} {S T : Finset (Fin n)}
    (ψ : locAt (A := A) (M := M) S →ₗ[Poly A n] locAt (A := A) (M := M) T)
    (h : ∀ x ∈ degZero (A := A) ℳ S, ψ x ∈ degZero (A := A) ℳ T)
    (x : degZero (A := A) ℳ S) :
    degPartRestrict (A := A) (M := M) ℳ ψ h x = ⟨ψ x.1, h x.1 x.2⟩ := by
  rfl

theorem altCech_iso_chartCech_of_termwise {X : Type*} [TopologicalSpace X] {A : Type*}
    [CommRing A] {n : ℕ}
    (P : CategoryTheory.Functor (Opposite (TopologicalSpace.Opens X)) (ModuleCat A))
    (U : Fin n → TopologicalSpace.Opens X)
    {M : Type*} [AddCommGroup M] [Module A M] [Module (Work.DSCOH.Poly A n) M]
    [IsScalarTower A (Work.DSCOH.Poly A n) M] {ℳ : ℕ → Submodule A M}
    [DirectSum.Decomposition ℳ] [SetLike.GradedSMul (Work.DSCOH.homSub A n) ℳ]
    (e : ∀ S : Finset (Fin n), S.Nonempty →
      (↥(Work.DSCOH.degZero (A := A) (M := M) ℳ S) ≃ₗ[A] ↥(P.obj (Opposite.op (S.inf U)))))
    (he : ∀ (S T : Finset (Fin n)) (hST : S ⊆ T) (hS : S.Nonempty) (hT : T.Nonempty)
      (x : ↥(Work.DSCOH.degZero (A := A) (M := M) ℳ S)),
      e T hT ⟨Work.DSCOH.resAt (A := A) (M := M) hST x.1,
          Work.DSCOH.resAt_degZero (A := A) (M := M) hST x.1 x.2⟩
        = P.map (CategoryTheory.homOfLE
            (Finset.le_inf fun b hb => Finset.inf_le (hST hb))).op (e S hS x)) :
    Nonempty (Work.DSCOH.altCech P U ≅ Work.DSCOH.chartCech (A := A) (n := n) (M := M) ℳ) := by
  classical
  -- The termwise linear equivalence between the two complexes.
  let Φ : ∀ q : ℕ, CechTerm (A := A) (n := n) (M := M) ℳ q ≃ₗ[A] AltCechTerm P U q :=
    fun q => LinearEquiv.piCongrRight (fun S : {S : Finset (Fin n) // S.card = q + 1} =>
      e S.1 (nonempty_of_card_eq S))
  have hΦ : ∀ (q : ℕ) (x : CechTerm (A := A) (n := n) (M := M) ℳ q)
      (S : {S : Finset (Fin n) // S.card = q + 1}),
      Φ q x S = e S.1 (nonempty_of_card_eq S) (x S) := by
    intro q x S
    rw [show Φ q = LinearEquiv.piCongrRight
        (fun S : {S : Finset (Fin n) // S.card = q + 1} => e S.1 (nonempty_of_card_eq S))
        from rfl,
      LinearEquiv.piCongrRight_apply]
  -- Compatibility of `Φ` with the differentials.
  have hcommfun : ∀ (q : ℕ) (x : CechTerm (A := A) (n := n) (M := M) ℳ q),
      altCechDiff P U q (Φ q x) = Φ (q + 1) (cechDiff (A := A) (n := n) (M := M) ℳ q x) := by
    intro q x
    funext T
    rw [altCechDiff, LinearMap.pi_apply]
    rw [hΦ (q + 1) (cechDiff (A := A) (n := n) (M := M) ℳ q x) T]
    rw [cechDiff, LinearMap.pi_apply, cechDiffComp]
    conv_lhs => rw [LinearMap.sum_apply]
    conv_rhs => rw [LinearMap.sum_apply, map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    conv_lhs => rw [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply]
    conv_rhs => rw [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply, map_zsmul]
    rw [hΦ q x ⟨T.1.erase i.1, by rw [Finset.card_erase_of_mem i.2]; omega⟩]
    rw [degPartRestrict_coe]
    rw [← he (T.1.erase i.1) T.1 (Finset.erase_subset i.1 T.1)
      (nonempty_of_card_eq (q := q) ⟨T.1.erase i.1, by rw [Finset.card_erase_of_mem i.2]; omega⟩)
      (nonempty_of_card_eq T) (x ⟨T.1.erase i.1, by rw [Finset.card_erase_of_mem i.2]; omega⟩)]
  -- The induced cochain map.
  have hcochain : ∀ q : ℕ,
      ModuleCat.ofHom ((Φ q).toLinearMap) ≫ (altCech P U).d q (q + 1) =
        (chartCech (A := A) (n := n) (M := M) ℳ).d q (q + 1) ≫
          ModuleCat.ofHom ((Φ (q + 1)).toLinearMap) := by
    intro q
    rw [altCech_d, chartCech_d]
    erw [← ModuleCat.ofHom_comp, ← ModuleCat.ofHom_comp]
    congr 1
    refine LinearMap.ext (fun x => ?_)
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap] using hcommfun q x
  let φ : chartCech (A := A) (n := n) (M := M) ℳ ⟶ altCech P U :=
    CochainComplex.ofHom (fun q => ModuleCat.ofHom ((Φ q).toLinearMap)) hcochain
  haveI hcomp : ∀ q : ℕ, IsIso (φ.f q) := fun q => by
    change IsIso (ModuleCat.ofHom ((Φ q).toLinearMap))
    exact (LinearEquiv.toModuleIso (Φ q)).isIso_hom
  haveI hφ : IsIso φ := HomologicalComplex.Hom.isIso_of_components φ
  exact ⟨(asIso φ).symm⟩

end Work.DSCOH
