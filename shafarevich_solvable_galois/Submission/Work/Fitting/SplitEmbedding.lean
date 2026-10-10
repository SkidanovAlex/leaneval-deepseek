import Mathlib.GroupTheory.Frattini
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Algebra.CharP.IntermediateField
import Mathlib.Algebra.Torsor.Defs
import Mathlib.FieldTheory.Galois.Basic
import Submission.Combine
import Submission.Shafarevich
import Submission.Work.Fitting.FrattiniLtFitting
import Submission.Work.Fitting.exists_supplement_of_not_le_frattini
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.Fitting

set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000
open scoped Classical
open Submission

universe u

/-- The **split embedding problem** over `ℚ` attached to a finite Galois subextension
`L ⊆ AlgebraicClosure ℚ` and a finite group `N` acting on itself through
`φ : Gal(L/ℚ) →* MulAut N`: the group is the semidirect product `N ⋊[φ] Gal(L/ℚ)` and the
projection onto `Gal(L/ℚ)` is `SemidirectProduct.rightHom`. -/
noncomputable def SplitEmbeddingProblem (L : IntermediateField ℚ (AlgebraicClosure ℚ))
    [FiniteDimensional ℚ L] [IsGalois ℚ L] (N : Type) [Group N] [Finite N]
    (φ : (L ≃ₐ[ℚ] L) →* MulAut N) : Submission.EmbeddingProblem ℚ where
  L := ↥L
  field := inferInstance
  algebra := inferInstance
  finiteDimensional := inferInstance
  isGalois := inferInstance
  G := N ⋊[φ] (L ≃ₐ[ℚ] L)
  group := inferInstance
  finite := Finite.of_equiv (N × (L ≃ₐ[ℚ] L)) SemidirectProduct.equivProd.symm
  π := SemidirectProduct.rightHom
  surjective := SemidirectProduct.rightHom_surjective

/-- The **split embedding problem** `1 → N → N ⋊[φ] Gal(L/ℚ) → Gal(L/ℚ) → 1` has a *proper*
solution: a finite Galois extension `L'/ℚ` containing `L` with `Gal(L'/ℚ) ≅ N ⋊[φ] Gal(L/ℚ)`
compatibly with the projection onto `Gal(L/ℚ)`.  This is the unfolded, universe-polymorphic form
of `(SplitEmbeddingProblem L N φ).IsSolvable`; the latter lives in the fixed universe of
`Submission.EmbeddingProblem`, so for a group in an arbitrary universe the hypothesis of
`realizable_of_solvable_of_split_solvable` should be used instead. -/
def SplitEmbeddingSolvable (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L]
    [IsGalois ℚ L] (N : Type u) [Group N] [Finite N] (φ : (L ≃ₐ[ℚ] L) →* MulAut N) : Prop :=
  ∃ (L' : Type) (_ : Field L') (_ : Algebra ℚ L') (_ : FiniteDimensional ℚ L')
      (_ : IsGalois ℚ L')
      (_ : Algebra ↥L L') (_ : IsScalarTower ℚ ↥L L') (_ : FiniteDimensional ↥L L')
      (_ : IsGalois ↥L L'),
    ∃ (e : N ⋊[φ] (L ≃ₐ[ℚ] L) ≃* (L' ≃ₐ[ℚ] L')), ∀ (g : N ⋊[φ] (L ≃ₐ[ℚ] L)) (x : ↥L),
      e g (algebraMap ↥L L' x) = algebraMap ↥L L' (SemidirectProduct.rightHom g x)

theorem realizableOver_of_splitEmbeddingSolvable {L : IntermediateField ℚ (AlgebraicClosure ℚ)}
    [FiniteDimensional ℚ L] [IsGalois ℚ L] {N : Type u} [Group N] [Finite N]
    {φ : (L ≃ₐ[ℚ] L) →* MulAut N} (h : SplitEmbeddingSolvable L N φ) :
    RealizableOver ℚ (N ⋊[φ] (L ≃ₐ[ℚ] L)) := by
  obtain ⟨L', hF, hA, hFD, hG, -, -, -, -, e, -⟩ := h
  exact ⟨L', hF, hA, hFD, hG, ⟨e⟩⟩

/-- **Ore's reduction** (universe-polymorphic form).  Every finite solvable group is realizable
over `ℚ`, *provided* every split embedding problem over `ℚ` with finite nilpotent kernel has a
solution, i.e. provided that for every finite Galois `L/ℚ` and every finite nilpotent group `N`
with an action of `Gal(L/ℚ)`, the semidirect product `N ⋊ Gal(L/ℚ)` is realizable over `ℚ`.
The hypothesis is Theorem 14 of Schmidt–Wingberg (arXiv:math/9809211) for the base field `ℚ`. -/
theorem realizable_of_solvable_of_split_embedding_univ
    (h : ∀ (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L] [IsGalois ℚ L]
           (N : Type u) [Group N] [Finite N], Group.IsNilpotent N →
           ∀ φ : (L ≃ₐ[ℚ] L) →* MulAut N, RealizableOver ℚ (N ⋊[φ] (L ≃ₐ[ℚ] L)))
    (G : Type u) [Group G] [Finite G] [Group.IsSolvable G] : Submission.RealizableOver ℚ G := by
  classical
  have main : ∀ n : ℕ, ∀ (K : Type u) [Group K] [Finite K] [Group.IsSolvable K],
      Nat.card K = n → RealizableOver ℚ K := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro K _ _ _ hcard
      by_cases hsub : Subsingleton K
      · exact realizableOver_of_subsingleton K
      · -- `F = F(K)` is a nontrivial nilpotent normal subgroup with `F ⊄ Φ(K)`
        have hFne : fitting K ≠ ⊥ := fitting_ne_bot hsub
        have hnotle : ¬ fitting K ≤ frattini K := by
          intro hle
          exact absurd (le_antisymm hle frattini_le_fitting)
            (ne_of_gt (frattini_lt_fitting K hsub))
        obtain ⟨U, hUtop, hFU⟩ := exists_supplement_of_not_le_frattini (fitting K) hnotle
        -- `U` is a proper subgroup, hence solvable of smaller order
        haveI hUsolv : Group.IsSolvable ↥U := inferInstance
        have hcardU : Nat.card ↥U < n := by
          rw [← hcard]
          refine lt_of_le_of_ne (Nat.le_of_dvd Nat.card_pos (Subgroup.card_subgroup_dvd_card U)) ?_
          intro hc
          exact hUtop (Subgroup.eq_top_of_card_eq U hc)
        have hUreal : RealizableOver ℚ ↥U := ih (Nat.card ↥U) hcardU ↥U rfl
        -- move the realization into `AlgebraicClosure ℚ`
        obtain ⟨L, hLfd, hLG, ⟨e⟩⟩ := RealizableOver.toClosure hUreal
        haveI := hLfd
        haveI := hLG
        haveI hFnorm : (fitting K).Normal := fitting_normal
        haveI hFnil : Group.IsNilpotent ↥(fitting K) := fitting_nilpotent K
        -- the conjugation action of `U` on `F`, transported along `e`
        let ψ : ↥U →* MulAut ↥(fitting K) := (MulAut.conjNormal (H := fitting K)).comp U.subtype
        let φ : (L ≃ₐ[ℚ] L) →* MulAut ↥(fitting K) := ψ.comp e.symm.toMonoidHom
        -- the split embedding problem is solvable by hypothesis
        have hreal : RealizableOver ℚ (↥(fitting K) ⋊[φ] (L ≃ₐ[ℚ] L)) :=
          h L ↥(fitting K) hFnil φ
        -- `F ⋊[ψ] U ≅ F ⋊[φ] Gal(L/ℚ)`
        have eiso : (↥(fitting K) ⋊[φ] (L ≃ₐ[ℚ] L)) ≃* (↥(fitting K) ⋊[ψ] ↥U) :=
          SemidirectProduct.congr (MulEquiv.refl ↥(fitting K)) e.symm fun g => by ext x; rfl
        -- `(x, u) ↦ x * u` is a surjection `F ⋊[ψ] U → K`
        set gHom : (↥(fitting K) ⋊[ψ] ↥U) →* K :=
          SemidirectProduct.lift (fitting K).subtype U.subtype fun u =>
            MonoidHom.ext fun x => by
              simpa [ψ, MulAut.conj_apply] using
                (MulAut.conjNormal_apply (H := fitting K) (U.subtype u) x) with hgHom
        have hgsurj : Function.Surjective gHom := by
          intro y
          have hy : y ∈ (fitting K) ⊔ U := by rw [hFU]; trivial
          obtain ⟨a, ha, b, hb, hab⟩ : ∃ a ∈ (fitting K : Subgroup K), ∃ b ∈ U, a * b = y := by
            have h2 : y ∈ (↑(fitting K ⊔ U) : Set K) := hy
            rw [Subgroup.normal_mul] at h2
            exact Set.mem_mul.mp h2
          refine ⟨SemidirectProduct.inl ⟨a, ha⟩ * SemidirectProduct.inr ⟨b, hb⟩, ?_⟩
          rw [hgHom, map_mul]
          simp only [SemidirectProduct.lift_inl, SemidirectProduct.lift_inr]
          exact hab
        exact (hreal.of_mulEquiv eiso).of_surjective gHom hgsurj
  exact main (Nat.card G) G rfl

/-- **Ore's reduction**, in the faithful form of the split embedding problem: if every split
embedding problem over `ℚ` with finite nilpotent kernel has a *proper* solution (Theorem 14 of
Schmidt–Wingberg for the base field `ℚ`), then every finite solvable group is realizable over
`ℚ`.  Unlike `realizable_of_solvable_of_split_embedding` this statement is
universe-polymorphic. -/
theorem realizable_of_solvable_of_split_solvable
    (h : ∀ (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L] [IsGalois ℚ L]
           (N : Type u) [Group N] [Finite N], Group.IsNilpotent N →
           ∀ φ : (L ≃ₐ[ℚ] L) →* MulAut N, SplitEmbeddingSolvable L N φ)
    (G : Type u) [Group G] [Finite G] [Group.IsSolvable G] : Submission.RealizableOver ℚ G :=
  realizable_of_solvable_of_split_embedding_univ
    (fun (L : IntermediateField ℚ (AlgebraicClosure ℚ)) _ _ N _ _ hN φ =>
      realizableOver_of_splitEmbeddingSolvable (h L N hN φ)) G

/-- **Ore's reduction**, in the form requested: every finite solvable group is realizable over
`ℚ`, provided every *split* embedding problem over `ℚ` with finite nilpotent kernel is solvable
(Theorem 14 of Schmidt–Wingberg for the base field `ℚ`).  Here `SplitEmbeddingProblem L N φ` is
the embedding problem `1 → N → N ⋊[φ] Gal(L/ℚ) → Gal(L/ℚ) → 1`. -/
theorem realizable_of_solvable_of_split_embedding
    (h : ∀ (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L] [IsGalois ℚ L]
           (N : Type) [Group N] [Finite N], Group.IsNilpotent N →
           ∀ φ : (L ≃ₐ[ℚ] L) →* MulAut N, (SplitEmbeddingProblem L N φ).IsSolvable)
    (G : Type) [Group G] [Finite G] [Group.IsSolvable G] : Submission.RealizableOver ℚ G :=
  realizable_of_solvable_of_split_embedding_univ
    (fun (L : IntermediateField ℚ (AlgebraicClosure ℚ)) _ _ (N : Type) _ _ hN φ =>
      EmbeddingProblem.isSolvable_realizable (SplitEmbeddingProblem L N φ) (h L N hN φ)) G

end Work.Fitting
