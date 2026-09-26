import Submission.Helpers
import Mathlib.Algebra.MonoidAlgebra.Module

open OnPropertyT
open scoped BigOperators

set_option autoImplicit false

namespace Submission.PropertyT

noncomputable section

open Submission.Helpers

variable {G : Type*} [Group G]

/-- In a symmetric set, inverses of elements of `S` lie in `S`. -/
lemma inv_mem_of_mem {S : Finset G} (hsym : (S : Set G)⁻¹ = S) {s : G} (hs : s ∈ S) :
    s⁻¹ ∈ S := by
  classical
  change s⁻¹ ∈ (S : Set G)
  rw [← hsym]
  exact Set.inv_mem_inv.mpr (by simpa using hs)

lemma mem_of_inv_mem {S : Finset G} (hsym : (S : Set G)⁻¹ = S) {s : G} (hs : s⁻¹ ∈ S) :
    s ∈ S := by
  classical
  change s ∈ (S : Set G)
  rw [← hsym]
  exact Set.mem_inv.mpr (by simpa using hs)

/-- The Laplacian of a symmetric set is self-adjoint. -/
lemma star_laplacian (S : Finset G) (hsym : (S : Set G)⁻¹ = S) :
    star (Laplacian S) = Laplacian S := by
  classical
  unfold Laplacian
  rw [star_sub, star_natCast]
  rw [star_sum]
  have hsum : (∑ s ∈ S, star (MonoidAlgebra.of ℝ G s)) = ∑ s ∈ S, MonoidAlgebra.of ℝ G s := by
    rw [show (∑ s ∈ S, star (MonoidAlgebra.of ℝ G s)) = ∑ s ∈ S, MonoidAlgebra.of ℝ G s⁻¹ by
      apply Finset.sum_congr rfl
      intro s hs
      rw [star_of]]
    refine Finset.sum_bij (fun s (_ : s ∈ S) => s⁻¹) ?_ ?_ ?_ ?_
    · intro s hs
      exact inv_mem_of_mem hsym hs
    · intro a ha b hb hab
      exact inv_injective hab
    · intro b hb
      refine ⟨b⁻¹, ?_, ?_⟩
      · exact inv_mem_of_mem hsym hb
      · simp
    · intro a ha
      rfl
  rw [hsum]

/-- Hermitian square: `star ξ * ξ` is star-invariant. -/
lemma star_star_mul (ξ : MonoidAlgebra ℝ G) : star (star ξ * ξ) = star ξ * ξ := by
  rw [star_mul, star_star]

/-- The squared-minus-Laplacian of a symmetric set is star-invariant. -/
lemma star_laplacian_sq_sub (S : Finset G) (Λ : ℝ) (hsym : (S : Set G)⁻¹ = S) :
    star (Laplacian S ^ 2 - Λ • Laplacian S) = Laplacian S ^ 2 - Λ • Laplacian S := by
  classical
  rw [star_sub, star_pow, star_smul, star_laplacian S hsym]

lemma mapDomain_of_hom {H : Type*} [Group H] (φ : G →* H) (g : G) :
    MonoidAlgebra.mapDomain φ (MonoidAlgebra.of ℝ G g) = MonoidAlgebra.of ℝ H (φ g) := by
  simp [MonoidAlgebra.of, MonoidAlgebra.mapDomain_single]

lemma mapDomain_hom_smul {H : Type*} [Group H] (φ : G →* H) (r : ℝ) (x : MonoidAlgebra ℝ G) :
    MonoidAlgebra.mapDomain φ (r • x) = r • MonoidAlgebra.mapDomain φ x := by
  exact (MonoidAlgebra.mapDomainLinearMap (R := ℝ) (S := ℝ) φ).map_smul r x

lemma mapDomain_laplacian {H : Type*} [Group H] [DecidableEq H] (φ : G →* H) (S : Finset G)
    (hinj : Set.InjOn φ (S : Set G)) :
    MonoidAlgebra.mapDomain φ (Laplacian S) = Laplacian (S.image φ) := by
  classical
  unfold Laplacian
  rw [mapDomain_hom_sub, mapDomain_hom_natCast]
  have hsum : MonoidAlgebra.mapDomain φ (∑ s ∈ S, MonoidAlgebra.of ℝ G s)
                = ∑ s ∈ S, MonoidAlgebra.of ℝ H (φ s) := by
    rw [mapDomain_sum_finset]
    apply Finset.sum_congr rfl
    intro s hs
    rw [mapDomain_of_hom]
  rw [hsum]
  have himg : (∑ s ∈ S, MonoidAlgebra.of ℝ H (φ s)) = ∑ t ∈ S.image φ, MonoidAlgebra.of ℝ H t := by
    exact ((Finset.sum_image (s := S) (f := fun t : H => MonoidAlgebra.of ℝ H t) (g := φ)) hinj).symm
  rw [himg]
  have hcard : (Nat.card ↥S : MonoidAlgebra ℝ H) = (Nat.card ↥(S.image φ) : MonoidAlgebra ℝ H) := by
    congr 1
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_coe, Fintype.card_coe]
    exact (Finset.card_image_of_injOn hinj).symm
  rw [hcard]

lemma mapDomain_hom_star_mul {H : Type*} [Group H] (φ : G →* H) (x y : MonoidAlgebra ℝ G) :
    MonoidAlgebra.mapDomain φ (star x * y) =
      star (MonoidAlgebra.mapDomain φ x) * MonoidAlgebra.mapDomain φ y := by
  classical
  rw [mapDomain_hom_mul]
  congr 1
  rw [mapDomain_hom_star]

lemma mapDomain_hom_sum_squares {H : Type*} [Group H] (φ : G →* H)
    (ξ : Finset (MonoidAlgebra ℝ G)) :
    MonoidAlgebra.mapDomain φ (∑ ξi ∈ ξ, star ξi * ξi)
      = ∑ ξi ∈ ξ, star (MonoidAlgebra.mapDomain φ ξi) * MonoidAlgebra.mapDomain φ ξi := by
  classical
  induction ξ using Finset.induction_on with
  | empty =>
      simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      rw [mapDomain_hom_add, ih]
      rw [mapDomain_hom_star_mul]

lemma sum_squares_image {H : Type*} [Group H] [DecidableEq (MonoidAlgebra ℝ H)] (φ : G →* H)
    (ξ : Finset (MonoidAlgebra ℝ G))
    (hinjξ : Set.InjOn (MonoidAlgebra.mapDomain φ) (ξ : Set (MonoidAlgebra ℝ G))) :
    (∑ x ∈ ξ.image (MonoidAlgebra.mapDomain φ), star x * x)
      = ∑ ξi ∈ ξ, star (MonoidAlgebra.mapDomain φ ξi) * MonoidAlgebra.mapDomain φ ξi := by
  classical
  exact (Finset.sum_image (s := ξ) (f := fun x : MonoidAlgebra ℝ H => star x * x)
    (g := MonoidAlgebra.mapDomain φ)) hinjξ

/-- Transfer of a property-(T) certificate along a surjective homomorphism which is
injective on the generating set and on the certificate elements. -/
theorem certificate_transfer {H : Type*} [Group H] [DecidableEq H]
    (φ : G →* H) (hφ : Function.Surjective φ)
    (S : Finset G) (hsym : (S : Set G)⁻¹ = S) (hgen : Subgroup.closure (S : Set G) = ⊤)
    (hinjS : Set.InjOn φ (S : Set G))
    (Λ : ℝ) (hΛ : 0 < Λ)
    (ξ : Finset (MonoidAlgebra ℝ G))
    (hinjξ : Set.InjOn (MonoidAlgebra.mapDomain φ) (ξ : Set (MonoidAlgebra ℝ G)))
    (hξ : Laplacian S ^ 2 - Λ • Laplacian S = ∑ ξi ∈ ξ, star ξi * ξi) :
    PropertyT H := by
  classical
  let T : Finset H := S.image φ
  refine ⟨T, ?_, ?_, Λ, hΛ, ξ.image (MonoidAlgebra.mapDomain φ), ?_⟩
  · -- T is symmetric
    change ((S.image φ : Finset H) : Set H)⁻¹ = (S.image φ : Finset H)
    rw [Finset.coe_image]
    rw [show (φ '' (S : Set G))⁻¹ = φ '' ((S : Set G)⁻¹)
        by exact (Set.image_inv (f := φ) (s := (S : Set G))).symm]
    exact congrArg (Set.image φ) hsym
  · -- T generates
    change Subgroup.closure ((S.image φ : Finset H) : Set H) = ⊤
    rw [Finset.coe_image]
    rw [← MonoidHom.map_closure φ (S : Set G), hgen]
    apply le_antisymm
    · intro x hx
      trivial
    · intro x _
      rcases hφ x with ⟨y, rfl⟩
      exact Subgroup.mem_map.mpr ⟨y, by simp, rfl⟩
  · -- certificate identity in ℝH
    have hp := congrArg (MonoidAlgebra.mapDomain φ) hξ
    have hL : MonoidAlgebra.mapDomain φ (Laplacian S ^ 2 - Λ • Laplacian S)
        = (Laplacian (S.image φ)) ^ 2 - Λ • Laplacian (S.image φ) := by
      rw [mapDomain_hom_sub, mapDomain_hom_pow, mapDomain_hom_smul,
        mapDomain_laplacian φ S hinjS]
    have hR : MonoidAlgebra.mapDomain φ (∑ ξi ∈ ξ, star ξi * ξi)
        = ∑ x ∈ ξ.image (MonoidAlgebra.mapDomain φ), star x * x := by
      rw [mapDomain_hom_sum_squares φ ξ]
      exact (sum_squares_image (H := H) φ ξ hinjξ).symm
    rw [← hL, ← hR]
    exact hp

/-- Property (T) (in the sense of this file) is invariant under isomorphism of groups. -/
theorem propertyT_iso {G H : Type*} [Group G] [Group H] [DecidableEq H]
    (e : G ≃* H) (hpt : PropertyT G) : PropertyT H := by
  classical
  rcases hpt with ⟨S, hsym, hgen, Λ, hΛ, ξ, hξ⟩
  refine certificate_transfer (φ := e) e.surjective S hsym hgen ?hinjS Λ hΛ ξ ?hinjξ hξ
  · intro s hs t ht hst
    exact e.injective hst
  · intro a ha b hb hab
    exact (MonoidAlgebra.mapDomain_injective (R := ℝ) e.injective) hab

end

end Submission.PropertyT
