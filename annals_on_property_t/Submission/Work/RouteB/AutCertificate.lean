import Submission.Work.RouteB.IndexTwo
import Submission.Work.RouteB.Generation
import Submission.Commons.Algebra.MonoidAlgebra.conj_laplacian
import Submission.Commons.GroupTheory.FreeGroup.sigma_conj_mem_SAutGen
import Submission.Commons.GroupTheory.FreeGroup.sigma_notMem_SAutGen

open OnPropertyT Submission.FreeGroupAut Submission.Helpers
open FreeGroup
open scoped BigOperators

set_option autoImplicit false

namespace Submission.Nielsen

noncomputable section

/-!
# Route B assembly: a certificate for `SAut(F_n)` gives property (T) for `Aut(F_n)`

This file combines the two Route-B pieces proved in this session:

* `RouteB.propertyT_of_index_two_extension` (certificate ascends across an
  index-two extension), and
* `closure_sAutGen_insert_sigma` (`SAutGen n ∪ {σᵢ}` generates `Aut(F_n)`),

into the end-to-end statement: **a property-(T) certificate for `SAut(F_n)` with
respect to the standard transvection generating set `SAutGen n` yields property
(T) for `Aut(F_n)`** (with the explicit generating set `SAutGen n ∪ {σᵢ}`).

The only remaining inputs are the finite computations
`∀ g ∈ SAutGen n, σᵢ g σᵢ ∈ SAutGen n` (that `σᵢ` normalises the transvection
set — delegated to the commons) and `σᵢ ∉ SAutGen n`; the paper's
computer-assisted certificate for `SAut(F_n)` then remains the sole mathematical
input.
-/

/-- `σᵢ` is an involution. -/
lemma sigma_mul_self {n : ℕ} (i : Fin n) : sigma i * sigma i = 1 := by
  calc sigma i * sigma i = (sigma i)⁻¹ * sigma i := by rw [sigma_inv i]
    _ = 1 := inv_mul_cancel (sigma i)

/-- Conjugating the transvection Laplacian by `σᵢ` leaves it invariant, provided
`σᵢ` normalises the transvection generating set (the commons lemma
`Commons.GroupTheory.FreeGroup.sigma_conj_mem_SAutGen` supplies this). -/
lemma sigma_conj_laplacian (n : ℕ) (i : Fin n)
    (hconj : ∀ g ∈ SAutGen n, sigma i * g * sigma i ∈ SAutGen n) :
    MonoidAlgebra.of ℝ (MulAut (FreeGroup (Fin n))) (sigma i)
        * OnPropertyT.Laplacian (SAutGen n)
        * MonoidAlgebra.of ℝ (MulAut (FreeGroup (Fin n))) (sigma i)
      = OnPropertyT.Laplacian (SAutGen n) := by
  classical
  change MonoidAlgebra.of ℝ (MulAut (FreeGroup (Fin n))) (sigma i)
      * Commons.Algebra.MonoidAlgebra.Laplacian (SAutGen n)
      * MonoidAlgebra.of ℝ (MulAut (FreeGroup (Fin n))) (sigma i)
    = Commons.Algebra.MonoidAlgebra.Laplacian (SAutGen n)
  have h := Commons.Algebra.MonoidAlgebra.conj_laplacian (SAutGen n) (sigma i)
  rw [sigma_inv i] at h
  rw [h]
  congr 1
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · rw [Finset.image_subset_iff]
    intro g hg
    exact hconj g hg
  · have hcard : (Finset.image (fun s : MulAut (FreeGroup (Fin n)) => (sigma i * s) * sigma i)
        (SAutGen n)).card = (SAutGen n).card :=
      Finset.card_image_of_injOn (fun a _ b _ hab => by
        rw [mul_assoc, mul_assoc] at hab
        exact mul_right_cancel (mul_left_cancel hab))
    rw [hcard]

/-- **Route B assembly.**  From a property-(T) certificate for `SAut(F_n)` with
respect to the transvection generating set `SAutGen n` — plus the finite input
`σᵢ ∉ SAutGen n` — one gets property (T) for `Aut(F_n)` (with the explicit
generating set `SAutGen n ∪ {σᵢ}` and `Λ = min Λ₀ 1`). -/
theorem propertyT_aut_of_sAutGen_certificate (n : ℕ) (i : Fin n)
    (hconj : ∀ g ∈ SAutGen n, sigma i * g * sigma i ∈ SAutGen n)
    (hnot : sigma i ∉ SAutGen n)
    (Λ₀ : ℝ) (hΛ₀ : 0 < Λ₀)
    (ξ : Finset (MonoidAlgebra ℝ (MulAut (FreeGroup (Fin n)))))
    (hξ : OnPropertyT.Laplacian (SAutGen n) ^ 2 - Λ₀ • OnPropertyT.Laplacian (SAutGen n)
      = ∑ x ∈ ξ, star x * x) :
    PropertyT (MulAut (FreeGroup (Fin n))) :=
  RouteB.propertyT_of_index_two_extension (SAutGen n) (sAutGen_symm n) (sigma i) (sigma_mul_self i)
    hnot (sigma_conj_laplacian n i hconj) (closure_sAutGen_insert_sigma n i) Λ₀ hΛ₀ ξ hξ

/-- **Route B assembly.**  From a property-(T) certificate for `SAut(F_n)` with
respect to the transvection generating set `SAutGen n` — plus the two finite
inputs `σᵢ` normalises `SAutGen n` and `σᵢ ∉ SAutGen n` — one gets property (T)
for `Aut(F_n)` (with the explicit generating set `SAutGen n ∪ {σᵢ}` and
`Λ = min Λ₀ 1`). -/
theorem propertyT_aut_of_sAutGen_certificate' (n : ℕ) (i : Fin n)
    (hnot : sigma i ∉ SAutGen n)
    (Λ₀ : ℝ) (hΛ₀ : 0 < Λ₀)
    (ξ : Finset (MonoidAlgebra ℝ (MulAut (FreeGroup (Fin n)))))
    (hξ : OnPropertyT.Laplacian (SAutGen n) ^ 2 - Λ₀ • OnPropertyT.Laplacian (SAutGen n)
      = ∑ x ∈ ξ, star x * x) :
    PropertyT (MulAut (FreeGroup (Fin n))) :=
  propertyT_aut_of_sAutGen_certificate n i
    (fun g hg => Commons.GroupTheory.FreeGroup.sigma_conj_mem_SAutGen n i hg)
    hnot Λ₀ hΛ₀ ξ hξ

/-- **Route B assembly (fully assembled).**  A property-(T) certificate for
`SAut(F_n)` with respect to the standard transvection generating set `SAutGen n`
— and nothing else — yields property (T) for `Aut(F_n)`, with the explicit
generating set `SAutGen n ∪ {σᵢ}` and `Λ = min Λ₀ 1`.  This is the exact
interface between the paper's computer-assisted input and the challenge
statement. -/
theorem propertyT_aut_of_sAutGen_certificate'' (n : ℕ) (i : Fin n)
    (Λ₀ : ℝ) (hΛ₀ : 0 < Λ₀)
    (ξ : Finset (MonoidAlgebra ℝ (MulAut (FreeGroup (Fin n)))))
    (hξ : OnPropertyT.Laplacian (SAutGen n) ^ 2 - Λ₀ • OnPropertyT.Laplacian (SAutGen n)
      = ∑ x ∈ ξ, star x * x) :
    PropertyT (MulAut (FreeGroup (Fin n))) :=
  propertyT_aut_of_sAutGen_certificate' n i
    (Commons.GroupTheory.FreeGroup.sigma_notMem_SAutGen n i) Λ₀ hΛ₀ ξ hξ

end

end Submission.Nielsen
