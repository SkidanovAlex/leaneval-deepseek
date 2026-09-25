import Mathlib
import Submission.Work.HilbertTowerCM.conjugationSubgroup_eq_conjugates
import Submission.Work.HilbertTowerCM.finrank_realPart_eq_card_conj
import Submission.Work.HilbertTowerCM.card_closure_conjugates_of_inversion

/-!
# `Work.HilbertTowerCM.realPart_finrank_eq_index_squares`

The degree of the maximal real subfield of a totally complex Galois number field, in the
situation where the complex conjugation `τ ∈ Gal(L/ℚ)` **inverts** a subgroup `A` of index `2`.

## The hypothesis package

`L/ℚ` is a totally complex Galois number field, `τ ∈ Gal(L/ℚ)` is an involution (`τ * τ = 1`)
which is the complex conjugation at some complex embedding `φ₀` (`ComplexEmbedding.IsConj φ₀ τ`),
and `A ≤ Gal(L/ℚ)` is a subgroup with

* `τ ∉ A` and `G = A ∪ A τ` (`hcover`), i.e. `[G : A] = 2` and `A` is normal;
* `τ a τ⁻¹ = a⁻¹` for all `a ∈ A` (`hcomm`), i.e. `τ` inverts `A`;
* `[L : ℚ] = 2 * |A|` (`hdeg`), which says exactly that `|Gal(L/ℚ)| = 2 |A|`.

## The conclusion

`[L⁺ : ℚ] = |A| / |⟨a² | a ∈ A⟩|`, where `L⁺ = NumberField.maximalRealSubfield L`.

## Proof

The conjugation subgroup `⟨{σ | ∃ φ, IsConj φ σ}⟩ = Gal(L/L⁺)` was identified with the normal
closure of `τ` (`conjugationSubgroup_eq_conjugates`) and `[L : L⁺]` with its order
(`finrank_realPart_eq_card_conj`).  By `card_closure_conjugates_of_inversion`, the hypothesis
package makes that normal closure equal to `T ∪ T τ` for the square subgroup
`T = ⟨{a² | a ∈ A}⟩`, hence `[L : L⁺] = 2 |T|`.  The tower law

`[L : ℚ] = [L⁺ : ℚ] · [L : L⁺]`

combined with `[L : ℚ] = 2 |A|` and `[L : L⁺] = 2 |T|` gives `[L⁺ : ℚ] · |T| = |A|` (after
cancelling the factor `2`), and since `|T| > 0` the claim follows by dividing.
-/

namespace Work.HilbertTowerCM

open NumberField

noncomputable section

/-- **Degree of the maximal real subfield for an inverting co-index-`2` involution.**
If `τ` is a complex conjugation of the totally complex Galois number field `L/ℚ`, if `A ≤ Gal(L/ℚ)`
has index `2`, does not contain `τ`, and is inverted by `τ`, and if `[L : ℚ] = 2 |A|`, then the
maximal real subfield has degree `|A| / |⟨a² | a ∈ A⟩|` over `ℚ`. -/
theorem realPart_finrank_eq_index_squares (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L]
    [NumberField.IsTotallyComplex L] (τ : L ≃ₐ[ℚ] L) (φ₀ : L →+* ℂ)
    (hτ : NumberField.ComplexEmbedding.IsConj φ₀ τ) (hτ2 : τ * τ = 1)
    (A : Subgroup (L ≃ₐ[ℚ] L)) (hτA : τ ∉ A)
    (hcover : ∀ g : L ≃ₐ[ℚ] L, g ∈ A ∨ ∃ a : A, g = (a : L ≃ₐ[ℚ] L) * τ)
    (hcomm : ∀ a : A, τ * (a : L ≃ₐ[ℚ] L) * τ⁻¹ = (a : L ≃ₐ[ℚ] L)⁻¹)
    (hdeg : Module.finrank ℚ L = 2 * Nat.card A) :
    Module.finrank ℚ ↥(NumberField.maximalRealSubfield L) =
      Nat.card A / Nat.card (Subgroup.closure {g : L ≃ₐ[ℚ] L | ∃ a : A, g = (a : L ≃ₐ[ℚ] L) ^ 2}) := by
  classical
  -- The conjugation subgroup `Gal(L/L⁺)` is the normal closure of `τ`.
  have hconj := conjugationSubgroup_eq_conjugates L τ φ₀ hτ
  -- Reindex the normal closure of `τ` as the conjugates `x τ x⁻¹`.
  have hreindex : {g : L ≃ₐ[ℚ] L | ∃ ρ : L ≃ₐ[ℚ] L, g = ρ⁻¹ * τ * ρ} =
      {g : L ≃ₐ[ℚ] L | ∃ x : L ≃ₐ[ℚ] L, g = x * τ * x⁻¹} := by
    ext g; constructor
    · rintro ⟨ρ, rfl⟩; exact ⟨ρ⁻¹, by rw [inv_inv]⟩
    · rintro ⟨x, rfl⟩; exact ⟨x⁻¹, by rw [inv_inv]⟩
  -- The normal closure of `τ` has twice the order of the square subgroup of `A`.
  have hcard := card_closure_conjugates_of_inversion
    (G := L ≃ₐ[ℚ] L) A τ hτA hτ2 hcover hcomm
  -- Hence `[L : L⁺] = 2 * |⟨{a² | a ∈ A}⟩|`.
  have hd : Module.finrank ↥(NumberField.maximalRealSubfield L) L =
      2 * Nat.card (Subgroup.closure {g : L ≃ₐ[ℚ] L | ∃ a : A, g = (a : L ≃ₐ[ℚ] L) ^ 2}) := by
    rw [finrank_realPart_eq_card_conj L, hconj, hreindex, hcard]
  -- The square subgroup is nontrivial, so its order can be divided by.
  have hzero : 0 < Nat.card (Subgroup.closure {g : L ≃ₐ[ℚ] L | ∃ a : A, g = (a : L ≃ₐ[ℚ] L) ^ 2}) := by
    rw [Nat.card_pos_iff]
    exact ⟨⟨1, Subgroup.one_mem _⟩, inferInstance⟩
  -- The tower law, combined with `[L : ℚ] = 2 |A|`, gives `[L⁺ : ℚ] * |T| = |A|`.
  have hmain : Module.finrank ℚ ↥(NumberField.maximalRealSubfield L) *
      Nat.card (Subgroup.closure {g : L ≃ₐ[ℚ] L | ∃ a : A, g = (a : L ≃ₐ[ℚ] L) ^ 2}) =
      Nat.card A := by
    have h := Module.finrank_mul_finrank ℚ ↥(NumberField.maximalRealSubfield L) L
    rw [hd] at h
    rw [hdeg] at h
    rw [Nat.mul_left_comm] at h
    exact Nat.mul_left_cancel (by norm_num) h
  rw [← hmain, Nat.mul_div_left _ hzero]

end

end Work.HilbertTowerCM
