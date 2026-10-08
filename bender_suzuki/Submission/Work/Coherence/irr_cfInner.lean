import Mathlib
import Submission.Work.Coherence.Basic
import Submission.Work.CharCore.star_trace_eq_trace_pow

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Coherence.irr_cfInner`

The orthonormality of the irreducible complex characters of a finite group for the character
inner product `Work.Coherence.cfInner`:

`⟪χ, ψ⟫ = 1` if `χ = ψ` and `= 0` otherwise, for `χ, ψ ∈ Irr G`.

Since `Irr G` is the set of characters of the simple finite dimensional complex representations
of `G`, this is the classical orthogonality relation for characters.  The proof reduces to
Mathlib's `FDRep.char_orthonormal`, using `Work.CharCore.star_trace_eq_trace_pow` (a finite
order element of `GL(V)` has eigenvalues that are roots of unity, so the trace of the inverse
is the complex conjugate of the trace) to convert the `star` in the definition of `cfInner`
into evaluation at the inverse element.
-/

noncomputable section

open Classical Finset

namespace Work.Coherence

universe u

section Helpers

variable {G : Type u} [Group G] [Fintype G]

/-- For a finite group, the order of `G` is invertible in `ℂ`. -/
instance instInvertibleNatCardComplex : Invertible (Nat.card G : ℂ) :=
  invertibleOfNonzero (by
    have := Nat.card_pos (α := G)
    exact_mod_cast this.ne')

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- The character of a finite dimensional complex representation takes at the inverse of an
element the complex conjugate of its value at that element: `χ (g⁻¹) = conj (χ g)`.

This holds because `(ρ g) ^ (orderOf g) = 1`, so `ρ g` has finite order; by
`Work.CharCore.star_trace_eq_trace_pow` the trace of the conjugate of `LinearMap.trace` is the
trace of `(ρ g) ^ (orderOf g - 1) = ρ g⁻¹`. -/
theorem star_trace_eq_trace_inv (ρ : Representation ℂ G V) (g : G) :
    starRingEnd ℂ (ρ.character g) = ρ.character g⁻¹ := by
  have hn : 0 < orderOf g := orderOf_pos g
  have hT : (ρ g) ^ orderOf g = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
  have h := Work.CharCore.star_trace_eq_trace_pow (ρ g) (orderOf g) hn hT
  have hpow : (ρ g) ^ (orderOf g - 1) = ρ g⁻¹ := by
    rw [← map_pow]
    congr 1
    apply eq_inv_of_mul_eq_one_right
    rw [← pow_succ', Nat.sub_add_cancel hn, pow_orderOf_eq_one]
  simp only [Representation.character]
  rw [h, hpow]

/-- The character of a finite dimensional complex representation, evaluated at the inverse of an
element, is the complex conjugate of its value at that element. -/
theorem representation_char_inv_eq_conj (ρ : Representation ℂ G V) (g : G) :
    ρ.character g⁻¹ = starRingEnd ℂ (ρ.character g) :=
  (star_trace_eq_trace_inv ρ g).symm

end Helpers

section FDRep

variable {G : Type u} [Group G] [Fintype G]

/-- The character of a finite dimensional complex representation, evaluated at the inverse of an
element, is the complex conjugate of its value at that element (`FDRep` version). -/
theorem fdRep_char_inv_eq_conj (V : FDRep ℂ G) (g : G) :
    V.character g⁻¹ = starRingEnd ℂ (V.character g) :=
  representation_char_inv_eq_conj (V := V) V.ρ g

/-- Two simple finite dimensional complex representations with the same character are
isomorphic.  This is the converse of `FDRep.char_iso`; it follows from the diagonal case of the
orthogonality of characters. -/
theorem nonempty_iso_of_char_eq (V W : FDRep ℂ G) [CategoryTheory.Simple V]
    [CategoryTheory.Simple W] (h : V.character = W.character) : Nonempty (V ≅ W) := by
  haveI := instInvertibleNatCardComplex (G := G)
  have h1 : (Nat.card G : ℂ)⁻¹ * ∑ g : G, V.character g * V.character g⁻¹ = 1 := by
    rw [FDRep.char_orthonormal V V]
    exact if_pos ⟨CategoryTheory.Iso.refl V⟩
  have h2 : (Nat.card G : ℂ)⁻¹ * ∑ g : G, V.character g * W.character g⁻¹ =
      (if Nonempty (V ≅ W) then (1 : ℂ) else 0) := FDRep.char_orthonormal V W
  rw [h] at h1 h2
  by_contra hne
  rw [if_neg hne] at h2
  rw [h1] at h2
  exact one_ne_zero h2

/-- **Orthonormality of the characters of simple finite dimensional complex representations**:
the characters of two simple representations are orthonormal for `cfInner`. -/
theorem cfInner_char_eq_ite (V W : FDRep ℂ G) [CategoryTheory.Simple V]
    [CategoryTheory.Simple W] :
    cfInner V.character W.character = if V.character = W.character then 1 else 0 := by
  haveI := instInvertibleNatCardComplex (G := G)
  have hstar : ∀ x : G, starRingEnd ℂ (W.character x) = W.character x⁻¹ :=
    fun x => (fdRep_char_inv_eq_conj W x).symm
  have hsum : (∑ x : G, V.character x * starRingEnd ℂ (W.character x)) =
      ∑ x : G, V.character x * W.character x⁻¹ :=
    Finset.sum_congr rfl fun x _ => by rw [hstar x]
  rw [cfInner, Fintype.card_eq_nat_card, hsum, FDRep.char_orthonormal V W]
  by_cases h : Nonempty (V ≅ W)
  · rw [if_pos h, if_pos (by obtain ⟨e⟩ := h; exact FDRep.char_iso e)]
  · rw [if_neg h, if_neg fun hc => h (nonempty_iso_of_char_eq V W hc)]

end FDRep

/-- **Orthonormality of the irreducible complex characters**: for `χ, ψ ∈ Irr G` the character
inner product `⟪χ, ψ⟫` is `1` if `χ = ψ` and `0` otherwise. -/
theorem irr_cfInner {G : Type*} [Group G] [Fintype G] {χ ψ : G → ℂ}
    (hχ : χ ∈ Irr G) (hψ : ψ ∈ Irr G) :
    cfInner χ ψ = if χ = ψ then 1 else 0 := by
  obtain ⟨V, hV, hVχ⟩ := mem_Irr.mp hχ
  obtain ⟨W, hW, hWχ⟩ := mem_Irr.mp hψ
  haveI := hV
  haveI := hW
  rw [← hVχ, ← hWχ]
  exact cfInner_char_eq_ite V W

end Work.Coherence
