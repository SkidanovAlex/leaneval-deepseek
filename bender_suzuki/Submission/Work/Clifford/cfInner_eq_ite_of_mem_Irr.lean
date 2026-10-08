import Mathlib
import Submission.Work.Clifford.CFun
import Submission.Work.CharCore.star_trace_eq_trace_pow

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Clifford.cfInner_eq_ite_of_mem_Irr`

The orthonormality of the irreducible complex characters of a finite group for the
character inner product `Work.Clifford.cfInner`:

`⟪χ, ψ⟫ = 1` if `χ = ψ` and `= 0` otherwise, for `χ, ψ ∈ Irr G`.

The proof reduces to Mathlib's `FDRep.char_orthonormal`, using
`Work.CharCore.star_trace_eq_trace_pow` (a finite order element of `GL(V)` has eigenvalues that
are roots of unity, so the trace of its inverse is the complex conjugate of its trace) to convert
the `star` in the definition of `cfInner` into evaluation at the inverse element, and the diagonal
case of `FDRep.char_orthonormal` to see that two simple finite dimensional complex representations
with the same character are isomorphic.
-/

noncomputable section

open Classical

namespace Work.Clifford

variable {G : Type*} [Group G] [Fintype G]

/-- For a finite group, the order `Nat.card G` is invertible in `ℂ`. -/
instance instInvertibleNatCardComplex : Invertible (Nat.card G : ℂ) :=
  invertibleOfNonzero (by
    have := Nat.card_pos (α := G)
    exact_mod_cast this.ne')

/-- The value of the character of a complex representation at the inverse of an element is the
complex conjugate of its value at that element: `χ (g⁻¹) = conj (χ g)`.

This holds because `(V.ρ g) ^ orderOf g = 1`: the eigenvalues of `V.ρ g` are roots of unity, so
the trace of its inverse `(V.ρ g) ^ (orderOf g - 1) = V.ρ g⁻¹` is the conjugate of its trace,
by `Work.CharCore.star_trace_eq_trace_pow`. -/
theorem star_char_eq_char_inv (V : FDRep ℂ G) (g : G) :
    starRingEnd ℂ (V.character g) = V.character g⁻¹ := by
  have hn : 0 < orderOf g := orderOf_pos g
  have hT : (V.ρ g) ^ orderOf g = 1 := by
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  have h := Work.CharCore.star_trace_eq_trace_pow (V := V) (V.ρ g) (orderOf g) hn hT
  have hpow : (V.ρ g) ^ (orderOf g - 1) = V.ρ g⁻¹ := by
    rw [← map_pow]
    congr 1
    apply eq_inv_of_mul_eq_one_right
    rw [← pow_succ', tsub_add_cancel_of_le hn, pow_orderOf_eq_one]
  simp only [FDRep.character]
  rw [h, hpow]

/-- Two simple finite dimensional complex representations with the same character are
isomorphic.  This is the converse of `FDRep.char_iso`; it follows from the diagonal case of
the orthogonality of characters. -/
theorem nonempty_iso_of_char_eq (V W : FDRep ℂ G) [CategoryTheory.Simple V]
    [CategoryTheory.Simple W] (h : V.character = W.character) : Nonempty (V ≅ W) := by
  have h1 : (Nat.card G : ℂ)⁻¹ * ∑ g : G, V.character g * V.character g⁻¹ = 1 := by
    rw [FDRep.char_orthonormal V V]
    simp
  have h2 : (Nat.card G : ℂ)⁻¹ * ∑ g : G, V.character g * W.character g⁻¹ =
      (if Nonempty (V ≅ W) then (1 : ℂ) else 0) := FDRep.char_orthonormal V W
  rw [h] at h1 h2
  rw [h2] at h1
  by_contra hne
  rw [if_neg hne] at h1
  exact zero_ne_one h1

/-- **Orthonormality of the characters of the simple finite dimensional complex representations**
of a finite group, in the form needed here. -/
theorem cfInner_char_eq_ite (V W : FDRep ℂ G) [CategoryTheory.Simple V]
    [CategoryTheory.Simple W] :
    cfInner V.character W.character = if V.character = W.character then 1 else 0 := by
  have hstar : ∀ g : G, starRingEnd ℂ (W.character g) = W.character g⁻¹ :=
    fun g => star_char_eq_char_inv W g
  have hsum : (∑ x : G, V.character x * starRingEnd ℂ (W.character x)) =
      ∑ x : G, V.character x * W.character x⁻¹ :=
    Finset.sum_congr rfl fun x _ => by rw [hstar x]
  rw [cfInner, Fintype.card_eq_nat_card, hsum, FDRep.char_orthonormal V W]
  by_cases h : Nonempty (V ≅ W)
  · rw [if_pos h, if_pos (by obtain ⟨e⟩ := h; exact FDRep.char_iso e)]
  · rw [if_neg h, if_neg fun hc => h (nonempty_iso_of_char_eq V W hc)]

theorem cfInner_eq_ite_of_mem_Irr {G : Type*} [Group G] [Fintype G] {χ ψ : G → ℂ}
    (hχ : χ ∈ Work.Clifford.Irr G) (hψ : ψ ∈ Work.Clifford.Irr G) :
    Work.Clifford.cfInner χ ψ = if χ = ψ then 1 else 0 := by
  obtain ⟨V, hV, hVχ⟩ := hχ
  obtain ⟨W, hW, hWχ⟩ := hψ
  haveI := hV
  haveI := hW
  rw [← hVχ, ← hWχ]
  exact cfInner_char_eq_ite V W

end Work.Clifford
