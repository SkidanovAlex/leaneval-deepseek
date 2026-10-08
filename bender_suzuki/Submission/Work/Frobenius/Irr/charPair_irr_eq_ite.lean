import Mathlib
import Submission.Work.Frobenius.Pair

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Orthonormality of irreducible characters for the bilinear trace pairing

`Work.Frobenius.charPair χ ψ = |G|⁻¹ * ∑ x, χ x * ψ x⁻¹` is the bilinear trace pairing on
complex functions on a finite group.  On the irreducible characters
(`Work.Frobenius.Irr G`, the characters of the irreducible finite dimensional complex
representations) it is the standard orthonormal pairing: `charPair χ ψ = 1` if `χ = ψ`
and `= 0` otherwise (this module, `charPair_irr_eq_ite`).

The proof is a direct application of Mathlib's `Representation.char_orthonormal`, which
computes the same sum as the dimension of the space of intertwining maps between the two
representations.  Converting the resulting criterion `Nonempty (Equiv σ ρ)`, i.e. the
existence of an isomorphism of representations, into the equality of characters requires
the converse direction "equal characters of irreducible representations over `ℂ` are
isomorphic" (`nonempty_equiv_of_char_eq`), which is proved from the diagonal case of
orthonormality exactly as in `Work.Clifford.nonempty_iso_of_char_eq`.
-/

@[expose] public section

noncomputable section

open Classical

namespace Work.Frobenius.Irr

variable {G : Type*} [Group G] [Fintype G]

/-- For a finite group the order `Nat.card G` is invertible in `ℂ`. -/
instance instInvertibleNatCardComplex : Invertible (Nat.card G : ℂ) :=
  invertibleOfNonzero (by
    have := Nat.card_pos (α := G)
    exact_mod_cast this.ne')

/-- Two irreducible finite dimensional complex representations with the same character are
isomorphic.  This is the converse of `Representation.char_iso`; it follows from the diagonal
case of `Representation.char_orthonormal`.

The statement is phrased with the conclusion `Nonempty (σ.Equiv ρ)`, i.e. in the same order of
arguments as the `if` in `Representation.char_orthonormal ρ σ`, so that it can be applied
directly to identify the two `if` conditions in `charPair_irr_eq_ite`. -/
theorem nonempty_equiv_of_char_eq {G : Type*} [Group G] [Fintype G]
    {V W : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    [Representation.IsIrreducible ρ] [Representation.IsIrreducible σ]
    (h : ρ.character = σ.character) : Nonempty (Representation.Equiv σ ρ) := by
  have h1 : (Nat.card G : ℂ)⁻¹ * ∑ g : G, σ.character g * σ.character g⁻¹ = 1 := by
    rw [Representation.char_orthonormal σ σ]
    exact if_pos ⟨Representation.Equiv.refl σ⟩
  have h2 : (Nat.card G : ℂ)⁻¹ * ∑ g : G, ρ.character g * σ.character g⁻¹ =
      (if Nonempty (Representation.Equiv σ ρ) then (1 : ℂ) else 0) :=
    Representation.char_orthonormal ρ σ
  rw [h] at h2
  rw [h2] at h1
  by_contra hne
  rw [if_neg hne] at h1
  exact zero_ne_one h1

theorem charPair_irr_eq_ite {G : Type*} [Group G] [Fintype G] {χ ψ : G → ℂ}
    (hχ : χ ∈ Irr G) (hψ : ψ ∈ Irr G) :
    charPair χ ψ = if χ = ψ then 1 else 0 := by
  obtain ⟨d, rfl⟩ := hχ
  obtain ⟨e, rfl⟩ := hψ
  have hd : Representation.IsIrreducible d.ρ := d.irred
  have he : Representation.IsIrreducible e.ρ := e.irred
  rw [charPair_apply, Representation.char_orthonormal d.ρ e.ρ]
  by_cases h : Nonempty (Representation.Equiv e.ρ d.ρ)
  · rw [if_pos h, if_pos]
    exact (Representation.char_iso h.some).symm
  · rw [if_neg h, if_neg]
    intro hc
    exact h (nonempty_equiv_of_char_eq d.ρ e.ρ hc)

end Work.Frobenius.Irr
