import Mathlib
import Submission.Work.A7REC.Char.Y6Defs

namespace Work.A7REC.Char

/-- The trace of the identity endomorphism equals the dimension, with **no** finiteness hypothesis
on `V`.  `LinearMap.trace` is the trace along some finite basis when one exists and `0` otherwise
(see its definition in `Mathlib/LinearAlgebra/Trace.lean`); correspondingly `Module.finrank` is `0`
as soon as no finite basis exists (`finrank_eq_zero_of_not_exists_basis_finset`).  Over a field the
`Module.Free` instance needed by that lemma is `Module.Free.of_divisionRing`. -/
theorem trace_one_of_module (V : Type) [AddCommGroup V] [Module ℂ V] :
    LinearMap.trace ℂ V (1 : V →ₗ[ℂ] V) = (Module.finrank ℂ V : ℂ) := by
  classical
  by_cases H : ∃ s : Finset V, Nonempty (Module.Basis s ℂ V)
  · obtain ⟨s, ⟨b⟩⟩ := H
    rw [LinearMap.trace_eq_matrix_trace ℂ b 1, LinearMap.toMatrix_one, Matrix.trace_one,
      Module.finrank_eq_card_basis b]
  · rw [LinearMap.trace, dite_eq_right H, finrank_eq_zero_of_not_exists_basis_finset H,
      Nat.cast_zero]
    simp

/-- **Faithfulness** (`A7RepNeOneProp`).  If `G` is simple and `ρ z` has trace different from the
dimension, then `ρ` kills no non-identity element.

Indeed, if `ρ x = 1` for some `x ≠ 1`, then the kernel of the monoid homomorphism `ρ` is a
non-trivial normal subgroup of `G`, hence all of `G` by simplicity; so `ρ` is the trivial
representation, `ρ z = 1`, and the trace of the identity is the dimension
(`trace_one_of_module`), contradicting the hypothesis. -/
theorem Y6RepNeOne : Work.A7REC.A7RepNeOneProp := by
  intro G _ V _ _ ρ z hsimple hz x hx hρx
  -- `x` lies in the (normal) kernel of `ρ`, so the kernel is non-trivial.
  have hxker : x ∈ MonoidHom.ker ρ := MonoidHom.mem_ker.mpr hρx
  have hker : MonoidHom.ker ρ = ⊤ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal (MonoidHom.ker ρ) with h | h
    · exfalso
      rw [h] at hxker
      exact hx (Subgroup.mem_bot.mp hxker)
    · exact h
  -- Hence `ρ` is the trivial representation and `ρ z = 1`.
  have hz1 : ρ z = 1 := by
    have : z ∈ MonoidHom.ker ρ := by rw [hker]; exact Subgroup.mem_top z
    exact MonoidHom.mem_ker.mp this
  -- The trace of the identity is the dimension, contradicting the hypothesis.
  exact hz (by rw [hz1]; exact trace_one_of_module V)

end Work.A7REC.Char
