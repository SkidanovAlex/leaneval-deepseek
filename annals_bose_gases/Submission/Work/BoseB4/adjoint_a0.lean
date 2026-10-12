import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Submission.Work.BoseB4.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.adjoint_a0` — condensate creation is the adjoint of annihilation

On the algebraic core `FockCore E = ℕ →₀ E` of the Fock space
`Fock E = ⨁_{n ∈ ℕ} E` the condensate ladder operators are

    `(a0 Ψ) n = √(n+1) • Ψ (n+1)`,   `(a0d Ψ') n = √n • Ψ' (n-1)`

(`Defs.a0_apply`, `Defs.a0d_apply`), with respect to the inner product of
`Fock E` inherited through the inclusion `Embed : FockCore E →ₗ[ℂ] Fock E`.
The **ladder weights are real** (`star_sq`) and Fock components of *distinct*
condensate levels are orthogonal (`inner_level_level`), so the level shifting
`n ↦ n+1` on the left is the level shifting `n+1 ↦ n` on the right, with the
weight `√(n+1)` unchanged by complex conjugation:

    `⟪a₀Ψ, Ψ'⟫ = ⟪Ψ, a₀†Ψ'⟫`.

Equivalently `a₀†` (creation) is the *Hilbert adjoint* of `a₀` (annihilation)
on the core — the first structural fact about the second-quantised operators of
FS §8 used in the `c`-number substitution `thm:Kafz`. The mirror statement
`⟪a₀†Ψ, Ψ'⟫ = ⟪Ψ, a₀Ψ'⟫` is `adjoint_a0d`, and the analytic layer of
`Submission/Work/BoseB4/Coherent.lean` (coherent states, Bargmann isometry)
builds on both.
-/

open scoped lp

namespace Work.BoseB4

set_option autoImplicit false

/-! ## 1. Component extraction: the levels `level a` are `Embed`-adjoint to evaluation -/

/-- The `a`-th condensate level against a core vector: this is the extraction of
the `a`-th Fock component, `⟪e_a ⊗ u, Ψ⟫ = ⟪u, Ψ a⟫`. -/
lemma inner_level_Embed {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (a : ℕ) (u : E) (Ψ : FockCore E) :
    inner ℂ (level E a u) (Embed E Ψ) = inner ℂ u (Ψ a) := by
  rw [show level E a u = lp.single 2 a u from rfl, lp.inner_single_left, Embed_apply]

/-- The conjugate direction of `inner_level_Embed`. -/
lemma inner_Embed_level {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (a : ℕ) (u : E) (Ψ : FockCore E) :
    inner ℂ (Embed E Ψ) (level E a u) = inner ℂ (Ψ a) u := by
  rw [show level E a u = lp.single 2 a u from rfl, lp.inner_single_right, Embed_apply]

/-! ## 2. The ladder weights are real and distinct levels are orthogonal -/

/-- The ladder weight `√n` is a real scalar, fixed by complex conjugation. -/
lemma star_sq (a : ℕ) : (starRingEnd ℂ) (sq a) = sq a := by simp [sq]

/-- Condensate levels at different occupations are orthogonal, and at equal
occupation the pairing is the spectator inner product. -/
lemma inner_level_level {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (m n : ℕ) (u v : E) :
    inner ℂ (level E m u) (level E n v) = if m = n then inner ℂ u v else 0 := by
  rw [← Embed_single (E := E) n v, inner_level_Embed]
  by_cases h : m = n
  · subst h; simp
  · rw [if_neg h, Finsupp.single_eq_of_ne h, inner_zero_right]

/-! ## 3. The adjointness statements -/

/-- **`a₀†` is the Hilbert adjoint of `a₀`** on the Fock core: annihilation
lowers the condensate number by one and creation raises it by one, and the
weight `√(n+1)` is real, so the two pairings agree. -/
theorem adjoint_a0 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (Ψ Ψ' : Work.BoseB4.FockCore E) :
    inner ℂ (Work.BoseB4.Embed E (Work.BoseB4.a0 Ψ)) (Work.BoseB4.Embed E Ψ')
      = inner ℂ (Work.BoseB4.Embed E Ψ) (Work.BoseB4.Embed E (Work.BoseB4.a0d Ψ')) := by
  revert Ψ'
  induction Ψ using Finsupp.induction_linear with
  | zero => intro Ψ'; simp
  | add f g hf hg =>
      intro Ψ'
      simp only [map_add]
      rw [inner_add_left, hf Ψ', hg Ψ', inner_add_left]
  | single a u =>
      intro Ψ'
      rw [a0_single, Embed_single, Embed_single, inner_level_Embed,
        inner_level_Embed, a0d_apply, inner_smul_left, inner_smul_right, star_sq]

/-- The mirror image of `adjoint_a0`: `a₀` is the Hilbert adjoint of `a₀†`. -/
theorem adjoint_a0d {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (Ψ Ψ' : Work.BoseB4.FockCore E) :
    inner ℂ (Work.BoseB4.Embed E (Work.BoseB4.a0d Ψ)) (Work.BoseB4.Embed E Ψ')
      = inner ℂ (Work.BoseB4.Embed E Ψ) (Work.BoseB4.Embed E (Work.BoseB4.a0 Ψ')) := by
  revert Ψ'
  induction Ψ using Finsupp.induction_linear with
  | zero => intro Ψ'; simp
  | add f g hf hg =>
      intro Ψ'
      simp only [map_add]
      rw [inner_add_left, hf Ψ', hg Ψ', inner_add_left]
  | single a u =>
      intro Ψ'
      rw [a0d_single, Embed_single, Embed_single, inner_level_Embed,
        inner_level_Embed, a0_apply, inner_smul_left, inner_smul_right, star_sq]

end Work.BoseB4
