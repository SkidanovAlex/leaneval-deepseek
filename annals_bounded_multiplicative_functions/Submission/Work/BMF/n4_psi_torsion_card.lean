import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.n4_torsion_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

/-- **The number of characters mod `q` whose `m`-th power is trivial equals the number of
`m`-th roots of unity mod `q`.**

This is finite-abelian-group duality: `DirichletCharacter ℂ q` is the dual group of
`(ZMod q)ˣ` (`MulChar.toUnitHom` is an equivalence onto `(ZMod q)ˣ →* ℂˣ`), and for a finite
abelian group `G` the `m`-torsion of `G` and of its dual have equal cardinality
(both equal `∏ᵢ gcd(nᵢ, m)` for `G ≅ ⊕ ℤ/nᵢ`).  Equivalently, both sides equal the number of
`A ∈ (ZMod q)ˣ` with `A^m = 1`, computed by orthogonality:
`Σ_ψ 1_{ψ^m = 1} = (1/φ(q)) Σ_{A} Σ_ψ ψ(A^m) = (1/φ(q)) Σ_A φ(q) 1_{A^m = 1}`,
using `Σ_ψ ψ(x) = φ(q)·1_{x=1}` (Chen's `sum_char_mul_conj` with `b = 1`) and
`Σ_{A ∈ (ZMod q)ˣ} χ(A) = φ(q)·1_{χ=1}` (for `χ ≠ 1`, multiply by `χ(B)` for some `B` with
`χ(B) ≠ 1` and reindex `A ↦ A·B`).  This is exactly the MRTTZ (3.12) duality count: the
multiplicity of the principal character in the `m`-th power map is the number of `m`-th roots
of unity mod `q`. -/
theorem n4_psi_torsion_card (q m : ℕ) [NeZero q] :
    ((Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun ψ ↦ ψ ^ m = 1)).card
      = ((Finset.univ : Finset (ZMod q)ˣ).filter (fun ζ ↦ ζ ^ m = 1)).card := by
  -- Noncanonical duality: the group of Dirichlet characters mod `q` is isomorphic to `(ZMod q)ˣ`.
  obtain ⟨e⟩ := MulChar.mulEquiv_units (ZMod q) ℂ
  -- A group isomorphism carries `m`-torsion to `m`-torsion.
  refine Finset.card_bij (fun ψ _ ↦ e ψ) ?_ ?_ ?_
  · intro ψ hψ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hψ ⊢
    rw [← map_pow, hψ, map_one]
  · intro ψ₁ _ ψ₂ _ h
    exact e.injective h
  · intro ζ hζ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hζ ⊢
    refine ⟨e.symm ζ, ?_, e.apply_symm_apply ζ⟩
    apply e.injective
    rw [map_pow, e.apply_symm_apply, hζ, map_one]

end Work.BMF
