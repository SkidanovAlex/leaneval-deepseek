import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Obligation 1, last piece: `normalClosure` is the sup of the conjugates

On an ambient field `Ω` that is **normal over `k`** (e.g. `Ω = AlgebraicClosure K`, where
`IsAlgClosure k Ω` holds), Mathlib's `normalClosure_def''` reads

    `normalClosure k E Ω = ⨆ σ : Ω ≃ₐ[k] Ω, E.map σ`,

so the normal closure of `E` is *literally* the sup of its `k`-conjugates, and the generation
hypothesis `hgenL` of `Work.SSGRoute.Sha2Lib.inertia_eq_bot_of_finset_sup` is a two-line
application (`normalClosure_le_iff_of_normal` + this identity).

**Warning recorded in `Submission/Work/SSGRoute/PING_sha2image_transport_proved_2026-10-05.md` §8:**
this identification *fails* for a bare `[IsAlgClosed Ω]` — the sup of the `Aut_k(Ω)`-images is the
*Galois* closure, not the normal closure (`k = ℚ`, `Ω = ℝ`, `E = ℚ(∛2)` is a counterexample).  The
`[Normal k Ω]` hypothesis is essential.
-/

namespace Work.SSGRoute.Sha2Lib

/-- **The normal closure is contained in any sup of the conjugates that covers them.**  If every
`k`-conjugate of `E` occurs among the `Lᵢ`, then `normalClosure k E Ω ≤ ⨆ i, Lᵢ i`. -/
theorem normalClosure_le_sup_conjugates {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    [Normal k Ω] (E : IntermediateField k Ω) {ι : Type} [Fintype ι]
    (Lᵢ : ι → IntermediateField k Ω)
    (hcover : ∀ σ : Ω ≃ₐ[k] Ω, ∃ i, Lᵢ i = E.map (AlgEquiv.toAlgHom σ)) :
    IntermediateField.normalClosure k E Ω ≤ Finset.univ.sup Lᵢ := by
  rw [IntermediateField.normalClosure_def'']
  refine iSup_le fun σ => ?_
  obtain ⟨i, hi⟩ := hcover σ
  rw [← hi]
  exact Finset.le_sup (Finset.mem_univ i)

end Work.SSGRoute.Sha2Lib
