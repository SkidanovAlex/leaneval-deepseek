import Mathlib
import Submission.Work.SSGRoute.H9.swKummerCochar_kills_levelKernel
import Submission.Work.SSGRoute.H9.swChainConjDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The level kernel of a Kummer level *over `K`*

`Work.SSGRoute.H9.swKummerCochar_kills_levelKernel` kills the kernel of `res k L` for a level `L`
over `k` containing a `p`-th root of `b`.  In the §4(b) chain the level is the Kummer level *over
`K`*, `L = K((b_i b_N)^{1/p})` (see
`Submission/Work/SSGRoute/NodeS34/swKLevel_localValue_eq_zero.lean` for why the level must be over
`K`): the hypothesis of the promotion is the vanishing on

  `ker (Gal(Ω/↥K) → Gal(L/↥K))  ∩  decomp k A ⊓ G_K`,

i.e. on the elements `u ∈ K.fixingSubgroup` whose image under
`AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) ↥L ∘ IntermediateField.fixingSubgroupEquiv K` is `1`.

This file supplies that vanishing, in the two forms the promotion consumes:

* `swKLevel_kills_levelKernel` — a single Kummer class `χ_b`;
* `swKLevel_sum_kills_levelKernel` — the sum `χ_{b_i} + χ_{b_N}`, i.e. the `hker` input of
  `NodeS34.swKLevel_localValue_eq_zero` at `L = K((b_i b_N)^{1/p})`.

The proofs are the one-liner of `swKummerCochar_kills_levelKernel`
(`AlgEquiv.restrictNormal_eq_one_iff` + `kummerIdx_eq_zero_of_apply_eq`), plus
`nodeKummerCocharZMod_mul` for the sum.
-/

namespace Work.SSGRoute.NodeS34

open _root_.SSGRoute

set_option autoImplicit false
set_option linter.unusedSectionVars false

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] [IsAlgClosed Ω] {K : IntermediateField k Ω} [FiniteDimensional k K]
  [IsGalois k K]

/-- **The kernel of the restriction to a level over `K` is killed by the Kummer cochain.**  If
`L ⊇ K(b^{1/p})` (witnessed by the chosen `p`-th root) and `u ∈ K.fixingSubgroup` acts trivially
on `L`, then `χ_b u = 0`. -/
theorem swKLevel_kills_levelKernel
    (L : IntermediateField ↥K Ω) [FiniteDimensional ↥K L] [IsGalois ↥K L]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) (b : (↥K)ˣ)
    (hroot : (Work.SSGRoute.kummerSqrtUnitZMod (Ω := Ω) p b : Ω) ∈ L)
    (u : Ω ≃ₐ[k] Ω) (huK : u ∈ K.fixingSubgroup)
    (huL : AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) ↥L
      ((IntermediateField.fixingSubgroupEquiv K) ⟨u, huK⟩) = 1) :
    Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b u = 0 := by
  haveI : Normal ↥K ↥L := (inferInstance : IsGalois ↥K ↥L).to_normal
  rw [Work.SSGRoute.ZSplit.nodeKummerCocharZMod_apply (K := K) (ζ := ζ) (hζK := hζK)
    (hζ := hζ) (β := b) huK, Work.SSGRoute.kummerCharZMod_apply]
  set u₀ : Ω ≃ₐ[↥K] Ω := (IntermediateField.fixingSubgroupEquiv K) ⟨u, huK⟩ with hu₀
  have hfiltr : u₀.restrictNormal ↥L = 1 := huL
  have hfixL : ∀ x ∈ L, u₀ x = x := (AlgEquiv.restrictNormal_eq_one_iff L u₀).mp hfiltr
  refine Work.SSGRoute.kummerIdx_eq_zero_of_apply_eq p
    (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) b
    (Work.SSGRoute.kummerSqrtUnitZMod (Ω := Ω) p b)
    (Work.SSGRoute.kummerSqrtUnitZMod_pow (Ω := Ω) p b) u₀ ?_
  exact hfixL _ hroot

/-- **The kernel of the restriction to `K((b_i b_N)^{1/p})` is killed by `χ_{b_i} + χ_{b_N}`** —
the `hker` input of `NodeS34.swKLevel_localValue_eq_zero` at the level `L ⊇ K((b_i b_N)^{1/p})`. -/
theorem swKLevel_sum_kills_levelKernel
    (L : IntermediateField ↥K Ω) [FiniteDimensional ↥K L] [IsGalois ↥K L]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) (bi bN : (↥K)ˣ)
    (hroot : (Work.SSGRoute.kummerSqrtUnitZMod (Ω := Ω) p (bi * bN) : Ω) ∈ L)
    (u : Ω ≃ₐ[k] Ω) (huK : u ∈ K.fixingSubgroup)
    (huL : AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) ↥L
      ((IntermediateField.fixingSubgroupEquiv K) ⟨u, huK⟩) = 1) :
    Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bi u
      + Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bN u = 0 := by
  have h := swKLevel_kills_levelKernel (K := K) L ζ hζ hζK (bi * bN) hroot u huK huL
  rwa [Work.SSGRoute.nodeKummerCocharZMod_mul K ζ hζ hζK bi bN] at h

end Work.SSGRoute.NodeS34
