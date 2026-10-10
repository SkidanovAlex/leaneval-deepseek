import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.HSRow.TransgressionDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.HSRow

open Classical

noncomputable section

open scoped Pointwise

/-- The coboundary of the *constant* `1`-cochain with value `m` is a locally constant `2`-cocycle:
`(g,h) ↦ ρ(g) • m = d¹ b g h` with `b ≡ m`.  It is a `2`-cocycle because `ρ` is a monoid
homomorphism, and it is locally constant with witness `U = ker (res k K)`, open since
`Gal(K/k)` is finite. -/
lemma const_coboundary_mem_lcCocycles2
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (D : Subgroup (Ω ≃ₐ[k] Ω)) (m : M) :
    (fun g _ => SSGRoute.res k K g • m) ∈ Work.SSGRoute.lcCocycles2 p k Ω K M D := by
  refine ⟨?_, ?_⟩
  · intro g _ h _ l _
    change SSGRoute.res k K g • (SSGRoute.res k K h • m) - SSGRoute.res k K (g * h) • m
      + SSGRoute.res k K g • m - SSGRoute.res k K g • m = 0
    rw [map_mul, mul_smul]
    abel
  · refine ⟨(SSGRoute.res k K).ker, ?_, ?_⟩
    · rw [show SSGRoute.res k K = AlgEquiv.restrictNormalHom K from rfl]
      rw [IntermediateField.restrictNormalHom_ker]
      exact IntermediateField.fixingSubgroup_isOpen K
    · intro g _ h _ u hu _ _ _ _
      have hu1 : SSGRoute.res k K u = 1 := MonoidHom.mem_ker.mp hu
      change SSGRoute.res k K (g * u) • m = SSGRoute.res k K g • m
      rw [map_mul, hu1, mul_one]

/-- The normalisation `normC c = c - d¹ (const (c 1 1))` of a locally constant `2`-cocycle on `D`
is again a locally constant `2`-cocycle on `D` (subtracting the coboundary of the constant
`(g,h) ↦ ρ(g) • c 1 1`; for local constancy use the witness `U = ker (res k K)`, open since
`Gal(K/k)` is finite, together with the consequence `c g 1 = ρ(g) • c 1 1` of the cocycle identity
at `(g,1,1)`). -/
theorem normC_mem_lcCocycles2
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (D : Subgroup (Ω ≃ₐ[k] Ω))
    (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M) (hc : c ∈ Work.SSGRoute.lcCocycles2 p k Ω K M D) :
    normC p k Ω K M c ∈ Work.SSGRoute.lcCocycles2 p k Ω K M D := by
  have hd : (fun g _ => SSGRoute.res k K g • c 1 1) ∈
      Work.SSGRoute.lcCocycles2 p k Ω K M D :=
    const_coboundary_mem_lcCocycles2 p k Ω K M D (c 1 1)
  have hsub : c - (fun g _ => SSGRoute.res k K g • c 1 1) ∈
      Work.SSGRoute.lcCocycles2 p k Ω K M D := Submodule.sub_mem _ hc hd
  have heq : normC p k Ω K M c = c - (fun g _ => SSGRoute.res k K g • c 1 1) := by
    funext g h
    simp only [Pi.sub_apply, normC_apply]
  rw [heq]
  exact hsub

end

end Work.SSGRoute.HSRow
