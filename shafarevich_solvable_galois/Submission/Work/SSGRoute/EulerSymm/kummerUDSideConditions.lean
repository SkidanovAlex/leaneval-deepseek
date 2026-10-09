import Mathlib
import Submission.Work.SSGRoute.EulerSymm.localArith.LocalStructureDefs
import Submission.Work.SSGRoute.ZConstruction.localKummerLift
import Submission.Work.SSGRoute.coker_assembly
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The side conditions of the target `EulerSymm.kummerGroupUDStructure`

The target `SSGRoute.EulerSymm.kummerGroupUDStructure` (obligation (C)) carries the binders

```
(p) [Fact p.Prime] (k) [Field k] [NumberField k] (Ω) [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
(K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
(A) (hA : SSGRoute.IsFinPlace k A) (Γ) (hΓ : Nat.Coprime (Nat.card ↥Γ) p) ... (T) (hT) ...
```

while the two *providers* of its (C-local) input — `EulerSymm.IsLocalKummerStructure` in
`localArith/isLocalKummerStructure_residueChar.lean` and its `¬`-case companion — and the
transport/gluing assembly `EulerSymm.isKummerStructure_from_local_and_transport` ask for the
*derived* data

* `[NumberField ↥K]`, `[IsSepClosure ↥K Ω]` (the level field is a number field, `Ω` is a separable
  closure of it),
* `hAK : SSGRoute.IsFinPlace ↥K A` (the place of `Ω` restricts to a finite place of `↥K`),
* `[Fintype ↥(Dsub k Ω K A Γ)]` (the restriction group is finite),
* `[Finite T]`, `[Finite (DualMod p T)]` (from the cyclotomic-dual datum `hT`),
* `[Finite (localKummer p k Ω K A hAK)]` (the local Kummer group `κˣ⧸(κˣ)ᵖ` of the level completion
  is finite — Milne *ADT* I.2.11's local finiteness).

This file collects those derivations, so that the final wiring of `kummerGroupUDStructure` is
independent of them.

## Reference

* `SSGRoute/ZConstruction/localKummerLift`: `isFinPlace_of_isFinPlace_below`;
* `Mathlib.NumberTheory.NumberField.Basic`: `NumberField.of_module_finite`;
* `Mathlib.FieldTheory.IsSepClosed`: `IsSepClosure.of_isAlgClosure_of_perfectField`;
* `EulerSymm/hsSetup.lean`: the `Fintype ↥(Dsub …)` instance;
* `SSGRoute/coker_assembly.lean`: `finite_of_finrank_eq_one`.
-/

open scoped TensorProduct Pointwise
open Classical

namespace Work.SSGRoute.EulerSymm

noncomputable section

/-! ## The level field is a number field, and `Ω` is a separable closure of it -/

/-- The level field `↥K` is a number field (it is a finite extension of `k`). -/
theorem numberField_intermediateField (k : Type) [Field k] [NumberField k]
    (Ω : Type) [Field Ω] [Algebra k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] :
    NumberField ↥K :=
  NumberField.of_module_finite k ↥K

/-- `Ω` is a separable closure of the level field `↥K`. -/
theorem isSepClosure_intermediateField (k : Type) [Field k] [NumberField k]
    (Ω : Type) [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] : IsSepClosure ↥K Ω := by
  haveI hΩ : IsAlgClosed Ω := IsAlgClosure.isAlgClosed (R := k) (K := Ω)
  haveI hAc : IsAlgClosure ↥K Ω := ⟨hΩ, inferInstance⟩
  exact IsSepClosure.of_isAlgClosure_of_perfectField ↥K Ω

/-- A finite place of `k` is a finite place of any intermediate field `k ≤ K ≤ Ω`.  (`IsFinPlace`
is `A.comap (algebraMap · Ω) ≠ ⊤`, and the valuation is already non-trivial on `k ≤ K`; the proof
is the one of `ZConstruction.isFinPlace_of_isFinPlace_below`, repeated here so as not to drag in
that file's `[IsAlgClosed Ω]`/`[Fact p.Prime]` section variables.) -/
theorem isFinPlace_intermediateField (k : Type) [Field k] [NumberField k] (Ω : Type) [Field Ω]
    [Algebra k Ω] (K : IntermediateField k Ω) (A : ValuationSubring Ω)
    (hA : SSGRoute.IsFinPlace k A) :
    SSGRoute.IsFinPlace ↥K A := by
  intro h
  apply hA
  have hval : ∀ x : ↥K, algebraMap ↥K Ω x ∈ A := by
    intro x
    have hx : x ∈ A.comap (algebraMap ↥K Ω) := by rw [h]; exact ValuationSubring.mem_top x
    rwa [ValuationSubring.mem_comap] at hx
  refine le_antisymm (ValuationSubring.le_top (A.comap (algebraMap k Ω))) ?_
  intro x _
  rw [ValuationSubring.mem_comap]
  simpa only [IsScalarTower.algebraMap_apply k ↥K Ω] using hval (algebraMap k ↥K x)

/-! ## Finiteness of the cyclotomic dual and of its `𝔽_p`-dual -/

/-- A cyclotomic dual `T` (`IsCyclotomicDual`) is finite: it is one-dimensional over `𝔽_p`. -/
theorem finite_of_isCyclotomicDual (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [NumberField k]
    (Ω : Type) [Field Ω] [Algebra k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K]
    (ζ : Ω) (T : Type) [AddCommGroup T] [Module (ZMod p) T]
    [DistribMulAction (K ≃ₐ[k] K) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ) : Finite T :=
  Work.SSGRoute.finite_of_finrank_eq_one p T hT.1

/-- The `𝔽_p`-dual `DualMod p T` of a finite module is finite. -/
theorem finite_dualMod (p : ℕ) [Fact p.Prime] (T : Type) [AddCommGroup T] [Module (ZMod p) T] [Finite T] :
    Finite (Work.SSGRoute.DualMod p T) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  exact Finite.of_injective (fun f : Work.SSGRoute.DualMod p T => (f : T → ZMod p))
    DFunLike.coe_injective

end

end Work.SSGRoute.EulerSymm
