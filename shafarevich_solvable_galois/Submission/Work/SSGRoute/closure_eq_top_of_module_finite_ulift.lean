import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A finitely generated `ULift ℤ`-module has finitely many additive generators

For an additive commutative group `V` carrying a `Module (ULift.{u} ℤ)` structure, the
`ULift.{u} ℤ`-scalar action is *forced*: `ULift.{u} ℤ` is canonically isomorphic to `ℤ`
(`ULift.ringEquiv`), so a module structure over it is the same thing as the canonical
`ℤ`-module structure of the abelian group, and in fact
`(ULift.up k) • x = k • x` for `k : ℤ`, `x : V` (`ulift_up_smul_eq_zsmul`), which is
`Int.cast_smul_eq_zsmul` together with the fact that the cast `ℤ → ULift.{u} ℤ` is `ULift.up`.
Consequently the `ULift.{u} ℤ`-span of a set is contained in its additive closure
(`mem_addSubgroup_closure_of_mem_span`), and a finite spanning set over `ULift.{u} ℤ` is a finite
set of additive generators.

## Note on universe parameters and instances

The statement uses the anonymous universe binder `{u : Universe}` of the requester (`Universe` is
not a Lean 4 identifier, so with `autoImplicit` enabled the binder is auto-bound: `u` is a dummy
term variable and the universe level of `ULift.{u} ℤ` is the auto-bound *level* of the same name).
The library is built with `autoImplicit = false`, so we enable it locally, exactly as the sibling
files of this workspace do (e.g. `Submission/Work/Properness/conjLift_mulFun.lean`).

The global `ULift.*` scalar instances (and `ZSMul.toSMul`) are pushed down in priority, so that the
*ambient* `Module (ULift.{u} ℤ) V` instance given in the statement is the one used for the
`•`-notation below (the same device as in `Submission/Work/SSGRoute/module_free_ulift_int.lean`).
Without it, `(ULift.up k) • x` would be elaborated with Mathlib's global `ULift` scalar instances,
which is not the structure the module finiteness hypothesis refers to.
-/

set_option autoImplicit true
set_option linter.unusedVariables false

attribute [local instance 1] ULift.smulLeft ULift.smulZeroClass ULift.mulAction ULift.distribSMul
  ULift.distribMulAction ULift.smulWithZero ULift.mulActionWithZero ULift.module ZSMul.toSMul

namespace Work.SSGRoute

/-- The scalar action of `ULift.up k` for the `ULift.{u} ℤ`-module structure on an additive
commutative group is the canonical integer action. -/
lemma ulift_up_smul_eq_zsmul {V : Type*} [AddCommGroup V]
    [Module (ULift.{u} ℤ) V] (k : ℤ) (x : V) : (ULift.up k) • x = k • x :=
  Int.cast_smul_eq_zsmul (ULift.{u} ℤ) k x

/-- Every element of the `ULift.{u} ℤ`-span of `s` lies in the additive closure of `s`: a
`ULift.{u} ℤ`-linear combination is an integral linear combination. -/
lemma mem_addSubgroup_closure_of_mem_span {V : Type*} [AddCommGroup V]
    [Module (ULift.{u} ℤ) V] (s : Set V) {x : V}
    (hx : x ∈ Submodule.span (ULift.{u} ℤ) s) : x ∈ AddSubgroup.closure s :=
  Submodule.span_induction (p := fun y _ => y ∈ AddSubgroup.closure s)
    (fun y hy => AddSubgroup.subset_closure hy)
    (AddSubgroup.zero_mem _)
    (fun y z _ _ hy hz => AddSubgroup.add_mem _ hy hz)
    (fun a y _ hy => by
      cases a with
      | up k =>
        rw [ulift_up_smul_eq_zsmul]
        exact AddSubgroup.zsmul_mem _ hy k)
    hx

/-- A finitely generated `ULift ℤ`-module (any universe) on an additive commutative group has a
finite set of *additive* generators. -/
theorem closure_eq_top_of_module_finite_ulift {u : Universe} {V : Type*} [AddCommGroup V]
    [Module (ULift.{u} ℤ) V] [Module.Finite (ULift.{u} ℤ) V] :
    ∃ s : Finset V, AddSubgroup.closure (s : Set V) = ⊤ := by
  obtain ⟨S, hSfin, hSspan⟩ :=
    Submodule.fg_def.mp (Module.Finite.fg_top (R := ULift.{u} ℤ) (M := V))
  refine ⟨hSfin.toFinset, ?_⟩
  rw [Set.Finite.coe_toFinset]
  refine le_antisymm le_top ?_
  intro x _
  exact mem_addSubgroup_closure_of_mem_span S (by rw [hSspan]; exact Submodule.mem_top)

end Work.SSGRoute
