import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.ZMod
import Mathlib.RingTheory.Finiteness.Cardinality
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A finitely generated `ℤ`-module killed by a prime `p` is finite

If `M` is a finitely generated `ℤ`-module and every element is annihilated by a prime `p`
(i.e. `p • x = 0` for all `x`), then `M` carries a `ZMod p`-module structure (namely the
canonical one on a group of exponent dividing `p`) and a finite `ℤ`-spanning set is then
also a `ZMod p`-spanning set. Since `ZMod p` is a finite ring, a finitely generated
`ZMod p`-module is finite, and hence so is `M`.

This is the elementary finiteness input used when reducing statements about groups of
exponent `p` (or `p`-torsion modules) to statements about finite `ZMod p`-modules.
-/

namespace Work.SSGRoute.ExtChain

theorem finite_ptorsion_module {p : ℕ} [Fact p.Prime] (M : Type) [AddCommGroup M] [Module ℤ M]
    (hfin : Module.Finite ℤ M) (hM : ∀ x : M, p • x = 0) : Finite M := by
  -- `ℤ`-module structures on an abelian group are unique; we record this for the ambient one
  -- so that we may switch between the ambient `ℤ`-action and the canonical `zsmul`.
  rename_i hp hAdd hMod
  have hMod_eq : hMod = AddCommGroup.toIntModule M := Subsingleton.elim _ _
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  -- `M` is a module over `ZMod p = ℤ / pℤ` (the `{ ... with }` keeps the structure transparent
  -- for the type class engine).
  letI : Module (ZMod p) M := { AddCommMonoid.zmodModule hM with }
  -- extract a finite `ℤ`-spanning set of `M`
  obtain ⟨s, hsfin, hs⟩ : ∃ s : Set M, s.Finite ∧ Submodule.span ℤ s = ⊤ := by
    rw [Module.finite_def, Submodule.fg_def] at hfin
    exact hfin
  -- the same set spans `M` over `ZMod p`: a `ℤ`-linear combination of elements of `s` can be
  -- evaluated using only the additive group structure, and `ZMod p`-submodules are additive
  -- subgroups.
  have hspan : Submodule.span (ZMod p) s = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ Submodule.span ℤ s := by rw [hs]; trivial
    refine Submodule.span_induction (p := fun y _ => y ∈ Submodule.span (ZMod p) s)
      ?_ ?_ ?_ ?_ hx
    · intro y hy; exact Submodule.subset_span hy
    · exact Submodule.zero_mem _
    · intro y z _ _ ihy ihz; exact Submodule.add_mem _ ihy ihz
    · intro c y _ ih
      -- the `ℤ`-scalar action is the canonical `zsmul`, which is available in every additive
      -- subgroup
      rw [hMod_eq]
      exact zsmul_mem ih c
  haveI : Module.Finite (ZMod p) M := by
    rw [Module.finite_def, Submodule.fg_def]
    exact ⟨s, hsfin, hspan⟩
  exact Module.finite_of_finite (ZMod p)

end Work.SSGRoute.ExtChain
