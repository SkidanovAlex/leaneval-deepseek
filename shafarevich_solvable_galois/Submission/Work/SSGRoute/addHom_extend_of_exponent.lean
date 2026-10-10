import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Submission.Work.SSGRoute.PTDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace Work.SSGRoute

/-- **Additive extension across a subgroup, in exponent `p` (`p` prime).** Let `V` be an abelian group of exponent `p` and `W ≤ V` a subgroup, and let `φ : W →+ B` have `p`-torsion values. Then `φ` extends to an additive map `V →+ B` with `p`-torsion values. -/
theorem addHom_extend_of_exponent (p : ℕ) [Fact p.Prime] {V B : Type*} [AddCommGroup V]
    [AddCommGroup B] (hV : ∀ v : V, p • v = 0) (W : AddSubgroup V) (φ : W →+ B)
    (hφ : ∀ w : W, p • φ w = 0) :
    ∃ Φ : V →+ B, (∀ w : W, Φ (w : V) = φ w) ∧ ∀ v : V, p • Φ v = 0 := by
  -- `V` is a vector space over `F_p` since every element has order dividing `p`.
  haveI : Module (ZMod p) V := AddCommGroup.zmodModule hV
  -- Regard `W` as a subspace of `V`.
  let Wsub : Submodule (ZMod p) V :=
    { carrier := ↑W
      zero_mem' := W.zero_mem
      add_mem' := fun ha hb => W.add_mem ha hb
      smul_mem' := fun c x hx => ZMod.smul_mem hx c }
  -- A subspace of a vector space is a direct summand.
  obtain ⟨W', hcompl⟩ := Submodule.exists_isCompl Wsub
  -- The projection onto `W` along the complement is a linear, hence additive, retraction.
  have hmem : ∀ v : V, Wsub.projection W' hcompl v ∈ W :=
    fun v => Submodule.projection_apply_mem hcompl v
  have hleft : ∀ w : W, Wsub.projection W' hcompl (w : V) = (w : V) :=
    fun w => Submodule.projection_apply_of_mem_left hcompl w.2
  refine ⟨{ toFun := fun v => φ ⟨Wsub.projection W' hcompl v, hmem v⟩
            map_zero' := ?_
            map_add' := ?_ }, ?_, ?_⟩
  · have h : (⟨Wsub.projection W' hcompl 0, hmem 0⟩ : W) = 0 := by
      ext; exact map_zero (Wsub.projection W' hcompl)
    rw [h, map_zero]
  · intro a b
    have h : (⟨Wsub.projection W' hcompl (a + b), hmem (a + b)⟩ : W)
        = ⟨Wsub.projection W' hcompl a, hmem a⟩
          + ⟨Wsub.projection W' hcompl b, hmem b⟩ := by
      ext; exact map_add (Wsub.projection W' hcompl) a b
    rw [h, map_add]
  · intro w
    have h : (⟨Wsub.projection W' hcompl (w : V), hmem (w : V)⟩ : W) = w := by
      ext; exact hleft w
    show φ (⟨Wsub.projection W' hcompl (w : V), hmem (w : V)⟩ : W) = φ w
    rw [h]
  · intro v
    exact hφ ⟨Wsub.projection W' hcompl v, hmem v⟩

end Work.SSGRoute
