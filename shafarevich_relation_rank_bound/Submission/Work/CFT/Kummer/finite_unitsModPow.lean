import Mathlib
import Submission.Work.CFT.Kummer.Defs
import Submission.Work.CFT.Kummer.finrank_unitsModPow

/-!
# Finiteness of `𝒪_Kˣ/(𝒪_Kˣ)^p` as an `𝔽_p`-module

`𝒪_Kˣ ≅ μ(K) × ℤ^r` is finitely generated as an abelian group (Dirichlet's unit theorem), hence
so is every quotient of it, and a finitely generated abelian group is a finite module over any
ring acting on it.  Therefore `unitsModPow K p = 𝒪_Kˣ/(𝒪_Kˣ)^p` is a finite `ZMod p`-module, for
**every** `p : ℕ`: no hypothesis is needed on `p`.  (In particular `p = 0` is covered — then
`ZMod 0 = ℤ` and `(𝒪_Kˣ)^0 = 1`, so the quotient is all of `𝒪_Kˣ`, infinite as a set but finite
as a `ℤ`-module.)

## Main result

* `Work.CFT.Kummer.finite_unitsModPow`.
-/

open NumberField

noncomputable section

set_option linter.style.haveILetI false

namespace Work.CFT.Kummer

/-- The unit group `𝒪_Kˣ` of a number field is finitely generated: by Dirichlet's unit theorem
`𝒪_Kˣ ≅ μ(K) × ℤ ^ rank K`, a product of the finite torsion subgroup and a free abelian group of
finite rank (`unitsMulEquiv`). -/
instance instGroupFGUnits (K : Type*) [Field K] [NumberField K] : Group.FG (𝓞 K)ˣ := by
  haveI : Group.FG (NumberField.Units.torsion K ×
      (Fin (NumberField.Units.rank K) → Multiplicative ℤ)) := inferInstance
  exact Group.fg_of_surjective (f := (unitsMulEquiv K).toMonoidHom)
    (unitsMulEquiv K).surjective

/-- If `G` is a finitely generated commutative group, then `Additive G` is a finite module over
every ring acting on it: a set of group generators of `G` spans `Additive G` as a module, since
a submodule is in particular an additive subgroup. -/
theorem module_finite_of_group_fg {R : Type*} [Ring R] {G : Type*} [CommGroup G]
    [Module R (Additive G)] [Group.FG G] : Module.Finite R (Additive G) := by
  obtain ⟨s, hs⟩ := (inferInstance : Group.FG G).out
  refine ⟨⟨s.map ⟨Additive.ofMul, Additive.ofMul.injective⟩, ?_⟩⟩
  rw [eq_top_iff]
  rintro x -
  obtain ⟨q, rfl⟩ : ∃ q : G, Additive.ofMul q = x := ⟨x.toMul, rfl⟩
  have hq : q ∈ Subgroup.closure (s : Set G) := hs ▸ Subgroup.mem_top q
  induction hq using Subgroup.closure_induction with
  | mem y hy =>
      exact Submodule.subset_span
        (Finset.mem_coe.mpr (Finset.mem_map.mpr ⟨y, Finset.mem_coe.mp hy, rfl⟩))
  | one => exact Submodule.zero_mem _
  | mul y z _ _ ihy ihz => exact Submodule.add_mem _ ihy ihz
  | inv y _ ihy =>
      rw [show Additive.ofMul y⁻¹ = -Additive.ofMul y from rfl]
      exact Submodule.neg_mem _ ihy
/-- `𝒪_Kˣ/(𝒪_Kˣ)^p` is finite: by Dirichlet's unit theorem `𝒪_Kˣ` is finitely generated, hence
so is its quotient by the `p`-th powers, which is killed by `p`. -/
theorem finite_unitsModPow (K : Type*) [Field K] [NumberField K] (p : ℕ) :
    Module.Finite (ZMod p) (Work.CFT.Kummer.unitsModPow K p) :=
  module_finite_of_group_fg (R := ZMod p)
    (G := (𝓞 K)ˣ ⧸ pthPowerSubgroup (𝓞 K)ˣ p)

end Work.CFT.Kummer
