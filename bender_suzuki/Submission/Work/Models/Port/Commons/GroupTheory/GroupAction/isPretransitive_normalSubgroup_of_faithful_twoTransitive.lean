import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

namespace Commons.GroupTheory.GroupAction

open MulAction

/-- A faithful 2-pretransitive action is "quasipreprimitive" in the sense of Wielandt
(theorem 7.1): any nontrivial normal subgroup is pretransitive.

Given a faithful 2-pretransitive action of `G` on `Ω`, a normal subgroup `N ≠ ⊥`
acts pretransitively on `Ω`.

Proof sketch: 2-pretransitivity gives a primitive action (`IsPreprimitive`),
hence a *quasiprimitive* one: every normal subgroup without fixed points is
pretransitive (`IsPreprimitive.isQuasiPreprimitive`).  Since the action is
faithful and `N ≠ ⊥`, the subgroup `N` cannot fix every point; otherwise
faithfulness would force `N = ⊥`.  The conclusion is the pretransitivity
of the induced action of `N`. -/
theorem isPretransitive_normalSubgroup_of_faithful_twoTransitive {G Ω : Type*}
    [Group G] [MulAction G Ω] [FaithfulSMul G Ω]
    [h2 : MulAction.IsMultiplyPretransitive G Ω 2] (N : Subgroup G) (hN : N.Normal)
    (hNbot : N ≠ ⊥) : ∀ x y : Ω, ∃ n : N, (n : G) • x = y := by
  -- N does not fix every point: otherwise faithfulness would force N = ⊥.
  have hfp : MulAction.fixedPoints N Ω ≠ Set.univ := by
    intro hfix
    apply hNbot
    rw [Subgroup.eq_bot_iff_forall]
    intro n hn
    have hfixall : ∀ a : Ω, (n : G) • a = a := by
      intro a
      have ha : a ∈ MulAction.fixedPoints N Ω := by simp [hfix]
      have hmem : ∀ m : N, m • a = a :=
        (MulAction.mem_fixedPoints (M := N) (α := Ω)).mp ha
      simpa [Subgroup.smul_def] using hmem ⟨n, hn⟩
    exact (faithfulSMul_iff (G := G) (α := Ω)).mp ‹FaithfulSMul G Ω› n hfixall
  -- 2-pretransitivity implies preprimitivity
  have hpp : MulAction.IsPreprimitive G Ω :=
    MulAction.isPreprimitive_of_is_two_pretransitive h2
  -- hence quasipreprimitivity: normal subgroups without fixed points are pretransitive
  letI hppI : MulAction.IsPreprimitive G Ω := hpp
  have hq : MulAction.IsQuasiPreprimitive G Ω := inferInstance
  letI : N.Normal := hN
  have hNtr : MulAction.IsPretransitive N Ω := hq.isPretransitive_of_normal hfp
  intro x y
  obtain ⟨n, hn⟩ := hNtr.exists_smul_eq x y
  exact ⟨n, by simpa [Subgroup.smul_def] using hn⟩

end Commons.GroupTheory.GroupAction