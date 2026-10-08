import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Over `𝔽₂`, the transvections generate the full linear group

The main theorem of this file is

`Work.Hering.Wagner.closure_transvections_eq_top`:
for a finite dimensional `ZMod 2`-vector space `V` of dimension at least two,
the transvections generate `V ≃ₗ[ZMod 2] V`.

The mathematical content is Dieudonné's theorem on the generation of the
special/general linear group by (dilatransvections), as formalised in
`Mathlib/LinearAlgebra/Transvection/Generation.lean`, together with the two
facts special to the field with two elements:

* every dilatransvection over `ZMod 2` is a transvection
  (`dilatransvections_subset_transvections_zmod2`), because the only non-zero
  value of `f v` makes the map `x ↦ x + f x • v` singular;
* no linear equivalence is exceptional over `ZMod 2`
  (`not_isExceptional_zmod2`), because the only homotheties of a non-trivial
  space are `0` and `1`, and neither is a bijective `fixedReduce` of a
  non-trivial quotient.
-/

namespace Work.Hering.Wagner

open LinearEquiv

open scoped Pointwise

/-! ### Elementary facts about `ZMod 2` -/

lemma zmod2_eq_zero_or_eq_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma zmod2_eq_one_of_ne_zero {a : ZMod 2} (h : a ≠ 0) : a = 1 := by
  rcases zmod2_eq_zero_or_eq_one a with h0 | h1
  · exact absurd h0 h
  · exact h1

/-! ### Dilatransvections over `𝔽₂` are transvections -/

/-- Over the field with two elements, a dilatransvection which happens to be
invertible is a transvection: the scalar `f v` cannot be `1`, since then
`x ↦ x + f x • v` would kill the non-zero vector `v`. -/
theorem dilatransvections_subset_transvections_zmod2 {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] :
    LinearEquiv.dilatransvections (ZMod 2) V ⊆ LinearEquiv.transvections (ZMod 2) V := by
  rintro e ⟨f, v, he⟩
  have he' : ∀ x : V, (e : V → V) x = LinearMap.transvection f v x :=
    fun x => congrArg (fun g => g x) he
  have hfv : f v = 0 := by
    by_contra h
    have h1 : f v = 1 := zmod2_eq_one_of_ne_zero h
    have hv : v ≠ 0 := fun hv => by rw [hv, map_zero] at h1; exact one_ne_zero h1.symm
    have hz : (e : V → V) v = (e : V → V) 0 := by
      rw [he' v, he' 0, LinearMap.transvection.apply, LinearMap.transvection.apply, h1,
        one_smul]
      simp only [map_zero, zero_smul, add_zero]
      rw [← two_smul (ZMod 2) v, show (2 : ZMod 2) = 0 from by decide, zero_smul]
    exact hv (e.injective hz)
  have heq : e = LinearEquiv.transvection hfv := by
    ext x
    rw [he' x]
    rfl
  rw [heq]
  exact LinearEquiv.mem_transvections hfv

/-! ### The exceptional case of Dieudonné's theorem is empty over `𝔽₂` -/

/-- Over the field with two elements no linear equivalence is exceptional:
the induced map on `V ⧸ e.fixedSubmodule` would be a homothety with scalar `a`,
and for `a = 1` it is the identity (contradicting `fixedReduce ≠ 1`) while for
`a = 0` it is the zero map, which is injective only on the trivial quotient,
contradicting `1 < finrank`. -/
theorem not_isExceptional_zmod2 {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Module.Finite (ZMod 2) V] (e : V ≃ₗ[ZMod 2] V) : ¬ LinearEquiv.IsExceptional e := by
  rintro ⟨hlt, hne, a, ha⟩
  rcases zmod2_eq_zero_or_eq_one a with h0 | h1
  · have hsub : Subsingleton (V ⧸ e.fixedSubmodule) :=
      ⟨fun x y => e.fixedReduce.injective (by
        have hx : e.fixedReduce x = 0 := by rw [ha x, h0, zero_smul]
        have hy : e.fixedReduce y = 0 := by rw [ha y, h0, zero_smul]
        rw [hx, hy])⟩
    have hz : Module.finrank (ZMod 2) (V ⧸ e.fixedSubmodule) = 0 :=
      (Module.finrank_eq_zero_iff_of_free (ZMod 2) _).mpr hsub
    omega
  · have hone : e.fixedReduce = 1 := by
      ext x
      rw [ha x, h1, one_smul]
      rfl
    exact hne hone

/-! ### The main theorem -/

set_option linter.unusedVariables false in
theorem closure_transvections_eq_top {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Module.Finite (ZMod 2) V] (h : 2 ≤ Module.finrank (ZMod 2) V) :
    Subgroup.closure (LinearEquiv.transvections (ZMod 2) V) = ⊤ := by
  -- Powers of the set of transvections lie in the subgroup they generate.
  have hpow : ∀ n : ℕ,
      (LinearEquiv.transvections (ZMod 2) V) ^ n ⊆
        (Subgroup.closure (LinearEquiv.transvections (ZMod 2) V) : Set (V ≃ₗ[ZMod 2] V)) := by
    intro n
    induction n with
    | zero =>
      intro x hx
      have hx1 : x = 1 := by simpa using hx
      rw [hx1]
      exact Subgroup.one_mem _
    | succ n ih =>
      intro x hx
      rw [pow_succ, Set.mem_mul] at hx
      obtain ⟨a, ha, b, hb, rfl⟩ := hx
      exact Subgroup.mul_mem _ (ih ha) (Subgroup.subset_closure hb)
  refine eq_top_iff.mpr fun e _ => ?_
  -- Dieudonné's theorem writes `e` as a product of transvections and one dilatransvection.
  have he := LinearEquiv.mem_transvections_pow_mul_dilatransvections_of_not_isExceptional
    (not_isExceptional_zmod2 e)
  rw [Set.mem_mul] at he
  obtain ⟨a, ha, b, hb, hab⟩ := he
  rw [← hab]
  exact Subgroup.mul_mem _ (hpow _ ha)
    (Subgroup.subset_closure (dilatransvections_subset_transvections_zmod2 hb))

end Work.Hering.Wagner
