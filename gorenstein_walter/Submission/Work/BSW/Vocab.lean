/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area BSW, `Work.BSW`)

# Area BSW: the counting vocabulary of Bender 1974

Bender's proof (`REFS/bender1974_bsw.txt`) works throughout with the function

* `i(x)` — "the number of ordered pairs `(u, v)` of involutions `u, v` satisfying `x = uv`",
  equivalently the number of involutions `u` with `u⁻¹ x u = x⁻¹` (they differ by the solution
  `u = x`, `v = 1` when `x` is itself an involution, which is why `Work.BSW.iFn` — Bender's own
  count of *involutions* — and `Work.BSW.invPairCount` — the pair count — are both provided),

and its special values `i(1) = |G : C_G(t)|` (the number of involutions).  The character formula
for `i` (Gorenstein 9.4.21, Bender §2) is stated as a separate contract in
`Submission/Work/BSW/Char/`.

This file also provides the conjugation action of `s` on `K` (`Work.BSW.conjHomK`), used to say
that a linear character of `K` is "not fixed by `s`".
-/
import Submission.Work.BSW.Basic

open scoped MatrixGroups

namespace Work.BSW

open Subgroup Work.GW2

/-- `x * x = 1` for an element of order `2`. -/
theorem mul_self_eq_one_of_orderOf_eq_two {G : Type} [Group G] {x : G} (h : orderOf x = 2) :
    x * x = 1 := by
  have h2 := pow_orderOf_eq_one x
  rw [h] at h2
  simpa [pow_two] using h2

section Counting

variable (G : Type) [Group G]

/-- The number of involutions of `G`. -/
noncomputable def invCount : ℕ := {u : G | orderOf u = 2}.ncard

/-- Bender's `i(x)`: the number of involutions `u` inverting `x`
(`u⁻¹ * x * u = x⁻¹`).  For `x` that is not an involution this is the number of ordered pairs
`(u, v)` of involutions with `u * v = x`; see `Work.BSW.invPairCount`. -/
noncomputable def iFn (x : G) : ℕ := {u : G | orderOf u = 2 ∧ u⁻¹ * x * u = x⁻¹}.ncard

/-- The number of ordered pairs of involutions with product `x`. -/
noncomputable def invPairCount (x : G) : ℕ :=
  {p : G × G | orderOf p.1 = 2 ∧ orderOf p.2 = 2 ∧ p.1 * p.2 = x}.ncard

@[simp] theorem iFn_one : iFn G 1 = invCount G := by
  rw [iFn, invCount]
  exact congrArg Set.ncard (Set.ext fun u => by simp)

/-- `i(1) = #{involutions}` in the pair-count formulation: the pairs `(u, v)` of involutions with
`u * v = 1` are exactly the pairs `(u, u)`. -/
theorem invPairCount_one : invPairCount G 1 = invCount G := by
  have key : ∀ u v : G, orderOf u = 2 → orderOf v = 2 → u * v = 1 → v = u := by
    intro u v hu hv huv
    have hvv : v * v = 1 := mul_self_eq_one_of_orderOf_eq_two hv
    have hvu : v⁻¹ = v := inv_eq_of_mul_eq_one_left hvv
    have huv' : u = v⁻¹ := mul_eq_one_iff_eq_inv.mp huv
    rw [huv', hvu]
  rw [invPairCount, invCount]
  refine Set.ncard_congr (fun p _ => p.1) ?_ ?_ ?_
  · rintro ⟨u, v⟩ ⟨hu, hv, huv⟩
    exact hu
  · rintro ⟨u₁, v₁⟩ ⟨u₂, v₂⟩ ⟨hu₁, hv₁, h₁⟩ ⟨hu₂, hv₂, h₂⟩ heq
    simp only [Prod.fst, Prod.snd] at *
    have k₁ : v₁ = u₁ := key u₁ v₁ hu₁ hv₁ h₁
    have k₂ : v₂ = u₂ := key u₂ v₂ hu₂ hv₂ h₂
    rw [k₁, k₂, heq]
  · intro u hu
    rw [Set.mem_setOf_eq] at hu
    exact ⟨(u, u), ⟨hu, hu, mul_self_eq_one_of_orderOf_eq_two hu⟩, rfl⟩

end Counting

section ConjAction

variable {G : Type} [Group G] [Finite G] {t s : G} {K : Subgroup G}

/-- Conjugation by `s` as an endomorphism of `K`, in the BSW setting: it is well defined because
`s` inverts `K` (`Work.BSW.inverts_s_K`). -/
def conjHomK (h : BSWHyps2 G t s K) : ↥K →* ↥K where
  toFun x := ⟨s * (x : G) * s⁻¹, by
    rw [inverts_s_K h (x : G) x.2]
    exact K.inv_mem x.2⟩
  map_one' := by
    ext
    simp
  map_mul' := by
    intro a b
    ext
    simp [mul_assoc]

@[simp] theorem conjHomK_apply (h : BSWHyps2 G t s K) (x : ↥K) :
    (conjHomK h x : G) = s * (x : G) * s⁻¹ := rfl

/-- `s` fixes the element `t` of `K` (it inverts it, and `t` is an involution). -/
@[simp] theorem conjHomK_t (h : BSWHyps2 G t s K) :
    conjHomK h ⟨t, t_mem_K h⟩ = ⟨t, t_mem_K h⟩ := by
  ext
  simp only [conjHomK_apply]
  rw [inverts_s_K h t (t_mem_K h), t_inv h]

/-- `conjHomK` is an involution: it is conjugation by `s`, and `s² = 1`. -/
theorem conjHomK_comp_self (h : BSWHyps2 G t s K) :
    (conjHomK h).comp (conjHomK h) = MonoidHom.id ↥K := by
  ext x
  simp only [MonoidHom.comp_apply, MonoidHom.id_apply, conjHomK_apply, s_inv h, mul_assoc]
  rw [s_mul_self h, mul_one, ← mul_assoc s s (x : G), s_mul_self h, one_mul]

end ConjAction

end Work.BSW
