import Mathlib
import Submission.Work.DoubleTransitivity.Sec2.prop1a_odd

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Two distinct commuting involutions lie in a common conjugate of a Bender subgroup

If `H` is a Bender subgroup of a finite group `G` and `a, b` are distinct commuting
involutions, then some conjugate `g H g⁻¹` contains both `a` and `b`.

The proof is short once Peterfalvi I §1 (10)(a) (`Sec1.unique_fixed`) and §2 Prop 1(a)
(`Sec2.prop1a_odd`) are available:

* `a * b` is again an involution (its square is `a² b² = 1` using `a b = b a`, and it is not
  trivial since `a ≠ b`), so `orderOf (a * b) = 2` is even, i.e. not odd;
* the contrapositive of `prop1a_odd` then produces a point `ω ∈ Ω = G ⧸ H` fixed by both `a`
  and `b`;
* writing `ω = mk g`, the stabiliser of `ω` is `conj g H` (`mem_conj_iff_smul_fixed`), so both
  `a` and `b` lie in `conj g H`.
-/

set_option autoImplicit false

open Submission.Blueprint
open Work.DoubleTransitivity

namespace Work.DoubleTransitivity.Sec5

/-- `a * b` is an involution when `a, b` are distinct commuting involutions. -/
private theorem orderOf_mul_eq_two {G : Type} [Group G] {a b : G}
    (ha : orderOf a = 2) (hb : orderOf b = 2) (hne : a ≠ b) (hcomm : a * b = b * a) :
    orderOf (a * b) = 2 := by
  have haa : a * a = 1 := by rw [← pow_two, ← ha]; exact pow_orderOf_eq_one a
  have hbb : b * b = 1 := by rw [← pow_two, ← hb]; exact pow_orderOf_eq_one b
  have h2 : (a * b) ^ 2 = 1 := by
    calc (a * b) ^ 2 = (a * b) * (a * b) := by rw [pow_two]
      _ = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [← hcomm]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [haa, hbb, one_mul]
  refine orderOf_eq_prime h2 ?_
  intro hab1
  apply hne
  calc a = a * 1 := (mul_one a).symm
    _ = a * (b * b) := by rw [hbb]
    _ = (a * b) * b := by group
    _ = 1 * b := by rw [hab1]
    _ = b := one_mul b

theorem exists_conj_of_commuting_involutions {G : Type} [Group G] [Finite G]
    {H : Subgroup G} (hH : Work.DoubleTransitivity.IsBender H) {a b : G}
    (ha : orderOf a = 2) (hb : orderOf b = 2) (hne : a ≠ b) (hcomm : a * b = b * a) :
    ∃ g : G, a ∈ Submission.Blueprint.conj g H ∧ b ∈ Submission.Blueprint.conj g H := by
  have hord : orderOf (a * b) = 2 := orderOf_mul_eq_two ha hb hne hcomm
  -- `orderOf (a * b)` is even, hence not odd, so `a` and `b` have a common fixed point.
  have hcommon : ∃ ω : Omega H, a • ω = ω ∧ b • ω = ω := by
    by_contra h
    exact absurd (Sec2.prop1a_odd hH ha hb h) (by rw [hord]; decide)
  obtain ⟨ω, haω, hbω⟩ := hcommon
  -- The stabiliser of `mk g = ω` is `conj g H`.
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective ω
  exact ⟨g, mem_conj_iff_smul_fixed.mpr haω, mem_conj_iff_smul_fixed.mpr hbω⟩

end Work.DoubleTransitivity.Sec5
