/-
Copyright (c) 2025. All rights reserved.

# Injectivity of inflation in degree `1`

For a normal subgroup `N ◁ G` and a `G`-module `A`, inflation
`H¹(G ⧸ N, A^N) → H¹(G, A)` is injective: its kernel is trivial.  This is the
degree-`1` part of the exactness of the inflation–restriction sequence, and the
first step of the five-term sequence attached to `1 → N → G → G ⧸ N → 1`.

The proof is the usual one: if the inflation of the class of a cocycle `f` on
`G ⧸ N` with values in `A^N` is a coboundary on `G`, say
`(inf f) g = g • a - a`, then `n • a - a = (inf f) n = 0` for every `n ∈ N`
because `f` vanishes at `1`; hence `a ∈ A^N`, and `a` is a primitive for `f`
on the quotient.

## Main result

* `Work.GroupCohomology.ker_infH1_eq_bot`
-/
import Mathlib
import Submission.Work.GroupCohomology.Inflation
import Submission.Work.GroupCohomology.H1pi_eq_zero_iff
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.GroupCohomology

/-- Inflation `H¹(G ⧸ N, A^N) → H¹(G, A)` is injective: its kernel is trivial. -/
theorem ker_infH1_eq_bot {G : Type*} {A : Type*} [Group G] [AddCommGroup A]
    [DistribMulAction G A] (N : Subgroup G) [N.Normal] :
    (Work.GroupCohomology.infH1 (A := A) N).ker = ⊥ := by
  -- It suffices to show that a class inflating to zero is already zero.
  have key : ∀ x : H1 (G ⧸ N) (invariants N A), infH1 (A := A) N x = 0 → x = 0 := by
    intro x hx
    induction x using QuotientAddGroup.induction_on with
    | _ f =>
      rw [show (↑f : H1 (G ⧸ N) (invariants N A)) =
            H1π (G ⧸ N) (invariants N A) f from rfl, infH1_H1π,
          H1pi_eq_zero_iff, mem_B1_iff] at hx
      obtain ⟨a, ha⟩ := hx
      -- `ha : d⁰_G a = inf f`, i.e. `g • a - a = (f (mk' g) : A)` for all `g : G`.
      -- Since `f` is a cocycle, it vanishes at `1`, so `n • a = a` for `n ∈ N`.
      have hainv : a ∈ invariants N A := by
        rw [mem_invariants]
        intro n
        have h := congrFun ha (n : G)
        rw [d0_apply, infCocycle1_apply] at h
        have hm : QuotientGroup.mk' N (n : G) = 1 := by
          rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
          exact n.2
        rw [hm] at h
        have h1 : (f : Z1 (G ⧸ N) (invariants N A)).1 1 = 0 :=
          Z1.map_one (G ⧸ N) (invariants N A) f.2
        rw [h1] at h
        exact sub_eq_zero.mp h
      rw [show (↑f : H1 (G ⧸ N) (invariants N A)) =
            H1π (G ⧸ N) (invariants N A) f from rfl, H1pi_eq_zero_iff, mem_B1_iff]
      -- `a`, being `N`-invariant, is the primitive of `f` on the quotient.
      refine ⟨⟨a, hainv⟩, ?_⟩
      funext q
      induction q using QuotientGroup.induction_on with
      | _ g =>
        show ((QuotientGroup.mk' N g) • (⟨a, hainv⟩ : invariants N A) - ⟨a, hainv⟩) =
          (f : (G ⧸ N) → invariants N A) (QuotientGroup.mk' N g)
        rw [quotientSMul_mk']
        apply Subtype.ext
        have h := congrFun ha g
        rw [d0_apply, infCocycle1_apply] at h
        exact h
  rw [AddMonoidHom.ker_eq_bot_iff]
  intro x y hxy
  have h : infH1 (A := A) N (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  exact sub_eq_zero.mp (key (x - y) h)

end Work.GroupCohomology
