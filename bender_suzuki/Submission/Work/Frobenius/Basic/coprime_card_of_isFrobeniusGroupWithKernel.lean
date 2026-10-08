import Mathlib
import Submission.Work.Frobenius.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

namespace Work.Frobenius.Basic

/-- In a Frobenius group with kernel `K` and complement `H`, the orders of `K` and `H` are
coprime.

Suppose a prime `p` divided both `|K|` and `|H|`.  By Cauchy's theorem there is `x ∈ H` of
order `p`; put `A = ⟨x⟩`, a group of order `p` acting on `K` by conjugation (which makes
sense because `K` is normal).  The fixed points of this action are the `k ∈ K` with
`x k x⁻¹ = k`, and these are trivial by the fixed-point-freeness of `H` on `K`, so the action
has exactly one fixed point.  A classical congruence for `p`-group actions
(`IsPGroup.card_modEq_card_fixedPoints`) then gives `|K| ≡ 1 [MOD p]`, contradicting `p ∣ |K|`. -/
theorem coprime_card_of_isFrobeniusGroupWithKernel {G : Type*} [Group G] [Fintype G] {K H : Subgroup G} (h : IsFrobeniusGroupWithKernel K H) : (Nat.card K).Coprime (Nat.card H) := by
  classical
  haveI : K.Normal := h.normal
  -- It suffices to rule out a common prime divisor.
  refine Nat.coprime_of_dvd' fun p hp hpK hpH => ?_
  haveI : Fact p.Prime := ⟨hp⟩
  -- Cauchy's theorem in `H` gives an element of order `p`.
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := H) p hpH
  have horder : orderOf (x : G) = p := by
    rw [Subgroup.orderOf_coe x, hx]
  have hxne : (x : G) ≠ 1 := by
    intro h1
    have h2 : orderOf ((x : G)) = 1 := by rw [h1]; exact orderOf_one
    rw [horder] at h2
    exact hp.ne_one h2
  -- The cyclic group `A = ⟨x⟩` of order `p` acts on `K` by conjugation.
  let A : Subgroup G := Subgroup.zpowers (x : G)
  letI : MulAction A K := MulAction.compHom K ((MulAut.conjNormal (H := K)).comp A.subtype)
  have hsmul : ∀ (a : A) (k : K), (((a • k : K) : G)) = (a : G) * (k : G) * (a : G)⁻¹ := by
    intro a k
    show ((MulAut.conjNormal (a : G)) k : G) = _
    rw [MulAut.conjNormal_apply]
  -- The only fixed point of this action is `1`.
  have hfix : MulAction.fixedPoints A K = {1} := by
    ext k
    rw [MulAction.mem_fixedPoints]
    constructor
    · intro hk
      have h1 := hk ⟨(x : G), Subgroup.mem_zpowers (x : G)⟩
      have h2 : (x : G) * (k : G) * (x : G)⁻¹ = (k : G) := by
        have h3 := congrArg (Subtype.val) h1
        rw [hsmul] at h3
        exact h3
      have h3 := h.fpf x.2 hxne k.2 h2
      exact Subtype.ext (by simpa using h3)
    · intro hk
      rw [Set.mem_singleton_iff] at hk
      subst hk
      intro a
      apply Subtype.ext
      rw [hsmul]
      simp
  have hcard : Nat.card (MulAction.fixedPoints A K) = 1 := by
    rw [hfix]
    simp
  -- `A` is a `p`-group, so `|K| ≡ |Fix| [MOD p]`.
  have hApg : IsPGroup p A := by
    refine IsPGroup.of_card (n := 1) ?_
    show Nat.card (Subgroup.zpowers (x : G)) = p ^ 1
    rw [pow_one, Nat.card_zpowers, horder]
  have hmod := hApg.card_modEq_card_fixedPoints K
  rw [hcard] at hmod
  have hzero : Nat.card K ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr hpK
  have h01 : (0 : ℕ) ≡ 1 [MOD p] := hzero.symm.trans hmod
  exact absurd (Nat.ModEq.eq_of_lt_of_lt h01 hp.pos hp.one_lt) zero_ne_one

end Work.Frobenius.Basic
