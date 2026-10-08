import Mathlib
import Submission.Work.ZassenhausSuzuki.Defs
import Submission.Work.ThmF.ChV12.canonicalForm
import Submission.Work.ZassenhausPSL2.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `C_H(s t) = 1` in a Zassenhaus split rank-one configuration

In a split rank-one configuration `H = Q ⋊ D` (`Q ⊴ H`, `D = H ∩ Hᵗ`, `Q ⊓ D = ⊥`,
`Q ⊔ D = H`) with `H` a Zassenhaus point stabiliser, an involution `s ∈ Q` and the
involution `t ∉ H`, the element `s t` is not centralised by any non-trivial element of `H`.

The argument is a fixed-point count in `Ω = G ⧸ H`.  Let `x ∈ H` commute with `g = s t`.
Then `x` fixes the three points

* `H`, because `x ∈ H`;
* `t H`, because `x ∈ H ∩ Hᵗ` (from the commutation relation `x g = g x` one gets
  `s x s = t x t`; the right hand side is `s x s ∈ H`, so `t x t ∈ H` and hence
  `x ∈ Hᵗ`);
* `g H = s t H`, because `x g = g x` and `x` fixes `H`.

These three points are pairwise distinct: `H ≠ t H` and `H ≠ s t H` because `t, s t ∉ H`
(the latter since `s ∈ H`), while `t H ≠ s t H` would force `s ∈ H ∩ Hᵗ = D` and hence
`s ∈ Q ⊓ D = ⊥`, contradicting `orderOf s = 2`.  Fixing three distinct points, `x` is
trivial by the Zassenhaus hypothesis.
-/

set_option autoImplicit false

namespace Work.ZassenhausSuzuki

theorem mem_H_centralizer_st {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) (hZ : Submission.Blueprint.IsZassenhaus H)
    (h2 : IsPGroup 2 Q) (hsQ : s ∈ Q) (hs2 : orderOf s = 2)
    {x : G} (hxH : x ∈ H) (hcomm : x * (s * t) = (s * t) * x) : x = 1 := by
  have ht2 : t * t = 1 := Work.RankOneUniqueness.mul_self_eq_one h
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hsH : s ∈ H := h.le hsQ
  have hss : s * s = 1 := by
    have h1 : s ^ 2 = 1 := by
      have := pow_orderOf_eq_one s
      rwa [hs2] at this
    simpa [pow_two] using h1
  have hsne : s ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hs2
    exact absurd hs2 (by norm_num)
  -- From `x * (s * t) = (s * t) * x` and `s² = t² = 1` we get `s * x * s = t * x * t`.
  have htst : t * x * t ∈ H := by
    have hkey : s * x * s = t * x * t := by
      have hh : s * (x * (s * t)) * t = s * ((s * t) * x) * t := by rw [hcomm]
      have hL : s * (x * (s * t)) * t = s * x * s := by
        calc s * (x * (s * t)) * t = s * x * s * t * t := by group
          _ = s * x * s * (t * t) := by group
          _ = s * x * s := by rw [ht2, mul_one]
      have hR : s * ((s * t) * x) * t = t * x * t := by
        calc s * ((s * t) * x) * t = s * s * t * x * t := by group
          _ = (s * s) * (t * x * t) := by group
          _ = t * x * t := by rw [hss, one_mul]
      rw [← hL, hh, hR]
    rw [← hkey]
    exact H.mul_mem (H.mul_mem hsH hxH) hsH
  -- `x` fixes the base point `H`.
  have hfix1 : x • Work.RankOneUniqueness.pt H = Work.RankOneUniqueness.pt H :=
    Work.RankOneUniqueness.smul_pt_of_mem H hxH
  -- `x` fixes the point `t H`.
  have hfix2 : x • ((t : G) : G ⧸ H) = ((t : G) : G ⧸ H) := by
    rw [Work.RankOneUniqueness.smul_mk, QuotientGroup.eq]
    have heq : (x * t)⁻¹ * t = (t * x * t)⁻¹ := by
      simp only [mul_inv_rev, hti, mul_assoc]
    rw [heq]
    exact H.inv_mem htst
  -- `x` fixes the point `s t H`.
  have hfix3 : x • ((s * t : G) : G ⧸ H) = ((s * t : G) : G ⧸ H) := by
    rw [Work.RankOneUniqueness.smul_mk, QuotientGroup.eq]
    have hcomm_inv : (s * t)⁻¹ * x⁻¹ = x⁻¹ * (s * t)⁻¹ := by
      have := congrArg Inv.inv hcomm
      simpa [mul_inv_rev] using this
    have heq : (x * (s * t))⁻¹ * (s * t) = x⁻¹ := by
      rw [mul_inv_rev, hcomm_inv, mul_assoc, inv_mul_cancel, mul_one]
    rw [heq]
    exact H.inv_mem hxH
  -- The three points are pairwise distinct.
  have h12 : Work.RankOneUniqueness.pt H ≠ ((t : G) : G ⧸ H) := by
    intro hc
    exact h.not_mem ((Work.RankOneUniqueness.mk_eq_pt_iff H t).mp hc.symm)
  have h13 : Work.RankOneUniqueness.pt H ≠ ((s * t : G) : G ⧸ H) := by
    intro hc
    have hstH : s * t ∈ H := (Work.RankOneUniqueness.mk_eq_pt_iff H (s * t)).mp hc.symm
    have htH : t ∈ H := by
      have := H.mul_mem (H.inv_mem hsH) hstH
      rwa [inv_mul_cancel_left] at this
    exact h.not_mem htH
  have h23 : ((t : G) : G ⧸ H) ≠ ((s * t : G) : G ⧸ H) := by
    intro hc
    have hmem : t⁻¹ * (s * t) ∈ H := QuotientGroup.eq.mp hc
    have hconj : s ∈ Submission.Blueprint.conj t H :=
      (Work.RankOneUniqueness.mem_conj_iff H t s).mpr ⟨t⁻¹ * (s * t), hmem, by group⟩
    have hsD : s ∈ Submission.Blueprint.twoPoint H t :=
      (Work.RankOneUniqueness.mem_twoPoint_iff (H := H) (t := t)).mpr ⟨hsH, hconj⟩
    have hsbot : s ∈ (⊥ : Subgroup G) := by
      rw [← h.inf_eq]; exact ⟨hsQ, hsD⟩
    exact hsne (Subgroup.mem_bot.mp hsbot)
  exact hZ (Work.RankOneUniqueness.pt H) ((t : G) : G ⧸ H) ((s * t : G) : G ⧸ H)
    h12 h13 h23 x hfix1 hfix2 hfix3

end Work.ZassenhausSuzuki
