import Mathlib
import Submission.Work.ZassenhausPSL2.Defs
import Submission.Work.ZassenhausPSL2.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open Submission.Blueprint

namespace Work.ZassenhausPSL2.ZData

/-!
# `D = twoPoint H t` acts fixed point freely on `Q`

In the split rank-one Zassenhaus configuration (`IsSplitRankOne H Q t`, `IsZassenhaus H`) every
non-identity element of the two-point stabiliser `D = H ⊓ Hᵗ` has no non-trivial fixed point on
the regular normal subgroup `Q`:

`∀ d ∈ D, d ≠ 1 → ∀ x ∈ Q, d * x * d⁻¹ = x → x = 1`.

The argument is the classical geometric one on `Ω = G ⧸ H`.  Let `d ∈ D`, `d ≠ 1` and
`1 ≠ x ∈ Q` with `d x = x d`.  Then `d` fixes

* the base point `∞ = H`, because `D ≤ H`;
* the point `tH`, because `D ≤ Hᵗ` is exactly the set of `d ∈ H` fixing `tH`;
* the point `x tH = x • (tH)`, because `d (x t) = x (d t) ∈ x t H` (using `d x = x d` and the
  previous point),

and these three points are pairwise distinct: `∞ ≠ tH` because `t ∉ H`; `∞ ≠ x tH` because
`x t ∈ H` would force `t = x⁻¹ (x t) ∈ H`; and `tH ≠ x tH` because `t⁻¹ x t ∈ H` together with
`x ∈ H` would put `x` in `Q ⊓ D = 1`.  Since `IsZassenhaus H` says that the pointwise
stabiliser of three distinct points of `Ω` is trivial, `d = 1`, a contradiction.
-/

theorem dStab_fpf_on_Q {G : Type} [Group G] [Finite G] (H Q : Subgroup G) (t : G)
    (h : Submission.Blueprint.IsSplitRankOne H Q t) (hz : Submission.Blueprint.IsZassenhaus H) :
    ∀ d : G, d ∈ Submission.Blueprint.twoPoint H t → d ≠ 1 →
      ∀ x : G, x ∈ Q → d * x * d⁻¹ = x → x = 1 := by
  intro d hd hd1 x hx hconj
  by_contra hx1
  -- the action on `Ω = G ⧸ H` is by left multiplication
  have hsmul : ∀ (g y : G), g • (y : G ⧸ H) = (g * y : G ⧸ H) := fun g y => by
    rw [MulAction.Quotient.smul_coe]; rfl
  have hcomm : d * x = x * d := by
    calc d * x = (d * x * d⁻¹) * d := by group
      _ = x * d := by rw [hconj]
  have hdH : d ∈ H := hd.1
  have hdconj : d ∈ conj t H := hd.2
  -- `d ∈ Hᵗ` means `t⁻¹ d t ∈ H`
  have htinv : t⁻¹ * d * t ∈ H := by
    rw [conj, Subgroup.mem_map] at hdconj
    obtain ⟨e, he, hed⟩ := hdconj
    have h1 : t * e * t⁻¹ = d := by
      have h2 : (MulAut.conj t) e = t * e * t⁻¹ := MulAut.conj_apply t e
      rw [MulEquiv.coe_toMonoidHom, h2] at hed; exact hed
    rw [← h1, show t⁻¹ * (t * e * t⁻¹) * t = e by group]; exact he
  -- the three points fixed by `d`
  have hp1 : d • ((1 : G) : G ⧸ H) = ((1 : G) : G ⧸ H) := by
    rw [hsmul d 1, QuotientGroup.eq]
    simpa using hdH
  have hp2 : d • (t : G ⧸ H) = (t : G ⧸ H) := by
    rw [hsmul d t, QuotientGroup.eq]
    rw [show (d * t)⁻¹ * t = (t⁻¹ * d * t)⁻¹ by group]
    exact H.inv_mem htinv
  have hp3 : d • (x • (t : G ⧸ H)) = x • (t : G ⧸ H) := by
    rw [← mul_smul, hcomm, mul_smul, hp2]
  -- they are pairwise distinct
  have h12 : ((1 : G) : G ⧸ H) ≠ (t : G ⧸ H) := by
    intro hc
    rw [QuotientGroup.eq] at hc
    exact h.not_mem (by simpa using hc)
  have h13 : ((1 : G) : G ⧸ H) ≠ x • (t : G ⧸ H) := by
    intro hc
    rw [hsmul x t] at hc
    rw [QuotientGroup.eq] at hc
    have hxt : x * t ∈ H := by simpa using hc
    have ht : t ∈ H := by
      have h3 : x⁻¹ * (x * t) ∈ H := H.mul_mem (H.inv_mem (h.le hx)) hxt
      simpa using h3
    exact h.not_mem ht
  have h23 : (t : G ⧸ H) ≠ x • (t : G ⧸ H) := by
    intro hc
    rw [hsmul x t] at hc
    rw [QuotientGroup.eq] at hc
    have htin : t⁻¹ * (x * t) ∈ H := by simpa using hc
    have hxconj : x ∈ conj t H := by
      rw [conj, Subgroup.mem_map]
      exact ⟨t⁻¹ * (x * t), htin, by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
    have hxbot : x ∈ (⊥ : Subgroup G) := by
      rw [← h.inf_eq]
      exact ⟨hx, h.le hx, hxconj⟩
    exact hx1 (by simpa using hxbot)
  exact hd1 (hz ((1 : G) : G ⧸ H) (t : G ⧸ H) (x • (t : G ⧸ H)) h12 h13 h23 d hp1 hp2 hp3)

end Work.ZassenhausPSL2.ZData
