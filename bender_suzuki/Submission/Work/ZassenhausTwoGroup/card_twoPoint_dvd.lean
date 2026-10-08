import Mathlib
import Submission.Work.ZassenhausTwoGroup.Defs
import Submission.Work.ZassenhausTwoGroup.isTI_Q
import Submission.Work.ZassenhausTwoGroup.card_dvd_card_sub_one_of_isFpfOn

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ZassenhausTwoGroup.card_twoPoint_dvd`

In a split rank-one Zassenhaus configuration (`IsSplitRankOne H Q t`, `IsZassenhaus H`) the
two-point stabiliser `D = twoPoint H t = H ⊓ Hᵗ` has order dividing `|Q| - 1`.

The proof has two ingredients.

* `isFpfOn_twoPoint_Q` (this file, geometric): `D` acts *fixed point freely* on `Q` by
  conjugation, using the permutation action on `Ω = G ⧸ H` from `Work.ZassenhausTwoGroup.IsTIQ`.
  If `1 ≠ x ∈ Q` commutes with `d ∈ D`, then `d` fixes the three distinct points
  `∞ = basePt H` (because `D ≤ H`), `t • ∞` (because `D ≤ Hᵗ`, the definition of `D = H ⊓ Hᵗ`)
  and `x • (t • ∞)` (because `d x = x d` and `d` fixes `t • ∞`).  Here `x • (t • ∞) ≠ ∞` since
  `x` fixes `∞`, and `x • (t • ∞) ≠ t • ∞` since `1 ≠ x ∈ Q` acts freely on `Ω ∖ {∞}`
  (`IsTIQ.Q_smul_eq_self`).  The Zassenhaus hypothesis (`IsZassenhaus H`: the pointwise
  stabiliser of three distinct points is trivial) then forces `d = 1`.

* `card_dvd_card_sub_one_of_isFpfOn` (imported, counting): if a subgroup `D ≤ N_G(A)` acts fixed
  point freely on `A` by conjugation, then `|D| ∣ |A| - 1` — the `D`-orbits on `A#` all have size
  `|D|`, so Burnside's count `∑_{d} |Fix d| = #orbits · |D|` reads
  `|A| + (|D| - 1) = #orbits · |D|`.

`D ≤ N_G(Q)` holds because `H ≤ N_G(Q)` (`IsSplitRankOne.normal`) and `D ≤ H`, and the theorem is
the instance `A = Q`, `D = twoPoint H t`.
-/

set_option autoImplicit false

open Submission.Blueprint

namespace Work.ZassenhausTwoGroup

namespace CardTwoPoint

variable {G : Type} [Group G] {H Q : Subgroup G} {t : G}

/-! ## The geometric part: `D = twoPoint H t` acts fixed point freely on `Q` -/

/-- `D = twoPoint H t` fixes the base point `∞ = basePt H` of `Ω = G ⧸ H`. -/
theorem smul_basePt_of_mem_twoPoint (h : IsSplitRankOne H Q t) {d : G}
    (hd : d ∈ twoPoint H t) : d • IsTIQ.basePt H = IsTIQ.basePt H :=
  IsTIQ.smul_basePt_of_mem H (twoPoint_le_H h hd)

/-- In a split rank-one Zassenhaus configuration, `D = twoPoint H t` acts fixed point freely on
`Q`: a `1 ≠ d ∈ D` commuting with `x ∈ Q` forces `x = 1`. -/
theorem isFpfOn_twoPoint_Q (h : IsSplitRankOne H Q t) (hz : IsZassenhaus H) :
    IsFpfOn (twoPoint H t) Q := by
  intro d hd hd1 x hx hconj
  by_contra hx1
  -- the three fixed points of `d`
  have hfix_base : d • IsTIQ.basePt H = IsTIQ.basePt H := smul_basePt_of_mem_twoPoint h hd
  have hfix_tpt : d • (t : G ⧸ H) = (t : G ⧸ H) :=
    ((IsTIQ.mem_twoPoint_iff_smul H t d).mp hd).2
  have hcomm : d * x = x * d := by
    calc d * x = (d * x * d⁻¹) * d := by group
      _ = x * d := by rw [hconj]
  have hfix_x : d • (x • (t : G ⧸ H)) = x • (t : G ⧸ H) := by
    calc d • (x • (t : G ⧸ H)) = (d * x) • (t : G ⧸ H) := by rw [mul_smul]
      _ = (x * d) • (t : G ⧸ H) := by rw [hcomm]
      _ = x • (d • (t : G ⧸ H)) := by rw [mul_smul]
      _ = x • (t : G ⧸ H) := by rw [hfix_tpt]
  -- the three points are pairwise distinct
  have ht_ne_base : (t : G ⧸ H) ≠ IsTIQ.basePt H := (IsTIQ.basePt_ne_iff H t).mpr h.not_mem
  have hne1 : IsTIQ.basePt H ≠ (t : G ⧸ H) := ht_ne_base.symm
  have hne2 : IsTIQ.basePt H ≠ x • (t : G ⧸ H) := by
    intro hc
    have h1 : x⁻¹ • IsTIQ.basePt H = x⁻¹ • (x • (t : G ⧸ H)) := by rw [hc]
    rw [IsTIQ.smul_basePt_of_mem H (H.inv_mem (h.le hx)),
      show x⁻¹ • (x • (t : G ⧸ H)) = (t : G ⧸ H) by rw [← mul_smul, inv_mul_cancel, one_smul]]
      at h1
    exact ht_ne_base h1.symm
  have hne3 : (t : G ⧸ H) ≠ x • (t : G ⧸ H) := by
    intro hc
    exact hx1 (IsTIQ.Q_smul_eq_self h hx hc.symm ht_ne_base)
  -- three distinct fixed points force `d = 1`
  exact hd1 (hz (IsTIQ.basePt H) (t : G ⧸ H) (x • (t : G ⧸ H)) hne1 hne2 hne3 d
    hfix_base hfix_tpt hfix_x)

end CardTwoPoint

/-! ## Assembly -/

theorem card_twoPoint_dvd {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) (hz : Submission.Blueprint.IsZassenhaus H) :
    Nat.card (Submission.Blueprint.twoPoint H t) ∣ Nat.card Q - 1 := by
  have hfpf : IsFpfOn (twoPoint H t) Q := CardTwoPoint.isFpfOn_twoPoint_Q h hz
  have hN : twoPoint H t ≤ Subgroup.normalizer (Q : Set G) :=
    le_trans (twoPoint_le_H h) (H_le_normalizer_Q h)
  exact card_dvd_card_sub_one_of_isFpfOn hN hfpf

end Work.ZassenhausTwoGroup
