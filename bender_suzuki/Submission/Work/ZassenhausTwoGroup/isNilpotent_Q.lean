import Mathlib
import Submission.Work.ZassenhausTwoGroup.Defs
import Submission.Work.ZassenhausTwoGroup.isTI_Q

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ZassenhausTwoGroup.isNilpotent_Q`

In the split rank-one data of a Zassenhaus group (`IsSplitRankOne H Q t`, `IsZassenhaus H`), the
two-point stabiliser `D = twoPoint H t` acts **fixed-point-freely** on `Q` by conjugation
(`fpfOn_twoPoint`, proved from the geometric description of the action of `G` on `Ω = G ⧸ H`).

If moreover `D ≠ ⊥` (hypothesis `hD`), then `D` contains an element of prime order `p`; its
conjugation action on `Q` is a fixed-point-free automorphism of prime order, so Thompson's
theorem (`Submission.Blueprint.ThompsonFrobeniusProp`, the hypothesis `hTh`) makes `Q`
nilpotent.

This is the `Q`-nilpotency step of Feit's theorem on Zassenhaus groups (the fact used everywhere
in the area `ZassenhausTwoGroup` that `Q = O_2(Q) × O_{2'}(Q)`).
-/

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.ZassenhausTwoGroup

open IsTIQ

/-- In a split rank-one Zassenhaus configuration the two-point stabiliser `D = twoPoint H t`
acts fixed-point-freely on `Q`.

Geometrically, on `Ω = G ⧸ H` an element `d ∈ D` fixes the base point `∞` and the point
`t • ∞`; if `d` also fixes `x ∈ Q` (`d x d⁻¹ = x`) then it fixes the third point `x • (t • ∞)`.
For `1 ≠ x ∈ Q` those three points are distinct, so triviality of the three-point stabiliser
(`IsZassenhaus H`) forces `d = 1`. -/
theorem fpfOn_twoPoint {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (h : IsSplitRankOne H Q t) (hz : IsZassenhaus H) :
    IsFpfOn (twoPoint H t) Q := by
  intro d hd hd1 x hx hdx
  by_contra hx1
  have hdH : d ∈ H := (Subgroup.mem_inf.mp hd).1
  have hdfix : d • (t : G ⧸ H) = (t : G ⧸ H) :=
    ((mem_twoPoint_iff_smul H t d).mp hd).2
  have hdx' : d * x = x * d := by
    calc d * x = d * x * d⁻¹ * d := by group
      _ = x * d := by rw [hdx]
  have hda : d • basePt H = basePt H := smul_basePt_of_mem H hdH
  have hdb : d • (t • basePt H) = t • basePt H := by
    simpa [smul_basePt] using hdfix
  have hdc : d • (x • (t • basePt H)) = x • (t • basePt H) := by
    rw [← mul_smul, hdx', mul_smul, hdb]
  have hab : basePt H ≠ t • basePt H := by
    intro hh
    exact h.not_mem ((smul_basePt_eq_iff H t).mp hh.symm)
  have hac : basePt H ≠ x • (t • basePt H) := by
    intro hh
    have hxt : x * t ∈ H := by
      have h1 : (x * t) • basePt H = basePt H := by
        rw [mul_smul]; exact hh.symm
      exact (smul_basePt_eq_iff H (x * t)).mp h1
    have htH : t ∈ H := by
      have h2 : x⁻¹ * (x * t) ∈ H := H.mul_mem (H.inv_mem (h.le hx)) hxt
      rwa [← mul_assoc, inv_mul_cancel, one_mul] at h2
    exact h.not_mem htH
  have hbc : t • basePt H ≠ x • (t • basePt H) := by
    intro hh
    have hxfix : x • (t : G ⧸ H) = (t : G ⧸ H) := by
      rw [← smul_basePt H t]
      rw [show x • (t • basePt H) = t • basePt H from hh.symm]
    have hxT : x ∈ twoPoint H t :=
      (mem_twoPoint_iff_smul H t x).mpr ⟨h.le hx, hxfix⟩
    have hxbot : x ∈ (⊥ : Subgroup G) := by
      rw [← h.inf_eq]
      exact ⟨hx, hxT⟩
    exact hx1 (Subgroup.mem_bot.mp hxbot)
  exact hd1 (hz (basePt H) (t • basePt H) (x • (t • basePt H)) hab hac hbc d hda hdb hdc)

theorem isNilpotent_Q {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hTh : Submission.Blueprint.ThompsonFrobeniusProp)
    (h : Submission.Blueprint.IsSplitRankOne H Q t) (hz : Submission.Blueprint.IsZassenhaus H)
    (hD : Submission.Blueprint.twoPoint H t ≠ ⊥) : Group.IsNilpotent Q := by
  by_cases hQ : Q = ⊥
  · rw [hQ]
    infer_instance
  have hfpf : IsFpfOn (twoPoint H t) Q := fpfOn_twoPoint h hz
  -- an element of `D = twoPoint H t` of prime order `p`
  have hDcard : 1 < Nat.card (twoPoint H t) := (Subgroup.one_lt_card_iff_ne_bot _).mpr hD
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (Nat.ne_of_gt hDcard)
  obtain ⟨g, hgord⟩ :=
    @exists_prime_orderOf_dvd_card' ↥(twoPoint H t) _ _ p ⟨hp⟩ hpdvd
  have hgH : (g : G) ∈ H := (Subgroup.mem_inf.mp g.2).1
  have hgne : (g : G) ≠ 1 := by
    intro hc
    have hg1 : (g : ↥(twoPoint H t)) = 1 := Subtype.ext hc
    rw [hg1, orderOf_one] at hgord
    exact hp.ne_one hgord.symm
  -- the conjugation action of `g` on `Q` as an automorphism of `Q`
  let φ : Subgroup.normalizer (Q : Set G) := ⟨(g : G), h.normal hgH⟩
  let α : MulAut Q := Subgroup.normalizerMonoidHom Q φ
  have hfpfα : ∀ x : Q, α x = x → x = 1 := by
    intro x hx
    have hxG : (g : G) * (x : G) * (g : G)⁻¹ = (x : G) := by
      have h := congrArg (fun y : Q => (y : G)) hx
      exact h
    exact Subtype.ext (hfpf (g : G) g.2 hgne (x : G) x.2 hxG)
  have hαne1 : α ≠ 1 := by
    intro hα1
    obtain ⟨x, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hQ
    exact hx (hfpfα x (by rw [hα1]; simp))
  -- the order of `α` is the prime `p`
  have hφord : orderOf φ = p := by
    have h1 : orderOf φ = orderOf (g : G) := by
      show orderOf (⟨(g : G), h.normal hgH⟩ : Subgroup.normalizer (Q : Set G)) =
        orderOf (g : G)
      rw [Subgroup.orderOf_mk]
    rw [h1, Subgroup.orderOf_coe, hgord]
  have hαdvd : orderOf α ∣ p := by
    have h := orderOf_map_dvd (Subgroup.normalizerMonoidHom Q) φ
    rwa [hφord] at h
  have hαord : orderOf α = p := by
    rcases (Nat.dvd_prime hp).mp hαdvd with h1 | h1
    · rw [orderOf_eq_one_iff] at h1
      exact absurd h1 hαne1
    · exact h1
  exact hTh ↥Q α (by rw [hαord]; exact hp) hfpfα

end Work.ZassenhausTwoGroup
