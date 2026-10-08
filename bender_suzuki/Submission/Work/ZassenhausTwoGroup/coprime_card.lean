import Mathlib
import Submission.Work.ZassenhausTwoGroup.Defs
import Submission.Work.ZassenhausTwoGroup.isTI_Q
import Submission.Work.RankOneUniqueness.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ZassenhausTwoGroup.coprime_card`

In the split rank-one set-up of a Zassenhaus group (`IsSplitRankOne H Q t`, `IsZassenhaus H`)
the two-point stabiliser `D = twoPoint H t` has order coprime to `|Q|`.

The proof is the classical orbit count, in the form `|D| ∣ |Q| - 1`.

* `D` acts on the group `Q` by conjugation (`D ≤ H ≤ N_G(Q)`).
* The action is fixed point free on `Q#`: if `1 ≠ x ∈ Q` and `d ∈ D` with `d x d⁻¹ = x`, then
  `d` fixes the three distinct points `∞ = pt H`, `t • ∞` and `x • (t • ∞)` of `Ω = G ⧸ H`
  (distinctness of the last two from `∞` and from each other uses `t ∉ H` and the freeness of
  the action of `Q` on `Ω ∖ {∞}`), so `d = 1` by the Zassenhaus hypothesis.
* Burnside's lemma (`∑_d |Fix d| = #orbits · |D|`) then gives
  `|Q| + (|D| - 1) = #orbits · |D|`, i.e. `|D| ∣ |Q| - 1`; hence `(|D|, |Q|) = 1`.
-/

set_option autoImplicit false

open Submission.Blueprint
open Work.RankOneUniqueness

namespace Work.ZassenhausTwoGroup

variable {G : Type} [Group G] {H Q : Subgroup G} {t : G}

/-! ## The geometric part: `D` fixes three distinct points of `Ω = G ⧸ H` -/

/-- Elements of `D = H ∩ Hᵗ` lie in `H`, hence fix the base point `∞ = pt H`. -/
lemma twoPoint_smul_pt {d : G} (hd : d ∈ twoPoint H t) : d • pt H = pt H :=
  smul_pt_of_mem H (mem_twoPoint_iff.mp hd).1

/-- Elements of `D = H ∩ Hᵗ` lie in `Hᵗ`, hence fix the point `t • ∞`. -/
lemma twoPoint_smul_tpt {d : G} (hd : d ∈ twoPoint H t) : d • (t • pt H) = t • pt H := by
  have h2 := (IsTIQ.mem_twoPoint_iff_smul H t d).mp hd
  simpa using h2.2

/-- `D = twoPoint H t` acts **fixed point freely** on `Q`: if `1 ≠ x ∈ Q` and `d ∈ D` with
`d x d⁻¹ = x`, then `d` fixes the three distinct points `∞`, `t • ∞`, `x • (t • ∞)` of
`Ω = G ⧸ H`, and the Zassenhaus hypothesis forces `d = 1`. -/
lemma isFpfOn_twoPoint_Q (h : IsSplitRankOne H Q t) (hz : IsZassenhaus H) :
    IsFpfOn (twoPoint H t) Q := by
  intro d hd hd1 x hx hconj
  by_contra hx1
  have hfix_pt : d • pt H = pt H := twoPoint_smul_pt hd
  have hfix_tpt : d • (t • pt H) = t • pt H := twoPoint_smul_tpt hd
  have hxd : d * x = x * d := by
    calc d * x = (d * x * d⁻¹) * d := by group
      _ = x * d := by rw [hconj]
  have hfix_x : d • (x • (t • pt H)) = x • (t • pt H) := by
    rw [← mul_smul, hxd, mul_smul, hfix_tpt]
  have hne1 : pt H ≠ t • pt H :=
    fun hc => h.not_mem ((smul_pt_iff H t).mp hc.symm)
  have hne2 : pt H ≠ x • (t • pt H) := by
    intro hc
    exact qPt_ne_pt h hx (by simpa using hc.symm)
  have hne3 : t • pt H ≠ x • (t • pt H) := by
    intro hc
    exact hx1 (IsTIQ.Q_smul_eq_self h hx (by simpa using hc.symm)
      ((IsTIQ.basePt_ne_iff H t).mpr h.not_mem))
  exact hd1 (hz (pt H) (t • pt H) (x • (t • pt H)) hne1 hne2 hne3 d
    hfix_pt hfix_tpt hfix_x)

/-! ## The counting part -/

/-- **Burnside count.** In the split rank-one Zassenhaus set-up, `|D|` divides `|Q| - 1`:
`D` acts on `Q` by conjugation, the action is fixed point free on `Q#`, so the sum of the
numbers of fixed points is `|Q| + (|D| - 1)`, which Burnside's lemma equates with
`#orbits · |D|`. -/
theorem card_twoPoint_dvd_card_Q_sub_one {G : Type} [Group G] [Finite G] {H Q : Subgroup G}
    {t : G} (h : IsSplitRankOne H Q t) (hz : IsZassenhaus H) :
    Nat.card (twoPoint H t) ∣ Nat.card Q - 1 := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  have hfpf := isFpfOn_twoPoint_Q h hz
  have hDQ : twoPoint H t ≤ Subgroup.normalizer (Q : Set G) :=
    le_trans (twoPoint_le_H h) (H_le_normalizer_Q h)
  have hsmul : ∀ (d : twoPoint H t) (x : Q), (d : G) * (x : G) * (d : G)⁻¹ ∈ Q := fun d x =>
    (Subgroup.mem_normalizer_iff.mp (hDQ d.2) (x : G)).mp x.2
  -- the conjugation action of `D` on `Q`
  letI : MulAction (twoPoint H t) Q :=
    { smul := fun d x => ⟨(d : G) * (x : G) * (d : G)⁻¹, hsmul d x⟩
      one_smul := fun x => by
        apply Subtype.ext
        show (1 : G) * (x : G) * (1 : G)⁻¹ = (x : G)
        simp
      mul_smul := fun d e x => by
        apply Subtype.ext
        show ((d : G) * (e : G)) * (x : G) * ((d : G) * (e : G))⁻¹
          = (d : G) * ((e : G) * (x : G) * (e : G)⁻¹) * (d : G)⁻¹
        group }
  -- `1` fixes everything
  have hfix1 : Fintype.card (MulAction.fixedBy Q (1 : twoPoint H t)) = Nat.card Q := by
    have he : (MulAction.fixedBy Q (1 : twoPoint H t)) ≃ Q :=
      (Equiv.subtypeEquivRight (fun x => by rw [MulAction.mem_fixedBy]; simp)).trans
        (Equiv.Set.univ Q)
    calc Fintype.card (MulAction.fixedBy Q (1 : twoPoint H t)) = Fintype.card Q :=
          Fintype.card_congr he
      _ = Nat.card Q := Nat.card_eq_fintype_card.symm
  -- every nontrivial `d` fixes only `1`
  have hfixne : ∀ d : twoPoint H t, d ≠ 1 → Fintype.card (MulAction.fixedBy Q d) = 1 := by
    intro d hd
    have he : (MulAction.fixedBy Q d) ≃ {x : Q // (d : G) * (x : G) * (d : G)⁻¹ = (x : G)} :=
      Equiv.subtypeEquivRight (fun x => by
        rw [MulAction.mem_fixedBy]
        exact ⟨fun hx => congrArg Subtype.val hx, fun hx => Subtype.ext hx⟩)
    rw [Fintype.card_congr he, Fintype.card_eq_one_iff]
    refine ⟨⟨1, by simp⟩, fun y => ?_⟩
    refine Subtype.ext (Subtype.ext ?_)
    exact hfpf (d : G) d.2 (fun h1 => hd (Subtype.ext h1)) (y : G) y.1.2 y.2
  -- the sum of the numbers of fixed points
  have hsum : (∑ d : twoPoint H t, Fintype.card (MulAction.fixedBy Q d))
      = Nat.card Q + (Nat.card (twoPoint H t) - 1) := by
    have h2 : (∑ d ∈ Finset.univ.erase (1 : twoPoint H t),
        Fintype.card (MulAction.fixedBy Q d)) = Nat.card (twoPoint H t) - 1 := by
      trans (∑ d ∈ Finset.univ.erase (1 : twoPoint H t), (1 : ℕ))
      · exact Finset.sum_congr rfl (fun d hd => hfixne d (Finset.mem_erase.mp hd).1)
      · rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ 1), Finset.card_univ,
          ← Nat.card_eq_fintype_card]
        simp
    rw [← Finset.add_sum_erase Finset.univ
      (fun d : twoPoint H t => Fintype.card (MulAction.fixedBy Q d)) (Finset.mem_univ 1),
      hfix1, h2]
  -- Burnside's lemma
  have hB := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group (twoPoint H t) Q
  have hmain : Nat.card Q + (Nat.card (twoPoint H t) - 1)
      = Fintype.card (Quotient (MulAction.orbitRel (twoPoint H t) Q)) * Nat.card (twoPoint H t) := by
    rw [← hsum, hB, Nat.card_eq_fintype_card]
  have hDpos : 1 ≤ Nat.card (twoPoint H t) := by
    haveI : Nonempty (twoPoint H t) := ⟨⟨1, (twoPoint H t).one_mem⟩⟩
    exact Nat.card_pos
  have hQpos : 1 ≤ Nat.card Q := by
    haveI : Nonempty Q := ⟨⟨1, Q.one_mem⟩⟩
    exact Nat.card_pos
  have h1 : Nat.card Q - 1
      = Fintype.card (Quotient (MulAction.orbitRel (twoPoint H t) Q)) * Nat.card (twoPoint H t)
        - Nat.card (twoPoint H t) := by omega
  have h2 : Fintype.card (Quotient (MulAction.orbitRel (twoPoint H t) Q))
        * Nat.card (twoPoint H t) - Nat.card (twoPoint H t)
      = (Fintype.card (Quotient (MulAction.orbitRel (twoPoint H t) Q)) - 1)
        * Nat.card (twoPoint H t) := by
    rw [Nat.sub_mul, one_mul]
  rw [h1, h2]
  exact dvd_mul_left _ _

theorem coprime_card {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) (hz : Submission.Blueprint.IsZassenhaus H) :
    Nat.Coprime (Nat.card (Submission.Blueprint.twoPoint H t)) (Nat.card Q) := by
  have hdiv : Nat.card (twoPoint H t) ∣ Nat.card Q - 1 := card_twoPoint_dvd_card_Q_sub_one h hz
  have hQpos : 1 ≤ Nat.card Q := by
    haveI : Nonempty Q := ⟨⟨1, Q.one_mem⟩⟩
    exact Nat.card_pos
  rw [Nat.coprime_iff_gcd_eq_one]
  have hg : Nat.gcd (Nat.card (twoPoint H t)) (Nat.card Q)
      ∣ Nat.card Q - (Nat.card Q - 1) :=
    Nat.dvd_sub (Nat.gcd_dvd_right _ _) ((Nat.gcd_dvd_left _ _).trans hdiv)
  have hsub : Nat.card Q - (Nat.card Q - 1) = 1 := by omega
  rw [hsub] at hg
  exact Nat.dvd_one.mp hg

end Work.ZassenhausTwoGroup
