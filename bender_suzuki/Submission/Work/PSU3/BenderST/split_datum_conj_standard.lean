import Mathlib
import Submission.Work.PSU3.BenderST.transport
import Submission.Work.PSU3.BenderST.Defs
import Submission.Work.PSU3.BST.psu3_wTrans
import Submission.Work.PSU3.BST.card_twoPoint_of_twoTransitive
import Submission.Work.Models.Abstract.exists_conj_eq
import Submission.Work.Models.Abstract.twoPoint_eq
import Submission.Work.Models.Abstract.involutions_subset_U
import Submission.Work.Models.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

namespace Work.PSU3.BenderST

/-- **Every split rank-one datum in a group carrying a Bender pair is conjugate to the standard
datum of that pair.**  This is the reduction that makes `BenderSTProp` a statement about the
three *models* only.

Route.  `Work.Models.Abstract.exists_conj_eq` gives `g₀` with `B = conj g₀ P.B`; conjugating
the whole datum by `MulAut.conj g₀⁻¹` (use `Work.PSU3.BenderST.isSplitRankOne_map`) we may
assume `B = P.B`.  Then
* `U = P.U`: `|twoPoint P.B w| * |P.U| = |P.B|` by
  `Work.PSU3.BST.card_twoPoint_of_twoTransitive` (`P.isMultiplyPretransitive_two`, `P.hindex`,
  `P.hwB`) and `|twoPoint P.B w| * |U| = |P.B|` by
  `Subgroup.card_sup_of_inf_eq_bot_of_le_normalizer` applied to `(twoPoint P.B w, U)`
  (use `h.inf_eq`, `h.sup_eq`, `h.normal` and `P.B ≤ N(U)`); hence `|U| = |P.U|`, so `U` is a
  normal Sylow `2`-subgroup and equals `P.U` (the existing
  `Work.PSU3.BenderST.datum_conj_eq` already contains this argument);
* `w` is conjugate to `P.w` by an element of `P.B`: apply
  `Work.PSU3.BST.transitive_involutions_outside'` to the standard datum
  `(P.B, P.U, P.w)` (`Work.PSU3.BenderST.benderPair_isSplitRankOne` for the split structure)
  and `t' = w`.

See `Submission/Work/PSU3/BenderST/ROUTE.md`. -/
theorem split_datum_conj_standard {G : Type} [Group G] [Finite G] (P : Submission.BenderPair G)
    (hstd : Submission.Blueprint.IsSplitRankOne P.B P.U P.w)
    {B U : Subgroup G} {w : G} (h : Submission.Blueprint.IsSplitRankOne B U w) :
    ∃ g : G, Submission.Blueprint.conj g B = P.B ∧ Submission.Blueprint.conj g U = P.U ∧
      MulAut.conj g w = P.w := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- ## Step 0.  `Work.Models.Abstract.exists_conj_eq` gives `B = conj g₀ P.B`; conjugating
  -- the whole datum by `g₀⁻¹` (which preserves split rank-one data, `isSplitRankOne_map`)
  -- reduces us to the case `B = P.B`.
  obtain ⟨g₀, hg₀⟩ := Work.Models.Abstract.exists_conj_eq P h.stronglyEmbedded
  have h₁ := isSplitRankOne_map (MulAut.conj g₀⁻¹) h
  have hB₁ : B.map (MulAut.conj g₀⁻¹).toMonoidHom = P.B := by
    rw [show B.map (MulAut.conj g₀⁻¹).toMonoidHom
        = Submission.Blueprint.conj g₀⁻¹ B from rfl, hg₀, Work.Models.conj_inv_conj]
  rw [hB₁] at h₁
  -- From now on `h₁ : IsSplitRankOne P.B (U^g₀⁻¹) (w^g₀⁻¹)`.
  set Q : Subgroup G := U.map (MulAut.conj g₀⁻¹).toMonoidHom with hQ
  set t : G := (MulAut.conj g₀⁻¹) w with ht
  -- ## Step 1.  `t ∉ P.B` exhibits `D = twoPoint P.B t` as a conjugate of the torus `P.T`.
  have htB : t ∉ P.B := h₁.not_mem
  obtain ⟨b, _hb, c, _hc, _hbc, hDc⟩ := Work.Models.Abstract.twoPoint_eq P htB
  have hcardD : Nat.card ↥(Submission.Blueprint.twoPoint P.B t) = Nat.card ↥P.T := by
    rw [hDc]
    exact Subgroup.card_map_of_injective (MulEquiv.injective _)
  -- ## Step 2.  `P.B = Q ⊔ D` with `Q ⊓ D = ⊥` and `D ≤ N(Q)` gives `|P.B| = |Q| · |D|`.
  have hcardBQ : Nat.card ↥P.B =
      Nat.card ↥Q * Nat.card ↥(Submission.Blueprint.twoPoint P.B t) := by
    conv_lhs => rw [← h₁.sup_eq]
    exact Commons.GroupTheory.Subgroup.card_sup_of_inf_eq_bot_of_le_normalizer Q _
      (le_trans inf_le_left h₁.normal) h₁.inf_eq
  -- ## Step 3.  Comparing with `|P.B| = |P.U| · |P.T|` gives `|Q| = |P.U|`.
  have hcardQ : Nat.card ↥Q = Nat.card ↥P.U := by
    have hpos : 0 < Nat.card ↥P.T := by
      haveI : Nonempty ↥P.T := ⟨1⟩
      exact Nat.card_pos
    refine Nat.mul_right_cancel hpos ?_
    rw [← hcardD, ← hcardBQ, P.card_eq_card_U_mul_card_T, hcardD]
  -- ## Step 4.  `P.U ≤ Q`: `P.B ⧸ Q` has odd order `|P.T|` while `P.U` is a 2-group.
  have hQnorm : (Q.subgroupOf P.B).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h₁.le).mpr h₁.normal
  have hidxQ : (Q.subgroupOf P.B).index = Nat.card ↥P.T := by
    have hcardQg : Nat.card ↥(Q.subgroupOf P.B) = Nat.card ↥Q :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe h₁.le).toEquiv
    have hpos : 0 < Nat.card ↥Q := by
      haveI : Nonempty ↥Q := ⟨1⟩
      exact Nat.card_pos
    refine Nat.mul_right_cancel hpos ?_
    calc (Q.subgroupOf P.B).index * Nat.card ↥Q
        = (Q.subgroupOf P.B).index * Nat.card ↥(Q.subgroupOf P.B) := by rw [hcardQg]
      _ = Nat.card ↥P.B := Subgroup.index_mul_card _
      _ = Nat.card ↥Q * Nat.card ↥(Submission.Blueprint.twoPoint P.B t) := hcardBQ
      _ = Nat.card ↥P.T * Nat.card ↥Q := by rw [hcardD, Nat.mul_comm]
  have hoddQ : Odd (Nat.card (↥P.B ⧸ Q.subgroupOf P.B)) := by
    rw [← Subgroup.index_eq_card, hidxQ]
    exact P.hoddT
  obtain ⟨k, hk⟩ := P.hU2.exists_card_eq
  have hcop : Nat.Coprime (Nat.card ↥P.U) (Nat.card (↥P.B ⧸ Q.subgroupOf P.B)) := by
    rw [hk]
    exact Nat.Coprime.pow_left k ((Nat.coprime_two_right.mpr hoddQ).symm)
  haveI := hQnorm
  have hUleQ : P.U ≤ Q := by
    intro u hu
    let φ : ↥P.U →* (↥P.B ⧸ Q.subgroupOf P.B) :=
      (QuotientGroup.mk' (Q.subgroupOf P.B)).comp (Subgroup.inclusion P.U_le_B)
    have h1 : orderOf (φ ⟨u, hu⟩) ∣ Nat.card ↥P.U :=
      (orderOf_map_dvd φ (⟨u, hu⟩ : ↥P.U)).trans
        (orderOf_dvd_natCard (⟨u, hu⟩ : ↥P.U))
    have h2 : orderOf (φ ⟨u, hu⟩) ∣ Nat.card (↥P.B ⧸ Q.subgroupOf P.B) :=
      orderOf_dvd_natCard (φ ⟨u, hu⟩)
    have hone : orderOf (φ ⟨u, hu⟩) = 1 :=
      (Nat.Coprime.coprime_dvd_left h1 hcop).eq_one_of_dvd h2
    have hmem : (Subgroup.inclusion P.U_le_B ⟨u, hu⟩ : ↥P.B) ∈ Q.subgroupOf P.B := by
      have hker : (Subgroup.inclusion P.U_le_B ⟨u, hu⟩ : ↥P.B) ∈
          (QuotientGroup.mk' (Q.subgroupOf P.B)).ker := by
        rw [MonoidHom.mem_ker]
        exact orderOf_eq_one_iff.mp hone
      rwa [QuotientGroup.ker_mk'] at hker
    exact Subgroup.mem_subgroupOf.mp hmem
  -- ## Step 5.  `P.U ≤ Q` and `|Q| = |P.U|` force `Q = P.U`.
  have hQU : Q = P.U :=
    (Subgroup.eq_of_le_of_card_ge hUleQ (le_of_eq hcardQ)).symm
  have hQU' : U.map (MulAut.conj g₀⁻¹).toMonoidHom = P.U := hQ ▸ hQU
  -- ## Step 6.  `transitive_involutions_outside'` conjugates `t` to `P.w` by an element of
  -- `P.B` (no hypothesis that `P.w` inverts the torus is needed).
  obtain ⟨a, ha, haeq⟩ :=
    Work.PSU3.BST.transitive_involutions_outside' (H := P.B) (Q := P.U) (t := P.w) hstd
      h₁.invol h₁.not_mem
  -- ## Assembly.  `g = a⁻¹ * g₀⁻¹` works.
  refine ⟨a⁻¹ * g₀⁻¹, ?_, ?_, ?_⟩
  · rw [Work.Models.conj_mul, hg₀, Work.Models.conj_inv_conj]
    exact Work.Models.conj_self_of_mem_normalizer (H := P.B)
      (Subgroup.le_normalizer (P.B.inv_mem ha))
  · rw [Work.Models.conj_mul]
    rw [show Submission.Blueprint.conj g₀⁻¹ U
        = U.map (MulAut.conj g₀⁻¹).toMonoidHom from rfl, hQU']
    exact Work.Models.conj_self_of_mem_normalizer (H := P.U)
      (hstd.normal (P.B.inv_mem ha))
  · have h1 : MulAut.conj (a⁻¹ * g₀⁻¹) w = a⁻¹ * ((MulAut.conj g₀⁻¹) w) * a := by
      rw [MulAut.conj_apply, MulAut.conj_apply]
      group
    rw [h1, ← ht, haeq]
    group

end Work.PSU3.BenderST
