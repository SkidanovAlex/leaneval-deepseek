import Mathlib
import Submission.Work.ThmG.Defs
import Submission.Work.ThmG.nilpotent_two_odd_split
import Submission.Work.FeitSibley.CharQ.scriptS_vanish

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.FeitSibley.ThmGBridge

theorem vanishesOffProp_of_fsdata {G : Type} [Group G] [Fintype G] (H Q : Subgroup G) (t : G)
    (hsplit : Work.ThmG.RankOneHyp G H Q t)
    (hQT : ∀ x : G, x ∉ H → Q ⊓ Submission.Blueprint.conj x Q = ⊥)
    (hDodd : Odd (Nat.card (Submission.Blueprint.twoPoint H t)))
    (hQnil : Group.IsNilpotent Q) (hQ1ne : Work.ThmG.oddPart Q ≠ ⊥)
    (hfpf : ∀ d ∈ Submission.Blueprint.twoPoint H t, d ≠ 1 →
      ∀ x ∈ Work.ThmG.oddPart Q, d * x * d⁻¹ = x → x = 1)
    (hcop : Nat.Coprime (Nat.card (Submission.Blueprint.twoPoint H t)) (Nat.card Q)) :
    ∀ chi ∈ Submission.Blueprint.excludingKernel H (Work.ThmG.oddPart Q),
      ∀ h : H, (h : G) ∉ Q → chi h = 0 := by
  classical
  intro chi hchi h hhQ
  -- the split rank-one datum underlying `hsplit`
  have hsplit' : Submission.Blueprint.IsSplitRankOne H Q t := hsplit.2.2.1
  -- the `2`-part / odd-part splitting `Q = O_2(Q) × O_{2'}(Q)` of the nilpotent `Q`
  obtain ⟨hsupQ, hinfQ, hcommQ, hcopS, hoddQ₁, hnilS, _hcardQ, _hQ₁ne⟩ :=
    Work.ThmG.nilpotent_two_odd_split Q hQnil
  -- `O_{2'}(Q)` is not a 2-group
  have hnot2Q₁ : ¬ IsPGroup 2 (Work.ThmG.oddPart Q) := by
    intro h2
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h2
    have hn0 : n = 0 := by
      by_contra hn0
      have hdvd : 2 ∣ 2 ^ n := dvd_pow_self 2 hn0
      rw [← hn] at hdvd
      have hmod : Nat.card ↥(Work.ThmG.oddPart Q) % 2 = 0 :=
        Nat.dvd_iff_mod_eq_zero.mp hdvd
      have hodd : Nat.card ↥(Work.ThmG.oddPart Q) % 2 = 1 := Nat.odd_iff.mp hoddQ₁
      omega
    rw [hn0, pow_zero] at hn
    exact hQ1ne (Subgroup.card_eq_one.mp hn)
  -- assemble the Feit–Sibley data
  let hFS : Work.FeitSibley.FSData G :=
    { H := H, Q := Q, D := Submission.Blueprint.twoPoint H t
      S := Work.ThmG.twoPart Q, Q1 := Work.ThmG.oddPart Q
      H_ne_top := hsplit'.stronglyEmbedded.1
      Q_le_H := hsplit'.le
      Q_normal_in_H := hsplit'.normal
      D_le_H := inf_le_left
      Q_inf_D := hsplit'.inf_eq
      Q_sup_D := hsplit'.sup_eq
      coprime_D_Q := hcop
      Q_TI := hQT
      S_sup_Q1 := hsupQ
      S_inf_Q1 := hinfQ
      commute := hcommQ
      coprime_S_Q1 := hcopS
      S_nilpotent := hnilS
      D_fpf_Q1 := hfpf
      Q1_not_two := hnot2Q₁
      D_odd := hDodd }
  -- the projections of the structure literal reduce to `H`, `Q`, `O_{2'}(Q)`
  have hchi' : chi ∈ Work.FeitSibley.scriptS hFS.H hFS.Q1 := hchi
  have hhQ' : (h : G) ∉ hFS.Q := hhQ
  exact Work.FeitSibley.CharQ.scriptS_vanish hFS hchi' hhQ'

end Work.FeitSibley.ThmGBridge
