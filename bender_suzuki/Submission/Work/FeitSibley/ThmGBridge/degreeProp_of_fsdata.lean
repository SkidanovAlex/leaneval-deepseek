import Mathlib
import Submission.Work.ThmG.Defs
import Submission.Work.ThmG.nilpotent_two_odd_split
import Submission.Work.FeitSibley.CharQ.degree_D_scriptS
import Submission.Work.CharCore.exists_irr_of_monoidHom
import Submission.Work.ThmF.ChV12.exists_linear

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmG.DegreeProp` from the Feit–Sibley hypotheses

Peterfalvi II, Appendice XII (3)–(4): in the split rank-one situation with `Q` a T.I.
subgroup, `D = H ∩ Hᵗ` of odd order, `Q` nilpotent, `D` fixed-point-free on `Q₁ = O_{2'}(Q)`
and `(|D|,|Q|) = 1`, the set `𝒮 = {χ ∈ Irr H | Q₁ ⊄ ker χ}` contains a character of degree
`|D|` and the degree of every member of `𝒮` is a multiple of it.

The Feit–Sibley input (`Work.FeitSibley.FSData` + `Work.FeitSibley.CharQ.degree_D_scriptS`)
needs, besides the structural data, one non-trivial linear character of `Q₁`.  That is supplied
here by `Work.ThmF.ChV12.exists_monoidHom_units_ne_one` (`Q₁` is nilpotent as a subgroup of
the nilpotent `Q`, hence solvable, and `Q₁ ≠ 1` by hypothesis) together with the dictionary
between monoid homomorphisms `A →* ℂˣ` and irreducible characters of degree one
(`Work.CharCore.exists_irr_of_monoidHom`).
-/

namespace Work.FeitSibley.ThmGBridge

/-- A nontrivial finite solvable group has a non-principal irreducible character of degree one.
This is the `Work.CharCore.Irr`-form of `Work.ThmF.ChV12.exists_monoidHom_units_ne_one`. -/
theorem exists_irr_deg_one_ne_trivial {A : Type} [Group A] [Fintype A] [Group.IsSolvable A]
    (hnt : Nontrivial A) :
    ∃ χ ∈ Work.CharCore.Irr A, χ 1 = 1 ∧ χ ≠ (fun _ : A => (1 : ℂ)) := by
  obtain ⟨φ, hφne⟩ := Work.ThmF.ChV12.exists_monoidHom_units_ne_one hnt
  obtain ⟨χ, hχIrr, hχeq⟩ := Work.CharCore.exists_irr_of_monoidHom φ
  refine ⟨χ, hχIrr, ?_, ?_⟩
  · rw [hχeq 1]; simp
  · intro hcon
    apply hφne
    ext g
    rw [← hχeq g, congrFun hcon g]
    simp

/-- `O_{2'}(Q)` is nilpotent whenever `Q` is: it is a subgroup of `Q`. -/
theorem isNilpotent_oddPart {G : Type} [Group G] (Q : Subgroup G) [Group.IsNilpotent Q] :
    Group.IsNilpotent ↥(Work.ThmG.oddPart Q) :=
  (Group.isNilpotent_congr
      (Subgroup.subgroupOfEquivOfLe (Work.ThmG.oddPart_le Q))).mp
    (Subgroup.isNilpotent ((Work.ThmG.oddPart Q).subgroupOf Q))

theorem degreeProp_of_fsdata {G : Type} [Group G] [Fintype G] (H Q : Subgroup G) (t : G)
    (hsplit : Work.ThmG.RankOneHyp G H Q t)
    (hQT : ∀ x : G, x ∉ H → Q ⊓ Submission.Blueprint.conj x Q = ⊥)
    (hDodd : Odd (Nat.card (Submission.Blueprint.twoPoint H t)))
    (hQnil : Group.IsNilpotent Q) (hQ1ne : Work.ThmG.oddPart Q ≠ ⊥)
    (hfpf : ∀ d ∈ Submission.Blueprint.twoPoint H t, d ≠ 1 →
      ∀ x ∈ Work.ThmG.oddPart Q, d * x * d⁻¹ = x → x = 1)
    (hcop : Nat.Coprime (Nat.card (Submission.Blueprint.twoPoint H t)) (Nat.card Q)) :
    ∃ chi ∈ Submission.Blueprint.excludingKernel H (Work.ThmG.oddPart Q),
      chi 1 = (Nat.card (Submission.Blueprint.twoPoint H t) : ℂ) ∧
      ∀ psi ∈ Submission.Blueprint.excludingKernel H (Work.ThmG.oddPart Q),
        ∃ a : ℕ, psi 1 = (a : ℂ) * chi 1 := by
  classical
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
  -- `Q₁ = O_{2'}(Q)` is a nontrivial nilpotent (hence solvable) group
  haveI hQnil' : Group.IsNilpotent Q := hQnil
  haveI hQ1nil : Group.IsNilpotent ↥(Work.ThmG.oddPart Q) := isNilpotent_oddPart Q
  haveI hQ1solv : Group.IsSolvable ↥(Work.ThmG.oddPart Q) := inferInstance
  haveI hQ1nt : Nontrivial ↥(Work.ThmG.oddPart Q) :=
    (Subgroup.nontrivial_iff_ne_bot (Work.ThmG.oddPart Q)).mpr hQ1ne
  -- hence it has a non-principal linear character
  have hlin : ∃ theta ∈ Work.CharCore.Irr ↥hFS.Q1,
      theta 1 = 1 ∧ theta ≠ (fun _ : ↥hFS.Q1 => 1) :=
    exists_irr_deg_one_ne_trivial hQ1nt
  -- Feit–Sibley, Appendice XII (3)–(4)
  obtain ⟨chi, hchi, hchi1, hchi2⟩ := Work.FeitSibley.CharQ.degree_D_scriptS hFS hlin
  refine ⟨chi, hchi, hchi1, ?_⟩
  intro psi hpsi
  obtain ⟨a, ha⟩ := hchi2 psi hpsi
  exact ⟨a, by rw [ha, hchi1]⟩

end Work.FeitSibley.ThmGBridge
