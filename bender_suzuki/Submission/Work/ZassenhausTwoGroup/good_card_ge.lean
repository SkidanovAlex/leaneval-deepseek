import Mathlib
import Submission.Work.ZassenhausTwoGroup.FeitThm2
import Submission.Work.ZassenhausTwoGroup.bf35_chars
import Submission.Work.ZassenhausTwoGroup.hchi_orb
import Submission.Work.ZassenhausTwoGroup.etaStar_data
import Submission.Work.ZassenhausTwoGroup.card_classes_meeting_Q
import Submission.Work.ZassenhausTwoGroup.card_H_classes_eq_card_induced
import Submission.Work.CharCore.Main
import Submission.Work.Induction.All

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false

open Classical

namespace Work.ZassenhausTwoGroup

/-- Conjugate elements have the same order. -/
private lemma orderOf_eq_of_isConj {G : Type*} [Group G] {x y : G} (h : IsConj x y) :
    orderOf x = orderOf y := by
  obtain ⟨g, hg⟩ := isConj_iff.mp h
  rw [← hg]
  refine SemiconjBy.orderOf_eq g ?_
  rw [SemiconjBy]
  simp [mul_assoc]

/-- The non-trivial irreducible characters of `Q`, as a finset. -/
private noncomputable abbrev IrrNT {G : Type*} [Group G] (Q : Subgroup G) [Fintype ↥Q] : Finset (↥Q → ℂ) :=
  (Work.CharCore.Irr ↥Q).filter (fun ζ => ζ ≠ 1)

/-- The image of the induction map `ζ ↦ Ind_Q^G ζ` on the non-trivial irreducible characters
of `Q`.  Its cardinality is Feit's `N`. -/
private noncomputable abbrev IndImage {G : Type*} [Group G] [Fintype G] (Q : Subgroup G) [Fintype ↥Q] :
    Finset (G → ℂ) :=
  (IrrNT Q).image (fun ζ => Work.Induction.indFun Q ζ)

/-- **The induction map is not constant on the non-trivial irreducible characters of `Q`.**
Equivalently, `Irr Q ∖ {1}` is not a single `H`-orbit; this is where `Q` not being a `2`-group
(and `|Q|` being even) enters: if all of `Q ∖ 1` were conjugate in `G`, all its elements would
have the same order, and Cauchy's theorem would make `Q` a `2`-group. -/
private theorem two_le_card_IndImage {G : Type} [Group G] [Fintype G] [IsSimpleGroup G]
    {H Q : Subgroup G} [Fintype ↥Q] {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) (hZ : Submission.Blueprint.IsZassenhaus H)
    (hQ2 : ¬ IsPGroup 2 Q) :
    2 ≤ (IndImage (G := G) Q).card := by
  classical
  -- ## A `2`-element and an element of non-`2`-power order in `Q`
  have hEven : Even (Nat.card ↥Q) := even_card_Q h
  have h2dvd : 2 ∣ Fintype.card ↥Q := by
    rw [Fintype.card_eq_nat_card]
    exact even_iff_two_dvd.mp hEven
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card (G := ↥Q) 2 h2dvd
  have hQ2' : ¬ IsPGroup 2 ↥Q := hQ2
  rw [IsPGroup.iff_orderOf] at hQ2'
  push_neg at hQ2'
  obtain ⟨g, hg⟩ := hQ2'
  have hg2 : orderOf g ≠ 2 := by
    have := hg 1
    simpa using this
  have hu1 : u ≠ 1 := by
    intro hc
    rw [hc, orderOf_one] at hu
    omega
  -- ## The two `G`-classes
  have huG1 : (u : G) ≠ 1 := by
    simpa using (Subtype.coe_ne_coe (a := u) (b := (1 : ↥Q))).mpr hu1
  have hg1ord : orderOf g ≠ 1 := by
    have := hg 0
    simpa using this
  have hgG1' : (g : G) ≠ 1 := by
    intro hc
    have hge : orderOf g = 1 := by
      rw [← Subgroup.orderOf_coe g, hc]
      exact orderOf_one
    exact hg1ord hge
  set c₁ : ClassesMeetingQ Q :=
    ⟨ConjClasses.mk (u : G), ⟨(u : G), ConjClasses.mem_carrier_mk, u.2, huG1⟩⟩ with hc₁
  set c₂ : ClassesMeetingQ Q :=
    ⟨ConjClasses.mk (g : G), ⟨(g : G), ConjClasses.mem_carrier_mk, g.2, hgG1'⟩⟩ with hc₂
  have hne_cls : c₁ ≠ c₂ := by
    intro hconv
    have hmk : ConjClasses.mk (u : G) = ConjClasses.mk (g : G) := by
      simpa [hc₁, hc₂] using congrArg Subtype.val hconv
    have hconj : IsConj (u : G) (g : G) := ConjClasses.mk_eq_mk_iff_isConj.mp hmk
    have hord := orderOf_eq_of_isConj hconj
    rw [Subgroup.orderOf_coe u, Subgroup.orderOf_coe g, hu] at hord
    exact hg2 hord.symm
  -- ## `2 ≤ #classes of G meeting Q ∖ 1`
  have hA2 : 2 ≤ Nat.card (ClassesMeetingQ Q) := by
    have h1 : 1 < Fintype.card (ClassesMeetingQ Q) :=
      Fintype.one_lt_card_iff.mpr ⟨c₁, c₂, hne_cls⟩
    rw [Fintype.card_eq_nat_card] at h1
    omega
  -- ## `N = #classes of G meeting Q ∖ 1`
  have hAN : Nat.card (ClassesMeetingQ Q) = (IndImage (G := G) Q).card := by
    rw [card_classes_meeting_Q H Q t h hZ, card_H_classes_eq_card_induced H Q t h hZ]
    rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]
  rw [hAN] at hA2
  exact hA2

/-- **Fibre separation.**  For every non-trivial irreducible `ζ` of `Q` there is another
non-trivial irreducible `η` inducing a *different* character of `G`. -/
private theorem exists_indFun_ne {G : Type} [Group G] [Fintype G] [IsSimpleGroup G]
    {H Q : Subgroup G} [Fintype ↥Q] {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) (hZ : Submission.Blueprint.IsZassenhaus H)
    (hQ2 : ¬ IsPGroup 2 Q) :
    ∀ ζ ∈ Work.CharCore.Irr ↥Q, ζ ≠ 1 →
      ∃ η ∈ Work.CharCore.Irr ↥Q, η ≠ 1 ∧
        Work.Induction.indFun Q η ≠ Work.Induction.indFun Q ζ := by
  classical
  intro ζ hζ hζ1
  have hN : 2 ≤ (IndImage (G := G) Q).card := two_le_card_IndImage h hZ hQ2
  by_contra hcon
  push_neg at hcon
  have hsub : IndImage (G := G) Q ⊆ {Work.Induction.indFun Q ζ} := by
    intro y hy
    rw [Finset.mem_singleton]
    obtain ⟨η, hη, rfl⟩ := Finset.mem_image.mp hy
    exact hcon η (Finset.mem_filter.mp hη).1 (Finset.mem_filter.mp hη).2
  have hle : (IndImage (G := G) Q).card ≤ 1 := by
    calc (IndImage (G := G) Q).card
        ≤ ({Work.Induction.indFun Q ζ} : Finset (G → ℂ)).card := Finset.card_le_card hsub
      _ = 1 := Finset.card_singleton _
  omega

theorem good_card_ge {G : Type} [Group G] [Fintype G] [IsSimpleGroup G] (H Q : Subgroup G)
    [Fintype ↥Q] (t : G)
    (h : Submission.Blueprint.IsSplitRankOne H Q t) (hZ : Submission.Blueprint.IsZassenhaus H)
    (hQ2 : ¬ IsPGroup 2 Q)
    (hne : Nat.card (Submission.Blueprint.twoPoint H t) ≠ Nat.card ↥Q - 1)
    {χ₀ : (↥Q → ℂ) → G → ℂ} {ε : ℤ} {c : ℤ}
    (hχ₀irr : ∀ ζ ∈ Work.CharCore.Irr ↥Q, ζ ≠ 1 → χ₀ ζ ∈ Work.CharCore.Irr G)
    (hdiff : ∀ ζ ∈ Work.CharCore.Irr ↥Q, ζ ≠ 1 → ∀ ζ' ∈ Work.CharCore.Irr ↥Q, ζ' ≠ 1 →
      Work.Induction.indFun Q ζ ≠ Work.Induction.indFun Q ζ' → ∀ g : G,
        (ζ' 1) * Work.Induction.indFun Q ζ g - (ζ 1) * Work.Induction.indFun Q ζ' g
          = (ε : ℂ) * ((ζ' 1) * χ₀ ζ g - (ζ 1) * χ₀ ζ' g))
    (hε : ε = 1 ∨ ε = -1)
    (hvan : ∀ ζ ∈ Work.CharCore.Irr ↥Q, ζ ≠ 1 → ∀ ζ' ∈ Work.CharCore.Irr ↥Q, ζ' ≠ 1 →
      Work.Induction.indFun Q ζ ≠ Work.Induction.indFun Q ζ' → ∀ g : G,
        (¬ ∃ x : G, x * g * x⁻¹ ∈ Q ∧ x * g * x⁻¹ ≠ 1) →
          (ζ' 1) * χ₀ ζ g - (ζ 1) * χ₀ ζ' g = 0)
    (hval : ∀ ζ ∈ Work.CharCore.Irr ↥Q, ζ ≠ 1 → ∀ y : G, y ∈ Q → y ≠ 1 →
      χ₀ ζ y = (ε : ℂ) * Work.Induction.indFun Q ζ y + (ζ 1) * (c : ℂ)) :
    Nat.card (Submission.Blueprint.twoPoint H t) ≤
      ((Work.CharCore.Irr G).filter (fun ψ => ψ ≠ (fun _ : G => (1 : ℂ)) ∧
        ∀ κ ∈ Work.CharCore.Irr ↥Q, κ ≠ 1 → ψ ≠ χ₀ κ)).card := by
  classical
  -- ## Basic positivity facts
  have hε0 : (ε : ℂ) ≠ 0 := by rcases hε with hh | hh <;> simp [hh]
  have hQindex : (Q.index : ℂ) ≠ 0 := by
    exact_mod_cast Subgroup.index_ne_zero_of_finite (H := Q)
  -- degree of a non-trivial irreducible of `Q` is non-zero
  have hdegζ : ∀ ζ ∈ Work.CharCore.Irr ↥Q, (ζ : ↥Q → ℂ) 1 ≠ 0 := by
    intro ζ hζ
    rw [Work.CharCore.irrDeg_spec hζ]
    exact_mod_cast Work.CharCore.irrDeg_ne_zero hζ
  -- ## This pair induces the same character iff the degrees agree
  have hdegEq : ∀ ζ ∈ Work.CharCore.Irr ↥Q, ∀ ζ' ∈ Work.CharCore.Irr ↥Q,
      Work.Induction.indFun Q ζ = Work.Induction.indFun Q ζ' → ζ 1 = ζ' 1 := by
    intro ζ hζ ζ' hζ' hII
    have h1 : Work.Induction.indFun Q ζ 1 = Work.Induction.indFun Q ζ' 1 := by rw [hII]
    rw [Work.Induction.indFun_apply_one, Work.Induction.indFun_apply_one] at h1
    exact mul_left_cancel₀ hQindex h1
  -- ## Constancy of `χ₀` on the fibres of the induction map
  have hχorb : ∀ ζ ∈ Work.CharCore.Irr ↥Q, ζ ≠ 1 → ∀ ζ' ∈ Work.CharCore.Irr ↥Q, ζ' ≠ 1 →
      Work.Induction.indFun Q ζ = Work.Induction.indFun Q ζ' → χ₀ ζ = χ₀ ζ' := by
    intro ζ hζ hζ1 ζ' hζ' hζ'1 hIeq
    obtain ⟨η, hη, hη1, hηne⟩ := exists_indFun_ne h hZ hQ2 ζ hζ hζ1
    have hdeg : (ζ : ↥Q → ℂ) 1 = ζ' 1 := hdegEq ζ hζ ζ' hζ' hIeq
    funext gp
    have h1 := hdiff ζ hζ hζ1 η hη hη1 hηne.symm gp
    have h2 := hdiff ζ' hζ' hζ'1 η hη hη1 (by rw [← hIeq]; exact hηne.symm) gp
    rw [hIeq, hdeg] at h1
    have hcancel : (ε : ℂ) * ((η 1) * χ₀ ζ gp - (ζ' 1) * χ₀ η gp)
        = (ε : ℂ) * ((η 1) * χ₀ ζ' gp - (ζ' 1) * χ₀ η gp) := h1.symm.trans h2
    have hB : (η 1) * χ₀ ζ gp - (ζ' 1) * χ₀ η gp
        = (η 1) * χ₀ ζ' gp - (ζ' 1) * χ₀ η gp := mul_left_cancel₀ hε0 hcancel
    have hη1' : (η : ↥Q → ℂ) 1 ≠ 0 := hdegζ η hη
    have : (η 1) * χ₀ ζ gp = (η 1) * χ₀ ζ' gp := by linear_combination hB
    exact mul_left_cancel₀ hη1' this
  -- ## Injectivity of `χ₀` across the fibres
  have hχrel : ∀ ζ ∈ Work.CharCore.Irr ↥Q, ζ ≠ 1 → ∀ ζ' ∈ Work.CharCore.Irr ↥Q, ζ' ≠ 1 →
      Work.Induction.indFun Q ζ ≠ Work.Induction.indFun Q ζ' → χ₀ ζ ≠ χ₀ ζ' := by
    intro ζ hζ hζ1 ζ' hζ' hζ'1 hNI hχeq
    have hX1 : χ₀ ζ 1 ≠ 0 := by
      rw [Work.CharCore.irrDeg_spec (hχ₀irr ζ hζ hζ1)]
      exact_mod_cast Work.CharCore.irrDeg_ne_zero (hχ₀irr ζ hζ hζ1)
    have hz1 : (ζ : ↥Q → ℂ) 1 ≠ 0 := hdegζ ζ hζ
    -- the value relation at `1` kills the left hand side
    have hg1 := hdiff ζ hζ hζ1 ζ' hζ' hζ'1 hNI 1
    rw [Work.Induction.indFun_apply_one, Work.Induction.indFun_apply_one] at hg1
    have hz0 : (ζ' 1 - ζ 1) * χ₀ ζ 1 = 0 := by
      have h0 : (ζ' 1) * ((Q.index : ℂ) * ζ 1) - (ζ 1) * ((Q.index : ℂ) * ζ' 1) = 0 := by ring
      rw [h0] at hg1
      have hX : (ζ' 1) * χ₀ ζ 1 - (ζ 1) * χ₀ ζ' 1 = 0 := by
        rcases mul_eq_zero.mp hg1.symm with hh | hh
        · exact absurd hh hε0
        · exact hh
      rw [← hχeq] at hX
      linear_combination hX
    have hz : ζ' 1 = ζ 1 := sub_eq_zero.mp ((mul_eq_zero.mp hz0).resolve_right hX1)
    refine hNI (funext fun gp => ?_)
    have hgg := hdiff ζ hζ hζ1 ζ' hζ' hζ'1 hNI gp
    have hL : (ζ' 1) * Work.Induction.indFun Q ζ gp
        - (ζ 1) * Work.Induction.indFun Q ζ' gp = 0 := by
      rw [hgg, hχeq, hz]; ring
    have hfac : ζ 1 * (Work.Induction.indFun Q ζ gp - Work.Induction.indFun Q ζ' gp) = 0 := by
      rw [hz] at hL; linear_combination hL
    exact sub_eq_zero.mp ((mul_eq_zero.mp hfac).resolve_left hz1)
  exact bf35_chars H Q t h hZ hQ2 χ₀ hχ₀irr hχrel hχorb

end Work.ZassenhausTwoGroup
