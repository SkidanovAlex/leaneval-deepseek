import Mathlib
import Submission.Work.CharCore.Main
import Submission.Work.Induction.All
import Submission.Work.ZassenhausTwoGroup.Defs
import Submission.Work.ZassenhausTwoGroup.FeitThm2
import Submission.Work.ZassenhausTwoGroup.zetaStar_norm
import Submission.Work.ZassenhausTwoGroup.etaStar_data
import Submission.Work.ZassenhausTwoGroup.chiXi_not_const
import Submission.Work.ZassenhausTwoGroup.chiXi_Xi0_inner
import Submission.Work.ZassenhausTwoGroup.chiGamma_inner
import Submission.Work.ZassenhausTwoGroup.chiXi_exceptionals

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Feit (24): the exceptional character has degree `|D|`

`Work.ZassenhausTwoGroup.chi1_degree_eq`: in the split rank-one Zassenhaus set-up with `Q` not a
`2`-group and `|D| ≠ |Q| - 1`, for every non-trivial *linear* irreducible character `ζ₁` of `Q`
there is an irreducible character of `G` of degree `|D| = |twoPoint H t|`.

This is Feit's display (24) (`χ₁(1) = q`) of *On a class of doubly transitive permutation groups*,
Illinois J. Math. **4** (1960).

The pieces it consumes (`Submission.Work.ZassenhausTwoGroup.chiXi_exceptionals`,
`...chiXi_Xi0_inner`, `...chiXi_not_const`) provide the exceptional constituent `χ_κ` of
`Ξ = Ind_Q^G ζ₁` together with `⟪χ_κ, Ξ₀⟫ = 0` (`Ξ₀ = Ind_Q^G 1_Q`), so that `Γ = Ξ - χ_κ` is a
character of norm `|D|` which is constant on `Q ∖ 1`; the two Frobenius-reciprocity identities
above then force the constant to vanish and give `χ_κ(1) = |D|`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open Classical
open Submission.Blueprint

namespace Work.ZassenhausTwoGroup

variable {G : Type} [Group G]

/-- `[G : Q] = (|Q|+1)|D|`. -/
private theorem Q_index_eq {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (h : IsSplitRankOne H Q t) :
    Q.index = (Nat.card ↥Q + 1) * Nat.card ↥(twoPoint H t) := by
  have hQpos : 0 < Nat.card ↥Q := Nat.card_pos
  have heq : Nat.card ↥Q * Q.index
      = Nat.card ↥Q * ((Nat.card ↥Q + 1) * Nat.card ↥(twoPoint H t)) := by
    rw [Subgroup.card_mul_index Q, ← Subgroup.card_mul_index H, card_H_eq h,
      Subgroup.index_eq_card H, card_quotient_eq h]
    ring
  exact Nat.eq_of_mul_eq_mul_left hQpos heq

/-- The sum of a non-trivial linear character over `Q` vanishes. -/
private theorem sum_zeta_eq_zero {G : Type} [Group G] [Fintype G] {Q : Subgroup G} [Fintype ↥Q]
    {ζ : ↥Q → ℂ} (hζ : ζ ∈ Work.CharCore.Irr ↥Q) (hζ1 : ζ ≠ 1) (hlin : ζ 1 = 1) :
    (∑ y : ↥Q, ζ y) = 0 := by
  obtain ⟨φ, hφ⟩ : ∃ φ : ↥Q →* ℂˣ, ∀ x : ↥Q, ζ x = (φ x : ℂ) := by
    refine (Work.CharCore.linear_char_iff_deg_one hζ).mp ?_
    have hspec := Work.CharCore.irrDeg_spec hζ
    have h1 : (Work.CharCore.irrDeg ζ : ℂ) = 1 := by rw [← hspec, hlin]
    exact_mod_cast h1
  have hφne : φ ≠ 1 := by
    intro hcon
    refine hζ1 (funext fun x => ?_)
    rw [hφ x, hcon]; rfl
  have := sum_coe_units_eq_ite φ
  rw [if_neg hφne] at this
  rw [← this]
  exact Finset.sum_congr rfl (fun x _ => hφ x)

/-- The sum of a non-trivial linear character over `Q ∖ {1}` is `-1`. -/
private theorem sum_zeta_erase {G : Type} [Group G] [Fintype G] {Q : Subgroup G} [Fintype ↥Q]
    {ζ : ↥Q → ℂ} (hζ : ζ ∈ Work.CharCore.Irr ↥Q) (hζ1 : ζ ≠ 1) (hlin : ζ 1 = 1) :
    (∑ y ∈ Finset.univ.erase (1 : ↥Q), ζ y) = -1 := by
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ (1 : ↥Q)),
    sum_zeta_eq_zero hζ hζ1 hlin, hlin]
  ring

/-- `⟪Ind ζ₁, Ind ζ₁⟫ = |D| + 1`. -/
private theorem Xi_self {G : Type} [Group G] [Fintype G] {H Q : Subgroup G} [Fintype ↥Q] {t : G}
    (h : IsSplitRankOne H Q t) (hZ : IsZassenhaus H)
    {ζ₁ : ↥Q → ℂ} (hζ : ζ₁ ∈ Work.CharCore.Irr ↥Q) (hζ1 : ζ₁ ≠ 1) (hlin : ζ₁ 1 = 1) :
    Work.CharCore.cfInner (Work.Induction.indFun Q ζ₁) (Work.Induction.indFun Q ζ₁)
      = (Nat.card ↥(twoPoint H t) : ℂ) + 1 :=
  zetaStar_norm h hZ hζ hζ1 hlin

theorem chi1_degree_eq {G : Type} [Group G] [Fintype G] [IsSimpleGroup G] (H Q : Subgroup G) [Fintype ↥Q] (t : G)
    (h : Submission.Blueprint.IsSplitRankOne H Q t) (hZ : Submission.Blueprint.IsZassenhaus H)
    (hQ2 : ¬ IsPGroup 2 Q) (hne : Nat.card (Submission.Blueprint.twoPoint H t) ≠ Nat.card Q - 1)
    (h2 : FeitThm2Prop)
    {ζ₁ : ↥Q → ℂ} (hζ : ζ₁ ∈ Work.CharCore.Irr ↥Q) (hζ1 : ζ₁ ≠ 1) (hlin : ζ₁ 1 = 1) :
    ∃ χ₁ : G → ℂ, χ₁ ∈ Work.CharCore.Irr G ∧
      χ₁ 1 = (Nat.card (Submission.Blueprint.twoPoint H t) : ℂ) := by
  classical
  obtain ⟨χκ, γ, hIrr, hmΞ, hchar, hnorm, hconst, hχ0⟩ :=
    chiXi_exceptionals H Q t h hZ hQ2 hne h2 hζ hζ1 hlin
  refine ⟨χκ, hIrr, ?_⟩
  set q : ℕ := Nat.card ↥(Submission.Blueprint.twoPoint H t) with hqdef
  set m : ℕ := Nat.card ↥Q with hmdef
  set Γ : G → ℂ := Work.Induction.indFun Q ζ₁ - χκ with hΓdef
  have hmΞ' : Work.CharCore.cfInner χκ (Work.Induction.indFun Q ζ₁) = 1 := hmΞ
  have hχ0' : Work.CharCore.cfInner χκ (Work.Induction.indFun Q (fun _ : ↥Q => (1 : ℂ))) = 0 := hχ0
  have hself : Work.CharCore.cfInner (Work.Induction.indFun Q ζ₁)
      (Work.Induction.indFun Q ζ₁) = (q : ℂ) + 1 := by
    rw [hqdef]; exact Xi_self h hZ hζ hζ1 hlin
  have hX0 : Work.CharCore.cfInner (Work.Induction.indFun Q ζ₁)
      (Work.Induction.indFun Q (fun _ : ↥Q => (1 : ℂ))) = (q : ℂ) := by
    rw [hqdef]; exact chiXi_Xi0_inner h hZ hζ hζ1 hlin
  have hclassX : Work.CharCore.IsClassFun (Work.Induction.indFun Q ζ₁) :=
    Work.Induction.isClassFun_indFun Q ζ₁
  have hclassG : Work.CharCore.IsClassFun Γ := by
    rw [hΓdef]
    exact hclassX.sub (Work.CharCore.isClassFun_of_mem_Irr hIrr)
  have hconst' : ∀ y : ↥Q, y ≠ 1 → Γ (y : G) = γ := by
    intro y hy; rw [hΓdef]; exact hconst y hy
  -- inner products of `Γ`
  have hGXi : Work.CharCore.cfInner Γ (Work.Induction.indFun Q ζ₁) = (q : ℂ) := by
    rw [hΓdef, Work.CharCore.cfInner_sub_left, hself, hmΞ']; ring
  have hGX0 : Work.CharCore.cfInner Γ (Work.Induction.indFun Q (fun _ : ↥Q => (1 : ℂ)))
      = (q : ℂ) := by
    rw [hΓdef, Work.CharCore.cfInner_sub_left, hX0, hχ0']; ring
  -- Frobenius reciprocity identities
  obtain ⟨hid1, hid2⟩ := chiGamma_inner h hζ hζ1 hlin hclassG hconst'
  have hmc : (m : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]; exact Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩
  have hkey1 : (Nat.card ↥Q : ℂ) * (q : ℂ) = Γ 1 - γ := by
    rw [← hGXi]; exact hid1
  have hkey2 : (Nat.card ↥Q : ℂ) * (q : ℂ) = Γ 1 + ((Nat.card ↥Q : ℂ) - 1) * γ := by
    rw [← hGX0]; exact hid2
  have hmnz : (Nat.card ↥Q : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]; exact Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩
  -- γ = 0
  have hγ0 : γ = 0 := by
    have hsub : Γ 1 - γ = Γ 1 + ((Nat.card ↥Q : ℂ) - 1) * γ := hkey1.symm.trans hkey2
    have hmul : (Nat.card ↥Q : ℂ) * γ = 0 := by linear_combination -hsub
    exact (mul_eq_zero.mp hmul).resolve_left hmnz
  -- degrees
  have hXi1 : Work.Induction.indFun Q ζ₁ 1 = ((Nat.card ↥Q : ℂ) + 1) * (q : ℂ) := by
    rw [Work.Induction.indFun_apply_one, hlin, mul_one, hqdef]
    rw [Q_index_eq h]; push_cast; ring
  have hΓ1 : Γ 1 = (Nat.card ↥Q : ℂ) * (q : ℂ) := by
    have hh := hkey1
    rw [hγ0, sub_zero] at hh
    exact hh.symm
  have hchi1 : χκ 1 = (q : ℂ) := by
    have hd : Γ 1 = Work.Induction.indFun Q ζ₁ 1 - χκ 1 := by
      rw [hΓdef]; rfl
    rw [hΓ1, hXi1] at hd
    linear_combination hd
  rw [hqdef]; exact hchi1

end Work.ZassenhausTwoGroup
