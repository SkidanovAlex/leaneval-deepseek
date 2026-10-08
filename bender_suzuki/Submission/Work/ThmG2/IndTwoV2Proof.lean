import Mathlib
import Submission.Work.ThmG2.Defs
import Submission.Work.ThmG2.cfInner_indFun_self_twoDoubleCoset
import Submission.Work.ThmF.Setup
import Submission.Work.ThmF.ChV12.Basic
import Submission.Work.ThmG.rankOne_isTI
import Submission.Work.CharCore.Main
import Submission.Work.CharCore.isChar_norm_two
import Submission.Work.CharCore.linear_char_iff_deg_one
import Submission.Work.CharCore.star_Irr
import Submission.Work.Induction.isChar_indFun
import Submission.Work.Induction.isClassFun_indFun

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Area `ThmG2`: the corrected field 6 `IndTwoV2Prop`, proved inside this area

`Work.ThmG2.IndTwoV2Prop` (Peterfalvi II, Ch. VI §1 p. 258, corrected: `λ` trivial on `QK`) is
normally supplied by area `ThmF` (`Work.ThmF.ChV12.ind_two_v2`), which however currently rests on
the two `sorry`s of `Submission/Work/ThmF/ChV12/_dev.lean`.  This module proves
`Work.ThmG2.indTwoV2Prop` **inside area `ThmG2`**, using

* `Work.ThmG2.cfInner_indFun_self_twoDoubleCoset` — Mackey's formula on the two double cosets,
  proved self-contained in this area, and
* `Work.CharCore.isChar_norm_two`, already axiom-clean in area `A5`,

so that `ThmG2` does not depend on the pending `_dev.lean`.  The proof is the one designed by area
`ThmF` (their `ind_two_v2`), with `t`-invariance of `λ` on `D` obtained from `K ⊆ ker λ` via the
element `d · (t d t)⁻¹ ∈ K`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Work.ThmG2

open Classical LeanEval.GroupTheory.Defs Submission.Blueprint Work.ThmF

variable {G : Type*} [Group G]

/-- `t * t = 1` for the distinguished involution `t` of a split rank-one datum. -/
theorem rankOne_t_mul_self {H Q : Subgroup G} {t : G} (h : IsSplitRankOne H Q t) :
    t * t = 1 := by
  have h2 : t ^ 2 = 1 := by
    have := pow_orderOf_eq_one t
    rw [h.invol] at this
    simpa using this
  simpa [pow_two] using h2

/-- `t` normalises the two-point stabiliser `D = twoPoint H t`. -/
theorem rankOne_conj_mem_twoPoint {H Q : Subgroup G} {t : G} (h : IsSplitRankOne H Q t) :
    ∀ d : twoPoint H t, (MulAut.conj t) (d:G) ∈ twoPoint H t := by
  intro d
  have hn := Work.ThmF.normalizes_twoPoint_of_data (@Work.ThmF.IsSplitRankOne.toData G _ H Q t h)
  have := (Subgroup.mem_normalizer_iff.mp hn) (d:G)
  rw [MulAut.conj_apply]
  exact this.mp d.2

/-- The double coset cover `G = H ∪ H t H` of the split rank-one situation. -/
theorem rankOne_doubleCoset_cover {H Q : Subgroup G} {t : G} (h : IsSplitRankOne H Q t) :
    ∀ g : G, g ∈ H ∨ ∃ a b : H, g = (a:G) * t * (b:G) := by
  intro g
  by_cases hg : g ∈ H
  · exact Or.inl hg
  · right
    have htH : t ∉ H := h.not_mem
    have h1 : (t : G ⧸ H) ≠ Work.ThmG.basePt H := (Work.ThmG.basePt_ne_iff H t).mpr htH
    have h2 : (g : G ⧸ H) ≠ Work.ThmG.basePt H := (Work.ThmG.basePt_ne_iff H g).mpr hg
    obtain ⟨c, hcH, hc⟩ := Work.ThmG.h_transitive h (t : G ⧸ H) (g : G ⧸ H) h1 h2
    have hc' : ((c * t : G) : G ⧸ H) = (g : G ⧸ H) := by
      rw [← Work.ThmG.smul_basePt H t, ← mul_smul, Work.ThmG.smul_basePt H (c*t)] at hc
      exact hc
    have hmem : (c * t)⁻¹ * g ∈ H := QuotientGroup.eq.mp hc'
    refine ⟨⟨c, hcH⟩, ⟨(c * t)⁻¹ * g, hmem⟩, ?_⟩
    push_cast
    group


theorem ind_two_v2_self {G : Type} [Group G] [Fintype G] (hS : Situation G) (H Q : Subgroup G) (t : G) (h : IsSplitRankOne H Q t) (hZ : ¬ IsZassenhaus H) (lam : H → ℂ) (hlam : lam ∈ Work.CharCore.Irr H) (h1 : lam 1 = 1) (hne : lam ≠ (fun _ : H => (1 : ℂ))) (hkerQ : ∀ x : H, (x : G) ∈ Q → lam x = 1) (hkerK : ∀ x : H, (x : G) ∈ Kset H t → lam x = 1) : ∃ f₁ ∈ Work.CharCore.Irr G, ∃ f₂ ∈ Work.CharCore.Irr G, f₁ ≠ f₂ ∧ Work.Induction.indFun H lam = f₁ + f₂ := by
  classical
  have ht := rankOne_t_mul_self h
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hDmap := rankOne_conj_mem_twoPoint h
  have hcover := rankOne_doubleCoset_cover h
  have hlam_class : Work.CharCore.IsClassFun lam := Work.CharCore.isClassFun_of_mem_Irr hlam
  -- `lam` is linear
  have hdeg : Work.CharCore.irrDeg lam = 1 := by
    have hspec := Work.CharCore.irrDeg_spec hlam
    rw [h1] at hspec
    exact_mod_cast hspec.symm
  obtain ⟨φ, hφ⟩ := (Work.CharCore.linear_char_iff_deg_one hlam).mp hdeg
  have hmul : ∀ a b : H, lam (a * b) = lam a * lam b := by
    intro a b
    rw [hφ (a * b), hφ a, hφ b, map_mul, Units.val_mul]
  -- the cross term is `1`: for `d ∈ D`, `lam d * conj (lam (t d t⁻¹)) = 1`
  have hcross : ∀ d : ↥(H ⊓ H.map (MulAut.conj t).toMonoidHom),
      lam ⟨(d:G), (Subgroup.mem_inf.mp d.2).1⟩ *
        star (lam ⟨(MulAut.conj t) (d:G),
          (Subgroup.mem_inf.mp (hDmap d)).1⟩) = 1 := by
    intro d
    set a : G := (d:G) with ha
    set c : G := (MulAut.conj t) (d:G) with hc
    set dh : H := ⟨a, (Subgroup.mem_inf.mp d.2).1⟩ with hdh
    set th : H := ⟨c, (Subgroup.mem_inf.mp (hDmap d)).1⟩ with hth
    have hstar : star (lam th) = lam th⁻¹ := Work.CharCore.star_Irr lam hlam th
    rw [hstar, ← hmul dh th⁻¹]
    refine hkerK (dh * th⁻¹) ?_
    rw [Work.ThmF.mem_Kset_iff]
    -- group-theoretic facts
    have haH : a ∈ H := (Subgroup.mem_inf.mp d.2).1
    have hcD : c ∈ twoPoint H t := hDmap d
    have hcH : c ∈ H := (Subgroup.mem_inf.mp hcD).1
    have hconja : (MulAut.conj t) a = c := by rw [ha, hc]
    have hta : t * a * t = c := by rw [← hconja, MulAut.conj_apply, htinv]
    have htct : t * c * t ∈ H := by
      have := (Subgroup.mem_inf.mp (hDmap ⟨c, hcD⟩)).1
      rwa [MulAut.conj_apply, htinv] at this
    have htca : t * c * t = a := by
      rw [← hta, show t * (t * a * t) * t = (t * t) * a * (t * t) from by group,
        ht, one_mul, mul_one]
    have hcoe : ((dh * th⁻¹ : H) : G) = a * c⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv]
    have hkey : t * (a * c⁻¹) * t = c * (t * c * t)⁻¹ := by
      rw [show t * (a * c⁻¹) * t = (MulAut.conj t) (a * c⁻¹) from by
            rw [MulAut.conj_apply, htinv],
          map_mul, map_inv, hconja,
          show (MulAut.conj t) c = t * c * t from by rw [MulAut.conj_apply, htinv]]
    refine ⟨?_, ?_⟩
    · refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · rw [hcoe]; exact H.mul_mem haH (H.inv_mem hcH)
      · rw [Work.ThmG.mem_conj_iff_inv, hcoe, htinv, hkey]
        exact H.mul_mem hcH (H.inv_mem htct)
    · rw [hcoe, show t * (a * c⁻¹) * t⁻¹ = c * (t * c * t)⁻¹ from by rw [htinv]; exact hkey,
        htca]
      group
  -- the norm of `lam` and of `Ind lam`
  have hself : Work.CharCore.cfInner lam lam = 1 := by
    rw [Work.CharCore.irr_orthonormal lam lam hlam hlam]; simp
  have h1D : (1:G) ∈ (H ⊓ H.map (MulAut.conj t).toMonoidHom : Subgroup G) :=
    Subgroup.mem_inf.mpr ⟨H.one_mem, (H.map (MulAut.conj t).toMonoidHom).one_mem⟩
  have hDcard : (Nat.card ↥(H ⊓ H.map (MulAut.conj t).toMonoidHom) : ℂ) ≠ 0 := by
    haveI : Nonempty ↥(H ⊓ H.map (MulAut.conj t).toMonoidHom) := ⟨⟨1, h1D⟩⟩
    rw [Nat.card_eq_fintype_card, Nat.cast_ne_zero]
    exact Fintype.card_ne_zero
  have hsum : (∑ d : ↥(H ⊓ H.map (MulAut.conj t).toMonoidHom),
      lam ⟨(d:G), (Subgroup.mem_inf.mp d.2).1⟩ *
        star (lam ⟨(MulAut.conj t) (d:G),
          (Subgroup.mem_inf.mp (hDmap d)).1⟩))
      = (Nat.card ↥(H ⊓ H.map (MulAut.conj t).toMonoidHom) : ℂ) := by
    rw [Finset.sum_congr rfl (fun d _ => hcross d), Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one, Nat.card_eq_fintype_card]
  have hnorm : Work.CharCore.cfInner (Work.Induction.indFun H lam)
      (Work.Induction.indFun H lam) = 2 := by
    rw [Work.ThmG2.cfInner_indFun_self_twoDoubleCoset (H := H) (t := t) (ψ := lam)
      ht h.not_mem hcover hDmap hlam_class]
    rw [hself, hsum, inv_mul_cancel₀ hDcard]
    norm_num
  exact Work.CharCore.isChar_norm_two (Work.Induction.isChar_indFun_irr hlam)
    (Work.Induction.isClassFun_indFun H lam) hnorm

/-- **Field 6 of `RankOneStructure2`, corrected** (Ch. VI §1, p. 258): for a linear character `λ`
of `H` trivial on `Q` and on `K = J(D,t)`, `Ind_H^G λ = f₁ + f₂` with `f₁ ≠ f₂` irreducible. -/
theorem indTwoV2Prop : IndTwoV2Prop := by
  intro G _ _ H Q t hh lam hlam h1 hne hQ hK
  obtain ⟨hS, _, hsplit, hZ, _⟩ := hh
  exact ind_two_v2_self hS H Q t hsplit hZ lam hlam h1 hne hQ hK

end Work.ThmG2
