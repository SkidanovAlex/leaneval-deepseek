import Mathlib
import Submission.Work.BG.c4TripleAux
import Submission.Work.BG.c4Aux
import Submission.Work.BG.L41Aux

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 Work.GW2.C23

/-! ## Linear reading of the three equations

The three hypotheses of `c4TripleDistinct` are the three decompositions of the §4 (`D.n = 2`)
`δ`-characters `δ_κ = ψ₁ + ψ₂ + ψ₃ + ψ₄`, `δ_{μ₂} = ψ₁ - ψ₂ + ψ₃ - ψ₄`,
`δ_{μ₃} = ψ₁ + ψ₂ - ψ₃ - ψ₄`.  The following three elementary (additive-group) facts are the
only linear manipulations used below: they read `ψ₄ = -ψ₂`, `ψ₄ = -ψ₃`, `ψ₃ = ψ₂` off the
equalities of the corresponding pairs. -/

private theorem c4td_eq_neg_of_triple {G : Type} [Group G] (a b c d : ClassFunction G ℂ)
    (h : a + b + c + d = a - b + c - d) : d = -b := by
  apply ClassFunction.ext
  intro g
  have hg := congrArg (fun φ : ClassFunction G ℂ => (φ : G → ℂ) g) h
  simp only [ClassFunction.add_apply, ClassFunction.sub_apply] at hg
  simp only [ClassFunction.neg_apply]
  linear_combination (1/2 : ℂ) * hg

private theorem c4td_eq_neg_of_triple2 {G : Type} [Group G] (a b c d : ClassFunction G ℂ)
    (h : a + b + c + d = a + b - c - d) : d = -c := by
  apply ClassFunction.ext
  intro g
  have hg := congrArg (fun φ : ClassFunction G ℂ => (φ : G → ℂ) g) h
  simp only [ClassFunction.add_apply, ClassFunction.sub_apply] at hg
  simp only [ClassFunction.neg_apply]
  linear_combination (1/2 : ℂ) * hg

private theorem c4td_eq_of_cross {G : Type} [Group G] (a b c d : ClassFunction G ℂ)
    (h : a - b + c - d = a + b - c - d) : c = b := by
  apply ClassFunction.ext
  intro g
  have hg := congrArg (fun φ : ClassFunction G ℂ => (φ : G → ℂ) g) h
  simp only [ClassFunction.add_apply, ClassFunction.sub_apply] at hg
  linear_combination (1/2 : ℂ) * hg

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 Work.GW2.C23 in
theorem c4TripleDistinct {G : Type} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (hC : Work.GW2.C16.Compat D C) (hn : D.n = 2)
    {β₂ : Work.BG.quotGroup C.P →* ℂˣ} (hβ : β₂ ≠ 1)
    {κ : ClassFunction ↥C.P.H0 ℂ} (hκ : Work.GW2.C16.IsKappa D C κ)
    {μ₂ μ₃ : ClassFunction ↥C.P.H0 ℂ} (hμ₂ : μ₂ ∈ Work.GW2.C16.S4Index C)
    (hμ₃ : μ₃ ∈ Work.GW2.C16.S4Index C)
    {ψ₁ ψ₂ ψ₃ ψ₄ : ClassFunction G ℂ}
    (hψ1 : Work.BG.IsPmIrr ψ₁) (hψ2 : Work.BG.IsPmIrr ψ₂)
    (hψ3 : Work.BG.IsPmIrr ψ₃) (hψ4 : Work.BG.IsPmIrr ψ₄)
    (heq1 : Work.GW2.C16.delta C β₂ κ = ψ₁ + ψ₂ + ψ₃ + ψ₄)
    (heq2 : Work.GW2.C16.delta C β₂ μ₂ = ψ₁ - ψ₂ + ψ₃ - ψ₄)
    (heq3 : Work.GW2.C16.delta C β₂ μ₃ = ψ₁ + ψ₂ - ψ₃ - ψ₄) :
    κ ≠ μ₂ ∧ κ ≠ μ₃ ∧ μ₂ ≠ μ₃ := by
  classical
  have h2 : Nat.card (Work.BG.quotGroup C.P) = 2 := quotGroup_card_two D C hC hn
  -- each of the three `δ`'s is an element of `ℤ[Irr G]` of norm `4`
  -- (`l41_delta_inner_self`, `s`-fixedness of `S4Index`)
  have hnκ : ClassFunction.inner (delta C β₂ κ) (delta C β₂ κ) = 4 := by
    rw [l41_delta_inner_self C h2 hβ hκ.1, if_pos hκ.2.2.1]
  have hn₂ : ClassFunction.inner (delta C β₂ μ₂) (delta C β₂ μ₂) = 4 := by
    rw [l41_delta_inner_self C h2 hβ hμ₂.1, if_pos hμ₂.2.1]
  have hn₃ : ClassFunction.inner (delta C β₂ μ₃) (delta C β₂ μ₃) = 4 := by
    rw [l41_delta_inner_self C h2 hβ hμ₃.1, if_pos hμ₃.2.1]
  refine ⟨?_, ?_, ?_⟩
  · -- `κ = μ₂` would force `ψ₄ = -ψ₂`, hence `δ_κ = ψ₁ + ψ₃`, hence `ψ₁ = ψ₃` by norm `4`;
    -- then `δ_κ = 2ψ₁` has degree `0`, contradicting `ψ₁(1) ≠ 0`
    intro h
    have hdeq : delta C β₂ κ = delta C β₂ μ₂ := by rw [h]
    have hfun : ψ₁ + ψ₂ + ψ₃ + ψ₄ = ψ₁ - ψ₂ + ψ₃ - ψ₄ :=
      heq1.symm.trans (hdeq.trans heq2)
    have hd : ψ₄ = -ψ₂ := c4td_eq_neg_of_triple ψ₁ ψ₂ ψ₃ ψ₄ hfun
    have hD : delta C β₂ κ = ψ₁ + ψ₃ := by
      rw [heq1, hd]
      abel
    have h13 : ψ₁ = ψ₃ :=
      pmIrr_add_eq_of_norm_four hψ1 hψ3 (by rw [← hD]; exact hnκ)
    have hz : (ψ₁ + ψ₃) 1 = 0 := by rw [← hD]; exact l41_delta_apply_one C hκ.1
    rw [← h13, ClassFunction.add_apply] at hz
    exact IsPmIrr.apply_one_ne_zero hψ1 (add_self_eq_zero.mp hz)
  · -- `κ = μ₃` would force `ψ₄ = -ψ₃`, hence `δ_κ = ψ₁ + ψ₂`, hence `ψ₁ = ψ₂`
    intro h
    have hdeq : delta C β₂ κ = delta C β₂ μ₃ := by rw [h]
    have hfun : ψ₁ + ψ₂ + ψ₃ + ψ₄ = ψ₁ + ψ₂ - ψ₃ - ψ₄ :=
      heq1.symm.trans (hdeq.trans heq3)
    have hd : ψ₄ = -ψ₃ := c4td_eq_neg_of_triple2 ψ₁ ψ₂ ψ₃ ψ₄ hfun
    have hD : delta C β₂ κ = ψ₁ + ψ₂ := by
      rw [heq1, hd]
      abel
    have h12 : ψ₁ = ψ₂ :=
      pmIrr_add_eq_of_norm_four hψ1 hψ2 (by rw [← hD]; exact hnκ)
    have hz : (ψ₁ + ψ₂) 1 = 0 := by rw [← hD]; exact l41_delta_apply_one C hκ.1
    rw [← h12, ClassFunction.add_apply] at hz
    exact IsPmIrr.apply_one_ne_zero hψ1 (add_self_eq_zero.mp hz)
  · -- `μ₂ = μ₃` would force `ψ₃ = ψ₂`, hence `δ_{μ₂} = ψ₁ - ψ₄ = ψ₁ + (-ψ₄)`, and norm `4`
    -- gives `ψ₁ = -ψ₄`, so `δ_{μ₂} = 2ψ₁`
    intro h
    have hdeq : delta C β₂ μ₂ = delta C β₂ μ₃ := by rw [h]
    have hfun : ψ₁ - ψ₂ + ψ₃ - ψ₄ = ψ₁ + ψ₂ - ψ₃ - ψ₄ :=
      heq2.symm.trans (hdeq.trans heq3)
    have hc : ψ₃ = ψ₂ := c4td_eq_of_cross ψ₁ ψ₂ ψ₃ ψ₄ hfun
    have hD : delta C β₂ μ₂ = ψ₁ - ψ₄ := by
      rw [heq2, hc]
      abel
    have hD2 : delta C β₂ μ₂ = ψ₁ + (-ψ₄) := by rw [hD, sub_eq_add_neg]
    have hnorm : ClassFunction.inner (ψ₁ + (-ψ₄)) (ψ₁ + (-ψ₄)) = 4 := by
      rw [← hD2]; exact hn₂
    have h14 : ψ₁ = -ψ₄ := pmIrr_add_eq_of_norm_four hψ1 (isPmIrr_neg hψ4) hnorm
    have hz : (ψ₁ + (-ψ₄)) 1 = 0 := by rw [← hD2]; exact l41_delta_apply_one C hμ₂.1
    rw [← h14, ClassFunction.add_apply] at hz
    exact IsPmIrr.apply_one_ne_zero hψ1 (add_self_eq_zero.mp hz)

end Work.BG
