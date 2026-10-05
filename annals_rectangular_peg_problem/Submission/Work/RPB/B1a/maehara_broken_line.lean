import Mathlib
import Submission.Work.RPB1a.Caratheodory.Brouwer.MaeharaDefs
import Submission.Work.RPB1a.Caratheodory.Brouwer.exists_maehara_broken_line
import Submission.Work.RPB.B1a.Maehara.Setup
import Submission.Work.RPB.B1a.Maehara.jordan_arcs_prod

set_option maxHeartbeats 1000000

namespace Work.RPB.B1a

open Set
open Work.RPB1a.Caratheodory.Brouwer
open Work.RPB.B1a.Maehara

/-- **The Maehara broken line.**

Assembly of the broken line `(0,2) ~ m + m ~ l + l ~ k + k ~ j + j ~ (0,-2)` from the two arcs of
the Jordan curve `γ` cut at `(-1,0)` and `(1,0)`: the arcs are produced by
`Work.RPB.B1a.Maehara.jordan_arcs_prod`, the topmost point `m` of the curve on the vertical line
`re = 0` by the intermediate value theorem, and the geometric construction of the broken line
(including the crossing argument on the downward segment) by
`Work.RPB1a.Caratheodory.Brouwer.maehara_broken_line_of_arcs`. -/
theorem maehara_broken_line (γ : Circle → ℝ × ℝ) (hγ : Continuous γ)
    (hinj : Function.Injective γ)
    (ha : ((-1 : ℝ), (0 : ℝ)) ∈ Set.range γ) (hb : ((1 : ℝ), (0 : ℝ)) ∈ Set.range γ)
    (hsub : Set.range γ ⊆ Work.RPB1a.Caratheodory.Brouwer.rect)
    (hbdry : Set.range γ ∩ Work.RPB1a.Caratheodory.Brouwer.rectB =
      {((-1 : ℝ), (0 : ℝ)), ((1 : ℝ), (0 : ℝ))}) :
    ∃ (β : ℝ → ℝ × ℝ) (x : ℝ × ℝ),
      Continuous β ∧ β (-1) = ((0 : ℝ), (2 : ℝ)) ∧ β 1 = ((0 : ℝ), (-2 : ℝ)) ∧
      (∀ t, β t ∈ Work.RPB1a.Caratheodory.Brouwer.rect) ∧
      (((-1 : ℝ), (0 : ℝ)) ∉ β '' Set.Icc (-1 : ℝ) 1) ∧
      (((1 : ℝ), (0 : ℝ)) ∉ β '' Set.Icc (-1 : ℝ) 1) ∧
      x ∉ Set.range γ ∧
      (∀ w ∈ β '' Set.Icc (-1 : ℝ) 1, w ∉ Set.range γ →
        w ∈ connectedComponentIn ((Set.range γ)ᶜ) x ∨
        ¬ Bornology.IsBounded (connectedComponentIn ((Set.range γ)ᶜ) w)) := by
  classical
  -- The two endpoints of the arcs are distinct.
  have hab : ((-1 : ℝ), (0 : ℝ)) ≠ ((1 : ℝ), (0 : ℝ)) := by
    intro h; have := congrArg Prod.fst h; norm_num at this
  -- Split the Jordan curve into two arcs running from `a` to `b`.
  obtain ⟨P, Q, hPc, hQc, hPm1, hP1, hQm1, hQ1, hPinj, hQinj, hPmem, hQmem, hcover, hinter⟩ :=
    jordan_arcs_prod γ hγ hinj ha hb hab
  have hPimg_sub : P '' Set.Icc (-1 : ℝ) 1 ⊆ Set.range γ :=
    fun z ⟨t, ht, hzt⟩ => hzt ▸ hPmem t ht
  have hQimg_sub : Q '' Set.Icc (-1 : ℝ) 1 ⊆ Set.range γ :=
    fun z ⟨t, ht, hzt⟩ => hzt ▸ hQmem t ht
  -- Clamp the two arcs outside `[-1,1]` so that they take values on the curve for *every* real
  -- parameter (the clamped path agrees with the original one on `[-1,1]`).
  set PJc : ℝ → ℝ × ℝ := clampPath P with hPJc
  set PJd : ℝ → ℝ × ℝ := clampPath Q with hPJd
  have hPJcc : Continuous PJc := by rw [hPJc]; exact continuous_clampPath hPc
  have hPJdc : Continuous PJd := by rw [hPJd]; exact continuous_clampPath hQc
  have hPJcinj : Set.InjOn PJc (Set.Icc (-1 : ℝ) 1) := by
    intro s hs t ht hst
    rw [hPJc] at hst
    rw [clampPath_of_mem hs, clampPath_of_mem ht] at hst
    exact hPinj hs ht hst
  have hPJdinj : Set.InjOn PJd (Set.Icc (-1 : ℝ) 1) := by
    intro s hs t ht hst
    rw [hPJd] at hst
    rw [clampPath_of_mem hs, clampPath_of_mem ht] at hst
    exact hQinj hs ht hst
  have hPJcm1 : PJc (-1) = ((-1 : ℝ), (0 : ℝ)) := by
    rw [hPJc, clampPath_neg_one]; exact hPm1
  have hPJc1 : PJc 1 = ((1 : ℝ), (0 : ℝ)) := by
    rw [hPJc, clampPath_one]; exact hP1
  have hPJdm1 : PJd (-1) = ((-1 : ℝ), (0 : ℝ)) := by
    rw [hPJd, clampPath_neg_one]; exact hQm1
  have hPJd1 : PJd 1 = ((1 : ℝ), (0 : ℝ)) := by
    rw [hPJd, clampPath_one]; exact hQ1
  have hPJcmem : ∀ t, PJc t ∈ Set.range γ := fun t => hPimg_sub (clampPath_mem_image P t)
  have hPJdmem : ∀ t, PJd t ∈ Set.range γ := fun t => hQimg_sub (clampPath_mem_image Q t)
  have hPJcImg : PJc '' Set.Icc (-1 : ℝ) 1 = P '' Set.Icc (-1 : ℝ) 1 := by
    rw [hPJc, clampPath_image]
  have hPJdImg : PJd '' Set.Icc (-1 : ℝ) 1 = Q '' Set.Icc (-1 : ℝ) 1 := by
    rw [hPJd, clampPath_image]
  have hunion : (PJc '' Set.Icc (-1 : ℝ) 1) ∪ (PJd '' Set.Icc (-1 : ℝ) 1) = Set.range γ := by
    rw [hPJcImg, hPJdImg]; exact hcover.symm
  have hinter' : (PJc '' Set.Icc (-1 : ℝ) 1) ∩ (PJd '' Set.Icc (-1 : ℝ) 1) =
      {((-1 : ℝ), (0 : ℝ)), ((1 : ℝ), (0 : ℝ))} := by
    rw [hPJcImg, hPJdImg]; exact hinter
  -- The topmost point of the curve on the vertical line `re = 0`.
  have hSne : (Set.range γ ∩ {p : ℝ × ℝ | p.1 = 0}).Nonempty := by
    have hIVT := intermediate_value_Icc (show (-1 : ℝ) ≤ 1 by norm_num)
      (f := fun t : ℝ => (P t).1) ((continuous_fst.comp hPc).continuousOn)
    have h0 : (0 : ℝ) ∈ Set.Icc ((fun t : ℝ => (P t).1) (-1)) ((fun t : ℝ => (P t).1) 1) := by
      change (0 : ℝ) ∈ Set.Icc (P (-1)).1 (P 1).1
      rw [hPm1, hP1]; norm_num
    obtain ⟨t, htm, ht0⟩ := hIVT h0
    exact ⟨P t, hPimg_sub ⟨t, htm, rfl⟩, ht0⟩
  have hScomp : IsCompact (Set.range γ ∩ {p : ℝ × ℝ | p.1 = 0}) :=
    (isCompact_range hγ).inter_right (isClosed_eq continuous_fst continuous_const)
  obtain ⟨m, hm_mem, hm_max⟩ :=
    hScomp.exists_isMaxOn hSne (f := fun p : ℝ × ℝ => p.2) continuous_snd.continuousOn
  have hmK : m ∈ Set.range γ := hm_mem.1
  have hm0 : m.1 = 0 := hm_mem.2
  have hmtop : ∀ p ∈ Set.range γ, p.1 = 0 → p.2 ≤ m.2 := fun p hp hp0 => hm_max ⟨hp, hp0⟩
  -- `m` lies on one of the two arcs; use that arc as the "upper" one `Jc`.
  by_cases hm : m ∈ PJc '' Set.Icc (-1 : ℝ) 1
  · exact maehara_broken_line_of_arcs γ hsub (PJc '' Set.Icc (-1 : ℝ) 1) (PJd '' Set.Icc (-1 : ℝ) 1)
      PJc PJd m hPJcc hPJdc hPJcinj hPJdinj hPJcm1 hPJc1 hPJdm1 hPJd1 hPJcmem hPJdmem rfl rfl
      hunion hinter' hm hm0 hmtop
  · have hm' : m ∈ PJd '' Set.Icc (-1 : ℝ) 1 := by
      have h : m ∈ (PJc '' Set.Icc (-1 : ℝ) 1) ∪ (PJd '' Set.Icc (-1 : ℝ) 1) := by
        rw [hunion]; exact hmK
      rcases h with h | h
      · exact absurd h hm
      · exact h
    exact maehara_broken_line_of_arcs γ hsub (PJd '' Set.Icc (-1 : ℝ) 1) (PJc '' Set.Icc (-1 : ℝ) 1)
      PJd PJc m hPJdc hPJcc hPJdinj hPJcinj hPJdm1 hPJd1 hPJcm1 hPJc1 hPJdmem hPJcmem rfl rfl
      (by rw [Set.union_comm]; exact hunion) (by rw [Set.inter_comm]; exact hinter') hm' hm0 hmtop

end Work.RPB.B1a
