import Mathlib
import Submission.Work.RatHurewicz.exists_cellTreatment

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The treatment of a cell, with an abstract vanishing locus

This is `Work.RatHurewicz.exists_cellTreatment` with the support `cellStar c ε` replaced by an
arbitrary set `S` on which the rate `μ` is assumed to vanish.  The parameter `ε` never enters the
construction (the flow `flowCell`, the push time `pushTime` and the two-phase formula involve only
`c`, `hN`, `μ`, `ν`), so the proof is the same; the two continuity lemmas
`continuous_flowCell_pair` and `continuous_pushTime_pair` of the imported module are reused
verbatim.
-/

open scoped Topology unitInterval

namespace Work.RatHurewicz

noncomputable section

open Work.ThomBordism.TwoSet
open Work.RatHurewicz.Triad

variable {j N : ℕ}

theorem exists_cellTreatmentOf {j N : ℕ} (hN : 1 ≤ N) (c : Work.ThomBordism.TwoSet.CellIdx j N)
    (S : Set (Work.ThomBordism.TwoSet.IC j))
    {Y : Type} [TopologicalSpace Y] (g : C(Work.ThomBordism.TwoSet.IC j, Y))
    (H : C(Work.ThomBordism.TwoSet.cellSet c × unitInterval, Y))
    (hH0 : ∀ z : Work.ThomBordism.TwoSet.cellSet c, H (z, 0) = g z)
    (hHbd : ∀ z : Work.ThomBordism.TwoSet.cellSet c,
      (z : Work.ThomBordism.TwoSet.IC j) ∈ Work.ThomBordism.TwoSet.cellRelbd c →
        ∀ t, H (z, t) = g z)
    (μ : C(Work.ThomBordism.TwoSet.IC j, ℝ)) (ν : C(Work.ThomBordism.TwoSet.IC j, unitInterval))
    (hμ0 : ∀ x, x ∉ S → μ x = 0)
    (hμ2 : ∀ x, x ∈ Work.ThomBordism.TwoSet.cellSet c → 2 ≤ μ x)
    (hν1 : ∀ x, x ∈ Work.ThomBordism.TwoSet.cellSet c → ν x = 1) :
    ∃ G : C(Work.ThomBordism.TwoSet.IC j × unitInterval, Y),
      (∀ x, G (x, 0) = g x) ∧
      (∀ x, x ∉ S → ∀ s, G (x, s) = g x) ∧
      (∀ (x : Work.ThomBordism.TwoSet.IC j)
        (hx : x ∈ Work.ThomBordism.TwoSet.cellSet c) (s : unitInterval),
        G (x, s) = H (⟨x, hx⟩, Work.RatHurewicz.Triad.pushTime μ ν x s)) ∧
      (∀ (x : Work.ThomBordism.TwoSet.IC j) (s : unitInterval), 1 ≤ (s : ℝ) * μ x →
        G (x, s) = H (⟨Work.ThomBordism.TwoSet.clampCell c hN x,
          Work.ThomBordism.TwoSet.clampCell_mem c hN x⟩,
            Work.RatHurewicz.Triad.pushTime μ ν x s)) := by
  classical
  have hkey : ∀ p : IC j × I, (p.2 : ℝ) * μ p.1 = 1 →
      g (flowCell c hN μ p.1 p.2) =
        H (⟨clampCell c hN p.1, clampCell_mem c hN p.1⟩, pushTime μ ν p.1 p.2) := by
    intro p hp
    have harr : 1 ≤ (p.2 : ℝ) * μ p.1 := le_of_eq hp.symm
    have hflow : flowCell c hN μ p.1 p.2 = clampCell c hN p.1 := by
      have hpar : flowParam μ p.1 p.2 = 1 := by
        apply Subtype.ext
        simp only [flowParam_val]
        exact min_eq_left (le_trans harr (le_max_right 0 _))
      rw [flowCell, hpar, segMap_one]
    have hpt : pushTime μ ν p.1 p.2 = 0 := pushTime_eq_zero_of_le (le_of_eq hp)
    rw [hflow, hpt]
    exact (hH0 ⟨clampCell c hN p.1, clampCell_mem c hN p.1⟩).symm
  have hcont : Continuous fun p : IC j × I =>
      if (p.2 : ℝ) * μ p.1 ≤ (1:ℝ) then g (flowCell c hN μ p.1 p.2)
      else H (⟨clampCell c hN p.1, clampCell_mem c hN p.1⟩, pushTime μ ν p.1 p.2) :=
    Continuous.if_le (g.continuous.comp (continuous_flowCell_pair hN c μ))
      (H.continuous.comp (Continuous.prodMk
        (Continuous.subtype_mk ((clampCell c hN).continuous.comp continuous_fst) _)
        (continuous_pushTime_pair μ ν)))
      ((continuous_subtype_val.comp continuous_snd).mul (μ.continuous.comp continuous_fst))
      continuous_const hkey
  refine ⟨⟨fun p => if (p.2 : ℝ) * μ p.1 ≤ (1:ℝ) then g (flowCell c hN μ p.1 p.2)
      else H (⟨clampCell c hN p.1, clampCell_mem c hN p.1⟩, pushTime μ ν p.1 p.2), hcont⟩,
    ?_, ?_, ?_, ?_⟩
  · intro x
    show (if ((0 : I) : ℝ) * μ x ≤ (1:ℝ) then g (flowCell c hN μ x 0)
      else H (⟨clampCell c hN x, clampCell_mem c hN x⟩, pushTime μ ν x 0)) = g x
    have h : ((0 : I) : ℝ) * μ x ≤ (1:ℝ) := by simp
    rw [if_pos h, flowCell_zero]
  · intro x hx s
    show (if (s : ℝ) * μ x ≤ (1:ℝ) then g (flowCell c hN μ x s)
      else H (⟨clampCell c hN x, clampCell_mem c hN x⟩, pushTime μ ν x s)) = g x
    have hμ : μ x = 0 := hμ0 x hx
    have h : (s : ℝ) * μ x ≤ (1:ℝ) := by rw [hμ, mul_zero]; norm_num
    rw [if_pos h, flowCell_eq_self_of_mu_eq_zero hN hμ s]
  · intro x hx s
    show (if (s : ℝ) * μ x ≤ (1:ℝ) then g (flowCell c hN μ x s)
      else H (⟨clampCell c hN x, clampCell_mem c hN x⟩, pushTime μ ν x s)) =
        H (⟨x, hx⟩, pushTime μ ν x s)
    by_cases h : (s : ℝ) * μ x ≤ (1:ℝ)
    · rw [if_pos h, flowCell_eq_self_of_mem hN μ hx s, pushTime_eq_zero_of_le h]
      exact (hH0 ⟨x, hx⟩).symm
    · rw [if_neg h, show (⟨clampCell c hN x, clampCell_mem c hN x⟩ : cellSet c) = ⟨x, hx⟩ from
        Subtype.ext (clampCell_eq_self c hN hx)]
  · intro x s h
    show (if (s : ℝ) * μ x ≤ (1:ℝ) then g (flowCell c hN μ x s)
      else H (⟨clampCell c hN x, clampCell_mem c hN x⟩, pushTime μ ν x s)) =
        H (⟨clampCell c hN x, clampCell_mem c hN x⟩, pushTime μ ν x s)
    by_cases hc : (s : ℝ) * μ x ≤ (1:ℝ)
    · rw [if_pos hc]
      exact hkey (x, s) (le_antisymm hc h)
    · rw [if_neg hc]

end

end Work.RatHurewicz
