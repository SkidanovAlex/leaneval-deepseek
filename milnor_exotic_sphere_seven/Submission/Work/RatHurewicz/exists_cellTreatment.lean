import Mathlib
import Submission.Work.RatHurewicz.Triad.StarSupport

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The treatment of a cell

Given a cell `c` of the grid, a map `g` on the cube, a *cell homotopy* `H` on `cellSet c`
(starting at `g` and relative to `cellRelbd c`) and cutoffs `μ ≥ 0` (the flow rate: `0` off the
support `cellStar c ε`, `≥ 2` on the cell) and `ν` (`= 1` on the cell), there is a homotopy `G` of
the whole cube which

* starts at `g`, is trivial off `cellStar c ε`;
* on `cellSet c` is `H(·, pushTime μ ν · ·)`, hence at time `1` the fully pushed values;
* at a point where the flow has arrived (`1 ≤ s·μ x`) is `H` evaluated at the clamp.

The construction is the two-phase formula of `Triad/NOTES_triadCompression.md` (session 5):
`g ∘ flowCell` before the arrival (the "move"), `H ∘ clamp` after it (the "push"), the two branches
agreeing at `s·μ x = 1` because there `flowCell = clampCell c x` and `pushTime = 0`.
-/

open scoped Topology unitInterval

namespace Work.RatHurewicz

noncomputable section

open Work.ThomBordism.TwoSet
open Work.RatHurewicz.Triad

variable {j N : ℕ}

theorem continuous_flowCell_pair (hN : 1 ≤ N) (c : CellIdx j N) (μ : C(IC j, ℝ)) :
    Continuous fun p : IC j × I => flowCell c hN μ p.1 p.2 := by
  have h : Continuous fun p : IC j × I =>
      (p.1, ((clampCell c hN) p.1, flowParam μ p.1 p.2)) :=
    continuous_fst.prodMk
      (((clampCell c hN).continuous.comp continuous_fst).prodMk
        (Continuous.subtype_mk
          ((continuous_const.min (continuous_const.max
            ((continuous_subtype_val.comp continuous_snd).mul
              (μ.continuous.comp continuous_fst))))) _))
  exact (continuous_segMap j).comp h

theorem continuous_pushTime_pair (μ : C(IC j, ℝ)) (ν : C(IC j, I)) :
    Continuous fun p : IC j × I => pushTime μ ν p.1 p.2 := by
  refine Continuous.subtype_mk ?_ _
  have h1 : Continuous fun p : IC j × I =>
      (⟨min 1 (max 0 ((p.2 : ℝ) * μ p.1 - 1)),
        ⟨le_min (by norm_num) (le_max_left _ _), min_le_left _ _⟩⟩ : I) :=
    Continuous.subtype_mk (continuous_const.min (continuous_const.max
      (((continuous_subtype_val.comp continuous_snd).mul
        (μ.continuous.comp continuous_fst)).sub continuous_const))) _
  exact (continuous_subtype_val.comp h1).mul (continuous_subtype_val.comp
    (ν.continuous.comp continuous_fst))

/-- **The treatment of a cell.** -/
theorem exists_cellTreatment {j N : ℕ} (hN : 1 ≤ N) (c : CellIdx j N)
    {ε : ℝ} (hε : 0 ≤ ε)
    {Y : Type} [TopologicalSpace Y] (g : C(IC j, Y))
    (H : C(cellSet c × I, Y))
    (hH0 : ∀ z : cellSet c, H (z, 0) = g z)
    (hHbd : ∀ z : cellSet c, (z : IC j) ∈ cellRelbd c → ∀ t, H (z, t) = g z)
    (μ : C(IC j, ℝ)) (ν : C(IC j, I))
    (hμ0 : ∀ x, x ∉ cellStar c ε → μ x = 0)
    (hμ2 : ∀ x, x ∈ cellSet c → 2 ≤ μ x)
    (hν1 : ∀ x, x ∈ cellSet c → ν x = 1) :
    ∃ G : C(IC j × I, Y),
      (∀ x, G (x, 0) = g x) ∧
      (∀ x, x ∉ cellStar c ε → ∀ s, G (x, s) = g x) ∧
      (∀ (x : IC j) (hx : x ∈ cellSet c) (s : I),
        G (x, s) = H (⟨x, hx⟩, pushTime μ ν x s)) ∧
      (∀ (x : IC j) (s : I), 1 ≤ (s : ℝ) * μ x →
        G (x, s) = H (⟨clampCell c hN x, clampCell_mem c hN x⟩, pushTime μ ν x s)) := by
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
