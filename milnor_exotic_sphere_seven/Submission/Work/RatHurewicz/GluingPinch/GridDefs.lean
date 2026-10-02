import Mathlib
import Submission.Work.RatHurewicz.GluingPinch.CutGen

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Dyadic grid cells of `I^n` and the based readings of a cube on them

For the arrangement computations of the pinch (`glue_class_of_collapse`) one cuts `I^n` along the
dyadic hyperplanes `{u i = 1/2}` (`Work.RatHurewicz.cl_cut_gen`) and reads a based cube on the
resulting `2^n` boxes.  This file supplies the two definitions used to *state* that additivity:

* `cellChart n k` — the affine chart of the box `k : Fin n → Fin 2` onto `I^n`
  (`u ↦ (fun i => clamp (((k i) + u i) / 2))`);
* `cellCube p k h` — the reading `p ∘ cellChart n k`, again a based cube (a cube vanishing on all
  the mid-hyperplanes is `x₀` on the boundary of every cell).

The additivity itself is `Work.RatHurewicz.cl_grid` (delegated).
-/

open scoped unitInterval Topology
open Work.Stems.Cubical
open Work.Stems.Hur2

namespace Work.RatHurewicz

noncomputable section


/-- `clamp` of a real in `[0,1]` is that real. -/
theorem clamp_eq_of_mem {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    ((clamp r : unitInterval) : ℝ) = r := by
  rw [clamp, Set.projIcc_of_mem zero_le_one hr]

/-- The affine chart of the dyadic cell `k` of `I^n` onto `I^n`. -/
def cellChart (n : ℕ) (k : Fin n → Fin 2) : C(IC n, IC n) :=
  ⟨fun u i => clamp ((((k i : ℕ) : ℝ) + (u i : ℝ)) / 2), by
    apply continuous_pi
    intro i
    exact continuous_clamp.comp
      (((continuous_const.add (continuous_subtype_val.comp (continuous_apply i))).div_const 2))⟩

theorem cellChart_apply (n : ℕ) (k : Fin n → Fin 2) (u : IC n) (i : Fin n) :
    cellChart n k u i = clamp ((((k i : ℕ) : ℝ) + (u i : ℝ)) / 2) := rfl

theorem clamp_castSucc_two (j : Fin 2) :
    ((clamp ((((j : ℕ) : ℝ) + 0) / 2) : unitInterval) : ℝ)
      = ((Fin.castSucc j : Fin 3) : ℕ) / 2 := by
  rw [clamp_eq_of_mem (r := ((((j : ℕ) : ℝ) + 0) / 2)) (by
    have h1 : ((j : ℕ) : ℝ) ≤ 1 := by
      exact_mod_cast Nat.lt_succ_iff.mp j.2
    have h0 : (0 : ℝ) ≤ ((j : ℕ) : ℝ) := Nat.cast_nonneg _
    constructor <;> nlinarith)]
  norm_num [Fin.val_castSucc]

theorem clamp_succ_two (j : Fin 2) :
    ((clamp ((((j : ℕ) : ℝ) + 1) / 2) : unitInterval) : ℝ)
      = ((Fin.succ j : Fin 3) : ℕ) / 2 := by
  rw [clamp_eq_of_mem (r := ((((j : ℕ) : ℝ) + 1) / 2)) (by
    have h1 : ((j : ℕ) : ℝ) ≤ 1 := by
      exact_mod_cast Nat.lt_succ_iff.mp j.2
    have h0 : (0 : ℝ) ≤ ((j : ℕ) : ℝ) := Nat.cast_nonneg _
    constructor <;> nlinarith)]
  norm_num [Fin.val_succ]

/-- The reading of a cube `p` on the dyadic cell `k`, a based cube as soon as `p` vanishes on all
the mid-hyperplanes `{u i = 1/2}`. -/
def cellCube {X : Type} [TopologicalSpace X] {x₀ : X} (n : ℕ) (p : GenLoop (Fin n) X x₀)
    (k : Fin n → Fin 2)
    (h : ∀ (i : Fin n) (m : Fin 3) (u : IC n), (u i : ℝ) = ((m : ℕ) : ℝ) / 2 → p.1 u = x₀) :
    GenLoop (Fin n) X x₀ :=
  ⟨⟨fun u => p.1 (cellChart n k u), p.1.continuous.comp (cellChart n k).continuous⟩, by
    intro u hu
    obtain ⟨i, hi | hi⟩ := hu
    · refine h i (Fin.castSucc (k i)) (cellChart n k u) ?_
      have hui : (u i : ℝ) = 0 := by rw [hi]; rfl
      rw [cellChart_apply, hui]
      exact clamp_castSucc_two (k i)
    · refine h i (Fin.succ (k i)) (cellChart n k u) ?_
      have hui : (u i : ℝ) = 1 := by rw [hi]; rfl
      rw [cellChart_apply, hui]
      exact clamp_succ_two (k i)⟩

end

end Work.RatHurewicz
