import Mathlib
import Submission.Work.EKLComp.Misiurewicz.Defs

/-!
# `vMove x y < r ↔ y ∈ V r • x`

The `V`-displacement `vMove x y` of `Submission/Work/EKLComp/Misiurewicz/Defs.lean` is the
infimum of the `δ > 0` with `CloseBy δ x y`, i.e. `y = g • x` for some `g ∈ V δ`.  This file
shows that, for `r > 0`, the strict inequality `vMove x y < r` is equivalent to `y` lying in the
`V r`-ball of `x`.

Two facts about the two strict inequalities that appear are needed, and neither is automatic:

* the infimum is *strictly* below `r` as soon as `r` itself is a member of the defining set —
  `V r = ⋂_{i,j}{|g_{ij} - 1_{ij}| < r}` is a *strict* neighbourhood condition, so a `g ∈ V r`
  actually lies in some `V δ` with `δ < r` (the maximum of the finitely many entry differences
  is `< r`);
* conversely, from `vMove x y < r` one must extract a member of the defining set below `r`,
  which needs that set to be nonempty — i.e. that `SL₃(ℝ)` acts transitively on `X₃`.
-/

namespace Work.Misiurewicz

open Work.EKLContract Work.EKLComp

/-! ## The action of `SL₃(ℝ)` on `X₃` is transitive -/

/-- Every two points of `X₃ = SL₃(ℝ)/SL₃(ℤ)` are related by some element of `SL₃(ℝ)`. -/
theorem X3_smul_transitive (x y : X3) : ∃ g : SL3, g • x = y := by
  obtain ⟨a, ha⟩ := Quotient.exists_rep x
  obtain ⟨b, hb⟩ := Quotient.exists_rep y
  refine ⟨b * a⁻¹, ?_⟩
  rw [← ha, ← hb]
  show mkX ((b * a⁻¹) * a) = mkX b
  congr 1
  group

/-! ## The neighbourhoods `V δ` grow and shrink strictly -/

theorem V_mono {δ δ' : ℝ} (h : δ ≤ δ') : V δ ⊆ V δ' :=
  fun _ hg i j => lt_of_lt_of_le (hg i j) h

/-- The largest of the entrywise deviations `|g_{ij} - 1_{ij}|`. -/
noncomputable def entrySup (g : SL3) : ℝ :=
  Finset.univ.sup' (Finset.univ_nonempty)
    (fun p : Fin 3 × Fin 3 => |g p.1 p.2 - (1 : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2|)

theorem le_entrySup (g : SL3) (i j : Fin 3) :
    |g i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ entrySup g :=
  Finset.le_sup' (fun p : Fin 3 × Fin 3 => |g p.1 p.2 - (1 : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2|)
    (Finset.mem_univ (i, j))

theorem entrySup_nonneg (g : SL3) : 0 ≤ entrySup g :=
  le_trans (abs_nonneg _) (le_entrySup g 0 0)

theorem entrySup_lt_iff (g : SL3) {r : ℝ} :
    entrySup g < r ↔ ∀ i j, |g i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < r := by
  rw [entrySup, Finset.sup'_lt_iff]
  constructor
  · intro h i j; exact h (i, j) (Finset.mem_univ _)
  · intro h p _; exact h p.1 p.2

/-- `V δ` is unbounded in `δ`: every `g` lies in some `V δ`. -/
theorem exists_pos_mem_V (g : SL3) : ∃ δ : ℝ, 0 < δ ∧ g ∈ V δ := by
  refine ⟨entrySup g + 1, by linarith [entrySup_nonneg g], fun i j => ?_⟩
  linarith [le_entrySup g i j]

/-- A strict refinement of membership in `V r`: some `V δ` with `δ < r` already contains `g`. -/
theorem exists_lt_mem_V {r : ℝ} (hr : 0 < r) {g : SL3} (hg : g ∈ V r) :
    ∃ δ : ℝ, 0 < δ ∧ δ < r ∧ g ∈ V δ := by
  have hlt : entrySup g < r := (entrySup_lt_iff g).mpr (fun i j => hg i j)
  refine ⟨(entrySup g + r) / 2, by linarith [entrySup_nonneg g], by linarith, fun i j => ?_⟩
  linarith [le_entrySup g i j]

/-! ## The defining set of `vMove` -/

/-- The set whose infimum defines `vMove x y` is nonempty, because the action is transitive
and `V δ` eventually contains every group element. -/
theorem vMove_set_nonempty (x y : X3) : ({δ : ℝ | 0 < δ ∧ CloseBy δ x y}).Nonempty := by
  obtain ⟨g, hg⟩ := X3_smul_transitive x y
  obtain ⟨δ, hδpos, hδg⟩ := exists_pos_mem_V g
  exact ⟨δ, hδpos, ⟨g, hδg, hg.symm⟩⟩

/-- The defining set of `vMove x y` is bounded below by `0`. -/
theorem bddBelow_vMove_set (x y : X3) : BddBelow {δ : ℝ | 0 < δ ∧ CloseBy δ x y} :=
  ⟨0, fun _ ha => le_of_lt ha.1⟩

/-! ## The characteristic property of `vMove` -/

/-- For `r > 0`, the displacement from `x` to `y` is `< r` exactly when `y` lies in the
`V r`-ball of `x`. -/
theorem vMove_lt_iff {r : ℝ} (hr : 0 < r) (x y : Work.EKLContract.X3) : Work.EKLComp.vMove x y < r ↔ y ∈ Work.EKLComp.Vball r x := by
  rw [mem_Vball]
  constructor
  · intro h
    obtain ⟨δ, hδ, hδlt⟩ := (csInf_lt_iff (bddBelow_vMove_set x y) (vMove_set_nonempty x y)).mp h
    obtain ⟨u, hu, huy⟩ := hδ.2
    exact ⟨u, V_mono (le_of_lt hδlt) hu, huy.symm⟩
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨δ, hδpos, hδlt, hδu⟩ := exists_lt_mem_V hr hu
    refine lt_of_le_of_lt (csInf_le (bddBelow_vMove_set x (u • x)) ⟨hδpos, ?_⟩) hδlt
    exact ⟨u, hδu, rfl⟩

end Work.Misiurewicz
