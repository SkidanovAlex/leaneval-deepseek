/-
Copyright: subproject `Submission/Work/FBif/` of `mandelbar_not_path_connected`.

# `Work.FBif` — the parabolic cycle (FBif, part 0)

The five points `cyclePt c z₁ j = T_c^j z₁` (`j = 0, …, 4`) of the parabolic period-`5` orbit are
pairwise distinct.  This is the non-degeneracy that makes the construction of the perturbing
antipolynomial (`Work.FBif.exists_goodPerturbation`) legal, and it is a consequence of the exact
period of `z₁`.
-/
import Submission.Work.FBif.Defs
import Submission.Work.FSeed.RootParabolic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set Function
open scoped Topology

noncomputable section

namespace Work.FBif

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

theorem cyclePt_zero (c z₁ : ℂ) : cyclePt c z₁ 0 = z₁ := rfl

theorem cyclePt_succ (c z₁ : ℂ) (j : ℕ) :
    cyclePt c z₁ (j + 1) = Tantibar c (cyclePt c z₁ j) := by
  simp [cyclePt, Function.iterate_succ_apply']

/-- The cycle points of an exactly period-`5` point are pairwise distinct (as long as the
indices stay below `5`). -/
theorem cyclePt_ne_of_lt {c z₁ : ℂ} {i j : ℕ} (hij : i < j) (hj : j ≤ 4)
    (hper : (Tantibar c)^[5] z₁ = z₁)
    (hne : ∀ k ∈ Finset.Ioo 0 5, (Tantibar c)^[k] z₁ ≠ z₁) :
    cyclePt c z₁ i ≠ cyclePt c z₁ j := by
  intro heq
  have hi5 : i ≤ 5 := le_trans hij.le (le_trans hj (by norm_num))
  have hd : (Tantibar c)^[j - i] ((Tantibar c)^[i] z₁) = (Tantibar c)^[i] z₁ := by
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hij.le]
    exact heq.symm
  have h1 : (Tantibar c)^[5 - i] ((Tantibar c)^[i] z₁) = z₁ := by
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hi5, hper]
  have hcomm : ∀ (x : ℂ) (m n : ℕ),
      (Tantibar c)^[m] ((Tantibar c)^[n] x) = (Tantibar c)^[n] ((Tantibar c)^[m] x) := by
    intro x m n
    rw [← Function.iterate_add_apply, ← Function.iterate_add_apply, Nat.add_comm]
  have h2 : (Tantibar c)^[j - i] z₁ = z₁ :=
    calc (Tantibar c)^[j - i] z₁
        = (Tantibar c)^[j - i] ((Tantibar c)^[5 - i] ((Tantibar c)^[i] z₁)) := by rw [h1]
      _ = (Tantibar c)^[5 - i] ((Tantibar c)^[j - i] ((Tantibar c)^[i] z₁)) := hcomm _ _ _
      _ = (Tantibar c)^[5 - i] ((Tantibar c)^[i] z₁) := by rw [hd]
      _ = z₁ := h1
  have hpos : 0 < j - i := Nat.sub_pos_of_lt hij
  have hlt : j - i < 5 := lt_of_le_of_lt (Nat.sub_le _ _) (lt_of_le_of_lt hj (by norm_num))
  exact hne (j - i) (Finset.mem_Ioo.mpr ⟨hpos, hlt⟩) h2

/-- The cycle points `z₁, T z₁, T² z₁, T³ z₁` avoid `T⁴ z₁`. -/
theorem cyclePt_ne_four {c z₁ : ℂ} (hper : (Tantibar c)^[5] z₁ = z₁)
    (hne : ∀ k ∈ Finset.Ioo 0 5, (Tantibar c)^[k] z₁ ≠ z₁) {j : ℕ} (hj : j ≤ 3) :
    cyclePt c z₁ j ≠ cyclePt c z₁ 4 :=
  cyclePt_ne_of_lt (by omega) (by norm_num) hper hne

end Work.FBif

namespace Work.EL

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- **The cycle points of a root-parabolic parameter are pairwise distinct below index `5`.** -/
theorem RootParabolic.cyclePt_ne {c : ℂ} (d : RootParabolic c) {i j : ℕ} (hij : i < j)
    (hj : j ≤ 4) : Work.FBif.cyclePt c d.z₁ i ≠ Work.FBif.cyclePt c d.z₁ j :=
  Work.FBif.cyclePt_ne_of_lt hij hj d.per_half d.ne_per

/-- `T⁴ z₁ ≠ z_j` for `j ≤ 3`: the non-degeneracy needed by the perturbation of HS Lemma 3.4. -/
theorem RootParabolic.cyclePt_ne_four {c : ℂ} (d : RootParabolic c) {j : ℕ} (hj : j ≤ 3) :
    Work.FBif.cyclePt c d.z₁ j ≠ Work.FBif.cyclePt c d.z₁ 4 :=
  Work.FBif.cyclePt_ne_four d.per_half d.ne_per hj

/-- The cycle closes up at index `5`. -/
theorem RootParabolic.cyclePt_five {c : ℂ} (d : RootParabolic c) :
    Work.FBif.cyclePt c d.z₁ 5 = d.z₁ := d.per_half

end Work.EL

end
