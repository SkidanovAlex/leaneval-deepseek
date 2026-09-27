import Mathlib
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLC6Core.cutSetup
import Submission.Work.EKLContract.Lemmas.mkX_mul

/-!
# `Work.EKLC6Core.cut_defs` — vocabulary for the cut cells (Pisa 7.27 / 7.38)

This module fixes the notions used by `Work.EKLC6Core.cut_cells`:

* `VThick η S` — the `η`-thickening `(V η) • S` of a subset of `X₃`, i.e.
  `{g • x : g ∈ V η, x ∈ S}`.  This is exactly the expression occurring in the *thin boundary*
  condition of `cut_cells`.
* `Vball x r` — the "ball" `(V r) • x` around `x`, the `V`-analogue of a metric ball (recall
  `V r` is the set of group elements at max-entry distance `< r` from the identity, so `Vball`
  is the image of an open set and hence open).
* `ThinBdry μ S` — Pisa 7.26/7.27: the boundary of `S` has *µ-thin boundary*, i.e. there is `c`
  with `μ (VThick η (frontier S)) ≤ c η` for all `η > 0`.  This is exactly the condition on the
  cells required by `cut_cells` (with the thickening measured with the group neighbourhoods
  `V η` instead of a metric `δ`-neighbourhood).
-/

open MeasureTheory Topology Filter Set
open scoped ENNReal Pointwise

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-- The `η`-thickening of a subset of `X₃`: `(V η) • S = {g • x : g ∈ V η, x ∈ S}`. -/
def VThick (η : ℝ) (S : Set X3) : Set X3 :=
  (fun p : SL3 × X3 => p.1 • p.2) '' ((V η) ×ˢ S)

/-- The "`V`-ball" `(V r) • x` around `x`.  For `r -> 0⁺` these form a neighbourhood basis. -/
def Vball (x : X3) (r : ℝ) : Set X3 := (fun u : SL3 => u • x) '' (V r)

/-- `S` has `µ`-thin boundary (Pisa 7.26): the `V η`-thickening of its frontier has measure at
most `c η`. -/
def ThinBdry (μ : Measure X3) (S : Set X3) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ η : ℝ, 0 < η → μ (VThick η (frontier S)) ≤ ENNReal.ofReal (c * η)

theorem VThick_def (η : ℝ) (S : Set X3) :
    VThick η S = (fun p : SL3 × X3 => p.1 • p.2) '' ((V η) ×ˢ S) := rfl

theorem Vball_def (x : X3) (r : ℝ) : Vball x r = (fun u : SL3 => u • x) '' (V r) := rfl

theorem mem_VThick {η : ℝ} {S : Set X3} {z : X3} :
    z ∈ VThick η S ↔ ∃ x ∈ S, ∃ g ∈ V η, g • x = z := by
  constructor
  · rintro ⟨⟨g, x⟩, ⟨hg, hx⟩, rfl⟩
    exact ⟨x, hx, g, hg, rfl⟩
  · rintro ⟨x, hx, g, hg, rfl⟩
    exact ⟨(g, x), ⟨hg, hx⟩, rfl⟩

theorem mem_Vball {x z : X3} {r : ℝ} : z ∈ Vball x r ↔ ∃ u ∈ V r, u • x = z := by
  constructor
  · rintro ⟨u, hu, rfl⟩; exact ⟨u, hu, rfl⟩
  · rintro ⟨u, hu, rfl⟩; exact ⟨u, hu, rfl⟩

/-- The thickening is monotone in the group neighbourhood. -/
theorem VThick_mono_left {η η' : ℝ} (h : η ≤ η') (S : Set X3) : VThick η S ⊆ VThick η' S := by
  rintro z ⟨p, ⟨hp, hpS⟩, rfl⟩
  exact ⟨p, ⟨fun i j => lt_of_lt_of_le (hp i j) h, hpS⟩, rfl⟩

/-- The thickening is monotone in the set. -/
theorem VThick_mono_right {S T : Set X3} (h : S ⊆ T) (η : ℝ) : VThick η S ⊆ VThick η T := by
  rintro z ⟨p, ⟨hp, hpS⟩, rfl⟩
  exact ⟨p, ⟨hp, h hpS⟩, rfl⟩

/-- A set is contained in its own thickenings. -/
theorem subset_VThick {η : ℝ} (hη : 0 < η) (S : Set X3) : S ⊆ VThick η S := by
  intro x hx
  refine ⟨((1 : SL3), x), ⟨?_, hx⟩, by simp⟩
  intro i j
  simp only [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply]
  split_ifs <;> simp [hη]

/-- The frontier is contained in its own thickening. -/
theorem frontier_subset_VThick {η : ℝ} (hη : 0 < η) (S : Set X3) :
    frontier S ⊆ VThick η (frontier S) := subset_VThick hη _

theorem Vball_mono {x : X3} {r r' : ℝ} (h : r ≤ r') : Vball x r ⊆ Vball x r' := by
  rintro z ⟨u, hu, rfl⟩
  exact ⟨u, fun i j => lt_of_lt_of_le (hu i j) h, rfl⟩

/-- Every `V`-ball is open. -/
theorem isOpen_Vball (x : X3) {r : ℝ} (hr : 0 < r) : IsOpen (Vball x r) := by
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective x
  have hset : Vball x r = mkX '' ((fun u : SL3 => u * g) '' (V r)) := by
    rw [← hg]
    ext z
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u * g, ⟨u, hu, rfl⟩, (Work.EKLContract.Lemmas.mkX_mul u g).symm⟩
    · rintro ⟨w, ⟨u, hu, rfl⟩, rfl⟩
      exact ⟨u, hu, Work.EKLContract.Lemmas.mkX_mul u g⟩
  rw [hset]
  exact isOpenMap_mkX _ ((Homeomorph.mulRight g).isOpenMap _ (isOpen_V r))

/-- A `V`-ball of radius `< ρ` sits inside the `V ρ`-ball around the same point, which is the
containment required of the cells in `cut_cells`. -/
theorem Vball_subset_Vball_of_le {x : X3} {r ρ : ℝ} (h : r ≤ ρ) :
    Vball x r ⊆ Vball x ρ := Vball_mono h

/-- The `V ρ`-ball around `mkX g` is a subset of `(V ρ) • mkX g`; stated in the exact form used
by `cut_cells`. -/
theorem Vball_eq_image (g : SL3) (ρ : ℝ) :
    Vball (mkX g) ρ = (fun u : SL3 => u • mkX g) '' (V ρ) := rfl

end Work.EKLC6Core
