/-
Copyright: subproject `Submission/Work/Implosion/` of `mandelbar_not_path_connected`.

# The local normal form of parabolic implosion (Hubbard–Schleicher §4)

This file sets up the *local model* around a simple parabolic periodic point whose
period is odd, in the form used in Hubbard–Schleicher, *Multicorns are not path
connected*, arXiv:1209.1753, §4 (Parabolic Perturbations).

Proposition 4.1 of that paper says: after a perturbation of the parameter, the
holomorphic second return map `p_c^{∘2k}` is, in a suitable local coordinate `ζ`,
of the form

  `f(ζ) = ζ + (ζ² − a²)·h(ζ)`,          `‖h(ζ) − 1‖ < ε` on the domain,

where `±a` are the two (simple) fixed points into which the parabolic fixed point
splits.  This file defines that normal form and proves its elementary API:
the two fixed points, the exact factorisation of `f(ζ) ∓ a`, the derivative, and
the behaviour of the normal form on the cut `ℓ = [−a,a]` that separates the
incoming from the outgoing petal.

Everything downstream (the Écalle coordinate `Ecalle.lean`, the `u`-model
`Model.lean`, the transit phase `Phase.lean`, the fundamental domain and the
Écalle cylinder) is stated for this normal form.
-/
import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Implosion

open Complex

/-! ## The normal form -/

/-- The **local normal form** of Hubbard–Schleicher, Prop. 4.1:
`f(ζ) = ζ + (ζ² − a²)·h(ζ)`.  Its critical point is `0` and its two simple
fixed points are `±a` (whenever `h(±a) ≠ 0`). -/
noncomputable def normalForm (a : ℂ) (h : ℂ → ℂ) (ζ : ℂ) : ℂ :=
  ζ + (ζ ^ 2 - a ^ 2) * h ζ

/-- `h` is `ε`-close to the constant function `1` on the set `U`.  This is the
hypothesis `|h − 1| < ε` of HS Prop. 4.1. -/
def EpsilonCloseOn (h : ℂ → ℂ) (U : Set ℂ) (ε : ℝ) : Prop :=
  ∀ ζ ∈ U, ‖h ζ - 1‖ ≤ ε

/-- The parametrisation `t ↦ t·a` of the cut `ℓ = [−a,a]`. -/
def cutPt (a : ℂ) (t : ℝ) : ℂ := (t : ℂ) * a

/-- The **cut** `ℓ = [−a,a]`: the straight segment joining the two fixed points of
the normal form.  It separates the incoming from the outgoing petal. -/
def cut (a : ℂ) : Set ℂ := cutPt a '' Set.Icc (-1 : ℝ) 1

/-- The image arc `f(ℓ)`, joining `a` to `−a`. -/
noncomputable def imageCut (a : ℂ) (h : ℂ → ℂ) : Set ℂ :=
  normalForm a h '' cut a

/-! ## The two fixed points -/

@[simp] theorem normalForm_apply_cutPt (a : ℂ) (h : ℂ → ℂ) (t : ℝ) :
    normalForm a h (cutPt a t)
      = cutPt a t + (((t : ℂ) ^ 2 - 1) * a ^ 2) * h (cutPt a t) := by
  simp only [normalForm, cutPt]
  ring

theorem normalForm_fixed_left (a : ℂ) (h : ℂ → ℂ) : normalForm a h a = a := by
  simp [normalForm]

theorem normalForm_fixed_right (a : ℂ) (h : ℂ → ℂ) : normalForm a h (-a) = -a := by
  simp [normalForm]

/-- The factorisation behind everything: `f(ζ) − a = (ζ − a)(1 + (ζ+a)h(ζ))`. -/
theorem normalForm_sub_left (a : ℂ) (h : ℂ → ℂ) (ζ : ℂ) :
    normalForm a h ζ - a = (ζ - a) * (1 + (ζ + a) * h ζ) := by
  simp only [normalForm]; ring

/-- `f(ζ) + a = (ζ + a)(1 + (ζ−a)h(ζ))`. -/
theorem normalForm_add_left (a : ℂ) (h : ℂ → ℂ) (ζ : ℂ) :
    normalForm a h ζ + a = (ζ + a) * (1 + (ζ - a) * h ζ) := by
  simp only [normalForm]; ring

/-- The critical point of the normal form is `0` (it is the critical point of the
quadratic factor `ζ² − a²`), independently of `h`. -/
theorem normalForm_zero (a : ℂ) (h : ℂ → ℂ) : normalForm a h 0 = -(a ^ 2) * h 0 := by
  simp [normalForm]

/-! ## Derivative -/

theorem hasDerivAt_normalForm (a : ℂ) (h h' : ℂ → ℂ) (ζ : ℂ) (hh : HasDerivAt h (h' ζ) ζ) :
    HasDerivAt (normalForm a h) (1 + 2 * ζ * h ζ + (ζ ^ 2 - a ^ 2) * h' ζ) ζ := by
  have h1 : HasDerivAt (fun ζ : ℂ => ζ ^ 2 - a ^ 2) (2 * ζ) ζ := by
    simpa using (hasDerivAt_id ζ).pow 2 |>.sub_const (a ^ 2)
  have := (hasDerivAt_id ζ).add (h1.mul hh)
  convert this using 1
  · funext x; simp [normalForm, Pi.add_apply]
  · ring

/-- The multiplier of the fixed point `a`. -/
theorem hasDerivAt_normalForm_at_left (a : ℂ) (h h' : ℂ → ℂ) (hh : HasDerivAt h (h' a) a) :
    HasDerivAt (normalForm a h) (1 + 2 * a * h a) a := by
  simpa using hasDerivAt_normalForm a h h' a hh

/-- The multiplier of the fixed point `−a`. -/
theorem hasDerivAt_normalForm_at_right (a : ℂ) (h h' : ℂ → ℂ)
    (hh : HasDerivAt h (h' (-a)) (-a)) :
    HasDerivAt (normalForm a h) (1 - 2 * a * h (-a)) (-a) := by
  have := hasDerivAt_normalForm a h h' (-a) hh
  convert this using 1
  ring

/-! ## The cut and its image -/

theorem cutPt_mem_cut (a : ℂ) (t : ℝ) (ht : t ∈ Set.Icc (-1:ℝ) 1) : cutPt a t ∈ cut a :=
  ⟨t, ht, rfl⟩

@[simp] theorem cutPt_one (a : ℂ) : cutPt a 1 = a := by simp [cutPt]

@[simp] theorem cutPt_neg_one (a : ℂ) : cutPt a (-1) = -a := by simp [cutPt]

@[simp] theorem cutPt_zero (a : ℂ) : cutPt a 0 = 0 := by simp [cutPt]

theorem mem_cut_iff (a : ℂ) (ζ : ℂ) :
    ζ ∈ cut a ↔ ∃ t : ℝ, t ∈ Set.Icc (-1:ℝ) 1 ∧ ζ = (t : ℂ) * a :=
  ⟨fun ⟨t, ht, h⟩ => ⟨t, ht, h.symm⟩, fun ⟨t, ht, h⟩ => ⟨t, ht, h.symm⟩⟩

theorem left_mem_cut (a : ℂ) : a ∈ cut a := ⟨1, by norm_num, by simp⟩

theorem right_mem_cut (a : ℂ) : -a ∈ cut a := ⟨-1, by norm_num, by simp⟩

/-- Points of the interior of the cut are exactly `t·a` with `|t| < 1`. -/
theorem mem_cut_interior (a : ℂ) (t : ℝ) (ht : t ∈ Set.Ioo (-1:ℝ) 1) : cutPt a t ∈ cut a :=
  cutPt_mem_cut a t (Set.Ioo_subset_Icc_self ht)

theorem left_mem_imageCut (a : ℂ) (h : ℂ → ℂ) : a ∈ imageCut a h :=
  ⟨a, left_mem_cut a, normalForm_fixed_left a h⟩

theorem right_mem_imageCut (a : ℂ) (h : ℂ → ℂ) : -a ∈ imageCut a h :=
  ⟨-a, right_mem_cut a, normalForm_fixed_right a h⟩

end Work.Implosion
