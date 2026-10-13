/-
Copyright: work module for the Elgindi finite-time singularity project.

# Auxiliary material for the transport estimate `Transport1`

This file contains the small vocabulary shared by the proof of Elgindi's Lemma
`Transport1` (§`H2`, tex 1099) and its supporting lemmas:

* `supAbsTh u z` — the supremum of `|u z θ|` over `θ ∈ [0,π/2]` at a *fixed* `z`.  This is
  the `θ`-direction analogue of `Work.Spaces.supAbs` (which takes the supremum over the
  whole quadrant), and is the natural form of the *angular* Hardy inequality of the paper
  (`infinity_separated`): after `HardyZ` has been applied in the radial variable one is
  left with a supremum over `θ`, for each fixed `z`, which has to be integrated against
  `w(z)² dz`.
* `DthIter_Dth` and `mixed_Dth` — the bookkeeping identities
  `D_θ^n(D_θ g) = D_θ^{n+1} g` and `D_z^j D_θ^i (D_θ g) = D_z^j D_θ^{i+1} g` used to turn
  the Leibniz expansion of `D_z^j D_θ^i (f · D_θ g)` into an expansion in terms of
  derivatives of `g`.
* `smoothNbhd_mul` and `SmoothInt_of_SmoothNbhd` — closure of the regularity hypotheses.
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.H2.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

set_option autoImplicit false

/-! ## The angular slice supremum -/

/-- `supAbsTh u z` is the supremum of `|u z θ|` over `θ ∈ [0,π/2]`, at the fixed radial
variable `z`.  It is the angular analogue of `Work.Spaces.supAbs`. -/
def supAbsTh (u : ℝ → ℝ → ℝ) (z : ℝ) : ℝ := sSup {y : ℝ | ∃ θ ∈ Spaces.Iθ, y = |u z θ|}

/-- The set whose supremum is `supAbsTh u z`. -/
theorem supAbsTh_def (u : ℝ → ℝ → ℝ) (z : ℝ) :
    supAbsTh u z = sSup {y : ℝ | ∃ θ ∈ Spaces.Iθ, y = |u z θ|} := rfl

/-- A pointwise bound by the angular slice supremum, from the boundedness of the slice. -/
theorem abs_le_supAbsTh {u : ℝ → ℝ → ℝ} {z θ : ℝ} (hθ : θ ∈ Spaces.Iθ)
    (h : BddAbove {y : ℝ | ∃ θ ∈ Spaces.Iθ, y = |u z θ|}) : |u z θ| ≤ supAbsTh u z :=
  le_csSup h ⟨θ, hθ, rfl⟩

/-- Bound of the angular slice supremum from a pointwise bound. -/
theorem supAbsTh_le {u : ℝ → ℝ → ℝ} {z C : ℝ}
    (h : ∀ θ ∈ Spaces.Iθ, |u z θ| ≤ C) : supAbsTh u z ≤ C :=
  csSup_le ⟨|u z 0|, 0, Spaces.zero_mem_Iθ, rfl⟩ (fun y hy => by
    rcases hy with ⟨θ, hθ, rfl⟩
    exact h θ hθ)

/-- The angular slice supremum is nonnegative. -/
theorem supAbsTh_nonneg {u : ℝ → ℝ → ℝ} {z : ℝ}
    (h : BddAbove {y : ℝ | ∃ θ ∈ Spaces.Iθ, y = |u z θ|}) : 0 ≤ supAbsTh u z :=
  le_trans (abs_nonneg _) (le_csSup h ⟨0, Spaces.zero_mem_Iθ, rfl⟩)

/-- The angular slice supremum of `u` is bounded by the full quadrant supremum of `u`. -/
theorem supAbsTh_le_supAbs (u : ℝ → ℝ → ℝ) {z : ℝ} (hz : z ∈ Spaces.Iz)
    (h : Spaces.SupFinite u) : supAbsTh u z ≤ Spaces.supAbs u :=
  supAbsTh_le fun θ hθ => Spaces.abs_le_supAbs hz hθ h

/-! ## Regularity closure -/

/-- The pointwise product of two functions smooth on a neighbourhood of the closed quadrant
is again smooth on a neighbourhood of the closed quadrant. -/
theorem smoothNbhd_mul {f g : ℝ → ℝ → ℝ} (hf : Spaces.SmoothNbhd f)
    (hg : Spaces.SmoothNbhd g) : Spaces.SmoothNbhd (fun z θ => f z θ * g z θ) := by
  show ContDiffOn ℝ ⊤ (Function.uncurry (fun z θ : ℝ => f z θ * g z θ)) _
  have h : Function.uncurry (fun z θ : ℝ => f z θ * g z θ)
      = Function.uncurry f * Function.uncurry g := rfl
  rw [h]
  exact hf.mul hg

/-- `SmoothNbhd` implies `SmoothInt`. -/
theorem SmoothInt_of_SmoothNbhd {u : ℝ → ℝ → ℝ} (h : Spaces.SmoothNbhd u) :
    Spaces.SmoothInt u := by
  refine ⟨h.mono ?_, ?_⟩
  · rintro ⟨z, θ⟩ ⟨hz, hθ⟩
    exact ⟨hz, by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  · intro θ hθ
    have hθ' : θ ∈ Set.Ioo (-1) (π / 2 + 1) :=
      ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
    have hmap : Set.MapsTo (fun z : ℝ => (z, θ)) (Set.Ioi (-1))
        (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (π / 2 + 1)) := fun z hz => ⟨hz, hθ'⟩
    exact h.comp (contDiffOn_id.prodMk contDiffOn_const) hmap

/-! ## Iterated `D_θ` against an extra `D_θ` -/

/-- `D_θ^n (D_θ g) = D_θ^{n+1} g`. -/
theorem DthIter_Dth (n : ℕ) (g : ℝ → ℝ → ℝ) :
    Spaces.DthIter n (Spaces.Dth g) = Spaces.DthIter (n + 1) g := by
  induction n with
  | zero => rfl
  | succ k ih =>
      rw [Spaces.DthIter_succ k (Spaces.Dth g), ih]
      exact (Spaces.DthIter_succ (k + 1) g).symm

/-- `D_z^j D_θ^i (D_θ g) = D_z^j D_θ^{i+1} g`, i.e. `mixed j i (D_θ g) = mixed j (i+1) g`. -/
theorem mixed_Dth (j i : ℕ) (g : ℝ → ℝ → ℝ) :
    Spaces.mixed j i (Spaces.Dth g) = Spaces.mixed j (i + 1) g := by
  rw [Spaces.mixed, Spaces.mixed, DthIter_Dth]

/-- `D_z^j (D_θ g) = mixed j 1 g`. -/
theorem DzIter_Dth (j : ℕ) (g : ℝ → ℝ → ℝ) :
    Spaces.DzIter j (Spaces.Dth g) = Spaces.mixed j 1 g := rfl

end Work.FTS.H2
