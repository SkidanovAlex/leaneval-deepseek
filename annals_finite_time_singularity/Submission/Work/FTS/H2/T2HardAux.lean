/-
Copyright: work module for the Elgindi finite-time singularity project.

# Auxiliary structural facts for the "hard" part of the `D_z`-transport pairing

This file collects the elementary facts about the operators `D_z = z ∂_z`, `D_θ = sin(2θ) ∂_θ`
which are needed to control the five order-five summands `Hhard α f g` of the pairing
`(f D_z g, g)_{ℋ⁴}` (see `Submission/Work/FTS/H2/T2Defs.lean`):

* `DzIter_mul_angular`: multiplication by an angular factor (a function of `θ` alone)
  commutes with every iterate of `D_z`,
* `mixed_eq_sin_mul'`: consequently every mixed derivative `D_z^j D_θ^{i+1} g` with at least
  one `θ`-derivative carries an explicit factor `sin(2θ)`; this is the vanishing at the
  angular boundary which makes the singular weights `sin(2θ)^{-γ}` integrable,
* `abs_slice_le_boxSup`: the angular slice `θ ↦ H z θ` of a function smooth on a
  neighbourhood of the closed quadrant is bounded on `Iθ`.
-/
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.H2.T2Defs
import Submission.Work.Spaces.HkAux

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

/-! ## Angular factors commute with `D_z` -/

/-- Multiplication by a factor `c θ` depending only on the angle commutes with every
iterate of `D_z = z ∂_z`. -/
theorem DzIter_mul_angular (c : ℝ → ℝ) (h : ℝ → ℝ → ℝ) (j : ℕ) :
    Spaces.DzIter j (fun z θ => c θ * h z θ)
      = fun z θ => c θ * Spaces.DzIter j h z θ := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Spaces.DzIter_succ, ih, Spaces.DzIter_succ]
    funext z θ
    show z * deriv (fun z' => c θ * Spaces.DzIter j h z' θ) z
        = c θ * (z * deriv (fun z' => Spaces.DzIter j h z' θ) z)
    rw [deriv_const_mul_field]
    ring

/-! ## The angular vanishing of the mixed derivatives -/

/-- Every mixed derivative `D_z^j D_θ^{i+1} g` carries an explicit factor `sin(2θ)`: the
operator `D_θ = sin(2θ) ∂_θ` contributes one factor of `sin(2θ)` and the remaining
`D_z`-derivatives act on `∂_θ D_θ^i g` through the angular factor.  (Private: the
pointwise form of the same identity is `Work.FTS.H2.mixed_eq_sin_mul`, proved in
`Submission/Work/FTS/H2/mixed_sin_bound.lean`.) -/
private theorem mixed_eq_sin_mul_fn (g : ℝ → ℝ → ℝ) (j i : ℕ) :
    Spaces.mixed j (i + 1) g
      = fun z θ => Real.sin (2 * θ)
          * Spaces.DzIter j (Spaces.pth (Spaces.DthIter i g)) z θ := by
  have h1 : Spaces.mixed j (i + 1) g
      = Spaces.DzIter j (fun z θ => Real.sin (2 * θ) * Spaces.pth (Spaces.DthIter i g) z θ) := by
    rw [Spaces.mixed, Spaces.DthIter_succ]
    rfl
  rw [h1]
  exact DzIter_mul_angular (fun θ => Real.sin (2 * θ)) (Spaces.pth (Spaces.DthIter i g)) j

/-- The same statement with the `θ`-derivative order written as `i - 1` for `i ≥ 1`. -/
theorem mixed_eq_sin_mul' (g : ℝ → ℝ → ℝ) (j i : ℕ) (hi : 1 ≤ i) :
    Spaces.mixed j i g
      = fun z θ => Real.sin (2 * θ)
          * Spaces.DzIter j (Spaces.pth (Spaces.DthIter (i - 1) g)) z θ := by
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  exact mixed_eq_sin_mul_fn g j i'

/-! ## Bounds for the angular slices -/

/-- The θ-slice of a function which is smooth on a neighbourhood of the closed quadrant
is bounded on the angular interval `Iθ`. -/
theorem abs_slice_le_boxSup (H : ℝ → ℝ → ℝ) (hsm : Spaces.SmoothNbhd H) {z : ℝ}
    (hz : z ∈ Spaces.Iz) : ∀ θ ∈ Spaces.Iθ, |H z θ| ≤ Spaces.boxSup z H := by
  have hcont : ContinuousOn (Function.uncurry H) (Set.Icc 0 z ×ˢ Spaces.Iθ) :=
    Spaces.continuousOn_box_of_contDiffOn hsm
  have hb : BddAbove (Spaces.boxSet z H) := Spaces.bddAbove_boxSup_of_continuousOn hcont
  intro θ hθ
  exact Spaces.le_boxSup hb ⟨hz, le_refl z⟩ hθ

/-! ## The five weights and the five summands of `Hhard` -/

/-- `Thard g k` is `mixed (4 - k) k g`, uniformly in `k : Fin 5`. -/
theorem Thard_eq_mixed (g : ℝ → ℝ → ℝ) (k : Fin 5) :
    Thard g k = fun z θ => Spaces.mixed (4 - k.val) k.val g z θ := by
  fin_cases k <;> rfl

/-- The angular weight of the `k`-th hard summand is `sin(2θ)^{-η}` for `k = 0` and
`sin(2θ)^{-γ}` otherwise. -/
theorem sghard_eq (α : ℝ) (k : Fin 5) :
    sghard α k = fun θ => (Real.sin (2 * θ)) ^ (-(if k.val = 0 then Spaces.eta else Spaces.gam α)) := by
  fin_cases k <;> rfl

theorem sghard_nonneg (α : ℝ) (k : Fin 5) {θ : ℝ} (hθ : θ ∈ Spaces.Iθ) : 0 ≤ sghard α k θ := by
  have hsin : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  fin_cases k <;> simp only [sghard] <;> exact Real.rpow_nonneg hsin _

end Work.FTS.H2
