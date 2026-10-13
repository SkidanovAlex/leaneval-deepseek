import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.Gamma_WlInf

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.TracesAux

/-! ## Two structural facts about `DthIter` on `z`-independent data

`Work.Spaces.DthIter_decomp` separates the angular and the radial variable; for a function of
`θ` alone (multiplied by the constant radial factor `1`) it identifies the two-variable
iterate `DthIter a` with the one-variable iterate `dthU^[a]`, where
`dthU φ = sin(2·) · φ'`. -/

/-- `D_θ^a` of a function of `θ` alone is the one-variable iterate `dthU^[a]`. -/
theorem DthIter_z_indep (a : ℕ) (g : ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.DthIter a (fun _ θ' => g θ') z θ = Work.Spaces.dthU^[a] g θ := by
  have h : (fun (_ : ℝ) (θ : ℝ) => g θ) = (fun (z : ℝ) (θ : ℝ) => g θ * (1 : ℝ)) := by
    funext z θ; ring
  rw [h, Work.Spaces.DthIter_decomp]
  ring

/-- **`Tfun j α` is bounded on the angular interval `Iθ`.**  This is continuity plus
compactness of `Iθ = [0, π/2]`; the bound depends on `j` and on `α`, which is all that the
chain rule identity `D_θ^{j+1}Γ = α·Tfun j α·Γ` needs.  (No restriction on `α > 0` is used:
`Tfun j α` is smooth for every real `α`.) -/
theorem exists_Tfun_bound (α : ℝ) (j : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ θ ∈ Work.Spaces.Iθ, |Work.Spaces.Tfun j α θ| ≤ M := by
  have hcont : ContinuousOn (Work.Spaces.Tfun j α) Work.Spaces.Iθ :=
    (Work.Spaces.Tfun_smooth j α).continuous.continuousOn
  obtain ⟨C, hC⟩ := IsCompact.exists_bound_of_continuousOn isCompact_Icc hcont
  refine ⟨max C 0, le_max_right _ _, fun θ hθ => ?_⟩
  have h := hC θ hθ
  rw [Real.norm_eq_abs] at h
  exact le_trans h (le_max_left _ _)

/-- **Every `D_θ`-iterate of the angular profile `Γ(θ) = (sin θ cos²θ)^{α/3}` is dominated by
`Γ` itself**, for `α > 0`.

Here `D_θ = sin(2θ)∂_θ` (`Work.Spaces.Dth`), so `D_θ^a Γ = Γ·q_a` with
`q_1 = (2α/3)(cos²θ - 2sin²θ) = (2α/3)(1 - 3sin²θ)`, and inductively `q_{a+1}` is again a
polynomial in `sin²θ` (the factor `sin(2θ)` in `D_θ` exactly absorbs the chain-rule factor);
hence `q_a` is continuous on `[0,π/2]` and bounded by some `C > 0` independent of `θ`.

This is the input of the *angular* boundary traces of the separated product
`(z,θ) ↦ Γ(θ)·r(z)`: the trace weighs the `a`-th iterate by `sin(2θ)^{1-γ}` and needs the
product to vanish at `θ = 0, π/2⁻`, where `sin(2θ)^{1-γ}Γ² ~ sin(2θ)^{1-γ+2α/3}` with
`1-γ+2α/3 = α(2/3 - 1/10) > 0` for `α > 0`. -/
theorem abs_DthIter_Gam_le {α : ℝ} (hα : 0 < α) (a : ℕ) (ha : a ≤ 8) :
    ∃ C : ℝ, 0 < C ∧ ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DthIter a (fun _ θ' => Work.Spaces.Gam α θ') 0 θ| ≤ C * Work.Spaces.Gam α θ := by
  rcases Nat.eq_zero_or_pos a with h0 | hpos
  · -- `a = 0`: the iterate is `Γ` itself, and `Γ ≤ 1` on `Iθ`.
    subst h0
    refine ⟨1, one_pos, ?_⟩
    intro θ hθ0 hθ1
    have hmem : θ ∈ Work.Spaces.Iθ := ⟨hθ0.le, hθ1.le⟩
    have hG := (Work.Spaces.Gam_bounds α θ hα hmem).1
    rw [Work.Spaces.DthIter_zero, abs_of_nonneg hG]
    linarith
  · -- `a ≥ 1`: `D_θ^a Γ = α·Tfun (a-1) α·Γ` on `(0,π/2)`, and `Tfun (a-1) α` is bounded.
    obtain ⟨M, hM0, hM⟩ := exists_Tfun_bound α (a - 1)
    refine ⟨α * M + 1, by positivity, ?_⟩
    intro θ hθ0 hθ1
    have hmem : θ ∈ Work.Spaces.Iθ := ⟨hθ0.le, hθ1.le⟩
    have hG := (Work.Spaces.Gam_bounds α θ hα hmem).1
    rw [DthIter_z_indep a (fun θ' => Work.Spaces.Gam α θ') 0 θ]
    have hb := Work.Spaces.dthU_iter_Gam_abs_bound a hpos α hα M hM θ hmem
    have hAM : 0 ≤ α * M := mul_nonneg hα.le hM0
    calc |Work.Spaces.dthU^[a] (fun t => Work.Spaces.Gam α t) θ|
        ≤ α * M * Work.Spaces.Gam α θ := hb
      _ ≤ (α * M + 1) * Work.Spaces.Gam α θ := by nlinarith [hG, hAM]

end Work.FTS.StrongEps.EpsE4Thr.TracesAux
