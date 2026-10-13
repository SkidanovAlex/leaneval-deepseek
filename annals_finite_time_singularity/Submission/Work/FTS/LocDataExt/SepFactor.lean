/-
# `Work.FTS.LocDataExt.SepFactor` — separability of the iterated operators `D_z`, `D_θ`

The perturbation of the localised-data extension is *separable*,
`locG α L β (hLoc α) = locR α L β (z)·Γ(θ)` (`Defs.lean`), and so is the far part
`zfar L F_* = (α/c)·zfarR L z·Γ(θ)`.  This module records the resulting splitting of the
mixed operators

  `D_z^j D_θ^i (ρ(z)·Γ(θ)) = (D_z^j ρ)(z)·(D_θ^i Γ)(θ)`,

which is unconditional in differentiability (Lean's `deriv` is totalised and both factors
enter only through `deriv_const_mul`/`deriv_mul_const`): it is the form in which every
pointwise estimate of the chapter is applied.

Also here: the congruence of `D_z`-iterates under *eventual* equality in `z` (the tool that
transports bounds from `FM.Fstar` to the far factor `zfarR L`, which agrees with `FM.Fstar`
beyond `2L` and vanishes below `L`), the `θ`-independence of `D_z^j ρ`, and the elementary
"eventually equal to a constant multiple" facts for `locR`.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.LocDataExt.Defs
import Submission.Work.FTS.LocData.HkFstarDefs
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocDataExt

set_option autoImplicit false

/-! ## Separability of the iterated operators -/

/-- `D_z^j` of a separable datum `ρ(z)·Γ(θ)` only differs the radial factor. -/
theorem DzIter_sepGam (α : ℝ) (ρ : ℝ → ℝ) (j : ℕ) :
    Work.Spaces.DzIter j (fun z θ => ρ z * Work.Spaces.Gam α θ)
      = fun z θ => Work.Spaces.DzIter j (fun z _ => ρ z) z θ * Work.Spaces.Gam α θ := by
  have h := Work.FTS.LocData.DzIter_mul_theta_factor j (fun θ => Work.Spaces.Gam α θ)
    (fun z _ => ρ z)
  rw [show (fun z θ : ℝ => ρ z * Work.Spaces.Gam α θ)
      = (fun z θ : ℝ => Work.Spaces.Gam α θ * ρ z) from (by funext z θ; exact mul_comm _ _), h]
  funext z θ
  ring

/-- `D_θ^i` of a separable datum `ρ(z)·Γ(θ)` only differs the angular factor. -/
theorem DthIter_sepGam (α : ℝ) (ρ : ℝ → ℝ) (i : ℕ) :
    Work.Spaces.DthIter i (fun z θ => ρ z * Work.Spaces.Gam α θ)
      = fun z θ => ρ z * Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ := by
  rw [Work.FTS.LocData.ZFBase.DthIter_mul_left_z i ρ (fun _ θ' => Work.Spaces.Gam α θ')]
  funext z θ
  rw [Work.FTS.LocData.DthIter_gamFn_z_indep α i z 0 θ]

/-- **The mixed derivatives of a separable datum split**: for `f z θ = ρ z · Γ θ`,

  `D_z^j D_θ^i f z θ = (D_z^j ρ)(z)·(D_θ^i Γ)(θ)`. -/
theorem mixed_sepGam (α : ℝ) (ρ : ℝ → ℝ) (j i : ℕ) :
    Work.Spaces.mixed j i (fun z θ => ρ z * Work.Spaces.Gam α θ)
      = fun z θ => Work.Spaces.DzIter j (fun z _ => ρ z) z θ
          * Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ := by
  rw [Work.Spaces.mixed, DthIter_sepGam α ρ i]
  have h := Work.FTS.LocData.DzIter_mul_theta_factor j
    (fun θ => Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) (fun z _ => ρ z)
  rw [show (fun z θ : ℝ => ρ z
        * Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ)
      = (fun z θ : ℝ => Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ * ρ z)
      from (by funext z θ; exact mul_comm _ _), h]
  funext z θ
  ring

/-- **`D_z^j ρ` does not depend on the angle.** -/
theorem DzIter_z_only_apply (ρ : ℝ → ℝ) (j : ℕ) (z θ : ℝ) :
    Work.Spaces.DzIter j (fun z _ => ρ z) z θ = Work.Spaces.DzIter j (fun z _ => ρ z) z 0 := by
  induction j generalizing z with
  | zero => rfl
  | succ j ih =>
      show Work.Spaces.Dz (Work.Spaces.DzIter j (fun z _ => ρ z)) z θ
        = Work.Spaces.Dz (Work.Spaces.DzIter j (fun z _ => ρ z)) z 0
      simp only [Work.Spaces.Dz, Work.Spaces.pz]
      congr 1
      exact Filter.EventuallyEq.deriv_eq (Eventually.of_forall fun w => ih w)

/-- Scalar multiples pass through `D_z`-iterates. -/
theorem DzIter_const_mul (c : ℝ) (f : Fn) (j : ℕ) :
    Work.Spaces.DzIter j (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.DzIter j f z θ := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [Work.Spaces.DzIter_succ, ih, Work.Spaces.DzIter_succ]
      funext z θ
      simp only [Work.Spaces.Dz, Work.Spaces.pz]
      rw [deriv_const_mul_field]
      ring

/-! ## Congruence of the iterates under eventual equality in `z` -/

/-- `D_z`-iterates agree for functions which agree on a neighbourhood of `z`, uniformly in `θ`. -/
theorem eventDzIter_congr {f g : Fn} {z : ℝ}
    (h : ∀ᶠ z' in 𝓝 z, ∀ θ' : ℝ, f z' θ' = g z' θ') (j : ℕ) :
    ∀ᶠ z' in 𝓝 z, ∀ θ' : ℝ, Work.Spaces.DzIter j f z' θ' = Work.Spaces.DzIter j g z' θ' := by
  induction j with
  | zero => exact h
  | succ j ih =>
      rcases mem_nhds_iff.mp ih with ⟨U, hU, hUopen, hzU⟩
      filter_upwards [hUopen.mem_nhds hzU] with z' hz'
      intro θ'
      have hev : (fun w : ℝ => Work.Spaces.DzIter j f w θ') =ᶠ[𝓝 z']
          (fun w : ℝ => Work.Spaces.DzIter j g w θ') :=
        Filter.eventually_of_mem (hUopen.mem_nhds hz') (fun w hw => hU hw θ')
      simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
      rw [hev.deriv_eq]

/-- Pointwise form of `eventDzIter_congr`. -/
theorem eq_of_eventuallyEq_nhds {g h : ℝ → ℝ} {z : ℝ} (hz : g =ᶠ[𝓝 z] h) : g z = h z :=
  Filter.EventuallyEq.eq_of_nhds hz

theorem DzIter_congr_of_eventuallyEq {f g : Fn} {z θ : ℝ}
    (h : ∀ᶠ z' in 𝓝 z, ∀ θ' : ℝ, f z' θ' = g z' θ') (j : ℕ) :
    Work.Spaces.DzIter j f z θ = Work.Spaces.DzIter j g z θ := by
  have h' : (fun z' : ℝ => Work.Spaces.DzIter j f z' θ) =ᶠ[𝓝 z]
      (fun z' : ℝ => Work.Spaces.DzIter j g z' θ) :=
    (eventDzIter_congr h j).mono (fun z' hz' => hz' θ)
  exact eq_of_eventuallyEq_nhds (g := fun z' : ℝ => Work.Spaces.DzIter j f z' θ)
    (h := fun z' : ℝ => Work.Spaces.DzIter j g z' θ) (z := z) h'

/-- Pointwise form for functions of `z` alone. -/
theorem DzIter_z_congr_of_eventuallyEq {ρ σ : ℝ → ℝ} {z : ℝ}
    (h : ∀ᶠ z' in 𝓝 z, ρ z' = σ z') (j : ℕ) (θ : ℝ) :
    Work.Spaces.DzIter j (fun z _ => ρ z) z θ = Work.Spaces.DzIter j (fun z _ => σ z) z θ :=
  DzIter_congr_of_eventuallyEq (h.mono (fun z' hz' => fun _ => hz')) j

/-! ## The radial factor `locR` near the two ends of `(0,∞)` -/

/-- `locR` vanishes identically on a neighbourhood of any `z ∈ (0, min L (3/4))`. -/
theorem locR_eventuallyEq_zero {α L β z : ℝ} (hL : 0 < L) (hz0 : 0 < z) (hzL : z < L)
    (hzb : z < 3 / 4) : ∀ᶠ z' in 𝓝 z, locR α L β z' = 0 := by
  filter_upwards [isOpen_Ioo.mem_nhds (show z ∈ Set.Ioo (0 : ℝ) L from ⟨hz0, hzL⟩),
    isOpen_Ioo.mem_nhds (show z ∈ Set.Ioo (0 : ℝ) (3 / 4) from ⟨hz0, hzb⟩)] with z' hz' hz''
  exact locR_eq_zero_of_le hL (le_of_lt hz'.1) (le_of_lt hz'.2) (le_of_lt hz''.2)

/-- Beyond `max (2L) (7/4)`, `locR` agrees with the (rescaled) plain profile
`-(α/c)·FM.Fstar`. -/
theorem locR_eventuallyEq_far {α L β z : ℝ} (hL : 0 < L) (hz : 2 * L < z) (hzb : 7 / 4 < z) :
    ∀ᶠ z' in 𝓝 z, locR α L β z' = -(α / Work.Spaces.c α) * Work.FM.Fstar z' := by
  filter_upwards [isOpen_Ioi.mem_nhds hz, isOpen_Ioi.mem_nhds hzb] with z' hz' hz''
  rw [locR_apply, zfarR_eq_FM_Fstar_of_ge hL (le_of_lt hz'), bumpZ_eq_zero_of_ge (le_of_lt hz'')]
  ring

end Work.FTS.LocDataExt
