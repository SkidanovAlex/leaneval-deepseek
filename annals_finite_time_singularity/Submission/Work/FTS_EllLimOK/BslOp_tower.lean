import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK

theorem BslOp_tower (α : ℝ) {Ψ : ℝ → ℝ → ℝ} {F : ℕ → ℕ → ℝ → ℝ → ℝ}
    (h00 : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 → Ψ z θ = F 0 0 z θ)
    (hdz : ∀ (c d : ℕ), c + d ≤ 1 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      HasDerivAt (fun z' : ℝ => F c d z' θ) (F (c + 1) d z θ / z) z)
    (hdth : ∀ (c d : ℕ), c + d ≤ 1 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      HasDerivAt (fun θ' : ℝ => F c d z θ') (F c (d + 1) z θ / Real.sin (2 * θ)) θ)
    {z θ : ℝ} (hzθ : (z, θ) ∈ Work.FTS.EllipticEst.Q0) :
    Work.Elliptic.bslOp α Ψ z θ
      = -(α ^ 2) * (F 2 0 z θ - F 1 0 z θ) - (α * (5 + α)) * F 1 0 z θ
        - (F 0 2 z θ - 2 * Real.cos (2 * θ) * F 0 1 z θ) / (Real.sin (2 * θ)) ^ 2
        + Real.tan θ * (F 0 1 z θ / Real.sin (2 * θ))
        + (Real.tan θ ^ 2 - 5) * F 0 0 z θ := by
  obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hzθ
  -- the basic local data at `(z,θ)`
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hθmem : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hsin0 : Real.sin (2 * θ) ≠ 0 := by
    have : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
    positivity
  have hcos0 : Real.cos θ ≠ 0 := by
    have h := Real.cos_pos_of_mem_Ioo (show θ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) from
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩)
    positivity
  have hΨ_eq : Ψ z θ = F 0 0 z θ := h00 z θ hzθ
  -- `Ψ` agrees with `F 0 0` near `(z,θ)`, slicewise
  have hnbz : (fun z' : ℝ => Ψ z' θ) =ᶠ[nhds z] (fun z' : ℝ => F 0 0 z' θ) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    exact h00 z' θ ⟨hz', hθ0, hθ1⟩
  have hnbt : (fun θ' : ℝ => Ψ z θ') =ᶠ[nhds θ] (fun θ' : ℝ => F 0 0 z θ') := by
    filter_upwards [isOpen_Ioo.mem_nhds hθmem] with θ' hθ'
    exact h00 z θ' ⟨hz, hθ'.1, hθ'.2⟩
  -- first derivatives of `Ψ` from the tower
  have hpzΨ : Work.Spaces.pz Ψ z θ = F 1 0 z θ / z := by
    have h := (hdz 0 0 (by norm_num) z θ hzθ).congr_of_eventuallyEq hnbz
    simpa only [Work.Spaces.pz] using h.deriv
  have hΨθ : HasDerivAt (fun θ' : ℝ => Ψ z θ') (F 0 1 z θ / Real.sin (2 * θ)) θ :=
    (hdth 0 0 (by norm_num) z θ hzθ).congr_of_eventuallyEq hnbt
  -- the neighbourhood form of `∂_zΨ = F 1 0 / z`, used to differentiate once more
  have hpzΨ_nb : (fun z' : ℝ => Work.Spaces.pz Ψ z' θ) =ᶠ[nhds z]
      (fun z' : ℝ => F 1 0 z' θ / z') := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    have hnb : (fun z'' : ℝ => Ψ z'' θ) =ᶠ[nhds z'] (fun z'' : ℝ => F 0 0 z'' θ) := by
      filter_upwards [isOpen_Ioi.mem_nhds hz'] with z'' hz''
      exact h00 z'' θ ⟨hz'', hθ0, hθ1⟩
    have h := (hdz 0 0 (by norm_num) z' θ ⟨hz', hθ0, hθ1⟩).congr_of_eventuallyEq hnb
    simpa only [Work.Spaces.pz] using h.deriv
  -- `∂_z²Ψ`: differentiate `z' ↦ F 1 0 z' θ / z'`
  have hpz2 : Work.Spaces.pzIter 2 Ψ z θ = (F 2 0 z θ - F 1 0 z θ) / z ^ 2 := by
    have hd : HasDerivAt (fun z' : ℝ => F 1 0 z' θ / z')
        ((F 2 0 z θ / z * z - F 1 0 z θ * 1) / z ^ 2) z :=
      (hdz 1 0 (by norm_num) z θ hzθ).div (hasDerivAt_id z) hz0
    have h2 : HasDerivAt (fun z' : ℝ => Work.Spaces.pz Ψ z' θ)
        ((F 2 0 z θ / z * z - F 1 0 z θ * 1) / z ^ 2) z :=
      hd.congr_of_eventuallyEq hpzΨ_nb
    show deriv (fun z' : ℝ => Work.Spaces.pz Ψ z' θ) z = (F 2 0 z θ - F 1 0 z θ) / z ^ 2
    rw [h2.deriv]
    field_simp
  -- the neighbourhood form of `∂_θΨ = F 0 1 / sin 2θ`
  have hpthΨ_nb : (fun θ' : ℝ => Work.Spaces.pth Ψ z θ') =ᶠ[nhds θ]
      (fun θ' : ℝ => F 0 1 z θ' / Real.sin (2 * θ')) := by
    filter_upwards [isOpen_Ioo.mem_nhds hθmem] with θ' hθ'
    have hnb : (fun θ'' : ℝ => Ψ z θ'') =ᶠ[nhds θ'] (fun θ'' : ℝ => F 0 0 z θ'') := by
      filter_upwards [isOpen_Ioo.mem_nhds (show θ' ∈ Set.Ioo 0 (Real.pi / 2) from hθ')]
        with θ'' hθ''
      exact h00 z θ'' ⟨hz, hθ''.1, hθ''.2⟩
    have h := (hdth 0 0 (by norm_num) z θ' ⟨hz, hθ'.1, hθ'.2⟩).congr_of_eventuallyEq hnb
    simpa only [Work.Spaces.pth] using h.deriv
  -- `∂_θ²Ψ`: differentiate `θ' ↦ F 0 1 z θ' / sin 2θ'`
  have hpth2 : Work.Spaces.pthIter 2 Ψ z θ
      = (F 0 2 z θ - 2 * Real.cos (2 * θ) * F 0 1 z θ) / (Real.sin (2 * θ)) ^ 2 := by
    have hd2 : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (2 * Real.cos (2 * θ)) θ := by
      have h := (Real.hasDerivAt_sin (2 * θ)).comp θ ((hasDerivAt_id θ).const_mul 2)
      exact h.congr_deriv (by ring)
    have hd : HasDerivAt (fun θ' : ℝ => F 0 1 z θ' / Real.sin (2 * θ'))
        ((F 0 2 z θ / Real.sin (2 * θ) * Real.sin (2 * θ)
          - F 0 1 z θ * (2 * Real.cos (2 * θ))) / (Real.sin (2 * θ)) ^ 2) θ :=
      (hdth 0 1 (by norm_num) z θ hzθ).div hd2 hsin0
    have h2 : HasDerivAt (fun θ' : ℝ => Work.Spaces.pth Ψ z θ')
        ((F 0 2 z θ / Real.sin (2 * θ) * Real.sin (2 * θ)
          - F 0 1 z θ * (2 * Real.cos (2 * θ))) / (Real.sin (2 * θ)) ^ 2) θ :=
      hd.congr_of_eventuallyEq hpthΨ_nb
    show deriv (fun θ' : ℝ => Work.Spaces.pth Ψ z θ') θ
      = (F 0 2 z θ - 2 * Real.cos (2 * θ) * F 0 1 z θ) / (Real.sin (2 * θ)) ^ 2
    rw [h2.deriv]
    field_simp
  -- `sec²θ = 1 + tan²θ`
  have htan_sq : (1 : ℝ) / Real.cos θ ^ 2 = 1 + Real.tan θ ^ 2 := by
    rw [Real.tan_eq_sin_div_cos, div_pow]
    field_simp
    nlinarith [Real.sin_sq_add_cos_sq θ]
  -- the `∂_θ(tan θ · Ψ)` term
  have htan : Work.Spaces.pth (fun a b => Real.tan b * Ψ a b) z θ
      = (1 + Real.tan θ ^ 2) * F 0 0 z θ + Real.tan θ * (F 0 1 z θ / Real.sin (2 * θ)) := by
    have hprod : HasDerivAt (fun b : ℝ => Real.tan b * Ψ z b)
        ((1 + Real.tan θ ^ 2) * F 0 0 z θ + Real.tan θ * (F 0 1 z θ / Real.sin (2 * θ))) θ := by
      have h := (Real.hasDerivAt_tan hcos0).mul hΨθ
      refine h.congr_deriv ?_
      rw [htan_sq, hΨ_eq]
    show deriv (fun b : ℝ => Real.tan b * Ψ z b) θ = _
    rw [hprod.deriv]
  -- the substituted operator identity
  have key : -(α ^ 2 * z ^ 2) * Work.Spaces.pzIter 2 Ψ z θ
        - (α * (5 + α) * z) * Work.Spaces.pz Ψ z θ
      + (-(Work.Spaces.pthIter 2 Ψ z θ)
        + Work.Spaces.pth (fun a b => Real.tan b * Ψ a b) z θ - 6 * Ψ z θ)
      = -(α ^ 2) * (F 2 0 z θ - F 1 0 z θ) - (α * (5 + α)) * F 1 0 z θ
        - (F 0 2 z θ - 2 * Real.cos (2 * θ) * F 0 1 z θ) / (Real.sin (2 * θ)) ^ 2
        + Real.tan θ * (F 0 1 z θ / Real.sin (2 * θ))
        + (Real.tan θ ^ 2 - 5) * F 0 0 z θ := by
    rw [hpz2, hpzΨ, hpth2, htan, hΨ_eq]
    field_simp
    ring
  rw [Work.Elliptic.bslOp_apply]
  exact key

end Work.FTS_EllLimOK
