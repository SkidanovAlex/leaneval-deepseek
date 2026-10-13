import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_EllLimOK.BslOp_tower
import Submission.Work.FTS.StrongEps.LocUnif.mixed_partials_of_smoothOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK

theorem tower_jet_identities {Ψ : ℝ → ℝ → ℝ} {F : ℕ → ℕ → ℝ → ℝ → ℝ}
    (h00 : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 → Ψ z θ = F 0 0 z θ)
    (hdz : ∀ (c d : ℕ), c + d ≤ 1 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      HasDerivAt (fun z' : ℝ => F c d z' θ) (F (c + 1) d z θ / z) z)
    (hdth : ∀ (c d : ℕ), c + d ≤ 1 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      HasDerivAt (fun θ' : ℝ => F c d z θ') (F c (d + 1) z θ / Real.sin (2 * θ)) θ) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.Spaces.pz Ψ z θ = F 1 0 z θ / z ∧
      Work.Spaces.pth Ψ z θ = F 0 1 z θ / Real.sin (2 * θ) ∧
      Work.Spaces.pzIter 2 Ψ z θ = (F 2 0 z θ - F 1 0 z θ) / z ^ 2 ∧
      Work.Spaces.pthIter 2 Ψ z θ
        = (F 0 2 z θ - 2 * Real.cos (2 * θ) * F 0 1 z θ) / (Real.sin (2 * θ)) ^ 2 := by
  intro z θ hzθ
  obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hzθ
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hθmem : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hsin0 : Real.sin (2 * θ) ≠ 0 := by
    have : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
    positivity
  -- `Ψ` agrees with `F 0 0` slicewise near `(z,θ)`
  have hnbz : (fun z' : ℝ => Ψ z' θ) =ᶠ[nhds z] (fun z' : ℝ => F 0 0 z' θ) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    exact h00 z' θ ⟨hz', hθ0, hθ1⟩
  have hnbt : (fun θ' : ℝ => Ψ z θ') =ᶠ[nhds θ] (fun θ' : ℝ => F 0 0 z θ') := by
    filter_upwards [isOpen_Ioo.mem_nhds hθmem] with θ' hθ'
    exact h00 z θ' ⟨hz, hθ'.1, hθ'.2⟩
  -- first derivatives
  have hpzΨ : Work.Spaces.pz Ψ z θ = F 1 0 z θ / z := by
    have h := (hdz 0 0 (by norm_num) z θ hzθ).congr_of_eventuallyEq hnbz
    simpa only [Work.Spaces.pz] using h.deriv
  have hpthΨ : Work.Spaces.pth Ψ z θ = F 0 1 z θ / Real.sin (2 * θ) := by
    have h := (hdth 0 0 (by norm_num) z θ hzθ).congr_of_eventuallyEq hnbt
    simpa only [Work.Spaces.pth] using h.deriv
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
  exact ⟨hpzΨ, hpthΨ, hpz2, hpth2⟩

end Work.FTS_EllLimOK
