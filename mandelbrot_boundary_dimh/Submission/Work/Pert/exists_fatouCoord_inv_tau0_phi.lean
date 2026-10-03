import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Pert.Basic
import Submission.Work.Pert.image_cover
import Submission.Work.Pert.deriv_psi0_close
import Submission.Work.Pert.fatouCoord_comp_tau0
import Submission.Work.Pert.inv_close_of_deriv_close

namespace Work.Pert

open Filter Metric Set
open scoped Topology

noncomputable section

/-- `τ₀` is an involution (the value at `0` is Lean's junk `0⁻¹ = 0`, which is fixed by `τ₀`). -/
private lemma tau0_tau0 (x : ℂ) : MandelDim.tau0 (MandelDim.tau0 x) = x := by
  simp only [MandelDim.tau0, div_eq_mul_inv]
  rw [mul_inv, inv_neg, inv_one, inv_inv]
  ring

/-- `deriv` is the junk value `0` where the function is not complex differentiable, so the bound
`‖deriv Φ u - 1‖ ≤ 1/2` forces differentiability at `u`. -/
private lemma differentiableAt_of_norm_deriv_sub_one_le {Φ : ℂ → ℂ} {u : ℂ}
    (h : ‖deriv Φ u - 1‖ ≤ 1 / 2) : DifferentiableAt ℂ Φ u := by
  by_contra hd
  have h0 : deriv Φ u = 0 := deriv_zero_of_not_differentiableAt hd
  rw [h0] at h
  norm_num at h

/-- The unperturbed limit coordinate on the `Φ₋` side, as the local inverse of `tau0 ∘ φ`:
for `w₀` a deep point of Shishikura's sector (room `ball w₀ (‖w₀‖/4) ⊆ QLeft ξ₀`) at which
`tau0 ∘ φ` is anchored (`‖tau0 (φ w₀) - w₀‖ ≤ ‖w₀‖/40`) and has `‖(tau0 ∘ φ)' - 1‖ ≤ 1/2` on that
ball, the image `ball (tau0 (φ w₀)) (‖w₀‖/40)` is covered by `tau0 ∘ φ` from `closedBall w₀ (‖w₀‖/10)`
and the (unique) inverse `Φ₀` is a Fatou coordinate for `F₀ = tau0 ∘ f₀ ∘ tau0` there, with
`tau0 (φ (Φ₀ ζ)) = ζ`. -/
theorem exists_fatouCoord_inv_tau0_phi {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {w₀ : ℂ} (h4 : Metric.ball w₀ (‖w₀‖ / 4) ⊆ MandelDim.QLeft d.ξ₀) (hbig : 8 ≤ ‖w₀‖)
    (hanc : ‖MandelDim.tau0 (d.φ w₀) - w₀‖ ≤ ‖w₀‖ / 40)
    (hder : ∀ u ∈ Metric.ball w₀ (‖w₀‖ / 4),
      ‖deriv (fun v : ℂ => MandelDim.tau0 (d.φ v)) u - 1‖ ≤ 1 / 2) :
    ∃ Φ₀ : ℂ → ℂ,
      (∀ ζ ∈ Metric.ball (MandelDim.tau0 (d.φ w₀)) (‖w₀‖ / 40),
        Φ₀ ζ ∈ Metric.closedBall w₀ (‖w₀‖ / 10) ∧ MandelDim.tau0 (d.φ (Φ₀ ζ)) = ζ) ∧
      MandelDim.IsFatouCoordOn (fun w : ℂ => MandelDim.tau0 (f₀ (MandelDim.tau0 w))) Φ₀
        (Metric.ball (MandelDim.tau0 (d.φ w₀)) (‖w₀‖ / 40)) := by
  classical
  ---------------------------------------------------------------------------------------------
  -- Notation and elementary constants
  ---------------------------------------------------------------------------------------------
  have hw0 : 0 < ‖w₀‖ := by linarith
  have hrpos : 0 < ‖w₀‖ / 10 := by linarith
  have hrlt : ‖w₀‖ / 10 < ‖w₀‖ / 4 := by linarith
  have hrdiv : ‖w₀‖ / 10 / 4 = ‖w₀‖ / 40 := by ring
  -- `Ψ = τ₀ ∘ φ`, the map we invert
  set Ψ : ℂ → ℂ := fun u => MandelDim.tau0 (d.φ u) with hΨ
  ---------------------------------------------------------------------------------------------
  -- `Ψ` is holomorphic on the quarter ball, with `‖Ψ' - 1‖ ≤ 1/2` there
  ---------------------------------------------------------------------------------------------
  have hderQ : ∀ u ∈ Metric.ball w₀ (‖w₀‖ / 4), ‖deriv Ψ u - 1‖ ≤ 1 / 2 :=
    fun u hu => hder u hu
  have hdiffQ : ∀ u ∈ Metric.ball w₀ (‖w₀‖ / 4), DifferentiableAt ℂ Ψ u :=
    fun u hu => differentiableAt_of_norm_deriv_sub_one_le (hderQ u hu)
  have hDiffOn : DifferentiableOn ℂ Ψ (Metric.ball w₀ (‖w₀‖ / 4)) :=
    fun u hu => (hdiffQ u hu).differentiableWithinAt
  -- `Ψ' ≠ 0` on the quarter ball
  have hderiv_ne : ∀ u ∈ Metric.ball w₀ (‖w₀‖ / 4), deriv Ψ u ≠ 0 := by
    intro u hu h0
    have h1 := hderQ u hu
    rw [h0] at h1
    norm_num at h1
  ---------------------------------------------------------------------------------------------
  -- The covering statement: `ball (Ψ w₀) (‖w₀‖/40) ⊆ Ψ '' closedBall w₀ (‖w₀‖/10)`
  ---------------------------------------------------------------------------------------------
  have hcov : Metric.ball (Ψ w₀) (‖w₀‖ / 40) ⊆ Ψ '' Metric.closedBall w₀ (‖w₀‖ / 10) := by
    have h := image_cover (Φ := Ψ) (z₀ := w₀) (r := ‖w₀‖ / 10) hrpos Metric.isOpen_ball
      (Metric.closedBall_subset_ball hrlt) hDiffOn
      (fun ζ hζ => hderQ ζ (Metric.closedBall_subset_ball hrlt hζ))
      (by rw [hrdiv]; exact hanc)
    rwa [hrdiv] at h
  ---------------------------------------------------------------------------------------------
  -- The inverse `Φ₀` of `Ψ` on the target ball
  ---------------------------------------------------------------------------------------------
  set U : Set ℂ := Metric.ball (Ψ w₀) (‖w₀‖ / 40) with hU
  let Φ₀ : ℂ → ℂ := fun ζ => if h : ζ ∈ U then (hcov h).choose else 0
  have hΦ₀ : ∀ ζ, Φ₀ ζ = if h : ζ ∈ U then (hcov h).choose else 0 := fun ζ => rfl
  have hΨΦ : ∀ ζ ∈ U, Ψ (Φ₀ ζ) = ζ := by
    intro ζ hζ
    rw [hΦ₀ ζ, dite_eq_left hζ]
    exact (hcov hζ).choose_spec.2
  have hmemΦ : ∀ ζ ∈ U, Φ₀ ζ ∈ Metric.closedBall w₀ (‖w₀‖ / 10) := by
    intro ζ hζ
    rw [hΦ₀ ζ, dite_eq_left hζ]
    exact (hcov hζ).choose_spec.1
  ---------------------------------------------------------------------------------------------
  -- `Ψ` is `2`-expanding in reverse on the quarter ball, hence `Φ₀` is `2`-Lipschitz on `U`
  ---------------------------------------------------------------------------------------------
  have hexp : ∀ z ∈ Metric.ball w₀ (‖w₀‖ / 4), ∀ z' ∈ Metric.ball w₀ (‖w₀‖ / 4),
      ‖z - z'‖ ≤ 2 * ‖Ψ z - Ψ z'‖ :=
    inv_close_of_deriv_close Metric.isOpen_ball (convex_ball w₀ (‖w₀‖ / 4)) hDiffOn hderQ
  have hlip : ∀ ζ ∈ U, ∀ ζ' ∈ U, ‖Φ₀ ζ - Φ₀ ζ'‖ ≤ 2 * ‖ζ - ζ'‖ := by
    intro ζ hζ ζ' hζ'
    have h0 := hexp (Φ₀ ζ) (Metric.closedBall_subset_ball hrlt (hmemΦ ζ hζ))
      (Φ₀ ζ') (Metric.closedBall_subset_ball hrlt (hmemΦ ζ' hζ'))
    rwa [hΨΦ ζ hζ, hΨΦ ζ' hζ'] at h0
  have hcont : ∀ ζ ∈ U, ContinuousAt Φ₀ ζ := by
    intro ζ hζ
    have hUmem : U ∈ 𝓝 ζ := by
      rw [hU]
      exact Metric.isOpen_ball.mem_nhds hζ
    have hLipOn : LipschitzOnWith (2 : NNReal) Φ₀ U :=
      LipschitzOnWith.of_dist_le_mul
        (fun x hx y hy => by simpa [dist_eq_norm] using hlip x hx y hy)
    exact (hLipOn.continuousOn.continuousWithinAt hζ).continuousAt hUmem
  ---------------------------------------------------------------------------------------------
  -- `Φ₀` is holomorphic on `U`: it is a continuous local left inverse of `Ψ`, whose derivative
  -- does not vanish there
  ---------------------------------------------------------------------------------------------
  have hdiffΦ₀ : ∀ ζ ∈ U, DifferentiableAt ℂ Φ₀ ζ := by
    intro ζ hζ
    have hwQ : Φ₀ ζ ∈ Metric.ball w₀ (‖w₀‖ / 4) :=
      Metric.closedBall_subset_ball hrlt (hmemΦ ζ hζ)
    have heq : ∀ᶠ y in 𝓝 ζ, Ψ (Φ₀ y) = y := by
      filter_upwards [show U ∈ 𝓝 ζ from by rw [hU]; exact Metric.isOpen_ball.mem_nhds hζ]
        with y hy
      exact hΨΦ y hy
    exact (HasDerivAt.of_local_left_inverse (f := Ψ) (g := Φ₀) (a := ζ)
      (f' := deriv Ψ (Φ₀ ζ)) (hcont ζ hζ) ((hdiffQ (Φ₀ ζ) hwQ).hasDerivAt)
      (hderiv_ne (Φ₀ ζ) hwQ) heq).differentiableAt
  ---------------------------------------------------------------------------------------------
  -- Assembly
  ---------------------------------------------------------------------------------------------
  refine ⟨Φ₀, ?_, ?_, ?_, ?_⟩
  · intro ζ hζ
    exact ⟨hmemΦ ζ hζ, hΨΦ ζ hζ⟩
  · intro ζ hζ
    exact (hdiffΦ₀ ζ hζ).differentiableWithinAt
  · intro a ha b hb hab
    rw [← hΨΦ a ha, ← hΨΦ b hb, hab]
  · intro ζ hζ hFζ
    show Φ₀ (MandelDim.tau0 (f₀ (MandelDim.tau0 ζ))) = Φ₀ ζ + 1
    -- `w = Φ₀ ζ` and `w + 1` both lie in the quarter ball
    have hwQ : Φ₀ ζ ∈ Metric.ball w₀ (‖w₀‖ / 4) :=
      Metric.closedBall_subset_ball hrlt (hmemΦ ζ hζ)
    have hw1Q : Φ₀ ζ + 1 ∈ Metric.ball w₀ (‖w₀‖ / 4) := by
      rw [Metric.mem_ball, dist_eq_norm]
      have h10 : ‖Φ₀ ζ - w₀‖ ≤ ‖w₀‖ / 10 := by
        have h := hmemΦ ζ hζ
        rw [Metric.mem_closedBall, dist_eq_norm] at h
        exact h
      calc ‖Φ₀ ζ + 1 - w₀‖ = ‖(Φ₀ ζ - w₀) + 1‖ := by ring_nf
        _ ≤ ‖Φ₀ ζ - w₀‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
        _ = ‖Φ₀ ζ - w₀‖ + 1 := by norm_num
        _ ≤ ‖w₀‖ / 10 + 1 := by linarith
        _ < ‖w₀‖ / 4 := by linarith
    -- Shishikura's Abel equation for `φ` at `w` and `w + 1`
    have habel : d.φ (Φ₀ ζ + 1) = f₀ (d.φ (Φ₀ ζ)) :=
      d.φ_abel (Φ₀ ζ) (d.Q_sub (h4 hwQ)) (d.Q_sub (h4 hw1Q))
    -- `φ w = τ₀ ζ`
    have hphiw : d.φ (Φ₀ ζ) = MandelDim.tau0 ζ := by
      have h := congrArg MandelDim.tau0 (hΨΦ ζ hζ)
      simpa [hΨ, tau0_tau0] using h
    -- `Ψ (w + 1) = F₀ ζ`
    have hPsi1 : Ψ (Φ₀ ζ + 1) = MandelDim.tau0 (f₀ (MandelDim.tau0 ζ)) := by
      simp only [hΨ]
      rw [habel, hphiw]
    -- so `Φ₀ (F₀ ζ)` and `Φ₀ ζ + 1` have the same `Ψ`-value
    have heq : Ψ (Φ₀ (MandelDim.tau0 (f₀ (MandelDim.tau0 ζ)))) = Ψ (Φ₀ ζ + 1) := by
      rw [hΨΦ (MandelDim.tau0 (f₀ (MandelDim.tau0 ζ))) hFζ, hPsi1]
    -- `Ψ` is `2`-expanding in reverse on the quarter ball
    have h0 := hexp (Φ₀ (MandelDim.tau0 (f₀ (MandelDim.tau0 ζ))))
      (Metric.closedBall_subset_ball hrlt (hmemΦ (MandelDim.tau0 (f₀ (MandelDim.tau0 ζ))) hFζ))
      (Φ₀ ζ + 1) hw1Q
    have h0' : ‖Φ₀ (MandelDim.tau0 (f₀ (MandelDim.tau0 ζ))) - (Φ₀ ζ + 1)‖ ≤ 0 := by
      rw [heq] at h0
      simpa using h0
    have hfin : Φ₀ (MandelDim.tau0 (f₀ (MandelDim.tau0 ζ))) - (Φ₀ ζ + 1) = 0 :=
      norm_eq_zero.mp (le_antisymm h0' (norm_nonneg _))
    exact sub_eq_zero.mp hfin

end

end Work.Pert
