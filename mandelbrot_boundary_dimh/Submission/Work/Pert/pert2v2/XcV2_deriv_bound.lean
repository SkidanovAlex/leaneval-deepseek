import Mathlib
import Submission.Work.Pert.pert2v2.Psi_Xc_constant
import Submission.Work.Pert.Ksub2.Setup
import Submission.Work.Interfaces.Fatou

namespace Work.Pert.pert2v2

open MandelDim Complex Set Metric

noncomputable section

/-- `τ₀` undoes the curve: `τ₀ (Xc d u) = d.φ u`, for *every* `u` (at points where `d.φ u = 0`
both sides are the junk value `0`). -/
theorem tau0_Xc_eq {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀) (u : ℂ) :
    MandelDim.tau0 (Work.Pert.Xc d u) = d.φ u := by
  simp only [Work.Pert.Xc, Work.Pert.tau0_tau0]

/-- **The derivative of `Ψ ∘ Xc d` is `1` at the deep left end, with rate `O(1/(-Re v))`.**

The composite `Ψ ∘ Xc d` of a Fatou coordinate `Ψ` of the limit dynamics `F₀ = τ₀ ∘ f₀ ∘ τ₀`
with the datum's curve `Xc d u = τ₀ (φ₀ u)` is a **Fatou coordinate of the translation**
`u ↦ u + 1`:
* the curve step `Xc d (u+1) = F₀ (Xc d u)` (`Work.Pert.Xc_add_one`) and `Ψ`'s Abel clause turn
  `+1` on the `u`-side into `+1` on the `w`-side;
* injectivity comes from `Ψ`'s injectivity on the cone (`hΨ`) together with `ParabData.φ_inj`:
  `Ψ (Xc d u₁) = Ψ (Xc d u₂) ⟹ Xc d u₁ = Xc d u₂ ⟹ φ u₁ = φ u₂ ⟹ u₁ = u₂`, since all the
  relevant points lie deep left, hence in `QLeft ξ₀` where `φ` is injective.

Shishikura's Lemma A.2.4(i) (`FatouDerivEstimate`) applied with the *constant* vector field
`1` — for which `Φ (z + v z) = Φ z + 1` is exactly the Abel clause and `‖v z - 1‖ = 0 < 1/4` is
free — then gives `‖deriv (Ψ ∘ Xc d) v - 1‖ ≤ C₂ / R` where `R` is the radius of the ball on which
the Abel clause is available.  Deep left, the ball `ball v (M/8)`, `M = -Re v`, lies in
`{Re < -ξ₀} ⊆ QLeft ξ₀` and (through `hleg`) in the region where `Xc d` lands in the cone, so
`R = M/8` is admissible and the bound is `8C₂/M`. -/
theorem XcV2_deriv_bound {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    (hF : MandelDim.FatouStatement) {Ξ' : ℝ} {Ψ : ℂ → ℂ}
    (hΨ : MandelDim.IsFatouCoordOn (fun w : ℂ => MandelDim.tau0 (f₀ (MandelDim.tau0 w))) Ψ
      (MandelDim.Qreg none (some (-(Ξ' : ℂ)))))
    {Nleg : ℝ} (hleg : ∀ u : ℂ, u.re < -Nleg →
      Work.Pert.Xc d u ∈ MandelDim.Qreg none (some (-(Ξ' : ℂ)))) :
    ∃ N C : ℝ, 0 < C ∧ ∀ v : ℂ, v.re ≤ -N →
      ‖deriv (fun w : ℂ => Ψ (Work.Pert.Xc d w)) v - 1‖ ≤ C / (-v.re) := by
  -- Lemma A.2.4(i) with its universal constants
  obtain ⟨R₁, C₁, C₂, hR₁, hC₁, hC₂, hEst⟩ := hF.2.2.2.2.1
  -- the datum's asymptotic of the curve, at the fixed error `ε = 1`
  obtain ⟨a, b, hasym⟩ := d.φ_asymp
  obtain ⟨R_A, hR_A⟩ := hasym 1 one_pos
  obtain ⟨R_B, hR_B⟩ := Work.Pert.exists_norm_add_clog_bound a b 1 one_pos
  -- the cone of `hΨ`
  set Q : Set ℂ := MandelDim.Qreg none (some (-(Ξ' : ℂ))) with hQ
  have hΨQ : MandelDim.IsFatouCoordOn
      (fun w : ℂ => MandelDim.tau0 (f₀ (MandelDim.tau0 w))) Ψ Q := by
    rw [hQ]; exact hΨ
  have hlegQ : ∀ u : ℂ, u.re < -Nleg → Work.Pert.Xc d u ∈ Q := by
    intro u hu; rw [hQ]; exact hleg u hu
  -- one scale dominating all the thresholds
  set K : ℝ := max 1 (max R₁ (max R_A (max R_B (max d.ξ₀ Nleg)))) with hK
  have hK1 : (1 : ℝ) ≤ K := by rw [hK]; exact le_max_left _ _
  have hKR₁ : R₁ ≤ K := by
    rw [hK]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hKRA : R_A ≤ K := by
    rw [hK]
    exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hKRB : R_B ≤ K := by
    rw [hK]
    exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _)))
  have hKξ : d.ξ₀ ≤ K := by
    rw [hK]
    exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))))
  have hKNleg : Nleg ≤ K := by
    rw [hK]
    exact le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))))
  refine ⟨64 * (K + 2), 8 * C₂ + 1, by positivity, ?_⟩
  intro v hv
  set M : ℝ := -v.re with hM
  have hMge : 64 * (K + 2) ≤ M := by rw [hM]; linarith
  have hMpos : 0 < M := by linarith
  -- the thresholds, expressed in terms of `M`
  have hρ8 : 8 * R₁ ≤ M := by linarith
  have hNleg7 : Nleg + 2 ≤ 7 * M / 8 := by linarith
  have hξ7 : d.ξ₀ + 1 < 7 * M / 8 := by linarith
  have hRA7 : R_A + 1 < 7 * M / 8 := by linarith
  have hRB7 : R_B ≤ 7 * M / 8 := by linarith
  -- geometry of the ball `ball v (M/8)`
  have hball_re : ∀ u ∈ ball v (M / 8), u.re ≤ -(7 * M / 8) := by
    intro u hu
    have h1 : dist u v < M / 8 := Metric.mem_ball.mp hu
    rw [dist_eq_norm] at h1
    have h2 : (u - v).re ≤ ‖u - v‖ := Complex.re_le_norm _
    have h3 : (u - v).re = u.re - v.re := Complex.sub_re _ _
    have h4 : v.re = -M := by rw [hM]; ring
    rw [h3, h4] at h2
    linarith
  have hball_norm : ∀ u ∈ ball v (M / 8), 7 * M / 8 ≤ ‖u‖ := by
    intro u hu
    have h1 : dist u v < M / 8 := Metric.mem_ball.mp hu
    rw [dist_eq_norm] at h1
    have h2 : ‖v‖ ≤ ‖v - u‖ + ‖u‖ := by
      have h := norm_add_le (v - u) u
      rwa [sub_add_cancel] at h
    have h3 : ‖v - u‖ = ‖u - v‖ := norm_sub_rev v u
    have h4 : M ≤ ‖v‖ := by
      have h := Complex.abs_re_le_norm v
      have h5 : |v.re| = M := by
        rw [show v.re = -M by rw [hM]; ring, abs_neg, abs_of_pos hMpos]
      linarith
    linarith
  have huQ : ∀ u ∈ ball v (M / 8), u ∈ MandelDim.QLeft d.ξ₀ := by
    intro u hu
    have hre : u.re < -d.ξ₀ := by have h1 := hball_re u hu; linarith
    exact Work.Parab.halfplane_subset_QLeft d.ξ₀ hre
  -- the curve is defined and nonvanishing on the ball
  have hφne : ∀ u ∈ ball v (M / 8), d.φ u ≠ 0 := by
    intro u hu
    have huQ' := huQ u hu
    have hnorm := hball_norm u hu
    have hRA : R_A < ‖u‖ := by linarith
    have hRB : R_B ≤ ‖u‖ := by linarith
    have hasy := hR_A u huQ' hRA
    have hcoer := hR_B u hRB
    intro hzero
    have hz : MandelDim.tau0 (d.φ u) = 0 := by rw [hzero]; simp [MandelDim.tau0]
    rw [hz, zero_sub, norm_neg] at hasy
    linarith
  have hXcd : DifferentiableOn ℂ (Work.Pert.Xc d) (ball v (M / 8)) := fun u hu =>
    (differentiableAt_Xc d (d.Q_sub (huQ u hu)) (hφne u hu)).differentiableWithinAt
  have hmaps : MapsTo (Work.Pert.Xc d) (ball v (M / 8)) Q := fun u hu =>
    hlegQ u (by have := hball_re u hu; linarith)
  -- `Ψ ∘ Xc d` is a Fatou coordinate of the translation `u ↦ u + 1` on the ball
  have hcomp : DifferentiableOn ℂ (fun u : ℂ => Ψ (Work.Pert.Xc d u)) (ball v (M / 8)) :=
    hΨQ.1.comp hXcd hmaps
  have hinj : Set.InjOn (fun u : ℂ => Ψ (Work.Pert.Xc d u)) (ball v (M / 8)) := by
    intro u₁ h₁ u₂ h₂ heq
    have hX : Work.Pert.Xc d u₁ = Work.Pert.Xc d u₂ :=
      hΨQ.2.1 (hmaps h₁) (hmaps h₂) heq
    have hp : d.φ u₁ = d.φ u₂ := by
      rw [← tau0_Xc_eq d u₁, ← tau0_Xc_eq d u₂, hX]
    exact d.φ_inj (huQ u₁ h₁) (huQ u₂ h₂) hp
  have habel : ∀ z ∈ ball v (M / 8), z + (fun _ : ℂ => (1 : ℂ)) z ∈ ball v (M / 8) →
      (fun u : ℂ => Ψ (Work.Pert.Xc d u)) (z + (fun _ : ℂ => (1 : ℂ)) z) =
        (fun u : ℂ => Ψ (Work.Pert.Xc d u)) z + 1 := by
    intro z hz hz1
    have hzre : z.re ≤ -(7 * M / 8) := hball_re z hz
    have hzQ : z ∈ MandelDim.QLeft d.ξ₀ := huQ z hz
    have hzDφ : z ∈ d.Dφ := d.Q_sub hzQ
    have hz1Dφ : z + 1 ∈ d.Dφ := (d.succ_iff z hzDφ).mpr (d.Q_maps hzQ)
    have hstep : Work.Pert.Xc d (z + 1) = Work.Pert.F0f f₀ (Work.Pert.Xc d z) :=
      Work.Pert.Xc_add_one d hzDφ hz1Dφ
    have hXQ : Work.Pert.Xc d z ∈ Q := hmaps hz
    have hFQ : Work.Pert.F0f f₀ (Work.Pert.Xc d z) ∈ Q := by
      rw [← hstep]
      refine hlegQ (z + 1) ?_
      simp only [Complex.add_re, Complex.one_re]
      linarith
    have hψ := hΨQ.2.2 (Work.Pert.Xc d z) hXQ hFQ
    show Ψ (Work.Pert.Xc d (z + 1)) = Ψ (Work.Pert.Xc d z) + 1
    rw [hstep]
    exact hψ
  -- Lemma A.2.4(i) at the constant vector field `1`
  obtain ⟨-, hbound⟩ := hEst (fun u : ℂ => Ψ (Work.Pert.Xc d u)) (fun _ : ℂ => (1 : ℂ)) v
    (M / 8) (by linarith) hcomp hinj (differentiableOn_const (1 : ℂ)) (by intro z hz; norm_num)
    habel
  have hfin : ‖deriv (fun w : ℂ => Ψ (Work.Pert.Xc d w)) v - 1‖ ≤ C₂ / (M / 8) := by
    simpa using hbound
  calc ‖deriv (fun w : ℂ => Ψ (Work.Pert.Xc d w)) v - 1‖
      ≤ C₂ / (M / 8) := hfin
    _ = 8 * C₂ / M := by rw [div_div_eq_mul_div]; ring
    _ ≤ (8 * C₂ + 1) / M := div_le_div_of_nonneg_right (by linarith) hMpos.le
    _ = (8 * C₂ + 1) / (-v.re) := by rw [hM]

end

end Work.Pert.pert2v2
