import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Pert.Basic
import Submission.Work.Pert.Setup
import Submission.Work.Pert.MaxDom
import Submission.Work.Pert.AsmDefs
import Submission.Work.Pert.discgate
import Submission.Work.Pert.DphiP_open
import Submission.Work.Pert.deriv_tauC
import Submission.Work.Pert.sigma_alpha_close
import Submission.Work.Pert.tauC_add_inv_le
import Submission.Work.Fatou.Qreg.InjGeom
import Submission.Work.Pert.deriv_tau0_seedP
import Submission.Work.Pert.deriv_bound_arith

namespace Work.Pert

open MandelDim Complex Set Filter
open scoped Topology

noncomputable section

/-! ## Auxiliary lemmas -/

/-- On the gate image the minimal level is `0`, so `coordP` is the seed value `τ (Φ⁻¹ w)`. -/
private theorem mIdxP_eq_zero_of_mem_image {f : ℂ → ℂ} {Df : Set ℂ} {τ Φ : ℂ → ℂ} {Q : Set ℂ}
    {w : ℂ} (hw : w ∈ Φ '' Q) :
    mIdxP f Df τ Φ Q w = 0 ∧ coordP f Df τ Φ Q w = seedP τ Φ Q w := by
  have hgood : GoodP f Df τ Φ Q w := goodP_of_mem_image hw
  have hspec : w - ((0 : ℕ) : ℂ) ∈ Φ '' Q ∧
      ∀ j : ℕ, j < 0 → f^[j] (seedP τ Φ Q (w - ((0 : ℕ) : ℂ))) ∈ Df :=
    ⟨by simpa using hw, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  have h0 : mIdxP f Df τ Φ Q w = 0 := Nat.le_zero.mp (mIdxP_le hgood hspec)
  refine ⟨h0, ?_⟩
  rw [coordP_self, h0]
  simp

/-- The derivative of `ζ ↦ τ₀ (τ_f ζ)` in terms of its value: with `σ ≠ 0`,
`(τ₀ ∘ τ_f)'(ζ) = -2πiα/σ - 2πiα · τ₀(τ_f ζ)` (the exact algebraic identity
`exp (-2πiαζ) = 1 + σ τ₀(τ_f ζ)` is what removes the exponential). -/
private theorem deriv_tau0_tauC {σ α : ℂ} (hσ : σ ≠ 0) (ζ : ℂ) :
    deriv (fun ζ => MandelDim.tau0 (Work.Pert.tauC σ α ζ)) ζ
      = -(2 * Real.pi * Complex.I * α / σ)
          - 2 * Real.pi * Complex.I * α * MandelDim.tau0 (Work.Pert.tauC σ α ζ) := by
  have hfun : (fun ζ => MandelDim.tau0 (Work.Pert.tauC σ α ζ))
      = (fun ζ => -(1 - Complex.exp (-(2 * Real.pi * Complex.I * α * ζ))) / σ) := by
    funext x
    rw [MandelDim.tau0, Work.Pert.tauC]
    by_cases hg : (1 : ℂ) - Complex.exp (-(2 * Real.pi * Complex.I * α * x)) = 0
    · simp [hg]
    · by_cases hx : σ = 0
      · simp [hx]
      · field_simp
  rw [hfun]
  have hderiv : deriv (fun ζ => -(1 - Complex.exp (-(2 * Real.pi * Complex.I * α * ζ))) / σ) ζ
      = -(2 * Real.pi * Complex.I * α / σ)
          * Complex.exp (-(2 * Real.pi * Complex.I * α * ζ)) := by
    have h1 : HasDerivAt (fun ζ : ℂ => Complex.exp (-(2 * Real.pi * Complex.I * α * ζ)))
        (Complex.exp (-(2 * Real.pi * Complex.I * α * ζ))
          * (-(2 * Real.pi * Complex.I * α))) ζ := by
      have hinner : HasDerivAt (fun y : ℂ => -(2 * Real.pi * Complex.I * α * y))
          (-(2 * Real.pi * Complex.I * α)) ζ :=
        (hasDerivAt_const_mul (2 * Real.pi * Complex.I * α) (x := ζ)).neg
      exact (Complex.hasDerivAt_exp (-(2 * Real.pi * Complex.I * α * ζ))).comp ζ hinner
    have h4 := (h1.const_sub (1 : ℂ)).neg.div_const σ
    have hgoal : HasDerivAt
        (fun ζ : ℂ => -(1 - Complex.exp (-(2 * Real.pi * Complex.I * α * ζ))) / σ)
        (- -(Complex.exp (-(2 * Real.pi * Complex.I * α * ζ))
            * (-(2 * Real.pi * Complex.I * α))) / σ) ζ := by
      simpa only [Pi.neg_apply, Pi.sub_apply, Pi.div_apply] using h4
    rw [hgoal.deriv]
    ring
  rw [hderiv]
  have hid : Complex.exp (-(2 * Real.pi * Complex.I * α * ζ))
      = 1 + σ * MandelDim.tau0 (Work.Pert.tauC σ α ζ) := by
    rw [MandelDim.tau0, Work.Pert.tauC]
    by_cases hg : (1 : ℂ) - Complex.exp (-(2 * Real.pi * Complex.I * α * ζ)) = 0
    · have he : Complex.exp (-(2 * Real.pi * Complex.I * α * ζ)) = 1 := (sub_eq_zero.mp hg).symm
      simp [he]
    · field_simp
      ring
  rw [hid]
  field_simp
  ring

/-- Norm bounds for points of the two discs `Dsm (±η)`, `η > 0`. -/
private lemma norm_bounds_of_mem_Dsm {η : ℝ} (hη : 0 < η) {w : ℂ}
    (hw : w ∈ MandelDim.Dsm η ∪ MandelDim.Dsm (-η)) :
    3 * η / 4 ≤ ‖w‖ ∧ ‖w‖ ≤ 5 * η / 4 := by
  have key : ∀ (c : ℝ), |c| = η → w ∈ MandelDim.Dsm c →
      3 * η / 4 ≤ ‖w‖ ∧ ‖w‖ ≤ 5 * η / 4 := by
    intro c hc hwc
    have h1 : ‖w - Complex.I * (c : ℂ)‖ ≤ |c| / 4 := by
      rw [MandelDim.Dsm, Metric.mem_closedBall, dist_eq_norm] at hwc
      exact hwc
    have h2 : ‖Complex.I * (c : ℂ)‖ = η := by
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, hc]
    rw [hc] at h1
    constructor
    · have h := norm_add_le (Complex.I * (c : ℂ) - w) w
      rw [sub_add_cancel] at h
      have h3 : ‖Complex.I * (c : ℂ) - w‖ = ‖w - Complex.I * (c : ℂ)‖ := norm_sub_rev _ _
      rw [h3, h2] at h
      linarith
    · have h := norm_add_le (w - Complex.I * (c : ℂ)) (Complex.I * (c : ℂ))
      rw [sub_add_cancel, h2] at h
      linarith
  rcases hw with hw | hw
  · exact key η (abs_of_pos hη) hw
  · exact key (-η) (by rw [abs_neg, abs_of_pos hη]) hw

/-! ## The target -/

theorem deriv_tau0_coordP_bounds {f : ℂ → ℂ} {Df : Set ℂ} {u : ℂ → ℂ} {σ α : ℂ}
    {ξ₁ η : ℝ} {Φm : ℂ → ℂ}
    (hξ : 0 < ξ₁) (h2ξ : 2 * ξ₁ < η) (hηbig : 1000000 ≤ η)
    (hInF1 : MandelDim.InF1 α) (hα0 : α ≠ 0)
    (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α))
    (hσ : ‖σ‖ ≤ 8 * Real.pi * ‖α‖)
    (hαη : ‖α‖ * η ≤ 1 / 16384) (hu0 : ‖u 0 - 1‖ ≤ 1 / 1024)
    (hΦm : MandelDim.IsFatouCoordOn (Work.Pert.liftF u σ α) Φm (Work.Pert.Qm ξ₁ α))
    (hder : ∀ ζ ∈ Work.Pert.Qm ξ₁ α, ‖deriv Φm ζ - 1‖ ≤ 1 / 4)
    (hcov : ∀ w ∈ MandelDim.Dsm η ∪ MandelDim.Dsm (-η),
      ∃ ζ ∈ Work.Pert.Qm ξ₁ α, Φm ζ = w)
    (hpin : ∀ w ∈ MandelDim.Dsm η ∪ MandelDim.Dsm (-η),
      ‖MandelDim.tau0 (Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm ξ₁ α) w) - w‖
        ≤ |η| / 40) :
    ∀ w ∈ MandelDim.Dsm η ∪ MandelDim.Dsm (-η),
      1 / 2 < ‖deriv (fun z => MandelDim.tau0
        (Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm ξ₁ α) z)) w‖ ∧
      ‖deriv (fun z => MandelDim.tau0
        (Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm ξ₁ α) z)) w‖ < 2 := by
  intro w hw
  have hηpos : 0 < η := by linarith
  have hηabs : |η| = η := abs_of_pos hηpos
  have hQopen : IsOpen (Qm ξ₁ α) := Work.Fatou.Qreg.isOpen_Qreg _ _
  obtain ⟨ζ₀, hζ₀Q, hΦζ₀⟩ := hcov w hw
  have hΦdiff : DifferentiableOn ℂ Φm (Qm ξ₁ α) := hΦm.1
  have hΦinj : Set.InjOn Φm (Qm ξ₁ α) := hΦm.2.1
  have hder_ne : ∀ z ∈ Qm ξ₁ α, deriv Φm z ≠ 0 := by
    intro z hz h0
    have h := hder z hz
    rw [h0, zero_sub, norm_neg, norm_one] at h
    norm_num at h
  have hwimg : w ∈ Φm '' (Qm ξ₁ α) := ⟨ζ₀, hζ₀Q, hΦζ₀⟩
  have hlev := mIdxP_eq_zero_of_mem_image (f := f) (Df := Df) (τ := tauC σ α) (Φ := Φm) (Q := Qm ξ₁ α) hwimg
  have hcoord : coordP f Df (tauC σ α) Φm (Qm ξ₁ α) w = tauC σ α ζ₀ := by
    rw [hlev.2, seedP, ← hΦζ₀]
    congr 1
    exact invOn_eq hΦinj ⟨ζ₀, hζ₀Q, rfl⟩ hζ₀Q rfl
  have hQimgopen : IsOpen (Φm '' (Qm ξ₁ α)) :=
    isOpen_image_of_deriv_ne_zero hQopen hΦdiff hder_ne
  have hev : (fun z => MandelDim.tau0 (coordP f Df (tauC σ α) Φm (Qm ξ₁ α) z))
      =ᶠ[𝓝 w] (fun z => MandelDim.tau0 (seedP (tauC σ α) Φm (Qm ξ₁ α) z)) := by
    filter_upwards [hQimgopen.mem_nhds hwimg] with z hz
    rw [(mIdxP_eq_zero_of_mem_image (f := f) (Df := Df) (τ := tauC σ α) (Φ := Φm) (Q := Qm ξ₁ α) hz).2]
  rw [hev.deriv_eq]
  obtain ⟨hwge, hwle⟩ := norm_bounds_of_mem_Dsm hηpos hw
  -- bound on `τ₀ (τ_f ζ₀)`
  have hp : ‖MandelDim.tau0 (tauC σ α ζ₀)‖ ≤ 51 * η / 40 := by
    have h := hpin w hw
    rw [hηabs, hcoord] at h
    have hsplit : MandelDim.tau0 (tauC σ α ζ₀)
        = (MandelDim.tau0 (tauC σ α ζ₀) - w) + w := by ring
    rw [hsplit]
    calc ‖(MandelDim.tau0 (tauC σ α ζ₀) - w) + w‖
        ≤ ‖MandelDim.tau0 (tauC σ α ζ₀) - w‖ + ‖w‖ := norm_add_le _ _
      _ ≤ η / 40 + 5 * η / 4 := by linarith
      _ = 51 * η / 40 := by ring
  have hτz : tauC σ α ζ₀ ≠ 0 := by
    intro h0
    have h2 : ‖w‖ ≤ η / 40 := by
      have h := hpin w hw
      rw [hηabs, hcoord, h0] at h
      simpa [MandelDim.tau0] using h
    linarith
  have hσne : σ ≠ 0 := by
    intro h0
    exact hτz (by rw [Work.Pert.tauC, h0, zero_div])
  have hden : (1 : ℂ) - Complex.exp (-(2 * Real.pi * Complex.I * α * ζ₀)) ≠ 0 := by
    intro h0
    exact hτz (by rw [Work.Pert.tauC, h0, div_zero])
  have hE : Complex.exp (-(2 * Real.pi * Complex.I * α * ζ₀)) ≠ 1 := by
    intro h; exact hden (by rw [h, sub_self])
  have hτdiff : DifferentiableAt ℂ (tauC σ α) ζ₀ :=
    (deriv_tauC hσne hτz hE).differentiableAt
  have hd := deriv_tau0_seedP (τ := tauC σ α) (Φ := Φm) (Q := Qm ξ₁ α)
      hQopen hΦdiff hΦinj hζ₀Q (hder_ne ζ₀ hζ₀Q) hτdiff hτz
  have hd' : deriv (fun z => MandelDim.tau0 (seedP (tauC σ α) Φm (Qm ξ₁ α) z)) (Φm ζ₀)
      = deriv (fun ζ => MandelDim.tau0 (tauC σ α ζ)) ζ₀ / deriv Φm ζ₀ := hd.deriv
  rw [← hΦζ₀, hd']
  rw [deriv_tau0_tauC hσne ζ₀]
  have hD : ‖deriv Φm ζ₀ - 1‖ ≤ 1 / 4 := hder ζ₀ hζ₀Q
  have hα_le : ‖α‖ ≤ 1 / 16384 / 1000000 := by
    have h1 : ‖α‖ * (1000000 : ℝ) ≤ ‖α‖ * η :=
      mul_le_mul_of_nonneg_left hηbig (norm_nonneg α)
    have h2 : ‖α‖ * (1000000 : ℝ) ≤ 1 / 16384 := le_trans h1 hαη
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 1000000)]
    linarith
  have hαs : ‖α‖ ≤ 1 / (2 * Real.pi) := by
    have h1 : (1 : ℝ) / 16384 / 1000000 ≤ 1 / 8 := by norm_num
    have h2 : (1 : ℝ) / 8 ≤ 1 / (2 * Real.pi) := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)]
      nlinarith [Real.pi_lt_four]
    linarith
  have hA0 := (sigma_alpha_close hα0 hαs (by linarith [hu0]) hnorm).1
  have hA : ‖σ / α + 2 * Real.pi * Complex.I‖ ≤ 1 / 16 := by
    refine le_trans hA0 ?_
    nlinarith [Real.pi_pos, Real.pi_lt_four, hα_le, hu0,
      norm_nonneg α, norm_nonneg (u 0 - 1)]
  exact deriv_bound_arith hηpos hA hαη hp hD

end

end Work.Pert
