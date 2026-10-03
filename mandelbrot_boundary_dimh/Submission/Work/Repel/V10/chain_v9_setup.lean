import Mathlib
import Submission.Work.Repel.Spec
import Submission.Work.Repel.boxes_v3
import Submission.Work.Repel.chain_v9_geom
import Submission.Work.L62.chain
import Submission.Work.Interfaces.Parabolic

/-!
# `Work.Repel.chain_v9_setup` : the hypothesis package of `chain_returns_v9`

The §6 assembly of `Work.Repel.chain_returns_v9` is a long chain of estimates on the composite

  `z ↦ w₀ ↦ ζ = s·π w₀ ↦ u = (φ₁|Dsm)⁻¹ ζ ↦ u' = ĥ^j u - k ↦ w₁ ↦ z' = φ₀ w₁`

of Shishikura's §6.  To be able to state (and delegate) its pieces, this file bundles the
hypotheses of `chain_returns_v9` into a structure `Work.Repel.V10`.
-/

namespace Work.Repel

open MandelDim Complex Set Metric Filter Topology

noncomputable section

/-- **The hypothesis package of `chain_returns_v9`** (verbatim, in the same order). -/
structure V10 where
  f₀ : ℂ → ℂ
  D₀ : Set ℂ
  d₀ : MandelDim.ParabData f₀ D₀
  hd : MandelDim.HornData d₀
  f : ℂ → ℂ
  hfdiff : Differentiable ℂ f
  η : ℝ
  y₀ : ℝ
  K₀ : Set ℂ
  K₀' : Set ℂ
  δ : ℝ
  P₀ : MandelDim.PertData d₀ f Set.univ η y₀ K₀ K₀' δ
  wt₀ : ℂ
  hφwt₀ : d₀.φ wt₀ = 0
  r₀ : ℝ
  hr₀ : 0 < r₀
  hK₀' : K₀' = Metric.closedBall wt₀ (2 * r₀)
  ρ₀ : ℝ
  σ₀ : ℝ
  hρ₀ : 0 < ρ₀
  hρ₀le : ρ₀ ≤ 1 / 2
  hσ₀ : 0 < σ₀
  hσ₀big : 4 / η ≤ σ₀
  hwt₀ : ‖wt₀‖ + ρ₀ ≤ 2 * η
  hinjφ₀ : Set.InjOn P₀.φ (Metric.ball wt₀ ρ₀)
  hcov₀ : Metric.ball 0 σ₀ ⊆ P₀.φ '' Metric.ball wt₀ ρ₀
  hsub₀ : Metric.ball wt₀ ρ₀ ⊆ P₀.Dφ
  hDflatDR : Work.Repel.Dflat η ⊆ P₀.DR
  s : ℂ
  hs : s ≠ 0
  η₁ : ℝ
  y₁' : ℝ
  K₂ : Set ℂ
  K₂' : Set ℂ
  δ₁ : ℝ
  d₁ : MandelDim.ParabData (Work.Repel.g0germ d₀) (Work.Repel.Dg0germ d₀ hd)
  P₁ : MandelDim.PertData d₁ (Work.Repel.germ1 s P₀.R) (Work.Repel.Dgerm1 s P₀.DR)
      η₁ y₁' K₂ K₂' δ₁
  R : ℂ → ℂ
  DR : Set ℂ
  β : ℂ
  ζa : ℂ
  ζb : ℂ
  ρ : ℝ
  sgn : ℝ
  C₀ : ℝ
  C₁ : ℝ
  C₁' : ℝ
  W : ℕ → Set ℂ
  b : ℝ
  hb : 0 < b
  hR : R = fun w => P₁.R w + 1 / MandelDim.rotOf (Work.Repel.germ1 s P₀.R)
  hk : ∃ k : ℕ, 2 ≤ k ∧ 1 / MandelDim.rotOf (Work.Repel.germ1 s P₀.R) = β + k
  hβre : 0 ≤ β.re
  hβre' : β.re < 1
  hβim : |β.im| ≤ b
  hDRopen : IsOpen DR
  hReq : MandelDim.IsTEquivariantOn R DR
  hRdiff : DifferentiableOn ℂ R DR
  hDRsub : DR ⊆ P₁.DR
  hIsChain : Work.L62.IsChain R β DR ζa ζb ρ sgn C₀ C₁ C₁' W
  hanchor : ∃ j₀ : ℕ, ∃ w ∈ W j₀, sgn * w.im < η₁ / 4
  hC₀ : 0 < C₀
  hC₁ : 0 < C₁
  hC₁' : 0 < C₁'
  hη : 100 ≤ η
  hη₁ : η₁ * ‖s‖ = Real.exp (2 * Real.pi * η)
  hsize : 64 * (C₀ + 1) ≤ η₁
  cbase : ℂ
  hbase : W 0 = Metric.ball cbase ρ
  hK₂' : Metric.closedBall cbase (2 * ρ) ⊆ K₂'
  ρ₁ : ℝ
  σ₁ : ℝ
  hρ₁ : 0 < ρ₁
  hρ₁le : ρ₁ ≤ ρ
  hσ₁ : 0 < σ₁
  hinjφ₁ : Set.InjOn P₁.φ (Metric.ball cbase ρ₁)
  hcov₁ : Metric.ball (d₁.φ cbase) σ₁ ⊆ P₁.φ '' Metric.ball cbase ρ₁
  hsub₁ : Metric.ball cbase ρ ⊆ P₁.Dφ
  hcbase : ‖cbase‖ + ρ ≤ η₁ / 2
  /-- v10: the target control is only required on the part of `ball wt₀ ρ₀` whose `φ₀`-image
  lies in `ball 0 σ₀` (that is all the assembly needs, and all that the intended supply
  provides: an unrestricted form would force `P₁.φ '' W 0 = s·π '' ball wt₀ ρ₀`). -/
  htgt' : ∀ w ∈ Metric.ball wt₀ ρ₀, P₀.φ w ∈ Metric.ball 0 σ₀ →
    s * MandelDim.piExp w ∈ P₁.φ '' Metric.ball cbase ρ₁
  htgt : ∀ u' ∈ W 0, ∃ w ∈ Metric.ball wt₀ ρ₀, MandelDim.piExp w = P₁.φ u' / s
  Cb : ℝ
  hCbpos : 0 < Cb
  hCbbd : ∀ u' ∈ W 0, ∀ w ∈ Metric.ball wt₀ ρ₀, MandelDim.piExp w = P₁.φ u' / s →
      ‖deriv P₀.φ w‖ * ‖deriv P₁.φ u'‖ ≤ Cb * ‖s‖ * ‖deriv MandelDim.piExp w‖
  cb : ℝ
  hcbpos : 0 < cb
  hcblo : ∀ u' ∈ W 0, ∀ w ∈ Metric.ball wt₀ ρ₀, MandelDim.piExp w = P₁.φ u' / s →
      cb * ‖s‖ * ‖deriv MandelDim.piExp w‖ ≤ ‖deriv P₀.φ w‖ * ‖deriv P₁.φ u'‖
  hfitlo : 4 * (η * η₁ ^ 2 / (320 * (C₀ + 1))) ≤ (C₁ * cb * η ^ 2 * η₁ / 10) ^ 2
  hfit : η * η₁ ^ 2 / (320 * (C₀ + 1)) ≤
      (10 ^ 6 * Cb * (C₁' + 1) * η ^ 2 * η₁) ^ 2 / 256
  hangle₀ : ∀ w w' : ℂ, ‖w‖ ≤ 2 * η → ‖w'‖ ≤ 2 * η →
      |Complex.arg (w' + 1 / (2 * MandelDim.rotOf f) - w)| < 2 * Real.pi / 3
  hangle₁ : ∀ u u' : ℂ, ‖u‖ ≤ 2 * η₁ → ‖u'‖ ≤ 2 * η₁ →
      |Complex.arg (u' + 1 / (2 * MandelDim.rotOf (Work.Repel.germ1 s P₀.R)) - u)|
        < 2 * Real.pi / 3

namespace V10

variable (V : V10)

theorem hηpos : 0 < V.η := by linarith [V.hη]
theorem hs_ne : V.s ≠ 0 := V.hs
theorem hη₁pos : 0 < V.η₁ := by
  have h : 0 < V.η₁ * ‖V.s‖ := by rw [V.hη₁]; positivity
  rw [mul_comm] at h
  exact pos_of_mul_pos_right h (norm_nonneg V.s)
theorem hη₁s : V.η₁ * ‖V.s‖ = Real.exp (2 * Real.pi * V.η) := V.hη₁
theorem hC₀pos : 0 < V.C₀ := V.hC₀
theorem hC₁pos : 0 < V.C₁ := V.hC₁
theorem hC₁'pos : 0 < V.C₁' := V.hC₁'

/-- The right-hand side of the derivative bound. -/
def Kmax : ℝ := 10 ^ 6 * V.Cb * (V.C₁' + 1) * V.η ^ 2 * V.η₁

/-- The counting bound of the conclusion. -/
def N₀ : ℝ := V.η * V.η₁ ^ 2 / (320 * (V.C₀ + 1))

/-- The centre of the target discs of the conclusion. -/
def p : ℂ := 1.05 * Complex.I / V.η

theorem N₀_le_Kmax : V.N₀ ≤ V.Kmax ^ 2 / 256 := V.hfit

/-- The level-0 target disc radius for which the `φ_star_close` containment of row 2 holds. -/
def r : ℝ := 9 / (20 * V.η)

theorem r_pos : 0 < V.r := by
  rw [r]
  apply div_pos (by norm_num)
  have := V.hηpos
  positivity

end V10

end

end Work.Repel
