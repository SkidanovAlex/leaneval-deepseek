import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.H2W.SliceA.Lzero1_order_shift
import Submission.Work.FTS.EllipticEst.H2W.WeakPureAux.towerAscent

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `WeakPureAux/cascadeBalance` — the exact amplitude balance of the cascade at `θ = π/2`

`WeakPureAux/NOTES_weakPhiPoleBound.md` §K records (numerically confirmed, by hand) that the
level amplitudes `a_k` of a slice expanded in `θ`-profiles `t^{-k}` satisfy the *linear* recursion

  `(R - λ_k) a_k = (1 - (k-2)²) a_{k-2} + ((k+1)/3 - 6) a_k`,

whose coefficients grow like `6^m m!`, so the cascade cannot be summed.  This module formalises
the *first* half of that statement, which is the part that needs no arithmetic:

**if the source has no component of order `N+2` (`(π/2-θ)^{N+2}·G(z,θ) → 0`) and the slice has a
pure power of order `N ≥ 2` with amplitude `B`, then**

  `(1 - N²)·B = α²z²·B₂ + α(5+α)z·B₁`,   (⋆)

where `B₁`, `B₂` are the order-`(N+2)` amplitudes of `∂_zΦ(z,·)` resp. `∂_z²Φ(z,·)`.  Reading
`(⋆)` as a recursion `N ↦ N+2` (the radial operator `R = α²z²∂_z² + α(5+α)z∂_z` applied to the
*next* amplitude is `(1-N²)` times the current one), it is exactly the statement that the
`θ`-order of the slice can only be pushed upwards along the levels — the mechanism of §K.

The engine is the proved `SliceA.Lzero1_order_shift`: at `θ = π/2` the operator `Lzero1` shifts a
pure power of order `N` to order `N+2` with the coefficient `1 - N²`, and no term of order `N`
(the radial part of the equation) can cancel that leading term.
-/

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

namespace Work.FTS.EllipticEst.H2W.WeakPureAux

local notation "Lθ" => nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))

/-- **The cascade amplitude balance.**  Hypotheses: the equation on the open quadrant, the
pure-power limits of order `N ≥ 2` for the slice (the three limits of `SliceA.Lzero1_order_shift`),
the order-`(N+2)` amplitudes `B₁`, `B₂` of `∂_zΦ(z,·)`, `∂_z²Φ(z,·)`, and the vanishing of the
order-`(N+2)` component of the source.  Conclusion: `(1-N²)·B = α²z²·B₂ + α(5+α)z·B₁`. -/
theorem cascadeBalance {α : ℝ} {G Φ : ℝ → ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    {N : ℕ} (hN : 2 ≤ N) {B B₁ B₂ : ℝ}
    (heq : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 →
      Work.Elliptic.bslOp α Φ z θ = G z θ)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (fun θ => Φ z θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (h0 : Filter.Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ N * Φ z θ) Lθ (nhds B))
    (h1 : Filter.Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ (N + 1) *
        deriv (fun θ' => Φ z θ') θ) Lθ (nhds ((N : ℝ) * B)))
    (h2 : Filter.Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ (N + 2) *
        deriv (fun s => deriv (fun θ' => Φ z θ') s) θ) Lθ
      (nhds ((N : ℝ) * ((N : ℝ) + 1) * B)))
    (hB₁ : Filter.Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ (N + 2) * Work.Spaces.pz Φ z θ)
      Lθ (nhds B₁))
    (hB₂ : Filter.Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ (N + 2)
        * Work.Spaces.pzIter 2 Φ z θ) Lθ (nhds B₂))
    (hG : Filter.Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ (N + 2) * G z θ) Lθ (nhds 0)) :
    (1 - (N : ℝ) ^ 2) * B = α ^ 2 * z ^ 2 * B₂ + α * (5 + α) * z * B₁ := by
  have hε : (0 : ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
  have hu : ContDiffOn ℝ 2 (fun θ => Φ z θ)
      (Set.Ioo (Real.pi / 2 - Real.pi / 4) (Real.pi / 2)) :=
    (hsm 2).mono (fun θ hθ => ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
  have hL := Work.FTS.EllipticEst.H2W.SliceA.Lzero1_order_shift
    (u := fun θ => Φ z θ) hN hε hu h0 h1 h2
  -- on a neighbourhood of `π/2` the source is `-α²z²∂_z²Φ - α(5+α)z∂_zΦ + Lzero1 (Φ z ·)`
  have hcongr : (fun θ : ℝ => (Real.pi / 2 - θ) ^ (N + 2) * G z θ) =ᶠ[Lθ]
      (fun θ : ℝ => (Real.pi / 2 - θ) ^ (N + 2) *
        (-(α ^ 2 * z ^ 2) * Work.Spaces.pzIter 2 Φ z θ
          - (α * (5 + α) * z) * Work.Spaces.pz Φ z θ
          + Work.FTS.EllipticEst.Lzero1 (fun θ' => Φ z θ') θ)) := by
    have hmem : Set.Ioi (Real.pi / 4) ∈ Lθ :=
      nhdsWithin_le_nhds
        (isOpen_Ioi.mem_nhds (by linarith [Real.pi_pos] : Real.pi / 4 < Real.pi / 2))
    filter_upwards [self_mem_nhdsWithin, hmem] with θ hθ₁ hθ₂
    have hlt : θ < Real.pi / 2 := hθ₁
    have hθ₂' : Real.pi / 4 < θ := hθ₂
    have hgt : 0 < θ := by linarith [hθ₂', Real.pi_pos]
    have h := heq z hz θ hgt hlt
    rw [Work.Elliptic.bslOp_apply] at h
    have hLz : Work.Elliptic.Lzero Φ z θ
        = Work.FTS.EllipticEst.Lzero1 (fun θ' => Φ z θ') θ := by
      rw [Work.FTS.EllipticEst.Lzero1_eq_Lzero (fun θ' => Φ z θ') z]
      simp only [Work.Elliptic.Lzero, Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero,
        Work.Spaces.pth]
    rw [← h, hLz]
  have hlim : Filter.Tendsto
      (fun θ : ℝ => (Real.pi / 2 - θ) ^ (N + 2) *
        (-(α ^ 2 * z ^ 2) * Work.Spaces.pzIter 2 Φ z θ
          - (α * (5 + α) * z) * Work.Spaces.pz Φ z θ
          + Work.FTS.EllipticEst.Lzero1 (fun θ' => Φ z θ') θ)) Lθ
      (nhds (-(α ^ 2 * z ^ 2) * B₂ + -(α * (5 + α) * z) * B₁
        + (1 - (N : ℝ) ^ 2) * B)) := by
    have h1' : Filter.Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ (N + 2) *
        (-(α ^ 2 * z ^ 2) * Work.Spaces.pzIter 2 Φ z θ)) Lθ
        (nhds (-(α ^ 2 * z ^ 2) * B₂)) := by
      have h := hB₂.const_mul (-(α ^ 2 * z ^ 2))
      simpa only [mul_assoc, mul_comm, mul_left_comm] using h
    have h2' : Filter.Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ (N + 2) *
        (-(α * (5 + α) * z) * Work.Spaces.pz Φ z θ)) Lθ
        (nhds (-(α * (5 + α) * z) * B₁)) := by
      have h := hB₁.const_mul (-(α * (5 + α) * z))
      simpa only [mul_assoc, mul_comm, mul_left_comm] using h
    have h3' : Filter.Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ (N + 2) *
        Work.FTS.EllipticEst.Lzero1 (fun θ' => Φ z θ') θ) Lθ
        (nhds ((1 - (N : ℝ) ^ 2) * B)) := hL
    have hsum := (h1'.add h2').add h3'
    refine hsum.congr (fun θ => by ring)
  have h0lim := hG.congr' hcongr
  rw [Filter.Tendsto] at h0lim hlim
  have hkey : (0 : ℝ) = -(α ^ 2 * z ^ 2) * B₂ + -(α * (5 + α) * z) * B₁
      + (1 - (N : ℝ) ^ 2) * B := tendsto_nhds_unique h0lim hlim
  linarith [hkey]

/-- **No isolated pure power of order `N ≥ 2`.**  If the radial amplitudes vanish as well (the
radial terms are also `o(t^{-(N+2)})`), then the slice's order-`N` amplitude is zero. -/
theorem cascadeBalance_zero_amp {α : ℝ} {G Φ : ℝ → ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    {N : ℕ} (hN : 2 ≤ N) {B : ℝ}
    (heq : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 →
      Work.Elliptic.bslOp α Φ z θ = G z θ)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (fun θ => Φ z θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (h0 : Filter.Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ N * Φ z θ) Lθ (nhds B))
    (h1 : Filter.Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ (N + 1) *
        deriv (fun θ' => Φ z θ') θ) Lθ (nhds ((N : ℝ) * B)))
    (h2 : Filter.Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ (N + 2) *
        deriv (fun s => deriv (fun θ' => Φ z θ') s) θ) Lθ
      (nhds ((N : ℝ) * ((N : ℝ) + 1) * B)))
    (hB₁ : Filter.Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ (N + 2) * Work.Spaces.pz Φ z θ)
      Lθ (nhds 0))
    (hB₂ : Filter.Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ (N + 2)
        * Work.Spaces.pzIter 2 Φ z θ) Lθ (nhds 0))
    (hG : Filter.Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ (N + 2) * G z θ) Lθ (nhds 0)) :
    B = 0 := by
  have hbal := cascadeBalance hz hN heq hsm h0 h1 h2 hB₁ hB₂ hG
  have hcoef : (1 : ℝ) - (N : ℝ) ^ 2 ≠ 0 := by
    have h2N : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    nlinarith
  have : (1 - (N : ℝ) ^ 2) * B = 0 := by
    rw [hbal]; ring
  exact (mul_eq_zero.mp this).resolve_left hcoef

end Work.FTS.EllipticEst.H2W.WeakPureAux
