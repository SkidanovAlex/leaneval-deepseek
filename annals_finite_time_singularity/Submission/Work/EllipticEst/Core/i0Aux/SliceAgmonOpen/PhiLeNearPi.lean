import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.EllipticEst.Core.i0Aux.SliceAgmonOpen.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.Core.i0Aux.SliceAgmonOpen

open scoped Real Topology
open MeasureTheory Set Filter

/-- The derivative of `β = f²·sin(2θ)^η` is `2·sin(2θ)^{2η}·Φ`, where `Φ` is the primitive
of the weighted `θ`-integration by parts (see `Defs.lean`).  Consequently the sign of `Φ`
is the sign of `β'`, which is what forces `Φ` to become small near `π/2`. -/
theorem PhiLeNearPi_deriv_beta {f : ℝ → ℝ} (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (beta f) θ = 2 * (Real.sin (2 * θ)) ^ (2 * Work.Spaces.eta) * Phi f θ := by
  have hsin2 : 0 < Real.sin (2 * θ) := sin_two_pos hθ
  have hfd : DifferentiableOn ℝ f (Set.Ioo 0 (Real.pi / 2)) := hf.differentiableOn (by norm_num)
  have hf' : HasDerivAt f (deriv f θ) θ :=
    (hfd.differentiableAt (isOpen_Ioo.mem_nhds hθ)).hasDerivAt
  have hsin : HasDerivAt (fun θ : ℝ => Real.sin (2 * θ)) (2 * Real.cos (2 * θ)) θ := by
    have h := (Real.hasDerivAt_sin (2 * θ)).comp θ ((hasDerivAt_id θ).const_mul 2)
    simpa [Function.comp_def, mul_comm] using h
  have hpow : HasDerivAt (fun θ : ℝ => (Real.sin (2 * θ)) ^ Work.Spaces.eta)
      ((2 * Real.cos (2 * θ)) * Work.Spaces.eta
        * (Real.sin (2 * θ)) ^ (Work.Spaces.eta - 1)) θ :=
    hsin.rpow_const (Or.inl (ne_of_gt hsin2))
  have hmul : HasDerivAt (beta f)
      ((2 * f θ ^ (2 - 1) * deriv f θ) * (Real.sin (2 * θ)) ^ Work.Spaces.eta
        + f θ ^ 2 * ((2 * Real.cos (2 * θ)) * Work.Spaces.eta
          * (Real.sin (2 * θ)) ^ (Work.Spaces.eta - 1))) θ := by
    change HasDerivAt (fun y : ℝ => f y ^ 2 * (Real.sin (2 * y)) ^ Work.Spaces.eta) _ θ
    have h := (hf'.pow 2).mul hpow
    have hfun : (f ^ 2 * fun θ : ℝ => (Real.sin (2 * θ)) ^ Work.Spaces.eta)
        = fun y : ℝ => f y ^ 2 * (Real.sin (2 * y)) ^ Work.Spaces.eta := by
      funext y; simp only [Pi.mul_apply, Pi.pow_apply]
    rw [hfun] at h
    exact h
  rw [hmul.deriv]
  have h1 : (Real.sin (2 * θ)) ^ (2 * Work.Spaces.eta)
        * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)
      = (Real.sin (2 * θ)) ^ Work.Spaces.eta := by
    rw [← Real.rpow_add hsin2]; congr 1; ring
  have h2 : (Real.sin (2 * θ)) ^ (2 * Work.Spaces.eta)
        * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta))
      = (Real.sin (2 * θ)) ^ (Work.Spaces.eta - 1) := by
    rw [← Real.rpow_add hsin2]; congr 1; ring
  rw [Phi, Work.FTS.EllipticEst.thEta]
  rw [show 2 * (Real.sin (2 * θ)) ^ (2 * Work.Spaces.eta)
        * (f θ * deriv f θ * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)
          + Work.Spaces.eta / 2 * f θ ^ 2 * (2 * Real.cos (2 * θ))
              * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta)))
      = 2 * (f θ * deriv f θ)
          * ((Real.sin (2 * θ)) ^ (2 * Work.Spaces.eta)
              * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
        + f θ ^ 2 * (2 * Real.cos (2 * θ) * Work.Spaces.eta)
          * ((Real.sin (2 * θ)) ^ (2 * Work.Spaces.eta)
              * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta)))
      from by ring]
  rw [h1, h2]
  norm_num
  ring

/-- `β = f²·sin(2θ)^η` tends to `0` at `(π/2)⁻` as soon as `f²·sin(2θ)^{-(1+η)}` does:
`β = (f² sin(2θ)^{-(1+η)}) · sin(2θ)^{1+2η}` and `sin(2θ) ≤ 1` near `π/2`. -/
theorem PhiLeNearPi_beta_tendsto {f : ℝ → ℝ}
    (hrate1 : Filter.Tendsto
      (fun θ : ℝ => (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta)))
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) :
    Filter.Tendsto (beta f) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  have hIoo : Set.Ioo 0 (Real.pi / 2) ∈ nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) := by
    rw [Set.Ioo]
    exact Filter.inter_mem
      (mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by linarith [Real.pi_pos])))
      self_mem_nhdsWithin
  refine squeeze_zero' ?_ ?_ hrate1
  · filter_upwards [hIoo] with θ hθ
    rw [beta]
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_pos hθ).le _)
  · filter_upwards [hIoo] with θ hθ
    have hs : 0 < Real.sin (2 * θ) := sin_two_pos hθ
    have hbeta_eq : beta f θ = (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta))
        * (Real.sin (2 * θ)) ^ (1 + 2 * Work.Spaces.eta) := by
      rw [beta, mul_assoc, ← Real.rpow_add hs,
        show -(1 + Work.Spaces.eta) + (1 + 2 * Work.Spaces.eta) = Work.Spaces.eta by ring]
    rw [hbeta_eq]
    refine mul_le_of_le_one_right ?_ ?_
    · exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs.le _)
    · exact Real.rpow_le_one hs.le (Real.sin_le_one _) (by linarith [Work.Spaces.eta_pos])

theorem PhiLeNearPi {f : ℝ → ℝ} (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    (hrate1 : Filter.Tendsto
      (fun θ : ℝ => (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta)))
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) :
    ∀ b δ : ℝ, b < Real.pi / 2 → 0 < δ → ∃ θ ∈ Set.Ioo b (Real.pi / 2), Phi f θ ≤ δ := by
  intro b δ hb hδ
  by_contra hcon
  have hcon' : ∀ θ, θ ∈ Set.Ioo b (Real.pi / 2) → δ < Phi f θ :=
    fun θ hθ => not_le.mp (fun hle => hcon ⟨θ, hθ, hle⟩)
  -- Work on a sub-interval `(c, π/2)` with `b < c` and `0 < c`.
  have hmax : max b 0 < Real.pi / 2 := max_lt hb (half_pos Real.pi_pos)
  obtain ⟨c, hc₁, hc₂⟩ := exists_between hmax
  have hbc : b < c := lt_of_le_of_lt (le_max_left b 0) hc₁
  have h0c : 0 < c := lt_of_le_of_lt (le_max_right b 0) hc₁
  have hcpi : c < Real.pi / 2 := hc₂
  have hsub : Set.Ioo c (Real.pi / 2) ⊆ Set.Ioo 0 (Real.pi / 2) :=
    fun x hx => ⟨lt_trans h0c hx.1, hx.2⟩
  -- `β` is continuous on `(c, π/2)` and strictly increasing there, since `Φ > δ > 0`.
  have hcont : ContinuousOn (beta f) (Set.Ioo c (Real.pi / 2)) := by
    have hfcont : ContinuousOn f (Set.Ioo c (Real.pi / 2)) := hf.continuousOn.mono hsub
    have hsincont : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo c (Real.pi / 2)) :=
      (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
    have hpowcont : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ Work.Spaces.eta)
        (Set.Ioo c (Real.pi / 2)) :=
      hsincont.rpow_const
        (fun θ hθ => Or.inl (ne_of_gt (sin_two_pos ⟨lt_trans h0c hθ.1, hθ.2⟩)))
    have h := (hfcont.pow 2).mul hpowcont
    have hfun : (f ^ 2 * fun θ : ℝ => (Real.sin (2 * θ)) ^ Work.Spaces.eta) = beta f := by
      funext θ; simp only [Pi.mul_apply, Pi.pow_apply, beta]
    rw [hfun] at h
    exact h
  have hpos : ∀ x ∈ Set.Ioo c (Real.pi / 2), 0 < deriv (beta f) x := by
    intro x hx
    have hx0 : x ∈ Set.Ioo 0 (Real.pi / 2) := hsub hx
    have hxb : x ∈ Set.Ioo b (Real.pi / 2) := ⟨lt_trans hbc hx.1, hx.2⟩
    rw [PhiLeNearPi_deriv_beta hf hx0]
    exact mul_pos (mul_pos (by norm_num) (Real.rpow_pos_of_pos (sin_two_pos hx0) _))
      (lt_trans hδ (hcon' x hxb))
  have hmono : StrictMonoOn (beta f) (Set.Ioo c (Real.pi / 2)) :=
    strictMonoOn_of_deriv_pos (convex_Ioo c (Real.pi / 2)) hcont
      (fun x hx => hpos x (by simpa [interior_Ioo] using hx))
  -- Two points `θ₀ < θ₁` of the interval; monotonicity gives `β θ₀ < β θ₁`.
  obtain ⟨θ₀, hcθ₀, hθ₀π⟩ := exists_between hcpi
  obtain ⟨θ₁, hθ₀θ₁, hθ₁π⟩ := exists_between hθ₀π
  have hθ₀ : θ₀ ∈ Set.Ioo c (Real.pi / 2) := ⟨hcθ₀, hθ₀π⟩
  have hθ₁ : θ₁ ∈ Set.Ioo c (Real.pi / 2) := ⟨lt_trans hcθ₀ hθ₀θ₁, hθ₁π⟩
  have hstrict : beta f θ₀ < beta f θ₁ := (hmono.lt_iff_lt hθ₀ hθ₁).mpr hθ₀θ₁
  -- But `β → 0` at `(π/2)⁻`: monotonicity forces `β θ₁ ≤ 0`, while `β θ₀ ≥ 0`.
  have hbt : Filter.Tendsto (beta f) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
      (nhds 0) := PhiLeNearPi_beta_tendsto hrate1
  have hIoi1 : Set.Ioi θ₁ ∈ nhds (Real.pi / 2) := Ioi_mem_nhds hθ₁π
  have hIoi : Set.Ioi θ₁ ∈ nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) :=
    mem_nhdsWithin_of_mem_nhds hIoi1
  have hev : ∀ᶠ θ in nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)), beta f θ₁ ≤ beta f θ := by
    filter_upwards [self_mem_nhdsWithin, hIoi] with θ hθI hθgt
    have hθ : θ ∈ Set.Ioo c (Real.pi / 2) := ⟨lt_trans hθ₁.1 (show θ₁ < θ from hθgt), hθI⟩
    exact le_of_lt ((hmono.lt_iff_lt hθ₁ hθ).mpr (show θ₁ < θ from hθgt))
  have hle0 : beta f θ₁ ≤ 0 := ge_of_tendsto hbt hev
  have hge0 : 0 ≤ beta f θ₀ := by
    rw [beta]
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_pos (hsub hθ₀)).le _)
  exact absurd hstrict (not_lt.mpr (le_trans hle0 hge0))

end Work.EllipticEst.Core.i0Aux.SliceAgmonOpen
