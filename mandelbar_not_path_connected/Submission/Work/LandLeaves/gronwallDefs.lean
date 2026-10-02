/-
Copyright: subproject `Submission/Work/LandLeaves/` of `mandelbar_not_path_connected`.

# `gronwallArea` — definitions (Laurent coefficients at infinity etc.)
-/
import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Complex Metric Set Filter
namespace Work.LandLeaves
open scoped Topology

noncomputable section

noncomputable def regPart (ψ : ℂ → ℂ) : ℂ → ℂ :=
  fun ζ => if ζ = 0 then 0 else ψ ζ⁻¹ - ζ⁻¹

lemma isOpen_lt_norm (a : ℝ) : IsOpen {w : ℂ | a < ‖w‖} :=
  isOpen_lt continuous_const continuous_norm

noncomputable def Fext (ψ : ℂ → ℂ) : ℂ → ℂ :=
  Function.update (regPart ψ) 0 ((nhdsWithin 0 {0}ᶜ).limUnder (regPart ψ))

lemma Fext_eq (ψ : ℂ → ℂ) {ζ : ℂ} (hζ : ζ ≠ 0) : Fext ψ ζ = ψ ζ⁻¹ - ζ⁻¹ := by
  rw [Fext, Function.update_of_ne hζ, regPart]
  simp [hζ]

lemma Fext_diff (ψ : ℂ → ℂ) (C : ℝ)
    (hd : DifferentiableOn ℂ ψ {w : ℂ | 1 < ‖w‖})
    (hb : ∀ w, 1 < ‖w‖ → ‖ψ w - w‖ ≤ C) :
    DifferentiableOn ℂ (Fext ψ) (ball 0 1) := by
  have hset : ball (0:ℂ) 1 \ {0} = {ζ : ℂ | 0 < ‖ζ‖ ∧ ‖ζ‖ < 1} := by
    ext ζ
    simp only [Set.mem_sdiff, mem_ball, dist_zero_right, Set.mem_singleton_iff, Set.mem_setOf_eq,
      norm_pos_iff]
    tauto
  have hbdd : BddAbove (norm ∘ regPart ψ '' (ball 0 1 \ {0})) := by
    rw [bddAbove_def]
    refine ⟨C, ?_⟩
    rintro y ⟨ζ, hζ, rfl⟩
    simp only [Function.comp_apply]
    obtain ⟨hζb, hζ0⟩ := hζ
    have hζne : ζ ≠ 0 := hζ0
    rw [regPart, if_neg hζne]
    refine hb ζ⁻¹ ?_
    have hlt : ‖ζ‖ < 1 := by simpa [mem_ball, dist_zero_right] using hζb
    rw [norm_inv, one_lt_inv₀ (norm_pos_iff.mpr hζne)]; exact hlt
  have hdiff : DifferentiableOn ℂ (regPart ψ) (ball 0 1 \ {0}) := by
    rw [hset]
    refine DifferentiableOn.congr ?_ (fun ζ hζ => by rw [regPart, if_neg (norm_pos_iff.mp hζ.1)])
    intro ζ hζ
    obtain ⟨hζ0, hζ1⟩ := hζ
    have hζne : ζ ≠ 0 := norm_pos_iff.mp hζ0
    have hinv : 1 < ‖ζ⁻¹‖ := by
      rw [norm_inv, one_lt_inv₀ (norm_pos_iff.mpr hζne)]; exact hζ1
    have h1 : DifferentiableAt ℂ ψ ζ⁻¹ := (hd.differentiableAt ((isOpen_lt_norm 1).mem_nhds hinv))
    have h2 : DifferentiableAt ℂ (fun ζ : ℂ => ζ⁻¹) ζ := differentiableAt_inv hζne
    exact ((h1.comp ζ h2).sub h2).differentiableWithinAt
  rw [Fext]
  exact differentiableOn_update_limUnder_of_bddAbove (ball_mem_nhds 0 one_pos) hdiff hbdd

/-- the Laurent coefficients at infinity: `-n`-th coefficient. -/
noncomputable def bco (ψ : ℂ → ℂ) (n : ℕ) : ℂ :=
  iteratedDeriv n (Fext ψ) 0 / (n.factorial : ℂ)

/-- circle integral form of the coefficients, valid at any radius in `(0,1)`. -/
lemma circle_integral_bco (ψ : ℂ → ℂ) (C : ℝ)
    (hd : DifferentiableOn ℂ ψ {w : ℂ | 1 < ‖w‖})
    (hb : ∀ w, 1 < ‖w‖ → ‖ψ w - w‖ ≤ C) (n : ℕ) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    ∮ z in C(0, s), (1 / (z - 0) ^ (n+1)) • Fext ψ z = (2 * ↑Real.pi * I) * bco ψ n := by
  have hFd : DifferentiableOn ℂ (Fext ψ) (ball 0 1) := Fext_diff ψ C hd hb
  have hcont : ContinuousOn (Fext ψ) (closedBall 0 s) := by
    refine hFd.continuousOn.mono (fun z hz => ?_)
    rw [mem_closedBall, dist_zero_right] at hz
    exact mem_ball_zero_iff.mpr (lt_of_le_of_lt hz hs1)
  have hdiff : ∀ z ∈ ball 0 s \ (∅ : Set ℂ), DifferentiableAt ℂ (Fext ψ) z := by
    intro z hz
    rw [Set.sdiff_empty] at hz
    have hz1 : z ∈ ball (0:ℂ) 1 := by
      rw [mem_ball, dist_zero_right] at hz ⊢; linarith [hz]
    exact hFd.differentiableAt (Metric.isOpen_ball.mem_nhds hz1)
  have h := Complex.circleIntegral_one_div_sub_center_pow_smul_of_differentiable_on_off_countable
      (R := s) (f := Fext ψ) (c := 0) (s := ∅) hs0 n Set.countable_empty hcont hdiff
  rw [h, bco, smul_eq_mul]
  field_simp

lemma hasSum_expansion (ψ : ℂ → ℂ) (C : ℝ)
    (hd : DifferentiableOn ℂ ψ {w : ℂ | 1 < ‖w‖})
    (hb : ∀ w, 1 < ‖w‖ → ‖ψ w - w‖ ≤ C) :
    ∀ ζ : ℂ, ‖ζ‖ < 1 → HasSum (fun n => bco ψ n * ζ^n) (Fext ψ ζ) := by
  intro ζ hζ
  obtain ⟨s, hs1, hs2⟩ : ∃ s : ℝ, ‖ζ‖ < s ∧ s < 1 := ⟨(‖ζ‖+1)/2, by linarith, by linarith⟩
  have hs0 : 0 < s := lt_of_le_of_lt (norm_nonneg ζ) hs1
  set R : NNReal := ⟨s, le_of_lt hs0⟩ with hRdef
  have hRc : (R : ℝ) = s := rfl
  have hFd : DifferentiableOn ℂ (Fext ψ) (ball 0 1) := Fext_diff ψ C hd hb
  have hcont : ContinuousOn (Fext ψ) (closedBall 0 R) := by
    refine hFd.continuousOn.mono (fun z hz => ?_)
    rw [mem_closedBall, dist_zero_right] at hz
    exact mem_ball_zero_iff.mpr (lt_of_le_of_lt (hRc ▸ hz) hs2)
  have hdiff : ∀ z ∈ ball 0 R \ (∅ : Set ℂ), DifferentiableAt ℂ (Fext ψ) z := by
    intro z hz
    rw [Set.sdiff_empty] at hz
    have hz1 : z ∈ ball (0:ℂ) 1 := by
      rw [mem_ball, dist_zero_right] at hz ⊢; rw [hRc] at hz; linarith [hz]
    exact hFd.differentiableAt (Metric.isOpen_ball.mem_nhds hz1)
  have hRpos : (0:NNReal) < R := NNReal.coe_lt_coe.mp (by rw [hRc]; exact hs0)
  have hps := Complex.hasFPowerSeriesOnBall_of_differentiable_off_countable
      (R := R) (c := 0) (f := Fext ψ) (s := ∅) Set.countable_empty hcont hdiff hRpos
  have hsum := hps.hasSum (y := ζ) (by
    rw [Metric.mem_eball, edist_zero_right]
    exact_mod_cast (hRc ▸ hs1 : ‖ζ‖ < (R:ℝ)))
  have hterm : (fun n => (cauchyPowerSeries (Fext ψ) 0 (R : ℝ) n) (fun _ => ζ))
      = (fun n => bco ψ n * ζ^n) := by
    funext n
    rw [cauchyPowerSeries_apply]
    simp only [sub_zero]
    rw [show (fun z : ℂ => (ζ / z) ^ n • z⁻¹ • Fext ψ z)
          = (fun z : ℂ => ζ^n * ((1 / (z - 0) ^ (n+1)) • Fext ψ z)) from by
        funext z; rw [sub_zero, div_eq_mul_inv]; ring_nf]
    rw [circleIntegral.integral_const_mul]
    rw [hRc, circle_integral_bco ψ C hd hb n hs0 hs2, smul_eq_mul]
    have h2pi : (2 * (↑Real.pi : ℂ) * I) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    field_simp
  rw [hterm] at hsum
  simpa [zero_add] using hsum


/-- Expansion of `ψ` on the exterior of the unit disk. -/
lemma psi_expansion (ψ : ℂ → ℂ) (C : ℝ)
    (hd : DifferentiableOn ℂ ψ {w : ℂ | 1 < ‖w‖})
    (hb : ∀ w, 1 < ‖w‖ → ‖ψ w - w‖ ≤ C) :
    ∀ z : ℂ, 1 < ‖z‖ → HasSum (fun n => bco ψ n * (z⁻¹)^n) (ψ z - z) := by
  intro z hz
  have hz0 : z ≠ 0 := by rintro rfl; norm_num at hz
  have hζ : ‖z⁻¹‖ < 1 := by
    rw [norm_inv, inv_lt_one₀ (norm_pos_iff.mpr hz0)]; exact hz
  have h := hasSum_expansion ψ C hd hb (z⁻¹) hζ
  rwa [Fext_eq ψ (inv_ne_zero hz0), inv_inv] at h

/-- The contour integral `(1/2i) ∮_{|z|=r} conj(ψ) ψ' dz`. -/
noncomputable def Aint (ψ : ℂ → ℂ) (r : ℝ) : ℂ :=
  (2 * I)⁻¹ * ∮ z in C(0, r), (starRingEnd ℂ (ψ z)) * deriv ψ z

/-- The complement of `ψ({|z|>r})` (the "filled-in" continuum). -/
def Eset (ψ : ℂ → ℂ) (r : ℝ) : Set ℂ := (ψ '' {z : ℂ | r < ‖z‖})ᶜ

end

end Work.LandLeaves
