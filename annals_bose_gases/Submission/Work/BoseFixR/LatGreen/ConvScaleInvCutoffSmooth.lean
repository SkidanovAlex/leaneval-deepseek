import Mathlib.Tactic.Have
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Submission.Work.BoseFixR.LatGreen.ConvScaleInvCutoff
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixR.LatGreen

open Metric
open scoped Topology ContDiff

/-!
# `Work.BoseFixR.LatGreen.ConvScaleInvCutoffSmooth`

The `C^∞` version of `Work.BoseFixR.LatGreen.ConvScaleInvCutoff`: the same bump construction
`F = φ · c⁻¹` (`c := convScale ℓ`), but now smooth of every order rather than merely `C¹`.

The only new ingredient is that the auxiliary lemma `contDiff_one_mul_inv_of_tsupport_ne_zero` of
`ConvScaleInvCutoff` holds with `1` replaced by an arbitrary `n : ℕ` (the bump `φ` is `C^n` for
every `n`, and at a point where `c` vanishes the whole product vanishes identically on a
neighbourhood).  Everything else -- the compactness argument producing `δ > 0` with `c > 1/4` on
`closedBall 0 (R + δ)`, the bump `φ`, the agreement on `closedBall 0 R` and the bound `|F| ≤ 2` --
is taken from `ConvScaleInvCutoff`.
-/

/-- **`φ · c⁻¹` is `C^n` if `c` is `C^n` and nonvanishing on the closed support of the smooth bump
`φ`.**  At a point `x` either `c x ≠ 0`, and then `φ · c⁻¹` is `C^n` there as a product of the
smooth `φ` with `c⁻¹` (`ContDiffAt.inv`), or `c x = 0`, and then `x` lies outside the closed support
of `φ`, on a neighbourhood of which `φ` vanishes identically, so that `φ · c⁻¹` is locally `0`. -/
lemma contDiff_mul_inv_of_tsupport_ne_zero {n : ℕ} {c : EuclideanSpace ℝ (Fin 3) → ℝ}
    {φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin 3))} (hc : ContDiff ℝ n c)
    (hφ : ∀ x ∈ tsupport (φ : EuclideanSpace ℝ (Fin 3) → ℝ), c x ≠ 0) :
    ContDiff ℝ n (fun x => (φ : EuclideanSpace ℝ (Fin 3) → ℝ) x * (c x)⁻¹) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : c x = 0
  · have hxnot : x ∉ tsupport (φ : EuclideanSpace ℝ (Fin 3) → ℝ) := fun h => hφ x h hx
    have hopen : IsOpen (tsupport (φ : EuclideanSpace ℝ (Fin 3) → ℝ))ᶜ :=
      (isClosed_tsupport _).isOpen_compl
    refine (contDiffAt_const (c := (0 : ℝ)) (x := x) (n := n)).congr_of_eventuallyEq ?_
    filter_upwards [hopen.mem_nhds hxnot] with y hy
    have hy0 : (φ : EuclideanSpace ℝ (Fin 3) → ℝ) y = 0 := by
      by_contra hne
      exact hy (subset_tsupport _ hne)
    simp [hy0]
  · exact (ContDiffBump.contDiff φ).contDiffAt.mul (hc.contDiffAt.inv hx)

/-- **A compactly supported smooth function agreeing with `1/(χ⋆χ)(·/ℓ)` on `ball 0 R`.**

With `0 < ℓ` and `R ≤ ℓ·chiR0` (`Submission.BoseGases.chiR0`), there is
`F : ℝ³ → ℝ` with

* `ContDiff ℝ n F` for every `n : ℕ`, and `HasCompactSupport F`, and
* `F x = (Submission.BoseGases.convScale ℓ x)⁻¹` and `|F x| ≤ 2` for `‖x‖ ≤ R`.

This is the smooth, compactly supported factor fed into
`Work.BoseFixR.LatGreen.RadialSmoothCosDecaySchwartz` in the alternative
(Fourier) proof of `Work.BoseFixR.LatGreen.W1funDecay`: `W₁ = g₀/(χ⋆χ)(·/ℓ)` and
`g₀` is supported in `ball 0 R`, so multiplying by a bump that is `1` there
changes nothing on the support of `g₀`.

Route: `c := Submission.BoseGases.convScale ℓ = (conv3 χ χ) ∘ (ℓ⁻¹ • ·)` is
`C^∞` (`Submission.CubicChi.conv_contDiff`), and `c ≥ 1/2` on `closedBall 0 R`
(`Submission.BoseGases.convScale_ge_half_ball`, from `R ≤ ℓ·chiR0`); by
continuity `c ≥ 1/4` on some `closedBall 0 (R + δ)`, `δ > 0`. Take a smooth bump
`φ` which is `1` on `closedBall 0 R` and supported in `ball 0 (R + δ)`
(`ContDiffBump`, scaled), and set `F := φ · c⁻¹`. Then `F` is `C^∞` (inside
`support φ ⊆ ball 0 (R+δ)` use `c ≥ 1/4 > 0` and smoothness of `c⁻¹`; outside
`support φ` the function vanishes on a neighbourhood of the point) and compactly
supported (`support F ⊆ support φ`), and on `closedBall 0 R` we have `φ = 1`,
`c ≥ 1/2`, so `F x = c x⁻¹` and `|F x| ≤ 2`. -/
theorem ConvScaleInvCutoffSmooth {ℓ R : ℝ} (hℓ : 0 < ℓ) (hR : 0 < R)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0) :
    ∃ F : EuclideanSpace ℝ (Fin 3) → ℝ, (∀ n : ℕ, ContDiff ℝ n F) ∧ HasCompactSupport F ∧
      (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ R → F x = (Submission.BoseGases.convScale ℓ x)⁻¹) ∧
      (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ R → |F x| ≤ 2) := by
  have hc : ContDiff ℝ ∞ (Submission.BoseGases.convScale ℓ) := convScale_contDiff ℓ
  -- `c ≥ 1/2` on the ball, hence `c > 1/4` on a slightly larger ball
  obtain ⟨δ, hδpos, hδ⟩ := exists_add_pos_lt_of_closedBall (a := (1 : ℝ) / 4) hR.le hc.continuous
    (fun x hx => lt_of_lt_of_le (by norm_num)
      (Submission.BoseGases.convScale_ge_half_ball hℓ hR.le hRℓ hx))
  -- the smooth bump `φ ≡ 1` on `closedBall 0 R`, supported in `closedBall 0 (R + δ)`
  let φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin 3)) := ⟨R, R + δ, hR, by linarith⟩
  have hφrIn : φ.rIn = R := rfl
  have hφrOut : φ.rOut = R + δ := rfl
  have hφ_one : ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ R →
      (φ : EuclideanSpace ℝ (Fin 3) → ℝ) x = 1 := by
    intro x hx
    exact ContDiffBump.one_of_mem_closedBall φ
      (by simpa [hφrIn, mem_closedBall, dist_eq_norm] using hx)
  have hφ_nz : ∀ x ∈ tsupport (φ : EuclideanSpace ℝ (Fin 3) → ℝ),
      Submission.BoseGases.convScale ℓ x ≠ 0 := by
    intro x hx
    rw [ContDiffBump.tsupport_eq φ, hφrOut] at hx
    exact ne_of_gt (lt_trans (by norm_num : (0 : ℝ) < 1 / 4)
      (hδ x (by simpa [mem_closedBall, dist_eq_norm] using hx)))
  refine ⟨fun x => (φ : EuclideanSpace ℝ (Fin 3) → ℝ) x * (Submission.BoseGases.convScale ℓ x)⁻¹,
    ?_, ?_, ?_, ?_⟩
  · intro n
    exact contDiff_mul_inv_of_tsupport_ne_zero
      (hc.of_le (WithTop.coe_le_coe.mpr le_top)) hφ_nz
  · exact (φ.hasCompactSupport).mul_right
  · intro x hx
    simp only [hφ_one x hx, one_mul]
  · intro x hx
    have hc1 : (1 : ℝ)/2 ≤ Submission.BoseGases.convScale ℓ x :=
      Submission.BoseGases.convScale_ge_half_ball hℓ hR.le hRℓ hx
    have hcpos : 0 < Submission.BoseGases.convScale ℓ x := by linarith
    have hinv : (Submission.BoseGases.convScale ℓ x)⁻¹ ≤ 2 := by
      have h := (inv_le_inv₀ hcpos (by norm_num : (0 : ℝ) < 1/2)).2 hc1
      simpa using h
    change |(φ : EuclideanSpace ℝ (Fin 3) → ℝ) x * (Submission.BoseGases.convScale ℓ x)⁻¹| ≤ 2
    rw [hφ_one x hx, one_mul, abs_of_nonneg (inv_nonneg.mpr hcpos.le)]
    exact hinv

end Work.BoseFixR.LatGreen
