import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.remov.Psi_slice_sinCos2_integrable
import Submission.Work.FTS.EllipticEst.remov.DzIter_one_Psi_estimate_sound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

/-- **The angular moment of `D_zΨ` vanishes for a datum of the weak class.**

This is the `Ψ`-half of `remov.Fstar_DzIter_one_eq_zero`: the moment condition needed to apply
the induction step `EllWeakPos_DzIter_one_shift` to the radially differentiated data
`(D_z F, D_z Ψ)`.

The proof is a *first-order* argument (no differentiation under the integral sign, hence no
`C¹`-up-to-the-boundary hypothesis): fix `z₀ > 0`, put
`B = ∫_θ ∂_zΨ(z₀,θ) sinθcos²θ dθ`, and for `h ∈ (0,z₀)` set
`G_h(θ) = (Ψ(z₀+h,θ) - Ψ(z₀,θ))/h - ∂_zΨ(z₀,θ)`.

* Because the two angular moments `F_*(Ψ)(z₀)`, `F_*(Ψ)(z₀+h)` vanish (a hypothesis) and
  `θ ↦ Ψ(z,θ) sinθcos²θ` is integrable (`Psi_slice_sinCos2_integrable`), linearity gives
  `∫_θ G_h(θ) sinθcos²θ dθ = -B`.
* On the other hand `G_h(θ) = h^{-1}∫_0^h (∂_zΨ(z₀+s,θ) - ∂_zΨ(z₀,θ)) ds`, so by the
  fundamental theorem of calculus along the `θ`-slice and Cauchy–Schwarz in `s`,
  `|G_h(θ)| ≤ (2/3)√h √(∫_0^h (∂_z²Ψ(z₀+s,θ))² ds)`, whence by Young's inequality and
  Tonelli `|B| ≤ K √h`, with `K` the weighted `ℋ^k`-energy of `z²∂_z²Ψ` divided by `z₀⁴` plus
  `π/2` (`DzIter_one_Psi_estimate`).

Letting `h → 0` gives `B = 0`, and `F_*(D_zΨ)(z₀) = z₀ B` because `D_z = z ∂_z` pulls out of the
angular integral. -/
theorem Fstar_DzIter_one_Psi {α : ℝ} {k : ℕ} (hk : 1 ≤ k) {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) :
    ∀ z, 0 < z → Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) z = 0 := by
  intro z₀ hz₀
  have hso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hcontσ : Continuous (fun p : ℝ × ℝ => Work.Elliptic.sinCos2 p.2) := by
    simp only [Work.Elliptic.sinCos2]; fun_prop
  have hsinCos2_nn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Work.Elliptic.sinCos2 θ := by
    intro θ hθ
    rw [Work.Elliptic.sinCos2]
    have h1 : 0 ≤ Real.sin θ :=
      Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
    nlinarith [sq_nonneg (Real.cos θ)]
  have hPsi : ∀ z, 0 < z → MeasureTheory.Integrable
      (fun θ : ℝ => Ψ z θ * Work.Elliptic.sinCos2 θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    intro z hz
    have h1 : MeasureTheory.Integrable
        (fun θ : ℝ => |Ψ z θ| * Work.Elliptic.sinCos2 θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      (Psi_slice_sinCos2_integrable hk h z hz).integrable
    refine h1.mono' ?_ ?_
    · exact Work.Spaces.aesm_slice_of_continuousOn_Qd
        (fun p : ℝ × ℝ => Ψ p.1 p.2 * Work.Elliptic.sinCos2 p.2)
        (hso.continuousOn.mul hcontσ.continuousOn) hz
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hsinCos2_nn θ hθ)]
  set B : ℝ := ∫ θ in Work.Spaces.Iθ, Work.Spaces.pz Ψ z₀ θ * Work.Elliptic.sinCos2 θ with hB
  have hF : Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) z₀ = z₀ * B := by
    rw [Work.Elliptic.Fstar, hB]
    rw [show (fun θ : ℝ => Work.Spaces.DzIter 1 Ψ z₀ θ * Work.Elliptic.sinCos2 θ)
        = fun θ : ℝ => z₀ * (Work.Spaces.pz Ψ z₀ θ * Work.Elliptic.sinCos2 θ) from by
      funext θ
      simp only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.Dz]
      ring]
    rw [MeasureTheory.integral_const_mul]
  by_cases hBint : MeasureTheory.Integrable
      (fun θ : ℝ => Work.Spaces.pz Ψ z₀ θ * Work.Elliptic.sinCos2 θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)
  · have hzero : B = 0 := by
      have hest := DzIter_one_Psi_estimate_sound hk h hPsi z₀ hz₀ hBint
      by_contra hne
      have hpos : 0 < |B| := abs_pos.mpr hne
      set K : ℝ := (∫ z in Work.Spaces.Iz,
              ∫ θ in Work.Spaces.Iθ,
                ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
                  * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2)
              / z₀ ^ 4
            + Real.pi / 2 with hKdef
      have hKnn : 0 ≤ K := by
        rw [hKdef]
        have h1 : 0 ≤ ∫ z in Work.Spaces.Iz,
              ∫ θ in Work.Spaces.Iθ,
                ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
                  * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 :=
          integral_nonneg fun z => integral_nonneg fun θ => sq_nonneg _
        have h2 : 0 ≤ z₀ ^ 4 := by positivity
        have h3 : 0 ≤ Real.pi / 2 := by positivity
        exact add_nonneg (div_nonneg h1 h2) h3
      set h₁ : ℝ := min (z₀ / 2) ((|B| / (2 * (K + 1))) ^ 2) with hh₁
      have hh₁pos : 0 < h₁ := by
        rw [hh₁]
        exact lt_min (by linarith) (by positivity)
      have hh₁lt : h₁ < z₀ := by
        rw [hh₁]
        exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
      have hb := hest h₁ ⟨hh₁pos, hh₁lt⟩
      have hK1 : 0 < K + 1 := by linarith
      have hsq : Real.sqrt h₁ ≤ |B| / (2 * (K + 1)) := by
        have hle : h₁ ≤ (|B| / (2 * (K + 1))) ^ 2 := by
          rw [hh₁]
          exact min_le_right _ _
        calc Real.sqrt h₁ ≤ Real.sqrt ((|B| / (2 * (K + 1))) ^ 2) := Real.sqrt_le_sqrt hle
          _ = |B| / (2 * (K + 1)) := by
              rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
      have hstep : K * Real.sqrt h₁ ≤ |B| / 2 := by
        have h1 : K * Real.sqrt h₁ ≤ K * (|B| / (2 * (K + 1))) :=
          mul_le_mul_of_nonneg_left hsq hKnn
        have h2 : K * (|B| / (2 * (K + 1))) ≤ |B| / 2 := by
          have hcoef : K / (2 * (K + 1)) ≤ 1 / 2 := by
            rw [div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 2)]
            linarith
          calc K * (|B| / (2 * (K + 1))) = (K / (2 * (K + 1))) * |B| := by ring
            _ ≤ (1 / 2) * |B| := mul_le_mul_of_nonneg_right hcoef (abs_nonneg B)
            _ = |B| / 2 := by ring
        linarith
      linarith [hb, hstep, hpos]
    rw [hF, hzero, mul_zero]
  · have hzero : B = 0 := by
      rw [hB]
      exact MeasureTheory.integral_undef hBint
    rw [hF, hzero, mul_zero]

end

end Work.FTS.EllipticEst.remov
