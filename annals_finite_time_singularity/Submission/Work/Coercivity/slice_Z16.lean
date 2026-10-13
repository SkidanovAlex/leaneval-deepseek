import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Coercivity.zAux
import Submission.Work.Coercivity.wip_L_self
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Coercivity.slice_ibp_eta
import Submission.Work.Coercivity.L_mul_self_Weta
import Submission.Work.Coercivity.slice_Z16_integrable

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Coercivity

/-- **The `Z₁+Z₆` slice identity of the `D_z`-coercivity estimate (Elgindi, Annals 194 (3) 2021,
§"`L²` coercivity for `𝓛_Γ^T` with one `z`-derivative").**

Writing `g = D_z f` and `Weta = w²·sin(2θ)^{-η}`, the pointwise identity
`𝓛(g)·w = g·w + z∂_z(g·w)` (`L_mul_w_deriv`) gives, for every fixed `z > 0` and every `θ`,

  `L g · g · Weta = ½ g² · Weta + ½ ∂_z(z (g w)²) · sin(2θ)^{-η}`,

and the `θ`-integration by parts of `D_θ g · g · Weta` (`slice_ibp_eta`, whose boundary term
`sin(2θ)^{1-η} g²` vanishes because `η = 99/100 < 1`) gives

  `∫_θ D_θ g · g · Weta = (η-1) ∫_θ cos(2θ) g² · Weta`.

Since `Z16 = Z1 + Z6 = 𝓛(D_z f) - (3/(1+z)) D_θ(D_z f)`, adding `-(3/(1+z))` times the second
identity to the `θ`-integral of the first yields exactly the identity below. -/
theorem slice_Z16 (f : ℝ → ℝ → ℝ) (hsm : Spaces.SmoothNbhd f) :
    ∀ z, 0 < z → (∫ θ in Spaces.Iθ, Z16 f z θ * Spaces.Dz f z θ * Weta z θ)
      = (1 / 2) * (∫ θ in Spaces.Iθ, (Spaces.Dz f z θ) ^ 2 * Weta z θ)
        + (1 / 2) * (∫ θ in Spaces.Iθ,
            deriv (fun z' => z' * (Spaces.Dz f z' θ * Spaces.w z') ^ 2) z
              * (Real.sin (2 * θ)) ^ (-Spaces.eta))
        + (3 * (1 - Spaces.eta) / (1 + z))
            * (∫ θ in Spaces.Iθ, Real.cos (2 * θ) * (Spaces.Dz f z θ) ^ 2 * Weta z θ) := by
  intro z hz
  have hg : Spaces.SmoothNbhd (Spaces.Dz f) := Work.Spaces.SmoothNbhd.Dz hsm
  have hIBP := slice_ibp_eta (Spaces.Dz f) hg hz
  have hBC := slice_Z16_integrable f hsm hz
  have hLmul : ∀ θ ∈ Spaces.Iθ, L (Spaces.Dz f) z θ * Spaces.Dz f z θ * Weta z θ
      = (1 / 2) * (Spaces.Dz f z θ) ^ 2 * Weta z θ
        + (1 / 2) * deriv (fun z' => z' * (Spaces.Dz f z' θ * Spaces.w z') ^ 2) z
            * (Real.sin (2 * θ)) ^ (-Spaces.eta) :=
    fun θ hθ => L_mul_self_Weta (Spaces.Dz f) hg hz hθ
  have hIA := hBC.1
  have hIB := hBC.2.1
  have hIX := hBC.2.2.1
  have hIY := hBC.2.2.2
  -- (1) the pointwise identity for the `𝓛(D_z f)` term, integrated over `θ`
  have hA_pt : ∀ θ ∈ Spaces.Iθ, L (Spaces.Dz f) z θ * Spaces.Dz f z θ * Weta z θ
      = (1 / 2) * ((Spaces.Dz f z θ) ^ 2 * Weta z θ)
        + (1 / 2) * (deriv (fun z' => z' * (Spaces.Dz f z' θ * Spaces.w z') ^ 2) z
            * (Real.sin (2 * θ)) ^ (-Spaces.eta)) := by
    intro θ hθ
    rw [hLmul θ hθ]; ring
  have hA_eq : ∫ θ in Spaces.Iθ, L (Spaces.Dz f) z θ * Spaces.Dz f z θ * Weta z θ
      = (1 / 2) * (∫ θ in Spaces.Iθ, (Spaces.Dz f z θ) ^ 2 * Weta z θ)
        + (1 / 2) * (∫ θ in Spaces.Iθ,
            deriv (fun z' => z' * (Spaces.Dz f z' θ * Spaces.w z') ^ 2) z
              * (Real.sin (2 * θ)) ^ (-Spaces.eta)) := by
    calc ∫ θ in Spaces.Iθ, L (Spaces.Dz f) z θ * Spaces.Dz f z θ * Weta z θ
        = ∫ θ in Spaces.Iθ, ((1 / 2) * ((Spaces.Dz f z θ) ^ 2 * Weta z θ)
            + (1 / 2) * (deriv (fun z' => z' * (Spaces.Dz f z' θ * Spaces.w z') ^ 2) z
                * (Real.sin (2 * θ)) ^ (-Spaces.eta))) :=
          MeasureTheory.setIntegral_congr_fun measurableSet_Icc hA_pt
      _ = (1 / 2) * (∫ θ in Spaces.Iθ, (Spaces.Dz f z θ) ^ 2 * Weta z θ)
            + (1 / 2) * (∫ θ in Spaces.Iθ,
                deriv (fun z' => z' * (Spaces.Dz f z' θ * Spaces.w z') ^ 2) z
                  * (Real.sin (2 * θ)) ^ (-Spaces.eta)) := by
          rw [MeasureTheory.integral_add (hIX.const_mul (1 / 2)) (hIY.const_mul (1 / 2)),
              MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  -- (2) the `θ`-integration by parts for the `Z₆` term
  have hB_eq : ∫ θ in Spaces.Iθ, Spaces.Dth (Spaces.Dz f) z θ * Spaces.Dz f z θ * Weta z θ
      = (Spaces.eta - 1)
          * ∫ θ in Spaces.Iθ, Real.cos (2 * θ) * (Spaces.Dz f z θ) ^ 2 * Weta z θ := by
    have e1 : ∫ θ in Spaces.Iθ, Spaces.Dth (Spaces.Dz f) z θ * Spaces.Dz f z θ * Weta z θ
        = Spaces.w z ^ 2 * ∫ θ in Spaces.Iθ,
            Spaces.Dth (Spaces.Dz f) z θ * Spaces.Dz f z θ
              * (Real.sin (2 * θ)) ^ (-Spaces.eta) := by
      have h2 : ∫ θ in Spaces.Iθ, Spaces.Dth (Spaces.Dz f) z θ * Spaces.Dz f z θ * Weta z θ
          = ∫ θ in Spaces.Iθ, Spaces.w z ^ 2
              * (Spaces.Dth (Spaces.Dz f) z θ * Spaces.Dz f z θ
                  * (Real.sin (2 * θ)) ^ (-Spaces.eta)) := by
        apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
        intro θ hθ; simp only [Weta]; ring
      rw [h2, MeasureTheory.integral_const_mul]
    have e2 : ∫ θ in Spaces.Iθ, Real.cos (2 * θ) * (Spaces.Dz f z θ) ^ 2 * Weta z θ
        = Spaces.w z ^ 2 * ∫ θ in Spaces.Iθ,
            Real.cos (2 * θ) * (Spaces.Dz f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta) := by
      have h2 : ∫ θ in Spaces.Iθ, Real.cos (2 * θ) * (Spaces.Dz f z θ) ^ 2 * Weta z θ
          = ∫ θ in Spaces.Iθ, Spaces.w z ^ 2
              * (Real.cos (2 * θ) * (Spaces.Dz f z θ) ^ 2
                  * (Real.sin (2 * θ)) ^ (-Spaces.eta)) := by
        apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
        intro θ hθ; simp only [Weta]; ring
      rw [h2, MeasureTheory.integral_const_mul]
    rw [e1, e2, hIBP]; ring
  -- (3) split the integrand of the left-hand side
  have hG_pt : ∀ θ ∈ Spaces.Iθ, Z16 f z θ * Spaces.Dz f z θ * Weta z θ
      = L (Spaces.Dz f) z θ * Spaces.Dz f z θ * Weta z θ
        + (-(3 / (1 + z)))
            * (Spaces.Dth (Spaces.Dz f) z θ * Spaces.Dz f z θ * Weta z θ) := by
    intro θ hθ
    unfold Z16 Z1 Z6
    ring
  have hG_eq : ∫ θ in Spaces.Iθ, Z16 f z θ * Spaces.Dz f z θ * Weta z θ
      = (∫ θ in Spaces.Iθ, L (Spaces.Dz f) z θ * Spaces.Dz f z θ * Weta z θ)
        + (-(3 / (1 + z)))
            * (∫ θ in Spaces.Iθ, Spaces.Dth (Spaces.Dz f) z θ * Spaces.Dz f z θ * Weta z θ) := by
    have h1 : ∫ θ in Spaces.Iθ, Z16 f z θ * Spaces.Dz f z θ * Weta z θ
        = ∫ θ in Spaces.Iθ, (L (Spaces.Dz f) z θ * Spaces.Dz f z θ * Weta z θ
            + (-(3 / (1 + z)))
              * (Spaces.Dth (Spaces.Dz f) z θ * Spaces.Dz f z θ * Weta z θ)) :=
      MeasureTheory.setIntegral_congr_fun measurableSet_Icc hG_pt
    rw [h1, MeasureTheory.integral_add (μ := MeasureTheory.volume.restrict Spaces.Iθ)
        hIA (hIB.const_mul (-(3 / (1 + z)))), MeasureTheory.integral_const_mul]
  rw [hG_eq, hA_eq, hB_eq]
  ring

end Work.Coercivity
