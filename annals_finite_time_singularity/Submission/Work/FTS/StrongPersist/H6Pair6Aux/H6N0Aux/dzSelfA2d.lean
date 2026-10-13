import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.boundarySeqs
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.truncBound
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.dzSelf2d
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bAux.dzSelf1dW

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux

/-!
## The weighted radial self-pairing with a coefficient `A(z,θ)`

With `w z = (1+z)²/z²`, `ρ = w²`, `s z = z ρ z = (1+z)⁴/z³` and `D = z ∂_z`, the exact
identity

`s' Y² + 2 ρ (DY) Y = (s Y²)'`

integrated against a coefficient `ψ` with `|ψ| ≤ A`, `|z ψ'| ≤ B` on `(0,∞)` gives (FTC on
`[ε,M]`, the boundary terms being killed along the dyadic minimiser sequences of `H = w²Y²`,
see `T5bAux.dzSelf1dW`)

`|∫_0^∞ w² ψ (zY') Y| ≤ (3A + B) ∫_0^∞ w² Y²`,

and with `A = B = K` the constant is `4K ≤ 5K`, which is `dzSelfA1d` below.

Applying this slicewise in `θ` with the coefficient `ψ = A(·,θ)` (hypotheses `hAbd`, `hAdz`
at fixed `θ ∈ (0,π/2)`), multiplying by `σ θ > 0` and integrating over `θ` against the
angular weight `σ` (Fubini, using the product-integrability hypotheses `hF`, `hD2`, `hcross`)
gives `dzSelfA2d`.
-/

noncomputable section

/-- **The one-dimensional slice bound.**  For a coefficient `ψ` with `|ψ| ≤ K` and
`|z ψ'| ≤ K` on `(0,∞)` and a radial profile `Y`,

`|∫_0^∞ w² ψ (z Y') Y| ≤ 5 K ∫_0^∞ w² Y²`.

This is `T5bAux.dzSelf1dW` with `A = B = K` (which gives the constant `3K + K = 4K ≤ 5K`). -/
theorem dzSelfA1d {K : ℝ} {ψ Y : ℝ → ℝ}
    (hK0 : 0 ≤ K)
    (hψsm : ContDiffOn ℝ 1 ψ (Set.Ioi 0))
    (hψA : ∀ z ∈ Set.Ioi (0 : ℝ), |ψ z| ≤ K)
    (hψB : ∀ z ∈ Set.Ioi (0 : ℝ), |z * deriv ψ z| ≤ K)
    (hY : ContDiffOn ℝ 1 Y (Set.Ioi 0))
    (hF : MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * (Y z) ^ 2)
      (Set.Ioi 0))
    (hD : MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2 * (z * deriv Y z) ^ 2) (Set.Ioi 0)) :
    |∫ z in Set.Ioi (0 : ℝ),
        (Work.Spaces.w z) ^ 2 * (ψ z * ((z * deriv Y z) * Y z))|
      ≤ 5 * K * ∫ z in Set.Ioi (0 : ℝ), (Work.Spaces.w z) ^ 2 * (Y z) ^ 2 := by
  have h1 := T5bAux.dzSelf1dW (ψ := ψ) (Y := Y) (A := K) (B := K)
    hK0 hK0 hψsm hψA hψB hY hF hD
  have hI0 : 0 ≤ ∫ z in Set.Ioi (0 : ℝ), (Work.Spaces.w z) ^ 2 * (Y z) ^ 2 :=
    setIntegral_nonneg measurableSet_Ioi (fun z _ => by positivity)
  have hIeq : (∫ z in Set.Ioi (0 : ℝ),
        (Work.Spaces.w z) ^ 2 * (ψ z * ((z * deriv Y z) * Y z)))
      = ∫ z in Set.Ioi (0 : ℝ),
        (Work.Spaces.w z) ^ 2 * ψ z * ((z * deriv Y z) * Y z) :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => by ring)
  calc |∫ z in Set.Ioi (0 : ℝ),
        (Work.Spaces.w z) ^ 2 * (ψ z * ((z * deriv Y z) * Y z))|
      = |∫ z in Set.Ioi (0 : ℝ),
          (Work.Spaces.w z) ^ 2 * ψ z * ((z * deriv Y z) * Y z)| := by rw [hIeq]
    _ ≤ (3 * K + K) * ∫ z in Set.Ioi (0 : ℝ), (Work.Spaces.w z) ^ 2 * (Y z) ^ 2 := h1
    _ = 4 * K * ∫ z in Set.Ioi (0 : ℝ), (Work.Spaces.w z) ^ 2 * (Y z) ^ 2 := by ring
    _ ≤ 5 * K * ∫ z in Set.Ioi (0 : ℝ), (Work.Spaces.w z) ^ 2 * (Y z) ^ 2 := by
        have hcoef : 4 * K ≤ 5 * K := by linarith
        calc 4 * K * ∫ z in Set.Ioi (0 : ℝ), (Work.Spaces.w z) ^ 2 * (Y z) ^ 2
            = (4 * K) * (∫ z in Set.Ioi (0 : ℝ), (Work.Spaces.w z) ^ 2 * (Y z) ^ 2) := by
              ring
          _ ≤ (5 * K) * (∫ z in Set.Ioi (0 : ℝ), (Work.Spaces.w z) ^ 2 * (Y z) ^ 2) :=
              mul_le_mul_of_nonneg_right hcoef hI0
          _ = 5 * K * ∫ z in Set.Ioi (0 : ℝ), (Work.Spaces.w z) ^ 2 * (Y z) ^ 2 := by ring

theorem dzSelfA2d {σ : ℝ → ℝ} {A V : ℝ → ℝ → ℝ} {K : ℝ}
    (hK0 : 0 ≤ K)
    (hσm : AEMeasurable σ (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hσpos : ∀ θ ∈ Set.Ioo 0 (π / 2), 0 < σ θ)
    (hA : ∀ θ ∈ Set.Ioo 0 (π / 2), ContDiffOn ℝ 1 (fun z => A z θ) (Set.Ioi 0))
    (hAbd : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → |A z θ| ≤ K)
    (hAdz : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |z * deriv (fun z' => A z' θ) z| ≤ K)
    (hV : ∀ θ ∈ Set.Ioo 0 (π / 2), ContDiffOn ℝ 1 (fun z => V z θ) (Set.Ioi 0))
    (hVae : AEMeasurable (Function.uncurry V)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hF : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * σ p.2 * (V p.1 p.2) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hD2 : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * σ p.2
        * (p.1 * Work.Spaces.pz V p.1 p.2) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hcross : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * σ p.2
        * (A p.1 p.2 * ((p.1 * Work.Spaces.pz V p.1 p.2) * V p.1 p.2)))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))) :
    |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.w z) ^ 2 * σ θ * (A z θ * ((z * Work.Spaces.pz V z θ) * V z θ))|
      ≤ 5 * K * ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.w z) ^ 2 * σ θ * (V z θ) ^ 2 := by
  have hΛz : MeasureTheory.volume.restrict Work.Spaces.Iz
      = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) :=
    Measure.restrict_congr_set dzSelf2d_Iz_ae
  have hΛθ : MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) :=
    Measure.restrict_congr_set dzSelf2d_Ith_ae
  have haeθ : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      θ ∈ Set.Ioo (0 : ℝ) (π / 2) := by
    have h := MeasureTheory.ae_restrict_mem (μ := (MeasureTheory.volume : Measure ℝ))
      (s := Set.Ioo (0 : ℝ) (π / 2)) measurableSet_Ioo
    rwa [← hΛθ] at h
  have hσae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), 0 < σ θ :=
    haeθ.mono (fun θ hmem => hσpos θ hmem)
  -- slice integrability of `w²V²` for a.e. `θ` (divide by `σ θ > 0`)
  have hsliceF : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * (V z θ) ^ 2)
        (Set.Ioi 0) := by
    have h1 : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        MeasureTheory.Integrable
          (fun z => (Work.Spaces.w z) ^ 2 * σ θ * (V z θ) ^ 2)
          (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
      MeasureTheory.Integrable.prod_left_ae hF
    filter_upwards [h1, hσae] with θ hθ hpos
    have h2 : MeasureTheory.Integrable
        (fun z => σ θ * ((Work.Spaces.w z) ^ 2 * (V z θ) ^ 2))
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
      simpa only [mul_comm, mul_left_comm, mul_assoc] using hθ
    have h3 : MeasureTheory.Integrable
        (fun z => (Work.Spaces.w z) ^ 2 * (V z θ) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
      (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (ne_of_gt hpos))
        (fun z => (Work.Spaces.w z) ^ 2 * (V z θ) ^ 2)).mp h2
    rw [hΛz] at h3
    exact h3
  -- slice integrability of `w²(z∂_zV)²` for a.e. `θ`
  have hsliceD : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      MeasureTheory.IntegrableOn
        (fun z => (Work.Spaces.w z) ^ 2 * (z * Work.Spaces.pz V z θ) ^ 2)
        (Set.Ioi 0) := by
    have h1 : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        MeasureTheory.Integrable
          (fun z => (Work.Spaces.w z) ^ 2 * σ θ * (z * Work.Spaces.pz V z θ) ^ 2)
          (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
      MeasureTheory.Integrable.prod_left_ae hD2
    filter_upwards [h1, hσae] with θ hθ hpos
    have h2 : MeasureTheory.Integrable
        (fun z => σ θ * ((Work.Spaces.w z) ^ 2 * (z * Work.Spaces.pz V z θ) ^ 2))
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
      simpa only [mul_comm, mul_left_comm, mul_assoc] using hθ
    have h3 : MeasureTheory.Integrable
        (fun z => (Work.Spaces.w z) ^ 2 * (z * Work.Spaces.pz V z θ) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
      (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (ne_of_gt hpos))
        (fun z => (Work.Spaces.w z) ^ 2 * (z * Work.Spaces.pz V z θ) ^ 2)).mp h2
    rw [hΛz] at h3
    exact h3
  -- the a.e.-`θ` slicewise 1-D bound with coefficient `A(·,θ)`
  have hkey : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      |∫ z in Work.Spaces.Iz,
          (Work.Spaces.w z) ^ 2 * σ θ * (A z θ * ((z * Work.Spaces.pz V z θ) * V z θ))|
        ≤ 5 * K * (σ θ * ∫ z in Set.Ioi (0 : ℝ),
            (Work.Spaces.w z) ^ 2 * (V z θ) ^ 2) := by
    filter_upwards [haeθ, hσae, hsliceF, hsliceD] with θ hmem hpos hsf hsd
    have h1 : |∫ z in Set.Ioi (0 : ℝ),
          (Work.Spaces.w z) ^ 2
            * (A z θ * ((z * deriv (fun z' => V z' θ) z) * V z θ))|
        ≤ 5 * K * ∫ z in Set.Ioi (0 : ℝ), (Work.Spaces.w z) ^ 2 * (V z θ) ^ 2 :=
      dzSelfA1d (K := K) hK0 (hA θ hmem)
        (fun z hz => hAbd z θ hz hmem.1 hmem.2)
        (fun z hz => hAdz z θ hz hmem.1 hmem.2) (hV θ hmem) hsf hsd
    have hfun : (fun z => (Work.Spaces.w z) ^ 2 * σ θ
          * (A z θ * ((z * Work.Spaces.pz V z θ) * V z θ)))
        = fun z => σ θ * ((Work.Spaces.w z) ^ 2
          * (A z θ * ((z * deriv (fun z' => V z' θ) z) * V z θ))) := by
      funext z
      simp only [Work.Spaces.pz]
      ring
    have hL : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * σ θ
          * (A z θ * ((z * Work.Spaces.pz V z θ) * V z θ)))
        = σ θ * ∫ z in Set.Ioi (0 : ℝ), (Work.Spaces.w z) ^ 2
            * (A z θ * ((z * deriv (fun z' => V z' θ) z) * V z θ)) := by
      rw [hfun, setIntegral_congr_set dzSelf2d_Iz_ae]
      rw [MeasureTheory.integral_const_mul]
    rw [hL, abs_mul, abs_of_pos hpos]
    calc σ θ * |∫ z in Set.Ioi (0 : ℝ), (Work.Spaces.w z) ^ 2
            * (A z θ * ((z * deriv (fun z' => V z' θ) z) * V z θ))|
        ≤ σ θ * (5 * K * ∫ z in Set.Ioi (0 : ℝ),
            (Work.Spaces.w z) ^ 2 * (V z θ) ^ 2) :=
          mul_le_mul_of_nonneg_left h1 hpos.le
      _ = 5 * K * (σ θ * ∫ z in Set.Ioi (0 : ℝ),
            (Work.Spaces.w z) ^ 2 * (V z θ) ^ 2) := by ring
  -- integrability of the upper bound
  have hψint : MeasureTheory.Integrable
      (fun θ => σ θ * ∫ z in Set.Ioi (0 : ℝ), (Work.Spaces.w z) ^ 2 * (V z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    have h := MeasureTheory.Integrable.integral_prod_right hF
    have hfun : (fun θ => ∫ z, (Work.Spaces.w z) ^ 2 * σ θ * (V z θ) ^ 2
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iz))
        = fun θ => σ θ * ∫ z in Set.Ioi (0 : ℝ),
            (Work.Spaces.w z) ^ 2 * (V z θ) ^ 2 := by
      funext θ
      rw [show (fun z => (Work.Spaces.w z) ^ 2 * σ θ * (V z θ) ^ 2)
          = fun z => σ θ * ((Work.Spaces.w z) ^ 2 * (V z θ) ^ 2) from by
            funext z; ring]
      rw [MeasureTheory.integral_const_mul]
      rw [setIntegral_congr_set dzSelf2d_Iz_ae]
    rwa [hfun] at h
  have hRHSint : MeasureTheory.Integrable
      (fun θ => 5 * K * (σ θ * ∫ z in Set.Ioi (0 : ℝ),
        (Work.Spaces.w z) ^ 2 * (V z θ) ^ 2))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    hψint.const_mul (5 * K)
  have hLHSint : MeasureTheory.Integrable
      (fun θ => |∫ z in Work.Spaces.Iz,
        (Work.Spaces.w z) ^ 2 * σ θ * (A z θ * ((z * Work.Spaces.pz V z θ) * V z θ))|)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    have h := MeasureTheory.Integrable.integral_prod_right hcross
    exact h.abs
  -- Fubini and the comparison
  have hswap : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.w z) ^ 2 * σ θ * (A z θ * ((z * Work.Spaces.pz V z θ) * V z θ)))
      = ∫ θ in Work.Spaces.Iθ, ∫ z in Work.Spaces.Iz,
        (Work.Spaces.w z) ^ 2 * σ θ * (A z θ * ((z * Work.Spaces.pz V z θ) * V z θ)) :=
    MeasureTheory.integral_integral_swap hcross
  calc |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.w z) ^ 2 * σ θ * (A z θ * ((z * Work.Spaces.pz V z θ) * V z θ))|
      = |∫ θ in Work.Spaces.Iθ, ∫ z in Work.Spaces.Iz,
          (Work.Spaces.w z) ^ 2 * σ θ
            * (A z θ * ((z * Work.Spaces.pz V z θ) * V z θ))| := by rw [hswap]
    _ ≤ ∫ θ in Work.Spaces.Iθ,
          |∫ z in Work.Spaces.Iz,
            (Work.Spaces.w z) ^ 2 * σ θ
              * (A z θ * ((z * Work.Spaces.pz V z θ) * V z θ))| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ θ in Work.Spaces.Iθ, 5 * K * (σ θ * ∫ z in Set.Ioi (0 : ℝ),
          (Work.Spaces.w z) ^ 2 * (V z θ) ^ 2) :=
        integral_mono_ae hLHSint hRHSint hkey
    _ = 5 * K * ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.w z) ^ 2 * σ θ * (V z θ) ^ 2 := by
        rw [MeasureTheory.integral_const_mul]
        congr 1
        rw [show (fun θ => σ θ * ∫ z in Set.Ioi (0 : ℝ),
              (Work.Spaces.w z) ^ 2 * (V z θ) ^ 2)
            = fun θ => ∫ z in Work.Spaces.Iz,
              (Work.Spaces.w z) ^ 2 * σ θ * (V z θ) ^ 2 from by
              funext θ
              rw [← MeasureTheory.integral_const_mul]
              rw [← setIntegral_congr_set dzSelf2d_Iz_ae]
              exact MeasureTheory.integral_congr_ae
                (Filter.Eventually.of_forall fun z => by ring)]
        rw [← MeasureTheory.integral_integral_swap hF]

end

end Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux
