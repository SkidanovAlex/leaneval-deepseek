/-
Copyright: work module for the Elgindi finite-time singularity project.

# The radial-slice energy `T` of a mixed slot is bounded by the `ℋ⁴`-norm

For `f` of class `C^∞` on the open quadrant with `HkMem α 4 f` (`0 < α`) and any `a b`
with `a + b ≤ 2`, the mixed slot `D_z^{b+1} D_θ^{a+1} f` has finite radial-slice energy

  `T(σ) = sin(2σ)^{-γ} · ∫_s (D_z^{b+1} D_θ^{a+1} f)² w²`     (`γ = gam α`),

it is integrable over `Iθ`, and `∫_θ T ≤ HkSq α 4 f`.

The proof is a direct Tonelli argument.  The pointwise identity
`(D_z^{b+1}D_θ^{a+1}f · Wt)² = sin(2θ)^{-γ}·((D_z^{b+1}D_θ^{a+1}f)² w²)` (valid on `Iθ`,
`Wt² = w² sin(2θ)^{-γ}`) exhibits `T` as the angular partially-integrated mixed slot of the
`ℋ⁴`-integrand, which is pointwise dominated by `HkIntegrand α 4 f`; the exchange of the two
iterated integrals is Tonelli for the (nonnegative, product-integrable) slot, and the result
is `HkSq`.  The Tonelli swap for the whole `ℋ⁴`-integrand of an open-class datum is
`Work.FTS.TransportS.SupDzAux.sda_HkSqSwap_open`, and the product integrability of the single
mixed slot is `Work.FTS.EllipticEst.AeSlotOneAe.Interp.integrable_uncurry_slot_mixed`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.TransportS.SupDzAux.SdaAux
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.EllipticEst.AeSlotOneAe.Interp.TkA_slotIntegrable

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.SupPort

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false

/-- `sin (2θ) ≥ 0` for `θ ∈ Iθ`. -/
theorem sin_two_nonneg_Iθ_fts {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
    (by linarith [hθ.2, Real.pi_pos])

/-- The pointwise identity behind the mixed-slot energy: on `Iθ`, the square of the weighted
mixed slot is the angular weight `sin(2θ)^{-γ}` times the square of the unweighted mixed slot
against `w²`. -/
theorem mixed_Wt_sq_eq_fts (α : ℝ) (f : ℝ → ℝ → ℝ) (j i : ℕ) {s θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.mixed j i f s θ * Work.Spaces.Wt α s θ) ^ 2
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        * ((Work.Spaces.mixed j i f s θ) ^ 2 * (Work.Spaces.w s) ^ 2) := by
  have hsq : ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    rw [← Real.rpow_natCast ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) 2]
    simp only [Nat.cast_ofNat]
    rw [← Real.rpow_mul (sin_two_nonneg_Iθ_fts hθ) (-(Work.Spaces.gam α / 2)) 2]
    congr 1
    ring
  rw [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow, mul_pow, hsq]
  ring

theorem mixed_T_le_HkSq {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    (b a : ℕ) (hab : a + b ≤ 2) :
    MeasureTheory.IntegrableOn (fun σ => (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
        * ∫ s in Work.Spaces.Iz,
            (Work.Spaces.mixed (b + 1) (a + 1) f s σ) ^ 2 * (Work.Spaces.w s) ^ 2)
      Work.Spaces.Iθ
    ∧ (∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
        * ∫ s in Work.Spaces.Iz,
            (Work.Spaces.mixed (b + 1) (a + 1) f s σ) ^ 2 * (Work.Spaces.w s) ^ 2)
      ≤ Work.Spaces.HkSq α 4 f := by
  have hi : 1 ≤ a + 1 := by omega
  have hij : (a + 1) + (b + 1) ≤ 4 := by omega
  -- The weighted mixed slot, as a function of `(z,θ)`, is product-integrable.
  have hΦint : MeasureTheory.Integrable
      (fun p : ℝ × ℝ =>
        (Work.Spaces.mixed (b + 1) (a + 1) f p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.FTS.EllipticEst.AeSlotOneAe.Interp.integrable_uncurry_slot_mixed
      hF hmem (b + 1) (a + 1) hi hij
  -- Tonelli for the `ℋ⁴`-integrand of an open-class datum.
  obtain ⟨hswap, hGint, hGslice⟩ :=
    Work.FTS.TransportS.SupDzAux.sda_HkSqSwap_open α f hF hmem
  -- The angular partial integral of the slot is integrable.
  have hΦθ : MeasureTheory.Integrable
      (fun θ : ℝ => ∫ z in Work.Spaces.Iz,
        (Work.Spaces.mixed (b + 1) (a + 1) f z θ * Work.Spaces.Wt α z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    hΦint.integral_prod_right
  -- Pointwise domination and monotonicity of the inner integral.
  have hmono : (∫ θ in Work.Spaces.Iθ, (∫ z in Work.Spaces.Iz,
        (Work.Spaces.mixed (b + 1) (a + 1) f z θ * Work.Spaces.Wt α z θ) ^ 2))
      ≤ ∫ θ in Work.Spaces.Iθ,
          (∫ z in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f z θ) := by
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => MeasureTheory.integral_nonneg fun z => sq_nonneg _)
      hGint ?_
    filter_upwards [hGslice] with θ hθint
    exact MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun z => sq_nonneg _) hθint
      (Filter.Eventually.of_forall fun z =>
        Work.Spaces.sq_le_HkIntegrand_mixed α 4 f z θ (a + 1) (b + 1) hi hij)
  -- The two descriptions of the angular integrand agree on `Iθ`.
  have hae : (fun σ : ℝ => (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
        * ∫ s in Work.Spaces.Iz,
            (Work.Spaces.mixed (b + 1) (a + 1) f s σ) ^ 2 * (Work.Spaces.w s) ^ 2)
      =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun θ : ℝ => ∫ z in Work.Spaces.Iz,
        (Work.Spaces.mixed (b + 1) (a + 1) f z θ * Work.Spaces.Wt α z θ) ^ 2) := by
    refine MeasureTheory.ae_restrict_of_forall_mem
      (show MeasurableSet Work.Spaces.Iθ from by
        rw [Work.Spaces.Iθ]; exact measurableSet_Icc) fun θ hθ => ?_
    show (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        * (∫ s in Work.Spaces.Iz,
            (Work.Spaces.mixed (b + 1) (a + 1) f s θ) ^ 2 * (Work.Spaces.w s) ^ 2)
      = ∫ z in Work.Spaces.Iz,
          (Work.Spaces.mixed (b + 1) (a + 1) f z θ * Work.Spaces.Wt α z θ) ^ 2
    have hcast : (∫ z in Work.Spaces.Iz,
          (Work.Spaces.mixed (b + 1) (a + 1) f z θ * Work.Spaces.Wt α z θ) ^ 2)
        = ∫ z in Work.Spaces.Iz, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * ((Work.Spaces.mixed (b + 1) (a + 1) f z θ) ^ 2 * (Work.Spaces.w z) ^ 2) :=
      MeasureTheory.integral_congr_ae
        (Filter.Eventually.of_forall fun z => mixed_Wt_sq_eq_fts α f (b + 1) (a + 1) hθ)
    rw [hcast, MeasureTheory.integral_const_mul]
  refine ⟨hΦθ.congr hae.symm, ?_⟩
  calc (∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
        * ∫ s in Work.Spaces.Iz,
            (Work.Spaces.mixed (b + 1) (a + 1) f s σ) ^ 2 * (Work.Spaces.w s) ^ 2)
      = ∫ θ in Work.Spaces.Iθ, (∫ z in Work.Spaces.Iz,
          (Work.Spaces.mixed (b + 1) (a + 1) f z θ * Work.Spaces.Wt α z θ) ^ 2) :=
        MeasureTheory.integral_congr_ae hae
    _ ≤ ∫ θ in Work.Spaces.Iθ,
          (∫ z in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f z θ) := hmono
    _ = Work.Spaces.HkSq α 4 f := hswap

end Work.FTS.StrongEps.SupPort
