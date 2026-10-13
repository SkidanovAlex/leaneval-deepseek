/-
# The angular integration by parts for the `SmoothOpen` class

`Work.Coercivity.wip ρ (Dth h) h = ∫∫ (D_θ h)·h·ρ` is computed by integrating by parts in
`θ` on `(0,π/2)`.  Writing `ρ = Φ(z)·sin(2θ)^{-q}` with `Φ` depending on `z` only, the
integrand is `sin(2θ)·∂_θ h·h·Φ·sin(2θ)^{-q} = (1/2)Φ·sin(2θ)^{1-q}·∂_θ(h²)`, so

  `wip (Φ·sin(2θ)^{-q}) (D_θ h) h = (q-1)·∫_z Φ(z)·∫_θ cos(2θ)·sin(2θ)^{-q}·h²`

provided the two boundary terms `sin(2θ)^{1-q} h²` vanish at `θ = 0, π/2`.  The vanishing
is *derived* (not assumed) from the integrability hypotheses: `sin(2θ)^{-q}h²` is
integrable on `Iθ`, so if the boundary value were nonzero, `h² ` would diverge
logarithmically there — contradiction (`SinBoundaryTendsto`).  This is the exact analogue
of `wip_Dz_ibp` in the angular variable.

## Layout

* `IbpU`, `IbpA`, `IbpE` — the three integrands `sin^{-q}H²`, `sin(2θ)∂_θH·H·sin^{-q}`,
  `cos(2θ)sin^{-q}H²`;
* `sliceIbp` — the one-dimensional integration by parts (via `IbpInnerDeriv`, the
  derivative computation, and `SinBoundaryTendsto`, the boundary vanishing);
* `wip_Dth_ibp` — the two-dimensional statement, obtained by applying the slice identity
  for almost every `z` and integrating in `z` (`integral_congr_ae`).

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.Defs
import Submission.Work.Coercivity.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongPersist.H6Aux.R.IbpInnerDeriv
import Submission.Work.FTS.StrongPersist.H6Aux.R.SinBoundaryTendsto
import Submission.Work.FTS.Vocab

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Aux.R

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- `sin(2θ)^{-q}·H²`. -/
def IbpU (q : ℝ) (H : ℝ → ℝ) : ℝ → ℝ := fun θ => (Real.sin (2 * θ)) ^ (-q) * (H θ) ^ 2

/-- `sin(2θ)·∂_θH·H·sin(2θ)^{-q}`. -/
def IbpA (q : ℝ) (H : ℝ → ℝ) : ℝ → ℝ :=
  fun θ => Real.sin (2 * θ) * deriv H θ * H θ * (Real.sin (2 * θ)) ^ (-q)

/-- `cos(2θ)·sin(2θ)^{-q}·H²`. -/
def IbpE (q : ℝ) (H : ℝ → ℝ) : ℝ → ℝ :=
  fun θ => Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q) * (H θ) ^ 2

/-- **The one-dimensional angular integration by parts** on `[0,π/2]`, with weight
`sin(2θ)^{-q}`.  The three integrability hypotheses make the boundary terms vanish. -/
theorem sliceIbp {q : ℝ} {H : ℝ → ℝ}
    (hH : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), HasDerivAt H (deriv H θ) θ)
    (hU : MeasureTheory.IntegrableOn (IbpU q H) Work.Spaces.Iθ)
    (hA : MeasureTheory.IntegrableOn (IbpA q H) Work.Spaces.Iθ)
    (hE : MeasureTheory.IntegrableOn (IbpE q H) Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ, IbpA q H θ) = (q - 1) * (∫ θ in Work.Spaces.Iθ, IbpE q H θ) := by
  have hpi : (0 : ℝ) < Real.pi / 2 := by positivity
  set v' : ℝ → ℝ := fun θ => 2 * IbpA q H θ - 2 * (q - 1) * IbpE q H θ with hv'def
  have hderiv : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun θ' => Real.sin (2 * θ') * (IbpU q H θ')) (v' θ) θ := by
    intro θ hθ
    have h1 := IbpInnerDeriv (q := q) hH θ hθ
    simpa only [v', IbpA, IbpE, IbpU] using h1
  have hwnn : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 ≤ IbpU q H θ := by
    intro θ hθ
    have hs : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    exact mul_nonneg (Real.rpow_nonneg hs.le _) (sq_nonneg _)
  have hv'int : MeasureTheory.IntegrableOn v' Work.Spaces.Iθ := by
    refine ((hA.const_mul 2).sub (hE.const_mul (2 * (q - 1)))).congr ?_
    filter_upwards with θ
    simp only [v', Pi.sub_apply]
    try ring
  have hlim := SinBoundaryTendsto hU hwnn hderiv hv'int
  have hInt : IntervalIntegrable v' volume (0 : ℝ) (Real.pi / 2) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hpi.le).mpr
      (hv'int.mono_set Set.Ioc_subset_Icc_self)
  have hFTC : (∫ θ in (0 : ℝ)..(Real.pi / 2), v' θ) = 0 := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hpi hderiv hInt
      hlim.1 hlim.2
    simpa using h
  have hconv : ∀ g : ℝ → ℝ,
      (∫ θ in Work.Spaces.Iθ, g θ) = ∫ θ in (0 : ℝ)..(Real.pi / 2), g θ := by
    intro g
    rw [show Work.Spaces.Iθ = Set.Icc 0 (Real.pi / 2) from rfl,
      MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hpi.le]
  have h0 : (∫ θ in Work.Spaces.Iθ, v' θ) = 0 := by rw [hconv]; exact hFTC
  have hdecomp : (∫ θ in Work.Spaces.Iθ, v' θ)
      = 2 * (∫ θ in Work.Spaces.Iθ, IbpA q H θ)
        - (2 * (q - 1)) * (∫ θ in Work.Spaces.Iθ, IbpE q H θ) := by
    rw [show v' = fun θ => 2 * IbpA q H θ - (2 * (q - 1)) * IbpE q H θ from rfl,
      MeasureTheory.integral_sub (hA.const_mul 2) (hE.const_mul (2 * (q - 1))),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  have h2 : (2 : ℝ) * ((∫ θ in Work.Spaces.Iθ, IbpA q H θ)
      - (q - 1) * (∫ θ in Work.Spaces.Iθ, IbpE q H θ)) = 0 := by
    rw [show (2 : ℝ) * ((∫ θ in Work.Spaces.Iθ, IbpA q H θ)
        - (q - 1) * (∫ θ in Work.Spaces.Iθ, IbpE q H θ))
        = (∫ θ in Work.Spaces.Iθ, v' θ) from by rw [hdecomp]; ring, h0]
  rcases mul_eq_zero.mp h2 with h | h
  · norm_num at h
  · linarith

/-- **The angular integration by parts for the `SmoothOpen` class.**  For `u` smooth on the
open quadrant and `Φ` a `z`-only weight, the `wip`-pairing of `D_θu` with `u` against
`Φ(z)sin(2θ)^{-q}` is `(q-1)` times the pairing of `u²` with `Φ(z)cos(2θ)sin(2θ)^{-q}`. -/
theorem wip_Dth_ibp {u : Fn} {Φ : ℝ → ℝ} {q : ℝ}
    (hs : Work.FTS.EllipticEst.SmoothOpen u)
    (hint0 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => u z θ ^ 2 * Φ z * (Real.sin (2 * θ)) ^ (-q)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hint1 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dth u z θ * u z θ * Φ z
        * (Real.sin (2 * θ)) ^ (-q))) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hint2 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => u z θ ^ 2 * Φ z * Real.cos (2 * θ)
        * (Real.sin (2 * θ)) ^ (-q))) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    Work.Coercivity.wip (fun z θ => Φ z * (Real.sin (2 * θ)) ^ (-q)) (Work.Spaces.Dth u) u
      = (q - 1) * (∫ z in Work.Spaces.Iz, Φ z * ∫ θ in Work.Spaces.Iθ,
          Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q) * u z θ ^ 2) := by
  have hmeas : (MeasureTheory.volume.restrict (Work.Spaces.Iz : Set ℝ)).prod
      (MeasureTheory.volume.restrict (Work.Spaces.Iθ : Set ℝ))
      = MeasureTheory.volume.restrict ((Work.Spaces.Iz : Set ℝ) ×ˢ (Work.Spaces.Iθ : Set ℝ)) := by
    rw [MeasureTheory.Measure.prod_restrict, MeasureTheory.Measure.volume_eq_prod]
  have hI0 := hint0; rw [MeasureTheory.IntegrableOn, ← hmeas] at hI0
  have hI1 := hint1; rw [MeasureTheory.IntegrableOn, ← hmeas] at hI1
  have hI2 := hint2; rw [MeasureTheory.IntegrableOn, ← hmeas] at hI2
  have hzpos : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), 0 < z := by
    have h : (Work.Spaces.Iz : Set ℝ) =ᵐ[MeasureTheory.volume] Set.Ioi 0 :=
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0)).symm
    rw [MeasureTheory.Measure.restrict_congr_set h]
    exact MeasureTheory.ae_restrict_mem measurableSet_Ioi
  have hslices : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable (fun θ => u z θ ^ 2 * Φ z * (Real.sin (2 * θ)) ^ (-q))
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)
      ∧ MeasureTheory.Integrable
          (fun θ => Work.Spaces.Dth u z θ * u z θ * Φ z * (Real.sin (2 * θ)) ^ (-q))
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)
      ∧ MeasureTheory.Integrable
          (fun θ => u z θ ^ 2 * Φ z * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q))
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    have h1 := hI0.prod_right_ae
    have h2 := hI1.prod_right_ae
    have h3 := hI2.prod_right_ae
    filter_upwards [h1, h2, h3] with z hz1 hz2 hz3
    exact ⟨hz1, hz2, hz3⟩
  have hpt : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.Dth u z θ * u z θ * (Φ z * (Real.sin (2 * θ)) ^ (-q)))
        = (q - 1) * (Φ z * ∫ θ in Work.Spaces.Iθ,
            Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q) * u z θ ^ 2) := by
    filter_upwards [hslices, hzpos] with z hz hzp
    obtain ⟨hz0, hz1, hz2⟩ := hz
    rcases eq_or_ne (Φ z) 0 with hΦ | hΦ
    · rw [hΦ]; simp
    · have hsub : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
          HasDerivAt (fun θ' => u z θ') (deriv (fun θ' => u z θ') θ) θ := by
        intro θ hθ
        have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := by
          rw [Work.FTS.EllipticEst.mem_Q0]; exact ⟨hzp, hθ.1, hθ.2⟩
        have hcd : ContDiffAt ℝ Work.Stability.smoothOrder (Function.uncurry u) (z, θ) :=
          hs.contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hmem)
        exact (Work.Spaces.differentiableAt_curry_right
          (hcd.differentiableAt Work.FTS.LocData.smoothOrder_ne_zero)).hasDerivAt
      have hU : MeasureTheory.IntegrableOn (IbpU q (fun θ => u z θ)) Work.Spaces.Iθ := by
        have h1 : MeasureTheory.IntegrableOn
            (fun θ => Φ z * IbpU q (fun θ' => u z θ') θ) Work.Spaces.Iθ := by
          refine hz0.congr ?_
          filter_upwards with θ
          simp only [IbpU]; try ring
        refine (h1.const_mul ((Φ z)⁻¹)).congr ?_
        filter_upwards with θ
        simp only [IbpU]
        field_simp
      have hA : MeasureTheory.IntegrableOn (IbpA q (fun θ => u z θ)) Work.Spaces.Iθ := by
        have h1 : MeasureTheory.IntegrableOn
            (fun θ => Φ z * IbpA q (fun θ' => u z θ') θ) Work.Spaces.Iθ := by
          refine hz1.congr ?_
          filter_upwards with θ
          simp only [IbpA, Work.Spaces.Dth, Work.Spaces.pth]; try ring
        refine (h1.const_mul ((Φ z)⁻¹)).congr ?_
        filter_upwards with θ
        simp only [IbpA]
        field_simp
      have hE : MeasureTheory.IntegrableOn (IbpE q (fun θ => u z θ)) Work.Spaces.Iθ := by
        have h1 : MeasureTheory.IntegrableOn
            (fun θ => Φ z * IbpE q (fun θ' => u z θ') θ) Work.Spaces.Iθ := by
          refine hz2.congr ?_
          filter_upwards with θ
          simp only [IbpE]; try ring
        refine (h1.const_mul ((Φ z)⁻¹)).congr ?_
        filter_upwards with θ
        simp only [IbpE]
        field_simp
      have hkey := sliceIbp (q := q) hsub hU hA hE
      have hL : (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.Dth u z θ * u z θ * (Φ z * (Real.sin (2 * θ)) ^ (-q)))
          = Φ z * (∫ θ in Work.Spaces.Iθ, IbpA q (fun θ' => u z θ') θ) := by
        rw [show (∫ θ in Work.Spaces.Iθ,
              Work.Spaces.Dth u z θ * u z θ * (Φ z * (Real.sin (2 * θ)) ^ (-q)))
            = (∫ θ in Work.Spaces.Iθ, Φ z * IbpA q (fun θ' => u z θ') θ) from by
          apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
          intro θ _
          simp only [IbpA, Work.Spaces.Dth, Work.Spaces.pth]
          ring]
        rw [MeasureTheory.integral_const_mul]
      rw [hL, hkey]
      simp only [IbpE]
      ring
  rw [Work.Coercivity.wip, MeasureTheory.integral_congr_ae hpt,
    MeasureTheory.integral_const_mul]

end Work.FTS.StrongPersist.H6Aux.R
