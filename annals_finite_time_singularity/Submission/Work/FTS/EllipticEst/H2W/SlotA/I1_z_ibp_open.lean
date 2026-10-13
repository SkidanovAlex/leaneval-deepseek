import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.H2W.SlotA.radialDerivPointwiseOpen
import Submission.Work.FTS.EllipticEst.H2W.SlotA.radialIbpZeroOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The radial integration by parts of `I₁` on the open half-strip

This is the *weak-class* version of `Work.FTS.EllipticEst.H2W.I1_z_ibp_honest`: the smoothness
hypothesis is `C³` on the **open** half-strip `qd = (0,∞) × (0,π/2)` (which is what the
almost-everywhere class `H2W.Ae.AeData` supplies, and which is *not* implied by the joint `C²`
of the original statement of `H2W.I1_z_ibp` — see `H2W/NOTES_I1_z_ibp_FALSE.md`).

With `W2 z = (w z)^2`, `Φ` of class `C³` on `qd`, `z`-support of `Φ` in a compact
`[a,b] ⊂ (0,∞)` (for every angle `θ`), and the four integrability hypotheses:

  `∫_z ∫_θ (z²∂_z²Φ)·∂_θ²Φ·W2·sin(2θ)^{-η}`
  `= - ∫_z ∫_θ z²∂_zΦ·∂_z∂_θ²Φ·W2·sin(2θ)^{-η}`
    `- ∫_z ∫_θ z²∂_zΦ·∂_θ²Φ·(W2)'·sin(2θ)^{-η}`
    `- 2 ∫_z ∫_θ z∂_zΦ·∂_θ²Φ·W2·sin(2θ)^{-η}`.

The proof is the one of the sibling file: the four integrands sum to `∂_z(z²∂_zΦ·W2·∂_θ²Φ)`
pointwise (on the open strip, by `radial_deriv_pointwise_open`), whose `z`-integral vanishes at
every angle in the open interval (by `radial_ibp_zero_open`); Fubini then gives the identity.  All
integrals are over the open strip; the passage between `θ ∈ Iθ` and `θ ∈ (0,π/2)` is by the
almost-everywhere equality of the two angular intervals (their difference is `{0, π/2}`).
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.SlotA

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Fubini and the a.e. equality of the angular intervals -/

private theorem setIntegral_swap' {F : ℝ × ℝ → ℝ} {s t : Set ℝ}
    (h : MeasureTheory.IntegrableOn F (s ×ˢ t)) :
    (∫ z in s, ∫ θ in t, F (z, θ)) = ∫ θ in t, ∫ z in s, F (z, θ) := by
  have hInt : MeasureTheory.Integrable F ((volume.restrict s).prod (volume.restrict t)) := by
    rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod]
    exact h
  have hsw := MeasureTheory.integral_integral_swap (μ := volume.restrict s)
    (ν := volume.restrict t) (f := fun z θ => F (z, θ)) hInt
  simpa using hsw

private theorem setIntegral_prod_eq' {F : ℝ × ℝ → ℝ} {s t : Set ℝ}
    (h : MeasureTheory.IntegrableOn F (s ×ˢ t)) :
    (∫ p in s ×ˢ t, F p) = ∫ z in s, ∫ θ in t, F (z, θ) := by
  rw [MeasureTheory.Measure.volume_eq_prod]
  exact MeasureTheory.setIntegral_prod F h

/-- The two angular intervals agree almost everywhere. -/
private theorem restrict_Icc_eq_restrict_Ioo (c : ℝ) :
    (volume : Measure ℝ).restrict (Set.Icc 0 c) = (volume : Measure ℝ).restrict (Set.Ioo 0 c) :=
  MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioo_ae_eq_Icc' (measure_singleton (0 : ℝ)) (measure_singleton c)).symm

/-- The product-restricted measures over `Ioi 0 ×ˢ Icc 0 c` and `Ioi 0 ×ˢ Ioo 0 c` agree. -/
private theorem restrict_prod_Icc_eq_Ioo (c : ℝ) :
    (volume : Measure (ℝ × ℝ)).restrict (Set.Ioi 0 ×ˢ Set.Icc 0 c)
      = (volume : Measure (ℝ × ℝ)).restrict (Set.Ioi 0 ×ˢ Set.Ioo 0 c) := by
  have hθ := restrict_Icc_eq_restrict_Ioo c
  conv_lhs => rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ, ← MeasureTheory.Measure.prod_restrict]
  conv_rhs => rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ, ← MeasureTheory.Measure.prod_restrict]
  rw [hθ]

/-- Integration over the closed angular interval is integration over the open one. -/
private theorem setIntegral_Iθ_eq_Ioo (g : ℝ → ℝ) :
    (∫ θ in Work.Spaces.Iθ, g θ) = ∫ θ in Set.Ioo 0 (Real.pi / 2), g θ := by
  rw [Work.Spaces.Iθ]
  exact MeasureTheory.setIntegral_congr_set
    (MeasureTheory.Ioo_ae_eq_Icc' (measure_singleton (0 : ℝ))
      (measure_singleton (Real.pi / 2))).symm

/-! ## The main statement -/

theorem I1_z_ibp_open (η : ℝ) (hη : 0 < η) (Φ : ℝ → ℝ → ℝ) (a b : ℝ) (ha : 0 < a)
    (hab : a < b)
    (hsm : ContDiffOn ℝ 3 (Function.uncurry Φ) qd)
    (hsupp : ∀ z θ, z ∉ Set.Icc a b → Φ z θ = 0)
    (hI1 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
        (p.1 ^ 2 * Work.Spaces.pzIter 2 Φ p.1 p.2) * Work.Spaces.pthIter 2 Φ p.1 p.2
          * (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-η))
      (Set.Ioi 0 ×ˢ Work.Spaces.Iθ))
    (hI2 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
        p.1 ^ 2 * Work.Spaces.pz Φ p.1 p.2 * Work.Spaces.pz (Work.Spaces.pthIter 2 Φ) p.1 p.2
          * (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-η))
      (Set.Ioi 0 ×ˢ Work.Spaces.Iθ))
    (hI3 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
        p.1 ^ 2 * Work.Spaces.pz Φ p.1 p.2 * Work.Spaces.pthIter 2 Φ p.1 p.2
          * deriv (fun z' => (Work.Spaces.w z') ^ 2) p.1 * (Real.sin (2 * p.2)) ^ (-η))
      (Set.Ioi 0 ×ˢ Work.Spaces.Iθ))
    (hI4 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
        p.1 * Work.Spaces.pz Φ p.1 p.2 * Work.Spaces.pthIter 2 Φ p.1 p.2
          * (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-η))
      (Set.Ioi 0 ×ˢ Work.Spaces.Iθ)) :
    (∫ z in Set.Ioi 0, ∫ θ in Work.Spaces.Iθ,
        (z ^ 2 * Work.Spaces.pzIter 2 Φ z θ) * Work.Spaces.pthIter 2 Φ z θ
          * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-η))
      = - (∫ z in Set.Ioi 0, ∫ θ in Work.Spaces.Iθ,
            z ^ 2 * Work.Spaces.pz Φ z θ * Work.Spaces.pz (Work.Spaces.pthIter 2 Φ) z θ
              * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-η))
        - (∫ z in Set.Ioi 0, ∫ θ in Work.Spaces.Iθ,
            z ^ 2 * Work.Spaces.pz Φ z θ * Work.Spaces.pthIter 2 Φ z θ
              * deriv (fun z' => (Work.Spaces.w z') ^ 2) z * (Real.sin (2 * θ)) ^ (-η))
        - 2 * (∫ z in Set.Ioi 0, ∫ θ in Work.Spaces.Iθ,
            z * Work.Spaces.pz Φ z θ * Work.Spaces.pthIter 2 Φ z θ * (Work.Spaces.w z) ^ 2
              * (Real.sin (2 * θ)) ^ (-η)) := by
  -- ## The five integrands on the product space
  set F1 : ℝ × ℝ → ℝ := fun p =>
    (p.1 ^ 2 * Work.Spaces.pzIter 2 Φ p.1 p.2) * Work.Spaces.pthIter 2 Φ p.1 p.2
      * (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-η) with hF1
  set F2 : ℝ × ℝ → ℝ := fun p =>
    p.1 ^ 2 * Work.Spaces.pz Φ p.1 p.2 * Work.Spaces.pz (Work.Spaces.pthIter 2 Φ) p.1 p.2
      * (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-η) with hF2
  set F3 : ℝ × ℝ → ℝ := fun p =>
    p.1 ^ 2 * Work.Spaces.pz Φ p.1 p.2 * Work.Spaces.pthIter 2 Φ p.1 p.2
      * deriv (fun z' => (Work.Spaces.w z') ^ 2) p.1 * (Real.sin (2 * p.2)) ^ (-η) with hF3
  set F4 : ℝ × ℝ → ℝ := fun p =>
    p.1 * Work.Spaces.pz Φ p.1 p.2 * Work.Spaces.pthIter 2 Φ p.1 p.2
      * (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-η) with hF4
  set FD : ℝ × ℝ → ℝ := fun p =>
    deriv (fun z' => (z' ^ 2 * Work.Spaces.pz Φ z' p.2 * (Work.Spaces.w z') ^ 2)
        * Work.Spaces.pthIter 2 Φ z' p.2) p.1 * (Real.sin (2 * p.2)) ^ (-η) with hFD
  have hSmeas : MeasurableSet qd := isOpen_qd.measurableSet
  have hIθmeas : MeasurableSet Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]; exact measurableSet_Icc
  -- ## Integrability on the open strip, from the `Iθ`-versions
  have hI1S : MeasureTheory.IntegrableOn F1 qd := by
    have h := hI1
    rw [MeasureTheory.IntegrableOn, Work.Spaces.Iθ] at h
    rw [restrict_prod_Icc_eq_Ioo (Real.pi / 2)] at h
    simpa only [MeasureTheory.IntegrableOn, qd, hF1] using h
  have hI2S : MeasureTheory.IntegrableOn F2 qd := by
    have h := hI2
    rw [MeasureTheory.IntegrableOn, Work.Spaces.Iθ] at h
    rw [restrict_prod_Icc_eq_Ioo (Real.pi / 2)] at h
    simpa only [MeasureTheory.IntegrableOn, qd, hF2] using h
  have hI3S : MeasureTheory.IntegrableOn F3 qd := by
    have h := hI3
    rw [MeasureTheory.IntegrableOn, Work.Spaces.Iθ] at h
    rw [restrict_prod_Icc_eq_Ioo (Real.pi / 2)] at h
    simpa only [MeasureTheory.IntegrableOn, qd, hF3] using h
  have hI4S : MeasureTheory.IntegrableOn F4 qd := by
    have h := hI4
    rw [MeasureTheory.IntegrableOn, Work.Spaces.Iθ] at h
    rw [restrict_prod_Icc_eq_Ioo (Real.pi / 2)] at h
    simpa only [MeasureTheory.IntegrableOn, qd, hF4] using h
  -- ## The pointwise product rule on the open strip
  have hpt : ∀ p ∈ qd, F1 p + F2 p + F3 p + 2 * F4 p = FD p := by
    rintro ⟨z, θ⟩ hp
    obtain ⟨hz, hθ⟩ := hp
    simp only [hF1, hF2, hF3, hF4, hFD]
    rw [radial_deriv_pointwise_open Φ hsm hz hθ]
    ring
  -- ## Integrability of the sum and of the total derivative
  have hsum_int : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => F1 p + F2 p + F3 p + 2 * F4 p) qd :=
    ((hI1S.add hI2S).add hI3S).add (hI4S.const_mul 2)
  have hD_int : MeasureTheory.IntegrableOn FD qd :=
    hsum_int.congr_fun (fun p hp => hpt p hp) hSmeas
  -- ## The `z`-inner integral vanishes at every angle of the open interval
  have hinner : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), (∫ z in Set.Ioi 0, FD (z, θ)) = 0 := by
    intro θ hθ
    have h := radial_ibp_zero_open η hη Φ a b ha hab hsm hsupp θ hθ
    simpa only [hFD, mul_comm] using h
  have hzero : (∫ θ in Set.Ioo 0 (Real.pi / 2), ∫ z in Set.Ioi 0, FD (z, θ)) = 0 := by
    refine (MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun θ hθ => hinner θ hθ)).trans ?_
    simp
  have hprod_zero : (∫ p in qd, FD p) = 0 := by
    rw [setIntegral_prod_eq' hD_int]
    rw [setIntegral_swap' (F := FD) hD_int]
    exact hzero
  -- ## The linearity bookkeeping on the product space
  have hlin : (∫ p in qd, F1 p + F2 p + F3 p + 2 * F4 p) = ∫ p in qd, FD p :=
    MeasureTheory.setIntegral_congr_fun hSmeas (fun p hp => hpt p hp)
  have hA : (∫ p in qd, F1 p + F2 p)
      = (∫ p in qd, F1 p) + (∫ p in qd, F2 p) :=
    MeasureTheory.integral_add hI1S hI2S
  have hB : (∫ p in qd, F1 p + F2 p + F3 p)
      = (∫ p in qd, F1 p + F2 p) + (∫ p in qd, F3 p) :=
    MeasureTheory.integral_add (hI1S.add hI2S) hI3S
  have hC : (∫ p in qd, F1 p + F2 p + F3 p + 2 * F4 p)
      = (∫ p in qd, F1 p + F2 p + F3 p) + (∫ p in qd, 2 * F4 p) :=
    MeasureTheory.integral_add ((hI1S.add hI2S).add hI3S) (hI4S.const_mul 2)
  have hD : (∫ p in qd, 2 * F4 p) = 2 * (∫ p in qd, F4 p) :=
    MeasureTheory.integral_const_mul (2 : ℝ) F4
  have hsumprod : (∫ p in qd, F1 p) + (∫ p in qd, F2 p) + (∫ p in qd, F3 p)
      + 2 * (∫ p in qd, F4 p) = 0 := by
    linarith [hA, hB, hC, hD, hlin, hprod_zero]
  -- ## Convert the `θ`-integrals from `Iθ` to the open interval
  have hconv1 : (∫ z in Set.Ioi 0, ∫ θ in Work.Spaces.Iθ, F1 (z, θ))
      = ∫ p in qd, F1 p := by
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      (fun z _ => setIntegral_Iθ_eq_Ioo (fun θ => F1 (z, θ)))]
    exact (setIntegral_prod_eq' hI1S).symm
  have hconv2 : (∫ z in Set.Ioi 0, ∫ θ in Work.Spaces.Iθ, F2 (z, θ))
      = ∫ p in qd, F2 p := by
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      (fun z _ => setIntegral_Iθ_eq_Ioo (fun θ => F2 (z, θ)))]
    exact (setIntegral_prod_eq' hI2S).symm
  have hconv3 : (∫ z in Set.Ioi 0, ∫ θ in Work.Spaces.Iθ, F3 (z, θ))
      = ∫ p in qd, F3 p := by
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      (fun z _ => setIntegral_Iθ_eq_Ioo (fun θ => F3 (z, θ)))]
    exact (setIntegral_prod_eq' hI3S).symm
  have hconv4 : (∫ z in Set.Ioi 0, ∫ θ in Work.Spaces.Iθ, F4 (z, θ))
      = ∫ p in qd, F4 p := by
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      (fun z _ => setIntegral_Iθ_eq_Ioo (fun θ => F4 (z, θ)))]
    exact (setIntegral_prod_eq' hI4S).symm
  -- ## Assembly
  rw [hconv1, hconv2, hconv3, hconv4]
  linarith [hsumprod]

end Work.FTS.EllipticEst.H2W.SlotA
