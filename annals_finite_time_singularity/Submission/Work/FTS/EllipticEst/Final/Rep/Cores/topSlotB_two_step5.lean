import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.Final.Rep.H2W.slot20_bound
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.Mine.SlotDefs
import Submission.Work.FTS.EllipticEst.H2W.sliceStep5Weak
import Submission.Work.FTS.EllipticEst.H2W.Step5.s20SliceIntegrable
import Submission.Work.FTS.EllipticEst.H2W.Slot01W.SliceRegular
import Submission.Work.FTS.EllipticEst.Final.Rep.Cores.topB_step5_integrable
import Submission.Work.FTS.EllipticEst.Cores.topB_sliceStep5_uniform

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cores

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The two-dimensional transfer of the slice Step-5 estimate

This file proves the requested lemma `Work.FTS.EllipticEst.Cores.topSlotB_two_step5`, the
two-dimensional Step-5 estimate of Elgindi's `prop:H2` for the second angular derivative
`∂_θθΨ` in the weak hypothesis class `TT.EllWeakPos α 2 F Ψ`:

  `s20M4 α Ψ ≤ C (s20J2 α F Ψ + s20M3 α Ψ + s20A2 Ψ + s20A1 Ψ + s20A0 Ψ)`.

The mathematical content is the *slicewise transfer*:

* for every `z > 0`, the slice `u_z := Ψ z ·` satisfies all the hypotheses of the
  one-dimensional Step-5 estimate (`Cores.topB_sliceStep5_uniform`): the equation
  `Lzero1 u_z = Gsrc α F Ψ z ·` on `(0,π/2)`, the two Dirichlet values, continuity on the closed
  interval (`remov.weakSliceRegular`) and the six `IntegrableOn` slots
  (`H2W.Step5.s20SliceIntegrable` together with `remov.weakSliceRegular`);
* hence the slice estimate holds for every `z > 0`; multiplying it by the nonnegative radial
  weight `2 w(z)²` and rewriting the five right-hand slots as `SG, SM3, SA2, SA1, SA0` gives the
  a.e.-in-`z` comparison
  `z ↦ ∫_θ s20F4 α Ψ z θ ≤ z ↦ 2 C (SG + SM3 + SA2 + SA1 + SA0)`;
* the five slot functions are honest by `Cores.topB_step5_integrable`, so
  `integral_mono_of_nonneg` integrates the comparison:
  `s20M4 α Ψ ≤ 2 C (∫ SG + ∫ SM3 + ∫ SA2 + ∫ SA1 + ∫ SA0)`;
* the slot integrals are `s20J2 α F Ψ`, `s20M3 α Ψ / 8`, `s20A2 Ψ`, `s20A1 Ψ`, `s20A0 Ψ`, and
  `s20M3 α Ψ ≥ 0`, giving the statement with the constant `2 C`. -/

/-! ## Bridging `pthIter` and iterated `deriv` -/

private lemma pthIter_one (Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pthIter 1 Ψ z θ = deriv (fun t => Ψ z t) θ := rfl

private lemma pthIter_two (Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pthIter 2 Ψ z θ = deriv (fun t => deriv (fun s => Ψ z s) t) θ := rfl

private lemma pthIter_three (Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pthIter 3 Ψ z θ = deriv (deriv (deriv (fun t => Ψ z t))) θ := rfl

private lemma pthIter_four (Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pthIter 4 Ψ z θ
      = deriv (deriv (deriv (deriv (fun t => Ψ z t)))) θ := rfl

private lemma pthIter_two_G (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pthIter 2 (Work.FTS.EllipticEst.Mine.Gsrc α F Ψ) z θ
      = deriv (deriv (fun t => Work.FTS.EllipticEst.Mine.Gsrc α F Ψ z t)) θ := rfl

/-! ## The slot functions -/

/-- The `z`-integrand of `s20J2`: the source slot `∫_θ (∂_θ²Gsrc)² σ₄`. -/
private def SG (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ := fun z =>
  (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
    (Work.Spaces.pthIter 2 (Work.FTS.EllipticEst.Mine.Gsrc α F Ψ) z θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (4 - Work.Spaces.gam α)

/-- The `z`-integrand of `s20M3`: the Step-4 slot `∫_θ (∂_θ³Ψ)² σ₂`. -/
private def SM3 (α : ℝ) (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ := fun z =>
  (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
    (Work.Spaces.pthIter 3 Ψ z θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α)

/-- The `z`-integrand of `s20A2`: the `η`-slot `∫_θ (∂_θ²Ψ)² sEta`. -/
private def SA2 (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ := fun z =>
  (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
    (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ

/-- The `z`-integrand of `s20A1`: the slot `∫_θ (∂_θΨ)²`. -/
private def SA1 (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ := fun z =>
  (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2

/-- The `z`-integrand of `s20A0`: the slot `∫_θ Ψ²`. -/
private def SA0 (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ := fun z =>
  (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2

private lemma sin_two_nonneg_Iθ' {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) := by
  rw [Work.Spaces.Iθ] at hθ
  exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
    (by linarith [hθ.2, Real.pi_pos])

/-! ## Rewriting the six integrands -/

private lemma s20F4_eq_slots (α : ℝ) (Ψ : ℝ → ℝ → ℝ) (z : ℝ) :
    (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.H2W.s20F4 α Ψ z θ)
      = 2 * (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (deriv (deriv (deriv (deriv (fun t => Ψ z t)))) θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (4 - Work.Spaces.gam α)) := by
  have hp : ∀ θ : ℝ, Work.FTS.EllipticEst.H2W.s20F4 α Ψ z θ
      = (2 * (Work.Spaces.w z) ^ 2) *
        ((deriv (deriv (deriv (deriv (fun t => Ψ z t)))) θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (4 - Work.Spaces.gam α)) := by
    intro θ
    rw [show Work.FTS.EllipticEst.H2W.s20F4 α Ψ z θ
        = (2 * (Work.Spaces.w z) ^ 2) * ((Work.Spaces.pthIter 4 Ψ z θ) ^ 2 *
            Real.rpow (Real.sin (2 * θ)) (4 - Work.Spaces.gam α)) from rfl]
    rw [pthIter_four Ψ z θ]
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hp),
    MeasureTheory.integral_const_mul]

private lemma SG_eq (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) (z : ℝ) :
    SG α F Ψ z = (Work.Spaces.w z) ^ 2 *
      (∫ θ in Work.Spaces.Iθ,
        (deriv (deriv (fun t => Work.FTS.EllipticEst.Mine.Gsrc α F Ψ z t)) θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (4 - Work.Spaces.gam α)) := by
  rw [SG, ← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul]
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => by
    rw [pthIter_two_G α F Ψ z θ])]

private lemma SM3_eq (α : ℝ) (Ψ : ℝ → ℝ → ℝ) (z : ℝ) :
    SM3 α Ψ z = (Work.Spaces.w z) ^ 2 *
      (∫ θ in Work.Spaces.Iθ, (deriv (deriv (deriv (fun t => Ψ z t))) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α)) := by
  rw [SM3, ← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul]
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => by
    rw [pthIter_three Ψ z θ])]

private lemma SA2_eq (Ψ : ℝ → ℝ → ℝ) (z : ℝ) :
    SA2 Ψ z = (Work.Spaces.w z) ^ 2 *
      (∫ θ in Work.Spaces.Iθ, (deriv (fun t => deriv (fun s => Ψ z s) t) θ) ^ 2 *
        Work.FTS.EllipticEst.sEta θ) := by
  rw [SA2, ← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul]
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => by
    rw [pthIter_two Ψ z θ])]

private lemma SA1_eq (Ψ : ℝ → ℝ → ℝ) (z : ℝ) :
    SA1 Ψ z = (Work.Spaces.w z) ^ 2 *
      (∫ θ in Work.Spaces.Iθ, (deriv (fun t => Ψ z t) θ) ^ 2) := by
  rw [SA1, ← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul]
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => by
    rw [pthIter_one Ψ z θ])]

/-! ## The assembly -/

theorem topSlotB_two_step5 : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
    Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
      Work.FTS.EllipticEst.H2W.s20M4 α Ψ
        ≤ C * (Work.FTS.EllipticEst.H2W.s20J2 α F Ψ + Work.FTS.EllipticEst.H2W.s20M3 α Ψ
            + Work.FTS.EllipticEst.H2W.s20A2 Ψ + Work.FTS.EllipticEst.H2W.s20A1 Ψ
            + Work.FTS.EllipticEst.H2W.s20A0 Ψ) := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := topB_sliceStep5_uniform
  refine ⟨2 * C₁, by linarith, ?_⟩
  intro α F Ψ hα hα4 h
  have hIz : MeasurableSet Work.Spaces.Iz := measurableSet_Ici
  have hγ1 : 1 ≤ Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
  have hγ2 : Work.Spaces.gam α ≤ 3 / 2 := by rw [Work.Spaces.gam]; linarith
  -- the slice estimate, for each `z > 0`
  have hslice : ∀ z, 0 < z →
      (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.H2W.s20F4 α Ψ z θ)
        ≤ 2 * C₁ * (SG α F Ψ z + SM3 α Ψ z + SA2 Ψ z + SA1 Ψ z + SA0 Ψ z) := by
    intro z hz
    have hu4 : ContDiffOn ℝ 4 (fun t => Ψ z t) (Set.Ioo 0 (Real.pi / 2)) := by
      have h1 : ContDiffOn ℝ 4 (fun θ : ℝ => (z, θ)) (Set.Ioo 0 (Real.pi / 2)) := by fun_prop
      have h2 := (h.smooth 4).comp h1 (fun θ hθ => ⟨hz, hθ⟩)
      simpa [Function.comp_def, Function.uncurry] using h2
    have hwr :=
      Work.FTS.EllipticEst.remov.weakSliceRegular 2 (by norm_num) α F Ψ hα hα4 h z hz
    have huc : ContinuousOn (fun t => Ψ z t) (Set.Icc 0 (Real.pi / 2)) := hwr.1
    have hz0 : (fun t => Ψ z t) 0 = 0 := hwr.2.1
    have hzpi : (fun t => Ψ z t) (Real.pi / 2) = 0 := hwr.2.2.1
    have hI0 : MeasureTheory.IntegrableOn (fun θ => ((fun t => Ψ z t) θ) ^ 2)
        Work.Spaces.Iθ := hwr.2.2.2.2.1
    have hI1 : MeasureTheory.IntegrableOn (fun θ => (deriv (fun t => Ψ z t) θ) ^ 2)
        Work.Spaces.Iθ := hwr.2.2.2.2.2.1
    have hI2 : MeasureTheory.IntegrableOn
        (fun θ => (deriv (fun t => deriv (fun s => Ψ z s) t) θ) ^ 2 *
          Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := hwr.2.2.2.2.2.2
    obtain ⟨_, _, _, hIslice3, hIslice4, hIsliceG⟩ :=
      Work.FTS.EllipticEst.H2W.Step5.s20SliceIntegrable α F Ψ hα hα4 h z hz
    have hode : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ
          = (fun t => Work.FTS.EllipticEst.Mine.Gsrc α F Ψ z t) θ :=
      fun θ hθ => Work.FTS.EllipticEst.Mine.Lzero1_slice_eq_Gsrc h.eq hz hθ.1 hθ.2
    have h1d := hC₁ (Work.Spaces.gam α) hγ1 hγ2 (fun t => Ψ z t)
      (fun t => Work.FTS.EllipticEst.Mine.Gsrc α F Ψ z t) hu4 huc hz0 hzpi hode
      hIslice4 hIslice3 hI2 hI1 hI0 hIsliceG
    rw [s20F4_eq_slots α Ψ z, SG_eq α F Ψ z, SM3_eq α Ψ z, SA2_eq Ψ z, SA1_eq Ψ z]
    calc 2 * (Work.Spaces.w z) ^ 2 *
          (∫ θ in Work.Spaces.Iθ, (deriv (deriv (deriv (deriv (fun t => Ψ z t)))) θ) ^ 2 *
            Real.rpow (Real.sin (2 * θ)) (4 - Work.Spaces.gam α))
        ≤ 2 * (Work.Spaces.w z) ^ 2 *
            (C₁ * ((∫ θ in Work.Spaces.Iθ,
                  (deriv (deriv (fun t => Work.FTS.EllipticEst.Mine.Gsrc α F Ψ z t)) θ) ^ 2 *
                    Real.rpow (Real.sin (2 * θ)) (4 - Work.Spaces.gam α))
              + (∫ θ in Work.Spaces.Iθ, (deriv (deriv (deriv (fun t => Ψ z t))) θ) ^ 2 *
                    Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α))
              + (∫ θ in Work.Spaces.Iθ, (deriv (fun t => deriv (fun s => Ψ z s) t) θ) ^ 2 *
                    Work.FTS.EllipticEst.sEta θ)
              + (∫ θ in Work.Spaces.Iθ, (deriv (fun t => Ψ z t) θ) ^ 2)
              + (∫ θ in Work.Spaces.Iθ, ((fun t => Ψ z t) θ) ^ 2))) := by
          exact mul_le_mul_of_nonneg_left h1d (by positivity)
      _ = 2 * C₁ * ((Work.Spaces.w z) ^ 2 *
            (∫ θ in Work.Spaces.Iθ,
                (deriv (deriv (fun t => Work.FTS.EllipticEst.Mine.Gsrc α F Ψ z t)) θ) ^ 2 *
                  Real.rpow (Real.sin (2 * θ)) (4 - Work.Spaces.gam α))
          + (Work.Spaces.w z) ^ 2 *
            (∫ θ in Work.Spaces.Iθ, (deriv (deriv (deriv (fun t => Ψ z t))) θ) ^ 2 *
                  Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α))
          + (Work.Spaces.w z) ^ 2 *
            (∫ θ in Work.Spaces.Iθ, (deriv (fun t => deriv (fun s => Ψ z s) t) θ) ^ 2 *
                  Work.FTS.EllipticEst.sEta θ)
          + (Work.Spaces.w z) ^ 2 *
            (∫ θ in Work.Spaces.Iθ, (deriv (fun t => Ψ z t) θ) ^ 2)
          + (Work.Spaces.w z) ^ 2 *
            (∫ θ in Work.Spaces.Iθ, ((fun t => Ψ z t) θ) ^ 2)) := by
          ring
  -- the five slot functions are honest
  obtain ⟨hSGint, hSM3int, hSA2int, hSA1int, hSA0int⟩ :=
    topB_step5_integrable α F Ψ hα hα4 h
  -- the a.e. comparison in `z`
  have hae : (fun z => ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.H2W.s20F4 α Ψ z θ)
      ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz]
      (fun z => 2 * C₁ * (SG α F Ψ z + SM3 α Ψ z + SA2 Ψ z + SA1 Ψ z + SA0 Ψ z)) := by
    refine MeasureTheory.ae_restrict_of_forall_mem hIz fun z hz => ?_
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
    · subst hz0
      have hw0 : Work.Spaces.w 0 = 0 := by rw [Work.Spaces.w]; norm_num
      have h0 : (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.H2W.s20F4 α Ψ 0 θ) = 0 := by
        simp only [Work.FTS.EllipticEst.H2W.s20F4, hw0]
        simp
      have h1 : (2 * C₁ * (SG α F Ψ 0 + SM3 α Ψ 0 + SA2 Ψ 0 + SA1 Ψ 0 + SA0 Ψ 0)) = 0 := by
        simp only [SG, SM3, SA2, SA1, SA0, hw0]
        ring
      simp only []
      rw [h0, h1]
    · exact hslice z hzpos
  -- the monotone comparison of the outer integrals
  have hnn : 0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz]
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.H2W.s20F4 α Ψ z θ) := by
    refine Filter.Eventually.of_forall fun z => ?_
    refine MeasureTheory.integral_nonneg_of_ae ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => ?_
    rw [show Work.FTS.EllipticEst.H2W.s20F4 α Ψ z θ
        = 2 * (Work.Spaces.w z) ^ 2 *
            ((Work.Spaces.pthIter 4 Ψ z θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (4 - Work.Spaces.gam α)) from rfl]
    exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
      (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ' hθ) _))
  have hintR : MeasureTheory.Integrable
      (fun z => 2 * C₁ * (SG α F Ψ z + SM3 α Ψ z + SA2 Ψ z + SA1 Ψ z + SA0 Ψ z))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    ((((hSGint.add hSM3int).add hSA2int).add hSA1int).add hSA0int).const_mul _
  have hmain := MeasureTheory.integral_mono_of_nonneg hnn hintR hae
  -- identify the two sides
  have hLs : (∫ z in Work.Spaces.Iz,
      ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.H2W.s20F4 α Ψ z θ)
      = Work.FTS.EllipticEst.H2W.s20M4 α Ψ := rfl
  have hRs : (∫ z in Work.Spaces.Iz,
      (fun z => 2 * C₁ * (SG α F Ψ z + SM3 α Ψ z + SA2 Ψ z + SA1 Ψ z + SA0 Ψ z)) z)
      = 2 * C₁ * (Work.FTS.EllipticEst.H2W.s20J2 α F Ψ
          + (1 / 8) * Work.FTS.EllipticEst.H2W.s20M3 α Ψ
          + Work.FTS.EllipticEst.H2W.s20A2 Ψ + Work.FTS.EllipticEst.H2W.s20A1 Ψ
          + Work.FTS.EllipticEst.H2W.s20A0 Ψ) := by
    rw [MeasureTheory.integral_const_mul]
    congr 1
    have hA : (∫ z in Work.Spaces.Iz,
        (SG α F Ψ z + SM3 α Ψ z + SA2 Ψ z + SA1 Ψ z + SA0 Ψ z))
        = (∫ z in Work.Spaces.Iz, SG α F Ψ z) + (∫ z in Work.Spaces.Iz, SM3 α Ψ z)
          + (∫ z in Work.Spaces.Iz, SA2 Ψ z) + (∫ z in Work.Spaces.Iz, SA1 Ψ z)
          + (∫ z in Work.Spaces.Iz, SA0 Ψ z) := by
      rw [MeasureTheory.integral_add
            (f := (fun z => SG α F Ψ z + SM3 α Ψ z + SA2 Ψ z + SA1 Ψ z))
            (g := (fun z => SA0 Ψ z)) (((hSGint.add hSM3int).add hSA2int).add hSA1int) hSA0int,
          MeasureTheory.integral_add
            (f := (fun z => SG α F Ψ z + SM3 α Ψ z + SA2 Ψ z))
            (g := (fun z => SA1 Ψ z)) ((hSGint.add hSM3int).add hSA2int) hSA1int,
          MeasureTheory.integral_add
            (f := (fun z => SG α F Ψ z + SM3 α Ψ z))
            (g := (fun z => SA2 Ψ z)) (hSGint.add hSM3int) hSA2int,
          MeasureTheory.integral_add (f := (SG α F Ψ)) (g := (SM3 α Ψ)) hSGint hSM3int]
    rw [hA]
    have e1 : (∫ z in Work.Spaces.Iz, SG α F Ψ z) = Work.FTS.EllipticEst.H2W.s20J2 α F Ψ := by
      rw [Work.FTS.EllipticEst.H2W.s20J2]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      rfl
    have e2 : (∫ z in Work.Spaces.Iz, SM3 α Ψ z)
        = (1 / 8) * Work.FTS.EllipticEst.H2W.s20M3 α Ψ := by
      have hF3 : ∀ z, (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.H2W.s20F3 α Ψ z θ)
          = 8 * SM3 α Ψ z := by
        intro z
        rw [show (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.H2W.s20F3 α Ψ z θ)
            = ∫ θ in Work.Spaces.Iθ, (8 * (Work.Spaces.w z) ^ 2) *
                ((Work.Spaces.pthIter 3 Ψ z θ) ^ 2 *
                  Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α)) from rfl]
        rw [MeasureTheory.integral_const_mul, SM3]
        ring
      rw [Work.FTS.EllipticEst.H2W.s20M3,
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hF3),
        MeasureTheory.integral_const_mul]
      ring
    have e3 : (∫ z in Work.Spaces.Iz, SA2 Ψ z) = Work.FTS.EllipticEst.H2W.s20A2 Ψ := rfl
    have e4 : (∫ z in Work.Spaces.Iz, SA1 Ψ z) = Work.FTS.EllipticEst.H2W.s20A1 Ψ := rfl
    have e5 : (∫ z in Work.Spaces.Iz, SA0 Ψ z) = Work.FTS.EllipticEst.H2W.s20A0 Ψ := rfl
    rw [e1, e2, e3, e4, e5]
  rw [hLs, hRs] at hmain
  have hM3 : 0 ≤ Work.FTS.EllipticEst.H2W.s20M3 α Ψ :=
    Work.FTS.EllipticEst.H2W.s20M3_nonneg α Ψ
  have hfin : 2 * C₁ * (Work.FTS.EllipticEst.H2W.s20J2 α F Ψ
        + (1 / 8) * Work.FTS.EllipticEst.H2W.s20M3 α Ψ
        + Work.FTS.EllipticEst.H2W.s20A2 Ψ + Work.FTS.EllipticEst.H2W.s20A1 Ψ
        + Work.FTS.EllipticEst.H2W.s20A0 Ψ)
      ≤ 2 * C₁ * (Work.FTS.EllipticEst.H2W.s20J2 α F Ψ
        + Work.FTS.EllipticEst.H2W.s20M3 α Ψ + Work.FTS.EllipticEst.H2W.s20A2 Ψ
        + Work.FTS.EllipticEst.H2W.s20A1 Ψ + Work.FTS.EllipticEst.H2W.s20A0 Ψ) := by
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    linarith
  linarith [hmain, hfin]

end

end Work.FTS.EllipticEst.Cores
