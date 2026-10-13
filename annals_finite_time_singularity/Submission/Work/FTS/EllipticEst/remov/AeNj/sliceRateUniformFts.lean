import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.AeI1Fts.slice_rate
import Submission.Work.FTS.EllipticEst.AeI1Fts.Defs
import Submission.Work.FTS.EllipticEst.AeI1Fts.N_bound
import Submission.Work.EllipticEst.Core.weightedCS
import Submission.Work.EllipticEst.Core.thEtaFacts
import Submission.Work.EllipticEst.Core.thEtaInvIntegralBounds
import Submission.Work.EllipticEst.Core.tendstoSqBoundLeft
import Submission.Work.FTS.EllipticEst.TT.sliceFtcKey
import Submission.Work.FTS.EllipticEst.EllTwoAsm.HeavyDerivIntegrable
import Submission.Work.FTS.EllipticEst.remov.AeNj.sliceRateTwoRight

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The uniform (`z`-free) slice rate of `U = z ∂_z u` at the two angular endpoints

`Work.FTS.EllipticEst.AeI1Fts.slice_rate` produces, for almost every `z > 0`, an *existential*
constant `C` with the two endpoint rates of the angular slice `θ ↦ U u z θ = z ∂_z u (z,θ)`.
That `C` comes from the *existential* constant `K` of
`Work.EllipticEst.Core.sliceBoundaryLimit` (`∃ K > 0, …`) and is therefore not usable in an
assembly that needs a *numerical* constant.

Here the same argument is re-run with the constant kept explicit.  The two ingredients carrying
the numerical constant are the *explicit* reciprocal-mass bound
`Work.EllipticEst.Core.thEtaInvIntegralBounds` (`∫_{(0,θ)} σ⁻¹ ≤ 2·θ^{1+η}` and its
`(π/2-θ)`-mirror) and weighted Cauchy–Schwarz `Work.EllipticEst.Core.weightedCS`; the endpoint
limit which Cauchy–Schwarz leaves over is identified with `0` through the trace lemma
`Work.FTS.EllipticEst.TT.AeI1.aeDzTraceHk`.  Since `√2 ≤ 2`, the constant `2` is uniform in
`z`, `θ`, `u` and `α`.

* `sliceRateTwoLeft` — the `0⁺` half for an arbitrary `C¹` slice `f` with finite weighted energy
  and vanishing trace at `0⁺` (proved here);
* `remov/AeNj/sliceRateTwoRight` — the mirror `(π/2)⁻` half;
* `sliceRateUniformFts` — the target, assembled from the two halves applied to the slice
  `θ ↦ U u z θ`, the derivative identity `∂_θ(U u z ·) = V u z ·` (`AeI1Fts.slice_deriv_eq`)
  and the a.e. trace vanishing `TT.AeI1.aeDzTraceHk`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov.AeNj

set_option autoImplicit false

local notation "Iθo" => Set.Ioo (0 : ℝ) (Real.pi / 2)

/-- **The `0⁺` half of the uniform slice rate.**  For `f` of class `C¹` on `(0,π/2)` whose
weighted derivative square `(f')²·σ` (`σ = thEta = sin(2θ)^{-η}`) is integrable there and whose
trace at `0⁺` vanishes,

`|f θ| ≤ 2 √(∫_{0<θ'<θ} (f')²σ) · θ^{(1+η)/2}`  for all `θ ∈ (0, π/2)`.

Proof: weighted Cauchy–Schwarz against the dual weight `σ⁻¹` applied to the exact
fundamental-theorem-of-calculus identity `f θ = ∫_{0<θ'<θ} f'` (`TT.sliceFtcKey`, the additive
constant being identified with `0` from the vanishing trace via `Core.tendstoSqBoundLeft`), the
explicit reciprocal-mass bound `thEtaInvIntegralBounds.2.1`, and finally `√2 ≤ 2`. -/
theorem sliceRateTwoLeft {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f Iθo)
    (hint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Iθo)
    (h0 : Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) :
    ∀ θ ∈ Iθo,
      |f θ| ≤ 2 * Real.sqrt (∫ θ' in Set.Ioo 0 θ,
          (deriv f θ') ^ 2 * Work.FTS.EllipticEst.thEta θ') * θ ^ ((1 + Work.Spaces.eta) / 2) := by
  have heta1 : Work.Spaces.eta < 1 := Work.Spaces.eta_lt_one
  have heta0 : 0 ≤ Work.Spaces.eta := Work.Spaces.eta_nonneg
  -- the weighted derivative square with the raw `sin`-power weight of `HeavyDerivIntegrable`
  have hint' : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Iθo := by
    simpa only [Work.FTS.EllipticEst.thEta] using hint
  -- `deriv f` is integrable on `(0,π/2)` and on every subinterval
  obtain ⟨_, hI⟩ := Work.FTS.EllipticEst.EllTwoAsm.HeavyDerivIntegrable
    (-(Work.Spaces.eta)) (by linarith) (by linarith) f hf hint'
  -- the exact FTC identity, with an additive constant `c₀`
  obtain ⟨c₀, hc₀⟩ := (Work.FTS.EllipticEst.TT.sliceFtcKey f hf hI).1
  -- weighted Cauchy–Schwarz on `(0, θ)`: the deviation bound with the constant `2`
  have hdev : ∀ θ ∈ Iθo, (f θ - c₀) ^ 2
      ≤ 2 * θ ^ (1 + Work.Spaces.eta)
          * (∫ t in Set.Ioo 0 θ, (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t) := by
    intro θ hθ
    have hsub : Set.Ioo 0 θ ⊆ Iθo := fun x hx => ⟨hx.1, lt_trans hx.2 hθ.2⟩
    have hcs := Work.EllipticEst.Core.weightedCS (s := Set.Ioo 0 θ) measurableSet_Ioo
      (w := Work.FTS.EllipticEst.thEta) (g := fun t : ℝ => deriv f t)
      (fun t ht => Work.EllipticEst.Core.thEtaFacts.1 t (hsub ht))
      (Work.EllipticEst.Core.thEtaFacts.2.2.2.mono hsub)
      ((hf.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl).mono hsub)
      (hint.mono_set hsub)
      (Work.EllipticEst.Core.thEtaInvIntegralBounds.1 θ hθ)
    have hAnn : 0 ≤ ∫ t in Set.Ioo 0 θ, (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t :=
      MeasureTheory.setIntegral_nonneg measurableSet_Ioo (fun t ht => mul_nonneg (sq_nonneg _)
        (Work.FTS.EllipticEst.thEta_nonneg ⟨le_of_lt (hsub ht).1, le_of_lt (hsub ht).2⟩))
    rw [hc₀ θ hθ]
    calc (∫ t in Set.Ioo 0 θ, deriv f t) ^ 2
        ≤ (∫ t in Set.Ioo 0 θ, (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t)
            * (∫ t in Set.Ioo 0 θ, (Work.FTS.EllipticEst.thEta t)⁻¹) := hcs
      _ ≤ (∫ t in Set.Ioo 0 θ, (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t)
            * (2 * θ ^ (1 + Work.Spaces.eta)) :=
          mul_le_mul_of_nonneg_left (Work.EllipticEst.Core.thEtaInvIntegralBounds.2.1 θ hθ) hAnn
      _ = 2 * θ ^ (1 + Work.Spaces.eta)
            * (∫ t in Set.Ioo 0 θ, (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t) := by ring
  -- the total energy is nonnegative and dominates every truncated one
  have hglob : 0 ≤ ∫ t in Iθo, (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioo (fun t ht => mul_nonneg (sq_nonneg _)
      (Work.FTS.EllipticEst.thEta_nonneg ⟨le_of_lt ht.1, le_of_lt ht.2⟩))
  have hbdd : ∀ θ ∈ Iθo, (f θ - c₀) ^ 2
      ≤ (2 * ∫ t in Iθo, (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t)
          * θ ^ (1 + Work.Spaces.eta) := by
    intro θ hθ
    have hsub : Set.Ioo 0 θ ⊆ Iθo := fun x hx => ⟨hx.1, lt_trans hx.2 hθ.2⟩
    have hmono : (∫ t in Set.Ioo 0 θ, (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t)
        ≤ ∫ t in Iθo, (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t := by
      refine MeasureTheory.setIntegral_mono_set hint ?_ ?_
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
        exact mul_nonneg (sq_nonneg _)
          (Work.FTS.EllipticEst.thEta_nonneg ⟨le_of_lt ht.1, le_of_lt ht.2⟩)
      · filter_upwards with t ht
        exact ⟨ht.1, lt_trans ht.2 hθ.2⟩
    calc (f θ - c₀) ^ 2
        ≤ 2 * θ ^ (1 + Work.Spaces.eta)
            * (∫ t in Set.Ioo 0 θ, (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t) :=
          hdev θ hθ
      _ ≤ 2 * θ ^ (1 + Work.Spaces.eta)
            * (∫ t in Iθo, (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t) :=
          mul_le_mul_of_nonneg_left hmono
            (mul_nonneg (by norm_num) (Real.rpow_nonneg hθ.1.le _))
      _ = (2 * ∫ t in Iθo, (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t)
            * θ ^ (1 + Work.Spaces.eta) := by ring
  -- the additive constant is the trace of `f` at `0⁺`, hence `0`
  have hlim : Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds c₀) :=
    Work.EllipticEst.Core.tendstoSqBoundLeft
      (M := 2 * ∫ t in Iθo, (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t)
      (mul_nonneg (by norm_num) hglob) hbdd
  have hc0 : c₀ = 0 := tendsto_nhds_unique hlim h0
  -- the rate
  intro θ hθ
  have hsq : (f θ) ^ 2
      ≤ 2 * θ ^ (1 + Work.Spaces.eta)
          * (∫ t in Set.Ioo 0 θ, (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t) := by
    have h := hdev θ hθ
    rwa [hc0, sub_zero] at h
  calc |f θ| = Real.sqrt ((f θ) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (2 * θ ^ (1 + Work.Spaces.eta)
          * ∫ t in Set.Ioo 0 θ, (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t) :=
        Real.sqrt_le_sqrt hsq
    _ = Real.sqrt 2 * θ ^ ((1 + Work.Spaces.eta) / 2)
          * Real.sqrt (∫ t in Set.Ioo 0 θ,
              (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t) := by
        have hsp : 0 ≤ θ ^ (1 + Work.Spaces.eta) := Real.rpow_nonneg hθ.1.le _
        rw [show 2 * θ ^ (1 + Work.Spaces.eta)
              * (∫ t in Set.Ioo 0 θ, (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t)
            = 2 * (θ ^ (1 + Work.Spaces.eta)
              * (∫ t in Set.Ioo 0 θ, (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t)) from by
              ring]
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) _]
        rw [Real.sqrt_mul hsp _]
        rw [show Real.sqrt (θ ^ (1 + Work.Spaces.eta)) = θ ^ ((1 + Work.Spaces.eta) / 2) from by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hθ.1.le]
          congr 1
          ring]
        ring
    _ ≤ 2 * Real.sqrt (∫ t in Set.Ioo 0 θ,
            (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t)
          * θ ^ ((1 + Work.Spaces.eta) / 2) := by
        have hsqrt2 : Real.sqrt 2 ≤ 2 := by
          nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
        have hnn : 0 ≤ θ ^ ((1 + Work.Spaces.eta) / 2)
            * Real.sqrt (∫ t in Set.Ioo 0 θ,
                (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t) :=
          mul_nonneg (Real.rpow_nonneg hθ.1.le _) (Real.sqrt_nonneg _)
        have hstep := mul_le_mul_of_nonneg_right hsqrt2 hnn
        calc Real.sqrt 2 * θ ^ ((1 + Work.Spaces.eta) / 2)
              * Real.sqrt (∫ t in Set.Ioo 0 θ,
                  (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t)
            = Real.sqrt 2 * (θ ^ ((1 + Work.Spaces.eta) / 2)
                * Real.sqrt (∫ t in Set.Ioo 0 θ,
                    (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t)) := by ring
          _ ≤ 2 * (θ ^ ((1 + Work.Spaces.eta) / 2)
                * Real.sqrt (∫ t in Set.Ioo 0 θ,
                    (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t)) := hstep
          _ = 2 * Real.sqrt (∫ t in Set.Ioo 0 θ,
                  (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t)
                * θ ^ ((1 + Work.Spaces.eta) / 2) := by ring

theorem sliceRateUniformFts {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hU : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.AeI1Fts.U u))
    (hV : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.AeI1Fts.V u)) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        |Work.FTS.EllipticEst.AeI1Fts.U u z θ|
          ≤ 2 * Real.sqrt (∫ θ' in Set.Ioo 0 θ,
                (Work.FTS.EllipticEst.AeI1Fts.V u z θ') ^ 2
                  * Work.FTS.EllipticEst.AeI1Fts.sigE θ') * θ ^ ((1 + Work.Spaces.eta) / 2))
      ∧ (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        |Work.FTS.EllipticEst.AeI1Fts.U u z θ|
          ≤ 2 * Real.sqrt (∫ θ' in Set.Ioo θ (Real.pi / 2),
                (Work.FTS.EllipticEst.AeI1Fts.V u z θ') ^ 2
                  * Work.FTS.EllipticEst.AeI1Fts.sigE θ')
            * (Real.pi / 2 - θ) ^ ((1 + Work.Spaces.eta) / 2)) := by
  have hS : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  -- the Clairaut slot `z ∂_θ∂_z u` is honestly `ℋ⁰` (it agrees with `V u` on the open quadrant)
  have hMix : Work.Spaces.HkMem α 0
      (fun z θ => z * Work.Spaces.pth (Work.Spaces.pz u) z θ) := by
    refine Work.FTS.EllipticEst.AeI1Fts.HkMem_zero_congr
      (f := Work.FTS.EllipticEst.AeI1Fts.V u)
      (g := fun z θ => z * Work.Spaces.pth (Work.Spaces.pz u) z θ) ?_ hV
    intro z θ hz hθ0 hθπ
    show z * Work.Spaces.pz (Work.Spaces.pth u) z θ
      = z * Work.Spaces.pth (Work.Spaces.pz u) z θ
    exact congrArg (fun t => z * t) (Work.Spaces.pz_pth_comm (f := u)
      ((h.smooth 2).contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds
        (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ0, hθπ⟩))))
  -- the trace of the slice vanishes at both endpoints, a.e. in `z`
  have htr := Work.FTS.EllipticEst.TT.AeI1.aeDzTraceHk α u G h
    (show Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz u z θ) from hU) hMix
  filter_upwards [htr, MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hztr hz
  have hzpos : 0 < z := Set.mem_Ioi.mp hz
  -- the slice `θ ↦ U u z θ` and its data
  have hf : ContDiffOn ℝ 1 (fun θ' => Work.FTS.EllipticEst.AeI1Fts.U u z θ') Iθo :=
    Work.FTS.EllipticEst.AeI1Fts.contDiffOn_slice_U_one hS hzpos
  have htrL : Filter.Tendsto (fun θ' => Work.FTS.EllipticEst.AeI1Fts.U u z θ')
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
    show Filter.Tendsto (fun θ' => z * Work.Spaces.pz u z θ')
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) from hztr.1
  have htrR : Filter.Tendsto (fun θ' => Work.FTS.EllipticEst.AeI1Fts.U u z θ')
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) :=
    show Filter.Tendsto (fun θ' => z * Work.Spaces.pz u z θ')
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) from hztr.2
  -- the weighted square of `V u z ·` is integrable on the *open* interval
  have hVsig : MeasureTheory.IntegrableOn
      (fun θ' => (Work.FTS.EllipticEst.AeI1Fts.V u z θ') ^ 2
        * Work.FTS.EllipticEst.AeI1Fts.sigE θ') Iθo := by
    have hzmem : z ∈ Work.Spaces.Iz := le_of_lt hzpos
    have hw : Work.Spaces.w z ≠ 0 :=
      ne_of_gt (Work.FTS.EllipticEst.TT.AeI1.w_pos_of_pos hzpos)
    have h1 : MeasureTheory.IntegrableOn
        (fun θ' => (Work.Spaces.w z) ^ 2 * ((Work.FTS.EllipticEst.AeI1Fts.V u z θ') ^ 2
          * Work.FTS.EllipticEst.AeI1Fts.sigE θ')) Work.Spaces.Iθ :=
      (hV.1 z hzmem).congr_fun (fun θ' hθ' => by
        change Work.Spaces.HkIntegrand α 0 (Work.FTS.EllipticEst.AeI1Fts.V u) z θ'
          = (Work.Spaces.w z) ^ 2 * ((Work.FTS.EllipticEst.AeI1Fts.V u z θ') ^ 2
            * Work.FTS.EllipticEst.AeI1Fts.sigE θ')
        rw [Work.FTS.EllipticEst.AeI1Fts.hk_zero_eq α _ hθ']) measurableSet_Icc
    have h2 : MeasureTheory.IntegrableOn
        (fun θ' => (Work.FTS.EllipticEst.AeI1Fts.V u z θ') ^ 2
          * Work.FTS.EllipticEst.AeI1Fts.sigE θ') Work.Spaces.Iθ := by
      have h3 : MeasureTheory.Integrable
          (fun θ' => ((Work.Spaces.w z) ^ 2)⁻¹
            * ((Work.Spaces.w z) ^ 2 * ((Work.FTS.EllipticEst.AeI1Fts.V u z θ') ^ 2
              * Work.FTS.EllipticEst.AeI1Fts.sigE θ')))
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
        MeasureTheory.Integrable.const_mul h1 (((Work.Spaces.w z) ^ 2)⁻¹)
      refine MeasureTheory.IntegrableOn.congr_fun h3 (fun θ' _ => ?_) measurableSet_Icc
      exact inv_mul_cancel_left₀ (pow_ne_zero 2 hw) _
    exact h2.mono_set Set.Ioo_subset_Icc_self
  -- the weighted derivative square of the slice is the same object
  have hint : MeasureTheory.IntegrableOn
      (fun θ' : ℝ => (deriv (fun θ'' => Work.FTS.EllipticEst.AeI1Fts.U u z θ'') θ') ^ 2
        * Work.FTS.EllipticEst.thEta θ') Iθo := by
    refine hVsig.congr_fun (fun θ' hθ' => ?_) measurableSet_Ioo
    rw [Work.FTS.EllipticEst.AeI1Fts.slice_deriv_eq hS hzpos hθ']
    simp only [Work.FTS.EllipticEst.AeI1Fts.sigE, Work.FTS.EllipticEst.thEta]
  -- the two truncated energies, rewritten in terms of `V u z ·`
  have hIntL : ∀ θ ∈ Iθo,
      (∫ θ' in Set.Ioo 0 θ,
          (deriv (fun θ'' => Work.FTS.EllipticEst.AeI1Fts.U u z θ'') θ') ^ 2
            * Work.FTS.EllipticEst.thEta θ')
        = ∫ θ' in Set.Ioo 0 θ, (Work.FTS.EllipticEst.AeI1Fts.V u z θ') ^ 2
            * Work.FTS.EllipticEst.AeI1Fts.sigE θ' := by
    intro θ hθ
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun θ' hθ' => ?_)
    rw [Work.FTS.EllipticEst.AeI1Fts.slice_deriv_eq hS hzpos ⟨hθ'.1, lt_trans hθ'.2 hθ.2⟩]
    simp only [Work.FTS.EllipticEst.AeI1Fts.sigE, Work.FTS.EllipticEst.thEta]
  have hIntR : ∀ θ ∈ Iθo,
      (∫ θ' in Set.Ioo θ (Real.pi / 2),
          (deriv (fun θ'' => Work.FTS.EllipticEst.AeI1Fts.U u z θ'') θ') ^ 2
            * Work.FTS.EllipticEst.thEta θ')
        = ∫ θ' in Set.Ioo θ (Real.pi / 2), (Work.FTS.EllipticEst.AeI1Fts.V u z θ') ^ 2
            * Work.FTS.EllipticEst.AeI1Fts.sigE θ' := by
    intro θ hθ
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun θ' hθ' => ?_)
    rw [Work.FTS.EllipticEst.AeI1Fts.slice_deriv_eq hS hzpos ⟨lt_trans hθ.1 hθ'.1, hθ'.2⟩]
    simp only [Work.FTS.EllipticEst.AeI1Fts.sigE, Work.FTS.EllipticEst.thEta]
  constructor
  · intro θ hθ
    have hres := sliceRateTwoLeft hf hint htrL θ hθ
    rw [hIntL θ hθ] at hres
    exact hres
  · intro θ hθ
    have hres := sliceRateTwoRight hf hint htrR θ hθ
    rw [hIntR θ hθ] at hres
    exact hres

end Work.FTS.EllipticEst.remov.AeNj
