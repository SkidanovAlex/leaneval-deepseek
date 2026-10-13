import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongEps.EpsRLX.ProfileSlotCompare
import Submission.Work.FTS.EllipticEst.ThetaU.OpenSliceAux.DthIter_DzIter_eqOn_of_isOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsRLX.ProfileDzSlot

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- Almost every `θ ∈ Iθ = [0,π/2]` lies in the open interval `(0,π/2)` (the two endpoints are
null).  Used to transfer the pointwise identities that hold only on the *open* quadrant. -/
theorem ae_mem_Ioo_Iθ_aux :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  change ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) (Real.pi / 2))),
    θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)
  rw [← MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
      (b := Real.pi / 2))]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

/-- **The slicewise Hardy transfer for the pure `D_z`-slot of the `ε`-scheme.**

The same statement as the sibling module
`Submission.Work.FTS.StrongEps.EpsRLX.ProfileDzSlot.hardy_slice_dzIter_le`; kept here so that the
main theorem below is self-contained.  For a.e. `z > 0` the `θ`-slice `u := D_z^b f z ·` is `C¹`
on `(0,π/2)` with vanishing traces at both endpoints (from `BdryTraces α 6 f`, `a = 0` slots), so
the weighted Hardy inequality `hardySinGam_weak` with `c = γ` gives

`∫_θ sin(2θ)^{-γ} u² ≤ C/(γ-1)² ∫_θ sin(2θ)^{2-γ}(u')²`,

which is the stated bound because `(epsW)² = w² sin(2θ)^{-γ}` on `Iθ` and
`sin(2θ)·u' = mixed b 1 f` a.e. on `Iθ` (the identity holds on the open quadrant). -/
theorem hardy_slice_local :
    ∃ C : ℝ, 0 < C ∧ ∀ {α : ℝ} {f : ℝ → ℝ → ℝ}, α ∈ Set.Ioc 0 1 →
      Work.FTS.EllipticEst.SmoothOpen f → Work.FTS.Nonlin.BdryTraces α 6 f →
      ∀ b : ℕ, b ≤ 4 →
      (∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
          MeasureTheory.Integrable
            (fun θ : ℝ => (Work.Spaces.mixed b 1 f z θ * Work.Spaces.Wt α z θ) ^ 2)
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) →
      ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.DzIter b f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2)
          ≤ C / (Work.Spaces.gam α - 1) ^ 2
            * ∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.mixed b 1 f z θ * Work.Spaces.Wt α z θ) ^ 2
        ∧ MeasureTheory.Integrable
            (fun θ : ℝ =>
              (Work.Spaces.DzIter b f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2)
            (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  obtain ⟨CH, hCHpos, hCH⟩ := Work.FTS.StrongEps.EpsSqTools.hardySinGam_weak
  refine ⟨CH, hCHpos, ?_⟩
  intro α f hα hso htr b hb hslot_ae
  filter_upwards [hslot_ae, Work.FTS.StrongEps.EpsSqTools.ae_pos_Iz] with z hslot hz
  have hγ1 : 1 < Work.Spaces.gam α := Work.Spaces.one_lt_gam hα.1
  have hγ32 : Work.Spaces.gam α ≤ 3 / 2 := by rw [Work.Spaces.gam]; linarith [hα.2]
  -- the slice is `C¹` on the open interval
  have hu_cd : ContDiffOn ℝ 1 (fun θ : ℝ => Work.Spaces.DzIter b f z θ)
      (Set.Ioo 0 (Real.pi / 2)) :=
    ((hso.DzIter b).curry_θ hz).of_le
      (show (1 : WithTop ℕ∞) ≤ Work.Stability.smoothOrder from by
        simp [Work.Stability.smoothOrder])
  -- the vanishing traces at both endpoints, from `BdryTraces α 6 f`
  have htrb := htr 0 b (by omega)
  have ht1 : Tendsto (fun θ : ℝ => Work.Spaces.DzIter b f z θ) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    Work.FTS.H2.HQ.tendsto_nhdsGT_zero_of_traces α hα.1
      (u := fun θ : ℝ => Work.Spaces.mixed b 0 f z θ)
      (htrb.2 z (Set.mem_Ioi.mpr hz)).1
  have ht2 : Tendsto (fun θ : ℝ => Work.Spaces.DzIter b f z θ) (𝓝[<] (Real.pi / 2)) (𝓝 0) :=
    Work.FTS.H2.HQ.tendsto_nhdsLT_zero_of_traces α hα.1
      (u := fun θ : ℝ => Work.Spaces.mixed b 0 f z θ)
      (htrb.2 z (Set.mem_Ioi.mpr hz)).2
  -- the identity `D_θ(D_z^b f) = mixed b 1 f` on the open quadrant
  have hEqOn : Set.EqOn
      (Function.uncurry (Work.Spaces.DthIter 1 (Work.Spaces.DzIter b f)))
      (Function.uncurry (Work.Spaces.mixed b 1 f))
      (Work.FTS.EllipticEst.Q0) :=
    Work.FTS.EllipticEst.ThetaU.OpenSliceAux.DthIter_DzIter_eqOn_of_isOpen
      (V := Work.FTS.EllipticEst.Q0) (g := f)
      Work.FTS.EllipticEst.isOpen_Q0
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall f).mp hso) b 1
  have hDth : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.Spaces.mixed b 1 f z θ
        = Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.DzIter b f) z θ := by
    intro θ hθ
    have hm : Work.Spaces.mixed b 1 f z θ
        = Work.Spaces.DthIter 1 (Work.Spaces.DzIter b f) z θ :=
      (hEqOn (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩)).symm
    have hD : Work.Spaces.DthIter 1 (Work.Spaces.DzIter b f) z θ
        = Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.DzIter b f) z θ := rfl
    rw [hm, hD]
  -- the weight algebra, a.e. in `θ`
  have hsin2_ae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      (Work.Spaces.mixed b 1 f z θ * Work.Spaces.Wt α z θ) ^ 2
        = Work.Spaces.w z ^ 2 * (Real.sin (2 * θ) ^ (2 - Work.Spaces.gam α)
            * (Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2) := by
    filter_upwards [ae_mem_Ioo_Iθ_aux] with θ hθ
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
    have hWt := Work.FTS.StrongEps.EpsSqTools.Wt_sq_eq_eps (α := α) (z := z) hθI
    have hpth := Work.FTS.H2.pth_sq_mul_sin_eq α hα.1 hα.2
      (Work.Spaces.DzIter b f) z θ hθI
    have hDth' : Work.Spaces.Dth (Work.Spaces.DzIter b f) z θ = Work.Spaces.mixed b 1 f z θ := by
      have h1 : Work.Spaces.Dth (Work.Spaces.DzIter b f) z θ
          = Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.DzIter b f) z θ := rfl
      rw [h1, ← hDth θ hθ]
    exact (calc Work.Spaces.w z ^ 2 * (Real.sin (2 * θ) ^ (2 - Work.Spaces.gam α)
            * (Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2)
        = Work.Spaces.w z ^ 2 * ((Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2
            * Real.sin (2 * θ) ^ (2 - Work.Spaces.gam α)) := by ring
      _ = Work.Spaces.w z ^ 2 * ((Work.Spaces.Dth (Work.Spaces.DzIter b f) z θ) ^ 2
            * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α))) := by rw [hpth]
      _ = Work.Spaces.w z ^ 2 * ((Work.Spaces.mixed b 1 f z θ) ^ 2
            * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α))) := by rw [hDth']
      _ = (Work.Spaces.mixed b 1 f z θ) ^ 2
            * (Work.Spaces.w z ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α))) := by ring
      _ = (Work.Spaces.mixed b 1 f z θ) ^ 2 * (Work.Spaces.Wt α z θ) ^ 2 := by rw [hWt]
      _ = (Work.Spaces.mixed b 1 f z θ * Work.Spaces.Wt α z θ) ^ 2 := by rw [mul_pow]).symm
  -- Hardy's derivative-side integrability, transported from the slot
  have hRwire : MeasureTheory.Integrable
      (fun θ : ℝ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ) ^ (2 - Work.Spaces.gam α)
        * (Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    hslot.congr hsin2_ae
  have hw_ne : Work.Spaces.w z ^ 2 ≠ 0 := by
    have h1 : (0 : ℝ) < (1 + z) ^ 2 := by positivity
    have h2 : (0 : ℝ) < z ^ 2 := by positivity
    rw [Work.Spaces.w]
    exact pow_ne_zero 2 (div_ne_zero (ne_of_gt h1) (ne_of_gt h2))
  have hRint : MeasureTheory.Integrable
      (fun θ : ℝ => Real.sin (2 * θ) ^ (2 - Work.Spaces.gam α)
        * (Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    refine (hRwire.const_mul ((Work.Spaces.w z ^ 2)⁻¹)).congr ?_
    filter_upwards with θ
    rw [← mul_assoc, inv_mul_cancel₀ hw_ne, one_mul]
  obtain ⟨hHint, hHle⟩ := hCH (Work.Spaces.gam α)
    (fun θ : ℝ => Work.Spaces.DzIter b f z θ) hγ1 hγ32 hu_cd ht1 ht2
    (by simpa only [MeasureTheory.IntegrableOn, Work.Spaces.pth] using hRint)
  have hHle' : (∫ θ in Work.Spaces.Iθ,
        Real.sin (2 * θ) ^ (-(Work.Spaces.gam α)) * (Work.Spaces.DzIter b f z θ) ^ 2)
      ≤ CH / (Work.Spaces.gam α - 1) ^ 2 * ∫ θ in Work.Spaces.Iθ,
          Real.sin (2 * θ) ^ (2 - Work.Spaces.gam α)
            * (Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2 := by
    simpa only [Work.Spaces.pth] using hHle
  -- the `θ`-integral identity of the two slot integrals
  have hsinteq : Work.Spaces.w z ^ 2 * (∫ θ in Work.Spaces.Iθ,
        Real.sin (2 * θ) ^ (2 - Work.Spaces.gam α)
          * (Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2)
      = ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.mixed b 1 f z θ * Work.Spaces.Wt α z θ) ^ 2 := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hsin2_ae] with θ hθ
    exact hθ.symm
  -- the `θ`-integrability of the `epsW`-slice
  have heps_int : MeasureTheory.Integrable
      (fun θ : ℝ => (Work.Spaces.DzIter b f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    refine (hHint.const_mul (Work.Spaces.w z ^ 2)).congr ?_
    refine MeasureTheory.ae_restrict_of_forall_mem
      (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc) fun θ hθ => ?_
    show Work.Spaces.w z ^ 2 * (Real.sin (2 * θ) ^ (-(Work.Spaces.gam α))
        * (Work.Spaces.DzIter b f z θ) ^ 2)
      = (Work.Spaces.DzIter b f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2
    have h1 : (Work.FTS.StrongEps.epsW α z θ) ^ 2
        = Work.Spaces.w z ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α)) :=
      Work.FTS.StrongEps.EpsSqTools.epsW_sq_eq (α := α) (z := z) hθ
    rw [mul_pow, h1]
    ring
  refine ⟨?_, heps_int⟩
  calc (∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.DzIter b f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2)
      = Work.Spaces.w z ^ 2 * ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.DzIter b f z θ) ^ 2
            * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α)) :=
        Work.FTS.StrongEps.EpsSqTools.epsSq_slice_eq α z (Work.Spaces.DzIter b f)
    _ = Work.Spaces.w z ^ 2 * ∫ θ in Work.Spaces.Iθ,
          Real.sin (2 * θ) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.DzIter b f z θ) ^ 2 := by
        congr 1
        exact MeasureTheory.integral_congr_ae
          (Filter.Eventually.of_forall fun θ => by ring)
    _ ≤ Work.Spaces.w z ^ 2 * (CH / (Work.Spaces.gam α - 1) ^ 2
          * ∫ θ in Work.Spaces.Iθ, Real.sin (2 * θ) ^ (2 - Work.Spaces.gam α)
              * (Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2) :=
        mul_le_mul_of_nonneg_left hHle' (sq_nonneg _)
    _ = CH / (Work.Spaces.gam α - 1) ^ 2 * (Work.Spaces.w z ^ 2
          * ∫ θ in Work.Spaces.Iθ, Real.sin (2 * θ) ^ (2 - Work.Spaces.gam α)
              * (Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2) := by ring
    _ = CH / (Work.Spaces.gam α - 1) ^ 2 * ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.mixed b 1 f z θ * Work.Spaces.Wt α z θ) ^ 2 := by rw [hsinteq]

/-- **The pure `D_z`-slots of the `ε`-scheme are dominated by the `ℋ⁶`-norm.**

For `α ∈ (0,1]`, `f` smooth on the open quadrant, honestly in `ℋ⁶` and with the boundary traces
`BdryTraces α 6 f`, every radial slot `D_z^b f` (`b ≤ 4`) is in the weighted space `X` of the
`ε`-scheme (`EpsMem`), with weighted energy bounded by `C/(γ-1)² · |f|²_{ℋ⁶}` (`γ = 1 + α/10`).

The energy of the slot carries the *mixed* weight `w² sin(2θ)^{-γ}`, which is more singular at
the angular boundary than the pure `D_z`-weight `w² sin(2θ)^{-η}` of `HkIntegrand`; the extra
factor `(γ-1)^{-2}` pays for the angular weighted Hardy inequality
(`Work.FTS.StrongEps.EpsSqTools.hardySinGam_weak`) which trades the two units of
`sin(2θ)^{-γ}` on `D_z^b f` for the derivative block `D_z^b D_θ f = mixed b 1 f`, i.e. for the
`(b,1)`-slot of `HkIntegrand α 6 f` (`Work.FTS.StrongEps.EpsRLX.slot_mixed_le_HkSq`).  The
boundary traces in `BdryTraces α 6 f` (the `a = 0` slots) are exactly the vanishing conditions
of the Hardy inequality. -/
theorem EpsSq_dzIter_le_HkSq :
    ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1, ∀ {f : ℝ → ℝ → ℝ},
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
      Work.FTS.Nonlin.BdryTraces α 6 f → ∀ b : ℕ, b ≤ 4 →
      Work.FTS.StrongEps.EpsMem α (Work.Spaces.DzIter b f) ∧
      Work.FTS.StrongEps.EpsSq α (Work.Spaces.DzIter b f)
        ≤ C / (Work.Spaces.gam α - 1) ^ 2 * Work.Spaces.HkSq α 6 f := by
  obtain ⟨C, hCpos, hC⟩ := hardy_slice_local
  refine ⟨C, hCpos, ?_⟩
  intro α hα f hso hm htr b hb
  -- The `(b,1)` mixed slot: product integrability, a.e. slice integrability, and its value.
  have hslot_prod :=
    Work.FTS.EllipticEst.AeSlotOneAe.Interp.integrable_uncurry_slot_mixed (α := α) (k := 6)
      hso hm b 1 (by norm_num) (by omega)
  have hslot_ae : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable
        (fun θ : ℝ => (Work.Spaces.mixed b 1 f z θ * Work.Spaces.Wt α z θ) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    hslot_prod.prod_right_ae
  have hslot_le :=
    Work.FTS.StrongEps.EpsRLX.slot_mixed_le_HkSq (α := α) (k := 6) hso hm (j := b) (i := 1)
      (by norm_num) (by omega)
  -- the slicewise Hardy transfer
  have hpoint : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.DzIter b f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2)
        ≤ C / (Work.Spaces.gam α - 1) ^ 2
          * ∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.mixed b 1 f z θ * Work.Spaces.Wt α z θ) ^ 2
      ∧ MeasureTheory.Integrable
          (fun θ : ℝ =>
            (Work.Spaces.DzIter b f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2)
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    hC hα hso htr b hb hslot_ae
  have hKpos : (0 : ℝ) ≤ C / (Work.Spaces.gam α - 1) ^ 2 :=
    div_nonneg hCpos.le (by positivity)
  refine ⟨?_, ?_⟩
  · -- `EpsMem α (DzIter b f)`
    have hAESM : MeasureTheory.AEStronglyMeasurable
        (fun p : ℝ × ℝ =>
          (Work.Spaces.DzIter b f p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
      Work.Spaces.aesm_of_continuousOn_Qd _
        (ContinuousOn.pow
          (ContinuousOn.mul (hso.DzIter b).continuousOn
            (Work.FTS.StrongEps.EpsSqTools.continuousOn_epsW α)) 2)
    have hslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        MeasureTheory.HasFiniteIntegral
          (fun θ : ℝ => (Work.Spaces.DzIter b f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2)
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      filter_upwards [hpoint] with z hz using hz.2.2
    have hzInt : MeasureTheory.HasFiniteIntegral
        (fun z : ℝ => ∫ θ, ‖(Work.Spaces.DzIter b f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2‖
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
      have haesm : MeasureTheory.AEStronglyMeasurable
          (fun z : ℝ => ∫ θ, ‖(Work.Spaces.DzIter b f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2‖
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
          (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
        hAESM.norm.integral_prod_right'
      have hbdd : (fun z : ℝ => ‖∫ θ,
            ‖(Work.Spaces.DzIter b f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2‖
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)‖)
          ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz]
          (fun z : ℝ => C / (Work.Spaces.gam α - 1) ^ 2
            * (∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.mixed b 1 f z θ * Work.Spaces.Wt α z θ) ^ 2)) := by
        filter_upwards [hpoint] with z hz
        rw [Real.norm_of_nonneg (MeasureTheory.integral_nonneg fun θ => norm_nonneg _)]
        refine le_trans (le_of_eq ?_) hz.1
        exact MeasureTheory.integral_congr_ae
          (Filter.Eventually.of_forall fun θ => Real.norm_of_nonneg (sq_nonneg _))
      exact (MeasureTheory.Integrable.mono' (hslot_le.1.const_mul _) haesm hbdd).2
    have hmeas : (MeasureTheory.volume : Measure (ℝ × ℝ)).restrict
          (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
        = (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_restrict]
    rw [Work.FTS.StrongEps.EpsMem, MeasureTheory.IntegrableOn, hmeas]
    exact ⟨hAESM, (MeasureTheory.hasFiniteIntegral_prod_iff' hAESM).mpr ⟨hslice, hzInt⟩⟩
  · -- the energy bound
    have hmain : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.DzIter b f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2)
        ≤ C / (Work.Spaces.gam α - 1) ^ 2
          * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.mixed b 1 f z θ * Work.Spaces.Wt α z θ) ^ 2) := by
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun z =>
          MeasureTheory.integral_nonneg fun θ => sq_nonneg _)
        (hslot_le.1.const_mul _) ?_
      filter_upwards [hpoint] with z hz using hz.1
    calc Work.FTS.StrongEps.EpsSq α (Work.Spaces.DzIter b f)
        = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.DzIter b f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2 := rfl
      _ ≤ C / (Work.Spaces.gam α - 1) ^ 2
            * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.mixed b 1 f z θ * Work.Spaces.Wt α z θ) ^ 2) := hmain
      _ ≤ C / (Work.Spaces.gam α - 1) ^ 2 * Work.Spaces.HkSq α 6 f :=
          mul_le_mul_of_nonneg_left hslot_le.2 hKpos

end Work.FTS.StrongEps.EpsRLX.ProfileDzSlot
