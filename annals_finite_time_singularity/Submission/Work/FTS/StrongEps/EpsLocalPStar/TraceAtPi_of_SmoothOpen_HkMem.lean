import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.StrongEps.EpsLocalPStar.SliceTracePiO
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.EllipticEst.AeSlotOneAe.Interp.TkA_slotIntegrable
import Submission.Work.FTS.StrongEps.EpsSqTools.EpsSq_le_HkSq_ClassC
import Submission.Work.FTS.StrongEps.EpsZero.pz_prod_integrable_of_smoothOpen
import Submission.Work.FTS.StrongEps.EpsLocalPStar.SliceTracePiPth
import Submission.Work.FTS.StrongEps.EpsLocalPStar.TraceThetaStepPi

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

open scoped Real Topology
open MeasureTheory Set Filter

/-!
## The angular trace at `θ = π/2`, with the weighted Hardy rate and integrability

For a datum `f` which is `C^∞` on the open quadrant (`Work.FTS.EllipticEst.SmoothOpen`) and
honest in `ℋ¹` (`Work.Spaces.HkMem α 1 f`), the `θ`-slices `θ ↦ f z θ` have a trace `lam z` at
`θ = π/2⁻` for almost every `z > 0`, converging at the weighted Hardy rate

  `(f z θ - lam z)² ≤ (100/(γ-1))·sin(2θ)^{γ-1}·∫_{Iθ} sin(2σ)^{2-γ}(∂_θ f)²`,  `π/4 < θ < π/2`,

and the trace is integrable against the multiplicative measure `dz/z`
(`Integrable (fun u => lam (exp u))`).

**Route.**

* The two slots of the level-`1` norm that matter are `S z = ∫_θ (D_θf·W)² = w(z)²·∫_θ
  sin^{2-γ}(∂_θf)²` and `T z = ∫_θ (f·w/sin^{η/2})² = w(z)²·∫_θ f² sin^{-η}`; both are
  integrable in `z`, with `∫S ≤ |f|²_{ℋ¹}` and `∫T ≤ |f|²_{ℋ¹}` (`L2Sq_mixed_le_HkSq`,
  `L2Sq_DzIter_le_HkSq`).
* For a.e. `z > 0` the slot integrability of the `(0,1)`-slot gives, through `SliceTracePiPth`
  (the `π/2`-endpoint trace of a single slice in the `pth`-vocabulary), both the trace and its
  rate, and — through the right-endpoint Jensen step `TraceThetaStepPi` — the `L²` bound
  `lam z² ≤ (200/(γ-1))·A z + (8/π)·K z`, where `A z = ∫_θ sin^{2-γ}(∂_θf)²` and
  `K z = ∫_θ f² sin^{-η}`.
* Multiplying by `w(z)²` converts `A` into `S` and `K` into `T`, so
  `lam z² w(z)² ≤ (200/(γ-1))S z + (8/π)T z` a.e., the right-hand side being integrable with
  integral at most `(200/(γ-1) + 8/π)|f|²_{ℋ¹} ≤ (300/(γ-1))|f|²_{ℋ¹}`.
* Finally `2ab ≤ a² + b²` with the elementary weight `z/(1+z)² = 1/(z·w(z))` gives
  `∫_{(0,∞)} |lam z|/z dz ≤ (1/2)∫ (lam·w)² + (1/2)∫ (z/(1+z)²)² < ∞`, and the change of
  variables `z = exp u` (`integrable_comp_exp`) converts this into `Integrable (lam ∘ exp)`.

The only point that needs care is the measurability of `lam`: it is defined as the `liminf` of
the slice along the sequence `π/2 - 1/(n+2)`, each term being the indicator of `(0,∞)` applied
to the slice — measurable because the slice is continuous on the open half-line
(`ContinuousOn.measurable_piecewise`). -/

/-- The indicator (on `(0,∞)`) of a function continuous on `(0,∞)` is measurable. -/
private theorem measurable_indicator_Ioi_of_continuousOn {g : ℝ → ℝ}
    (h : ContinuousOn g (Set.Ioi 0)) :
    Measurable ((Set.Ioi (0:ℝ)).indicator g) := by
  rw [← Set.piecewise_eq_indicator]
  exact h.measurable_piecewise continuousOn_const measurableSet_Ioi
/-! ## Helper lemmas -/

/-- Pointwise `η`-slot identity on `Iθ`. -/
private theorem eta_slot_pointwise {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) (h : ℝ) :
    (h * (Work.Spaces.w z / (Real.sin (2*θ))^(Work.Spaces.eta/2)))^2
      = (Work.Spaces.w z)^2 * (h^2 * (Real.sin (2*θ))^(-Work.Spaces.eta)) := by
  have hs := Work.FTS.StrongEps.EpsSqTools.sin_two_nonneg_Iθ_eps hθ
  have hpow : ((Real.sin (2*θ))^(Work.Spaces.eta/2))^2 = (Real.sin (2*θ))^(Work.Spaces.eta) := by
    rw [Work.FTS.StrongEps.EpsSqTools.sin_rpow_sq hs]; congr 1; ring
  rw [mul_pow, div_pow, hpow, Real.rpow_neg hs]
  ring

/-- The `η`-weighted angular energy of a slice is integrable, from the corresponding
`(0,0)`-slot. -/
private theorem integrableOn_etaSlot_of_slot {z : ℝ} {f : ℝ → ℝ → ℝ} (hz : 0 < z)
    (h : MeasureTheory.IntegrableOn
      (fun θ => (f z θ * (Work.Spaces.w z / (Real.sin (2*θ))^(Work.Spaces.eta/2)))^2)
      Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn
      (fun θ => (f z θ)^2 * (Real.sin (2*θ))^(-Work.Spaces.eta)) Work.Spaces.Iθ := by
  have hw : (Work.Spaces.w z)^2 ≠ 0 := by
    have h1 : (0:ℝ) < (1+z)^2 := by positivity
    have h2 : (0:ℝ) < z^2 := by positivity
    rw [Work.Spaces.w]; exact pow_ne_zero 2 (div_ne_zero (ne_of_gt h1) (ne_of_gt h2))
  refine ((h.const_mul (((Work.Spaces.w z)^2)⁻¹))).congr ?_
  refine MeasureTheory.ae_restrict_of_forall_mem
    (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc) (fun θ hθ => ?_)
  show ((Work.Spaces.w z)^2)⁻¹
      * (f z θ * (Work.Spaces.w z / (Real.sin (2*θ))^(Work.Spaces.eta/2)))^2
    = (f z θ)^2 * (Real.sin (2*θ))^(-Work.Spaces.eta)
  rw [eta_slot_pointwise hθ (f z θ), ← mul_assoc, inv_mul_cancel₀ hw, one_mul]

/-- The `η`-slot integral identity: the weighted slot is `w²` times the plain `η`-energy. -/
private theorem integral_etaSlot_eq {z : ℝ} {f : ℝ → ℝ → ℝ} (_hz : 0 < z) :
    (∫ θ in Work.Spaces.Iθ,
        (f z θ * (Work.Spaces.w z / (Real.sin (2*θ))^(Work.Spaces.eta/2)))^2)
      = (Work.Spaces.w z)^2 * ∫ θ in Work.Spaces.Iθ,
          (f z θ)^2 * (Real.sin (2*θ))^(-Work.Spaces.eta) := by
  rw [← MeasureTheory.integral_const_mul]
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc
    (fun θ hθ => eta_slot_pointwise hθ (f z θ))

/-- `(z/(1+z)²)²` is integrable on `(0,∞)`. -/
private theorem integrableOn_sq_div_one_add_sq :
    MeasureTheory.IntegrableOn (fun z : ℝ => (z/(1+z)^2)^2) (Set.Ioi 0) := by
  refine MeasureTheory.Integrable.mono'
    Work.FTS.StrongEps.EpsZero.integrableOn_one_div_one_add_sq ?_ ?_
  · have : Measurable (fun z : ℝ => (z/(1+z)^2)^2) := by fun_prop
    exact this.aestronglyMeasurable
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
    have hz' : (0:ℝ) < z := hz
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have h0 : (0:ℝ) < 1 + z := by linarith
    have h1 : z^2 ≤ (1+z)^2 := by nlinarith
    rw [div_pow]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    calc z^2 * (1+z)^2 ≤ (1+z)^2 * (1+z)^2 := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = 1 * ((1+z)^2)^2 := by ring

section Main

theorem TraceAtPi_of_SmoothOpen_HkMem {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {f : ℝ → ℝ → ℝ}
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α 1 f) :
    ∃ lam : ℝ → ℝ, Measurable lam ∧
      (∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))),
        Filter.Tendsto (fun θ => f z θ)
          (nhdsWithin (Real.pi/2) (Set.Iio (Real.pi/2))) (nhds (lam z))) ∧
      (∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))),
          ∀ θ ∈ Set.Ioo (Real.pi/4) (Real.pi/2),
        (f z θ - lam z)^2
          ≤ 100 / (Work.Spaces.gam α - 1) * (Real.sin (2*θ))^(Work.Spaces.gam α - 1)
            * (∫ σ in Work.Spaces.Iθ,
                (Real.sin (2*σ))^(2 - Work.Spaces.gam α) * (Work.Spaces.pth f z σ)^2)) ∧
      MeasureTheory.Integrable (fun u : ℝ => lam (Real.exp u)) := by
  classical
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  have hγ1 : 1 < Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
  have hγm : 0 < Work.Spaces.gam α - 1 := by rw [Work.Spaces.gam]; linarith
  have hγle : Work.Spaces.gam α - 1 ≤ 1 := by rw [Work.Spaces.gam]; linarith
  -- the two weighted slots and the two angular energies
  let S : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ)^2
  let T : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ,
      (f z θ * (Work.Spaces.w z / (Real.sin (2*θ))^(Work.Spaces.eta/2)))^2
  let A : ℝ → ℝ := fun z => ∫ σ in Work.Spaces.Iθ,
      (Real.sin (2*σ))^(2 - Work.Spaces.gam α) * (Work.Spaces.pth f z σ)^2
  let Kmaj : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ,
      (f z θ)^2 * (Real.sin (2*θ))^(-Work.Spaces.eta)
  -- (1) the slots are integrable in z and dominated by the `ℋ¹`-norm
  have hprodMixed : MeasureTheory.Integrable
      (Function.uncurry (fun z θ : ℝ =>
        (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ)^2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.FTS.EllipticEst.AeSlotOneAe.Interp.integrable_uncurry_slot_mixed
      (α := α) (k := 1) hso hm 0 1 (by norm_num) (by norm_num)
  have hSint : MeasureTheory.Integrable S (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    hprodMixed.integral_prod_left
  have hSle : (∫ z in Work.Spaces.Iz, S z) ≤ Work.Spaces.HkSq α 1 f := by
    have h := Work.Spaces.L2Sq_mixed_le_HkSq α 1 f hm 1 0 (by norm_num) (by norm_num)
    rw [Work.Spaces.L2Sq] at h
    exact h
  have hprodZ : MeasureTheory.Integrable
      (Function.uncurry (fun z θ : ℝ =>
        (Work.Spaces.DzIter 0 f z θ
          * (Work.Spaces.w z / (Real.sin (2*θ))^(Work.Spaces.eta/2)))^2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.FTS.EllipticEst.AeSlotOneAe.Interp.integrable_uncurry_slot_z
      (α := α) (k := 1) hso hm 0 (by norm_num)
  have hTint : MeasureTheory.Integrable T (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    hprodZ.integral_prod_left
  have hTle : (∫ z in Work.Spaces.Iz, T z) ≤ Work.Spaces.HkSq α 1 f := by
    have h := Work.Spaces.L2Sq_DzIter_le_HkSq α 1 f hm 0 (by norm_num)
    rw [Work.Spaces.L2Sq] at h
    exact h
  have hHknn : 0 ≤ Work.Spaces.HkSq α 1 f := by
    rw [Work.Spaces.HkSq]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Ici (fun z _ =>
      MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ _ =>
        Work.Spaces.HkIntegrand_nonneg α 1 f z θ))
  -- (2) the measure on `(0,∞)` and on `Iz` agree
  have hIz : (MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Ioi (0:ℝ))
      = MeasureTheory.volume.restrict Work.Spaces.Iz :=
    MeasureTheory.restrict_Ioi_eq_restrict_Ici
  have haepos : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))), 0 < z := by
    rw [hIz]; exact Work.FTS.StrongEps.EpsSqTools.ae_pos_Iz
  have hslot_ae : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))),
      MeasureTheory.Integrable (fun θ => (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ)^2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    rw [hIz]
    exact hprodMixed.prod_right_ae
  -- (3) the a.e. trace at `π/2` with its rate and the `L²` bound on the limit
  have hgood : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))), ∃ mu : ℝ,
      Filter.Tendsto (fun θ => f z θ) (nhdsWithin (Real.pi/2) (Set.Iio (Real.pi/2))) (nhds mu) ∧
      (∀ θ ∈ Set.Ioo (Real.pi/4) (Real.pi/2),
        (f z θ - mu)^2 ≤ 100/(Work.Spaces.gam α - 1)
          * (Real.sin (2*θ))^(Work.Spaces.gam α - 1) * A z) ∧
      mu^2 ≤ 200/(Work.Spaces.gam α - 1) * A z + 8/Real.pi * Kmaj z := by
    filter_upwards [hslot_ae, haepos] with z hslot hz
    have hAnn : 0 ≤ A z := by
      simp only [A]
      exact MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun σ hσ =>
        mul_nonneg (Real.rpow_nonneg (Work.FTS.StrongEps.EpsSqTools.sin_two_nonneg_Iθ_eps hσ) _)
          (sq_nonneg _))
    have hetaint : MeasureTheory.IntegrableOn
        (fun θ => (f z θ)^2 * (Real.sin (2*θ))^(-Work.Spaces.eta)) Work.Spaces.Iθ :=
      integrableOn_etaSlot_of_slot hz
        (Work.FTS.EllipticEst.integrableOn_zSummand α 1 hso hm 0 (by norm_num) (le_of_lt hz))
    obtain ⟨mu, hmu, hbd⟩ := SliceTracePiPth hα hz hso hslot
    exact ⟨mu, hmu, hbd, TraceThetaStepPi hγ1 hAnn hetaint hbd⟩
  -- (4) the trace at `π/2` along the sequence `π/2 - 1/(n+2)`, defined as a liminf
  let θs : ℕ → ℝ := fun n => Real.pi/2 - 1/((n:ℝ) + 2)
  have hθs_mem : ∀ n : ℕ, θs n ∈ Set.Ioo (0:ℝ) (Real.pi/2) := by
    intro n
    have h1 : (0:ℝ) < 1/((n:ℝ)+2) := one_div_pos.mpr (by
      have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      linarith)
    have h2 : (1:ℝ)/((n:ℝ)+2) ≤ 1/2 := by
      have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      rw [div_le_div_iff₀ (by linarith : (0:ℝ) < (n:ℝ)+2)
        (show (0:ℝ) < 2 by norm_num)]
      linarith
    constructor
    · simp only [θs]; linarith [Real.pi_gt_three]
    · simp only [θs]; linarith
  have hθs_tend : Filter.Tendsto θs atTop
      (nhdsWithin (Real.pi/2) (Set.Iio (Real.pi/2))) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, Filter.Eventually.of_forall fun n => (hθs_mem n).2⟩
    have h2 : Tendsto (fun n : ℕ => (n:ℝ) + 2) atTop atTop :=
      tendsto_atTop_add_const_right atTop (f := fun n : ℕ => (n:ℝ)) 2
        tendsto_natCast_atTop_atTop
    have hinv : Tendsto (fun n : ℕ => ((n:ℝ)+2)⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp h2
    have h3 := (tendsto_const_nhds (x := Real.pi/2)).sub hinv
    simpa [θs, one_div, sub_zero] using h3
  let g : ℕ → ℝ → ℝ := fun n z => (Set.Ioi (0:ℝ)).indicator (fun z' => f z' (θs n)) z
  have hg_meas : ∀ n : ℕ, Measurable (g n) := fun n =>
    measurable_indicator_Ioi_of_continuousOn ((hso.curry_z (hθs_mem n)).continuousOn)
  let lam : ℝ → ℝ := fun z => Filter.liminf (fun n => g n z) atTop
  have hlam_meas : Measurable lam := Measurable.liminf hg_meas
  have hlam_eq : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))),
      ∀ mu : ℝ, Filter.Tendsto (fun θ => f z θ)
        (nhdsWithin (Real.pi/2) (Set.Iio (Real.pi/2))) (nhds mu) → lam z = mu := by
    filter_upwards [haepos] with z hz mu hmu
    have hseq : Filter.Tendsto (fun n : ℕ => f z (θs n)) atTop (nhds mu) := hmu.comp hθs_tend
    have hcongr : (fun n : ℕ => g n z) = fun n : ℕ => f z (θs n) := by
      funext n
      simp only [g, Set.indicator_of_mem (Set.mem_Ioi.mpr hz)]
    have h1 : lam z = Filter.liminf (fun n : ℕ => f z (θs n)) atTop := by
      simp only [lam]
      rw [hcongr]
    rw [h1, hseq.liminf_eq]
  have htrace_ae : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))),
      Filter.Tendsto (fun θ => f z θ)
        (nhdsWithin (Real.pi/2) (Set.Iio (Real.pi/2))) (nhds (lam z)) := by
    filter_upwards [hgood, hlam_eq] with z hg1 hg2
    obtain ⟨mu, hmu, -⟩ := hg1
    rw [hg2 mu hmu]
    exact hmu
  have hbd_ae : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))),
      ∀ θ ∈ Set.Ioo (Real.pi/4) (Real.pi/2),
        (f z θ - lam z)^2 ≤ 100/(Work.Spaces.gam α - 1)
          * (Real.sin (2*θ))^(Work.Spaces.gam α - 1)
          * (∫ σ in Work.Spaces.Iθ,
              (Real.sin (2*σ))^(2 - Work.Spaces.gam α) * (Work.Spaces.pth f z σ)^2) := by
    filter_upwards [hgood, hlam_eq] with z hg1 hg2 θ hθ
    obtain ⟨mu, hmu, hbd, -⟩ := hg1
    rw [hg2 mu hmu]
    exact hbd θ hθ
  -- (5) the pointwise `L²` bound on the limit
  have hpoint : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))),
      (lam z)^2 * (Work.Spaces.w z)^2
        ≤ (200/(Work.Spaces.gam α - 1)) * S z + (8/Real.pi) * T z := by
    filter_upwards [hgood, hlam_eq, haepos] with z hg1 hg2 hz
    obtain ⟨mu, hmu, -, hsq⟩ := hg1
    rw [hg2 mu hmu]
    have hAeq : A z * (Work.Spaces.w z)^2 = S z := by
      have h := Work.FTS.StrongEps.EpsSqTools.slot_slice_eq (α := α) (z := z) hα0 hα1 f
      simp only [S, A]
      rw [h]; ring
    have hKeq : Kmaj z * (Work.Spaces.w z)^2 = T z := by
      have h := integral_etaSlot_eq (f := f) (z := z) hz
      simp only [T, Kmaj]
      rw [h]; ring
    calc mu^2 * (Work.Spaces.w z)^2
        ≤ (200/(Work.Spaces.gam α - 1) * A z + 8/Real.pi * Kmaj z)
            * (Work.Spaces.w z)^2 := mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
      _ = (200/(Work.Spaces.gam α - 1)) * (A z * (Work.Spaces.w z)^2)
            + (8/Real.pi) * (Kmaj z * (Work.Spaces.w z)^2) := by ring
      _ = (200/(Work.Spaces.gam α - 1)) * S z + (8/Real.pi) * T z := by rw [hAeq, hKeq]
  -- (6) integrability of the majorants and of `z ↦ lam z / z`
  have hmaj : MeasureTheory.Integrable
      (fun z : ℝ => (200/(Work.Spaces.gam α - 1)) * S z + (8/Real.pi) * T z)
      (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))) := by
    rw [hIz]
    exact (hSint.const_mul (200/(Work.Spaces.gam α - 1))).add
      (hTint.const_mul (8/Real.pi))
  have hsqint : MeasureTheory.Integrable (fun z : ℝ => (lam z * Work.Spaces.w z)^2)
      (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))) := by
    refine MeasureTheory.Integrable.mono' hmaj ?_ ?_
    · have hmeas : Measurable (fun z : ℝ => (lam z * Work.Spaces.w z)^2) := by
        have hw : Measurable (fun z : ℝ => Work.Spaces.w z) := by
          simp only [Work.Spaces.w]; fun_prop
        exact (hlam_meas.mul hw).pow_const 2
      exact hmeas.aestronglyMeasurable
    · filter_upwards [hpoint] with z hz
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      simpa only [mul_pow] using hz
  have hInt2 : MeasureTheory.Integrable (fun z : ℝ => (z/(1+z)^2)^2)
      (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))) := integrableOn_sq_div_one_add_sq
  have hzdiv : MeasureTheory.Integrable (fun z : ℝ => lam z / z)
      (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))) := by
    refine MeasureTheory.Integrable.mono' ((hsqint.add hInt2).const_mul ((1:ℝ)/2)) ?_ ?_
    · exact (hlam_meas.div measurable_id).aestronglyMeasurable
    · filter_upwards [haepos] with z hz
      have hw : 0 < Work.Spaces.w z := by rw [Work.Spaces.w]; positivity
      have h1 : lam z / z = lam z * Work.Spaces.w z * (z / (1+z)^2) := by
        rw [Work.Spaces.w]
        field_simp
      have h3 : |lam z| * Work.Spaces.w z = |lam z * Work.Spaces.w z| := by
        rw [abs_mul, abs_of_pos hw]
      have hb : (0:ℝ) ≤ z / (1+z)^2 := by positivity
      rw [Real.norm_eq_abs, h1, abs_mul, abs_mul, abs_of_pos hw, abs_of_nonneg hb, h3]
      show |lam z * Work.Spaces.w z| * (z/(1+z)^2)
          ≤ (1/2 : ℝ) * ((lam z * Work.Spaces.w z)^2 + (z/(1+z)^2)^2)
      have h5 := two_mul_le_add_sq |lam z * Work.Spaces.w z| (z/(1+z)^2)
      have h6 : (|lam z * Work.Spaces.w z|)^2 = (lam z * Work.Spaces.w z)^2 := sq_abs _
      linarith [h5, h6]
  -- (7) the conclusion
  refine ⟨lam, hlam_meas, htrace_ae, hbd_ae, ?_⟩
  have hcomp := (integrable_comp_exp (fun z : ℝ => lam z / z)).mpr hzdiv
  refine hcomp.congr (Filter.Eventually.of_forall fun u => ?_)
  simp only [smul_eq_mul]
  rw [mul_div_cancel₀ (lam (Real.exp u)) (Real.exp_ne_zero u)]

end Main

end Work.FTS.StrongEps.EpsLocalPStar
