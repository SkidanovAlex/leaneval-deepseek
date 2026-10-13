import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6Aux.Defs
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.SlotT2.Basic
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.slotEnergy6
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.hardSlotSliceSixZero
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.Asm
import Submission.Work.FTS.StrongPersist.N6Trans.T1Hon.Defs
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.Npair6Aux

open Work.FTS.TransportS.SlotT2 (canonW canonW_nonneg canonW_zero_z canonW_gam_eq)

set_option maxHeartbeats 1600000

/-! ## Helpers for `zeroTerm` -/

/-- `SmoothOpen` gives continuity on the open quadrant. -/
theorem smoothOpen_continuousOn_Q0 {F : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.SmoothOpen F) :
    ContinuousOn (Function.uncurry F) (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
  (h.forall 0).continuousOn

/-- The two angular endpoints of `Iθ` are null, so `θ ∈ (0, π/2)` almost everywhere. -/
theorem ae_Iθ_mem_Ioo :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  have hθ : Work.Spaces.Iθ =ᵐ[MeasureTheory.volume] Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
      (b := Real.pi / 2)).symm
  rw [MeasureTheory.Measure.restrict_congr_set hθ]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

/-- A `canonW q`-weighted mixed slot of order `a + b ≤ k` with `1 ≤ a` and `q ≤ γ` is dominated
by the `ℋ^k`-integrand, on the open angular interval. -/
theorem canonW_mul_mixed_le_hk (α q : ℝ) (k : ℕ) (g : ℝ → ℝ → ℝ) (a b : ℕ)
    (hqγ : q ≤ Work.Spaces.gam α) (ha : 1 ≤ a) (hab : a + b ≤ k) {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    canonW q z θ * (Work.Spaces.mixed b a g z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α k g z θ := by
  have hmono : canonW q z θ ≤ canonW (Work.Spaces.gam α) z θ :=
    Work.FTS.StrongPersist.N6Trans.SixAux.canonW_mono_open hqγ hθ
  have hWt : canonW (Work.Spaces.gam α) z θ = (Work.Spaces.Wt α z θ) ^ 2 :=
    canonW_gam_eq α z θ (Set.Ioo_subset_Icc_self hθ)
  calc canonW q z θ * (Work.Spaces.mixed b a g z θ) ^ 2
      ≤ canonW (Work.Spaces.gam α) z θ * (Work.Spaces.mixed b a g z θ) ^ 2 :=
        mul_le_mul_of_nonneg_right hmono (sq_nonneg _)
    _ = (Work.Spaces.mixed b a g z θ * Work.Spaces.Wt α z θ) ^ 2 := by rw [hWt]; ring
    _ ≤ Work.Spaces.HkIntegrand α k g z θ :=
        Work.Spaces.sq_le_HkIntegrand_mixed α k g z θ a b ha hab

/-- **The pointwise domination of the `zeroTerm` integrand** on the open quadrant:
`|canonW q · A · D_θ(mixed b a f) · mixed b a f|` is at most `(K0/2)` times the sum of the
level-`7` and the level-`6` integrands. -/
theorem zeroTerm_integrand_le (α q : ℝ) {A f : ℝ → ℝ → ℝ} {K0 : ℝ} {a b : ℕ}
    (hK0 : 0 ≤ K0) (hqγ : q ≤ Work.Spaces.gam α) (hqη : a = 0 → q ≤ Work.Spaces.eta)
    (hab : a + b ≤ 6)
    (hval : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |A z θ| ≤ K0)
    (hfsm : Work.FTS.EllipticEst.SmoothOpen f)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    |canonW q z θ * A z θ * Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ
        * Work.Spaces.mixed b a f z θ|
      ≤ (K0 / 2) * (Work.Spaces.HkIntegrand α 7 f z θ
          + Work.Spaces.HkIntegrand α 6 f z θ) := by
  have hIθ : θ ∈ Work.Spaces.Iθ := Set.Ioo_subset_Icc_self hθ
  have hcw : 0 ≤ canonW q z θ := canonW_nonneg hIθ
  have hW2 : canonW q z θ * (Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 7 f z θ := by
    rw [Work.FTS.StrongPersist.N6Trans.T1Hon.Dth_mixed_eq hfsm b a hz hθ]
    exact canonW_mul_mixed_le_hk α q 7 f (a + 1) b hqγ (by omega) (by omega) hθ
  have hZ2 : canonW q z θ * (Work.Spaces.mixed b a f z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
    Work.FTS.StrongPersist.N6Trans.SixAux.canonW_mixed_le6_open α q f a b hqγ hqη hab hθ
  have hA : |A z θ| ≤ K0 := hval z θ hz hθ.1 hθ.2
  have hAM : 2 * |Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ|
        * |Work.Spaces.mixed b a f z θ|
      ≤ (Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ) ^ 2
        + (Work.Spaces.mixed b a f z θ) ^ 2 := by
    have h := two_mul_le_add_sq |Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ|
      |Work.Spaces.mixed b a f z θ|
    rw [sq_abs, sq_abs] at h
    exact h
  have hstep : 2 * (canonW q z θ * |Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ|
        * |Work.Spaces.mixed b a f z θ|)
      ≤ canonW q z θ * (Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ) ^ 2
        + canonW q z θ * (Work.Spaces.mixed b a f z θ) ^ 2 := by
    nlinarith [hAM, hcw]
  calc |canonW q z θ * A z θ * Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ
          * Work.Spaces.mixed b a f z θ|
      = canonW q z θ * |A z θ| * |Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ|
          * |Work.Spaces.mixed b a f z θ| := by
        simp only [abs_mul, abs_of_nonneg hcw]
    _ ≤ canonW q z θ * K0 * |Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ|
          * |Work.Spaces.mixed b a f z θ| := by
        refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
        refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
        exact mul_le_mul_of_nonneg_left hA hcw
    _ = (K0 / 2) * (2 * (canonW q z θ * |Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ|
          * |Work.Spaces.mixed b a f z θ|)) := by ring
    _ ≤ (K0 / 2) * (canonW q z θ * (Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ) ^ 2
          + canonW q z θ * (Work.Spaces.mixed b a f z θ) ^ 2) :=
        mul_le_mul_of_nonneg_left hstep (by linarith)
    _ ≤ (K0 / 2) * (Work.Spaces.HkIntegrand α 7 f z θ + Work.Spaces.HkIntegrand α 6 f z θ) :=
        mul_le_mul_of_nonneg_left (add_le_add hW2 hZ2) (by linarith)

/-- **The three conjuncts of `zeroTerm` for a single canonical weight `canonW q`.**  The constant
`C` and its slice-level hypothesis `hC` are the two components of
`Work.FTS.StrongPersist.N6Trans.T1SixAux.hardSlotSliceSixZero` (with the existential opened);
everything else is proved here. -/
theorem zeroTerm_canon {C : ℝ} (hCpos : 0 < C)
    (hC : ∀ (q Kf z : ℝ) (F Y : ℝ → ℝ → ℝ),
      0 ≤ q → q ≤ 2 → 0 ≤ Kf → z ∈ Work.Spaces.Iz →
      Work.FTS.EllipticEst.SmoothOpen F → Work.FTS.EllipticEst.SmoothOpen Y →
      (∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 → |F z θ| ≤ Kf) →
      (∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 → |Work.Spaces.Dth F z θ| ≤ Kf) →
      MeasureTheory.IntegrableOn (fun θ : ℝ => canonW q z θ * (Y z θ) ^ 2) Work.Spaces.Iθ →
      |∫ θ in Work.Spaces.Iθ, canonW q z θ * F z θ * Work.Spaces.Dth Y z θ * Y z θ|
        ≤ C * Kf * ∫ θ in Work.Spaces.Iθ, canonW q z θ * (Y z θ) ^ 2)
    (α : ℝ) {A f : ℝ → ℝ → ℝ} {K0 : ℝ} {a b : ℕ} {q : ℝ}
    (hsmA : Work.FTS.EllipticEst.SmoothOpen A) (hK0 : 0 ≤ K0)
    (hval : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |A z θ| ≤ K0)
    (hdb : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |Work.Spaces.Dth A z θ| ≤ K0)
    (hfsm : Work.FTS.EllipticEst.SmoothOpen f)
    (hf6 : Work.Spaces.HkMem α 6 f) (hf7 : Work.Spaces.HkMem α 7 f)
    (hab : a + b ≤ 6) (hq0 : 0 ≤ q) (hq2 : q ≤ 2)
    (hqγ : q ≤ Work.Spaces.gam α) (hqη : a = 0 → q ≤ Work.Spaces.eta) :
    (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ : ℝ => canonW q z θ * A z θ
        * Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ * Work.Spaces.mixed b a f z θ)
        Work.Spaces.Iθ) ∧
      MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, canonW q z θ * A z θ
        * Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ * Work.Spaces.mixed b a f z θ)
        Work.Spaces.Iz ∧
      |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, canonW q z θ * A z θ
        * Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ * Work.Spaces.mixed b a f z θ|
      ≤ C * K0 * Work.Spaces.HkSq α 6 f := by
  have hZsm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.mixed b a f) := hfsm.mixed b a
  have hWsm : Work.FTS.EllipticEst.SmoothOpen
      (Work.Spaces.Dth (Work.Spaces.mixed b a f)) := hZsm.Dth
  have hsl : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ : ℝ =>
      canonW q z θ * (Work.Spaces.mixed b a f z θ) ^ 2) Work.Spaces.Iθ :=
    fun z hz => Work.FTS.StrongPersist.N6Trans.T1SixAux.slotSliceIntegrable α q hfsm hf6
      hqγ hqη hab hz
  obtain ⟨henergyI, henergyB⟩ :=
    Work.FTS.StrongPersist.N6Trans.T1SixAux.slotEnergyZOuter α q hfsm hf6 hq0 hqγ hqη hab
  -- the slice-level bound, valid at every `z ∈ Iz` (trivially at `z = 0`)
  have hslice : ∀ z ∈ Work.Spaces.Iz,
      |∫ θ in Work.Spaces.Iθ, canonW q z θ * A z θ
          * Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ * Work.Spaces.mixed b a f z θ|
        ≤ C * K0 * ∫ θ in Work.Spaces.Iθ,
            canonW q z θ * (Work.Spaces.mixed b a f z θ) ^ 2 := by
    intro z hz
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
    · subst hz0
      have h1 : (∫ θ in Work.Spaces.Iθ, canonW q 0 θ * A 0 θ
          * Work.Spaces.Dth (Work.Spaces.mixed b a f) 0 θ
          * Work.Spaces.mixed b a f 0 θ) = 0 := by
        rw [show (fun θ : ℝ => canonW q 0 θ * A 0 θ
            * Work.Spaces.Dth (Work.Spaces.mixed b a f) 0 θ
            * Work.Spaces.mixed b a f 0 θ) = fun _ => (0 : ℝ) from
          funext fun θ => by simp [canonW_zero_z], MeasureTheory.integral_zero]
      have h2 : (∫ θ in Work.Spaces.Iθ,
          canonW q 0 θ * (Work.Spaces.mixed b a f 0 θ) ^ 2) = 0 := by
        rw [show (fun θ : ℝ => canonW q 0 θ * (Work.Spaces.mixed b a f 0 θ) ^ 2)
            = fun _ => (0 : ℝ) from funext fun θ => by simp [canonW_zero_z],
          MeasureTheory.integral_zero]
      rw [h1, h2, abs_zero, mul_zero]
    · exact hC q K0 z A (Work.Spaces.mixed b a f) hq0 hq2 hK0 hz hsmA hZsm
        (fun θ hθ hθ2 => hval z θ hzpos hθ hθ2)
        (fun θ hθ hθ2 => hdb z θ hzpos hθ hθ2) (hsl z hz)
  refine ⟨?_, ?_, ?_⟩
  · -- first conjunct: `θ`-slice integrability of the integrand
    intro z hz
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
    · subst hz0
      rw [show (fun θ : ℝ => canonW q 0 θ * A 0 θ
          * Work.Spaces.Dth (Work.Spaces.mixed b a f) 0 θ
          * Work.Spaces.mixed b a f 0 θ) = fun _ => (0 : ℝ) from
        funext fun θ => by simp [canonW_zero_z]]
      exact integrableOn_zero
    · have hcont : ContinuousOn (fun p : ℝ × ℝ => canonW q p.1 p.2 * A p.1 p.2
            * Work.Spaces.Dth (Work.Spaces.mixed b a f) p.1 p.2
            * Work.Spaces.mixed b a f p.1 p.2)
            (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
        ((Work.FTS.TransportS.SlotT2.continuousOn_canonW q).mul
          (smoothOpen_continuousOn_Q0 hsmA)).mul
          (smoothOpen_continuousOn_Q0 hWsm) |>.mul (smoothOpen_continuousOn_Q0 hZsm)
      refine MeasureTheory.Integrable.mono'
        (((hf7.1 z hz).add (hf6.1 z hz)).const_mul (K0 / 2))
        (Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcont hzpos) ?_
      filter_upwards [ae_Iθ_mem_Ioo] with θ hθ
      rw [Real.norm_eq_abs]
      exact zeroTerm_integrand_le α q hK0 hqγ hqη hab hval hfsm hzpos hθ
  · -- second conjunct: integrability of the marginal
    have hcont : ContinuousOn (fun p : ℝ × ℝ => canonW q p.1 p.2 * A p.1 p.2
          * Work.Spaces.Dth (Work.Spaces.mixed b a f) p.1 p.2
          * Work.Spaces.mixed b a f p.1 p.2)
          (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      ((Work.FTS.TransportS.SlotT2.continuousOn_canonW q).mul
        (smoothOpen_continuousOn_Q0 hsmA)).mul
        (smoothOpen_continuousOn_Q0 hWsm) |>.mul (smoothOpen_continuousOn_Q0 hZsm)
    refine MeasureTheory.Integrable.mono' (henergyI.const_mul (C * K0))
      (Work.Spaces.aesm_of_continuousOn_Qd _ hcont).integral_prod_right' ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => ?_
    rw [Real.norm_eq_abs]
    exact hslice z hz
  · -- third conjunct: the bound
    calc |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, canonW q z θ * A z θ
            * Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ * Work.Spaces.mixed b a f z θ|
        ≤ ∫ z in Work.Spaces.Iz, |∫ θ in Work.Spaces.Iθ, canonW q z θ * A z θ
            * Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ
            * Work.Spaces.mixed b a f z θ| :=
          MeasureTheory.abs_integral_le_integral_abs
      _ ≤ ∫ z in Work.Spaces.Iz, (C * K0) * (∫ θ in Work.Spaces.Iθ,
            canonW q z θ * (Work.Spaces.mixed b a f z θ) ^ 2) := by
          refine MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall (fun z => abs_nonneg _))
            (henergyI.const_mul (C * K0)) ?_
          exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici
            (fun z hz => hslice z hz)
      _ = (C * K0) * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            canonW q z θ * (Work.Spaces.mixed b a f z θ) ^ 2) :=
          MeasureTheory.integral_const_mul (C * K0) _
      _ ≤ (C * K0) * Work.Spaces.HkSq α 6 f :=
          mul_le_mul_of_nonneg_left henergyB (mul_nonneg hCpos.le hK0)

/-- ## Route (all listed ingredients are already proved in this workspace)

Let `Z := mixed b a f`, so `Dth Z = mixed b (a+1) f`.  The bound is the θ-transport estimate:
use the proved slice-level lemma `Work.FTS.StrongPersist.N6Trans.T1SixAux.hardSlotSliceSixZero`
with `q := qρ` (the exponent of the leaf weight, `ρ = canonW qρ`, `0 ≤ qρ ≤ 2`) and `Kf := K0`,
applied at every `z ∈ Iz`: it gives
`|∫_θ canonW qρ z θ * A z θ * Dth Z z θ * Z z θ| ≤ (3/2) K0 ∫_θ canonW qρ z θ * (Z z θ)²`,
its hypotheses being `0 ≤ K0`, the two pointwise bounds `|A| ≤ K0`, `|Dth A| ≤ K0`, `SmoothOpen A`,
`SmoothOpen Z` (from `DatHyp.sm` and `α ≤ 1`) and the θ-slice integrability of
`canonW qρ z · * (Z z ·)²` — which is `T1SixAux.slotSliceIntegrable` (`a ≥ 1`) resp.
`SlotT2.zslot_slice_integrable` (`a = 0`, `qρ ∈ {η,0}`), from `DatHyp.h6`.

Then `|∫_z ∫_θ ...| ≤ ∫_z |∫_θ ...| ≤ (3/2) K0 ∫_z ∫_θ canonW qρ z θ (Z z θ)²`
(`MeasureTheory.abs_integral_le_integral_abs` on the integrable marginal, then
`MeasureTheory.integral_mono_of_nonneg`), and the last quantity is `≤ (3/2) K0 HkSq α 6 f` by
`T1SixAux.energy_mixed6` (`a ≥ 1`) resp. `T1SixAux.energy_z6` (`a = 0`, weight `≤ η`).

For the integrability conjuncts: pointwise on the open quadrant
`ρ|A||Dth Z||Z| ≤ K0 (ρ|Dth Z|² + ρ|Z|²)/2`; `ρ|Z|² ≤ HkIntegrand α 6 f` and, since `a + b ≤ 6`,
`ρ|Dth Z|² ≤ HkIntegrand α 7 f` (`Z7 := Dth Z = mixed b (a+1) f` has order `≤ 7`, angular `≥ 1`
when `a ≥ 1`; when `a = 0` use the pure slot with the `η` weight and `HkIntegrand α 7 f` — note
`DatHyp.h7` is present exactly for this).  Hence both conjuncts follow with
`MeasureTheory.Integrable.mono'` and `DatHyp.h6`, `DatHyp.h7`. -/
theorem zeroTerm : ∃ C : ℝ, 0 < C ∧
    ∀ α ∈ Set.Ioc 0 1, ∀ (A f : Work.FTS.Galerkin.Fn) (K0 M : ℝ) (a b : ℕ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.SmoothOpen A → 0 ≤ K0 →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |A z θ| ≤ K0) →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |Work.Spaces.Dth A z θ| ≤ K0) →
      Work.FTS.StrongPersist.H6Rows.Npair6Aux.DatHyp α f M → a + b ≤ 6 →
      Work.FTS.TransportS.IsLeafW α a ρ →
      (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ : ℝ => ρ z θ * A z θ
          * Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ * Work.Spaces.mixed b a f z θ)
          Work.Spaces.Iθ) ∧
      MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, ρ z θ * A z θ
          * Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ * Work.Spaces.mixed b a f z θ)
          Work.Spaces.Iz ∧
      |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ * A z θ
          * Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ * Work.Spaces.mixed b a f z θ|
        ≤ C * K0 * Work.Spaces.HkSq α 6 f := by
  obtain ⟨C6, hC6pos, hC6⟩ := Work.FTS.StrongPersist.N6Trans.T1SixAux.hardSlotSliceSixZero
  refine ⟨C6, hC6pos, ?_⟩
  intro α hαmem A f K0 M a b ρ hsmA hK0 hval hdb hdat hab hleaf
  obtain ⟨hα, hα1⟩ := hαmem
  obtain ⟨hfsm, hf6, hf7, -, -, -⟩ := hdat
  rcases hleaf with hρ | hρ | ⟨ha1, hρ⟩
  · -- `ρ = leafEta = canonW η`
    rw [hρ]
    exact zeroTerm_canon hC6pos hC6 α hsmA hK0 hval hdb hfsm hf6 hf7 hab
      (q := Work.Spaces.eta) (by norm_num [Work.Spaces.eta]) (by norm_num [Work.Spaces.eta])
      (by rw [Work.Spaces.gam, Work.Spaces.eta]; linarith)
      (fun _ => by norm_num [Work.Spaces.eta])
  · -- `ρ = leafOne = canonW 0`
    rw [hρ]
    rw [show Work.FTS.TransportS.leafOne = canonW 0 from by
      funext z θ
      simp only [Work.FTS.TransportS.leafOne, canonW, neg_zero, Real.rpow_zero, mul_one]]
    exact zeroTerm_canon hC6pos hC6 α hsmA hK0 hval hdb hfsm hf6 hf7 hab
      (q := 0) (by norm_num) (by norm_num) (by rw [Work.Spaces.gam]; linarith)
      (fun _ => by norm_num [Work.Spaces.eta])
  · -- `ρ = leafGam α = canonW γ`, with `1 ≤ a`
    rw [hρ]
    exact zeroTerm_canon hC6pos hC6 α hsmA hK0 hval hdb hfsm hf6 hf7 hab
      (q := Work.Spaces.gam α) (by rw [Work.Spaces.gam]; linarith)
      (by rw [Work.Spaces.gam]; linarith) (le_refl _) (fun _ => False.elim (by omega))

end Work.FTS.StrongPersist.H6Rows.Npair6Aux
