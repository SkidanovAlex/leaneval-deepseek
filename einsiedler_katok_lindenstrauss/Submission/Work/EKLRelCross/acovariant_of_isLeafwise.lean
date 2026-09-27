import Mathlib
import Submission.Work.EKLContract.All
import Submission.Work.EKLRelCross.Instances
import Submission.Work.EKLRelCross.LeafBasic
import Submission.Work.EKLRelCross.acovPerTAux
import Submission.Work.EKLRelCross.covariance_bad_measurable

/-!
# `Work.EKLRelCross.acovariant_of_isLeafwise` — (U7) of the frozen EKL contract

The `A`-covariance of a system of leafwise measures (EKL (4), Pisa 7.16), the second half of the
frozen contract `P_Leafwise`.

For every fixed `t`, the covariance
`ν (aDiag t • x) ∝ (ν x).map (g ↦ aDiag t * g * (aDiag t)⁻¹)` holds for `μ`-a.e. `x`
(`Work.EKLRelCross.per_t_covariance`, the flower / Pisa 7.17 argument).

This file produces a **single** conull set on which the covariance holds for *all* `t` at once.
The two algebraic properties of the pointwise relation `CovPt` are

* `CovPt ν t x ↔ CovPt ν (-t) (aDiag t • x)`  (symmetry), and
* `CovPt ν s y → CovPt ν h (aDiag s • y) → CovPt ν (s + h) y`  (the cocycle identity),

hence `CovPt ν s y → ¬ CovPt ν t x → ¬ CovPt ν (s + t) x` and
`(fun s => t + s) '' {s | CovPt ν s (aDiag t • x)} ⊆ {s | ¬ CovPt ν s x}`.

So if `x` and `aDiag t • x` both lie in the conull set
`A = {x | volume {s | (x,s) ∈ Bad} = 0}`, where `Bad` is the measurable bad set of
`Work.EKLRelCross.covariance_bad_measurable`, then the complement of the bad slice at
`aDiag t • x` — of infinite Lebesgue measure — is transported into the bad slice at `x`, so the
latter has measure `⊤`; but it has measure `0` because `x ∈ A`.  Contradiction.

The "for a.e. `x`, `volume (BadSlice x) = 0`" input is Tonelli applied to the measurable set
`Bad` (measurability: `Work.EKLRelCross.covariance_bad_measurable`).
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open Work.EKLContract

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

noncomputable section

namespace Work.EKLRelCross

/-! ## The pointwise covariance relation and its algebra -/

/-- The conjugation map `g ↦ aDiag t * g * (aDiag t)⁻¹` is measurable. -/
theorem measurable_conjF (t : Fin 3 → ℝ) :
    Measurable (fun g : SL3 => aDiag t * g * (aDiag t)⁻¹) :=
  ((continuous_const.mul continuous_id).mul continuous_const).measurable

/-- `CovPt` holds at `t = 0`. -/
theorem covPt_zero (ν : X3 → Measure SL3) (x : X3) : CovPt ν 0 x := by
  refine ⟨1, one_ne_zero, ENNReal.one_ne_top, ?_⟩
  show ν (aDiag 0 • x) = 1 • Measure.map (fun g : SL3 => aDiag 0 * g * (aDiag 0)⁻¹) (ν x)
  rw [aDiag_zero]
  simp

/-- **Symmetry of the pointwise covariance.** -/
theorem covPt_neg (ν : X3 → Measure SL3) {t : Fin 3 → ℝ} {x : X3} (h : CovPt ν t x) :
    CovPt ν (-t) (aDiag t • x) := by
  obtain ⟨c, hc0, hct, hc⟩ := h
  refine ⟨c⁻¹, ENNReal.inv_ne_zero.mpr hct, ENNReal.inv_ne_top.mpr hc0, ?_⟩
  show ν (aDiag (-t) • (aDiag t • x))
    = c⁻¹ • Measure.map (fun g : SL3 => aDiag (-t) * g * (aDiag (-t))⁻¹) (ν (aDiag t • x))
  rw [aDiag_neg_smul]
  have h2 : Measure.map (fun g : SL3 => aDiag (-t) * g * (aDiag (-t))⁻¹) (ν (aDiag t • x))
      = c • ν x := by
    rw [hc, Measure.map_smul,
      Measure.map_map (measurable_conjF (-t)) (measurable_conjF t), conjFun_add] <;> try fun_prop
    have hzero : (-t + t : Fin 3 → ℝ) = 0 := by funext i; simp
    rw [hzero, aDiag_zero]
    simp
  rw [h2, smul_smul, ENNReal.inv_mul_cancel hc0 hct, one_smul]

/-- **Symmetry of the pointwise covariance** (converse direction). -/
theorem covPt_neg' (ν : X3 → Measure SL3) {t : Fin 3 → ℝ} {x : X3}
    (h : CovPt ν (-t) (aDiag t • x)) : CovPt ν t x := by
  obtain ⟨c, hc0, hct, hc⟩ := h
  refine ⟨c⁻¹, ENNReal.inv_ne_zero.mpr hct, ENNReal.inv_ne_top.mpr hc0, ?_⟩
  show ν (aDiag t • x) = c⁻¹ • Measure.map (fun g : SL3 => aDiag t * g * (aDiag t)⁻¹) (ν x)
  have h1 : aDiag (-t) • (aDiag t • x) = x := aDiag_neg_smul t x
  rw [h1] at hc
  have h2 : Measure.map (fun g : SL3 => aDiag t * g * (aDiag t)⁻¹) (ν x)
      = c • ν (aDiag t • x) := by
    rw [hc, Measure.map_smul,
      Measure.map_map (measurable_conjF t) (measurable_conjF (-t)), conjFun_add] <;> try fun_prop
    have hzero : (t + -t : Fin 3 → ℝ) = 0 := by funext i; simp
    rw [hzero, aDiag_zero]
    simp
  rw [h2, smul_smul, ENNReal.inv_mul_cancel hc0 hct, one_smul]

/-- **The cocycle identity**: covariance at `(y,s)` and at `(aDiag s • y, h)` gives covariance at
`(y, s+h)`. -/
theorem covPt_add (ν : X3 → Measure SL3) {s h : Fin 3 → ℝ} {y : X3}
    (hs : CovPt ν s y) (hh : CovPt ν h (aDiag s • y)) : CovPt ν (s + h) y := by
  obtain ⟨c₁, hc₁0, hc₁t, hc₁⟩ := hs
  obtain ⟨c₂, hc₂0, hc₂t, hc₂⟩ := hh
  refine ⟨c₂ * c₁, mul_ne_zero hc₂0 hc₁0, ENNReal.mul_ne_top hc₂t hc₁t, ?_⟩
  show ν (aDiag (s + h) • y)
    = (c₂ * c₁) • Measure.map (fun g : SL3 => aDiag (s + h) * g * (aDiag (s + h))⁻¹) (ν y)
  have hstep : aDiag h • (aDiag s • y) = aDiag (s + h) • y := by
    rw [aDiag_smul_mul,
      show (h + s : Fin 3 → ℝ) = s + h from by funext i; simp [add_comm]]
  rw [← hstep, hc₂, hc₁, Measure.map_smul,
    Measure.map_map (measurable_conjF h) (measurable_conjF s), conjFun_add] <;> try fun_prop
  rw [show (h + s : Fin 3 → ℝ) = s + h from by funext i; simp [add_comm]]
  rw [smul_smul]

/-- **Contrapositive of the cocycle identity.** -/
theorem covPt_shift (ν : X3 → Measure SL3) {s h : Fin 3 → ℝ} {y : X3}
    (hs : CovPt ν s y) (hbad : ¬ CovPt ν (s + h) y) : ¬ CovPt ν h (aDiag s • y) :=
  fun hh => hbad (covPt_add ν hs hh)

/-! ## The Lebesgue measure of `Fin 3 → ℝ` -/

/-- The Lebesgue measure of `Fin 3 → ℝ` is infinite. -/
theorem volume_univ_fin3 : (volume : Measure (Fin 3 → ℝ)) Set.univ = ⊤ := by
  rw [MeasureTheory.volume_pi, MeasureTheory.Measure.pi_univ]
  simp [Real.volume_univ]

/-- The Lebesgue measure of `Fin 3 → ℝ` is translation invariant. -/
theorem volume_image_add (t : Fin 3 → ℝ) (S : Set (Fin 3 → ℝ)) :
    volume ((fun s : Fin 3 → ℝ => s + t) '' S) = volume S := by
  have h : (fun x : Fin 3 → ℝ => x + -t) ⁻¹' S = (fun s : Fin 3 → ℝ => s + t) '' S := by
    ext x
    constructor
    · intro hx
      refine ⟨x + -t, hx, ?_⟩
      abel
    · rintro ⟨g, hg, rfl⟩
      show (g + t) + -t ∈ S
      rwa [show (g + t) + -t = g from by abel]
  rw [← h]
  simp

/-! ## The main theorem -/

/-- **(U7)** The `A`-covariance of a leafwise system (EKL (4), Pisa 7.16). -/
theorem acovariant_of_isLeafwise (h2 : Work.EKLContract.P_X3) (μ : MeasureTheory.Measure Work.EKLContract.X3) [MeasureTheory.IsProbabilityMeasure μ]
    (U : Subgroup Work.EKLContract.SL3) (hU : Work.EKLContract.IsHoro U) (t0 : Fin 3 → ℝ)
    (ht0 : MeasureTheory.MeasurePreserving (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t0 • x) μ μ)
    (hcontr : ∀ u ∈ U, Filter.Tendsto (fun n : ℕ => Work.EKLContract.aDiag t0 ^ n * u * (Work.EKLContract.aDiag t0 ^ n)⁻¹) Filter.atTop (nhds 1))
    (ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3) (X' : Set Work.EKLContract.X3) (hL : Work.EKLContract.IsLeafwise μ U ν X') :
    Work.EKLContract.IsAInvariant μ → ∃ X'' ⊆ X', MeasurableSet X'' ∧ μ X''ᶜ = 0 ∧
        ∀ (t : Fin 3 → ℝ) (x : Work.EKLContract.X3), x ∈ X'' → Work.EKLContract.aDiag t • x ∈ X'' →
          ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
            ν (Work.EKLContract.aDiag t • x) = c • (ν x).map (fun g => Work.EKLContract.aDiag t * g * (Work.EKLContract.aDiag t)⁻¹) := by
  intro hAinv
  -- ## a.e. free `U`-orbits
  have hfree : ∀ᵐ x ∂μ, ∀ u ∈ U, u • x = x → u = 1 := ae_free_orbit h2 μ U hU t0 ht0 hcontr
  -- ## the good region and the bad set
  let Good : Set (X3 × (Fin 3 → ℝ)) := {p | p.1 ∈ X' ∧ aDiag p.2 • p.1 ∈ X'}
  let Bad : Set (X3 × (Fin 3 → ℝ)) :=
    {p | p.1 ∈ X' ∧ aDiag p.2 • p.1 ∈ X' ∧ ¬ ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
      ν (aDiag p.2 • p.1) = c • (ν p.1).map (fun g : SL3 => aDiag p.2 * g * (aDiag p.2)⁻¹)}
  have hGoodmeas : MeasurableSet Good := by
    refine MeasurableSet.inter ?_ ?_
    · exact hL.meas_dom.preimage measurable_fst
    · exact hL.meas_dom.preimage continuous_aDiag_smul_pair.measurable
  have hBadmeas : MeasurableSet (Goodᶜ ∪ Bad) :=
    hGoodmeas.compl.union (covariance_bad_measurable (U := U) hU hL)
  -- ## the "free at both ends" condition, a.e.
  have hPae : ∀ (t : Fin 3 → ℝ), ∀ᵐ x ∂μ,
      (x ∈ X' ∧ aDiag t • x ∈ X' ∧ (∀ u ∈ U, u • x = x → u = 1) ∧
        (∀ u ∈ U, u • (aDiag t • x) = aDiag t • x → u = 1)) := by
    intro t
    have ht : MeasurePreserving (fun x : X3 => aDiag t • x) μ μ := hAinv t
    filter_upwards [MeasureTheory.ae_iff.mpr hL.conull,
      ht.quasiMeasurePreserving.ae (MeasureTheory.ae_iff.mpr hL.conull),
      hfree, ht.quasiMeasurePreserving.ae hfree] with x hx hx' hf hf'
    exact ⟨hx, hx', hf, hf'⟩
  -- ## covariance holds for every fixed `t` at a.e. `x`
  have hper : ∀ t : Fin 3 → ℝ, μ {x : X3 | ¬ CovPt ν t x} = 0 := by
    intro t
    have hPz : μ {x : X3 | ¬ (x ∈ X' ∧ aDiag t • x ∈ X' ∧
        (∀ u ∈ U, u • x = x → u = 1) ∧
        (∀ u ∈ U, u • (aDiag t • x) = aDiag t • x → u = 1))} = 0 :=
      MeasureTheory.ae_iff.mp (hPae t)
    have hcov := axP_per_t_covariance (U := U) hU hL hAinv hfree t
    have hQz : μ {x : X3 | ¬ ((x ∈ X' ∧ aDiag t • x ∈ X' ∧
        (∀ u ∈ U, u • x = x → u = 1) ∧
        (∀ u ∈ U, u • (aDiag t • x) = aDiag t • x → u = 1)) →
        ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
          ν (aDiag t • x) = c • (ν x).map (fun g : SL3 => aDiag t * g * (aDiag t)⁻¹))} = 0 :=
      MeasureTheory.ae_iff.mp hcov
    have hsub : {x : X3 | ¬ CovPt ν t x} ⊆
        {x : X3 | ¬ ((x ∈ X' ∧ aDiag t • x ∈ X' ∧ (∀ u ∈ U, u • x = x → u = 1) ∧
          (∀ u ∈ U, u • (aDiag t • x) = aDiag t • x → u = 1)) →
          ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
            ν (aDiag t • x) = c • (ν x).map (fun g : SL3 => aDiag t * g * (aDiag t)⁻¹))} ∪
        {x : X3 | ¬ (x ∈ X' ∧ aDiag t • x ∈ X' ∧ (∀ u ∈ U, u • x = x → u = 1) ∧
          (∀ u ∈ U, u • (aDiag t • x) = aDiag t • x → u = 1))} := by
      intro x hx
      by_cases hPx : (x ∈ X' ∧ aDiag t • x ∈ X' ∧ (∀ u ∈ U, u • x = x → u = 1) ∧
          (∀ u ∈ U, u • (aDiag t • x) = aDiag t • x → u = 1))
      · exact Or.inl (fun hcon => hx (hcon hPx))
      · exact Or.inr hPx
    exact measure_mono_null hsub (measure_union_null hQz hPz)
  -- ## the fibers of the bad set are `μ`-null
  have hBadFib : ∀ t : Fin 3 → ℝ, μ {x : X3 | (x, t) ∈ Goodᶜ ∪ Bad} = 0 := by
    intro t
    have hPz : μ {x : X3 | ¬ (x ∈ X' ∧ aDiag t • x ∈ X' ∧
        (∀ u ∈ U, u • x = x → u = 1) ∧
        (∀ u ∈ U, u • (aDiag t • x) = aDiag t • x → u = 1))} = 0 :=
      MeasureTheory.ae_iff.mp (hPae t)
    have hsub : {x : X3 | (x, t) ∈ Goodᶜ ∪ Bad} ⊆
        {x : X3 | ¬ (x ∈ X' ∧ aDiag t • x ∈ X' ∧ (∀ u ∈ U, u • x = x → u = 1) ∧
          (∀ u ∈ U, u • (aDiag t • x) = aDiag t • x → u = 1))} ∪ {x : X3 | ¬ CovPt ν t x} := by
      intro x hx
      rcases hx with hx | hx
      · refine Or.inl fun hP => hx ⟨hP.1, hP.2.1⟩
      · rcases hx with ⟨hxX', hxX, hxnc⟩
        by_cases hPx : (x ∈ X' ∧ aDiag t • x ∈ X' ∧ (∀ u ∈ U, u • x = x → u = 1) ∧
            (∀ u ∈ U, u • (aDiag t • x) = aDiag t • x → u = 1))
        · exact Or.inr fun hcov => hxnc hcov
        · exact Or.inl hPx
    exact measure_mono_null hsub (measure_union_null hPz (hper t))
  -- ## Tonelli: for a.e. `x` the bad slice is Lebesgue-null
  have hprod : (μ.prod volume) (Goodᶜ ∪ Bad) = 0 := by
    rw [Measure.prod_apply_symm hBadmeas]
    have hfib : (fun t : Fin 3 → ℝ => μ ((fun x : X3 => (x, t)) ⁻¹' (Goodᶜ ∪ Bad)))
        = fun _ => (0 : ℝ≥0∞) := by
      funext t
      exact hBadFib t
    rw [hfib]
    simp
  have hmeasVol : Measurable fun x : X3 => volume (Prod.mk x ⁻¹' (Goodᶜ ∪ Bad)) := by
    have huncurry : Function.uncurry (fun (x : X3) (t : Fin 3 → ℝ) =>
        (Prod.mk x ⁻¹' (Goodᶜ ∪ Bad)).indicator (fun _ => (1 : ℝ≥0∞)) t)
        = (Goodᶜ ∪ Bad).indicator (fun _ => (1 : ℝ≥0∞)) := by
      funext p
      rcases p with ⟨x, t⟩
      by_cases hp : (x, t) ∈ Goodᶜ ∪ Bad
      · have hmem : t ∈ Prod.mk x ⁻¹' (Goodᶜ ∪ Bad) := hp
        simp only [Function.uncurry]
        rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hp]
      · have hmem : t ∉ Prod.mk x ⁻¹' (Goodᶜ ∪ Bad) := hp
        simp only [Function.uncurry]
        rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hp]
    have h2 : Measurable (Function.uncurry (fun (x : X3) (t : Fin 3 → ℝ) =>
        (Prod.mk x ⁻¹' (Goodᶜ ∪ Bad)).indicator (fun _ => (1 : ℝ≥0∞)) t)) := by
      rw [huncurry]
      exact Measurable.indicator measurable_const hBadmeas
    have h3 : Measurable fun x : X3 => ∫⁻ t : Fin 3 → ℝ,
        (Prod.mk x ⁻¹' (Goodᶜ ∪ Bad)).indicator (fun _ => (1 : ℝ≥0∞)) t ∂volume :=
      Measurable.lintegral_prod_right h2
    have hfun : (fun x : X3 => ∫⁻ t : Fin 3 → ℝ,
        (Prod.mk x ⁻¹' (Goodᶜ ∪ Bad)).indicator (fun _ => (1 : ℝ≥0∞)) t ∂volume)
        = fun x : X3 => volume (Prod.mk x ⁻¹' (Goodᶜ ∪ Bad)) := by
      funext x
      exact lintegral_indicator_one (hBadmeas.preimage measurable_prodMk_left)
    rwa [hfun] at h3
  have hslice : ∀ᵐ x ∂μ, volume (Prod.mk x ⁻¹' (Goodᶜ ∪ Bad)) = 0 := by
    have h1 : (∫⁻ x : X3, volume (Prod.mk x ⁻¹' (Goodᶜ ∪ Bad)) ∂μ) = 0 := by
      rw [← Measure.prod_apply hBadmeas, hprod]
    exact (MeasureTheory.lintegral_eq_zero_iff hmeasVol).mp h1
  -- ## the conull set on which the covariance holds for all `t`
  refine ⟨X' ∩ {x : X3 | volume (Prod.mk x ⁻¹' (Goodᶜ ∪ Bad)) = 0}, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact hx.1
  · exact hL.meas_dom.inter (hmeasVol (measurableSet_singleton 0))
  · rw [Set.compl_inter]
    exact measure_union_null hL.conull (MeasureTheory.ae_iff.mp hslice)
  · intro t x hx hx'
    by_contra hcon
    have hconCov : ¬ CovPt ν t x := hcon
    have hxX' : x ∈ X' := hx.1
    have hxA : volume (Prod.mk x ⁻¹' (Goodᶜ ∪ Bad)) = 0 := hx.2
    have hyX' : aDiag t • x ∈ X' := hx'.1
    have hyA : volume (Prod.mk (aDiag t • x) ⁻¹' (Goodᶜ ∪ Bad)) = 0 := hx'.2
    -- the true bad set is contained in the bad slice
    have hBsub : ∀ y : X3, {s : Fin 3 → ℝ | ¬ CovPt ν s y} ⊆ Prod.mk y ⁻¹' (Goodᶜ ∪ Bad) := by
      intro y s hs
      by_cases hcases : y ∈ X' ∧ aDiag s • y ∈ X'
      · exact Or.inr ⟨hcases.1, hcases.2, fun hc => hs hc⟩
      · exact Or.inl hcases
    -- the complement of the bad slice lies in the good set
    have hGsub : ∀ y : X3, y ∈ X' →
        (Prod.mk y ⁻¹' (Goodᶜ ∪ Bad))ᶜ ⊆ {s : Fin 3 → ℝ | CovPt ν s y} := by
      intro y hy s hs
      by_contra hcon'
      have hmem : (y, s) ∈ Goodᶜ ∪ Bad := by
        by_cases hcases : aDiag s • y ∈ X'
        · exact Or.inr ⟨hy, hcases, hcon'⟩
        · exact Or.inl fun hg => hcases hg.2
      exact hs hmem
    -- `-t` is bad at `aDiag t • x`
    have hnegt : ¬ CovPt ν (-t) (aDiag t • x) := fun h => hconCov (covPt_neg' ν h)
    -- a good `s` at `aDiag t • x` gives a bad `s + t` at `x`
    have hshift : ∀ s : Fin 3 → ℝ, CovPt ν s (aDiag t • x) → ¬ CovPt ν (s + t) x := by
      intro s hs hgood
      have hbadst : ¬ CovPt ν (s + (-(s + t))) (aDiag t • x) := by
        have heq : (s + (-(s + t)) : Fin 3 → ℝ) = -t := by
          funext i
          simp only [Pi.add_apply, Pi.neg_apply]
          ring
        rw [heq]
        exact hnegt
      have h2 := covPt_shift ν hs hbadst
      rw [aDiag_smul_mul] at h2
      exact h2 (covPt_neg ν hgood)
    -- the transported complement of the bad slice of `aDiag t • x` lies in the bad slice of `x`
    have hsub : (fun s : Fin 3 → ℝ => s + t) '' (Prod.mk (aDiag t • x) ⁻¹' (Goodᶜ ∪ Bad))ᶜ
        ⊆ Prod.mk x ⁻¹' (Goodᶜ ∪ Bad) := by
      rintro u ⟨s, hs, rfl⟩
      exact hBsub x (hshift s (hGsub (aDiag t • x) hyX' hs))
    have hvolG : volume ((Prod.mk (aDiag t • x) ⁻¹' (Goodᶜ ∪ Bad))ᶜ) = ⊤ := by
      have hcompl := measure_compl (hBadmeas.preimage measurable_prodMk_left)
        (by rw [hyA]; exact ENNReal.zero_ne_top)
      rw [hyA, volume_univ_fin3] at hcompl
      simpa using hcompl
    have hle : volume ((fun s : Fin 3 → ℝ => s + t) ''
        (Prod.mk (aDiag t • x) ⁻¹' (Goodᶜ ∪ Bad))ᶜ) ≤ volume (Prod.mk x ⁻¹' (Goodᶜ ∪ Bad)) :=
      measure_mono hsub
    rw [volume_image_add t, hvolG, hxA] at hle
    exact absurd hle (by simp)

end Work.EKLRelCross

end
