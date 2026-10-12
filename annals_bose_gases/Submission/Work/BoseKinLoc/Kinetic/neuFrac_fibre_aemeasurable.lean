import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.Kinetic.continuous_fibre_sq_diff
import Submission.Work.BoseKinLoc.Kinetic.neuFrac_lipschitz_of_aemeasurable
import Submission.Work.BoseKinLoc.Kinetic.neuFrac_translate
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Kinetic.neuFrac_fibre_aemeasurable`

**The slot-`i` fibre of the box Neumann fraction is a.e. strongly measurable in the pair
`(u, q₂)`** (the translation parameter and the remaining coordinates).  This is the
measurability input that lets the `N`-body kinetic localisation integrate
`u ↦ neuFrac ℓ a2 u (z ↦ Φ (kcInsN n i (z,q₂)))` over `q₂` by Fubini
(see `Work.BoseKinLoc.Kinetic.fibre_lift`).

## Strategy: continuity, not a dense family of trials

`neuFrac ℓ a2 u ψ` is an `sInf` over the smooth compactly supported trials, so it is *not*
manifestly an integral and the corpus's `StronglyMeasurable.integral_prod_right` arguments do
not apply.  Instead we prove that the map is *continuous*, in three steps.

1. **Translation covariance** (`neuFrac_translate`, delegated):
   `neuFrac ℓ a2 u ψ = neuFrac ℓ a2 0 (fun z ↦ ψ (ℓ • u + z))`.  So the `u`-dependence is only
   a translation of the state, and it suffices to handle the *fixed* box `Λ(0) = acube ℓ`.
2. **Lipschitz estimate in the state** (`neuFrac_lipschitz`, delegated): for states with
   `∫_{acube ℓ} ψ² ≤ R²` and `∫_{acube ℓ} ψ'² ≤ R²` (`R > 0`),
   `|neuFrac ℓ a2 0 ψ − neuFrac ℓ a2 0 ψ'| ≤ 6R·√(∫_{acube ℓ}(ψ−ψ')²)`.
3. **Continuity of the states** (`continuous_fibre_sq_diff`, delegated): the map
   `(q, q') ↦ ∫_{acube ℓ}(φ_q − φ_q')²` is continuous for the shifted slot-`i` fibres
   `φ_q = z ↦ Φ (kcInsN n i (ℓ • q.1 + z, q.2))` (dominated convergence on the fixed cube
   `acube ℓ`, using that `Φ` is bounded with support in the compact box `abox (n+1) ℓ`).

Combining 2 and 3 gives continuity of `q ↦ neuFrac ℓ a2 0 (φ_q)`, and 1 identifies it with the
target function; a continuous function is a.e. strongly measurable.

The uniform radius is `R = max 1 (M·ℓ·√ℓ)` where `M` bounds `|Φ|` (available because
`tsupport Φ ⊆ abox (n+1) ℓ` is compact and `Φ` is continuous): indeed
`∫_{acube ℓ} φ_q² ≤ M²·ℓ³ ≤ R²`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseKinLoc.Kinetic

open Submission.BoseGases

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

/-! ## 1. The shifted slot-`i` fibre and its basic analytic properties -/

/-- The slot-`i` fibre of `Φ` with the inserted variable translated by `ℓ • q.1`:
`z ↦ Φ (kcInsN n i (ℓ • q.1 + z, q.2))`.  By `neuFrac_translate` its Neumann fraction on the
*fixed* box `Λ(0) = acube ℓ` is `neuFrac ℓ a2 q.1 (z ↦ Φ (kcInsN n i (z, q.2)))`. -/
abbrev fibreState {n : ℕ} (i : Fin (n + 1)) (Φ : Submission.BoseGases.X (n + 1) → ℝ) (ℓ : ℝ)
    (q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n) :
    EuclideanSpace ℝ (Fin 3) → ℝ :=
  fun z => Φ (Submission.BoseGases.kcInsN n i (ℓ • q.1 + z, q.2))

/-- The shifted slot-`i` fibre is continuous. -/
lemma fibreState_continuous {ℓ : ℝ} {n : ℕ} (i : Fin (n + 1))
    {Φ : Submission.BoseGases.X (n + 1) → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ)
    (q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n) :
    Continuous (fibreState i Φ ℓ q) := by
  have hins : Continuous (fun z : EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.kcInsN n i (z, q.2)) := by
    have h1 : (fun z : EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.kcInsN n i (z, q.2))
        = Function.update (Submission.BoseGases.kcInsN n i (0, q.2)) i := by
      funext z
      exact Submission.BoseGases.kcInsN_update_zero i z q.2
    rw [h1]
    have hupd : ContDiff ℝ (⊤ : ENat)
        (Function.update (Submission.BoseGases.kcInsN n i (0, q.2)) i) :=
      contDiff_update (⊤ : ENat) (Submission.BoseGases.kcInsN n i (0, q.2)) i
    exact hupd.continuous
  exact hΦ.continuous.comp (hins.comp (by fun_prop))

/-- If the shifted slot-`i` fibre does not vanish at `w`, then `w` lies in the translate
`acube ℓ - ℓ • q.1` of the cube. -/
lemma mem_shift_image_of_ne_zero {ℓ : ℝ} {n : ℕ} (i : Fin (n + 1))
    {Φ : Submission.BoseGases.X (n + 1) → ℝ}
    (hsupp : tsupport Φ ⊆ Submission.BoseGases.abox (n + 1) ℓ)
    {q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n} {w : EuclideanSpace ℝ (Fin 3)}
    (hw : fibreState i Φ ℓ q w ≠ 0) :
    w ∈ (fun z : EuclideanSpace ℝ (Fin 3) => z - ℓ • q.1) '' Submission.BoseGases.acube ℓ := by
  refine ⟨ℓ • q.1 + w, ?_, ?_⟩
  · have hx : Submission.BoseGases.kcInsN n i (ℓ • q.1 + w, q.2)
        ∈ Submission.BoseGases.abox (n + 1) ℓ :=
      hsupp (subset_tsupport Φ (Function.mem_support.mpr hw))
    simpa [Submission.BoseGases.kc_insN_apply_same n i (ℓ • q.1 + w) q.2] using hx i
  · abel

/-- The shifted slot-`i` fibre of a state supported in `abox (n+1) ℓ` is compactly supported:
its support is contained in the translate of `acube ℓ` by `-ℓ • q.1`. -/
lemma fibreState_hasCompactSupport {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} (i : Fin (n + 1))
    {Φ : Submission.BoseGases.X (n + 1) → ℝ}
    (hsupp : tsupport Φ ⊆ Submission.BoseGases.abox (n + 1) ℓ)
    (q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n) :
    HasCompactSupport (fibreState i Φ ℓ q) := by
  have hK : IsCompact
      ((fun z : EuclideanSpace ℝ (Fin 3) => z - ℓ • q.1) '' Submission.BoseGases.acube ℓ) :=
    (Submission.BoseGases.acube_compact hℓ).image (by fun_prop)
  refine IsCompact.of_isClosed_subset hK isClosed_closure ?_
  refine closure_minimal (fun w hw => ?_) hK.isClosed
  exact mem_shift_image_of_ne_zero i hsupp (Function.mem_support.mp hw)

/-- The square of the shifted slot-`i` fibre is integrable (continuous with compact support). -/
lemma fibreState_sq_integrable {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} (i : Fin (n + 1))
    {Φ : Submission.BoseGases.X (n + 1) → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ)
    (hsupp : tsupport Φ ⊆ Submission.BoseGases.abox (n + 1) ℓ)
    (q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n) :
    Integrable (fun z : EuclideanSpace ℝ (Fin 3) => (fibreState i Φ ℓ q z) ^ 2) :=
  Continuous.integrable_of_hasCompactSupport ((fibreState_continuous i hΦ q).pow 2)
    ((fibreState_hasCompactSupport hℓ i hsupp q).comp_left
      (g := fun t : ℝ => t ^ 2) (by norm_num))

/-- The square of the difference of two shifted slot-`i` fibres is integrable. -/
lemma fibreState_diff_sq_integrable {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} (i : Fin (n + 1))
    {Φ : Submission.BoseGases.X (n + 1) → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ)
    (hsupp : tsupport Φ ⊆ Submission.BoseGases.abox (n + 1) ℓ)
    (q q' : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n) :
    Integrable (fun z : EuclideanSpace ℝ (Fin 3) =>
      (fibreState i Φ ℓ q z - fibreState i Φ ℓ q' z) ^ 2) := by
  have hc : Continuous (fun z : EuclideanSpace ℝ (Fin 3) =>
      fibreState i Φ ℓ q z - fibreState i Φ ℓ q' z) :=
    (fibreState_continuous i hΦ q).sub (fibreState_continuous i hΦ q')
  have hs : HasCompactSupport (fun z : EuclideanSpace ℝ (Fin 3) =>
      fibreState i Φ ℓ q z - fibreState i Φ ℓ q' z) := by
    have hK : IsCompact (((fun z : EuclideanSpace ℝ (Fin 3) => z - ℓ • q.1)
          '' Submission.BoseGases.acube ℓ)
        ∪ ((fun z : EuclideanSpace ℝ (Fin 3) => z - ℓ • q'.1)
          '' Submission.BoseGases.acube ℓ)) :=
      ((Submission.BoseGases.acube_compact hℓ).image (by fun_prop)).union
        ((Submission.BoseGases.acube_compact hℓ).image (by fun_prop))
    refine IsCompact.of_isClosed_subset hK isClosed_closure ?_
    refine closure_minimal (fun w hw => ?_) hK.isClosed
    rcases eq_or_ne (fibreState i Φ ℓ q w) 0 with h0 | h0
    · refine Or.inr (mem_shift_image_of_ne_zero i hsupp ?_)
      intro hzero
      exact (Function.mem_support.mp hw) (by rw [h0, hzero, sub_self])
    · exact Or.inl (mem_shift_image_of_ne_zero i hsupp h0)
  exact Continuous.integrable_of_hasCompactSupport (hc.pow 2)
    (hs.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num))

/-! ## 2. Elementary bounds -/

/-- A continuous function whose support lies in the compact box `abox (n+1) ℓ` is bounded. -/
lemma exists_bound_of_tsupport_subset_abox {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ}
    {Φ : Submission.BoseGases.X (n + 1) → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ)
    (hsupp : tsupport Φ ⊆ Submission.BoseGases.abox (n + 1) ℓ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : Submission.BoseGases.X (n + 1), |Φ x| ≤ M := by
  obtain ⟨C, hC⟩ := (Submission.BoseGases.abox_compact (n + 1) hℓ).exists_bound_of_continuousOn
    hΦ.continuous.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : x ∈ Submission.BoseGases.abox (n + 1) ℓ
  · have h := hC x hx
    rw [Real.norm_eq_abs] at h
    exact le_trans h (le_max_left _ _)
  · rw [image_eq_zero_of_notMem_tsupport (fun hmem => hx (hsupp hmem)), abs_zero]
    exact le_max_right _ _

/-- The box `Λ(0)` is the centred cube. -/
lemma lamBox_zero (ℓ : ℝ) : Work.BoseKinLoc.lamBox ℓ 0 = Submission.BoseGases.acube ℓ := by
  ext z
  simp [Work.BoseKinLoc.lamBox, Work.BSKinetic.bsBox]

/-- The `L²`-mass of the shifted slot-`i` fibre over the cube is at most `M²ℓ³`. -/
lemma integral_fibreState_sq_le {ℓ M : ℝ} (hℓ : 0 < ℓ) {n : ℕ} (i : Fin (n + 1))
    {Φ : Submission.BoseGases.X (n + 1) → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ)
    {M : ℝ} (hM : ∀ x : Submission.BoseGases.X (n + 1), |Φ x| ≤ M)
    (q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n) :
    ∫ z in Submission.BoseGases.acube ℓ, (fibreState i Φ ℓ q z) ^ 2 ≤ M ^ 2 * ℓ ^ 3 := by
  have hvol : (volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))
      (Submission.BoseGases.acube ℓ) ≠ ⊤ := by
    rw [Submission.BoseGases.acube_volume ℓ hℓ.le]
    exact ENNReal.ofReal_lt_top.ne
  have hfint : IntegrableOn (fun z : EuclideanSpace ℝ (Fin 3) => (fibreState i Φ ℓ q z) ^ 2)
      (Submission.BoseGases.acube ℓ) volume :=
    ContinuousOn.integrableOn_compact (Submission.BoseGases.acube_compact hℓ)
      ((fibreState_continuous i hΦ q).pow 2).continuousOn
  have hgint : IntegrableOn (fun _ : EuclideanSpace ℝ (Fin 3) => M ^ 2)
      (Submission.BoseGases.acube ℓ) volume := integrableOn_const hvol
  have hpoint : ∀ z ∈ Submission.BoseGases.acube ℓ,
      (fibreState i Φ ℓ q z) ^ 2 ≤ M ^ 2 := fun z _ => by
    have h := pow_le_pow_left₀ (abs_nonneg (fibreState i Φ ℓ q z)) (hM _) 2
    rwa [sq_abs] at h
  have hstep := MeasureTheory.setIntegral_mono_on hfint hgint
    (Submission.BoseGases.acube_measurable ℓ) hpoint
  have hconst : (∫ z in Submission.BoseGases.acube ℓ, M ^ 2 : ℝ) = M ^ 2 * ℓ ^ 3 := by
    rw [MeasureTheory.setIntegral_const, MeasureTheory.Measure.real_def,
      Submission.BoseGases.acube_volume ℓ hℓ.le, ENNReal.toReal_ofReal (by positivity),
      smul_eq_mul]
    ring
  linarith [hstep, hconst.le]

/-! ## 3. The main theorem -/

theorem neuFrac_fibre_aemeasurable {ℓ a2 : ℝ} (hℓ : 0 < ℓ) (ha2 : 0 < a2) {n : ℕ}
    {Φ : Submission.BoseGases.X (n + 1) → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ)
    (hsupp : tsupport Φ ⊆ Submission.BoseGases.abox (n + 1) ℓ) (i : Fin (n + 1)) :
    MeasureTheory.AEStronglyMeasurable
      (fun q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n =>
        Work.BoseKinLoc.neuFrac ℓ a2 q.1 (fun z : EuclideanSpace ℝ (Fin 3) =>
          Φ (Submission.BoseGases.kcInsN n i (z, q.2))))
      ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
        (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n))) := by
  -- a global bound on `Φ`
  obtain ⟨M, hM0, hM⟩ := exists_bound_of_tsupport_subset_abox hℓ hΦ hsupp
  -- the uniform radius
  set R : ℝ := max 1 (M * ℓ * Real.sqrt ℓ) with hRdef
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hRsq : M ^ 2 * ℓ ^ 3 ≤ R ^ 2 := by
    have h1 : M * ℓ * Real.sqrt ℓ ≤ R := le_max_right _ _
    have h2 : 0 ≤ M * ℓ * Real.sqrt ℓ := mul_nonneg (mul_nonneg hM0 hℓ.le) (Real.sqrt_nonneg _)
    have h3 : (M * ℓ * Real.sqrt ℓ) ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ h2 h1 2
    have h4 : (M * ℓ * Real.sqrt ℓ) ^ 2 = M ^ 2 * ℓ ^ 3 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hℓ.le]
      ring
    rwa [h4] at h3
  -- the uniform `L²` bound on the cube
  have hbox : ∀ q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n,
      ∫ z in Submission.BoseGases.acube ℓ, (fibreState i Φ ℓ q z) ^ 2 ≤ R ^ 2 :=
    fun q => le_trans (integral_fibreState_sq_le (M := M) hℓ i hΦ hM q) hRsq
  -- the Lipschitz estimate on the fixed box
  have hlip : ∀ q q' : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n,
      |Work.BoseKinLoc.neuFrac ℓ a2 0 (fibreState i Φ ℓ q)
          - Work.BoseKinLoc.neuFrac ℓ a2 0 (fibreState i Φ ℓ q')|
        ≤ 6 * R * Real.sqrt (∫ z in Submission.BoseGases.acube ℓ,
            (fibreState i Φ ℓ q z - fibreState i Φ ℓ q' z) ^ 2) := by
    intro q q'
    have h := Work.BoseKinLoc.Kinetic.neuFrac_lipschitz_of_aemeasurable (ℓ := ℓ) (a2 := a2) (R := R)
      hℓ ha2 hRpos (0 : EuclideanSpace ℝ (Fin 3))
      (fibreState_continuous i hΦ q).aestronglyMeasurable
      (fibreState_continuous i hΦ q').aestronglyMeasurable
      (fibreState_sq_integrable hℓ i hΦ hsupp q)
      (fibreState_sq_integrable hℓ i hΦ hsupp q')
      (fibreState_diff_sq_integrable hℓ i hΦ hsupp q q')
      (by rw [lamBox_zero]; exact hbox q) (by rw [lamBox_zero]; exact hbox q')
    rwa [lamBox_zero] at h
  -- continuity of the squared difference integral
  have hG : Continuous (fun q : (EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n)
        × (EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n) =>
      ∫ z in Submission.BoseGases.acube ℓ,
        (fibreState i Φ ℓ q.1 z - fibreState i Φ ℓ q.2 z) ^ 2) :=
    continuous_fibre_sq_diff (ℓ := ℓ) hℓ hΦ hsupp i
  -- continuity of the normalized Neumann fraction
  have hcont : Continuous (fun q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n =>
      Work.BoseKinLoc.neuFrac ℓ a2 0 (fibreState i Φ ℓ q)) := by
    rw [continuous_iff_continuousAt]
    intro q₀
    show Tendsto (fun q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n =>
      Work.BoseKinLoc.neuFrac ℓ a2 0 (fibreState i Φ ℓ q)) (𝓝 q₀)
      (𝓝 (Work.BoseKinLoc.neuFrac ℓ a2 0 (fibreState i Φ ℓ q₀)))
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hlim : Tendsto (fun q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n =>
        ∫ z in Submission.BoseGases.acube ℓ,
          (fibreState i Φ ℓ q z - fibreState i Φ ℓ q₀ z) ^ 2) (𝓝 q₀) (𝓝 0) := by
      have h1 : Tendsto (fun q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n =>
          (q, q₀)) (𝓝 q₀) (𝓝 (q₀, q₀)) :=
        Filter.Tendsto.prodMk_nhds tendsto_id tendsto_const_nhds
      have h2 := (hG.continuousAt).tendsto.comp h1
      have hzero : (∫ z in Submission.BoseGases.acube ℓ,
            (fibreState i Φ ℓ (q₀, q₀).1 z - fibreState i Φ ℓ (q₀, q₀).2 z) ^ 2) = 0 := by
        simp
      rwa [hzero] at h2
    refine squeeze_zero
      (f := fun q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n =>
        ‖Work.BoseKinLoc.neuFrac ℓ a2 0 (fibreState i Φ ℓ q)
          - Work.BoseKinLoc.neuFrac ℓ a2 0 (fibreState i Φ ℓ q₀)‖)
      (g := fun q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n =>
        6 * R * Real.sqrt (∫ z in Submission.BoseGases.acube ℓ,
          (fibreState i Φ ℓ q z - fibreState i Φ ℓ q₀ z) ^ 2))
      (fun q => norm_nonneg _) (fun q => ?_) ?_
    · simpa [Real.norm_eq_abs] using hlip q q₀
    · have hfin := (hlim.sqrt).const_mul (6 * R)
      simpa using hfin
  -- assemble
  have hAE : MeasureTheory.AEStronglyMeasurable
      (fun q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n =>
        Work.BoseKinLoc.neuFrac ℓ a2 0 (fibreState i Φ ℓ q))
      ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
        (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n))) :=
    hcont.aestronglyMeasurable
  refine hAE.congr (Filter.Eventually.of_forall (fun q => ?_))
  exact (Work.BoseKinLoc.Kinetic.neuFrac_translate ℓ a2 q.1
    (fun z : EuclideanSpace ℝ (Fin 3) => Φ (Submission.BoseGases.kcInsN n i (z, q.2)))).symm

end Work.BoseKinLoc.Kinetic
