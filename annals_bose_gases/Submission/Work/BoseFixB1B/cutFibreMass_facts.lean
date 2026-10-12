import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Submission.Work.BoseFixB1B.CutFibreForms
import Submission.Work.BoseFixB1B.chiB_abs_le_boxMargin
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.cutFibreMass_facts`

The **fibre-mass facts** for the smooth approximants of the sharp box state.

## What is proved

For the sliding box `B(u) = dlBox L d u`, the sliding window `χ_B = chiB L d u` and the peeled
fibre-mass form `cutFibreMass L A volA χ i Ψ` of `Work.BoseFixB1B.CutFibreForms` (the squared
`L²`-mass of the windowed, box-mean-free slot-`i` fibre of `Ψ`, integrated over the outside
configuration and the slot position), we show

* **(boundedness)** the total mass `∑ᵢ cutFibreMass … i Ψ_δ` of the smooth approximants
  `Ψ_δ = (∏ᵢ γ_δ(xᵢ))·ψ` is bounded uniformly in `δ > 0`, and so is the total mass of the sharp
  box state `1_{B(u)^{n+1}}·ψ`;
* **(convergence)** `∑ᵢ cutFibreMass … i (Ψ_δ − 1_{B(u)^{n+1}}ψ) → 0` as `δ → 0⁺`.

Both are consequences of the single quantitative bound `cutFibreMass_sum_le_L2`: the total fibre
mass is dominated by the `L²`-mass of the ambient state.  Its proof is the elementary one-body
estimate, for each slot `i` and outside configuration `r`,

    ∫_{acube L} (χ(z)·Q_{B(u),i}Ψ(z,r))² dz
      ≤ |χ|_∞² ∫_{B(u)} (Q_{B(u),i}Ψ(z,r))² dz      (χ vanishes off B(u))
      ≤ |χ|_∞² ∫_{B(u)} Ψ(z,r)² dz,                  (the mean-free projection is an L²-contraction)

together with the peel `∫_{abox (n+1) L} = ∫_{abox n L}∫_{acube L}` of the inserted coordinate
(`Submission.BoseGases.abox_integral_peel`) and `|χ_B| ≤ chiSup²`
(`Work.SmallBoxTBWord.abs_chiB_le_chiSup_sq`).  The convergence of the total mass is then
dominated convergence for `∫_{abox} (Ψ_δ − 1_{B(u)^{n+1}}ψ)²`, whose pointwise limit holds off the
Lebesgue-null set of configurations one of whose coordinates has vanishing box margin
`Work.BoseFixB1B.boxMargin` (a finite union of coordinate hyperplanes).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1B

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## 1. Generic integral bounds on a measurable set -/

/-- If `f ≤ C` on `s`, then `∫_s f ≤ C |s|`.  No measurability of `f` is needed: when `f` is not
integrable on `s` both sides are `0`, and in the integrable case the comparison with the constant
function `C` applies. -/
lemma setIntegral_le_const {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α} {f : α → ℝ}
    {C : ℝ} (hs : MeasurableSet s) (hμ : μ s < ⊤) (hC : 0 ≤ C) (h : ∀ x ∈ s, f x ≤ C) :
    ∫ x in s, f x ∂μ ≤ C * μ.real s := by
  by_cases hf : IntegrableOn f s μ
  · have hg : IntegrableOn (fun _ : α => C) s μ :=
      integrableOn_const (μ := μ) (s := s) (ne_of_lt hμ) (by simp)
    have hae : ∀ᵐ x ∂(μ.restrict s), f x ≤ (fun _ : α => C) x := by
      rw [ae_restrict_iff' hs]
      exact ae_of_all μ (fun x hx => h x hx)
    have hmono : ∫ x in s, f x ∂μ ≤ ∫ x in s, (fun _ : α => C) x ∂μ :=
      integral_mono_ae (μ := μ.restrict s) hf hg hae
    have hconst : ∫ x in s, (fun _ : α => C) x ∂μ = C * μ.real s := by
      rw [setIntegral_const]
      simp [smul_eq_mul, mul_comm]
    linarith [hmono, hconst]
  · have hf' : ¬ Integrable f (μ.restrict s) := hf
    rw [integral_undef hf']
    exact mul_nonneg hC (measureReal_nonneg)

/-- If `|f| ≤ C` on `s`, then `|∫_s f| ≤ C |s|`. -/
lemma abs_setIntegral_le_const {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}
    {f : α → ℝ} {C : ℝ} (hs : MeasurableSet s) (hμ : μ s < ⊤) (h : ∀ x ∈ s, |f x| ≤ C) :
    |∫ x in s, f x ∂μ| ≤ C * μ.real s := by
  haveI : IsFiniteMeasure (μ.restrict s) := ⟨by rwa [Measure.restrict_apply_univ]⟩
  have hb : ∀ᵐ x ∂(μ.restrict s), ‖f x‖ ≤ C := by
    rw [ae_restrict_iff' hs]
    exact ae_of_all μ (fun x hx => by simpa [Real.norm_eq_abs] using h x hx)
  have h1 := norm_integral_le_of_norm_le_const (μ := μ.restrict s) (f := f) (C := C) hb
  simpa [Real.norm_eq_abs, Measure.restrict_apply_univ, measureReal_def] using h1

/-- If `f ≤ β` on `s` with `β ≥ 0` integrable on `s`, then `∫_s f ≤ ∫_s β`.  The integrability of
`f` is not assumed: when `f` is not integrable on `s` the left-hand side is `0`, and the right-hand
side is nonnegative because `β ≥ 0`. -/
lemma setIntegral_le_of_le_ae {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}
    {f β : α → ℝ} (hs : MeasurableSet s) (hβ : IntegrableOn β s μ)
    (hβ0 : ∀ x ∈ s, 0 ≤ β x) (h : ∀ x ∈ s, f x ≤ β x) :
    ∫ x in s, f x ∂μ ≤ ∫ x in s, β x ∂μ := by
  by_cases hf : IntegrableOn f s μ
  · exact integral_mono_ae hf hβ (by
      filter_upwards [ae_restrict_mem hs] with x hx
      exact h x hx)
  · have hf' : ¬ Integrable f (μ.restrict s) := hf
    rw [integral_undef hf']
    exact integral_nonneg_of_ae (by
      filter_upwards [ae_restrict_mem hs] with x hx
      exact hβ0 x hx)

/-! ## 2. The insertion map `kcInsN` and the box mean -/

/-- Inserting a point of `acube L` into a configuration of `abox n L` gives a configuration of
`abox (n+1) L`. -/
lemma kcInsN_mem_abox {n : ℕ} {L : ℝ} (i : Fin (n+1)) {y : E3} {r : X n}
    (hy : y ∈ acube L) (hr : r ∈ abox n L) :
    (kcInsN n i) (y, r) ∈ abox (n+1) L := by
  intro j
  rcases Fin.eq_self_or_eq_succAbove i j with h | ⟨j', h⟩
  · subst h; rw [kc_insN_apply_same]; exact hy
  · subst h; rw [kc_insN_apply_succ]
    exact (mem_abox_iff n L r).mp hr j'

/-- **The box mean-free projection along a peeled fibre.**  The mean of `Ψ` over the box `A` in the
inserted slot is independent of the value inserted there, so the projection is the difference of
the fibre of `Ψ` and the box mean of the fibre. -/
lemma boxQ_kcInsN_eq {n : ℕ} (i : Fin (n+1)) (volA : ℝ) (A : Set E3)
    (Ψ : X (n+1) → ℝ) (y : E3) (r : X n) :
    Work.SmallBoxTBWord.boxQ volA A i Ψ ((kcInsN n i) (y, r))
      = Ψ ((kcInsN n i) (y, r))
        - (1/volA) * ∫ z in A, Ψ ((kcInsN n i) (z, r)) := by
  unfold Work.SmallBoxTBWord.boxQ Work.SmallBoxTBWord.boxP
  congr 2
  apply integral_congr_ae
  filter_upwards with z
  congr 1
  ext j
  by_cases hj : j = i
  · subst hj; simp [kc_insN_apply_same]
  · obtain ⟨j', hji⟩ := Fin.exists_succAbove_eq hj
    subst hji
    rw [Function.update_apply, if_neg (Fin.succAbove_ne i j')]
    simp [kc_insN_apply_succ]

/-- The window vanishes off the sliding box. -/
lemma chiB_eq_zero_of_notMem_dlBox {L d : ℝ} (hL : 0 < L) (hd : 0 < d) (u : E3) {y : E3}
    (hy : y ∉ dlBox L d u) : chiB L d u y = 0 := by
  by_contra h
  exact hy (chiB_support_mem hL hd u y h)

/-! ## 3. Volumes of the cube and the box -/

lemma volume_real_acube {L : ℝ} (hL : 0 ≤ L) : (volume : Measure E3).real (acube L) = L^3 := by
  rw [measureReal_def, acube_volume L hL, ENNReal.toReal_ofReal (pow_nonneg hL 3)]

lemma volume_real_abox (N : ℕ) {L : ℝ} (hL : 0 ≤ L) :
    (volume : Measure (X N)).real (abox N L) = (L^3)^N := by
  rw [measureReal_def, abox_volume N L hL,
    ENNReal.toReal_ofReal (pow_nonneg (pow_nonneg hL 3) N)]

/-! ## 4. Pointwise and measurability facts for the two states -/

/-- The smooth approximant is bounded by `Cb` on the box. -/
lemma cutFibre_abs_cutProd_le {k : ℕ} {L d : ℝ} (hL : 0 < L) {u : E3} {ψ : X k → ℝ}
    {K Cb : ℝ} {γ : ℝ → E3 → ℝ} (hcut : IsCutFamily L d u K γ) {δ : ℝ} (hδ : 0 < δ)
    (hCb : 0 ≤ Cb) (hψb : ∀ x ∈ abox k L, |ψ x| ≤ Cb) :
    ∀ x ∈ abox k L, |cutProd (γ δ) ψ x| ≤ Cb := by
  intro x hx
  have h01 : ∀ y, 0 ≤ γ δ y ∧ γ δ y ≤ 1 := (hcut.2 δ hδ).2.2.1
  have hprod0 : 0 ≤ ∏ i : Fin k, γ δ (x i) := Finset.prod_nonneg (fun i _ => (h01 (x i)).1)
  have hprod1 : ∏ i : Fin k, γ δ (x i) ≤ 1 :=
    Finset.prod_le_one₀ (fun i _ => (h01 (x i)).1) (fun i _ => (h01 (x i)).2)
  rw [cutProd_apply, abs_mul, abs_of_nonneg hprod0]
  calc (∏ i : Fin k, γ δ (x i)) * |ψ x| ≤ 1 * Cb :=
        mul_le_mul hprod1 (hψb x hx) (abs_nonneg _) zero_le_one
    _ = Cb := one_mul Cb

/-- The sharp box state is bounded by `Cb` on the box. -/
lemma cutFibre_abs_sharpBoxState_le {k : ℕ} {L d : ℝ} {u : E3} {ψ : X k → ℝ} {Cb : ℝ}
    (hCb : 0 ≤ Cb) (hψb : ∀ x ∈ abox k L, |ψ x| ≤ Cb) :
    ∀ x ∈ abox k L, |sharpBoxState (dlBox L d u) ψ x| ≤ Cb := by
  intro x hx
  by_cases h : ∀ i : Fin k, x i ∈ dlBox L d u
  · rw [sharpState_eq_self_of_mem h]; exact hψb x hx
  · rw [sharpState_eq_zero_of_notMem h, abs_zero]; exact hCb

/-- Measurability of the product approximant. -/
lemma cutFibre_measurable_cutProd {k : ℕ} {γ : E3 → ℝ} (hγ : Continuous γ) {ψ : X k → ℝ}
    (hψ : Continuous ψ) : Measurable (cutProd γ ψ) := by
  have h1 : Continuous (fun x : X k => ∏ i : Fin k, γ (x i)) :=
    continuous_finsetProd Finset.univ (fun i _ => hγ.comp (continuous_apply i))
  exact (h1.mul hψ).measurable

/-- Measurability of the sharp box state. -/
lemma cutFibre_measurable_sharpBoxState {k : ℕ} {B : Set E3} (hB : MeasurableSet B)
    {ψ : X k → ℝ} (hψ : Measurable ψ) : Measurable (sharpBoxState B ψ) := by
  rw [sharpBoxState]
  refine hψ.indicator ?_
  rw [Work.PerSector.slotBox, show {z : Fin k → E3 | ∀ i, z i ∈ B}
      = ⋂ i, {z : Fin k → E3 | z i ∈ B} from by ext z; simp [Set.mem_iInter]]
  exact MeasurableSet.iInter (fun i => hB.preimage (measurable_pi_apply i))

/-! ## 5. The mean-free projection is an `L²`-contraction -/

/-- **The mean-free projection decreases the `L²` mass.**  For a measurable function `g` bounded on
`A` by `Cb`, with `volA = |A|`, the `L²`-mass of `g` minus its mean over `A` is at most the
`L²`-mass of `g`: `∫_A (g − ⨏_A g)² = ∫_A g² − |A|·(⨏_A g)² ≤ ∫_A g²`. -/
lemma setIntegral_sq_sub_mean_le {A : Set E3} {volA Cb : ℝ}
    (hA : MeasurableSet A) (hfin : (volume : Measure E3) A < ⊤)
    (hvol : volA = (volume : Measure E3).real A)
    {g : E3 → ℝ} (hg : Measurable g) (hCb : 0 ≤ Cb) (hgb : ∀ y ∈ A, |g y| ≤ Cb) :
    ∫ y in A, (g y - (1 / volA) * ∫ z in A, g z) ^ 2 ≤ ∫ y in A, (g y) ^ 2 := by
  set m : ℝ := (1 / volA) * ∫ z in A, g z with hm
  have hgi : IntegrableOn g A volume :=
    IntegrableOn.of_bound hfin hg.aestronglyMeasurable Cb (by
      rw [ae_restrict_iff' hA]
      exact ae_of_all _ (fun y hy => by simpa [Real.norm_eq_abs] using hgb y hy))
  have hg2 : IntegrableOn (fun y : E3 => (g y) ^ 2) A volume :=
    IntegrableOn.of_bound hfin (hg.pow_const 2).aestronglyMeasurable (Cb ^ 2) (by
      rw [ae_restrict_iff' hA]
      exact ae_of_all _ (fun y hy => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hgb y hy) 2))
  have hmvol : m * volA = ∫ z in A, g z := by
    rw [hm]
    rcases eq_or_ne volA 0 with hv | hv
    · rw [hv, mul_zero]
      have hz : (volume : Measure E3) A = 0 := by
        have h0 : (volume : Measure E3).real A = 0 := by rw [← hvol, hv]
        rw [measureReal_def] at h0
        rcases (ENNReal.toReal_eq_zero_iff _).mp h0 with h | h
        · exact h
        · exact absurd h (ne_of_lt hfin)
      exact (setIntegral_measure_zero _ hz).symm
    · calc (1 / volA) * (∫ z in A, g z) * volA
          = (∫ z in A, g z) * ((1 / volA) * volA) := by ring
        _ = (∫ z in A, g z) * 1 := by rw [one_div, inv_mul_cancel₀ hv]
        _ = ∫ z in A, g z := mul_one _
  have hpt : ∀ y : E3, (g y - m) ^ 2 = (g y) ^ 2 - (2 * m) * g y + m ^ 2 := fun y => by ring
  have hm2 : IntegrableOn (fun _ : E3 => (m ^ 2 : ℝ)) A volume :=
    integrableOn_const (μ := volume) (s := A) (ne_of_lt hfin) (by simp)
  have hsplit1 : ∫ y in A, ((g y) ^ 2 - (2 * m) * g y)
      = (∫ y in A, (g y) ^ 2) - (2 * m) * (∫ y in A, g y) := by
    rw [integral_sub (f := fun y : E3 => (g y) ^ 2) (g := fun y : E3 => (2 * m) * g y)
      hg2 (hgi.const_mul (2 * m)), integral_const_mul]
  have hsplit2 : ∫ y in A, (m ^ 2 : ℝ) = m ^ 2 * volA := by
    rw [setIntegral_const, ← hvol]
    simp [smul_eq_mul, mul_comm]
  have hsplitAdd : ∫ y in A, ((g y) ^ 2 - (2 * m) * g y + m ^ 2)
      = (∫ y in A, ((g y) ^ 2 - (2 * m) * g y)) + ∫ y in A, (m ^ 2 : ℝ) :=
    integral_add (f := fun y : E3 => (g y) ^ 2 - (2 * m) * g y) (g := fun _ : E3 => m ^ 2)
      (hg2.sub (hgi.const_mul (2 * m))) hm2
  have hexp : ∫ y in A, (g y - m) ^ 2 = (∫ y in A, (g y) ^ 2) - m ^ 2 * volA := by
    rw [show (fun y : E3 => (g y - m) ^ 2)
        = fun y => ((g y) ^ 2 - (2 * m) * g y + m ^ 2) from by
      funext y; exact hpt y]
    rw [hsplitAdd, hsplit1, hsplit2, ← hmvol]
    ring
  rw [hexp]
  have h0 : 0 ≤ m ^ 2 * volA := mul_nonneg (sq_nonneg m) (by rw [hvol]; exact measureReal_nonneg)
  simpa using sub_le_sub_left h0 (∫ y in A, (g y) ^ 2)

/-! ## 6. The box mean of a fibre is bounded -/

/-- The box mean of a peeled fibre of a state bounded by `Cb` on the box is bounded by `Cb`. -/
lemma boxP_fibre_abs_le {n : ℕ} {L d : ℝ} (hL : 0 < L) (hd : 0 < d) (u : E3)
    {Ψ : X (n+1) → ℝ} {Cb : ℝ} (hCb : 0 ≤ Cb)
    (hΨb : ∀ x ∈ abox (n+1) L, |Ψ x| ≤ Cb) (i : Fin (n+1)) {r : X n}
    (hr : r ∈ abox n L) :
    |(1 / SmallBoxSliding.boxMass L d u) * ∫ z in dlBox L d u, Ψ ((kcInsN n i) (z, r))| ≤ Cb := by
  have hAmeas : MeasurableSet (dlBox L d u) := SmallBoxSliding.measurableSet_dlBox L d u
  have hAfin : (volume : Measure E3) (dlBox L d u) < ⊤ :=
    (Work.SmallBoxTBWord.isCompact_dlBox hL hd u).measure_lt_top
  have hvol : SmallBoxSliding.boxMass L d u = (volume : Measure E3).real (dlBox L d u) :=
    SmallBoxSliding.boxMass_eq_measureReal L d u
  have hvol0 : 0 ≤ SmallBoxSliding.boxMass L d u := by
    rw [hvol]; exact measureReal_nonneg
  have hsub : dlBox L d u ⊆ acube L := SmallBoxSliding.dlBox_subset_acube L d u
  have hgb : ∀ z ∈ dlBox L d u, |Ψ ((kcInsN n i) (z, r))| ≤ Cb := fun z hz =>
    hΨb _ (kcInsN_mem_abox i (hsub hz) ((mem_abox_iff n L r).mp hr))
  have hint := abs_setIntegral_le_const hAmeas hAfin hgb
  rw [← hvol] at hint
  rcases eq_or_ne (SmallBoxSliding.boxMass L d u) 0 with hv | hv
  · rw [hv, one_div, inv_zero, zero_mul, abs_zero]; exact hCb
  · have hpos : 0 < SmallBoxSliding.boxMass L d u := lt_of_le_of_ne hvol0 (Ne.symm hv)
    calc |(1 / SmallBoxSliding.boxMass L d u) * ∫ z in dlBox L d u, Ψ ((kcInsN n i) (z, r))|
        = |1 / SmallBoxSliding.boxMass L d u|
            * |∫ z in dlBox L d u, Ψ ((kcInsN n i) (z, r))| := abs_mul _ _
      _ ≤ |1 / SmallBoxSliding.boxMass L d u| * (Cb * SmallBoxSliding.boxMass L d u) :=
          mul_le_mul_of_nonneg_left hint (abs_nonneg _)
      _ = Cb * (|1 / SmallBoxSliding.boxMass L d u| * SmallBoxSliding.boxMass L d u) := by ring
      _ = Cb := by
          rw [abs_of_pos (one_div_pos.mpr hpos), one_div, inv_mul_cancel₀ hv, mul_one]

/-! ## 7. The pointwise (in the outside configuration) fibre-mass bound -/

/-- **The pointwise fibre-mass bound.**  For `r ∈ abox n L`, the windowed `L²`-mass of the
mean-free slot-`i` fibre of `Ψ` is at most `chiSup⁴` times the (unwindowed, unprojected)
`L²`-mass of the same fibre. -/
lemma cutFibreMass_integrand_le {n : ℕ} {L d : ℝ} (hL : 0 < L) (hd : 0 < d) (u : E3)
    {Ψ : X (n+1) → ℝ} (hΨm : Measurable Ψ) {Cb : ℝ} (hCb : 0 ≤ Cb)
    (hΨb : ∀ x ∈ abox (n+1) L, |Ψ x| ≤ Cb) (i : Fin (n+1)) {r : X n}
    (hr : r ∈ abox n L) :
    (∫ y in acube L, (chiB L d u y * Work.SmallBoxTBWord.boxQ (SmallBoxSliding.boxMass L d u)
        (dlBox L d u) i Ψ ((kcInsN n i) (y, r)))^2)
      ≤ chiSup^4 * ∫ y in acube L, (Ψ ((kcInsN n i) (y, r)))^2 := by
  have hAmeas : MeasurableSet (dlBox L d u) := SmallBoxSliding.measurableSet_dlBox L d u
  have hAfin : (volume : Measure E3) (dlBox L d u) < ⊤ :=
    (Work.SmallBoxTBWord.isCompact_dlBox hL hd u).measure_lt_top
  have hvol : SmallBoxSliding.boxMass L d u = (volume : Measure E3).real (dlBox L d u) :=
    SmallBoxSliding.boxMass_eq_measureReal L d u
  have hsub : dlBox L d u ⊆ acube L := SmallBoxSliding.dlBox_subset_acube L d u
  have hfcube : (volume : Measure E3) (acube L) < ⊤ := acube_lt_top L hL.le
  have hgmeas : Measurable (fun y : E3 => Ψ ((kcInsN n i) (y, r))) :=
    hΨm.comp ((kcInsN n i).measurable.comp (measurable_id.prod measurable_const))
  have hgb : ∀ y ∈ acube L, |Ψ ((kcInsN n i) (y, r))| ≤ Cb := fun y hy =>
    hΨb _ (kcInsN_mem_abox i hy ((mem_abox_iff n L r).mp hr))
  have hmb : |(1 / SmallBoxSliding.boxMass L d u) *
      ∫ z in dlBox L d u, Ψ ((kcInsN n i) (z, r))| ≤ Cb :=
    boxP_fibre_abs_le hL hd u hCb hΨb i hr
  have hχ : ∀ y : E3, |chiB L d u y| ≤ chiSup^2 := fun y =>
    Work.SmallBoxTBWord.abs_chiB_le_chiSup_sq u y
  set M : ℝ := (1 / SmallBoxSliding.boxMass L d u) *
    ∫ z in dlBox L d u, Ψ ((kcInsN n i) (z, r)) with hM
  have hmain : (∫ y in acube L, (chiB L d u y * (Ψ ((kcInsN n i) (y, r)) - M))^2)
      ≤ chiSup^4 * ∫ y in acube L, (Ψ ((kcInsN n i) (y, r)))^2 := by
    have htrunc : (∫ y in acube L, (chiB L d u y * (Ψ ((kcInsN n i) (y, r)) - M))^2)
        = ∫ y in dlBox L d u, (chiB L d u y * (Ψ ((kcInsN n i) (y, r)) - M))^2 :=
      setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (acube_measurable L) hsub
        (fun y hy => by
          rw [chiB_eq_zero_of_notMem_dlBox hL hd u hy.2, zero_mul]
          norm_num)
    have hβint : IntegrableOn (fun y : E3 => (chiSup^2)^2 *
        (Ψ ((kcInsN n i) (y, r)) - M)^2) (dlBox L d u) volume := by
      refine IntegrableOn.of_bound hAfin ?_ ((chiSup^2)^2 * (2*Cb)^2) ?_
      · exact (((hgmeas.sub_const M).pow_const 2).const_mul _).aestronglyMeasurable
      · rw [ae_restrict_iff' hAmeas]
        refine ae_of_all _ (fun y hy => ?_)
        have h1 : |Ψ ((kcInsN n i) (y, r)) - M| ≤ 2 * Cb := by
          have habs : |Ψ ((kcInsN n i) (y, r)) - M|
              ≤ |Ψ ((kcInsN n i) (y, r))| + |M| := by
            simpa [Real.norm_eq_abs] using
              norm_sub_le (Ψ ((kcInsN n i) (y, r))) M
          rw [hM] at hmb ⊢
          linarith [hgb y (hsub hy)]
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (chiSup^2)),
          abs_of_nonneg (sq_nonneg _), ← sq_abs (Ψ ((kcInsN n i) (y, r)) - M)]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) h1 2) (sq_nonneg _)
    have step2 : (∫ y in dlBox L d u, (chiB L d u y * (Ψ ((kcInsN n i) (y, r)) - M))^2)
        ≤ ∫ y in dlBox L d u, (chiSup^2)^2 * (Ψ ((kcInsN n i) (y, r)) - M)^2 :=
      setIntegral_le_of_le_ae hAmeas hβint
        (fun y _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
        (fun y _ => by
          rw [mul_pow, ← sq_abs (chiB L d u y)]
          exact mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (abs_nonneg _) (hχ y) 2) (sq_nonneg _))
    have step3 : (∫ y in dlBox L d u, (Ψ ((kcInsN n i) (y, r)) - M)^2)
        ≤ ∫ y in dlBox L d u, (Ψ ((kcInsN n i) (y, r)))^2 := by
      have h := setIntegral_sq_sub_mean_le (A := dlBox L d u)
        (volA := SmallBoxSliding.boxMass L d u) (Cb := Cb) hAmeas hAfin hvol hgmeas hCb
        (fun y hy => hgb y (hsub hy))
      simpa only [hM] using h
    have step4 : (∫ y in dlBox L d u, (Ψ ((kcInsN n i) (y, r)))^2)
        ≤ ∫ y in acube L, (Ψ ((kcInsN n i) (y, r)))^2 := by
      refine setIntegral_mono_set (f := fun y : E3 => (Ψ ((kcInsN n i) (y, r)))^2) ?_ ?_ ?_
      · exact IntegrableOn.of_bound hfcube (hgmeas.pow_const 2).aestronglyMeasurable (Cb ^ 2) (by
          rw [ae_restrict_iff' (acube_measurable L)]
          exact ae_of_all _ (fun y hy => by
            rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) (hgb y hy) 2))
      · exact ae_of_all _ (fun y => sq_nonneg _)
      · exact ae_of_all _ (fun y hy => hsub hy)
    calc (∫ y in acube L, (chiB L d u y * (Ψ ((kcInsN n i) (y, r)) - M))^2)
        = ∫ y in dlBox L d u, (chiB L d u y * (Ψ ((kcInsN n i) (y, r)) - M))^2 := htrunc
      _ ≤ ∫ y in dlBox L d u, (chiSup^2)^2 * (Ψ ((kcInsN n i) (y, r)) - M)^2 := step2
      _ = (chiSup^2)^2 * ∫ y in dlBox L d u, (Ψ ((kcInsN n i) (y, r)) - M)^2 :=
          integral_const_mul _ _
      _ ≤ (chiSup^2)^2 * ∫ y in dlBox L d u, (Ψ ((kcInsN n i) (y, r)))^2 :=
          mul_le_mul_of_nonneg_left step3 (sq_nonneg _)
      _ ≤ (chiSup^2)^2 * ∫ y in acube L, (Ψ ((kcInsN n i) (y, r)))^2 :=
          mul_le_mul_of_nonneg_left step4 (sq_nonneg _)
      _ = chiSup^4 * ∫ y in acube L, (Ψ ((kcInsN n i) (y, r)))^2 := by ring
  have hQ : ∀ y : E3, Work.SmallBoxTBWord.boxQ (SmallBoxSliding.boxMass L d u) (dlBox L d u) i Ψ
      ((kcInsN n i) (y, r)) = Ψ ((kcInsN n i) (y, r)) - M := by
    intro y
    rw [boxQ_kcInsN_eq, hM]
  simpa only [hQ] using hmain

/-! ## 8. Integrability of the fibre `L²`-mass -/

/-- The `L²`-mass of the slot-`i` fibre, as a function of the outside configuration, is
integrable.  (It is bounded by `Cb²·L³` on the box, and measurable by the Bochner-Fubini
theorem.) -/
lemma integrableOn_fibreIntegral {n : ℕ} (i : Fin (n+1)) {L : ℝ} (hL : 0 < L)
    {Ψ : X (n+1) → ℝ} (hΨ : Measurable Ψ) {Cb : ℝ} (hCb : 0 ≤ Cb)
    (hΨb : ∀ x ∈ abox (n+1) L, |Ψ x| ≤ Cb) :
    IntegrableOn (fun r : X n => ∫ y in acube L, (Ψ ((kcInsN n i) (y, r)))^2)
      (abox n L) volume := by
  have hfin : (volume : Measure (X n)) (abox n L) < ⊤ := abox_lt_top n L hL.le
  refine IntegrableOn.of_bound hfin ?_ (Cb^2 * L^3) ?_
  · have hjoint : Measurable (fun p : X n × E3 => (Ψ ((kcInsN n i) (p.2, p.1)))^2) :=
      (hΨ.comp ((kcInsN n i).measurable.comp (measurable_snd.prod measurable_fst))).pow_const 2
    exact hjoint.aestronglyMeasurable.integral_prod_right'
  · rw [ae_restrict_iff' (abox_measurable n L)]
    refine ae_of_all _ (fun r hr => ?_)
    have hle : ∫ y in acube L, (Ψ ((kcInsN n i) (y, r)))^2 ≤ Cb^2 * L^3 := by
      have hb : ∀ y ∈ acube L, (Ψ ((kcInsN n i) (y, r)))^2 ≤ Cb^2 := by
        intro y hy
        have h1 := hΨb _ (kcInsN_mem_abox i hy ((mem_abox_iff n L r).mp hr))
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) h1 2
      have h := setIntegral_le_const (acube_measurable L) (acube_lt_top L hL.le) (sq_nonneg _) hb
      rwa [volume_real_acube hL.le] at h
    rw [Real.norm_eq_abs,
      abs_of_nonneg (integral_nonneg_of_ae (ae_of_all _ (fun y => sq_nonneg _)))]
    exact hle

/-! ## 9. The total fibre mass is bounded by the `L²`-mass -/

/-- **The fibre mass is dominated by the `L²`-mass.**  For a measurable state `Ψ` bounded by `Cb`
on the box, the sum of the windowed, mean-free fibre masses is at most `(n+1)·chiSup⁴` times the
`L²`-mass of `Ψ` on the box. -/
theorem cutFibreMass_sum_le_L2 {n : ℕ} {L d : ℝ} (hL : 0 < L) (hd : 0 < d) (u : E3)
    {Ψ : X (n+1) → ℝ} (hΨm : Measurable Ψ) {Cb : ℝ} (hCb : 0 ≤ Cb)
    (hΨb : ∀ x ∈ abox (n+1) L, |Ψ x| ≤ Cb) :
    ∑ i : Fin (n+1), cutFibreMass L (dlBox L d u) (SmallBoxSliding.boxMass L d u)
        (chiB L d u) i Ψ
      ≤ (↑(n+1) : ℝ) * (chiSup^4 * ∫ x in abox (n+1) L, (Ψ x)^2) := by
  have hInt : IntegrableOn (fun x : X (n+1) => (Ψ x)^2) (abox (n+1) L) volume :=
    IntegrableOn.of_bound (abox_lt_top (n+1) L hL.le) (hΨm.pow_const 2).aestronglyMeasurable
      (Cb^2) (by
        rw [ae_restrict_iff' (abox_measurable (n+1) L)]
        exact ae_of_all _ (fun x hx => by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hΨb x hx) 2))
  have hper : ∀ i : Fin (n+1), cutFibreMass L (dlBox L d u) (SmallBoxSliding.boxMass L d u)
      (chiB L d u) i Ψ ≤ chiSup^4 * ∫ x in abox (n+1) L, (Ψ x)^2 := by
    intro i
    have hstep : (∫ r in abox n L, ∫ y in acube L, (chiB L d u y * Work.SmallBoxTBWord.boxQ
          (SmallBoxSliding.boxMass L d u) (dlBox L d u) i Ψ ((kcInsN n i) (y, r)))^2)
        ≤ chiSup^4 * ∫ x in abox (n+1) L, (Ψ x)^2 := by
      calc (∫ r in abox n L, ∫ y in acube L, (chiB L d u y * Work.SmallBoxTBWord.boxQ
            (SmallBoxSliding.boxMass L d u) (dlBox L d u) i Ψ ((kcInsN n i) (y, r)))^2)
          ≤ ∫ r in abox n L, chiSup^4 * ∫ y in acube L,
              (Ψ ((kcInsN n i) (y, r)))^2 :=
            setIntegral_le_of_le_ae (abox_measurable n L)
              ((integrableOn_fibreIntegral i hL hΨm hCb hΨb).const_mul _)
              (fun r _ => mul_nonneg (pow_nonneg chiSup_pos.le 4)
                (integral_nonneg_of_ae (ae_of_all _ (fun y => sq_nonneg _))))
              (fun r hr => cutFibreMass_integrand_le hL hd u hΨm hCb hΨb i hr)
        _ = chiSup^4 * ∫ r in abox n L, ∫ y in acube L, (Ψ ((kcInsN n i) (y, r)))^2 :=
            integral_const_mul _ _
        _ = chiSup^4 * ∫ x in abox (n+1) L, (Ψ x)^2 := by
            rw [abox_integral_peel i (fun x => (Ψ x)^2) hInt]
    simpa only [cutFibreMass] using hstep
  calc (∑ i : Fin (n+1), cutFibreMass L (dlBox L d u) (SmallBoxSliding.boxMass L d u)
        (chiB L d u) i Ψ)
      ≤ ∑ _i : Fin (n+1), chiSup^4 * ∫ x in abox (n+1) L, (Ψ x)^2 :=
        Finset.sum_le_sum (fun i _ => hper i)
    _ = (↑(n+1) : ℝ) * (chiSup^4 * ∫ x in abox (n+1) L, (Ψ x)^2) := by
        rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]

/-! ## 10. The configurations with a vanishing box margin are null -/

/-- A coordinate hyperplane of `E³` is Lebesgue-null. -/
lemma cutFibreMass_coord_hyperplane_null (i : Fin 3) (c : ℝ) :
    (volume : Measure E3) {y : E3 | y i = c} = 0 := by
  have hqmp : Measure.QuasiMeasurePreserving (fun y : E3 => y i)
      (volume : Measure E3) (volume : Measure ℝ) :=
    (Measure.quasiMeasurePreserving_eval (fun _ : Fin 3 => (volume : Measure ℝ)) i).comp
      (PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving
  have h := hqmp.preimage_null (Real.volume_singleton (a := c))
  have heq : (fun y : E3 => y i) ⁻¹' ({c} : Set ℝ) = {y : E3 | y i = c} := by ext y; simp
  rw [heq] at h
  exact h

/-- `{y | boxMargin L d u y = 0}` is contained in a finite union of coordinate hyperplanes of
`E³`, hence is Lebesgue-null. -/
lemma cutFibreMass_boxMargin_eq_zero_null (L d : ℝ) (u : E3) :
    (volume : Measure E3) {y : E3 | boxMargin L d u y = 0} = 0 := by
  classical
  have hSnull : ∀ i : Fin 3,
      (volume : Measure E3) ({y : E3 | y i = L / 2} ∪ {y : E3 | y i = -(L / 2)}
        ∪ {y : E3 | y i = (L * d) * u i + L * d / 2}
        ∪ {y : E3 | y i = (L * d) * u i - L * d / 2}) = 0 := by
    intro i
    refine measure_union_null (measure_union_null (measure_union_null ?_ ?_) ?_) ?_
    · exact cutFibreMass_coord_hyperplane_null i (L / 2)
    · exact cutFibreMass_coord_hyperplane_null i (-(L / 2))
    · exact cutFibreMass_coord_hyperplane_null i ((L * d) * u i + L * d / 2)
    · exact cutFibreMass_coord_hyperplane_null i ((L * d) * u i - L * d / 2)
  have hconv : ∀ {a c : ℝ}, |a| = c → a = c ∨ a = -c := by
    intro a c hx
    rcases le_or_gt 0 a with h | h
    · left; rw [abs_of_nonneg h] at hx; exact hx
    · right; rw [abs_of_neg h] at hx; linarith
  have hcover : {y : E3 | boxMargin L d u y = 0} ⊆
      ⋃ i : Fin 3, ({y : E3 | y i = L / 2} ∪ {y : E3 | y i = -(L / 2)}
        ∪ {y : E3 | y i = (L * d) * u i + L * d / 2}
        ∪ {y : E3 | y i = (L * d) * u i - L * d / 2}) := by
    intro y hy
    have hy' : boxMargin L d u y = 0 := hy
    rw [boxMargin, min_eq_iff] at hy'
    rcases hy' with ⟨hA, -⟩ | ⟨hB, -⟩
    · obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_inf' (H := Finset.univ_nonempty)
        (f := fun i : Fin 3 => L / 2 - |y i|)
      have hzero : |y i| = L / 2 := by linarith
      refine Set.mem_iUnion.mpr ⟨i, ?_⟩
      rcases hconv hzero with h | h
      · exact Or.inl (Or.inl (Or.inl h))
      · exact Or.inl (Or.inl (Or.inr h))
    · obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_inf' (H := Finset.univ_nonempty)
        (f := fun i : Fin 3 => L * d / 2 - |(y - (L * d) • u) i|)
      have hzero : |(y - (L * d) • u) i| = L * d / 2 := by linarith
      have hcoord : (y - (L * d) • u) i = y i - (L * d) * u i := by
        simp [PiLp.sub_apply, PiLp.smul_apply]
      rw [hcoord] at hzero
      refine Set.mem_iUnion.mpr ⟨i, ?_⟩
      rcases hconv hzero with h | h
      · refine Or.inl (Or.inr ?_)
        simp only [Set.mem_setOf_eq]
        linarith only [h]
      · refine Or.inr ?_
        simp only [Set.mem_setOf_eq]
        linarith only [h]
  refine measure_mono_null hcover ?_
  exact measure_iUnion_null_iff.mpr hSnull

/-- Almost every configuration has all its box margins nonzero. -/
lemma cutFibreMass_ae_boxMargin_coord_ne_zero (k : ℕ) (L d : ℝ) (u : E3) :
    ∀ᵐ x ∂(volume : Measure (X k)), ∀ i : Fin k, boxMargin L d u (x i) ≠ 0 := by
  have hcoord : ∀ i : Fin k, (volume : Measure (X k))
      {x : X k | boxMargin L d u (x i) = 0} = 0 := by
    intro i
    have hqmp : Measure.QuasiMeasurePreserving (fun x : X k => x i)
        (volume : Measure (X k)) (volume : Measure E3) :=
      Measure.quasiMeasurePreserving_eval (fun _ : Fin k => (volume : Measure E3)) i
    exact hqmp.preimage_null (cutFibreMass_boxMargin_eq_zero_null L d u)
  rw [MeasureTheory.ae_iff]
  have hset : {x : X k | ¬ (∀ i : Fin k, boxMargin L d u (x i) ≠ 0)}
      = ⋃ i : Fin k, {x : X k | boxMargin L d u (x i) = 0} := by
    ext x; simp [not_forall]
  rw [hset]
  exact measure_iUnion_null_iff.mpr hcoord

/-! ## 11. Pointwise convergence of the difference of the two states -/

/-- **The difference of the approximant and the sharp state vanishes eventually**, off the null set
of configurations with a vanishing box margin. -/
lemma cutFibreMass_ae_tendsto {k : ℕ} {L d : ℝ} (hL : 0 < L) (hd : 0 < d) (u : E3)
    {ψ : X k → ℝ} {K : ℝ} {γ : ℝ → E3 → ℝ} (hcut : IsCutFamily L d u K γ) :
    ∀ᵐ x ∂((volume : Measure (X k)).restrict (abox k L)),
      Filter.Tendsto
        (fun δ : ℝ => cutProd (γ δ) ψ x - sharpBoxState (dlBox L d u) ψ x)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have hae : ∀ᵐ x ∂(volume : Measure (X k)), ∀ i : Fin k, boxMargin L d u (x i) ≠ 0 :=
    cutFibreMass_ae_boxMargin_coord_ne_zero k L d u
  have hae' : ∀ᵐ x ∂((volume : Measure (X k)).restrict (abox k L)),
      ∀ i : Fin k, boxMargin L d u (x i) ≠ 0 :=
    ae_mono (Measure.restrict_le_self (μ := volume) (s := abox k L)) hae
  filter_upwards [hae'] with x hx
  by_cases hall : ∀ i : Fin k, x i ∈ dlBox L d u
  · have hpos : ∀ i : Fin k, 0 < boxMargin L d u (x i) := fun i =>
      lt_of_le_of_ne (boxMargin_nonneg_iff.mpr (hall i)) (Ne.symm (hx i))
    have hev : (fun δ : ℝ => cutProd (γ δ) ψ x - sharpBoxState (dlBox L d u) ψ x)
        =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)] (fun _ => (0 : ℝ)) := by
      have h1 : ∀ i : Fin k, ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi 0), γ δ (x i) = 1 := by
        intro i
        filter_upwards [Filter.Eventually.filter_mono (nhdsWithin_le_nhds (a := (0 : ℝ))
            (s := Set.Ioi 0)) (Iio_mem_nhds (hpos i)), self_mem_nhdsWithin] with δ hlt hδ
        exact (hcut.2 δ hδ).2.2.2.1 (x i) hlt.le
      have h2 : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi 0), ∀ i : Fin k, γ δ (x i) = 1 :=
        Filter.eventually_all.mpr h1
      filter_upwards [h2] with δ hδ
      rw [cutProd_apply, Finset.prod_eq_one (fun i _ => hδ i), one_mul,
        sharpState_eq_self_of_mem hall, sub_self]
    exact Filter.Tendsto.congr' hev.symm tendsto_const_nhds
  · push Not at hall
    obtain ⟨i₀, hi₀⟩ := hall
    have hev : (fun δ : ℝ => cutProd (γ δ) ψ x - sharpBoxState (dlBox L d u) ψ x)
        =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)] (fun _ => (0 : ℝ)) := by
      filter_upwards [self_mem_nhdsWithin] with δ hδ
      have hγ0 : γ δ (x i₀) = 0 := by
        by_contra hne
        exact hi₀ ((hcut.2 δ hδ).2.1 (subset_tsupport _ (Function.mem_support.mpr hne)))
      rw [cutProd_apply, Finset.prod_eq_zero (Finset.mem_univ i₀) hγ0, zero_mul,
        sharpState_eq_zero_of_notMem (fun hc => hi₀ (hc i₀)), sub_zero]
    exact Filter.Tendsto.congr' hev.symm tendsto_const_nhds

/-- **The `L²`-mass of the difference of the two states tends to `0`.** -/
lemma cutFibreMass_tendsto_integral_sq {k : ℕ} {L d : ℝ} (hL : 0 < L) (hd : 0 < d) (u : E3)
    {ψ : X k → ℝ} {K Cb : ℝ} {γ : ℝ → E3 → ℝ} (hcut : IsCutFamily L d u K γ)
    (hψ : Continuous ψ) (hCb : 0 ≤ Cb) (hψb : ∀ x ∈ abox k L, |ψ x| ≤ Cb) :
    Filter.Tendsto
      (fun δ : ℝ => ∫ x in abox k L,
        (cutProd (γ δ) ψ x - sharpBoxState (dlBox L d u) ψ x)^2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have hae := cutFibreMass_ae_tendsto (ψ := ψ) (K := K) (γ := γ) hL hd u hcut
  haveI : IsFiniteMeasure ((volume : Measure (X k)).restrict (abox k L)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact abox_lt_top k L hL.le⟩
  have hbound : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ∀ᵐ x ∂((volume : Measure (X k)).restrict (abox k L)),
        ‖(cutProd (γ δ) ψ x - sharpBoxState (dlBox L d u) ψ x)^2‖ ≤ (2*Cb)^2 := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    filter_upwards [ae_restrict_mem (abox_measurable k L)] with x hx
    have h1 : |cutProd (γ δ) ψ x - sharpBoxState (dlBox L d u) ψ x| ≤ 2 * Cb := by
      have habs : |cutProd (γ δ) ψ x - sharpBoxState (dlBox L d u) ψ x|
          ≤ |cutProd (γ δ) ψ x| + |sharpBoxState (dlBox L d u) ψ x| := by
        simpa [Real.norm_eq_abs] using
          norm_sub_le (cutProd (γ δ) ψ x) (sharpBoxState (dlBox L d u) ψ x)
      have hA := cutFibre_abs_cutProd_le hL hcut hδ hCb hψb x hx
      have hB : |sharpBoxState (dlBox L d u) ψ x| ≤ Cb :=
        cutFibre_abs_sharpBoxState_le (d := d) (u := u) hCb hψb x hx
      linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have hmain := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (μ := (volume : Measure (X k)).restrict (abox k L))
    (l := nhdsWithin (0 : ℝ) (Set.Ioi 0))
    (F := fun δ x => (cutProd (γ δ) ψ x - sharpBoxState (dlBox L d u) ψ x)^2)
    (f := fun _ => (0 : ℝ)) (bound := fun _ => (2*Cb)^2)
    (by
      filter_upwards [self_mem_nhdsWithin] with δ hδ
      exact (((cutFibre_measurable_cutProd (hcut.2 δ hδ).1.continuous hψ).sub
        (cutFibre_measurable_sharpBoxState (SmallBoxSliding.measurableSet_dlBox L d u)
          hψ.measurable)).pow_const 2).aestronglyMeasurable)
    hbound (integrable_const _) (by
      filter_upwards [hae] with x hx
      simpa using hx.pow 2)
  simpa using hmain

/-! ## 12. The fibre-mass facts -/

theorem cutFibreMass_facts {n : ℕ} {L d : ℝ} (hL : 0 < L) (hd : 0 < d)
    (u : EuclideanSpace ℝ (Fin 3))
    {ψ : Submission.BoseGases.X (n+1) → ℝ} {K Cb : ℝ} {γ : ℝ → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hcut : Work.BoseFixB1B.IsCutFamily L d u K γ)
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hCb : 0 ≤ Cb)
    (hψb : ∀ x ∈ Submission.BoseGases.abox (n+1) L, |ψ x| ≤ Cb) :
    (∃ C : ℝ, 0 ≤ C ∧
      (∀ δ : ℝ, 0 < δ → ∑ i : Fin (n+1), Work.BoseFixB1B.cutFibreMass L
          (Submission.BoseGases.dlBox L d u) (Work.SmallBoxSliding.boxMass L d u)
          (Submission.BoseGases.chiB L d u) i (Work.BoseFixB1B.cutProd (γ δ) ψ) ≤ C) ∧
      (∑ i : Fin (n+1), Work.BoseFixB1B.cutFibreMass L
          (Submission.BoseGases.dlBox L d u) (Work.SmallBoxSliding.boxMass L d u)
          (Submission.BoseGases.chiB L d u) i
          (Work.BoseFixB1B.sharpBoxState (Submission.BoseGases.dlBox L d u) ψ) ≤ C))
    ∧ Filter.Tendsto (fun δ : ℝ => ∑ i : Fin (n+1), Work.BoseFixB1B.cutFibreMass L
        (Submission.BoseGases.dlBox L d u) (Work.SmallBoxSliding.boxMass L d u)
        (Submission.BoseGases.chiB L d u) i
        (fun x => Work.BoseFixB1B.cutProd (γ δ) ψ x
          - Work.BoseFixB1B.sharpBoxState (Submission.BoseGases.dlBox L d u) ψ x))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  set CC : ℝ := (↑(n+1) : ℝ) * chiSup^4 * Cb^2 * (L^3)^(n+1) with hCC
  have hCC0 : 0 ≤ CC := by
    rw [hCC]
    exact mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg chiSup_pos.le 4))
      (pow_nonneg hCb 2)) (pow_nonneg (pow_nonneg hL.le 3) _)
  have hmeasS : Measurable (sharpBoxState (dlBox L d u) ψ) :=
    cutFibre_measurable_sharpBoxState (SmallBoxSliding.measurableSet_dlBox L d u)
      hψ.continuous.measurable
  have hmass : ∀ {ω : X (n+1) → ℝ}, (∀ x ∈ abox (n+1) L, |ω x| ≤ Cb) →
      ∫ x in abox (n+1) L, (ω x)^2 ≤ Cb^2 * (L^3)^(n+1) := by
    intro ω hω
    have hle : ∫ x in abox (n+1) L, (ω x)^2
        ≤ Cb^2 * (volume : Measure (X (n+1))).real (abox (n+1) L) :=
      setIntegral_le_const (abox_measurable (n+1) L) (abox_lt_top (n+1) L hL.le) (sq_nonneg _)
        (fun x hx => by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hω x hx) 2)
    rwa [volume_real_abox (n+1) hL.le] at hle
  have hK0 : 0 ≤ (↑(n+1) : ℝ) * chiSup^4 :=
    mul_nonneg (Nat.cast_nonneg _) (pow_nonneg chiSup_pos.le 4)
  refine ⟨⟨CC, hCC0, ⟨?_, ?_⟩⟩, ?_⟩
  · intro δ hδ
    have hmeas : Measurable (cutProd (γ δ) ψ) :=
      cutFibre_measurable_cutProd (hcut.2 δ hδ).1.continuous hψ.continuous
    have hb := cutFibre_abs_cutProd_le hL hcut hδ hCb hψb
    calc (∑ i : Fin (n+1), cutFibreMass L (dlBox L d u) (SmallBoxSliding.boxMass L d u)
          (chiB L d u) i (cutProd (γ δ) ψ))
        ≤ (↑(n+1) : ℝ) * (chiSup^4 * ∫ x in abox (n+1) L, (cutProd (γ δ) ψ x)^2) :=
          cutFibreMass_sum_le_L2 hL hd u hmeas hCb hb
      _ = (↑(n+1) : ℝ) * chiSup^4 * (∫ x in abox (n+1) L, (cutProd (γ δ) ψ x)^2) := by ring
      _ ≤ (↑(n+1) : ℝ) * chiSup^4 * (Cb^2 * (L^3)^(n+1)) :=
          mul_le_mul_of_nonneg_left (hmass hb) hK0
      _ = CC := by rw [hCC]; ring
  · have hb : ∀ x ∈ abox (n+1) L, |sharpBoxState (dlBox L d u) ψ x| ≤ Cb :=
      cutFibre_abs_sharpBoxState_le (d := d) (u := u) hCb hψb
    calc (∑ i : Fin (n+1), cutFibreMass L (dlBox L d u) (SmallBoxSliding.boxMass L d u)
          (chiB L d u) i (sharpBoxState (dlBox L d u) ψ))
        ≤ (↑(n+1) : ℝ) * (chiSup^4 * ∫ x in abox (n+1) L,
            (sharpBoxState (dlBox L d u) ψ x)^2) :=
          cutFibreMass_sum_le_L2 hL hd u hmeasS hCb hb
      _ = (↑(n+1) : ℝ) * chiSup^4 * (∫ x in abox (n+1) L,
            (sharpBoxState (dlBox L d u) ψ x)^2) := by ring
      _ ≤ (↑(n+1) : ℝ) * chiSup^4 * (Cb^2 * (L^3)^(n+1)) :=
          mul_le_mul_of_nonneg_left (hmass hb) hK0
      _ = CC := by rw [hCC]; ring
  · have hkey : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        (∑ i : Fin (n+1), cutFibreMass L (dlBox L d u) (SmallBoxSliding.boxMass L d u)
          (chiB L d u) i
          (fun x => cutProd (γ δ) ψ x - sharpBoxState (dlBox L d u) ψ x))
        ≤ (↑(n+1) : ℝ) * (chiSup^4 *
          (∫ x in abox (n+1) L,
            (cutProd (γ δ) ψ x - sharpBoxState (dlBox L d u) ψ x)^2)) := by
      filter_upwards [self_mem_nhdsWithin] with δ hδ
      have hmeas : Measurable
          (fun x => cutProd (γ δ) ψ x - sharpBoxState (dlBox L d u) ψ x) :=
        (cutFibre_measurable_cutProd (hcut.2 δ hδ).1.continuous hψ.continuous).sub hmeasS
      have hb : ∀ x ∈ abox (n+1) L,
          |cutProd (γ δ) ψ x - sharpBoxState (dlBox L d u) ψ x| ≤ 2 * Cb := by
        intro x hx
        have habs : |cutProd (γ δ) ψ x - sharpBoxState (dlBox L d u) ψ x|
            ≤ |cutProd (γ δ) ψ x| + |sharpBoxState (dlBox L d u) ψ x| := by
          simpa [Real.norm_eq_abs] using
            norm_sub_le (cutProd (γ δ) ψ x) (sharpBoxState (dlBox L d u) ψ x)
        have hA := cutFibre_abs_cutProd_le hL hcut hδ hCb hψb x hx
        have hB : |sharpBoxState (dlBox L d u) ψ x| ≤ Cb :=
          cutFibre_abs_sharpBoxState_le (d := d) (u := u) hCb hψb x hx
        linarith
      exact cutFibreMass_sum_le_L2 (Cb := 2 * Cb) hL hd u hmeas (mul_nonneg (by norm_num) hCb) hb
    have hbound : Filter.Tendsto
        (fun δ : ℝ => (↑(n+1) : ℝ) * (chiSup^4 *
          (∫ x in abox (n+1) L,
            (cutProd (γ δ) ψ x - sharpBoxState (dlBox L d u) ψ x)^2)))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      have hc : Filter.Tendsto (fun _ : ℝ => (↑(n+1) : ℝ) * chiSup^4)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds ((↑(n+1) : ℝ) * chiSup^4)) :=
        tendsto_const_nhds
      have h := hc.mul (cutFibreMass_tendsto_integral_sq hL hd u hcut hψ.continuous hCb hψb)
      simpa [mul_assoc] using h
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbound ?_ hkey
    exact Filter.Eventually.of_forall (fun δ => Finset.sum_nonneg (fun i _ => by
      unfold cutFibreMass
      exact integral_nonneg_of_ae (ae_of_all _ (fun r =>
        integral_nonneg_of_ae (ae_of_all _ (fun y => sq_nonneg _))))))

end Work.BoseFixB1B
