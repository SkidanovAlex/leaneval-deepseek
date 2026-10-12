import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BSKinetic.bsW_fsKinCoeff_le
import Submission.Work.BSKinetic.dlBox_eq_empty_of_far
import Submission.Work.BSKinetic.exists_chiScale_bound
import Submission.Work.BSKinetic.exists_fibre_bound
import Submission.Work.BSKinetic.smallBoxWord1_eq_zero_of_dlBox_eq_empty
import Submission.Work.BSKinetic.tBdiagForm_one_eq_bsW
import Submission.Work.BSKinetic.windowed_mean_free_bounds
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BSKinetic

/-! **Uniform bounds and compact `u`-support for the one-body sliding word and the one-body anchored
big-box word on slot fibres.**  This is the analytic bookkeeping that makes all the `u`- and
`r`-integrals of the slot-sum reduction absolutely convergent (the state lies in the box, and the
sliding windows `chiB ℓ d u` are supported in `dlBox ℓ d u ⊆ acube ℓ`).

Far vanishing (easy): if `dlBox ℓ d u = ∅` then `chiB ℓ d u ≡ 0` and
`boxQInd volA (dlBox ℓ d u) i Ψ ≡ 0` (the box indicator is the zero function and the box mean
vanishes), so both summands of `tBwordInd` are `0`; and `dlBox ℓ d u = ∅` as soon as
`‖(ℓ*d)•u‖ > √3*(ℓ + ℓ*d)/2`, i.e. `‖u‖ > √3*(1+d)/(2*d)`, because
`x ∈ acube ℓ ∧ x - (ℓ*d)•u ∈ acube (ℓ*d)` forces `‖x‖ ≤ √3*ℓ/2` and `‖x - (ℓ*d)•u‖ ≤ √3*ℓ*d/2`.

Bound: for `u` in that ball and `r ∈ abox n ℓ` the word is a coefficient times an integral of
`(boxQInd ...)²` over the compact box `abox 1 ℓ` (bounded by `4*sup²*ℓ³`, using
`|(1/volA)∫_A φ| ≤ sup_A |φ|` when `volA = boxMass ℓ d u = |dlBox ℓ d u|`), plus a `p`-integral of
`fsKinCoeff c ‖p‖ * ‖tBamp (chiB ℓ d u) p (boxQInd ...) 0 x‖²`.  The latter is bounded **uniformly
in `u`** by the Fourier-decay estimate `Commons.Analysis.Fourier.fourier_decay_mul_update` fed with
*explicit* derivative data: the support radius `R = √3 ℓ/2` of `chiB ℓ d u` and global bounds `G k`
on `‖iteratedFDeriv ℝ k (chiB ℓ d u)‖` (uniform in `u`, from the Leibniz rule applied to
`chiScale ℓ * (chiScale (ℓ*d) ∘ (· - (ℓ*d)u))`) and bounds `M k` on the state `boxQ ...` on the ball
of radius `√3 ℓ/2` (from `‖iteratedFDeriv ℝ k Φ‖` on the compact image of that ball under
`kcInsN n i (·, r)`, uniform in `r ∈ abox n ℓ`).  Then
`fsKinCoeff c r ≤ 2*(1+c²)*(1+r²)` (cf. `famKin_fsKinCoeff_le_bound` in
`Submission/Work/BSKinetic/familyBigKin_eq_slotFamily.lean`) reduces the `p`-integral to
`∫_p (1+‖p‖)⁻⁴ < ∞` (`integrable_one_add_norm`).

The anchored big-box conjunct is the same computation with the **fixed** window `chiScale ℓ`
(so `G` is `u`-independent) — an alternative there is to combine
`Work.UBBInputs9.A.tBdiagFormInd_eq_tBdiagForm`, `Work.SmallBoxTBWord.tBdiagForm_sq_eq_dirichlet`
(the Dirichlet form of the windowed projected state) with the pointwise symbol bound
`fsKinCoeff c r ≤ 2*r² + 2*c²`. -/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)
open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## 0. Auxiliary analytic facts -/

/-- **The box mean is bounded by the sup of the state on the box.**  For a measurable set `A` of
finite measure and a function `f` bounded by `S` on `A`, the normalised mean `|A|⁻¹∫_A f` is
bounded by `S` (the case `|A| = 0` is degenerate and gives the value `0`). -/
lemma abs_mean_le_of_sup {A : Set ℝ³} {f : ℝ³ → ℝ} {S : ℝ}
    (hA : MeasurableSet A) (hfin : (volume : Measure ℝ³) A < ⊤)
    (hS : 0 ≤ S) (hb : ∀ z ∈ A, |f z| ≤ S) :
    |(1 / (volume : Measure ℝ³).real A) * ∫ z in A, f z| ≤ S := by
  set v : ℝ := (volume : Measure ℝ³).real A with hv
  have hvnn : 0 ≤ v := by rw [hv]; exact measureReal_nonneg
  have hINE : |(∫ z in A, f z)| ≤ ∫ z in A, |f z| := by
    rw [show (∫ z in A, f z) = ∫ z, f z ∂(volume.restrict A) from rfl,
        show (∫ z in A, |f z|) = ∫ z, |f z| ∂(volume.restrict A) from rfl]
    exact norm_integral_le_integral_norm f
  have hgint : Integrable (fun _ : ℝ³ => S) (volume.restrict A) := by
    rw [MeasureTheory.integrable_const_iff]
    exact Or.inr (MeasureTheory.isFiniteMeasure_restrict.mpr (ne_of_lt hfin))
  have hae : ∀ᵐ z ∂(volume.restrict A), |f z| ≤ S := by
    rw [MeasureTheory.ae_restrict_iff' hA]
    exact Eventually.of_forall fun z hz => hb z hz
  have hle : (∫ z in A, |f z|) ≤ ∫ z in A, S :=
    integral_mono_of_nonneg (Eventually.of_forall fun z => abs_nonneg _) hgint hae
  have hval : (∫ z in A, S) = v * S := by
    rw [setIntegral_const, smul_eq_mul]
  have hvv : v⁻¹ * v ≤ 1 := by
    rcases eq_or_lt_of_le hvnn with h | h
    · rw [← h]; simp
    · exact le_of_eq (inv_mul_cancel₀ (ne_of_gt h))
  calc |(1 / v) * ∫ z in A, f z|
      = v⁻¹ * |(∫ z in A, f z)| := by
        rw [one_div, abs_mul, abs_of_nonneg (inv_nonneg.mpr hvnn)]
    _ ≤ v⁻¹ * (v * S) := by
        refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hvnn)
        calc |(∫ z in A, f z)| ≤ ∫ z in A, |f z| := hINE
          _ ≤ ∫ z in A, S := hle
          _ = v * S := hval
    _ = (v⁻¹ * v) * S := by ring
    _ ≤ 1 * S := mul_le_mul_of_nonneg_right hvv hS
    _ = S := one_mul S

/-- The one-particle `boxQInd` at a single slot, in closed form: the box indicator times the
difference of the fibre value from the box mean. -/
lemma boxQInd_N1_apply (volA : ℝ) (A : Set ℝ³) (φ : X 1 → ℝ) (x : X 1) :
    Work.UBBInputs8.boxQInd volA A 0 φ x = A.indicator (fun _ => 1) (x 0) *
      (φ (fun _ : Fin 1 => x 0) - (1 / volA) * ∫ z in A, φ (fun _ : Fin 1 => z)) := by
  simp only [Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxPInd]
  have hx : φ x = φ (fun _ : Fin 1 => x 0) := by congr 1; funext j; fin_cases j; rfl
  have hz : ∀ z : ℝ³, φ (Function.update x 0 z) = φ (fun _ : Fin 1 => z) := by
    intro z; congr 1; funext j; fin_cases j; simp
  simp_rw [hz]
  rw [hx]
  ring

/-- **The excited count of a one-particle box is bounded by `4 S² ℓ³`**, where `S` bounds the fibre
values on the box and the box mean. -/
lemma cnPlusBoxInd_one_le {ℓ : ℝ} (hℓ : 0 < ℓ) {A : Set ℝ³} {volA S : ℝ} {φ : X 1 → ℝ}
    (hb : ∀ z ∈ A, |φ (fun _ : Fin 1 => z)| ≤ S)
    (hm : |(1 / volA) * ∫ z in A, φ (fun _ : Fin 1 => z)| ≤ S) :
    |Work.UBBInputs8.cnPlusBoxInd ℓ A volA φ| ≤ 4 * S ^ 2 * ℓ ^ 3 := by
  have hS : 0 ≤ S := le_trans (abs_nonneg _) hm
  have hpt : ∀ x : X 1, (Work.UBBInputs8.boxQInd volA A 0 φ x) ^ 2 ≤ 4 * S ^ 2 := by
    intro x
    rw [boxQInd_N1_apply]
    by_cases hxA : x 0 ∈ A
    · rw [Set.indicator_of_mem hxA, one_mul]
      have h1 : |φ (fun _ : Fin 1 => x 0)| ≤ S := hb (x 0) hxA
      have h2 : |φ (fun _ : Fin 1 => x 0)
            - (1 / volA) * ∫ z in A, φ (fun _ : Fin 1 => z)| ≤ S + S := by
        calc |φ (fun _ : Fin 1 => x 0) - (1 / volA) * ∫ z in A, φ (fun _ : Fin 1 => z)|
            ≤ |φ (fun _ : Fin 1 => x 0)|
              + |(1 / volA) * ∫ z in A, φ (fun _ : Fin 1 => z)| := abs_sub _ _
          _ ≤ S + S := add_le_add h1 hm
      calc (φ (fun _ : Fin 1 => x 0) - (1 / volA) * ∫ z in A, φ (fun _ : Fin 1 => z)) ^ 2
          = |φ (fun _ : Fin 1 => x 0) - (1 / volA) * ∫ z in A, φ (fun _ : Fin 1 => z)| ^ 2 :=
            (sq_abs _).symm
        _ ≤ (S + S) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h2 2
        _ = 4 * S ^ 2 := by ring
    · rw [Set.indicator_of_notMem hxA, zero_mul, sq]
      nlinarith [sq_nonneg S]
  have hboxlt : (volume : Measure (X 1)) (abox 1 ℓ) < ⊤ := by
    rw [abox_volume 1 ℓ hℓ.le]; exact ENNReal.ofReal_lt_top
  have hgint : Integrable (fun _ : X 1 => 4 * S ^ 2) (volume.restrict (abox 1 ℓ)) := by
    rw [MeasureTheory.integrable_const_iff]
    exact Or.inr (MeasureTheory.isFiniteMeasure_restrict.mpr (ne_of_lt hboxlt))
  have hle : (∫ x in abox 1 ℓ, (Work.UBBInputs8.boxQInd volA A 0 φ x) ^ 2)
      ≤ 4 * S ^ 2 * ℓ ^ 3 := by
    calc (∫ x in abox 1 ℓ, (Work.UBBInputs8.boxQInd volA A 0 φ x) ^ 2)
        ≤ ∫ x in abox 1 ℓ, 4 * S ^ 2 :=
          integral_mono_of_nonneg (Eventually.of_forall fun x => sq_nonneg _) hgint
            (Eventually.of_forall hpt)
      _ = 4 * S ^ 2 * ℓ ^ 3 := by
          rw [setIntegral_const, smul_eq_mul, Measure.real_def, abox_volume 1 ℓ hℓ.le,
            ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ ((ℓ ^ 3)) ^ 1), pow_one]
          ring
  rw [Work.UBBInputs8.cnPlusBoxInd, Fin.sum_univ_one,
    abs_of_nonneg (MeasureTheory.integral_nonneg fun x => sq_nonneg _)]
  exact hle

/-- The box mean over the anchored cube `acube ℓ` is bounded by the sup on the cube. -/
lemma abs_mean_acube_le {ℓ : ℝ} (hℓ : 0 < ℓ) {S : ℝ} {φ1 : ℝ³ → ℝ}
    (hb : ∀ z ∈ acube ℓ, |φ1 z| ≤ S) :
    |(1 / ℓ ^ 3) * ∫ z in acube ℓ, φ1 z| ≤ S := by
  have h0 : (0 : ℝ³) ∈ acube ℓ := by
    rw [mem_acube_iff]; intro m
    constructor <;> simp <;> linarith
  have hS : 0 ≤ S := le_trans (abs_nonneg _) (hb 0 h0)
  have hv : (volume : Measure ℝ³).real (acube ℓ) = ℓ ^ 3 := by
    rw [Measure.real_def, acube_volume ℓ hℓ.le, ENNReal.toReal_ofReal (by positivity)]
  have h := abs_mean_le_of_sup (A := acube ℓ) (f := φ1) (acube_measurable ℓ)
      (by rw [acube_volume ℓ hℓ.le]; exact ENNReal.ofReal_lt_top) hS hb
  rwa [hv] at h

/-- The box mean over the sliding box `dlBox ℓ d u` is bounded by the sup on `acube ℓ`. -/
lemma abs_mean_dlBox_le {ℓ d : ℝ} (hℓ : 0 < ℓ) {S : ℝ} {φ1 : ℝ³ → ℝ} {u : ℝ³}
    (hb : ∀ z ∈ acube ℓ, |φ1 z| ≤ S) :
    |(1 / Work.SmallBoxSliding.boxMass ℓ d u) * ∫ z in dlBox ℓ d u, φ1 z| ≤ S := by
  have hsub : dlBox ℓ d u ⊆ acube ℓ := fun z hz => hz.1
  have hS : 0 ≤ S := le_trans (abs_nonneg _) (hb 0 (by
    rw [mem_acube_iff]; intro m; constructor <;> simp <;> linarith))
  have h := abs_mean_le_of_sup (A := dlBox ℓ d u) (f := φ1)
      (Work.SmallBoxSliding.measurableSet_dlBox ℓ d u)
      (Work.SmallBoxSliding.volume_dlBox_lt_top hℓ d u) hS (fun z hz => hb z (hsub hz))
  rwa [← Work.SmallBoxSliding.boxMass_eq_measureReal] at h

/-- The derivative part of `exists_chiScale_bound`. -/
lemma exists_chiScale_deriv_bound {s : ℝ} (hs : s ≠ 0) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x v : ℝ³, |fderiv ℝ (chiScale s) x v| ≤ D * ‖v‖ := by
  obtain ⟨C, D, hC, hD, hb, hd⟩ := exists_chiScale_bound hs
  exact ⟨D, hD, hd⟩

/-- **Uniform sup and derivative bounds for the sliding window `chiB ℓ d u`.** -/
lemma exists_chiB_bound {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) :
    ∃ Cχ Dχ : ℝ, 0 ≤ Cχ ∧ 0 ≤ Dχ ∧
      (∀ (u z : ℝ³), |chiB ℓ d u z| ≤ Cχ) ∧
      (∀ (u z : ℝ³) (k : Fin 3), |fderiv ℝ (chiB ℓ d u) z (kcStdBasis k)| ≤ Dχ) := by
  have hld : ℓ * d ≠ 0 := mul_ne_zero (ne_of_gt hℓ) (ne_of_gt hd)
  obtain ⟨Dℓ, hDℓ0, hDℓ⟩ := exists_chiScale_deriv_bound (s := ℓ) (ne_of_gt hℓ)
  obtain ⟨Dld, hDld0, hDld⟩ := exists_chiScale_deriv_bound (s := ℓ * d) hld
  have hchi : 0 ≤ chiSup := le_of_lt chiSup_pos
  refine ⟨chiSup ^ 2, chiSup * Dld + chiSup * Dℓ, by positivity,
    by nlinarith [hchi, hDld0, hDℓ0], ?_, ?_⟩
  · intro u z
    exact Work.SmallBoxTBWord.abs_chiB_le_chiSup_sq u z
  · intro u z k
    have hnorm : ‖kcStdBasis k‖ = 1 := by
      rw [kcStdBasis, EuclideanSpace.norm_single]; norm_num
    rw [Work.UBBInputs9.C.fderiv_chiB_apply ℓ d (ne_of_gt hℓ) (ne_of_gt hd) u z (kcStdBasis k)]
    have h1 : |chiScale ℓ z| ≤ chiSup := abs_chiScale_le_chiSup ℓ z
    have h2 : |fderiv ℝ (chiScale (ℓ * d)) (z - (ℓ * d) • u) (kcStdBasis k)| ≤ Dld := by
      simpa [hnorm] using hDld (z - (ℓ * d) • u) (kcStdBasis k)
    have h3 : |chiScale (ℓ * d) (z - (ℓ * d) • u)| ≤ chiSup := abs_chiScale_le_chiSup (ℓ * d) _
    have h4 : |fderiv ℝ (chiScale ℓ) z (kcStdBasis k)| ≤ Dℓ := by
      simpa [hnorm] using hDℓ z (kcStdBasis k)
    have hcs : 0 ≤ chiSup := le_of_lt chiSup_pos
    calc |chiScale ℓ z * (fderiv ℝ (chiScale (ℓ * d)) (z - (ℓ * d) • u)) (kcStdBasis k)
          + chiScale (ℓ * d) (z - (ℓ * d) • u) * (fderiv ℝ (chiScale ℓ) z) (kcStdBasis k)|
        ≤ |chiScale ℓ z * (fderiv ℝ (chiScale (ℓ * d)) (z - (ℓ * d) • u)) (kcStdBasis k)|
          + |chiScale (ℓ * d) (z - (ℓ * d) • u) * (fderiv ℝ (chiScale ℓ) z) (kcStdBasis k)| :=
          abs_add_le _ _
      _ = |chiScale ℓ z| * |(fderiv ℝ (chiScale (ℓ * d)) (z - (ℓ * d) • u)) (kcStdBasis k)|
          + |chiScale (ℓ * d) (z - (ℓ * d) • u)| * |(fderiv ℝ (chiScale ℓ) z) (kcStdBasis k)| := by
          rw [abs_mul, abs_mul]
      _ ≤ chiSup * Dld + chiSup * Dℓ :=
          add_le_add (mul_le_mul h1 h2 (abs_nonneg _) hcs) (mul_le_mul h3 h4 (abs_nonneg _) hcs)

/-! ## 1. The slot fibre value -/

/-- The slot-`i` fibre of an `(n+1)`-particle state at a constant configuration. -/
@[simp] lemma slotState1_apply_one {n : ℕ} (i : Fin (n + 1)) (Φ : X (n + 1) → ℝ)
    (r : X n) (z : ℝ³) :
    slotState1 i Φ r (fun _ : Fin 1 => z) = Φ (kcInsN n i (z, r)) := rfl

/-! ## 2. The anchored big-box word -/

/-- **Uniform bound for the one-particle anchored big-box word on slot fibres.** -/
lemma bigBoxWord1_bound {ℓ c : ℝ} (hℓ : 0 < ℓ) (n : ℕ)
    {Φ : X (n + 1) → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ) :
    ∃ Kb : ℝ, 0 ≤ Kb ∧ ∀ (i : Fin (n + 1)) (r : X n), r ∈ abox n ℓ →
      |bigBoxWord1 ℓ c (slotState1 i Φ r)| ≤ Kb := by
  obtain ⟨S, S1, hS, hS1, hfib⟩ := exists_fibre_bound hℓ n hΦ
  obtain ⟨Dℓ, hDℓ0, hDℓ⟩ := exists_chiScale_deriv_bound (s := ℓ) (ne_of_gt hℓ)
  have hchi : 0 ≤ chiSup := le_of_lt chiSup_pos
  refine ⟨2 * c ^ 2 * ((chiSup * (S + S)) ^ 2 * ℓ ^ 3)
      + 2 * (3 * ((chiSup * S1 + Dℓ * (S + S)) ^ 2 * ℓ ^ 3)), ?_, ?_⟩
  · have h1 : 0 ≤ (chiSup * (S + S)) ^ 2 * ℓ ^ 3 :=
      mul_nonneg (sq_nonneg _) (pow_nonneg hℓ.le 3)
    have h2 : 0 ≤ (chiSup * S1 + Dℓ * (S + S)) ^ 2 * ℓ ^ 3 :=
      mul_nonneg (sq_nonneg _) (pow_nonneg hℓ.le 3)
    nlinarith [sq_nonneg c, h1, h2]
  · intro i r hr
    obtain ⟨hvb, hvd⟩ := hfib i r hr
    have hnorm : ∀ k : Fin 3, ‖kcStdBasis k‖ = 1 := by
      intro k; rw [kcStdBasis, EuclideanSpace.norm_single]; norm_num
    have hmean : |(1 / ℓ ^ 3) * ∫ z in acube ℓ, Φ (kcInsN n i (z, r))| ≤ S :=
      abs_mean_acube_le hℓ hvb
    have hstate := windowed_mean_free_bounds (ℓ := ℓ)
        (χ := chiScale ℓ) (φ1 := fun z : ℝ³ => Φ (kcInsN n i (z, r)))
        (m := (1 / ℓ ^ 3) * ∫ z in acube ℓ, Φ (kcInsN n i (z, r)))
        (S := S) (S1 := S1) (Cχ := chiSup) (Dχ := Dℓ)
        (chiScale_contDiff (ne_of_gt hℓ)) (chiScale_hasCompactSupport (ne_of_gt hℓ))
        (hΦ.comp (Work.SmallBoxBridge.Fourier.contDiff_kcInsN_right i r))
        (fun z hz => chiScale_eq_zero_of_notMem_acube hℓ hz)
        hS hS1 hchi hDℓ0
        (fun z => abs_chiScale_le_chiSup ℓ z)
        (fun k z => by simpa [hnorm k] using hDℓ z (kcStdBasis k))
        hvb (fun k z hz => hvd z hz k) hmean
    have hfun : (fun z : ℝ³ => chiScale ℓ z * (slotState1 i Φ r (fun _ : Fin 1 => z)
          - (1 / ℓ ^ 3) * ∫ z' in acube ℓ, slotState1 i Φ r (fun _ : Fin 1 => z')))
        = (fun z : ℝ³ => chiScale ℓ z * (Φ (kcInsN n i (z, r))
          - (1 / ℓ ^ 3) * ∫ z' in acube ℓ, Φ (kcInsN n i (z', r)))) := by
      funext z
      have h1 : slotState1 i Φ r (fun _ : Fin 1 => z) = Φ (kcInsN n i (z, r)) := rfl
      have h2 : (∫ z' in acube ℓ, slotState1 i Φ r (fun _ : Fin 1 => z'))
          = ∫ z' in acube ℓ, Φ (kcInsN n i (z', r)) :=
        integral_congr_ae (Eventually.of_forall fun z' => rfl)
      rw [h1, h2]
    have hword : bigBoxWord1 ℓ c (slotState1 i Φ r)
        = ((2 * Real.pi) ^ 3)⁻¹ * Work.BSKinetic.Decomp.bsW (fsKinCoeff c) (fun z : ℝ³ =>
            chiScale ℓ z * (Φ (kcInsN n i (z, r))
              - (1 / ℓ ^ 3) * ∫ z' in acube ℓ, Φ (kcInsN n i (z', r)))) := by
      rw [show bigBoxWord1 ℓ c (slotState1 i Φ r) =
          Work.UBBInputs8.tBdiagFormInd ℓ (acube ℓ) (ℓ ^ 3) (chiScale ℓ)
            (fsKinCoeff c) (slotState1 i Φ r) from rfl]
      rw [Work.UBBInputs9.A.tBdiagFormInd_eq_tBdiagForm (fsKinCoeff c) (slotState1 i Φ r)
            (fun z hz => chiScale_eq_zero_of_notMem_acube hℓ hz),
          Work.BSKinetic.tBdiagForm_one_eq_bsW hℓ (F := fsKinCoeff c)
            (φ := slotState1 i Φ r)]
      rw [hfun]
    calc |bigBoxWord1 ℓ c (slotState1 i Φ r)|
        = ((2 * Real.pi) ^ 3)⁻¹ * Work.BSKinetic.Decomp.bsW (fsKinCoeff c) (fun z : ℝ³ =>
            chiScale ℓ z * (Φ (kcInsN n i (z, r))
              - (1 / ℓ ^ 3) * ∫ z' in acube ℓ, Φ (kcInsN n i (z', r)))) := by
          rw [hword, abs_of_nonneg]
          exact mul_nonneg (by positivity)
            (MeasureTheory.integral_nonneg fun p =>
              mul_nonneg (fsKinCoeff_nonneg c ‖p‖) (sq_nonneg _))
      _ ≤ 2 * c ^ 2 * ((chiSup * (S + S)) ^ 2 * ℓ ^ 3)
            + 2 * (3 * ((chiSup * S1 + Dℓ * (S + S)) ^ 2 * ℓ ^ 3)) :=
          bsW_fsKinCoeff_le hℓ hstate.1 hstate.2.1 hstate.2.2.1 hstate.2.2.2.1 hstate.2.2.2.2

/-! ## 3. The sliding small-box word -/

/-- **Uniform bound for the one-particle sliding small-box word on slot fibres.** -/
lemma smallBoxWord1_bound {ℓ d ε c : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (n : ℕ)
    {Φ : X (n + 1) → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ) :
    ∃ Ks : ℝ, 0 ≤ Ks ∧ ∀ (i : Fin (n + 1)) (r : X n), r ∈ abox n ℓ →
      ∀ u : ℝ³, |smallBoxWord1 ℓ d ε c u (slotState1 i Φ r)| ≤ Ks := by
  obtain ⟨S, S1, hS, hS1, hfib⟩ := exists_fibre_bound hℓ n hΦ
  obtain ⟨Cχ, Dχ, hCχ, hDχ, hχb, hχd⟩ := exists_chiB_bound hℓ hd
  refine ⟨|Work.SmallBoxTBWord.tbGapCoeff (ℓ * d) ε| * (4 * S ^ 2 * ℓ ^ 3)
      + (2 * c ^ 2 * ((Cχ * (S + S)) ^ 2 * ℓ ^ 3)
          + 2 * (3 * ((Cχ * S1 + Dχ * (S + S)) ^ 2 * ℓ ^ 3))), ?_, ?_⟩
  · have h4 : 0 ≤ |Work.SmallBoxTBWord.tbGapCoeff (ℓ * d) ε| * (4 * S ^ 2 * ℓ ^ 3) :=
      mul_nonneg (abs_nonneg _) (by positivity)
    have h5 : 0 ≤ 2 * c ^ 2 * ((Cχ * (S + S)) ^ 2 * ℓ ^ 3) :=
      mul_nonneg (by positivity) (mul_nonneg (sq_nonneg _) (pow_nonneg hℓ.le 3))
    have h6 : 0 ≤ 2 * (3 * ((Cχ * S1 + Dχ * (S + S)) ^ 2 * ℓ ^ 3)) :=
      mul_nonneg (by norm_num)
        (mul_nonneg (by norm_num) (mul_nonneg (sq_nonneg _) (pow_nonneg hℓ.le 3)))
    linarith
  · intro i r hr u
    obtain ⟨hvb, hvd⟩ := hfib i r hr
    have hχvanish : ∀ z : ℝ³, z ∉ dlBox ℓ d u → chiB ℓ d u z = 0 := by
      intro z hz
      by_contra hc
      exact hz (Work.UBBInputs9.A.tsupport_chiB_subset_dlBox hℓ hd u
        (subset_tsupport _ (Function.mem_support.mpr hc)))
    -- the mean of the sliding box
    have hmean : |(1 / Work.SmallBoxSliding.boxMass ℓ d u)
        * ∫ z in dlBox ℓ d u, Φ (kcInsN n i (z, r))| ≤ S :=
      abs_mean_dlBox_le hℓ hvb
    -- the gap term
    have hgap : |Work.UBBInputs8.cnPlusBoxInd ℓ (dlBox ℓ d u)
        (Work.SmallBoxSliding.boxMass ℓ d u) (slotState1 i Φ r)| ≤ 4 * S ^ 2 * ℓ ^ 3 :=
      cnPlusBoxInd_one_le hℓ
        (fun z hz => by rw [slotState1_apply_one]; exact hvb z hz.1)
        (by rw [show (∫ z in dlBox ℓ d u, slotState1 i Φ r (fun _ : Fin 1 => z))
              = ∫ z in dlBox ℓ d u, Φ (kcInsN n i (z, r)) from
              integral_congr_ae (Eventually.of_forall fun z => slotState1_apply_one i Φ r z)]
            exact hmean)
    -- the spectral term
    have hstate := windowed_mean_free_bounds (ℓ := ℓ)
        (χ := chiB ℓ d u) (φ1 := fun z : ℝ³ => Φ (kcInsN n i (z, r)))
        (m := (1 / Work.SmallBoxSliding.boxMass ℓ d u)
          * ∫ z in dlBox ℓ d u, Φ (kcInsN n i (z, r)))
        (S := S) (S1 := S1) (Cχ := Cχ) (Dχ := Dχ)
        (Work.SmallBoxTBWord.contDiff_chiB hℓ hd u)
        (Work.SmallBoxTBWord.hasCompactSupport_chiB hℓ hd u)
        (hΦ.comp (Work.SmallBoxBridge.Fourier.contDiff_kcInsN_right i r))
        (fun z hz => by
          by_contra hc
          exact hz (Work.SmallBoxTBWord.tsupport_chiB_subset_acube hℓ hd u
            (subset_tsupport _ (Function.mem_support.mpr hc))))
        hS hS1 hCχ hDχ
        (fun z => hχb u z)
        (fun k z => hχd u z k)
        (fun z hz => hvb z hz)
        (fun k z hz => hvd z hz k)
        hmean
    have hspec := bsW_fsKinCoeff_le (c := c) hℓ hstate.1 hstate.2.1 hstate.2.2.1
      hstate.2.2.2.1 hstate.2.2.2.2
    have hspecabs : |((2 * Real.pi) ^ 3)⁻¹ * Work.BSKinetic.Decomp.bsW (fsKinCoeff c)
        (fun z : ℝ³ => chiB ℓ d u z * (Φ (kcInsN n i (z, r))
          - (1 / Work.SmallBoxSliding.boxMass ℓ d u)
            * ∫ z' in dlBox ℓ d u, Φ (kcInsN n i (z', r))))|
        ≤ 2 * c ^ 2 * ((Cχ * (S + S)) ^ 2 * ℓ ^ 3)
          + 2 * (3 * ((Cχ * S1 + Dχ * (S + S)) ^ 2 * ℓ ^ 3)) := by
      rw [abs_of_nonneg (mul_nonneg (by positivity)
        (MeasureTheory.integral_nonneg fun p => mul_nonneg (fsKinCoeff_nonneg c ‖p‖) (sq_nonneg _)))]
      exact hspec
    -- the word identity
    have hfun : (fun z : ℝ³ => chiB ℓ d u z * (slotState1 i Φ r (fun _ : Fin 1 => z)
          - (1 / Work.SmallBoxSliding.boxMass ℓ d u)
            * ∫ z' in dlBox ℓ d u, slotState1 i Φ r (fun _ : Fin 1 => z')))
        = (fun z : ℝ³ => chiB ℓ d u z * (Φ (kcInsN n i (z, r))
          - (1 / Work.SmallBoxSliding.boxMass ℓ d u)
            * ∫ z' in dlBox ℓ d u, Φ (kcInsN n i (z', r)))) := by
      funext z
      have h1 : slotState1 i Φ r (fun _ : Fin 1 => z) = Φ (kcInsN n i (z, r)) := rfl
      have h2 : (∫ z' in dlBox ℓ d u, slotState1 i Φ r (fun _ : Fin 1 => z'))
          = ∫ z' in dlBox ℓ d u, Φ (kcInsN n i (z', r)) :=
        integral_congr_ae (Eventually.of_forall fun z' => rfl)
      rw [h1, h2]
    have hword : smallBoxWord1 ℓ d ε c u (slotState1 i Φ r)
        = Work.SmallBoxTBWord.tbGapCoeff (ℓ * d) ε
            * Work.UBBInputs8.cnPlusBoxInd ℓ (dlBox ℓ d u)
                (Work.SmallBoxSliding.boxMass ℓ d u) (slotState1 i Φ r)
          + ((2 * Real.pi) ^ 3)⁻¹ * Work.BSKinetic.Decomp.bsW (fsKinCoeff c)
              (fun z : ℝ³ => chiB ℓ d u z * (Φ (kcInsN n i (z, r))
                - (1 / Work.SmallBoxSliding.boxMass ℓ d u)
                  * ∫ z' in dlBox ℓ d u, Φ (kcInsN n i (z', r)))) := by
      rw [show smallBoxWord1 ℓ d ε c u (slotState1 i Φ r) =
          Work.UBBInputs8.tBwordInd ℓ (dlBox ℓ d u) (Work.SmallBoxSliding.boxMass ℓ d u)
            (chiB ℓ d u) (ℓ * d) ε c (slotState1 i Φ r) from rfl]
      rw [show Work.UBBInputs8.tBwordInd ℓ (dlBox ℓ d u) (Work.SmallBoxSliding.boxMass ℓ d u)
            (chiB ℓ d u) (ℓ * d) ε c (slotState1 i Φ r)
          = Work.SmallBoxTBWord.tbGapCoeff (ℓ * d) ε
              * Work.UBBInputs8.cnPlusBoxInd ℓ (dlBox ℓ d u)
                  (Work.SmallBoxSliding.boxMass ℓ d u) (slotState1 i Φ r)
            + Work.UBBInputs8.tBdiagFormInd ℓ (dlBox ℓ d u) (Work.SmallBoxSliding.boxMass ℓ d u)
                (chiB ℓ d u) (fsKinCoeff c) (slotState1 i Φ r) from rfl]
      rw [Work.UBBInputs9.A.tBdiagFormInd_eq_tBdiagForm (fsKinCoeff c) (slotState1 i Φ r)
            hχvanish,
          Work.BSKinetic.tBdiagForm_one_eq_bsW hℓ (F := fsKinCoeff c)
            (φ := slotState1 i Φ r),
          hfun]
    rw [hword]
    calc |Work.SmallBoxTBWord.tbGapCoeff (ℓ * d) ε
            * Work.UBBInputs8.cnPlusBoxInd ℓ (dlBox ℓ d u)
                (Work.SmallBoxSliding.boxMass ℓ d u) (slotState1 i Φ r)
          + ((2 * Real.pi) ^ 3)⁻¹ * Work.BSKinetic.Decomp.bsW (fsKinCoeff c)
              (fun z : ℝ³ => chiB ℓ d u z * (Φ (kcInsN n i (z, r))
                - (1 / Work.SmallBoxSliding.boxMass ℓ d u)
                  * ∫ z' in dlBox ℓ d u, Φ (kcInsN n i (z', r))))|
        ≤ |Work.SmallBoxTBWord.tbGapCoeff (ℓ * d) ε
            * Work.UBBInputs8.cnPlusBoxInd ℓ (dlBox ℓ d u)
                (Work.SmallBoxSliding.boxMass ℓ d u) (slotState1 i Φ r)|
          + |((2 * Real.pi) ^ 3)⁻¹ * Work.BSKinetic.Decomp.bsW (fsKinCoeff c)
              (fun z : ℝ³ => chiB ℓ d u z * (Φ (kcInsN n i (z, r))
                - (1 / Work.SmallBoxSliding.boxMass ℓ d u)
                  * ∫ z' in dlBox ℓ d u, Φ (kcInsN n i (z', r))))| := abs_add_le _ _
      _ = |Work.SmallBoxTBWord.tbGapCoeff (ℓ * d) ε|
            * |Work.UBBInputs8.cnPlusBoxInd ℓ (dlBox ℓ d u)
                (Work.SmallBoxSliding.boxMass ℓ d u) (slotState1 i Φ r)|
          + |((2 * Real.pi) ^ 3)⁻¹ * Work.BSKinetic.Decomp.bsW (fsKinCoeff c)
              (fun z : ℝ³ => chiB ℓ d u z * (Φ (kcInsN n i (z, r))
                - (1 / Work.SmallBoxSliding.boxMass ℓ d u)
                  * ∫ z' in dlBox ℓ d u, Φ (kcInsN n i (z', r))))| := by rw [abs_mul]
      _ ≤ |Work.SmallBoxTBWord.tbGapCoeff (ℓ * d) ε| * (4 * S ^ 2 * ℓ ^ 3)
          + (2 * c ^ 2 * ((Cχ * (S + S)) ^ 2 * ℓ ^ 3)
              + 2 * (3 * ((Cχ * S1 + Dχ * (S + S)) ^ 2 * ℓ ^ 3))) :=
          add_le_add (mul_le_mul_of_nonneg_left hgap (abs_nonneg _)) hspecabs

/-! ## 4. Assembly -/

theorem slotWord_bounds {ℓ d ε c : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (n : ℕ)
    (Φ : Submission.BoseGases.X (n + 1) → ℝ) (hΦ : ContDiff ℝ (⊤ : ENat) Φ) :
    ∃ (K R : ℝ), 0 ≤ K ∧ 0 ≤ R ∧
      (∀ (u : EuclideanSpace ℝ (Fin 3)), R < ‖u‖ → ∀ (i : Fin (n + 1)) (r : Submission.BoseGases.X n),
          Work.BSKinetic.smallBoxWord1 ℓ d ε c u (Work.BSKinetic.slotState1 i Φ r) = 0) ∧
      (∀ (i : Fin (n + 1)) (r : Submission.BoseGases.X n), r ∈ Submission.BoseGases.abox n ℓ →
          ∀ u : EuclideanSpace ℝ (Fin 3),
            |Work.BSKinetic.smallBoxWord1 ℓ d ε c u (Work.BSKinetic.slotState1 i Φ r)| ≤ K) ∧
      (∀ (i : Fin (n + 1)) (r : Submission.BoseGases.X n), r ∈ Submission.BoseGases.abox n ℓ →
          |Work.BSKinetic.bigBoxWord1 ℓ c (Work.BSKinetic.slotState1 i Φ r)| ≤ K) := by
  obtain ⟨Kb, hKb0, hKb⟩ := bigBoxWord1_bound (ℓ := ℓ) (c := c) hℓ n hΦ
  obtain ⟨Ks, hKs0, hKs⟩ := smallBoxWord1_bound (ℓ := ℓ) (d := d) (ε := ε) (c := c) hℓ hd n hΦ
  refine ⟨max Kb Ks, Real.sqrt 3 * (1 + d) / (2 * d), le_max_of_le_right hKs0, ?_, ?_, ?_, ?_⟩
  · positivity
  · intro u hu i r
    exact smallBoxWord1_eq_zero_of_dlBox_eq_empty _
      (dlBox_eq_empty_of_far hℓ hd hu)
  · intro i r hr u
    exact le_trans (hKs i r hr u) (le_max_right Kb Ks)
  · intro i r hr
    exact le_trans (hKb i r hr) (le_max_left Kb Ks)


end

end Work.BSKinetic
