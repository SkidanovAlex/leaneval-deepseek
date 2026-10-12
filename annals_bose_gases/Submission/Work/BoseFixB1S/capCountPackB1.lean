import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBogFS.card_le_of_separated
import Submission.Work.BoseFixB1S.pairSepAeB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-- The support of the two-factor small-box cutoff is measurable (it is open, being the support of
a continuous function). -/
theorem measurableSet_support_chiSmallB {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ}
    (u : EuclideanSpace ℝ (Fin 3)) :
    MeasurableSet (Function.support (Submission.BoseGases.chiSmallB M ℓ d u)) := by
  have hc : Continuous (Submission.BoseGases.chiSmallB M ℓ d u) := by
    unfold Submission.BoseGases.chiSmallB
    exact (Submission.BoseGases.chiScale_continuous ℓ).mul
      ((Submission.BoseGases.chiSmall_continuous hM).comp (by fun_prop))
  rw [show Function.support (Submission.BoseGases.chiSmallB M ℓ d u)
      = {x | Submission.BoseGases.chiSmallB M ℓ d u x = 0}ᶜ by
    ext x; simp [Function.mem_support]]
  exact (isClosed_eq hc continuous_const).isOpen_compl.measurableSet

/-- `Φ²` is integrable on the box for a continuous state `Φ` (the box is compact). -/
theorem integrableOn_sq_abox {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ}
    {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ) :
    MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n => (Φ x) ^ 2)
      (Submission.BoseGases.abox n ℓ) :=
  ((hΦc.pow 2).continuousOn).integrableOn_compact (Submission.BoseGases.abox_compact n hℓ)

/-- `Φ² · 1_A(x i)` is integrable on the box for a measurable `A` and a continuous state `Φ`
(the box has finite volume and both factors are bounded). -/
theorem integrableOn_sq_indicator_abox {ℓ : ℝ} (hℓ : 0 < ℓ)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A) {n : ℕ}
    {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ) (i : Fin n) :
    MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
        (Φ x) ^ 2 * (A.indicator (fun _ => (1 : ℝ)) (x i)))
      (Submission.BoseGases.abox n ℓ) := by
  obtain ⟨B, hB⟩ := (Submission.BoseGases.abox_compact n hℓ).exists_bound_of_continuousOn
    (s := Submission.BoseGases.abox n ℓ) (f := Φ) hΦc.continuousOn
  have hfin : (volume : Measure (Submission.BoseGases.X n))
      (Submission.BoseGases.abox n ℓ) < ⊤ :=
    Submission.BoseGases.abox_lt_top n ℓ hℓ.le
  haveI : IsFiniteMeasure
      ((volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
  refine Integrable.mono' (integrable_const (B ^ 2)) ?_ ?_
  · exact (hΦc.measurable.pow_const 2).aestronglyMeasurable.mul
      (((measurable_const.indicator hA).comp (measurable_pi_apply i))).aestronglyMeasurable
  · filter_upwards [self_mem_ae_restrict (Submission.BoseGases.abox_measurable n ℓ)] with x hx
    have hΦx : ‖Φ x‖ ≤ B := hB x hx
    have hid : ‖A.indicator (fun _ => (1 : ℝ)) (x i)‖ ≤ 1 := by
      by_cases h : x i ∈ A <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]
    calc ‖(Φ x) ^ 2 * (A.indicator (fun _ => (1 : ℝ)) (x i))‖
        = ‖(Φ x) ^ 2‖ * ‖A.indicator (fun _ => (1 : ℝ)) (x i)‖ := norm_mul _ _
      _ = ‖Φ x‖ ^ 2 * ‖A.indicator (fun _ => (1 : ℝ)) (x i)‖ := by rw [norm_pow]
      _ ≤ B ^ 2 * 1 :=
          mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hΦx 2) hid (norm_nonneg _) (sq_nonneg B)
      _ = B ^ 2 := mul_one _

/-- A point of `ℝ³` whose coordinate differences from `c` are all bounded by `L / 2` (i.e. lying
in the axis-parallel cube of side `L` centred at `c`) lies within `√3 · L / 2` of `c`. -/
private lemma norm_sub_le_sqrt_three_half {y c : EuclideanSpace ℝ (Fin 3)} {L : ℝ}
    (h : ∀ j : Fin 3, |(y - c).ofLp j| ≤ L / 2) :
    ‖y - c‖ ≤ Real.sqrt 3 * (L / 2) := by
  have hL2 : (0 : ℝ) ≤ L / 2 := le_trans (abs_nonneg _) (h 0)
  have h2 : ‖y - c‖ ^ 2 ≤ (Real.sqrt 3 * (L / 2)) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc ∑ j : Fin 3, ‖(y - c).ofLp j‖ ^ 2
        ≤ ∑ _j : Fin 3, (L / 2) ^ 2 := by
          refine Finset.sum_le_sum fun j _ => ?_
          have hj := h j
          have hsq : ((y - c).ofLp j) ^ 2 ≤ (L / 2) ^ 2 := by
            rw [sq_le_sq, abs_of_nonneg hL2]
            exact hj
          rwa [Real.norm_eq_abs, sq_abs]
      _ = 3 * (L / 2) ^ 2 := by simp
      _ = (Real.sqrt 3 * (L / 2)) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  have := (sq_le_sq.mp h2)
  rwa [abs_of_nonneg (norm_nonneg _),
    abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg 3) hL2)] at this

/-- **Packing bound for the cutoff cube**: a finite family of points of the axis-parallel cube of
side `L` centred at `c`, pairwise at distance `≥ r`, with `r ≤ L / 16`, has at most `64 L³/r³`
members.  (The balls of radius `r/2` around the points are disjoint and lie in a ball of radius
`√3 L/2 + r/2`; only the exponent `3` and the size of the constant are used.) -/
private theorem capPackCubeCardLe {ι : Type*} (S : Finset ι)
    (y : ι → EuclideanSpace ℝ (Fin 3)) {c : EuclideanSpace ℝ (Fin 3)} {L r : ℝ}
    (hL : 0 < L) (hr : 0 < r) (hrL : r ≤ L / 16)
    (hcube : ∀ i ∈ S, ∀ j : Fin 3, |(y i - c).ofLp j| ≤ L / 2)
    (hsep : ∀ i ∈ S, ∀ i' ∈ S, i ≠ i' → r ≤ dist (y i) (y i')) :
    (S.card : ℝ) ≤ 64 * (L ^ 3 / r ^ 3) := by
  have hR0 : (0 : ℝ) ≤ Real.sqrt 3 * (L / 2) :=
    mul_nonneg (Real.sqrt_nonneg 3) (by linarith)
  have hsep' : ∀ i j : {i // i ∈ S}, i ≠ j →
      r ≤ ‖(y i.1 - c) - (y j.1 - c)‖ := by
    intro i j hij
    have h := hsep i.1 i.2 j.1 j.2 (by simpa using hij)
    rw [dist_eq_norm] at h
    rwa [sub_sub_sub_cancel_right]
  have hnorm : ∀ i : {i // i ∈ S}, ‖y i.1 - c‖ ≤ Real.sqrt 3 * (L / 2) :=
    fun i => norm_sub_le_sqrt_three_half (hcube i.1 i.2)
  have hle := Work.BoseBogFS.card_le_of_separated (fun i : {i // i ∈ S} => y i.1 - c)
    (δ := r) (r := Real.sqrt 3 * (L / 2)) hr hR0 hsep' hnorm
  rw [Finset.card_univ, Fintype.card_coe] at hle
  have hbase : Real.sqrt 3 * (2 * (Real.sqrt 3 * (L / 2)) / r) + 2 = 3 * (L / r) + 2 := by
    have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
    have hmain : Real.sqrt 3 * (2 * (Real.sqrt 3 * (L / 2)) / r) = 3 * (L / r) := by
      calc Real.sqrt 3 * (2 * (Real.sqrt 3 * (L / 2)) / r)
          = (Real.sqrt 3 * Real.sqrt 3) * (2 * (L / 2)) / r := by ring
        _ = 3 * (2 * (L / 2)) / r := by rw [h3]
        _ = 3 * (L / r) := by ring
    rw [hmain]
  rw [hbase] at hle
  have hLr : (16 : ℝ) ≤ L / r := by
    rw [le_div_iff₀ hr]
    linarith
  have hlin : 3 * (L / r) + 2 ≤ 4 * (L / r) := by linarith
  have hnonneg : (0 : ℝ) ≤ 3 * (L / r) + 2 := by linarith
  refine le_trans hle (le_trans (pow_le_pow_left₀ hnonneg hlin 3) ?_)
  rw [mul_pow, div_pow]
  norm_num

/-- The pointwise (a.e.) count bound: at an a.e. configuration with `Φ ≠ 0` the cutoff support
carries at most `64 (ℓd)³/r³` particles, by `pairSepAeB1` (pairwise `r`-separation) and the
`ℝ³`-packing lemma `capPackCubeCardLe`. -/
theorem capCount_ae_le {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) {R r : ℝ} (hR : 0 < R) (hr : 0 < r)
    (hrR : r ≤ R)
    (hball : Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) r ⊆ Function.support v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hRℓ : R ≤ ℓ * d / 16) (hRχ : R ≤ ℓ * Submission.BoseGases.chiR0)
    (hden : ∀ z : EuclideanSpace ℝ (Fin 3), ‖z‖ ≤ R →
      1 / 2 ≤ Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi
        (ℓ⁻¹ • z))
    {u : EuclideanSpace ℝ (Fin 3)} {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ}
    (hΦc : Continuous Φ)
    (hpair : Work.BoseFixB1.pairSum v M ℓ d u Φ = 0) :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)),
      (∑ i : Fin n, (Φ x) ^ 2 *
          (Function.support (Submission.BoseGases.chiSmallB M ℓ d u)).indicator
            (fun _ => (1 : ℝ)) (x i))
        ≤ (64 * ((ℓ * d) ^ 3 / r ^ 3)) * (Φ x) ^ 2 := by
  classical
  have hsepae := pairSepAeB1 (v := v) h hv hv1 hR hr hrR hball hv_supp hM hℓ hd hRℓ hRχ hden
    hΦc hpair
  filter_upwards [hsepae] with x hx
  by_cases h0 : Φ x = 0
  · simp [h0]
  · have hcount : (∑ i : Fin n, (Function.support
            (Submission.BoseGases.chiSmallB M ℓ d u)).indicator (fun _ => (1 : ℝ)) (x i))
        ≤ 64 * ((ℓ * d) ^ 3 / r ^ 3) := by
      have h1 : (∑ i : Fin n, (Function.support
              (Submission.BoseGases.chiSmallB M ℓ d u)).indicator (fun _ => (1 : ℝ)) (x i))
          = ((Finset.univ.filter (fun i : Fin n =>
              x i ∈ Function.support (Submission.BoseGases.chiSmallB M ℓ d u))).card : ℝ) := by
        rw [← Finset.sum_boole
          (fun i : Fin n => x i ∈ Function.support (Submission.BoseGases.chiSmallB M ℓ d u))
          Finset.univ]
        exact Finset.sum_congr rfl (fun i _ => by rw [Set.indicator_apply])
      rw [h1]
      refine capPackCubeCardLe (S := Finset.univ.filter (fun i : Fin n =>
          x i ∈ Function.support (Submission.BoseGases.chiSmallB M ℓ d u))) (y := x)
        (c := (ℓ * d) • u) (L := ℓ * d) (r := r) (by positivity) hr (by linarith) ?_ ?_
      · intro i hi j
        have hne : Submission.BoseGases.chiSmallB M ℓ d u (x i) ≠ 0 :=
          Function.mem_support.mp (Finset.mem_filter.mp hi).2
        exact Submission.BoseGases.chiSmallB_support_small_box_dist hM hℓ hd hne j
      · intro i hi i' hi' hne'
        have h1' : Submission.BoseGases.chiSmallB M ℓ d u (x i) ≠ 0 :=
          Function.mem_support.mp (Finset.mem_filter.mp hi).2
        have h2' : Submission.BoseGases.chiSmallB M ℓ d u (x i') ≠ 0 :=
          Function.mem_support.mp (Finset.mem_filter.mp hi').2
        exact hx h0 i i' hne' h1' h2'
    calc (∑ i : Fin n, (Φ x) ^ 2 * (Function.support
            (Submission.BoseGases.chiSmallB M ℓ d u)).indicator (fun _ => (1 : ℝ)) (x i))
        = (Φ x) ^ 2 * (∑ i : Fin n, (Function.support
            (Submission.BoseGases.chiSmallB M ℓ d u)).indicator (fun _ => (1 : ℝ)) (x i)) := by
          rw [Finset.mul_sum]
      _ ≤ (Φ x) ^ 2 * (64 * ((ℓ * d) ^ 3 / r ^ 3)) :=
          mul_le_mul_of_nonneg_left hcount (sq_nonneg _)
      _ = (64 * ((ℓ * d) ^ 3 / r ^ 3)) * (Φ x) ^ 2 := by ring

theorem capCountPackB1 {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) {R r : ℝ} (hR : 0 < R) (hr : 0 < r)
    (hrR : r ≤ R)
    (hball : Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) r ⊆ Function.support v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hRℓ : R ≤ ℓ * d / 16) (hRχ : R ≤ ℓ * Submission.BoseGases.chiR0)
    (hden : ∀ z : EuclideanSpace ℝ (Fin 3), ‖z‖ ≤ R →
      1 / 2 ≤ Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi
        (ℓ⁻¹ • z))
    {u : EuclideanSpace ℝ (Fin 3)} {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ}
    (hΦc : Continuous Φ)
    (hpair : Work.BoseFixB1.pairSum v M ℓ d u Φ = 0) :
    ∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
        (Φ x) ^ 2 * (Function.support (Submission.BoseGases.chiSmallB M ℓ d u)).indicator
          (fun _ => (1 : ℝ)) (x i)
      ≤ 64 * ((ℓ * d) ^ 3 / r ^ 3)
          * ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 := by
  classical
  have hA : MeasurableSet (Function.support (Submission.BoseGases.chiSmallB M ℓ d u)) :=
    measurableSet_support_chiSmallB hM u
  have hInti : ∀ i : Fin n, MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X n => (Φ x) ^ 2 *
        (Function.support (Submission.BoseGases.chiSmallB M ℓ d u)).indicator
          (fun _ => (1 : ℝ)) (x i))
      (Submission.BoseGases.abox n ℓ) :=
    fun i => integrableOn_sq_indicator_abox hℓ hA hΦc i
  have hInt2 : MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X n => (Φ x) ^ 2) (Submission.BoseGases.abox n ℓ) :=
    integrableOn_sq_abox hℓ hΦc
  have hae := capCount_ae_le (v := v) h hv hv1 hR hr hrR hball hv_supp hM hℓ hd hRℓ hRχ hden
    hΦc hpair
  calc ∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
        (Φ x) ^ 2 * (Function.support (Submission.BoseGases.chiSmallB M ℓ d u)).indicator
          (fun _ => (1 : ℝ)) (x i)
      = ∫ x in Submission.BoseGases.abox n ℓ, ∑ i : Fin n,
          (Φ x) ^ 2 * (Function.support (Submission.BoseGases.chiSmallB M ℓ d u)).indicator
            (fun _ => (1 : ℝ)) (x i) :=
        (MeasureTheory.integral_finsetSum Finset.univ (fun i _ => hInti i)).symm
    _ ≤ ∫ x in Submission.BoseGases.abox n ℓ,
          (64 * ((ℓ * d) ^ 3 / r ^ 3)) * (Φ x) ^ 2 :=
        MeasureTheory.integral_mono_ae
          (MeasureTheory.integrable_finsetSum Finset.univ (fun i _ => hInti i))
          (hInt2.const_mul _) hae
    _ = 64 * ((ℓ * d) ^ 3 / r ^ 3)
          * ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 := by
        rw [MeasureTheory.integral_const_mul]

end

end Work.BoseFixB1S
