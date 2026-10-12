import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.aemeasurable_boxQInd_sliding
import Submission.Work.BoseFixB1.boxP_dlBox_abs_le
import Submission.Work.BoseFixB1.chiB_unifDeriv
import Submission.Work.BoseFixB1.tBdiagFormInd_abs_bound_of_decay
import Submission.Work.BoseFixB1.tBwordBInd_eq_zero_of_farSet
import Submission.Work.SlotWord.abs_boxQInd_le_of_bound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1

open MeasureTheory

set_option maxHeartbeats 1000000

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 0. The degenerate case `a v ≤ 0`

At a non-positive scattering length FS's box side `ℓ = K_ℓ (μa)^{-1/2}` vanishes, and then so does
the whole small-box kinetic word (the gap coefficient `(2ℓd)⁻¹ε_T` and the slot-volume factor
`(ℓ³)⁻¹` both vanish).  Hence `sbKin ≡ 0` and the integrability is trivial. -/

/-- `x ↦ x ^ (-(1/2))` vanishes on the nonpositive half-line (for `x < 0` the value is
`exp (log x * (-1/2)) * cos (π/2) = 0`, and `0 ^ (-(1/2)) = 0`). -/
lemma rpow_neg_half_eq_zero_of_nonpos {x : ℝ} (hx : x ≤ 0) : x ^ (-(1 / 2 : ℝ)) = 0 := by
  rcases lt_or_eq_of_le hx with h | h
  · rw [Real.rpow_def_of_neg h]
    have : (-(1 / 2 : ℝ)) * Real.pi = -(Real.pi / 2) := by ring
    rw [this, Real.cos_neg, Real.cos_pi_div_two, mul_zero]
  · subst h
    exact Real.zero_rpow (by norm_num)

/-- **The box side vanishes at a non-positive scattering length**: FS's `ℓ = K_ℓ (μa)^{-1/2}`. -/
lemma sideAt_eq_zero_of_nonpos {μ a : ℝ} (hμ : 0 ≤ μ) (ha : a ≤ 0) :
    Work.BoseBox.sideAt μ a = 0 := by
  rw [Work.BoseFixB1.sideAt_eq]
  have hμa : μ * a ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hμ ha
  rw [rpow_neg_half_eq_zero_of_nonpos hμa, mul_zero]

/-- **In the degenerate case `a v ≤ 0` the small-box word is identically zero**: the box side
`ℓ = sideAt μ (a v)` vanishes, so the gap coefficient `(2ℓd)⁻¹ε_T` and the slot-volume factor
`(ℓ³)⁻¹` of the spectral half both vanish. -/
lemma sbKin_eq_zero_of_sideAt_eq_zero {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ} {M n : ℕ}
    {u : EuclideanSpace ℝ (Fin 3)}
    (hℓ : Work.BoseBox.sideAt μ (_root_.BoseGases.a v) = 0)
    (Φ : Submission.BoseGases.X n → ℝ) :
    sbKin (v := v) μ M u Φ = 0 := by
  unfold sbKin Work.UBBInputs8.tBwordBInd Work.UBBInputs8.tBwordInd
    Work.UBBInputs8.tBwordKinInd Work.UBBInputs8.tBdiagFormInd
    Work.SmallBoxTBWord.tbGapCoeff Work.SmallBoxTBWord.tbPiFactor
  rw [hℓ]
  simp

/-! ## 1. Elementary parameter facts in the regime `0 < a v` -/

lemma paramsAt_d_pos {μ a : ℝ} (hμ : 0 < μ) (ha : 0 < a) :
    0 < (Work.BoseBox.paramsAt μ a).d :=
  Real.rpow_pos_of_pos (mul_pos hμ (pow_pos ha 3)) _

lemma sideAt_pos_of_pos {μ a : ℝ} (hμ : 0 < μ) (ha : 0 < a) :
    0 < Work.BoseBox.sideAt μ a := by
  rw [Work.BoseFixB1.sideAt_eq]
  exact mul_pos (Real.rpow_pos_of_pos (mul_pos hμ (pow_pos ha 3)) _)
    (Real.rpow_pos_of_pos (mul_pos hμ ha) _)

/-! ## 2. The supporting region `goodSet ℓ d 0`

The word vanishes as soon as the sliding box `B(u)` is empty, i.e. off the closure of the set of
admissible sliding centres, which is the bounded set `goodSet ℓ d 0`. -/

/-- A vector all of whose coordinates are bounded by `C` has norm at most `√3 · C`. -/
lemma norm_le_sqrt3_mul {C : ℝ} (hC : 0 ≤ C) {y : EuclideanSpace ℝ (Fin 3)}
    (hy : ∀ k : Fin 3, |y k| ≤ C) : ‖y‖ ≤ Real.sqrt 3 * C := by
  have hb : 0 ≤ Real.sqrt 3 * C := by positivity
  apply le_of_sq_le_sq
  · rw [EuclideanSpace.real_norm_sq_eq]
    calc ∑ k : Fin 3, (y k) ^ 2 ≤ ∑ _k : Fin 3, C ^ 2 := by
          refine Finset.sum_le_sum (fun k _ => ?_)
          exact sq_le_sq.mpr (by simpa [abs_of_nonneg hC] using hy k)
      _ = 3 * C ^ 2 := by norm_num
      _ = (Real.sqrt 3 * C) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  · exact hb

/-- A configuration of the centred box `abox n ℓ` has all coordinates of norm at most `ℓ`. -/
lemma norm_le_of_mem_abox {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {x : Submission.BoseGases.X n}
    (hx : x ∈ Submission.BoseGases.abox n ℓ) (j : Fin n) : ‖x j‖ ≤ ℓ := by
  have hmem : x j ∈ Submission.BoseGases.acube ℓ :=
    (Submission.BoseGases.mem_abox_iff n ℓ x).mp hx j
  have hcoord : ∀ m : Fin 3, |(x j) m| ≤ ℓ / 2 := by
    intro m
    have h2 := hmem m
    rw [Set.mem_Icc] at h2
    rw [abs_le]
    exact ⟨by linarith [h2.1], by linarith [h2.2]⟩
  have h1 : ‖x j‖ ≤ Real.sqrt 3 * (ℓ / 2) := norm_le_sqrt3_mul (by positivity) hcoord
  have h3 : Real.sqrt 3 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg 3]
  nlinarith [h1, h3, hℓ]

/-- **The sliding region `goodSet ℓ d 0` is bounded.**  On it, `|(ℓd) u_j| ≤ ½ℓ(1+d)`, hence
`|u_j| ≤ (1+d)/(2d)` and `‖u‖ ≤ √3 (1+d)/(2d)`. -/
lemma goodSet_zero_subset_closedBall {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) :
    Work.SmallBoxSliding.goodSet ℓ d 0 ⊆
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) (Real.sqrt 3 * ((1 + d) / (2 * d))) := by
  intro u hu
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
  refine norm_le_sqrt3_mul (by positivity) (fun k => ?_)
  have h := hu k
  have hld : 0 < ℓ * d := mul_pos hℓ hd
  have hzero : (0 : ℝ) ^ (-1 / 3 : ℝ) = 0 := Real.zero_rpow (by norm_num)
  rw [hzero, sub_zero] at h
  have hsmul : ((ℓ * d) • u).ofLp k = (ℓ * d) * u.ofLp k := by simp
  rw [hsmul, abs_mul, abs_of_nonneg hld.le] at h
  have h3 : |u.ofLp k| ≤ (1 + d) / (2 * d) := by
    rw [le_div_iff₀ (by positivity)]
    have h2 : d * |u.ofLp k| ≤ (1 + d) / 2 := by
      nlinarith [h, hℓ]
    nlinarith [h2, hd]
  exact h3

lemma volume_goodSet_zero_lt_top {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) :
    (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))
      (Work.SmallBoxSliding.goodSet ℓ d 0) < ⊤ := by
  refine lt_of_le_of_lt (measure_mono (goodSet_zero_subset_closedBall hℓ hd)) ?_
  exact (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 3))
    (Real.sqrt 3 * ((1 + d) / (2 * d)))).measure_lt_top

/-- Off `goodSet ℓ d 0` the sliding box has no admissible centre, i.e. the point lies in `farSet`. -/
lemma mem_farSet_of_notMem_goodSet {ℓ d : ℝ} {u : EuclideanSpace ℝ (Fin 3)}
    (hu : u ∉ Work.SmallBoxSliding.goodSet ℓ d 0) :
    u ∈ Work.SmallBoxSliding.farSet ℓ d 0 := by
  rw [Work.SmallBoxSliding.mem_farSet_iff]
  by_contra hc
  push_neg at hc
  exact hu (fun j => by
    have h := hc j
    have hzero : (0 : ℝ) ^ (-1 / 3 : ℝ) = 0 := Real.zero_rpow (by norm_num)
    rw [hzero, sub_zero]
    exact h)

/-! ## 3. Bounds on the gap half of the word -/

/-- Pointwise bound on FS's box mean-free projection in the sliding geometry, for a state bounded
on the ambient box: the box mean is a mean, so it costs at most `M` again.

**File-local on purpose** (`private`): the *general-box* version of this bound, with the same
name, lives in `Submission/Work/BoseFixB1/BoxPairIntGenC2/boxC2SumC2.lean` (namespace
`Work.BoseFixB1`) and is exported to `BoseFixB1S/boxC2SumC.lean` and
`BoseFixB1S/boxPair_perPairC.lean`; two same-named declarations in one namespace made the two
import cones mutually unimportable (so `chainCore` + `boxFramePGen`, hence the localised D1
assembly `boxSimpleA2TwoWindowSharp`, could not even be stated). This copy is used only here. -/
private lemma abs_boxQInd_le_two_mul {n : ℕ} {ℓ d M : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    {Φ : Submission.BoseGases.X n → ℝ}
    (hM : ∀ x : Submission.BoseGases.X n,
      (∀ j : Fin n, x j ∈ Submission.BoseGases.acube ℓ) → |Φ x| ≤ M)
    (i : Fin n) (u : EuclideanSpace ℝ (Fin 3)) (x : Submission.BoseGases.X n)
    (hx : ∀ j : Fin n, x j ∈ Submission.BoseGases.acube ℓ) :
    |Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
      (Submission.BoseGases.dlBox ℓ d u) i Φ x| ≤ 2 * M := by
  have hM0 : 0 ≤ M := by
    have h1 : |Φ (fun _ => (0 : EuclideanSpace ℝ (Fin 3)))| ≤ M :=
      hM _ (fun j => Submission.BoseGases.mem_acube_of_norm_le hℓ.le (by rw [norm_zero]; linarith))
    exact le_trans (abs_nonneg _) h1
  have h := Work.SlotWord.abs_boxQInd_le_of_bound (L := ℓ)
    (A := Submission.BoseGases.dlBox ℓ d u) (Work.SmallBoxSliding.dlBox_subset_acube ℓ d u)
    (volA := Work.SmallBoxSliding.boxMass ℓ d u) hM0
    (Work.SmallBoxSliding.volume_dlBox_lt_top hℓ d u) hM i x hx
  have hB : Work.SmallBoxSliding.boxMass ℓ d u
      = (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).real
          (Submission.BoseGases.dlBox ℓ d u) :=
    Work.SmallBoxSliding.boxMass_eq_measureReal ℓ d u
  have hBnn : 0 ≤ Work.SmallBoxSliding.boxMass ℓ d u := by
    rw [hB]; exact MeasureTheory.measureReal_nonneg
  have hterm : |Work.SmallBoxSliding.boxMass ℓ d u|⁻¹
      * (M * (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).real
          (Submission.BoseGases.dlBox ℓ d u)) ≤ M := by
    rw [abs_of_nonneg hBnn, ← hB]
    rcases eq_or_lt_of_le hBnn with h0 | h0
    · rw [← h0, inv_zero, zero_mul]; exact hM0
    · rw [mul_comm M (Work.SmallBoxSliding.boxMass ℓ d u), ← mul_assoc,
        inv_mul_cancel₀ (ne_of_gt h0), one_mul]
  linarith

/-- **The gap half of the sliding word is uniformly bounded** (in the sliding centre `u`). -/
lemma cnPlusBoxInd_abs_bound {n : ℕ} {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : Continuous Φ) :
    ∃ K : ℝ, ∀ u : EuclideanSpace ℝ (Fin 3),
      |Work.UBBInputs8.cnPlusBoxInd ℓ (Submission.BoseGases.dlBox ℓ d u)
        (Work.SmallBoxSliding.boxMass ℓ d u) Φ| ≤ K := by
  obtain ⟨M, hM⟩ := (Submission.BoseGases.abox_compact n hℓ).exists_bound_of_continuousOn
    hΦ.norm.continuousOn
  have hM' : ∀ x : Submission.BoseGases.X n,
      (∀ j : Fin n, x j ∈ Submission.BoseGases.acube ℓ) → |Φ x| ≤ M := by
    intro x hx
    have hx' : x ∈ Submission.BoseGases.abox n ℓ :=
      (Submission.BoseGases.mem_abox_iff n ℓ x).mpr hx
    simpa only [Real.norm_eq_abs, abs_abs] using hM x hx'
  refine ⟨(n : ℝ) * ((2 * M) ^ 2
    * (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).real
        (Submission.BoseGases.abox n ℓ)), fun u => ?_⟩
  have hb : ∀ (i : Fin n) (x : Submission.BoseGases.X n),
      (∀ j : Fin n, x j ∈ Submission.BoseGases.acube ℓ) →
      |Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
        (Submission.BoseGases.dlBox ℓ d u) i Φ x| ≤ 2 * M :=
    fun i x hx => abs_boxQInd_le_two_mul hℓ hd hM' i u x hx
  calc |∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
          (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) i Φ x) ^ 2|
      ≤ ∑ i : Fin n, |∫ x in Submission.BoseGases.abox n ℓ,
          (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) i Φ x) ^ 2| :=
          Finset.abs_sum_le_sum_abs _ Finset.univ
    _ ≤ ∑ _i : Fin n, ((2 * M) ^ 2
          * (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).real
              (Submission.BoseGases.abox n ℓ)) := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        have h := MeasureTheory.norm_setIntegral_le_of_norm_le_const
          (μ := (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)))
          (f := fun x : Submission.BoseGases.X n =>
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) i Φ x) ^ 2)
          (C := (2 * M) ^ 2)
          (Submission.BoseGases.abox_compact n hℓ).measure_lt_top
          (fun x hx => by
            have hx' : ∀ j : Fin n, x j ∈ Submission.BoseGases.acube ℓ :=
              (Submission.BoseGases.mem_abox_iff n ℓ x).mp hx
            rw [Real.norm_eq_abs, abs_pow]
            exact pow_le_pow_left₀ (abs_nonneg _) (hb i x hx') 2)
        simpa only [Real.norm_eq_abs] using h
    _ = (n : ℝ) * ((2 * M) ^ 2
          * (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).real
              (Submission.BoseGases.abox n ℓ)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-! ## 4. The uniform rapid decay of the sliding amplitude

FS's sliding amplitude `tBamp (χ_{B(u)}) p (Q_{B(u),i}Φ) i x` is the Fourier transform of a
compactly supported smooth function, so it decays like `(1+‖p‖)⁻³`, *uniformly* in the sliding
centre `u`, in `x ∈ abox n ℓ`, in the slot and in `p`.  The mechanism is the FS decomposition
`Q_{B,i}Φ = 1_BΦ − P_{B,i}Φ` (`Work.BoseBox.tBamp_boxQInd_eq_sub`), which reduces the amplitude
to the amplitude of the fixed smooth state `Φ` and the amplitude of the constant state, together
with the scalar box mean. -/

/-- **Uniform rapid decay of the sliding amplitude**, from the (uniform) window derivative data
and the (uniform) bound on the box mean. -/
lemma tBamp_chiB_boxQInd_decay_of_data {n : ℕ} {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ)
    {R : ℝ} (hR : 0 < R) {G : ℕ → ℝ} (hG0 : ∀ k, 0 ≤ G k)
    (hGsupp : ∀ (u z : EuclideanSpace ℝ (Fin 3)), Submission.BoseGases.chiB ℓ d u z ≠ 0 →
      ‖z‖ ≤ R)
    (hGderiv : ∀ (u : EuclideanSpace ℝ (Fin 3)) (k : ℕ), k ≤ 3 →
      ∀ z : EuclideanSpace ℝ (Fin 3),
      ‖iteratedFDeriv ℝ k (fun z => (Submission.BoseGases.chiB ℓ d u z : ℂ)) z‖ ≤ G k)
    {M₀ : ℝ}
    (hM₀ : ∀ (u : EuclideanSpace ℝ (Fin 3)) (x : Submission.BoseGases.X n),
      x ∈ Submission.BoseGases.abox n ℓ → ∀ i : Fin n,
      |Work.SmallBoxTBWord.boxP (Work.SmallBoxSliding.boxMass ℓ d u)
        (Submission.BoseGases.dlBox ℓ d u) i Φ (Function.update x i 0)| ≤ M₀) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (u : EuclideanSpace ℝ (Fin 3)) (x : Submission.BoseGases.X n),
        x ∈ Submission.BoseGases.abox n ℓ → ∀ (i : Fin n) (p : EuclideanSpace ℝ (Fin 3)),
        ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiB ℓ d u) p
          (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) i Φ) i x‖ ≤ C / (1 + ‖p‖) ^ 3 := by
  set S : ℝ := max R ℓ with hSdef
  have hS0 : 0 ≤ S := le_trans hR.le (le_max_left _ _)
  have hRS : R ≤ S := le_max_left _ _
  have hℓS : ℓ ≤ S := le_max_right _ _
  obtain ⟨M, hMnn, hMb⟩ :=
    Work.SmallBoxTBWord.complexified_iteratedFDeriv_bound (N := n) (S := S) hS0 hΦ
  obtain ⟨M₁, hM₁nn, hM₁b⟩ :=
    Work.SmallBoxTBWord.complexified_iteratedFDeriv_bound (N := n) (S := S) hS0
      (contDiff_const : ContDiff ℝ (⊤ : ENat) (fun _ : Submission.BoseGases.X n => (1 : ℝ)))
  have hχcd : ∀ u : EuclideanSpace ℝ (Fin 3),
      ContDiff ℝ 3 (fun z => (Submission.BoseGases.chiB ℓ d u z : ℂ)) := fun u =>
    Complex.ofRealCLM.contDiff.comp
      ((Work.SmallBoxTBWord.contDiff_chiB hℓ hd u).of_le (WithTop.coe_le_coe.mpr le_top))
  have hΦcd : ContDiff ℝ 3 (fun y : Submission.BoseGases.X n => (Φ y : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hΦ.of_le (WithTop.coe_le_coe.mpr le_top))
  have h1cd : ContDiff ℝ 3 (fun y : Submission.BoseGases.X n => ((1 : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp
      (contDiff_const.of_le (WithTop.coe_le_coe.mpr le_top))
  obtain ⟨C₁, hC₁nn, hC₁⟩ := Work.BoseBox.tBampDecayUniform (N := n) hR hRS
    (χ := fun t : EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.chiB ℓ d t)
    (Φ := fun _ : EuclideanSpace ℝ (Fin 3) => Φ) (G := G) (M := M)
    (fun t => hχcd t) (fun t z => hGsupp t z) (fun t k hk z => hGderiv t k hk z)
    (fun _ => hΦcd) (fun _ k hk y hy => hMb k hk y hy)
  obtain ⟨C₂, hC₂nn, hC₂⟩ := Work.BoseBox.tBampDecayUniform (N := n) hR hRS
    (χ := fun t : EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.chiB ℓ d t)
    (Φ := fun _ : EuclideanSpace ℝ (Fin 3) =>
      (fun _ : Submission.BoseGases.X n => (1 : ℝ))) (G := G) (M := M₁)
    (fun t => hχcd t) (fun t z => hGsupp t z) (fun t k hk z => hGderiv t k hk z)
    (fun _ => h1cd) (fun _ k hk y hy => hM₁b k hk y hy)
  refine ⟨C₁ + |M₀| * C₂, add_nonneg hC₁nn (mul_nonneg (abs_nonneg M₀) hC₂nn), ?_⟩
  intro u x hx i p
  have hxS : ∀ j : Fin n, ‖x j‖ ≤ S := by
    intro j
    exact le_trans (norm_le_of_mem_abox hℓ hx j) hℓS
  have hdec := Work.BoseBox.tBamp_boxQInd_eq_sub
    (volA := Work.SmallBoxSliding.boxMass ℓ d u) (A := Submission.BoseGases.dlBox ℓ d u)
    (χ := Submission.BoseGases.chiB ℓ d u) Φ i p x 0
    (fun z hz => by
      by_contra hne
      exact hz (Work.UBBInputs9.A.tsupport_chiB_subset_dlBox hℓ hd u
        (subset_tsupport _ hne)))
    (Work.SmallBoxTBWord.contDiff_chiB hℓ hd u).continuous
    (Work.SmallBoxTBWord.hasCompactSupport_chiB hℓ hd u) hΦ.continuous
  have hm : ‖((Work.SmallBoxTBWord.boxP (Work.SmallBoxSliding.boxMass ℓ d u)
      (Submission.BoseGases.dlBox ℓ d u) i Φ (Function.update x i 0) : ℝ) : ℂ)‖ ≤ |M₀| := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact le_trans (hM₀ u x hx i) (le_abs_self M₀)
  rw [hdec]
  calc ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiB ℓ d u) p Φ i x
        - ((Work.SmallBoxTBWord.boxP (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) i Φ (Function.update x i 0) : ℝ) : ℂ)
          * Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiB ℓ d u) p
              (fun _ : Submission.BoseGases.X n => (1 : ℝ)) i x‖
      ≤ ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiB ℓ d u) p Φ i x‖
        + ‖((Work.SmallBoxTBWord.boxP (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) i Φ (Function.update x i 0) : ℝ) : ℂ)
          * Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiB ℓ d u) p
              (fun _ : Submission.BoseGases.X n => (1 : ℝ)) i x‖ :=
        norm_sub_le _ _
    _ = ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiB ℓ d u) p Φ i x‖
        + ‖((Work.SmallBoxTBWord.boxP (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) i Φ (Function.update x i 0) : ℝ) : ℂ)‖
          * ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiB ℓ d u) p
              (fun _ : Submission.BoseGases.X n => (1 : ℝ)) i x‖ := by
        rw [norm_mul]
    _ ≤ C₁ / (1 + ‖p‖) ^ 3 + |M₀| * (C₂ / (1 + ‖p‖) ^ 3) := by
        refine add_le_add (hC₁ u x hxS i p) ?_
        exact mul_le_mul hm (hC₂ u x hxS i p) (norm_nonneg _) (abs_nonneg M₀)
    _ = (C₁ + |M₀| * C₂) / (1 + ‖p‖) ^ 3 := by ring

/-- **Uniform rapid decay of the sliding amplitude** (the instantiation of
`tBamp_chiB_boxQInd_decay_of_data` at FS's sliding window `chiB ℓ d u`, whose uniform derivative
data is `chiB_unifDeriv` and whose box-mean data is `boxP_dlBox_abs_le`). -/
lemma tBamp_chiB_boxQInd_decay {n : ℕ} {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (u : EuclideanSpace ℝ (Fin 3)) (x : Submission.BoseGases.X n),
        x ∈ Submission.BoseGases.abox n ℓ → ∀ (i : Fin n) (p : EuclideanSpace ℝ (Fin 3)),
        ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiB ℓ d u) p
          (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) i Φ) i x‖ ≤ C / (1 + ‖p‖) ^ 3 := by
  obtain ⟨R, hR, G, hG0, hsupp, hderiv⟩ := chiB_unifDeriv (ℓ := ℓ) (d := d) hℓ hd
  obtain ⟨M, hM⟩ := (Submission.BoseGases.abox_compact n hℓ).exists_bound_of_continuousOn
    hΦ.continuous.norm.continuousOn
  have hM' : ∀ x : Submission.BoseGases.X n,
      (∀ j : Fin n, x j ∈ Submission.BoseGases.acube ℓ) → |Φ x| ≤ M := by
    intro x hx
    have hx' : x ∈ Submission.BoseGases.abox n ℓ :=
      (Submission.BoseGases.mem_abox_iff n ℓ x).mpr hx
    simpa only [Real.norm_eq_abs, abs_abs] using hM x hx'
  exact tBamp_chiB_boxQInd_decay_of_data hℓ hd hΦ hR hG0 hsupp hderiv (M₀ := M)
    (fun u x hx i => boxP_dlBox_abs_le hℓ hd hM' i u x 0
      ((Submission.BoseGases.mem_abox_iff n ℓ x).mp hx))

/-! ## 5. The bound and the measurability of the whole word -/

/-- **The small-box word is uniformly bounded.** -/
lemma tBwordBInd_abs_bound {n : ℕ} {ℓ d ε c : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ) :
    ∃ K : ℝ, ∀ u : EuclideanSpace ℝ (Fin 3),
      |Work.UBBInputs8.tBwordBInd n ℓ d ε c u Φ| ≤ K := by
  obtain ⟨K₁, hK₁⟩ := cnPlusBoxInd_abs_bound (n := n) hℓ hd hΦ.continuous
  obtain ⟨C, hC0, hdec⟩ := tBamp_chiB_boxQInd_decay (n := n) (ℓ := ℓ) (d := d) hℓ hd hΦ
  obtain ⟨K₂, hK₂⟩ :=
    Work.BoseFixB1.tBdiagFormInd_abs_bound_of_decay (n := n) (ℓ := ℓ) (d := d) hℓ
      (Φ := Φ) hC0 hdec c
  refine ⟨|Work.SmallBoxTBWord.tbGapCoeff (ℓ * d) ε| * K₁ + K₂, fun u => ?_⟩
  have hgap : |Work.SmallBoxTBWord.tbGapCoeff (ℓ * d) ε *
      Work.UBBInputs8.cnPlusBoxInd ℓ (Submission.BoseGases.dlBox ℓ d u)
        (Work.SmallBoxSliding.boxMass ℓ d u) Φ|
      ≤ |Work.SmallBoxTBWord.tbGapCoeff (ℓ * d) ε| * K₁ := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hK₁ u) (abs_nonneg _)
  have hdiag := hK₂ u
  have hsplit : Work.UBBInputs8.tBwordBInd n ℓ d ε c u Φ
      = Work.SmallBoxTBWord.tbGapCoeff (ℓ * d) ε *
          Work.UBBInputs8.cnPlusBoxInd ℓ (Submission.BoseGases.dlBox ℓ d u)
            (Work.SmallBoxSliding.boxMass ℓ d u) Φ
        + Work.UBBInputs8.tBdiagFormInd ℓ (Submission.BoseGases.dlBox ℓ d u)
            (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.chiB ℓ d u)
            (Submission.BoseGases.fsKinCoeff c) Φ := rfl
  rw [hsplit]
  exact le_trans (abs_add_le _ _) (add_le_add hgap hdiag)


/-- **Joint measurability of the sliding spectral integrand.**  For a continuous state `Φ`, the
`(u,p)`-parametrised amplitude energy `∫_{abox n ℓ}‖tBamp (χ_{B(u)}) p (Q_{B(u),i}Φ) i x‖²` is
a.e. strongly measurable for `volume.prod volume`.

The proof runs at the single Fubini level of the space `S = ((u,p),x)` (whose last coordinate is
integrated out): the three ingredients of FS's decomposition
`Q_{B(u),i}Φ = 1_{B(u)}Φ − P_{B(u),i}Φ` — the box mass `boxMass ℓ d u`, the slot integral
`∫_{B(u)}Φ(update x i z)dz` and the amplitudes of the fixed states `Φ` and `1` — are each
a.e. strongly measurable in `s ∈ S` as marginals of *jointly measurable* kernels on `S × ℝ³`. -/
private lemma aemeasurable_diagIntegrand {n : ℕ} {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : Continuous Φ) (i : Fin n) :
    AEMeasurable
      (fun q : E3 × E3 =>
        ∫ x in Submission.BoseGases.abox n ℓ,
          ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiB ℓ d q.1) q.2
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d q.1)
              (Submission.BoseGases.dlBox ℓ d q.1) i Φ) i x‖ ^ 2)
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
  classical
  -- ## 0. The ambient measure on `S = ((u,p),x)`
  -- ## 1. The box volume `boxMass ℓ d u`, as a function of `s ∈ S`
  have hmass : AEMeasurable (fun s : (E3 × E3) × Submission.BoseGases.X n =>
      Work.SmallBoxSliding.boxMass ℓ d s.1.1)
      (((MeasureTheory.volume : MeasureTheory.Measure E3).prod MeasureTheory.volume).prod
        MeasureTheory.volume) := by
    have hboxInd : Measurable (fun t : ((E3 × E3) × Submission.BoseGases.X n) × E3 =>
        Work.SmallBoxSliding.boxInd ℓ d t.1.1.1 t.2) := by
      have hmap : Measurable (fun t : ((E3 × E3) × Submission.BoseGases.X n) × E3 =>
          (t.1.1.1, t.2)) :=
        (measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk measurable_snd
      have hset : MeasurableSet {t : ((E3 × E3) × Submission.BoseGases.X n) × E3 |
          t.2 ∈ Submission.BoseGases.dlBox ℓ d t.1.1.1} :=
        (Work.SmallBoxSliding.measurableSet_boxIndSet ℓ d).preimage hmap
      have hfun : (fun t : ((E3 × E3) × Submission.BoseGases.X n) × E3 =>
          Work.SmallBoxSliding.boxInd ℓ d t.1.1.1 t.2)
          = {t : ((E3 × E3) × Submission.BoseGases.X n) × E3 |
              t.2 ∈ Submission.BoseGases.dlBox ℓ d t.1.1.1}.indicator (fun _ => (1 : ℝ)) := by
        funext t
        rw [Work.SmallBoxSliding.boxInd]
        by_cases h : t.2 ∈ Submission.BoseGases.dlBox ℓ d t.1.1.1
        · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show t ∈ _ from h)]
        · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (show t ∉ _ from h)]
      rw [hfun]
      exact measurable_const.indicator hset
    have h := MeasureTheory.StronglyMeasurable.integral_prod_right'
      (ν := (MeasureTheory.volume : MeasureTheory.Measure E3)) hboxInd.stronglyMeasurable
    have hfun2 : (fun s : (E3 × E3) × Submission.BoseGases.X n =>
        ∫ z : E3, Work.SmallBoxSliding.boxInd ℓ d s.1.1 z)
        = fun s : (E3 × E3) × Submission.BoseGases.X n =>
            Work.SmallBoxSliding.boxMass ℓ d s.1.1 := by
      funext s; rw [Work.SmallBoxSliding.boxMass]
    rw [hfun2] at h
    exact h.aemeasurable
  -- ## 2. The slot integral `∫_{B(u)}Φ(update x i z)dz`, as a function of `s ∈ S`
  have hslot : AEMeasurable (fun s : (E3 × E3) × Submission.BoseGases.X n =>
      ∫ z in Submission.BoseGases.dlBox ℓ d s.1.1, Φ (Function.update s.2 i z))
      (((MeasureTheory.volume : MeasureTheory.Measure E3).prod MeasureTheory.volume).prod
        MeasureTheory.volume) := by
    have hjoint : Measurable (fun t : ((E3 × E3) × Submission.BoseGases.X n) × E3 =>
        (Submission.BoseGases.dlBox ℓ d t.1.1.1).indicator
          (fun z => Φ (Function.update t.1.2 i z)) t.2) := by
      have hmap : Measurable (fun t : ((E3 × E3) × Submission.BoseGases.X n) × E3 =>
          (t.1.1.1, t.2)) :=
        (measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk measurable_snd
      have hset : MeasurableSet {t : ((E3 × E3) × Submission.BoseGases.X n) × E3 |
          t.2 ∈ Submission.BoseGases.dlBox ℓ d t.1.1.1} :=
        (Work.SmallBoxSliding.measurableSet_boxIndSet ℓ d).preimage hmap
      have hupd : Measurable (fun t : ((E3 × E3) × Submission.BoseGases.X n) × E3 =>
          Function.update t.1.2 i t.2) :=
        (measurable_update' (a := i)).comp
          ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
      have hcomp : Measurable (fun t : ((E3 × E3) × Submission.BoseGases.X n) × E3 =>
          Φ (Function.update t.1.2 i t.2)) := hΦ.measurable.comp hupd
      have hite : (fun t : ((E3 × E3) × Submission.BoseGases.X n) × E3 =>
          (Submission.BoseGases.dlBox ℓ d t.1.1.1).indicator
            (fun z => Φ (Function.update t.1.2 i z)) t.2)
          = fun t => if t.2 ∈ Submission.BoseGases.dlBox ℓ d t.1.1.1
              then Φ (Function.update t.1.2 i t.2) else 0 := by
        funext t
        by_cases h : t.2 ∈ Submission.BoseGases.dlBox ℓ d t.1.1.1
        · rw [if_pos h, Set.indicator_of_mem h]
        · rw [if_neg h, Set.indicator_of_notMem h]
      rw [hite]
      exact Measurable.ite hset hcomp measurable_const
    have h := MeasureTheory.StronglyMeasurable.integral_prod_right'
      (ν := (MeasureTheory.volume : MeasureTheory.Measure E3)) hjoint.stronglyMeasurable
    refine h.aemeasurable.congr ?_
    filter_upwards with s
    rw [MeasureTheory.integral_indicator
      (Work.SmallBoxSliding.measurableSet_dlBox ℓ d s.1.1)]
  -- ## 3. The box mean `P_{B(u),i}Φ`, as a function of `s ∈ S`
  have hmean : AEMeasurable (fun s : (E3 × E3) × Submission.BoseGases.X n =>
      ((Work.SmallBoxTBWord.boxP (Work.SmallBoxSliding.boxMass ℓ d s.1.1)
        (Submission.BoseGases.dlBox ℓ d s.1.1) i Φ (Function.update s.2 i 0) : ℝ) : ℂ))
      (((MeasureTheory.volume : MeasureTheory.Measure E3).prod MeasureTheory.volume).prod
        MeasureTheory.volume) := by
    have hR : AEMeasurable (fun s : (E3 × E3) × Submission.BoseGases.X n =>
        Work.SmallBoxTBWord.boxP (Work.SmallBoxSliding.boxMass ℓ d s.1.1)
          (Submission.BoseGases.dlBox ℓ d s.1.1) i Φ (Function.update s.2 i 0))
        (((MeasureTheory.volume : MeasureTheory.Measure E3).prod MeasureTheory.volume).prod
          MeasureTheory.volume) := by
      have hfun : (fun s : (E3 × E3) × Submission.BoseGases.X n =>
          Work.SmallBoxTBWord.boxP (Work.SmallBoxSliding.boxMass ℓ d s.1.1)
            (Submission.BoseGases.dlBox ℓ d s.1.1) i Φ (Function.update s.2 i 0))
          = fun s => (Work.SmallBoxSliding.boxMass ℓ d s.1.1)⁻¹ *
              ∫ z in Submission.BoseGases.dlBox ℓ d s.1.1, Φ (Function.update s.2 i z) := by
        funext s
        rw [Work.SmallBoxTBWord.boxP]
        simp only [one_div, Function.update_idem]
      rw [hfun]
      exact (hmass.inv).mul hslot
    exact Complex.measurable_ofReal.comp_aemeasurable hR
  -- ## 4. The amplitudes of the fixed states `Φ` and `1`, as functions of `s ∈ S`
  have hamp : ∀ (Ψ : Submission.BoseGases.X n → ℝ), Continuous Ψ →
      AEMeasurable (fun s : (E3 × E3) × Submission.BoseGases.X n =>
        Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiB ℓ d s.1.1) s.1.2 Ψ i s.2)
      (((MeasureTheory.volume : MeasureTheory.Measure E3).prod MeasureTheory.volume).prod
        MeasureTheory.volume) := by
    intro Ψ hΨ
    have hchi_cont : Continuous (fun t : ((E3 × E3) × Submission.BoseGases.X n) × E3 =>
        Submission.BoseGases.chiB ℓ d t.1.1.1 t.2) := by
      unfold Submission.BoseGases.chiB
      refine ((Submission.BoseGases.chiScale_continuous ℓ).comp continuous_snd).mul ?_
      refine (Submission.BoseGases.chiScale_continuous (ℓ * d)).comp ?_
      exact continuous_snd.sub
        ((continuous_fst.comp (continuous_fst.comp continuous_fst)).const_smul
          (ℓ * d))
    have hupd : Measurable (fun t : ((E3 × E3) × Submission.BoseGases.X n) × E3 =>
        Function.update t.1.2 i t.2) :=
      (measurable_update' (a := i)).comp
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
    have hker : Measurable (fun t : ((E3 × E3) × Submission.BoseGases.X n) × E3 =>
        (Submission.BoseGases.chiB ℓ d t.1.1.1 t.2 : ℂ)
          * Complex.exp (-(Complex.I * (inner ℝ t.1.1.2 t.2 : ℂ)))
          * (Ψ (Function.update t.1.2 i t.2) : ℂ)) := by
      have hexp : Measurable (fun t : ((E3 × E3) × Submission.BoseGases.X n) × E3 =>
          Complex.exp (-(Complex.I * (inner ℝ t.1.1.2 t.2 : ℂ)))) := by
        have hcont : Continuous (fun t : ((E3 × E3) × Submission.BoseGases.X n) × E3 =>
            -(Complex.I * (inner ℝ t.1.1.2 t.2 : ℂ))) := by
          refine Continuous.neg ?_
          refine continuous_const.mul ?_
          exact Complex.continuous_ofReal.comp (by fun_prop)
        exact Complex.measurable_exp.comp hcont.measurable
      have hchi : Measurable (fun t : ((E3 × E3) × Submission.BoseGases.X n) × E3 =>
          (Submission.BoseGases.chiB ℓ d t.1.1.1 t.2 : ℂ)) :=
        Complex.measurable_ofReal.comp hchi_cont.measurable
      have hPsi : Measurable (fun t : ((E3 × E3) × Submission.BoseGases.X n) × E3 =>
          (Ψ (Function.update t.1.2 i t.2) : ℂ)) :=
        Complex.measurable_ofReal.comp (hΨ.measurable.comp hupd)
      exact (hchi.mul hexp).mul hPsi
    have h := MeasureTheory.StronglyMeasurable.integral_prod_right'
      (ν := (MeasureTheory.volume : MeasureTheory.Measure E3)) hker.stronglyMeasurable
    exact h.aemeasurable
  have hA := hamp Φ hΦ
  have hB := hamp (fun _ : Submission.BoseGases.X n => (1 : ℝ)) continuous_const
  -- ## 5. The FS decomposition of the projected amplitude, pointwise in `s ∈ S`
  have hdec : AEMeasurable (fun s : (E3 × E3) × Submission.BoseGases.X n =>
      (Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiB ℓ d s.1.1) s.1.2 Φ i s.2
        - ((Work.SmallBoxTBWord.boxP (Work.SmallBoxSliding.boxMass ℓ d s.1.1)
            (Submission.BoseGases.dlBox ℓ d s.1.1) i Φ (Function.update s.2 i 0) : ℝ) : ℂ)
          * Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiB ℓ d s.1.1) s.1.2
              (fun _ : Submission.BoseGases.X n => (1 : ℝ)) i s.2))
      (((MeasureTheory.volume : MeasureTheory.Measure E3).prod MeasureTheory.volume).prod
        MeasureTheory.volume) :=
    hA.sub (hmean.mul hB)
  have hproj : AEMeasurable (fun s : (E3 × E3) × Submission.BoseGases.X n =>
      Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiB ℓ d s.1.1) s.1.2
        (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d s.1.1)
          (Submission.BoseGases.dlBox ℓ d s.1.1) i Φ) i s.2)
      (((MeasureTheory.volume : MeasureTheory.Measure E3).prod MeasureTheory.volume).prod
        MeasureTheory.volume) := by
    refine hdec.congr ?_
    filter_upwards with s
    exact (Work.BoseBox.tBamp_boxQInd_eq_sub
      (volA := Work.SmallBoxSliding.boxMass ℓ d s.1.1)
      (A := Submission.BoseGases.dlBox ℓ d s.1.1)
      (χ := Submission.BoseGases.chiB ℓ d s.1.1) Φ i s.1.2 s.2 0
      (fun z hz => by
        by_contra hne
        exact hz (Work.UBBInputs9.A.tsupport_chiB_subset_dlBox hℓ hd s.1.1
          (subset_tsupport _ hne)))
      (Work.SmallBoxTBWord.contDiff_chiB hℓ hd s.1.1).continuous
      (Work.SmallBoxTBWord.hasCompactSupport_chiB hℓ hd s.1.1) hΦ).symm
  -- ## 6. Square, restrict the `x`-integral to the box, and integrate `x` out
  have hsquare : AEStronglyMeasurable
      (fun s : (E3 × E3) × Submission.BoseGases.X n =>
        ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiB ℓ d s.1.1) s.1.2
          (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d s.1.1)
            (Submission.BoseGases.dlBox ℓ d s.1.1) i Φ) i s.2‖ ^ 2)
      (((MeasureTheory.volume : MeasureTheory.Measure E3).prod MeasureTheory.volume).prod
        MeasureTheory.volume) := by
    have h1 : AEMeasurable (fun s : (E3 × E3) × Submission.BoseGases.X n =>
        ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiB ℓ d s.1.1) s.1.2
          (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d s.1.1)
            (Submission.BoseGases.dlBox ℓ d s.1.1) i Φ) i s.2‖)
        (((MeasureTheory.volume : MeasureTheory.Measure E3).prod MeasureTheory.volume).prod
          MeasureTheory.volume) :=
      hproj.norm
    exact (h1.pow_const 2).aestronglyMeasurable
  have hres : AEStronglyMeasurable
      (fun s : (E3 × E3) × Submission.BoseGases.X n =>
        ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiB ℓ d s.1.1) s.1.2
          (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d s.1.1)
            (Submission.BoseGases.dlBox ℓ d s.1.1) i Φ) i s.2‖ ^ 2)
      (((MeasureTheory.volume : MeasureTheory.Measure E3).prod MeasureTheory.volume).prod
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ))) :=
    hsquare.mono_measure (MeasureTheory.Measure.prod_mono le_rfl
      MeasureTheory.Measure.restrict_le_self)
  exact (hres.integral_prod_right').aemeasurable

/-- **The small-box word is a.e. strongly measurable** in the sliding centre. -/
lemma aestronglyMeasurable_tBwordBInd {n : ℕ} {ℓ d ε c : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ) :
    AEStronglyMeasurable
      (fun u : EuclideanSpace ℝ (Fin 3) => Work.UBBInputs8.tBwordBInd n ℓ d ε c u Φ)
      MeasureTheory.volume := by
  have hgap : AEStronglyMeasurable
      (fun u : EuclideanSpace ℝ (Fin 3) => Work.UBBInputs8.cnPlusBoxInd ℓ
        (Submission.BoseGases.dlBox ℓ d u) (Work.SmallBoxSliding.boxMass ℓ d u) Φ)
      MeasureTheory.volume := by
    rw [show (fun u : EuclideanSpace ℝ (Fin 3) => Work.UBBInputs8.cnPlusBoxInd ℓ
        (Submission.BoseGases.dlBox ℓ d u) (Work.SmallBoxSliding.boxMass ℓ d u) Φ)
        = fun u : EuclideanSpace ℝ (Fin 3) => ∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) i Φ x) ^ 2 from rfl]
    refine Finset.aestronglyMeasurable_fun_sum Finset.univ (fun i _ => ?_)
    have hD := aemeasurable_boxQInd_sliding hℓ hd hΦ.continuous i
    have hjoint : AEMeasurable (fun q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n =>
        (Submission.BoseGases.abox n ℓ).indicator
          (fun x => (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d q.1)
            (Submission.BoseGases.dlBox ℓ d q.1) i Φ x) ^ 2) q.2)
        (MeasureTheory.volume.prod MeasureTheory.volume) := by
      have h1 : AEMeasurable (fun q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n =>
          (Submission.BoseGases.abox n ℓ).indicator (fun _ => (1 : ℝ)) q.2)
          (MeasureTheory.volume.prod MeasureTheory.volume) :=
        ((measurable_const.indicator
          (Submission.BoseGases.abox_compact n hℓ).measurableSet).comp
            measurable_snd).aemeasurable
      have h2 : AEMeasurable (fun q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n =>
          (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d q.1)
            (Submission.BoseGases.dlBox ℓ d q.1) i Φ q.2) ^ 2)
          (MeasureTheory.volume.prod MeasureTheory.volume) := hD.pow_const 2
      refine (h1.mul h2).congr ?_
      filter_upwards with q
      obtain ⟨u, x⟩ := q
      show (Submission.BoseGases.abox n ℓ).indicator (fun _ => (1 : ℝ)) x *
          (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) i Φ x) ^ 2
        = (Submission.BoseGases.abox n ℓ).indicator
            (fun x => (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) i Φ x) ^ 2) x
      by_cases hx : x ∈ Submission.BoseGases.abox n ℓ
      · rw [Set.indicator_of_mem hx (fun _ => (1 : ℝ)), Set.indicator_of_mem hx,
          one_mul]
      · rw [Set.indicator_of_notMem hx (fun _ => (1 : ℝ)), Set.indicator_of_notMem hx,
          zero_mul]
    have hinter := hjoint.aestronglyMeasurable.integral_prod_right'
    refine hinter.congr ?_
    filter_upwards with u
    rw [MeasureTheory.integral_indicator
      (Submission.BoseGases.abox_compact n hℓ).measurableSet]
  have hdiag : AEStronglyMeasurable
      (fun u : EuclideanSpace ℝ (Fin 3) => Work.UBBInputs8.tBdiagFormInd ℓ
        (Submission.BoseGases.dlBox ℓ d u) (Work.SmallBoxSliding.boxMass ℓ d u)
        (Submission.BoseGases.chiB ℓ d u) (Submission.BoseGases.fsKinCoeff c) Φ)
      MeasureTheory.volume := by
    rw [show (fun u : EuclideanSpace ℝ (Fin 3) => Work.UBBInputs8.tBdiagFormInd ℓ
        (Submission.BoseGases.dlBox ℓ d u) (Work.SmallBoxSliding.boxMass ℓ d u)
        (Submission.BoseGases.chiB ℓ d u) (Submission.BoseGases.fsKinCoeff c) Φ)
        = fun u : EuclideanSpace ℝ (Fin 3) => ∑ i : Fin n,
            ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
              Submission.BoseGases.fsKinCoeff c ‖p‖ * ((ℓ ^ 3)⁻¹ *
                ∫ x in Submission.BoseGases.abox n ℓ,
                  ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiB ℓ d u) p
                    (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                      (Submission.BoseGases.dlBox ℓ d u) i Φ) i x‖ ^ 2) from rfl]
    refine Finset.aestronglyMeasurable_fun_sum Finset.univ (fun i _ => ?_)
    have hF := aemeasurable_diagIntegrand hℓ hd hΦ.continuous i
    have hcoefcont : Continuous (fun r : ℝ => Submission.BoseGases.fsKinCoeff c r) := by
      unfold Submission.BoseGases.fsKinCoeff
      exact ((continuous_id.sub continuous_const).max continuous_const).pow 2
    have hcoef : AEMeasurable (fun q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.fsKinCoeff c ‖q.2‖)
        (MeasureTheory.volume.prod MeasureTheory.volume) :=
      (hcoefcont.comp (continuous_norm.comp continuous_snd)).measurable.aemeasurable
    have hjoint : AEMeasurable (fun q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.fsKinCoeff c ‖q.2‖ * ((ℓ ^ 3)⁻¹ *
          ∫ x in Submission.BoseGases.abox n ℓ,
            ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiB ℓ d q.1) q.2
              (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d q.1)
                (Submission.BoseGases.dlBox ℓ d q.1) i Φ) i x‖ ^ 2))
        (MeasureTheory.volume.prod MeasureTheory.volume) :=
      hcoef.mul (hF.const_mul _)
    have hinter := hjoint.aestronglyMeasurable.integral_prod_right'
    exact hinter.const_mul _
  have hsplit : (fun u : EuclideanSpace ℝ (Fin 3) => Work.UBBInputs8.tBwordBInd n ℓ d ε c u Φ)
      = fun u : EuclideanSpace ℝ (Fin 3) =>
          Work.SmallBoxTBWord.tbGapCoeff (ℓ * d) ε *
            Work.UBBInputs8.cnPlusBoxInd ℓ (Submission.BoseGases.dlBox ℓ d u)
              (Work.SmallBoxSliding.boxMass ℓ d u) Φ
          + Work.UBBInputs8.tBdiagFormInd ℓ (Submission.BoseGases.dlBox ℓ d u)
              (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.chiB ℓ d u)
              (Submission.BoseGases.fsKinCoeff c) Φ := rfl
  rw [hsplit]
  exact (hgap.const_mul _).add hdiag

theorem integrable_sbKin {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    {μ : ℝ} (hμ : 0 < μ)
    {n : ℕ} (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))) :
    MeasureTheory.Integrable
      (fun u : EuclideanSpace ℝ (Fin 3) =>
        Work.BoseFixB1.sbKin (v := v) μ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M u
          (Φ : Submission.BoseGases.X n → ℝ)) := by
  by_cases ha : 0 < _root_.BoseGases.a v
  · -- **Main case `0 < a v`**: the word is bounded, measurable and supported on `goodSet ℓ d 0`.
    have hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := sideAt_pos_of_pos hμ ha
    have hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d := paramsAt_d_pos hμ ha
    have hsb : (fun u : EuclideanSpace ℝ (Fin 3) =>
          Work.BoseFixB1.sbKin (v := v) μ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M u
            (Φ : Submission.BoseGases.X n → ℝ))
        = fun u : EuclideanSpace ℝ (Fin 3) =>
          Work.UBBInputs8.tBwordBInd n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
            (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) u (Φ : Submission.BoseGases.X n → ℝ) :=
      rfl
    rw [hsb]
    obtain ⟨K, hK⟩ := tBwordBInd_abs_bound (n := n) hℓ hd Φ.contDiff
    have hmeas := aestronglyMeasurable_tBwordBInd (n := n) hℓ hd
      (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
      (ε := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT)
      (c := Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) Φ.contDiff
    refine MeasureTheory.IntegrableOn.integrable_of_forall_notMem_eq_zero (s :=
      Work.SmallBoxSliding.goodSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d 0) ?_ ?_
    · refine MeasureTheory.IntegrableOn.of_bound
        (volume_goodSet_zero_lt_top hℓ hd) (hmeas.mono_measure Measure.restrict_le_self) K ?_
      rw [MeasureTheory.ae_restrict_iff'
        (Work.SmallBoxSliding.measurableSet_goodSet _ _ _)]
      exact Filter.Eventually.of_forall
        (fun u _ => by simpa only [Real.norm_eq_abs] using hK u)
    · intro u hu
      exact Work.BoseFixB1.tBwordBInd_eq_zero_of_farSet hℓ hd
        (mem_farSet_of_notMem_goodSet hu) _
  · -- **Degenerate case `a v ≤ 0`**: the box side vanishes and so does the word.
    push_neg at ha
    have h0 : (fun u : EuclideanSpace ℝ (Fin 3) =>
          Work.BoseFixB1.sbKin (v := v) μ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M u
            (Φ : Submission.BoseGases.X n → ℝ)) = fun _ => (0 : ℝ) := by
      funext u
      exact sbKin_eq_zero_of_sideAt_eq_zero
        (sideAt_eq_zero_of_nonpos hμ.le ha) (Φ : Submission.BoseGases.X n → ℝ)
    rw [h0]
    exact MeasureTheory.integrable_zero (α := EuclideanSpace ℝ (Fin 3)) (ε' := ℝ)
      MeasureTheory.volume

end Work.BoseFixB1
