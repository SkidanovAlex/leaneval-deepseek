import Mathlib
import Submission.Work.Asymptotics.BlLow.Defs
import Submission.Work.HFN.HalfFunnel.lowBad_Tspike_bound
import Submission.Work.Asymptotics.KaxisMid.Classify

/-!
# Geometry of the low bad-line region `blLowSet`

This file collects the elementary facts about `blLowSet = {τ ∈ 𝒟 : 2/5 ≤ Im τ ≤ 1/2, |Re τ| > 3/4}`
needed by the window (spike) bound `Work.Asymptotics.BlLow.window_bound`:

* compactness of the closed box `blBox`;
* the translate pole `zpole τ = τ - tsign τ` lies in the closed CKMRV fundamental domain `𝒟`
  (so that the level-two coincidence classification applies to it);
* the window bounds `11/40 ≤ t ≤ 5/8`;
* the **crossed** point `crossedPt τ = tsign τ + S·τ = tsign τ - 1/τ`, which carries the unique
  `j`-coincidence of the closure of `blLowSet` (`j (crossedPt τ) = j τ`).
-/
noncomputable section

open UpperHalfPlane
open Work.Kernels
open Work.Asymptotics.HalfFunnel Work.HFN.HalfFunnel

namespace Work.HFN.BlLow
open Work.Asymptotics Work.Asymptotics.BlLow  -- ck-hfn-fix: fork moved out of Work.Asymptotics

set_option maxHeartbeats 800000

/-! ## 1. The closed box is compact -/

lemma isClosed_blBox : IsClosed blBox := by
  have h1 : IsClosed {τ : ℍ | (3 / 4 : ℝ) ≤ |τ.re|} :=
    isClosed_le continuous_const (continuous_abs.comp UpperHalfPlane.continuous_re)
  have h2 : IsClosed {τ : ℍ | |τ.re| ≤ (1 : ℝ)} :=
    isClosed_le (continuous_abs.comp UpperHalfPlane.continuous_re) continuous_const
  have h3 : IsClosed {τ : ℍ | (2 / 5 : ℝ) ≤ τ.im} :=
    isClosed_le continuous_const UpperHalfPlane.continuous_im
  have h4 : IsClosed {τ : ℍ | τ.im ≤ (1 / 2 : ℝ)} :=
    isClosed_le UpperHalfPlane.continuous_im continuous_const
  have hset : blBox = ({τ : ℍ | (3 / 4 : ℝ) ≤ |τ.re|} ∩ {τ : ℍ | |τ.re| ≤ (1 : ℝ)}) ∩
      ({τ : ℍ | (2 / 5 : ℝ) ≤ τ.im} ∩ {τ : ℍ | τ.im ≤ (1 / 2 : ℝ)}) := by
    ext τ; simp only [blBox, Set.mem_ofPred_eq, Set.mem_inter_iff]; tauto
  rw [hset]
  exact (h1.inter h2).inter (h3.inter h4)

lemma isCompact_blBox : IsCompact blBox := by
  have hsub : blBox ⊆ Metric.closedBall (⟨Complex.I, by simp⟩ : ℍ) 10 := by
    intro τ hτ
    rw [Metric.mem_closedBall]
    have hnum : ‖(τ : ℂ) - Complex.I‖ ≤ 2 := by
      have h := Complex.norm_le_abs_re_add_abs_im ((τ : ℂ) - Complex.I)
      have hre : ((τ : ℂ) - Complex.I).re = τ.re := by simp
      have him : ((τ : ℂ) - Complex.I).im = τ.im - 1 := by simp
      rw [hre, him] at h
      have h4 : |τ.im - 1| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith [hτ.2.2.1, hτ.2.2.2]
      linarith [hτ.2.1]
    have hI : (⟨Complex.I, by simp⟩ : ℍ).im = 1 := by
      rw [← UpperHalfPlane.coe_im]; simp
    have hsqrt : (1 / 2 : ℝ) ≤ Real.sqrt (τ.im * (⟨Complex.I, by simp⟩ : ℍ).im) := by
      rw [hI, mul_one, Real.le_sqrt (by norm_num) (by positivity)]
      linarith [hτ.2.2.1]
    have hstep : dist τ (⟨Complex.I, by simp⟩ : ℍ) ≤
        ‖(τ : ℂ) - Complex.I‖ / Real.sqrt (τ.im * (⟨Complex.I, by simp⟩ : ℍ).im) := by
      have h := UpperHalfPlane.dist_le_dist_coe_div_sqrt τ (⟨Complex.I, by simp⟩ : ℍ)
      simpa [UpperHalfPlane.coe_I, Complex.dist_eq] using h
    calc dist τ (⟨Complex.I, by simp⟩ : ℍ)
        ≤ ‖(τ : ℂ) - Complex.I‖ / Real.sqrt (τ.im * (⟨Complex.I, by simp⟩ : ℍ).im) := hstep
      _ ≤ 2 / (1 / 2 : ℝ) := div_le_div₀ (by norm_num) hnum (by norm_num) hsqrt
      _ ≤ 10 := by norm_num
  exact IsCompact.of_isClosed_subset (isCompact_closedBall _ 10) isClosed_blBox hsub

/-! ## 2. The translate pole lies in `𝒟` -/

/-- On `blLowSet`, `zpole τ = τ - tsign τ` has real part of modulus `< 1/4`. -/
lemma zpole_re_abs_lt_blLow {τ : ℍ} (hτ : blLowSet τ) : |(zpole τ).re| < 1 / 4 := by
  obtain ⟨h34, h1⟩ := blLowSet_re_abs_bounds hτ
  have hlt : τ.re < 1 := (abs_lt.mp h1).2
  have hgt : -1 < τ.re := (abs_lt.mp h1).1
  rw [zpole_re]
  rcases lt_or_ge 0 τ.re with hpos | hneg
  · rw [(tsign_eq_one_iff τ).mpr hpos]
    have h34' : 3 / 4 < τ.re := by rw [abs_of_pos hpos] at h34; exact h34
    rw [abs_lt]; constructor <;> linarith
  · rw [(tsign_eq_neg_one_iff τ).mpr hneg]
    have hneg' : τ.re < -(3 / 4) := by
      rcases hτ.2.2.2 with h | h
      · exact absurd h (by linarith)
      · exact h
    rw [abs_lt]; constructor <;> linarith

/-- `zpole τ ∈ 𝒟` for `τ ∈ blLowSet`. -/
lemma zpole_mem_DomainD_blLow {τ : ℍ} (hτ : blLowSet τ) : zpole τ ∈ DomainD := by
  have hD : τ ∈ DomainD := hτ.1
  have hre' := abs_lt.mp (zpole_re_abs_lt_blLow hτ)
  have hzc : ((zpole τ : ℍ) : ℂ) = (τ : ℂ) - (tsign τ : ℂ) := zpole_coe τ
  rcases lt_or_ge 0 τ.re with hpos | hneg
  · have h1 : (tsign τ : ℝ) = 1 := (tsign_eq_one_iff τ).mpr hpos
    have hcoe : ((zpole τ : ℍ) : ℂ) = (τ : ℂ) - 1 := by
      rw [hzc, h1]; norm_num
    have hlt : τ.re < 1 := hD.2.1
    refine ⟨by linarith [hre'.1], by linarith [hre'.2], ?_, ?_⟩
    · have h2 : ((zpole τ : ℍ) : ℂ) - (1 / 2 : ℂ) = (τ : ℂ) - (3 / 2 : ℂ) := by rw [hcoe]; ring
      rw [h2]
      have h3 : (3 / 2 : ℝ) - τ.re > 1 / 2 := by linarith
      have := Complex.abs_re_le_norm ((τ : ℂ) - (3 / 2 : ℂ))
      have hre : ((τ : ℂ) - (3 / 2 : ℂ)).re = τ.re - 3 / 2 := by simp
      rw [hre] at this
      rw [abs_of_neg (by linarith : τ.re - 3 / 2 < 0)] at this
      linarith
    · have h2 : ((zpole τ : ℍ) : ℂ) + (1 / 2 : ℂ) = (τ : ℂ) - (1 / 2 : ℂ) := by rw [hcoe]; ring
      rw [h2]
      exact hD.2.2.1
  · have h1 : (tsign τ : ℝ) = -1 := (tsign_eq_neg_one_iff τ).mpr hneg
    have hcoe : ((zpole τ : ℍ) : ℂ) = (τ : ℂ) + 1 := by
      rw [hzc, h1]; norm_num
    have hgt : -1 < τ.re := hD.1
    refine ⟨by linarith [hre'.1], by linarith [hre'.2], ?_, ?_⟩
    · have h2 : ((zpole τ : ℍ) : ℂ) - (1 / 2 : ℂ) = (τ : ℂ) + (1 / 2 : ℂ) := by rw [hcoe]; ring
      rw [h2]
      exact hD.2.2.2
    · have h2 : ((zpole τ : ℍ) : ℂ) + (1 / 2 : ℂ) = (τ : ℂ) + (3 / 2 : ℂ) := by rw [hcoe]; ring
      rw [h2]
      have h3 : (1 / 2 : ℝ) < τ.re + 3 / 2 := by linarith
      have := Complex.abs_re_le_norm ((τ : ℂ) + (3 / 2 : ℂ))
      have hre : ((τ : ℂ) + (3 / 2 : ℂ)).re = τ.re + 3 / 2 := by simp
      rw [hre] at this
      rw [abs_of_pos (by linarith : (0:ℝ) < τ.re + 3 / 2)] at this
      linarith

/-! ## 3. Window bounds -/

lemma blLow_window_bounds {τ : ℍ} {t : ℝ} (hτ : blLowSet τ) (ht : 0 < t)
    (hw : |t - τ.im| ≤ 1 / 8) : (11 : ℝ) / 40 ≤ t ∧ t ≤ 5 / 8 := by
  obtain ⟨h1, h2⟩ := blLowSet_im_bounds hτ
  have := abs_le.mp hw
  constructor <;> linarith

/-! ## 4. The crossed point -/

/-- The **crossed** orbit point `tsign τ + S·τ = tsign τ - 1/τ` attached to `τ`; it is the point
of the orbit of `τ` that carries the (only) `j`-coincidence of the closure of `blLowSet`. -/
def crossedPt (τ : ℍ) : ℍ := (tsign τ : ℝ) +ᵥ (ModularGroup.S • τ)

lemma crossedPt_coe (τ : ℍ) :
    ((crossedPt τ : ℍ) : ℂ) = (tsign τ : ℂ) - ((τ : ℂ))⁻¹ := by
  rw [crossedPt, UpperHalfPlane.coe_vadd, Work.Rigidity.coe_S_smul]
  push_cast
  ring

lemma crossedPt_im (τ : ℍ) : (crossedPt τ).im = τ.im / ‖(τ : ℂ)‖ ^ 2 := by
  rw [← UpperHalfPlane.coe_im, crossedPt_coe, Complex.sub_im, Complex.ofReal_im, zero_sub,
    Complex.inv_im, Complex.normSq_eq_norm_sq, UpperHalfPlane.coe_im]
  ring

lemma crossedPt_re (τ : ℍ) : (crossedPt τ).re = tsign τ - τ.re / ‖(τ : ℂ)‖ ^ 2 := by
  rw [← UpperHalfPlane.coe_re, crossedPt_coe, Complex.sub_re, Complex.ofReal_re, Complex.inv_re,
    Complex.normSq_eq_norm_sq, UpperHalfPlane.coe_re]

/-- The crossed point is `j`-equivalent to `τ`. -/
lemma crossedPt_jInvariantFun (τ : ℍ) :
    jInvariantFun (crossedPt τ) = jInvariantFun τ := by
  rcases tsign_eq_one_or_neg_one τ with h | h
  · have h1 : crossedPt τ = (1 : ℝ) +ᵥ (ModularGroup.S • τ) := by rw [crossedPt, h]
    rw [h1, Work.Kernels.KernelFacts.jInvariantFun_vadd_one,
      Work.Kernels.KernelFacts.jInvariantFun_S_smul]
  · have h1 : crossedPt τ = (-1 : ℝ) +ᵥ (ModularGroup.S • τ) := by rw [crossedPt, h]
    rw [h1]
    have h2 : (1 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ (ModularGroup.S • τ)) = ModularGroup.S • τ := by
      rw [← add_vadd]; norm_num
    have h3 := Work.Kernels.KernelFacts.jInvariantFun_vadd_one
      ((-1 : ℝ) +ᵥ (ModularGroup.S • τ))
    rw [h2, Work.Kernels.KernelFacts.jInvariantFun_S_smul] at h3
    exact h3.symm

/-! ## 5. The closed parameter box -/

/-- The closed parameter box containing the closure of `blLowSet`: the points of the *closed*
CKMRV fundamental domain with `|Re| ∈ [3/4,1]` and `Im ∈ [2/5,1/2]`. -/
def clBox : Set ℍ :=
  {τ : ℍ | 3 / 4 ≤ |τ.re| ∧ |τ.re| ≤ 1 ∧ (2 : ℝ) / 5 ≤ τ.im ∧ τ.im ≤ 1 / 2 ∧
    1 / 2 ≤ ‖(τ : ℂ) - (1 / 2 : ℂ)‖ ∧ 1 / 2 ≤ ‖(τ : ℂ) + (1 / 2 : ℂ)‖}

lemma blLowSet_subset_clBox {τ : ℍ} (hτ : blLowSet τ) : τ ∈ clBox := by
  obtain ⟨hD, h1, h2, hre⟩ := hτ
  have habs : |τ.re| < 1 := by rw [abs_lt]; exact ⟨hD.1, hD.2.1,⟩
  refine ⟨?_, habs.le, h1, h2, le_of_lt hD.2.2.1, le_of_lt hD.2.2.2⟩
  rcases hre with h | h
  · rw [abs_of_pos (by linarith)]; exact le_of_lt h
  · rw [abs_of_neg (by linarith)]; linarith

lemma isClosed_clBox : IsClosed clBox := by
  have h1 : IsClosed {τ : ℍ | (3 / 4 : ℝ) ≤ |τ.re|} :=
    isClosed_le continuous_const (continuous_abs.comp UpperHalfPlane.continuous_re)
  have h2 : IsClosed {τ : ℍ | |τ.re| ≤ (1 : ℝ)} :=
    isClosed_le (continuous_abs.comp UpperHalfPlane.continuous_re) continuous_const
  have h3 : IsClosed {τ : ℍ | (2 / 5 : ℝ) ≤ τ.im} :=
    isClosed_le continuous_const UpperHalfPlane.continuous_im
  have h4 : IsClosed {τ : ℍ | τ.im ≤ (1 / 2 : ℝ)} :=
    isClosed_le UpperHalfPlane.continuous_im continuous_const
  have h5 : IsClosed {τ : ℍ | (1 / 2 : ℝ) ≤ ‖(τ : ℂ) - (1 / 2 : ℂ)‖} :=
    isClosed_le continuous_const (Continuous.norm (UpperHalfPlane.continuous_coe.sub continuous_const))
  have h6 : IsClosed {τ : ℍ | (1 / 2 : ℝ) ≤ ‖(τ : ℂ) + (1 / 2 : ℂ)‖} :=
    isClosed_le continuous_const (Continuous.norm (UpperHalfPlane.continuous_coe.add continuous_const))
  have hset : clBox = (((({τ : ℍ | (3 / 4 : ℝ) ≤ |τ.re|} ∩ {τ : ℍ | |τ.re| ≤ (1 : ℝ)}) ∩
      ({τ : ℍ | (2 / 5 : ℝ) ≤ τ.im} ∩ {τ : ℍ | τ.im ≤ (1 / 2 : ℝ)})) ∩
      {τ : ℍ | (1 / 2 : ℝ) ≤ ‖(τ : ℂ) - (1 / 2 : ℂ)‖}) ∩
      {τ : ℍ | (1 / 2 : ℝ) ≤ ‖(τ : ℂ) + (1 / 2 : ℂ)‖}) := by
    ext τ; simp only [clBox, Set.mem_ofPred_eq, Set.mem_inter_iff]; tauto
  rw [hset]
  exact (((h1.inter h2).inter (h3.inter h4)).inter h5).inter h6

lemma isCompact_clBox : IsCompact clBox := by
  have hsub : clBox ⊆ Metric.closedBall (⟨Complex.I, by simp⟩ : ℍ) 10 := by
    intro τ hτ
    rw [Metric.mem_closedBall]
    have hnum : ‖(τ : ℂ) - Complex.I‖ ≤ 2 := by
      have h := Complex.norm_le_abs_re_add_abs_im ((τ : ℂ) - Complex.I)
      have hre : ((τ : ℂ) - Complex.I).re = τ.re := by simp
      have him : ((τ : ℂ) - Complex.I).im = τ.im - 1 := by simp
      rw [hre, him] at h
      have h4 : |τ.im - 1| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith [hτ.2.2.1, hτ.2.2.2]
      linarith [hτ.2.1]
    have hI : (⟨Complex.I, by simp⟩ : ℍ).im = 1 := by
      rw [← UpperHalfPlane.coe_im]; simp
    have hsqrt : (1 / 2 : ℝ) ≤ Real.sqrt (τ.im * (⟨Complex.I, by simp⟩ : ℍ).im) := by
      rw [hI, mul_one, Real.le_sqrt (by norm_num) (by positivity)]
      linarith [hτ.2.2.1]
    have hstep : dist τ (⟨Complex.I, by simp⟩ : ℍ) ≤
        ‖(τ : ℂ) - Complex.I‖ / Real.sqrt (τ.im * (⟨Complex.I, by simp⟩ : ℍ).im) := by
      have h := UpperHalfPlane.dist_le_dist_coe_div_sqrt τ (⟨Complex.I, by simp⟩ : ℍ)
      simpa [UpperHalfPlane.coe_I, Complex.dist_eq] using h
    calc dist τ (⟨Complex.I, by simp⟩ : ℍ)
        ≤ ‖(τ : ℂ) - Complex.I‖ / Real.sqrt (τ.im * (⟨Complex.I, by simp⟩ : ℍ).im) := hstep
      _ ≤ 2 / (1 / 2 : ℝ) := div_le_div₀ (by norm_num) hnum (by norm_num) hsqrt
      _ ≤ 10 := by norm_num
  exact IsCompact.of_isClosed_subset (isCompact_closedBall _ 10) isClosed_clBox hsub

/-! ## 6. Auxiliary geometry of the two coincidence branches -/

lemma normSq_coe (τ : ℍ) : ‖(τ : ℂ)‖ ^ 2 = τ.re ^ 2 + τ.im ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  ring

/-- On the tangency arcs, the crossed point is purely imaginary. -/
lemma crossedPt_re_eq_zero_of_arc1 {τ : ℍ} (harc : ‖(τ : ℂ) - (1 / 2 : ℂ)‖ = 1 / 2) :
    (crossedPt τ).re = 0 := by
  have hsq : ‖(τ : ℂ)‖ ^ 2 = τ.re := by
    have h2 : ‖(τ : ℂ) - (1 / 2 : ℂ)‖ ^ 2 = (1 / 2 : ℝ) ^ 2 := by rw [harc]
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply] at h2
    have h3 : ((τ : ℂ) - (1 / 2 : ℂ)).re = τ.re - 1 / 2 := by simp
    have h4 : ((τ : ℂ) - (1 / 2 : ℂ)).im = τ.im := by simp
    rw [h3, h4] at h2
    rw [normSq_coe]
    nlinarith [h2]
  have hpos : 0 < τ.re := by
    have h5 := normSq_coe τ
    have him : 0 < τ.im := τ.im_pos
    nlinarith [hsq, h5, him]
  have hsign : (tsign τ : ℝ) = 1 := (tsign_eq_one_iff τ).mpr hpos
  rw [crossedPt_re, hsign, hsq, div_self (ne_of_gt hpos), sub_self]

lemma crossedPt_re_eq_zero_of_arc2 {τ : ℍ} (harc : ‖(τ : ℂ) + (1 / 2 : ℂ)‖ = 1 / 2) :
    (crossedPt τ).re = 0 := by
  have hsq : ‖(τ : ℂ)‖ ^ 2 = -τ.re := by
    have h2 : ‖(τ : ℂ) + (1 / 2 : ℂ)‖ ^ 2 = (1 / 2 : ℝ) ^ 2 := by rw [harc]
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply] at h2
    have h3 : ((τ : ℂ) + (1 / 2 : ℂ)).re = τ.re + 1 / 2 := by simp
    have h4 : ((τ : ℂ) + (1 / 2 : ℂ)).im = τ.im := by simp
    rw [h3, h4] at h2
    rw [normSq_coe]
    nlinarith [h2]
  have hneg : τ.re < 0 := by
    have h5 := normSq_coe τ
    have him : 0 < τ.im := τ.im_pos
    nlinarith [hsq, h5, him]
  have hsign : (tsign τ : ℝ) = -1 := (tsign_eq_neg_one_iff τ).mpr (le_of_lt hneg)
  rw [crossedPt_re, hsign, hsq]
  have hne : τ.re ≠ 0 := ne_of_lt hneg
  field_simp
  ring

/-- On the bad lines, the translate pole is purely imaginary. -/
lemma zpole_re_eq_zero_of_re_eq {τ : ℍ} (h : τ.re = tsign τ) : (zpole τ).re = 0 := by
  rw [zpole_re, h, sub_self]

/-- `S` acts on the imaginary axis by `i t ↦ i/t`. -/
lemma S_smul_imagAxis (t : ℝ) (ht : 0 < t) :
    ModularGroup.S • imagAxis t ht = imagAxis (1 / t) (by positivity) := by
  apply UpperHalfPlane.ext
  rw [Work.Rigidity.coe_S_smul]
  simp only [imagAxis]
  congr 1
  rw [mul_inv, Complex.inv_I]
  push_cast
  ring

/-- **Stabiliser classification of purely imaginary coincidences.** Two points of the positive
imaginary axis with the same `j`-value are `it` and `i/t`. -/
lemma imagAxis_eq_or_inv {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (h : jInvariantFun (imagAxis s hs) = jInvariantFun (imagAxis t ht)) :
    t = s ∨ t = 1 / s := by
  obtain ⟨γ, hγ⟩ := jInvariantFun_eq_smul_of_eq h
  rcases eq_one_or_neg_one_or_S_of_smul_imagAxis ht hs hγ with h1 | h1 | h1 | h1
  · left
    rw [h1, one_smul] at hγ
    simpa [imagAxis] using congrArg UpperHalfPlane.im hγ
  · left
    have h4 : ((-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) • imagAxis t ht : ℍ)
        = imagAxis t ht := by
      have hh := ModularGroup.SL_neg_smul (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)
        (imagAxis t ht)
      simpa using hh
    rw [h1, h4] at hγ
    simpa [imagAxis] using congrArg UpperHalfPlane.im hγ
  · right
    rw [h1, S_smul_imagAxis] at hγ
    have h2 : 1 / t = s := by simpa [imagAxis] using congrArg UpperHalfPlane.im hγ
    field_simp at h2 ⊢
    linarith [h2]
  · right
    have h4 : ((-ModularGroup.S : Matrix.SpecialLinearGroup (Fin 2) ℤ) • imagAxis t ht : ℍ)
        = ModularGroup.S • imagAxis t ht := by
      have hh := ModularGroup.SL_neg_smul ModularGroup.S (imagAxis t ht)
      exact hh
    rw [h1, h4, S_smul_imagAxis] at hγ
    have h2 : 1 / t = s := by simpa [imagAxis] using congrArg UpperHalfPlane.im hγ
    field_simp at h2 ⊢
    linarith [h2]

/-! ## 7. Classification of the coincidences of the closure of `blLowSet` -/

lemma imagAxis_re_zero (t : ℝ) (ht : 0 < t) : ((imagAxis t ht : ℍ) : ℂ).re = 0 := by
  simp [imagAxis]

lemma imagAxis_congr {t s : ℝ} (ht : 0 < t) (hs : 0 < s) (h : t = s) :
    imagAxis t ht = imagAxis s hs := by
  apply UpperHalfPlane.ext
  show (t : ℂ) * Complex.I = (s : ℂ) * Complex.I
  rw [h]

/-- `τ ∉ 𝒟` for a point of the closed box carrying a coincidence with the contour. -/
lemma not_mem_DomainD_of_j_eq {τ : ℍ} (hτ : τ ∈ clBox) {t : ℝ} (ht : 0 < t)
    (hcoin : jInvariantFun τ = jInvariantFun (imagAxis t ht)) : τ ∉ DomainD := by
  intro hD
  have himre : ((imagAxis t ht : ℍ) : ℂ).re = 0 := imagAxis_re_zero t ht
  rcases Work.Asymptotics.KaxisMid.eq_or_eq_S_of_re_eq_zero hD himre hcoin with h | h
  · have hre : τ.re = 0 := by
      have h' : ((τ : ℂ)).re = 0 := by rw [← h]; exact himre
      rwa [UpperHalfPlane.coe_re] at h'
    have h34 : (3 / 4 : ℝ) ≤ |τ.re| := hτ.1
    rw [hre, abs_zero] at h34
    norm_num at h34
  · have hre : ((ModularGroup.S • τ : ℍ) : ℂ).re = 0 := by rw [← h]; exact himre
    rw [Work.Rigidity.coe_S_smul, Complex.neg_re, Complex.inv_re,
      Complex.normSq_eq_norm_sq] at hre
    have hns : ‖(τ : ℂ)‖ ^ 2 ≠ 0 := by
      have h2 : (0:ℝ) < ‖(τ : ℂ)‖ ^ 2 := by nlinarith [normSq_coe τ, τ.im_pos, sq_nonneg τ.re]
      exact ne_of_gt h2
    have hre0 : τ.re = 0 := by
      have h2 : τ.re / ‖(τ : ℂ)‖ ^ 2 = 0 := neg_eq_zero.mp hre
      exact (div_eq_zero_iff.mp h2).resolve_right hns
    have h34 : (3 / 4 : ℝ) ≤ |τ.re| := hτ.1
    rw [hre0, abs_zero] at h34
    norm_num at h34

/-- **Classification of the coincidences of the closure of `blLowSet`.**  For `τ` in the closed
box `clBox` and `t` in the window `[11/40,5/8]`, a coincidence `j τ = j (it)` forces the contour
point to be one of the two orbit points `zpole τ = τ - tsign τ` (on the bad lines) or
`crossedPt τ = tsign τ + S·τ` (on the tangency arcs). -/
theorem coincidence_classification {τ : ℍ} {t : ℝ} (hτ : τ ∈ clBox) (ht : 0 < t)
    (htw : (11 : ℝ) / 40 ≤ t) (htw2 : t ≤ 5 / 8)
    (hcoin : jInvariantFun τ = jInvariantFun (imagAxis t ht)) :
    imagAxis t ht = zpole τ ∨ imagAxis t ht = crossedPt τ := by
  have hnotD := not_mem_DomainD_of_j_eq hτ ht hcoin
  have hboundary : |τ.re| = 1 ∨ ‖(τ : ℂ) - (1 / 2 : ℂ)‖ = 1 / 2 ∨
      ‖(τ : ℂ) + (1 / 2 : ℂ)‖ = 1 / 2 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨hA, hB, hC⟩ := hcon
    refine hnotD ⟨?_, ?_, ?_, ?_⟩
    · have habs : |τ.re| < 1 := lt_of_le_of_ne hτ.2.1 hA
      exact (abs_lt.mp habs).1
    · have habs : |τ.re| < 1 := lt_of_le_of_ne hτ.2.1 hA
      exact (abs_lt.mp habs).2
    · exact lt_of_le_of_ne hτ.2.2.2.2.1 (Ne.symm hB)
    · exact lt_of_le_of_ne hτ.2.2.2.2.2 (Ne.symm hC)
  rcases hboundary with habs | harc | harc
  · -- bad line
    have habs' : τ.re = 1 ∨ τ.re = -1 := by
      rw [abs_eq (by norm_num : (0 : ℝ) ≤ 1)] at habs; exact habs
    have hre_eq : τ.re = tsign τ := by
      rcases habs' with h | h
      · have h1 : tsign τ = 1 := (tsign_eq_one_iff τ).mpr (by rw [h]; norm_num)
        rw [h, h1]
      · have h1 : tsign τ = -1 := (tsign_eq_neg_one_iff τ).mpr (by rw [h]; norm_num)
        rw [h, h1]
    have hzp : (zpole τ).re = 0 := zpole_re_eq_zero_of_re_eq hre_eq
    have hzim : (zpole τ).im = τ.im := zpole_im τ
    have hzpe : zpole τ = imagAxis τ.im τ.im_pos := by
      have h := Work.Asymptotics.KaxisMid.eq_imagAxis_of_re_eq_zero hzp
      have h2 : imagAxis (zpole τ).im (zpole τ).im_pos = imagAxis τ.im τ.im_pos :=
        imagAxis_congr _ _ hzim
      rw [← h2]; exact h
    have hj : jInvariantFun (imagAxis τ.im τ.im_pos) = jInvariantFun (imagAxis t ht) := by
      rw [← hzpe, zpole_jInvariantFun]; exact hcoin
    rcases imagAxis_eq_or_inv τ.im_pos ht hj with h | h
    · left
      rw [imagAxis_congr ht τ.im_pos h, hzpe]
    · exfalso
      have h2 : (2 : ℝ) ≤ 1 / τ.im := by
        rw [le_div_iff₀ τ.im_pos]; linarith [hτ.2.2.1, hτ.2.2.2]
      rw [h] at htw2
      linarith
  · -- first tangency arc
    have hcpre : (crossedPt τ).re = 0 := crossedPt_re_eq_zero_of_arc1 harc
    have hsq : ‖(τ : ℂ)‖ ^ 2 = τ.re := by
      have h2 : ‖(τ : ℂ) - (1 / 2 : ℂ)‖ ^ 2 = (1 / 2 : ℝ) ^ 2 := by rw [harc]
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply] at h2
      have h3 : ((τ : ℂ) - (1 / 2 : ℂ)).re = τ.re - 1 / 2 := by simp
      have h4 : ((τ : ℂ) - (1 / 2 : ℂ)).im = τ.im := by simp
      rw [h3, h4] at h2
      rw [normSq_coe]; nlinarith [h2]
    have hre_ge : (3 / 4 : ℝ) ≤ τ.re := by
      have h := hτ.1
      rw [abs_of_nonneg (by nlinarith [hsq, normSq_coe τ, τ.im_pos] : 0 ≤ τ.re)] at h
      exact h
    have hcpe : crossedPt τ = imagAxis (crossedPt τ).im (crossedPt τ).im_pos :=
      Work.Asymptotics.KaxisMid.eq_imagAxis_of_re_eq_zero hcpre
    have hj : jInvariantFun (imagAxis (crossedPt τ).im (crossedPt τ).im_pos)
        = jInvariantFun (imagAxis t ht) := by
      rw [← hcpe, crossedPt_jInvariantFun]; exact hcoin
    have hcpi_pos : 0 < (crossedPt τ).im := (crossedPt τ).im_pos
    rcases imagAxis_eq_or_inv hcpi_pos ht hj with h | h
    · right
      calc imagAxis t ht = imagAxis (crossedPt τ).im hcpi_pos := imagAxis_congr ht hcpi_pos h
        _ = crossedPt τ := hcpe.symm
    · exfalso
      have him_eq : (crossedPt τ).im = τ.im / ‖(τ : ℂ)‖ ^ 2 := crossedPt_im τ
      have hb : (crossedPt τ).im ≤ 2 / 3 := by
        rw [him_eq, div_le_iff₀ (by nlinarith [normSq_coe τ, τ.im_pos, sq_nonneg τ.re] :
          (0:ℝ) < ‖(τ : ℂ)‖ ^ 2)]
        nlinarith [hτ.2.2.1, hτ.2.2.2, hre_ge, hsq]
      have h6 : (1 : ℝ) / (crossedPt τ).im ≤ 5 / 8 := by rw [← h]; exact htw2
      have h5 := one_div_le_one_div_of_le hcpi_pos hb
      have h4 : (1 : ℝ) / ((2 : ℝ) / 3) = 3 / 2 := by norm_num
      linarith [h5, h4, h6]
  · -- second tangency arc
    have hcpre : (crossedPt τ).re = 0 := crossedPt_re_eq_zero_of_arc2 harc
    have hsq : ‖(τ : ℂ)‖ ^ 2 = -τ.re := by
      have h2 : ‖(τ : ℂ) + (1 / 2 : ℂ)‖ ^ 2 = (1 / 2 : ℝ) ^ 2 := by rw [harc]
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply] at h2
      have h3 : ((τ : ℂ) + (1 / 2 : ℂ)).re = τ.re + 1 / 2 := by simp
      have h4 : ((τ : ℂ) + (1 / 2 : ℂ)).im = τ.im := by simp
      rw [h3, h4] at h2
      rw [normSq_coe]; nlinarith [h2]
    have hre_le : (3 / 4 : ℝ) ≤ -τ.re := by
      have h := hτ.1
      rw [abs_of_nonpos (by nlinarith [hsq, normSq_coe τ, τ.im_pos] : τ.re ≤ 0)] at h
      exact h
    have hcpe : crossedPt τ = imagAxis (crossedPt τ).im (crossedPt τ).im_pos :=
      Work.Asymptotics.KaxisMid.eq_imagAxis_of_re_eq_zero hcpre
    have hj : jInvariantFun (imagAxis (crossedPt τ).im (crossedPt τ).im_pos)
        = jInvariantFun (imagAxis t ht) := by
      rw [← hcpe, crossedPt_jInvariantFun]; exact hcoin
    have hcpi_pos : 0 < (crossedPt τ).im := (crossedPt τ).im_pos
    rcases imagAxis_eq_or_inv hcpi_pos ht hj with h | h
    · right
      calc imagAxis t ht = imagAxis (crossedPt τ).im hcpi_pos := imagAxis_congr ht hcpi_pos h
        _ = crossedPt τ := hcpe.symm
    · exfalso
      have him_eq : (crossedPt τ).im = τ.im / ‖(τ : ℂ)‖ ^ 2 := crossedPt_im τ
      have hb : (crossedPt τ).im ≤ 2 / 3 := by
        rw [him_eq, div_le_iff₀ (by nlinarith [normSq_coe τ, τ.im_pos, sq_nonneg τ.re] :
          (0:ℝ) < ‖(τ : ℂ)‖ ^ 2)]
        nlinarith [hτ.2.2.1, hτ.2.2.2, hre_le, hsq]
      have h6 : (1 : ℝ) / (crossedPt τ).im ≤ 5 / 8 := by rw [← h]; exact htw2
      have h5 := one_div_le_one_div_of_le hcpi_pos hb
      have h4 : (1 : ℝ) / ((2 : ℝ) / 3) = 3 / 2 := by norm_num
      linarith [h5, h4, h6]

end Work.HFN.BlLow
