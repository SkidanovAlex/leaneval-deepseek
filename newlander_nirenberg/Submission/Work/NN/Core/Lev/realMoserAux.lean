import Mathlib
import Submission.Work.NN.Core.CnPert
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.NN.Core.gagliardoNirenbergGeomMean
import Submission.Work.NN.Core.Lev.nnGradBoundPoint
import Submission.Work.NN.Core.Lev.exists_polydisc_cutoff_lipschitz
import Submission.Work.NN.Core.Lev.ofReal_norm_le_liminf_eLpNorm_on
import Submission.Work.NN.Core.Lev.moserStepEnergyBound
import Submission.Work.NN.Core.contDiff_one_mul_of_support
import Submission.Work.NN.Core.volume_polydisc

/-!
# Auxiliary lemmas for the real-exponent Moser sup bound

Basic pointwise / regularity facts about the Wirtinger energy
`wEnergy h z = Σ_j (‖∂_j h z‖² + ‖∂̄_j h z‖²)`, the function `z ↦ ‖h z‖²`, its real powers, and
the `L^p` "power" identity used by the Moser iteration.
-/

namespace Work.NN.Core.Lev

open scoped NNReal ENNReal ContDiff Topology
open Set MeasureTheory Filter

noncomputable section

variable {n : ℕ}

/-- The gain factor `q = (2n)' = 2n/(2n-1) > 1` of the geometric-mean Gagliardo–Nirenberg
inequality in complex dimension `n`. -/
def moserQ (n : ℕ) : ℝ := ((NNReal.conjExponent ((2 * n : ℕ) : ℝ≥0)) : ℝ)

lemma moserQ_one_lt {n : ℕ} (hn : 0 < n) : 1 < moserQ n := by
  rw [moserQ]
  have hsub : ((1 : ℝ≥0) ≤ ((2 * n : ℕ) : ℝ≥0)) := by
    have : (1 : ℕ) ≤ 2 * n := by omega
    exact_mod_cast this
  have h2 : ((((2 * n : ℕ) : ℝ≥0) - 1 : ℝ≥0) : ℝ) = (((2 * n : ℕ) : ℝ≥0) : ℝ) - 1 := by
    rw [NNReal.coe_sub hsub]; norm_num
  have h1 : ((NNReal.conjExponent (((2 * n : ℕ) : ℝ≥0)) : ℝ)) =
      (((2 * n : ℕ) : ℝ≥0) : ℝ) / ((((2 * n : ℕ) : ℝ≥0) : ℝ) - 1) := by
    rw [NNReal.conjExponent, NNReal.coe_div, h2]
  rw [h1]
  have hp' : (1 : ℝ) < (((2 * n : ℕ) : ℝ≥0) : ℝ) := by
    have : (1 : ℕ) < 2 * n := by omega
    exact_mod_cast this
  rw [lt_div_iff₀ (by linarith : (0 : ℝ) < (((2 * n : ℕ) : ℝ≥0) : ℝ) - 1)]
  linarith

lemma moserQ_pos {n : ℕ} (hn : 0 < n) : 0 < moserQ n := lt_trans zero_lt_one (moserQ_one_lt hn)

/-- The Wirtinger energy density `Σ_j (‖∂_j h‖² + ‖∂̄_j h‖²)` of `h`. -/
def wEnergy (h : Cn n → ℂ) (z : Cn n) : ℝ :=
  ∑ j, (‖Work.CR.Flat.dCoord j h z‖ ^ 2 + ‖Work.CR.Flat.dbarCoord j h z‖ ^ 2)

lemma wEnergy_nonneg (h : Cn n → ℂ) (z : Cn n) : 0 ≤ wEnergy h z :=
  Finset.sum_nonneg fun j _ => by positivity

/-- The pointwise bound of the real differential by the Wirtinger energy (explicit constant). -/
lemma fderiv_le_wEnergy (hn : 0 < n) (h : Cn n → ℂ) (z : Cn n) :
    ‖fderiv ℝ h z‖ ^ 2 ≤ 8 * (n : ℝ) * wEnergy h z := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  set T : ℝ := wEnergy h z with hT
  set S : ℝ := ∑ j, (‖Work.CR.Flat.dCoord j h z‖ + ‖Work.CR.Flat.dbarCoord j h z‖) with hS
  have h1 : ‖fderiv ℝ h z‖ ≤ 2 * S := by
    rw [hS]
    exact Work.CR.Flat.Cauchy.bmCz.norm_fderiv_le_sum_wirtinger h z
  have h2 : ‖fderiv ℝ h z‖ ^ 2 ≤ 4 * S ^ 2 := by
    have h := pow_le_pow_left₀ (norm_nonneg (fderiv ℝ h z)) h1 2
    nlinarith [h]
  have h4 : ∀ j : Fin n, (‖Work.CR.Flat.dCoord j h z‖ + ‖Work.CR.Flat.dbarCoord j h z‖) ^ 2
      ≤ 2 * (‖Work.CR.Flat.dCoord j h z‖ ^ 2 + ‖Work.CR.Flat.dbarCoord j h z‖ ^ 2) := fun j =>
    by nlinarith [sq_nonneg (‖Work.CR.Flat.dCoord j h z‖ - ‖Work.CR.Flat.dbarCoord j h z‖)]
  have h3 : S ^ 2 ≤ 2 * (n : ℝ) * T := by
    rw [hS, hT, wEnergy]
    calc (∑ j, (‖Work.CR.Flat.dCoord j h z‖ + ‖Work.CR.Flat.dbarCoord j h z‖)) ^ 2
        ≤ (n : ℝ) * ∑ j,
            (‖Work.CR.Flat.dCoord j h z‖ + ‖Work.CR.Flat.dbarCoord j h z‖) ^ 2 := by
          simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ)
            (f := fun j : Fin n => ‖Work.CR.Flat.dCoord j h z‖
              + ‖Work.CR.Flat.dbarCoord j h z‖)
      _ ≤ (n : ℝ) * ∑ j, 2 * (‖Work.CR.Flat.dCoord j h z‖ ^ 2
            + ‖Work.CR.Flat.dbarCoord j h z‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => h4 j) (by positivity)
      _ = 2 * (n : ℝ) * ∑ j, (‖Work.CR.Flat.dCoord j h z‖ ^ 2
            + ‖Work.CR.Flat.dbarCoord j h z‖ ^ 2) := by
          rw [← Finset.mul_sum]; ring
  calc ‖fderiv ℝ h z‖ ^ 2 ≤ 4 * S ^ 2 := h2
    _ ≤ 4 * (2 * (n : ℝ) * T) := by nlinarith [h3]
    _ = 8 * (n : ℝ) * T := by ring

/-- The norm-squared function `z ↦ ‖h z‖²` is `C¹` on the polydisc. -/
lemma contDiffOn_normSq (h : Cn n → ℂ) {ρ : Fin n → ℝ}
    (hh : ContDiffOn ℝ 1 h (Work.CR.Flat.polydisc 0 ρ)) :
    ContDiffOn ℝ 1 (fun z => ‖h z‖ ^ 2) (Work.CR.Flat.polydisc 0 ρ) := by
  have h1 : (fun z : Cn n => ‖h z‖ ^ 2) = (fun w : ℂ => ‖w‖ ^ 2) ∘ h := rfl
  rw [h1]
  exact (contDiff_norm_sq ℝ (n := (1 : ℕ∞))).comp_contDiffOn hh

/-- Derivative of `z ↦ ‖h z‖²`, in operator-norm form. -/
lemma normSq_fderiv_le (h : Cn n → ℂ) {ρ : Fin n → ℝ}
    (hh : ContDiffOn ℝ 1 h (Work.CR.Flat.polydisc 0 ρ)) {z : Cn n}
    (hz : z ∈ Work.CR.Flat.polydisc 0 ρ) :
    ‖fderiv ℝ (fun z => ‖h z‖ ^ 2) z‖ ≤ 2 * ‖h z‖ * ‖fderiv ℝ h z‖ := by
  have hhd : DifferentiableAt ℝ h z :=
    (hh.differentiableOn (by norm_num)).differentiableAt
      ((Work.CR.Flat.isOpen_polydisc 0 ρ).mem_nhds hz)
  have hfd : HasFDerivAt (fun z => ‖h z‖ ^ 2)
      (2 • (innerSL ℝ (h z)).comp (fderiv ℝ h z)) z := hhd.hasFDerivAt.norm_sq
  rw [hfd.fderiv]
  calc ‖(2 : ℕ) • (innerSL ℝ (h z)).comp (fderiv ℝ h z)‖
      ≤ 2 * ‖(innerSL ℝ (h z)).comp (fderiv ℝ h z)‖ := norm_nsmul_le
    _ ≤ 2 * (‖innerSL ℝ (h z)‖ * ‖fderiv ℝ h z‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (by norm_num)
    _ = 2 * ‖h z‖ * ‖fderiv ℝ h z‖ := by rw [innerSL_apply_norm]; ring

/-- `(‖h ·‖²)^γ` is `C¹` on the polydisc for `γ ≥ 1`. -/
lemma contDiffOn_normSq_rpow (h : Cn n → ℂ) {ρ : Fin n → ℝ} {γ : ℝ} (hγ : 1 ≤ γ)
    (hh : ContDiffOn ℝ 1 h (Work.CR.Flat.polydisc 0 ρ)) :
    ContDiffOn ℝ 1 (fun z => (‖h z‖ ^ 2) ^ γ) (Work.CR.Flat.polydisc 0 ρ) := by
  have h1 : (fun z : Cn n => (‖h z‖ ^ 2) ^ γ)
      = (fun x : ℝ => x ^ γ) ∘ (fun z => ‖h z‖ ^ 2) := rfl
  rw [h1]
  refine (Real.contDiff_rpow_const_of_le (p := γ) (n := 1) (by simpa using hγ)).comp_contDiffOn ?_
  exact contDiffOn_normSq h hh

/-- Derivative of `z ↦ (‖h z‖²)^γ` for `γ ≥ 1`, in operator-norm form. -/
lemma normSq_rpow_fderiv_le (h : Cn n → ℂ) {ρ : Fin n → ℝ} {γ : ℝ} (hγ : 1 ≤ γ)
    (hh : ContDiffOn ℝ 1 h (Work.CR.Flat.polydisc 0 ρ)) {z : Cn n}
    (hz : z ∈ Work.CR.Flat.polydisc 0 ρ) :
    ‖fderiv ℝ (fun z => (‖h z‖ ^ 2) ^ γ) z‖
      ≤ γ * (‖h z‖ ^ 2) ^ (γ - 1) * (2 * ‖h z‖ * ‖fderiv ℝ h z‖) := by
  have hhd : DifferentiableAt ℝ h z :=
    (hh.differentiableOn (by norm_num)).differentiableAt
      ((Work.CR.Flat.isOpen_polydisc 0 ρ).mem_nhds hz)
  have htd : HasFDerivAt (fun z => ‖h z‖ ^ 2)
      (2 • (innerSL ℝ (h z)).comp (fderiv ℝ h z)) z := hhd.hasFDerivAt.norm_sq
  have hderiv := Real.hasDerivAt_rpow_const (x := ‖h z‖ ^ 2) (p := γ) (Or.inr hγ)
  have hcomp := hderiv.comp_hasFDerivAt z htd
  have hf : fderiv ℝ (fun z => (‖h z‖ ^ 2) ^ γ) z
      = (γ * (‖h z‖ ^ 2) ^ (γ - 1)) •
          ((2 : ℕ) • (innerSL ℝ (h z)).comp (fderiv ℝ h z)) := by
    simpa [Function.comp_def] using hcomp.fderiv
  rw [hf, norm_smul, Real.norm_of_nonneg (by positivity)]
  have hY : ‖(2 : ℕ) • (innerSL ℝ (h z)).comp (fderiv ℝ h z)‖
      ≤ 2 * ‖h z‖ * ‖fderiv ℝ h z‖ := by
    calc ‖(2 : ℕ) • (innerSL ℝ (h z)).comp (fderiv ℝ h z)‖
        ≤ 2 * ‖(innerSL ℝ (h z)).comp (fderiv ℝ h z)‖ := norm_nsmul_le
      _ ≤ 2 * (‖innerSL ℝ (h z)‖ * ‖fderiv ℝ h z‖) :=
          mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (by norm_num)
      _ = 2 * ‖h z‖ * ‖fderiv ℝ h z‖ := by rw [innerSL_apply_norm]; ring
  exact mul_le_mul_of_nonneg_left hY (by positivity)

/-- `‖ofRealCLM.comp S‖ = ‖S‖`. -/
lemma norm_comp_ofRealCLM {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : E →L[ℝ] ℝ) : ‖Complex.ofRealCLM.comp S‖ = ‖S‖ := by
  apply le_antisymm
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
    simpa [Complex.norm_real, Real.norm_eq_abs] using ContinuousLinearMap.le_opNorm S v
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
    have h : ‖S v‖ = ‖(Complex.ofRealCLM.comp S) v‖ := by
      simp [Complex.norm_real, Real.norm_eq_abs]
    rw [h]
    exact ContinuousLinearMap.le_opNorm _ v

/-- The complexified version: `z ↦ ((‖h z‖²)^γ : ℂ)` is `C¹` on the polydisc for `γ ≥ 1`. -/
lemma contDiffOn_normSq_rpow_complex (h : Cn n → ℂ) {ρ : Fin n → ℝ} {γ : ℝ} (hγ : 1 ≤ γ)
    (hh : ContDiffOn ℝ 1 h (Work.CR.Flat.polydisc 0 ρ)) :
    ContDiffOn ℝ 1 (fun z => (((‖h z‖ ^ 2) ^ γ : ℝ) : ℂ)) (Work.CR.Flat.polydisc 0 ρ) :=
  Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiffOn_normSq_rpow h hγ hh)

/-- The norm of the Fréchet derivative of the complexified `(‖h ·‖²)^γ`. -/
lemma normSq_rpow_fderiv_complex_le (h : Cn n → ℂ) {ρ : Fin n → ℝ} {γ : ℝ} (hγ : 1 ≤ γ)
    (hh : ContDiffOn ℝ 1 h (Work.CR.Flat.polydisc 0 ρ)) {z : Cn n}
    (hz : z ∈ Work.CR.Flat.polydisc 0 ρ) :
    ‖fderiv ℝ (fun z => (((‖h z‖ ^ 2) ^ γ : ℝ) : ℂ)) z‖
      ≤ γ * (‖h z‖ ^ 2) ^ (γ - 1) * (2 * ‖h z‖ * ‖fderiv ℝ h z‖) := by
  have hcd : ContDiffOn ℝ 1 (fun z => (‖h z‖ ^ 2) ^ γ) (Work.CR.Flat.polydisc 0 ρ) :=
    contDiffOn_normSq_rpow h hγ hh
  have hd : DifferentiableAt ℝ (fun z => (‖h z‖ ^ 2) ^ γ) z :=
    (hcd.differentiableOn (by norm_num)).differentiableAt
      ((Work.CR.Flat.isOpen_polydisc 0 ρ).mem_nhds hz)
  have hof : (fun z : Cn n => (((‖h z‖ ^ 2) ^ γ : ℝ) : ℂ))
      = Complex.ofRealCLM ∘ (fun z => (‖h z‖ ^ 2) ^ γ) := rfl
  rw [hof, fderiv_comp z Complex.ofRealCLM.differentiableAt hd, ContinuousLinearMap.fderiv]
  rw [norm_comp_ofRealCLM]
  exact normSq_rpow_fderiv_le h hγ hh hz

/-- `‖∂_j h z‖ ≤ ‖dh_z‖`. -/
lemma dCoord_le_fderiv (h : Cn n → ℂ) (z : Cn n) (j : Fin n) :
    ‖Work.CR.Flat.dCoord j h z‖ ≤ ‖fderiv ℝ h z‖ := by
  have h1 : ‖fderiv ℝ h z (Pi.single j (1:ℂ))‖ ≤ ‖fderiv ℝ h z‖ := by
    calc ‖fderiv ℝ h z (Pi.single j (1:ℂ))‖
        ≤ ‖fderiv ℝ h z‖ * ‖(Pi.single j (1:ℂ) : Fin n → ℂ)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ h z‖ := by rw [Pi.norm_single]; norm_num
  have h2 : ‖fderiv ℝ h z (Pi.single j Complex.I)‖ ≤ ‖fderiv ℝ h z‖ := by
    calc ‖fderiv ℝ h z (Pi.single j Complex.I)‖
        ≤ ‖fderiv ℝ h z‖ * ‖(Pi.single j Complex.I : Fin n → ℂ)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ h z‖ := by rw [Pi.norm_single]; norm_num
  have hI : ‖Complex.I * fderiv ℝ h z (Pi.single j Complex.I)‖ ≤ ‖fderiv ℝ h z‖ := by
    rw [norm_mul, Complex.norm_I, one_mul]; exact h2
  rw [Work.CR.Flat.dCoord]
  have h3 : ‖(1 / 2 : ℂ) * (fderiv ℝ h z (Pi.single j 1)
        - Complex.I * fderiv ℝ h z (Pi.single j Complex.I))‖
      = (1/2) * ‖fderiv ℝ h z (Pi.single j 1)
        - Complex.I * fderiv ℝ h z (Pi.single j Complex.I)‖ := by
    rw [norm_mul, show ‖(1 / 2 : ℂ)‖ = (1/2 : ℝ) by norm_num]
  rw [h3]
  calc (1/2 : ℝ) * ‖fderiv ℝ h z (Pi.single j 1)
        - Complex.I * fderiv ℝ h z (Pi.single j Complex.I)‖
      ≤ (1/2) * (‖fderiv ℝ h z (Pi.single j 1)‖
          + ‖Complex.I * fderiv ℝ h z (Pi.single j Complex.I)‖) := by
        gcongr; exact norm_sub_le _ _
    _ ≤ (1/2) * (‖fderiv ℝ h z‖ + ‖fderiv ℝ h z‖) :=
        mul_le_mul_of_nonneg_left (add_le_add h1 hI) (by norm_num)
    _ = ‖fderiv ℝ h z‖ := by ring

/-- `‖∂̄_j h z‖ ≤ ‖dh_z‖`. -/
lemma dbarCoord_le_fderiv (h : Cn n → ℂ) (z : Cn n) (j : Fin n) :
    ‖Work.CR.Flat.dbarCoord j h z‖ ≤ ‖fderiv ℝ h z‖ := by
  have h1 : ‖fderiv ℝ h z (Pi.single j (1:ℂ))‖ ≤ ‖fderiv ℝ h z‖ := by
    calc ‖fderiv ℝ h z (Pi.single j (1:ℂ))‖
        ≤ ‖fderiv ℝ h z‖ * ‖(Pi.single j (1:ℂ) : Fin n → ℂ)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ h z‖ := by rw [Pi.norm_single]; norm_num
  have h2 : ‖fderiv ℝ h z (Pi.single j Complex.I)‖ ≤ ‖fderiv ℝ h z‖ := by
    calc ‖fderiv ℝ h z (Pi.single j Complex.I)‖
        ≤ ‖fderiv ℝ h z‖ * ‖(Pi.single j Complex.I : Fin n → ℂ)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ h z‖ := by rw [Pi.norm_single]; norm_num
  have hI : ‖Complex.I * fderiv ℝ h z (Pi.single j Complex.I)‖ ≤ ‖fderiv ℝ h z‖ := by
    rw [norm_mul, Complex.norm_I, one_mul]; exact h2
  rw [Work.CR.Flat.dbarCoord]
  have h3 : ‖(1 / 2 : ℂ) * (fderiv ℝ h z (Pi.single j 1)
        + Complex.I * fderiv ℝ h z (Pi.single j Complex.I))‖
      = (1/2) * ‖fderiv ℝ h z (Pi.single j 1)
        + Complex.I * fderiv ℝ h z (Pi.single j Complex.I)‖ := by
    rw [norm_mul, show ‖(1 / 2 : ℂ)‖ = (1/2 : ℝ) by norm_num]
  rw [h3]
  calc (1/2 : ℝ) * ‖fderiv ℝ h z (Pi.single j 1)
        + Complex.I * fderiv ℝ h z (Pi.single j Complex.I)‖
      ≤ (1/2) * (‖fderiv ℝ h z (Pi.single j 1)‖
          + ‖Complex.I * fderiv ℝ h z (Pi.single j Complex.I)‖) := by
        gcongr; exact norm_add_le _ _
    _ ≤ (1/2) * (‖fderiv ℝ h z‖ + ‖fderiv ℝ h z‖) :=
        mul_le_mul_of_nonneg_left (add_le_add h1 hI) (by norm_num)
    _ = ‖fderiv ℝ h z‖ := by ring

/-- `wEnergy h z ≤ 2n ‖dh_z‖²`. -/
lemma wEnergy_le_fderiv (h : Cn n → ℂ) (z : Cn n) :
    wEnergy h z ≤ 2 * (n : ℝ) * ‖fderiv ℝ h z‖ ^ 2 := by
  have h2 : ∀ j : Fin n, ‖Work.CR.Flat.dCoord j h z‖ ^ 2
      + ‖Work.CR.Flat.dbarCoord j h z‖ ^ 2 ≤ 2 * ‖fderiv ℝ h z‖ ^ 2 := by
    intro j
    have h1 := dCoord_le_fderiv h z j
    have h2 := dbarCoord_le_fderiv h z j
    nlinarith [norm_nonneg (fderiv ℝ h z), norm_nonneg (Work.CR.Flat.dCoord j h z),
      norm_nonneg (Work.CR.Flat.dbarCoord j h z), sq_nonneg (‖fderiv ℝ h z‖)]
  rw [wEnergy]
  calc ∑ j, (‖Work.CR.Flat.dCoord j h z‖ ^ 2 + ‖Work.CR.Flat.dbarCoord j h z‖ ^ 2)
      ≤ ∑ _j : Fin n, 2 * ‖fderiv ℝ h z‖ ^ 2 := Finset.sum_le_sum fun j _ => h2 j
    _ = 2 * (n : ℝ) * ‖fderiv ℝ h z‖ ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- A `C¹` function is bounded on any strictly smaller polydisc. -/
lemma exists_bound_fderiv {h : Cn n → ℂ} {ρ s : Fin n → ℝ} (hsρ : ∀ j, s j < ρ j)
    (hh : ContDiffOn ℝ 1 h (Work.CR.Flat.polydisc 0 ρ)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z ∈ Work.CR.Flat.polydisc 0 s, ‖fderiv ℝ h z‖ ≤ K := by
  set cl : Set (Cn n) := {z | ∀ j, ‖z j‖ ≤ s j} with hcldef
  have hcl_compact : IsCompact cl := by
    have h : cl = Set.pi Set.univ (fun j => Metric.closedBall (0:ℂ) (s j)) := by
      ext z; simp [hcldef, Metric.mem_closedBall, dist_eq_norm]
    rw [h]; exact isCompact_univ_pi fun j => isCompact_closedBall 0 (s j)
  have hclρ : cl ⊆ Work.CR.Flat.polydisc 0 ρ := fun z hz j =>
    lt_of_le_of_lt (by simpa using hz j) (hsρ j)
  have hcont : ContinuousOn (fderiv ℝ h) (Work.CR.Flat.polydisc 0 ρ) :=
    hh.continuousOn_fderiv_of_isOpen (Work.CR.Flat.isOpen_polydisc 0 ρ) (by norm_num)
  obtain ⟨K, hK⟩ := hcl_compact.exists_bound_of_continuousOn (hcont.mono hclρ)
  refine ⟨max K 0, le_max_right _ _, fun z hz => ?_⟩
  exact le_trans (hK z (fun j => by simpa using le_of_lt (hz j))) (le_max_left _ _)

/-- The Wirtinger energy is bounded on a strictly smaller polydisc. -/
lemma exists_bound_wEnergy {h : Cn n → ℂ} {ρ s : Fin n → ℝ} (hsρ : ∀ j, s j < ρ j)
    (hh : ContDiffOn ℝ 1 h (Work.CR.Flat.polydisc 0 ρ)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z ∈ Work.CR.Flat.polydisc 0 s, wEnergy h z ≤ K := by
  obtain ⟨Kf, hKf0, hKf⟩ := exists_bound_fderiv hsρ hh
  refine ⟨2 * (n : ℝ) * Kf ^ 2, by positivity, fun z hz => ?_⟩
  refine (wEnergy_le_fderiv h z).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact pow_le_pow_left₀ (norm_nonneg _) (hKf z hz) 2

/-- For a nonnegative `v : α → ℝ` and `p > 0`, the `p`-th power of the `L^p` (semi)norm is the
`lintegral` of `v^p`. -/
lemma eLpNorm_ofReal_rpow {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    {v : α → ℝ} {p : ℝ} (hp : 0 < p) (hv : MeasureTheory.AEStronglyMeasurable v μ)
    (hvnn : 0 ≤ᵐ[μ] v) :
    (MeasureTheory.eLpNorm v (ENNReal.ofReal p) μ) ^ p
      = ∫⁻ x, ENNReal.ofReal (v x) ^ p ∂μ := by
  have hpne : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp).ne'
  have hptop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm hpne hptop hv]
  rw [ENNReal.toReal_ofReal hp.le]
  rw [← ENNReal.rpow_mul]
  rw [show (1 / p) * p = 1 by field_simp]
  rw [ENNReal.rpow_one]
  refine MeasureTheory.lintegral_congr_ae ?_
  filter_upwards [hvnn] with x hx
  rw [Real.enorm_eq_ofReal hx]

/-- `eLpNorm` of a complex function equals `eLpNorm` of its norm. -/
lemma eLpNorm_norm_eq {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    {F : Type*} [NormedAddCommGroup F] {f : α → F}
    (hf : MeasureTheory.AEStronglyMeasurable f μ) (p : ENNReal) :
    MeasureTheory.eLpNorm f p μ
      = MeasureTheory.eLpNorm (fun x => (‖f x‖ : ℝ)) p μ := by
  refine MeasureTheory.eLpNorm_congr_norm_ae hf hf.norm ?_
  filter_upwards with x
  rw [Real.norm_of_nonneg (norm_nonneg _)]

end
end Work.NN.Core.Lev
