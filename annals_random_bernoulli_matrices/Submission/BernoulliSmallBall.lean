import Mathlib
import Submission.Threshold
import Submission.Prelim
import Submission.Helpers

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Measure
open scoped ENNReal BigOperators

noncomputable section

/-!
# Layer 5b: per-vector small-ball estimates via the threshold

The net-argument of the proof of Theorem~A repeatedly needs the following
per-vector estimate: for a vector `y` whose *threshold*
`thres_p(y,L) := sup {t ∈ (0,1] : cf(Σ bᵢyᵢ, t) > L·t}` is at most `S`, the
small ball probability of the Bernoulli linear form `Σ (bᵢ+s)yᵢ` at any radius
`r` is at most `L·max(2S, r)` (the factor `2` comes from the threshold
boundary).  This module formalizes that estimate on the canonical
Bernoulli(`p`) product space and, by law transfer, for any independent
Bernoulli(`p`) vector on an arbitrary probability space.
-/

namespace Submission.BernoulliSmallBall

open Submission.Threshold
open Submission.Helpers

/-- ENNReal bound on the concentration function from a threshold bound:
`cf(y,r) ≤ L·max(2S, r)` whenever `thres_p(y,L) ≤ S` and `1 ≤ L`. -/
lemma cfP_le_ofReal_of_threshold_le {n : ℕ} {p : unitInterval} {y : Fin n → ℝ}
    {L S r : ℝ} (hL : 1 ≤ L) (hr : 0 < r) (hS : 0 < S)
    (hthr : threshold (n := n) p y L ≤ S) :
    cfP (n := n) p y r ≤ ENNReal.ofReal (L * max (2 * S) r) := by
  by_cases hSr : S < r
  · have hthr_r : threshold (n := n) p y L < r := lt_of_le_of_lt hthr hSr
    have hle := cfP_le_slope_of_threshold (n := n) (p := p) (x := y) (L := L) hL hr hthr_r
    have hL0 : 0 ≤ L := le_trans zero_le_one hL
    have hmul : L * r ≤ L * max (2 * S) r :=
      mul_le_mul_of_nonneg_left (le_max_right (2 * S) r) hL0
    exact le_trans hle (ENNReal.ofReal_le_ofReal hmul)
  · have hrS : r ≤ S := le_of_not_gt hSr
    have hr2S : r ≤ 2 * S := by nlinarith
    have hmono : cfP (n := n) p y r ≤ cfP (n := n) p y (2 * S) := by
      unfold cfP
      exact levyConcentration_mono (berP (n := n) p)
        (fun omega : Fin n → ℝ => ∑ i : Fin n, omega i * y i) hr2S
    have h2S0 : 0 < 2 * S := by nlinarith
    have hthr2S : threshold (n := n) p y L < 2 * S := lt_of_le_of_lt hthr (by nlinarith)
    have hle2 := cfP_le_slope_of_threshold (n := n) (p := p) (x := y) (L := L) hL h2S0 hthr2S
    have hL0 : 0 ≤ L := le_trans zero_le_one hL
    have hmul : L * (2 * S) ≤ L * max (2 * S) r :=
      mul_le_mul_of_nonneg_left (le_max_left (2 * S) r) hL0
    exact le_trans (le_trans hmono hle2) (ENNReal.ofReal_le_ofReal hmul)

/-- Real-valued small-ball bound on the canonical Bernoulli(`p`) space:
`(berP p).real {omega | |Σᵢ omegaᵢ·yᵢ + c − lam| ≤ r} ≤ L·max(2S, r)` for every
shift `c` and center `lam` whenever `thres_p(y,L) ≤ S`. -/
lemma canonical_smallBall_real_le_of_threshold_le {n : ℕ} {p : unitInterval}
    {y : Fin n → ℝ} {L S r : ℝ} (hL : 1 ≤ L) (hr : 0 < r) (hS : 0 < S)
    (hthr : threshold (n := n) p y L ≤ S) (c lam : ℝ) :
    (berP (n := n) p).real {omega : Fin n → ℝ | |(∑ i : Fin n, omega i * y i) + c - lam| ≤ r}
      ≤ L * max (2 * S) r := by
  have hcf := cfP_le_ofReal_of_threshold_le (n := n) (p := p) (y := y) hL hr hS hthr
  have htau0 : 0 ≤ L * max (2 * S) r := by
    have hL0 : 0 ≤ L := le_trans zero_le_one hL
    have hmax0 : 0 ≤ max (2 * S) r := le_trans (le_of_lt hr) (le_max_right (2 * S) r)
    exact mul_nonneg hL0 hmax0
  have hEq :
      (berP (n := n) p).real {omega : Fin n → ℝ | |(∑ i : Fin n, omega i * y i) + c - lam| ≤ r}
        = (berP (n := n) p).real {omega : Fin n → ℝ | |(∑ i : Fin n, omega i * y i) - (lam - c)| ≤ r} := by
    apply congrArg (fun s : Set (Fin n → ℝ) => (berP (n := n) p).real s)
    ext omega
    simp only [Set.mem_setOf_eq]
    have hnum : |(∑ i : Fin n, omega i * y i) + c - lam| = |(∑ i : Fin n, omega i * y i) - (lam - c)| := by
      congr 1
      ring
    rw [hnum]
  rw [hEq]
  apply Submission.Prelim.real_mem_le_of_levyConcentration_le (P := berP (n := n) p)
    (ξ := fun omega : Fin n → ℝ => ∑ i : Fin n, omega i * y i) (t := r)
    (τ := L * max (2 * S) r) htau0 ?_ (lam - c)
  simpa [cfP] using hcf

/-- Law transfer: for any independent Bernoulli(`p`) vector `X` on a
probability space, the small-ball probability of `|Σᵢ Xᵢ·yᵢ + c − lam| ≤ r` is
bounded by `L·max(2S, r)` whenever `thres_p(y,L) ≤ S`.  This is the
per-row estimate used in the net argument for the rows of the shifted matrix
`B_n^1(p) + s·1·1ᵀ` (`c := s·Σᵢyᵢ`, `lam := 0`). -/
theorem bernoulli_vector_smallBall_le_of_threshold {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [MeasureTheory.IsProbabilityMeasure P] {p : unitInterval}
    {X : Fin n → Ω → ℝ} (hXmeas : ∀ i : Fin n, Measurable (X i))
    (hXind : ProbabilityTheory.iIndepFun X P)
    (hXlaw : ∀ i : Fin n, HasLaw (X i) (bernoulliMeasure 1 0 p) P)
    {y : Fin n → ℝ} {L S r : ℝ} (hL : 1 ≤ L) (hr : 0 < r) (hS : 0 < S)
    (hthr : threshold (n := n) p y L ≤ S) (c lam : ℝ) :
    P.real {omega : Ω | |(∑ i : Fin n, X i omega * y i) + c - lam| ≤ r} ≤ L * max (2 * S) r := by
  let T : Ω → Fin n → ℝ := fun omega i => X i omega
  let Sfun : Set (Fin n → ℝ) := {a : Fin n → ℝ | |(∑ i : Fin n, a i * y i) + c - lam| ≤ r}
  have hTmeas : Measurable T := by
    dsimp [T]
    fun_prop
  have hmeasS : MeasurableSet Sfun := by
    dsimp [Sfun]
    have hG : Measurable (fun a : Fin n → ℝ => (∑ i : Fin n, a i * y i) + c - lam) := by
      fun_prop
    change MeasurableSet ((fun a : Fin n → ℝ => |(∑ i : Fin n, a i * y i) + c - lam|) ⁻¹' (Set.Iic r))
    exact hG.abs (isClosed_Iic.measurableSet)
  have hEv : {omega : Ω | |(∑ i : Fin n, X i omega * y i) + c - lam| ≤ r} = T ⁻¹' Sfun := by
    ext omega
    simp only [Set.mem_preimage]
    dsimp [Sfun, T]
    exact Iff.rfl
  have hLawT : P.map T = berP (n := n) p := by
    dsimp [T]
    have hmeas_aem : ∀ i : Fin n, AEMeasurable (fun omega : Ω => X i omega) P :=
      fun i => (hXmeas i).aemeasurable
    have hjoint := (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
        (f := fun (i : Fin n) (omega : Ω) => X i omega) hmeas_aem).1 hXind
    calc
      P.map (fun omega : Ω => fun i : Fin n => X i omega) = Measure.pi (fun i : Fin n => P.map (X i)) := hjoint
      _ = Measure.pi (fun _ : Fin n => bernoulliMeasure 1 0 p) := by
        congr 1
        funext i
        exact (hXlaw i).map_eq
  have hc1 : P.real {omega : Ω | |(∑ i : Fin n, X i omega * y i) + c - lam| ≤ r}
      = (P.map T).real Sfun := by
    rw [Measure.real_def, Measure.real_def]
    congr 1
    rw [Measure.map_apply hTmeas hmeasS]
    rw [hEv]
  rw [hc1, hLawT]
  have hcan := canonical_smallBall_real_le_of_threshold_le (n := n) (p := p) (y := y)
    hL hr hS hthr c lam
  simpa [Sfun] using hcan

end Submission.BernoulliSmallBall
