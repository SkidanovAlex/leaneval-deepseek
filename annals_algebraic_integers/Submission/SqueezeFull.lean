import Submission.SqueezeCore
import Submission.SqzKernel
import Submission.SqzTwoD
import Submission.SqzAvg
import Submission.SqzLogProd
import Submission.SqzExist
import Mathlib.Tactic

/-! # Squeeze core completion

Continues `Submission.SqueezeCore` with the analytic lemmas whose proofs were
carried out in the modules `SqzKernel`, `SqzTwoD`, `SqzAvg`, `SqzLogProd`,
`SqzExist` (aliases), plus the good-tuple existence lemma.
-/

noncomputable section

open Polynomial
open scoped Real BigOperators Topology ENNReal
open MeasureTheory

namespace Submission.SqueezeCore

open Submission.MinkBox
open Submission.Contracts
open Submission.EnergyHalf
open Submission.WeightedNorm
open Submission.SerreExample
open Submission.PotentialContinuity
open Submission.PotentialDefs
open Submission.WnormToolkit
open Submission.SupportConcentration

/-! ## Aliases of the analytic lemmas (proved in the sibling modules) -/

/-- There is a uniform bound on `∫_y |log|x−y||dμ(y)` for `x` in the interval. -/
lemma uniform_abs_log_kernel_bound :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x : ℝ, x ∈ Set.Icc aSerre bSerre →
        (∫ y : ℝ, |Real.log (|x - y|)| ∂muSerre) ≤ C :=
  Submission.SqzKernel.uniform_abs_log_kernel_bound

/-- `log|u−v|` is integrable over the two-fold product. -/
lemma integrable_prod_log_sub :
    Integrable (fun p : ℝ × ℝ => Real.log (|p.1 - p.2|)) (muSerre.prod muSerre) :=
  Submission.SqzTwoD.integrable_prod_log_sub

/-- `∫∫ log|u−v| = −energy`. -/
lemma integral_prod_log_sub_energy :
    (∫ p : ℝ × ℝ, Real.log (|p.1 - p.2|) ∂(muSerre.prod muSerre)) = -energy :=
  Submission.SqzTwoD.integral_prod_log_sub_energy

/-- the absolute kernel is integrable over the 2D product. -/
lemma integrable_abs_log_sub_2d :
    Integrable (fun p : ℝ × ℝ => |Real.log (|p.1 - p.2|)|) (muSerre.prod muSerre) :=
  Submission.SqzTwoD.integrable_abs_log_sub_2d

/-- `pairLog` is integrable over π_d. -/
lemma integrable_pairLog {d : ℕ} :
    Integrable (fun x : Fin d → ℝ => pairLog d x) (pserre d) :=
  Submission.SqzAvg.integrable_pairLog

/-- the average of the single-coordinate terms -/
lemma integral_sum_coordLog {d n : ℕ} (R : Polynomial ℤ) (hR : R ≠ 0) :
    (∫ x : Fin d → ℝ, (∑ k : Fin d, coordLog n R (x k)) ∂pserre d) =
      (d : ℝ) * (∫ x : ℝ, coordLog n R x ∂muSerre) :=
  Submission.SqzAvg.integral_sum_coordLog R hR

/-- the average of the pairwise terms -/
lemma integral_pairLog_eq {d : ℕ} :
    (∫ x : Fin d → ℝ, pairLog d x ∂pserre d) =
      ((d : ℝ) * (d - 1) / 2) * (-energy) :=
  Submission.SqzAvg.integral_pairLog_eq

/-- The average of `totalLog` equals the closed form. -/
lemma integral_totalLog_eq {d n : ℕ} (R : Polynomial ℤ) (hR : R ≠ 0) :
    (∫ x : Fin d → ℝ, totalLog d n R x ∂pserre d) =
      (d : ℝ) * (∫ x : ℝ, coordLog n R x ∂muSerre) +
        ((d : ℝ) * (d - 1) / 2) * (-energy) :=
  Submission.SqzAvg.integral_totalLog_eq R hR

/-- The totalLog average is bounded below by `(d·n − d(d−1)/2)·energy`. -/
lemma integral_totalLog_ge {d n : ℕ} (R : Polynomial ℤ) (hR : R ≠ 0)
    (hRint : 0 ≤ ∫ x : ℝ, Real.log (|Polynomial.aeval x R|) ∂muSerre) :
    ((d : ℝ) * (n : ℝ) - (d : ℝ) * (d - 1) / 2) * energy ≤
      (∫ x : Fin d → ℝ, totalLog d n R x ∂pserre d) :=
  Submission.SqzAvg.integral_totalLog_ge R hR hRint

/-- Pointwise: on the good set `log F = totalLog`. -/
lemma log_tupleF_eq_totalLog {d n : ℕ} (R : Polynomial ℤ) {x : Fin d → ℝ}
    (hx : GoodTuple d R x) :
    Real.log (tupleF d n R x) = totalLog d n R x :=
  Submission.SqzLogProd.log_tupleF_eq_totalLog R hx

/-- if an integrable function has integral ≥ c on a probability space, some
point has value ≥ c. -/
lemma exists_ge_integral {α : Type*} [MeasurableSpace α] {ν : Measure α} [IsProbabilityMeasure ν]
    {f : α → ℝ} (hf : Integrable f ν) {c : ℝ} (hc : c ≤ ∫ x, f x ∂ν) :
    ∃ x : α, c ≤ f x :=
  Submission.SqzExist.exists_ge_integral hf hc


/-! ## Integrability / positivity of `tupleF` on the good set -/

/-- per-coordinate `coordLog` is integrable (1D). -/
lemma integrable_coordLog_1d {n : ℕ} (R : Polynomial ℤ) (hR : R ≠ 0) :
    Integrable (fun x : ℝ => coordLog n R x) muSerre := by
  unfold coordLog
  exact (integrable_log_abs_aeval R hR).add (integrable_const_mul_log_weight n)


/-- `totalLog` is integrable over the d-fold product. -/
lemma integrable_totalLog {d n : ℕ} (R : Polynomial ℤ) (hR : R ≠ 0) :
    Integrable (fun x : Fin d → ℝ => totalLog d n R x) (pserre d) := by
  change Integrable (fun x : Fin d → ℝ =>
      (∑ k : Fin d, coordLog n R (x k)) + pairLog d x) (pserre d)
  refine MeasureTheory.Integrable.add ?_ ?_
  · -- sum over coordinates
    apply MeasureTheory.integrable_finsetSum
    intro k _
    exact integrable_comp_eval_mu k (coordLog n R) (integrable_coordLog_1d R hR)
  · exact integrable_pairLog

/-- `tupleF` is strictly positive on the good set. -/
lemma tupleF_pos_of_good {d n : ℕ} (R : Polynomial ℤ) {x : Fin d → ℝ}
    (hx : GoodTuple d R x) : 0 < tupleF d n R x := by
  unfold tupleF
  refine mul_pos ?_ ?_
  · refine Finset.prod_pos ?_
    intro k _
    refine mul_pos ?_ ?_
    · exact pow_pos (weight_pos muSerre (x k)) n
    · exact abs_pos.mpr (hx.2.1 k)
  · -- pairProd > 0 : all inner |x_i − x_j| > 0 when i < j (distinct)
    unfold MinkBox.pairProd
    refine Finset.prod_pos ?_
    intro i _
    refine Finset.prod_pos ?_
    intro j hj
    exact abs_pos.mpr (sub_ne_zero.mpr (hx.2.2.ne (by
      have hlt : i < j := (Finset.mem_filter.mp hj).2
      exact (ne_of_lt hlt))))

/-! ## Mean-value facts over π_d -/

/-- a positive-measure set is nonempty. -/
lemma nonempty_of_measure_pos {α : Type*} [MeasurableSpace α] {ν : Measure α}
    {s : Set α} (hs : 0 < ν s) : s.Nonempty := by
  rcases s.eq_empty_or_nonempty with hs0 | hsN
  · exfalso
    have h : ν s = 0 := by rw [hs0]; simp
    exact (not_lt_of_ge (le_of_eq h)) hs
  · exact hsN

/-- strict-ae positivity gives strictly positive integral (probability space). -/
lemma integral_pos_of_ae_pos {α : Type*} [MeasurableSpace α] {ν : Measure α}
    [IsProbabilityMeasure ν] {g : α → ℝ} (hg : Integrable g ν)
    (hgpos : ∀ᵐ x ∂ν, 0 < g x) : 0 < ∫ x, g x ∂ν := by
  have hgNneg : 0 ≤ᵐ[ν] g := hgpos.mono (fun x hx => le_of_lt hx)
  have hnn : 0 ≤ ∫ x, g x ∂ν := MeasureTheory.integral_nonneg_of_ae hgNneg
  by_contra hle
  have hz : (∫ x, g x ∂ν) = 0 := le_antisymm (le_of_not_gt hle) hnn
  have hgz : g =ᵐ[ν] 0 := (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae hgNneg hg).1 hz
  have hfalse : ∀ᵐ x ∂ν, False := by
    filter_upwards [hgpos, hgz] with x hpos hz
    rw [hz] at hpos
    norm_num at hpos
  have huniv : ν Set.univ = 0 := by
    rw [MeasureTheory.ae_iff] at hfalse
    simpa using hfalse
  have hprob : ν Set.univ = 1 := IsProbabilityMeasure.measure_univ
  rw [hprob] at huniv
  norm_num at huniv

/-- The good set has full measure (probability): complement null. -/
lemma ae_good {d : ℕ} (R : Polynomial ℤ) (hR : R ≠ 0) :
    (∀ᵐ x ∂(pserre d), GoodTuple d R x) := by
  rw [MeasureTheory.ae_iff]
  exact measure_good_compl R hR

/-- The good set has measure one. -/
lemma measure_good_set {d : ℕ} (R : Polynomial ℤ) (hR : R ≠ 0) :
    pserre d {x : Fin d → ℝ | GoodTuple d R x} = 1 := measure_good R hR

/-! ## Existence of a good tuple with large value -/

/-- Existence of a good tuple where the tuple product beats the target. -/
lemma exists_good_tuple {d n : ℕ} (hd : 1 ≤ d) (R : Polynomial ℤ) (hR : R ≠ 0)
    (hRint : 0 ≤ ∫ x : ℝ, Real.log (|Polynomial.aeval x R|) ∂muSerre) :
    ∃ x : Fin d → ℝ, GoodTuple d R x ∧
      Real.exp (((d : ℝ) * (n : ℝ) - (d : ℝ) * (d - 1) / 2) * energy) ≤ tupleF d n R x := by
  let ν : Measure (Fin d → ℝ) := pserre d
  let s : (Fin d → ℝ) → ℝ := fun x => totalLog d n R x
  let L : ℝ := ((d : ℝ) * (n : ℝ) - (d : ℝ) * (d - 1) / 2) * energy
  let E : ℝ := Real.exp L
  have hIntS : Integrable s ν := by
    dsimp [s, ν]
    exact integrable_totalLog R hR
  have hint : L ≤ ∫ x, s x ∂ν := by
    dsimp [s, L, ν]
    exact integral_totalLog_ge (d := d) (n := n) R hR hRint
  let T : Set (Fin d → ℝ) := {x | GoodTuple d R x ∧ L ≤ s x}
  have hTnot0 : ν T ≠ 0 := by
    intro hT0
    have hA0 : ν {x | L ≤ s x} = 0 := by
      have hsub : {x | L ≤ s x} ⊆ T ∪ {x | ¬ GoodTuple d R x} := by
        intro x hx
        by_cases hg : GoodTuple d R x
        · left
          exact ⟨hg, hx⟩
        · right
          exact hg
      apply le_antisymm
      · calc
          ν {x | L ≤ s x} ≤ ν (T ∪ {x : Fin d → ℝ | ¬ GoodTuple d R x}) := measure_mono hsub
          _ ≤ ν T + ν {x : Fin d → ℝ | ¬ GoodTuple d R x} := measure_union_le _ _
          _ = 0 := by
            rw [hT0]
            simp [measure_good_compl R hR, ν]
      · exact zero_le
    have hslt : ∀ᵐ x ∂ν, s x < L := by
      rw [MeasureTheory.ae_iff]
      have hset : {x | ¬ s x < L} = {x | L ≤ s x} := by
        ext x
        simp [le_of_not_gt]
      rw [hset]
      exact hA0
    have hIntH : Integrable (fun x : Fin d → ℝ => L - s x) ν := by
      exact (integrable_const L).sub hIntS
    have hpos : ∀ᵐ x ∂ν, 0 < L - s x := by
      filter_upwards [hslt] with x hx
      linarith
    have hsumle : (∫ x : Fin d → ℝ, (L - s x) ∂ν) ≤ 0 := by
      calc
        (∫ x : Fin d → ℝ, (L - s x) ∂ν) = L - (∫ x : Fin d → ℝ, s x ∂ν) := by
            rw [MeasureTheory.integral_sub (integrable_const L) hIntS]
            congr 1
            have hc : (∫ x : Fin d → ℝ, L ∂ν) = L := by
              rw [MeasureTheory.integral_const]
              rw [smul_eq_mul]
              rw [MeasureTheory.Measure.real_def]
              have hun : ν Set.univ = 1 := by
                dsimp [ν]
                simp
              rw [hun]
              norm_num
            exact hc
        _ ≤ 0 := by linarith
    have hposint : 0 < ∫ x : Fin d → ℝ, (L - s x) ∂ν := integral_pos_of_ae_pos hIntH hpos
    linarith
  have hTpos : 0 < ν T := lt_of_le_of_ne zero_le (Ne.symm hTnot0)
  have hTnonempty : T.Nonempty := nonempty_of_measure_pos hTpos
  rcases hTnonempty with ⟨x, hxT⟩
  refine ⟨x, hxT.1, ?_⟩
  have hxL : L ≤ s x := hxT.2
  have hFpos : 0 < tupleF d n R x := tupleF_pos_of_good R hxT.1
  have hlog : Real.log (tupleF d n R x) = s x := by
    simpa [s] using (log_tupleF_eq_totalLog R hxT.1)
  have hlelog : L ≤ Real.log (tupleF d n R x) := by rwa [hlog]
  calc
    E = Real.exp L := rfl
    _ ≤ Real.exp (Real.log (tupleF d n R x)) := Real.exp_le_exp.mpr hlelog
    _ = tupleF d n R x := Real.exp_log hFpos
end Submission.SqueezeCore
