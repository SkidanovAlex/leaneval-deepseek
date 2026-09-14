-- ⚠ IMPORT-CLASH WORKAROUND (session 123): verbatim copy of Submission.Commons.Analysis.GaussianMeasure.hermSum_dense_vec
-- with the import chain redirected so that the duplicate constant `toLp_norm_sq` of
-- `…bobkov_strong_nD` is not pulled into the same environment as
-- `…brascamp_lieb_truncated`.  Do not import both this file and the commons original.
import Mathlib
import Submission.Fix.HermiteSumDenseL2
import Submission.Commons.Analysis.GaussianMeasure.integrable_exp_neg_norm_sq_half

open MeasureTheory
open scoped BigOperators ENNReal

namespace Commons.Analysis.GaussianMeasure

set_option maxHeartbeats 2000000

noncomputable section

/-- The Gaussian measure with density `exp (-‖x‖^2 / 2)` on `ℝ^N`. -/
private abbrev gaussN (N : ℕ) : Measure (EuclideanSpace ℝ (Fin N)) :=
  volume.withDensity (fun x : EuclideanSpace ℝ (Fin N) => ENNReal.ofReal (Real.exp (-‖x‖ ^ 2 / 2)))

/-- The tensor product of Hermite polynomials indexed by `α`. -/
private abbrev hermN {N : ℕ} (α : Fin N → ℕ) : EuclideanSpace ℝ (Fin N) → ℝ :=
  fun x => ∏ i, Polynomial.aeval (x.ofLp i) (Polynomial.hermite (α i))

private lemma isFiniteMeasure_gaussN (N : ℕ) : IsFiniteMeasure (gaussN N) := by
  refine isFiniteMeasure_withDensity ?_
  have h := (integrable_exp_neg_norm_sq_half (n := N)).hasFiniteIntegral
  rw [MeasureTheory.HasFiniteIntegral] at h
  have hrew : ∀ a : EuclideanSpace ℝ (Fin N),
      ‖Real.exp (-‖a‖ ^ 2 / 2)‖ₑ = ENNReal.ofReal (Real.exp (-‖a‖ ^ 2 / 2)) := by
    intro a
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (Real.exp_nonneg _)]
  simp only [hrew] at h
  exact ne_of_lt h

theorem hermSum_dense_vec {N n : ℕ} (Φ : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin n)) (hΦ : MeasureTheory.MemLp Φ 2 (MeasureTheory.volume.withDensity (fun x : EuclideanSpace ℝ (Fin N) => ENNReal.ofReal (Real.exp (-‖x‖ ^ 2 / 2))))) (ε : ℝ) (hε : 0 < ε) : ∃ (s : Finset (Fin N → ℕ)) (C : (Fin N → ℕ) → EuclideanSpace ℝ (Fin n)), ∫ x : EuclideanSpace ℝ (Fin N), ‖Φ x - ∑ α ∈ s, (∏ i, Polynomial.aeval (x.ofLp i) (Polynomial.hermite (α i))) • C α‖ ^ 2 ∂(MeasureTheory.volume.withDensity (fun x : EuclideanSpace ℝ (Fin N) => ENNReal.ofReal (Real.exp (-‖x‖ ^ 2 / 2)))) < ε ^ 2 := by
  classical
  haveI : IsFiniteMeasure (gaussN N) := isFiniteMeasure_gaussN N
  -- each component of `Φ` is in `L²`
  have hcomp : ∀ j : Fin n, MemLp (fun x => (Φ x).ofLp j) 2 (gaussN N) := by
    intro j
    let L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin n => ℝ) j
    have h1 : MemLp (fun x => L ((hΦ.toLp Φ) x)) 2 (gaussN N) := L.comp_memLp (hΦ.toLp Φ)
    refine h1.ae_eq ?_
    filter_upwards [hΦ.coeFn_toLp] with x hx
    rw [hx]
    simp [L]
  set δ : ℝ := ε / Real.sqrt (n + 1) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    exact div_pos hε (Real.sqrt_pos.mpr (by positivity))
  -- scalar density for each component
  have hscalar : ∀ j : Fin n, ∃ (sj : Finset (Fin N → ℕ)) (cj : (Fin N → ℕ) → ℝ),
      ∫ x, ((Φ x).ofLp j - ∑ α ∈ sj, cj α * hermN α x) ^ 2 ∂(gaussN N) < δ ^ 2 := by
    intro j
    obtain ⟨sj, cj, hc⟩ := hermite_sum_dense_L2 (fun x => (Φ x).ofLp j) (hcomp j) δ hδpos
    exact ⟨sj, cj, by simpa only [hermN] using hc⟩
  choose sj cj hcj using hscalar
  let s : Finset (Fin N → ℕ) := Finset.univ.biUnion sj
  let C : (Fin N → ℕ) → EuclideanSpace ℝ (Fin n) :=
    fun α => WithLp.toLp 2 (fun j => if α ∈ sj j then cj j α else 0)
  refine ⟨s, C, ?_⟩
  change ∫ x, ‖Φ x - ∑ α ∈ s, hermN α x • C α‖ ^ 2 ∂(gaussN N) < ε ^ 2
  -- the polynomial part is in `L²`
  have memLp_finset_sum_real : ∀ (t : Finset (Fin N → ℕ)) (d : (Fin N → ℕ) → ℝ),
      MemLp (fun x => ∑ α ∈ t, d α * hermN α x) 2 (gaussN N) := by
    intro t
    induction t using Finset.induction with
    | empty =>
        intro d
        simpa using (MemLp.zero (p := 2) (μ := gaussN N) (ε := ℝ))
    | insert a t ha ih =>
        intro d
        have hfun : (fun x : EuclideanSpace ℝ (Fin N) => ∑ α ∈ insert a t, d α * hermN α x)
            = fun x => d a * hermN a x + ∑ α ∈ t, d α * hermN α x := by
          funext x; rw [Finset.sum_insert ha]
        rw [hfun]
        have h1 : MemLp (fun x : EuclideanSpace ℝ (Fin N) => d a * hermN a x) 2 (gaussN N) :=
          (memLp_hermite_product a).const_mul (d a)
        exact h1.add (ih d)
  have hInt : ∀ j : Fin n,
      Integrable (fun x => ((Φ x).ofLp j - ∑ α ∈ sj j, cj j α * hermN α x) ^ 2) (gaussN N) := by
    intro j
    exact ((hcomp j).sub (memLp_finset_sum_real (sj j) (cj j))).integrable_sq
  -- component form of the sum
  have hsum_comp : ∀ (x : EuclideanSpace ℝ (Fin N)) (j : Fin n),
      ((∑ α ∈ s, hermN α x • C α : EuclideanSpace ℝ (Fin n))).ofLp j
        = ∑ α ∈ sj j, cj j α * hermN α x := by
    intro x j
    have h1 : ((∑ α ∈ s, hermN α x • C α : EuclideanSpace ℝ (Fin n))).ofLp j
        = ∑ α ∈ s, hermN α x * (C α).ofLp j := by
      simp [WithLp.ofLp_sum, WithLp.ofLp_smul]
    rw [h1, ← Finset.sum_subset (Finset.subset_biUnion_of_mem sj (Finset.mem_univ j))]
    · refine Finset.sum_congr rfl (fun α hα => ?_)
      have hCα : (C α).ofLp j = cj j α := by
        simp only [C]
        rw [if_pos hα]
      rw [hCα, mul_comm]
    · intro α _ hα
      have hCα : (C α).ofLp j = 0 := by
        simp only [C]
        rw [if_neg hα]
      rw [hCα, mul_zero]
  have hpoint : ∀ x : EuclideanSpace ℝ (Fin N),
      ‖Φ x - ∑ α ∈ s, hermN α x • C α‖ ^ 2
        = ∑ j : Fin n, ((Φ x).ofLp j - ∑ α ∈ sj j, cj j α * hermN α x) ^ 2 := by
    intro x
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Real.norm_eq_abs, sq_abs, WithLp.ofLp_sub, Pi.sub_apply, hsum_comp x j]
  have hint_eq : ∫ x, ‖Φ x - ∑ α ∈ s, hermN α x • C α‖ ^ 2 ∂(gaussN N)
      = ∑ j : Fin n, ∫ x, ((Φ x).ofLp j - ∑ α ∈ sj j, cj j α * hermN α x) ^ 2 ∂(gaussN N) := by
    calc ∫ x, ‖Φ x - ∑ α ∈ s, hermN α x • C α‖ ^ 2 ∂(gaussN N)
        = ∫ x, ∑ j : Fin n, ((Φ x).ofLp j - ∑ α ∈ sj j, cj j α * hermN α x) ^ 2 ∂(gaussN N) :=
          integral_congr_ae (Filter.Eventually.of_forall hpoint)
      _ = ∑ j : Fin n, ∫ x, ((Φ x).ofLp j - ∑ α ∈ sj j, cj j α * hermN α x) ^ 2 ∂(gaussN N) :=
          integral_finsetSum Finset.univ (fun j _ => hInt j)
  have hδsq : δ ^ 2 = ε ^ 2 / ((n : ℝ) + 1) := by
    rw [hδdef, div_pow, Real.sq_sqrt (by positivity)]
  have hbound : (n : ℝ) * δ ^ 2 < ε ^ 2 := by
    rw [hδsq, mul_div_assoc']
    rw [div_lt_iff₀ (by positivity : (0:ℝ) < (n:ℝ) + 1)]
    nlinarith [sq_pos_of_pos hε]
  calc ∫ x, ‖Φ x - ∑ α ∈ s, hermN α x • C α‖ ^ 2 ∂(gaussN N)
      = ∑ j : Fin n, ∫ x, ((Φ x).ofLp j - ∑ α ∈ sj j, cj j α * hermN α x) ^ 2 ∂(gaussN N) := hint_eq
    _ ≤ ∑ j : Fin n, δ ^ 2 := Finset.sum_le_sum (fun j _ => le_of_lt (hcj j))
    _ = (n : ℝ) * δ ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ < ε ^ 2 := hbound

end

end Commons.Analysis.GaussianMeasure
