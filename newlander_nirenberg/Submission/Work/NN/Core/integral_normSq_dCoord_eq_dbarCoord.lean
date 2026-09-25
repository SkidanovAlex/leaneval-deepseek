/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The `L²` equality `‖∂φ‖ = ‖∂̄φ‖` for compactly supported `C¹` functions

For a `C¹` function `φ : ℂⁿ → ℂ` with compact support, the sum over the coordinate directions of the
squared norms of the `(1,0)`-derivatives equals the corresponding sum for the `(0,1)`-derivatives.
This is the flat case of the classical fact that the Dirichlet energy of a compactly supported
function splits evenly between its holomorphic and antiholomorphic parts.

The proof is by approximation: the identity is first proved for smooth compactly supported `φ`
(where the pointwise identity between the difference of the energies and the Jacobian determinant,
together with the divergence theorem for `C¹` compactly supported fields, gives the result), and
then extended to `C¹` functions by mollification, using that both `ψ` and `Dψ` are uniformly
approximated by the mollifications and dominated convergence for the integrals.

Main results:

* `Work.NN.Core.integral_normSq_dCoord_eq_dbarCoord`
-/
import Mathlib
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.NN.Core.integral_normSq_dCoord_eq_dbarCoord_of_contDiff
import Submission.Work.NN.Core.exists_contDiff_uniform_approx

open scoped ContDiff Topology
open MeasureTheory Filter

namespace Work.NN.Core

/-! ## elementary estimates for the coordinate derivatives -/

lemma norm_half_mul_sub_I_le (A B : ℂ) :
    ‖(1 / 2 : ℂ) * (A - Complex.I * B)‖ ≤ (1 / 2) * (‖A‖ + ‖B‖) := by
  have h1 : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
  rw [norm_mul, h1]
  have h2 : ‖A - Complex.I * B‖ ≤ ‖A‖ + ‖B‖ := by
    refine (norm_sub_le _ _).trans (le_of_eq ?_)
    rw [norm_mul, Complex.norm_I, one_mul]
  linarith [norm_nonneg A, norm_nonneg B]

lemma norm_half_mul_add_I_le (A B : ℂ) :
    ‖(1 / 2 : ℂ) * (A + Complex.I * B)‖ ≤ (1 / 2) * (‖A‖ + ‖B‖) := by
  have h1 : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
  rw [norm_mul, h1]
  have h2 : ‖A + Complex.I * B‖ ≤ ‖A‖ + ‖B‖ := by
    refine (norm_add_le _ _).trans (le_of_eq ?_)
    rw [norm_mul, Complex.norm_I, one_mul]
  linarith [norm_nonneg A, norm_nonneg B]

/-- Bound of the `(1,0)`-coefficient of a real-linear map by its operator norm. -/
lemma norm_dCoordCLM_le {n : ℕ} (j : Fin n) (L : (Fin n → ℂ) →L[ℝ] ℂ) :
    ‖(1 / 2 : ℂ) * (L (Pi.single j 1) - Complex.I * L (Pi.single j Complex.I))‖ ≤ ‖L‖ := by
  refine (norm_half_mul_sub_I_le _ _).trans ?_
  have h1 : ‖L (Pi.single j (1 : ℂ))‖ ≤ ‖L‖ := by
    have h := ContinuousLinearMap.le_opNorm L (Pi.single j (1 : ℂ))
    rwa [Pi.norm_single, norm_one, mul_one] at h
  have h2 : ‖L (Pi.single j (Complex.I : ℂ))‖ ≤ ‖L‖ := by
    have h := ContinuousLinearMap.le_opNorm L (Pi.single j (Complex.I : ℂ))
    rwa [Pi.norm_single, Complex.norm_I, mul_one] at h
  linarith

lemma norm_dbarCoordCLM_le {n : ℕ} (j : Fin n) (L : (Fin n → ℂ) →L[ℝ] ℂ) :
    ‖(1 / 2 : ℂ) * (L (Pi.single j 1) + Complex.I * L (Pi.single j Complex.I))‖ ≤ ‖L‖ := by
  refine (norm_half_mul_add_I_le _ _).trans ?_
  have h1 : ‖L (Pi.single j (1 : ℂ))‖ ≤ ‖L‖ := by
    have h := ContinuousLinearMap.le_opNorm L (Pi.single j (1 : ℂ))
    rwa [Pi.norm_single, norm_one, mul_one] at h
  have h2 : ‖L (Pi.single j (Complex.I : ℂ))‖ ≤ ‖L‖ := by
    have h := ContinuousLinearMap.le_opNorm L (Pi.single j (Complex.I : ℂ))
    rwa [Pi.norm_single, Complex.norm_I, mul_one] at h
  linarith

lemma dCoord_eq_CLM {n : ℕ} (j : Fin n) (f : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) :
    Work.CR.Flat.dCoord j f z
      = (1 / 2 : ℂ) * (fderiv ℝ f z (Pi.single j 1)
          - Complex.I * fderiv ℝ f z (Pi.single j Complex.I)) := rfl

lemma dbarCoord_eq_CLM {n : ℕ} (j : Fin n) (f : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) :
    Work.CR.Flat.dbarCoord j f z
      = (1 / 2 : ℂ) * (fderiv ℝ f z (Pi.single j 1)
          + Complex.I * fderiv ℝ f z (Pi.single j Complex.I)) := rfl

lemma norm_dCoord_le {n : ℕ} (j : Fin n) (f : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) :
    ‖Work.CR.Flat.dCoord j f z‖ ≤ ‖fderiv ℝ f z‖ :=
  norm_dCoordCLM_le j (fderiv ℝ f z)

lemma norm_dbarCoord_le {n : ℕ} (j : Fin n) (f : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) :
    ‖Work.CR.Flat.dbarCoord j f z‖ ≤ ‖fderiv ℝ f z‖ :=
  norm_dbarCoordCLM_le j (fderiv ℝ f z)

lemma dCoord_sub_dCoord {n : ℕ} (j : Fin n) (f g : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) :
    Work.CR.Flat.dCoord j f z - Work.CR.Flat.dCoord j g z
      = (1 / 2 : ℂ) * ((fderiv ℝ f z - fderiv ℝ g z) (Pi.single j 1)
          - Complex.I * ((fderiv ℝ f z - fderiv ℝ g z) (Pi.single j Complex.I))) := by
  simp only [Work.CR.Flat.dCoord, sub_apply]
  ring

lemma dbarCoord_sub_dbarCoord {n : ℕ} (j : Fin n) (f g : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) :
    Work.CR.Flat.dbarCoord j f z - Work.CR.Flat.dbarCoord j g z
      = (1 / 2 : ℂ) * ((fderiv ℝ f z - fderiv ℝ g z) (Pi.single j 1)
          + Complex.I * ((fderiv ℝ f z - fderiv ℝ g z) (Pi.single j Complex.I))) := by
  simp only [Work.CR.Flat.dbarCoord, sub_apply]
  ring

lemma norm_dCoord_sub_le {n : ℕ} (j : Fin n) (f g : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) :
    ‖Work.CR.Flat.dCoord j f z - Work.CR.Flat.dCoord j g z‖
      ≤ ‖fderiv ℝ f z - fderiv ℝ g z‖ := by
  rw [dCoord_sub_dCoord]
  exact norm_dCoordCLM_le j (fderiv ℝ f z - fderiv ℝ g z)

lemma norm_dbarCoord_sub_le {n : ℕ} (j : Fin n) (f g : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) :
    ‖Work.CR.Flat.dbarCoord j f z - Work.CR.Flat.dbarCoord j g z‖
      ≤ ‖fderiv ℝ f z - fderiv ℝ g z‖ := by
  rw [dbarCoord_sub_dbarCoord]
  exact norm_dbarCoordCLM_le j (fderiv ℝ f z - fderiv ℝ g z)


/-! ## the main glue -/

lemma tendsto_inv_succ_nat : Tendsto (fun k : ℕ => ((k:ℝ)+1)⁻¹) atTop (𝓝 0) := by
  simpa [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

lemma continuous_dCoord {n : ℕ} (j : Fin n) {f : (Fin n → ℂ) → ℂ} (hf : ContDiff ℝ 1 f) :
    Continuous (fun z => Work.CR.Flat.dCoord j f z) := by
  have hd : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
  simp only [Work.CR.Flat.dCoord]
  exact Continuous.const_mul
    ((hd.clm_apply continuous_const).sub (continuous_const.mul (hd.clm_apply continuous_const))) _

lemma continuous_dbarCoord {n : ℕ} (j : Fin n) {f : (Fin n → ℂ) → ℂ} (hf : ContDiff ℝ 1 f) :
    Continuous (fun z => Work.CR.Flat.dbarCoord j f z) := by
  have hd : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
  simp only [Work.CR.Flat.dbarCoord]
  exact Continuous.const_mul
    ((hd.clm_apply continuous_const).add (continuous_const.mul (hd.clm_apply continuous_const))) _

theorem integral_normSq_dCoord_eq_dbarCoord {n : ℕ} {φ : (Fin n → ℂ) → ℂ}
    (hφ : ContDiff ℝ 1 φ) (hcs : HasCompactSupport φ) :
    ∫ z : Fin n → ℂ, (∑ j : Fin n, ‖Work.CR.Flat.dCoord j φ z‖ ^ 2)
      = ∫ z : Fin n → ℂ, (∑ j : Fin n, ‖Work.CR.Flat.dbarCoord j φ z‖ ^ 2) := by
  classical
  obtain ⟨R, hRpos, hφ0⟩ := hcs.exists_pos_le_norm
  have hR : (0:ℝ) ≤ R := hRpos.le
  -- the approximating smooth compactly supported sequence
  have hseq : ∀ k : ℕ, ∃ ψ : (Fin n → ℂ) → ℂ,
      ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) ψ ∧ HasCompactSupport ψ ∧
      (∀ z, R + 1 ≤ ‖z‖ → ψ z = 0) ∧
      (∀ z, ‖ψ z - φ z‖ ≤ ((k:ℝ)+1)⁻¹) ∧
      (∀ z, ‖fderiv ℝ ψ z - fderiv ℝ φ z‖ ≤ ((k:ℝ)+1)⁻¹) := by
    intro k
    have hpos : (0:ℝ) < ((k:ℝ)+1)⁻¹ := by positivity
    exact exists_contDiff_uniform_approx hφ hR hφ0 hpos
  choose ψ hψsm hψcs hψsupp hψval hψder using hseq
  -- the identity holds for each approximant
  have hA : ∀ k : ℕ,
      ∫ z, (∑ j : Fin n, ‖Work.CR.Flat.dCoord j (ψ k) z‖ ^ 2)
        = ∫ z, (∑ j : Fin n, ‖Work.CR.Flat.dbarCoord j (ψ k) z‖ ^ 2) := by
    intro k
    exact integral_normSq_dCoord_eq_dbarCoord_of_contDiff ((hψsm k).of_le (by norm_num)) (hψcs k)
  -- a bound for `fderiv φ`
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ z, ‖fderiv ℝ φ z‖ ≤ C :=
    Continuous.bounded_above_of_compact_support
      (hφ.continuous_fderiv (by norm_num)) (hcs.fderiv ℝ)
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
  -- a universal dominating function
  set bound : (Fin n → ℂ) → ℝ :=
    fun z => (n : ℝ) * (C + 1) ^ 2 *
      (Metric.closedBall (0 : Fin n → ℂ) (R + 1)).indicator (fun _ => (1:ℝ)) z with hbounddef
  have hbound_int : Integrable bound volume := by
    have hmeas : MeasurableSet (Metric.closedBall (0 : Fin n → ℂ) (R + 1)) :=
      measurableSet_closedBall
    have hfin : volume (Metric.closedBall (0 : Fin n → ℂ) (R + 1)) ≠ ⊤ :=
      (isCompact_closedBall (0 : Fin n → ℂ) (R + 1)).measure_lt_top.ne
    have h1 : Integrable
        (fun z : Fin n → ℂ =>
          (Metric.closedBall (0 : Fin n → ℂ) (R + 1)).indicator (fun _ => (1:ℝ)) z) volume :=
      (integrable_indicator_iff hmeas).mpr (integrableOn_const hfin (by simp))
    exact h1.const_mul _
  -- the support of each approximant stays in the fixed ball
  have htsupp : ∀ k, tsupport (ψ k) ⊆ Metric.closedBall (0 : Fin n → ℂ) (R + 1) := by
    intro k
    refine closure_minimal ?_ Metric.isClosed_closedBall
    intro z hz
    rw [Function.mem_support] at hz
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra hcon
    exact hz (hψsupp k z (le_of_lt (not_le.mp hcon)))
  -- pointwise domination
  have hbound_pt : ∀ k : ℕ, ∀ᵐ z ∂volume,
      ‖(∑ j : Fin n, ‖Work.CR.Flat.dCoord j (ψ k) z‖ ^ 2)‖ ≤ bound z := by
    intro k
    refine Filter.Eventually.of_forall (fun z => ?_)
    by_cases hz : z ∈ Metric.closedBall (0 : Fin n → ℂ) (R + 1)
    · have hz1 : bound z = (n:ℝ) * (C + 1) ^ 2 := by
        simp only [hbounddef]
        rw [Set.indicator_of_mem hz]
        ring
      rw [hz1]
      have hnn : (0:ℝ) ≤ ∑ j : Fin n, ‖Work.CR.Flat.dCoord j (ψ k) z‖ ^ 2 :=
        Finset.sum_nonneg (fun j _ => pow_nonneg (norm_nonneg _) 2)
      rw [Real.norm_of_nonneg hnn]
      have hterm : ∀ j : Fin n, ‖Work.CR.Flat.dCoord j (ψ k) z‖ ^ 2 ≤ (C + 1) ^ 2 := by
        intro j
        have h1 : ‖Work.CR.Flat.dCoord j (ψ k) z‖ ≤ ‖fderiv ℝ (ψ k) z‖ := norm_dCoord_le j _ _
        have h2 : ‖fderiv ℝ (ψ k) z‖
            ≤ ‖fderiv ℝ φ z‖ + ‖fderiv ℝ (ψ k) z - fderiv ℝ φ z‖ := by
          have h := norm_add_le (fderiv ℝ φ z) (fderiv ℝ (ψ k) z - fderiv ℝ φ z)
          rwa [add_sub_cancel] at h
        have h3 : ‖fderiv ℝ (ψ k) z - fderiv ℝ φ z‖ ≤ ((k:ℝ)+1)⁻¹ := hψder k z
        have h4 : ((k:ℝ)+1)⁻¹ ≤ 1 :=
          inv_le_one_of_one_le₀ (by
            have hk : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
            linarith)
        have h5 : ‖Work.CR.Flat.dCoord j (ψ k) z‖ ≤ C + 1 := by
          linarith [hC z]
        exact pow_le_pow_left₀ (norm_nonneg _) h5 2
      calc ∑ j : Fin n, ‖Work.CR.Flat.dCoord j (ψ k) z‖ ^ 2
          ≤ ∑ _j : Fin n, (C + 1) ^ 2 := Finset.sum_le_sum (fun j _ => hterm j)
        _ = (n:ℝ) * (C + 1) ^ 2 := by
            simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    · have hz1 : bound z = 0 := by
        simp only [hbounddef]
        rw [Set.indicator_of_notMem hz]
        ring
      rw [hz1, norm_le_zero_iff]
      have hz' : R + 1 < ‖z‖ := by
        rw [Metric.mem_closedBall, not_le] at hz
        rwa [dist_zero_right] at hz
      have hfderiv0 : fderiv ℝ (ψ k) z = 0 :=
        fderiv_of_notMem_tsupport ℝ (fun hmem => by
          have h := htsupp k hmem
          rw [Metric.mem_closedBall, dist_zero_right] at h
          linarith)
      refine Finset.sum_eq_zero (fun j _ => ?_)
      have h0 : Work.CR.Flat.dCoord j (ψ k) z = 0 := by
        simp [Work.CR.Flat.dCoord, hfderiv0]
      rw [h0]
      simp
  -- pointwise convergence
  have hconv : ∀ z : Fin n → ℂ,
      Tendsto (fun k : ℕ => ∑ j : Fin n, ‖Work.CR.Flat.dCoord j (ψ k) z‖ ^ 2) atTop
        (𝓝 (∑ j : Fin n, ‖Work.CR.Flat.dCoord j φ z‖ ^ 2)) := by
    intro z
    refine tendsto_finsetSum Finset.univ (fun j _ => ?_)
    have h1 : Tendsto (fun k : ℕ => Work.CR.Flat.dCoord j (ψ k) z) atTop
        (𝓝 (Work.CR.Flat.dCoord j φ z)) := by
      refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
      refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) tendsto_inv_succ_nat
      exact (norm_dCoord_sub_le j (ψ k) φ z).trans (hψder k z)
    exact h1.norm.pow 2
  have hconv' : ∀ z : Fin n → ℂ,
      Tendsto (fun k : ℕ => ∑ j : Fin n, ‖Work.CR.Flat.dbarCoord j (ψ k) z‖ ^ 2) atTop
        (𝓝 (∑ j : Fin n, ‖Work.CR.Flat.dbarCoord j φ z‖ ^ 2)) := by
    intro z
    refine tendsto_finsetSum Finset.univ (fun j _ => ?_)
    have h1 : Tendsto (fun k : ℕ => Work.CR.Flat.dbarCoord j (ψ k) z) atTop
        (𝓝 (Work.CR.Flat.dbarCoord j φ z)) := by
      refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
      refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) tendsto_inv_succ_nat
      exact (norm_dbarCoord_sub_le j (ψ k) φ z).trans (hψder k z)
    exact h1.norm.pow 2
  have hbound_pt' : ∀ k : ℕ, ∀ᵐ z ∂volume,
      ‖(∑ j : Fin n, ‖Work.CR.Flat.dbarCoord j (ψ k) z‖ ^ 2)‖ ≤ bound z := by
    intro k
    refine Filter.Eventually.of_forall (fun z => ?_)
    by_cases hz : z ∈ Metric.closedBall (0 : Fin n → ℂ) (R + 1)
    · have hz1 : bound z = (n:ℝ) * (C + 1) ^ 2 := by
        simp only [hbounddef]
        rw [Set.indicator_of_mem hz]
        ring
      rw [hz1]
      have hnn : (0:ℝ) ≤ ∑ j : Fin n, ‖Work.CR.Flat.dbarCoord j (ψ k) z‖ ^ 2 :=
        Finset.sum_nonneg (fun j _ => pow_nonneg (norm_nonneg _) 2)
      rw [Real.norm_of_nonneg hnn]
      have hterm : ∀ j : Fin n, ‖Work.CR.Flat.dbarCoord j (ψ k) z‖ ^ 2 ≤ (C + 1) ^ 2 := by
        intro j
        have h1 : ‖Work.CR.Flat.dbarCoord j (ψ k) z‖ ≤ ‖fderiv ℝ (ψ k) z‖ := norm_dbarCoord_le j _ _
        have h2 : ‖fderiv ℝ (ψ k) z‖
            ≤ ‖fderiv ℝ φ z‖ + ‖fderiv ℝ (ψ k) z - fderiv ℝ φ z‖ := by
          have h := norm_add_le (fderiv ℝ φ z) (fderiv ℝ (ψ k) z - fderiv ℝ φ z)
          rwa [add_sub_cancel] at h
        have h3 : ‖fderiv ℝ (ψ k) z - fderiv ℝ φ z‖ ≤ ((k:ℝ)+1)⁻¹ := hψder k z
        have h4 : ((k:ℝ)+1)⁻¹ ≤ 1 :=
          inv_le_one_of_one_le₀ (by
            have hk : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
            linarith)
        have h5 : ‖Work.CR.Flat.dbarCoord j (ψ k) z‖ ≤ C + 1 := by
          linarith [hC z]
        exact pow_le_pow_left₀ (norm_nonneg _) h5 2
      calc ∑ j : Fin n, ‖Work.CR.Flat.dbarCoord j (ψ k) z‖ ^ 2
          ≤ ∑ _j : Fin n, (C + 1) ^ 2 := Finset.sum_le_sum (fun j _ => hterm j)
        _ = (n:ℝ) * (C + 1) ^ 2 := by
            simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    · have hz1 : bound z = 0 := by
        simp only [hbounddef]
        rw [Set.indicator_of_notMem hz]
        ring
      rw [hz1, norm_le_zero_iff]
      have hz' : R + 1 < ‖z‖ := by
        rw [Metric.mem_closedBall, not_le] at hz
        rwa [dist_zero_right] at hz
      have hfderiv0 : fderiv ℝ (ψ k) z = 0 :=
        fderiv_of_notMem_tsupport ℝ (fun hmem => by
          have h := htsupp k hmem
          rw [Metric.mem_closedBall, dist_zero_right] at h
          linarith)
      refine Finset.sum_eq_zero (fun j _ => ?_)
      have h0 : Work.CR.Flat.dbarCoord j (ψ k) z = 0 := by
        simp [Work.CR.Flat.dbarCoord, hfderiv0]
      rw [h0]
      simp
  -- passage to the limit
  have hlim1 : Tendsto (fun k : ℕ =>
      ∫ z, (∑ j : Fin n, ‖Work.CR.Flat.dCoord j (ψ k) z‖ ^ 2)) atTop
      (𝓝 (∫ z, (∑ j : Fin n, ‖Work.CR.Flat.dCoord j φ z‖ ^ 2))) := by
    refine tendsto_integral_of_dominated_convergence bound (fun k => ?_) hbound_int
      (fun k => hbound_pt k) (Filter.Eventually.of_forall hconv)
    exact Continuous.aestronglyMeasurable (continuous_finsetSum Finset.univ
      (fun j _ => ((continuous_dCoord j ((hψsm k).of_le (by norm_num))).norm.pow 2)))
  have hlim2 : Tendsto (fun k : ℕ =>
      ∫ z, (∑ j : Fin n, ‖Work.CR.Flat.dbarCoord j (ψ k) z‖ ^ 2)) atTop
      (𝓝 (∫ z, (∑ j : Fin n, ‖Work.CR.Flat.dbarCoord j φ z‖ ^ 2))) := by
    refine tendsto_integral_of_dominated_convergence bound (fun k => ?_) hbound_int
      (fun k => hbound_pt' k) (Filter.Eventually.of_forall hconv')
    exact Continuous.aestronglyMeasurable (continuous_finsetSum Finset.univ
      (fun j _ => ((continuous_dbarCoord j ((hψsm k).of_le (by norm_num))).norm.pow 2)))
  exact tendsto_nhds_unique hlim1
    (hlim2.congr' (Filter.Eventually.of_forall (fun k => (hA k).symm)))

end Work.NN.Core
