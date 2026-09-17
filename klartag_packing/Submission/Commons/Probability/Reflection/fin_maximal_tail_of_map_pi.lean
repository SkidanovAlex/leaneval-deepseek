import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib
import Submission.Commons.Probability.Gaussian.hasSubgaussianMGF_inner_stdGaussian
import Submission.Commons.Probability.Hoeffding.chernoff_weighted
import Submission.Commons.Probability.Reflection.pi_fin_maximal_abs_tail

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-!
# Maximal tail bound for the partial sums of `ε ⟪X i, w⟫`

Let `X : Fin n → Ω → E` be random vectors whose joint law is the product of `n` copies of the
standard Gaussian measure on a finite-dimensional real inner product space `E`.  For a fixed
vector `w` with `‖w‖ ≤ 1` we consider the partial sums of the real random variables
`ε * ⟪X i ω, w⟫`.  Since each `⟪X i, w⟫` is a centred Gaussian with variance `‖w‖²`, the
maximal inequality for symmetric sub-Gaussian sequences gives

`μ.real {ω | ∃ k ≤ n, r ≤ |∑_{i < k} ε ⟪X i ω, w⟫|} ≤ 4 * exp (-r² / (2 n ε²))`.

The main work consists in transporting the statement from `Ω` to the finite product space
`Fin n → ℝ` (where the maximal inequality `pi_fin_maximal_abs_tail` is available), using that
the law of `ω ↦ (ε * ⟪X j ω, w⟫)_j` is the product of the law `ν` of `ε * ⟪x, w⟫`.
-/

namespace Commons.Probability.Reflection

open MeasureTheory ProbabilityTheory

theorem fin_maximal_tail_of_map_pi {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ] {n : ℕ}
    (X : Fin n → Ω → E) (hX : ∀ i, Measurable (X i))
    (hlaw : μ.map (fun ω => fun j : Fin n => X j ω)
      = MeasureTheory.Measure.pi (fun _ : Fin n => ProbabilityTheory.stdGaussian E))
    (w : E) (hw : ‖w‖ ≤ 1) {ε r : ℝ} (hε : 0 ≤ ε) (hr : 0 ≤ r) :
    μ.real {ω | ∃ k ≤ n, r ≤ |∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k),
        ε * inner ℝ (X i ω) w|}
      ≤ 4 * Real.exp (-r ^ 2 / (2 * (n : ℝ) * ε ^ 2)) := by
  classical
  -- the sub-Gaussian parameter `c = ε²`
  let c : NNReal := ⟨ε ^ 2, sq_nonneg ε⟩
  have hce : (c : ℝ) = ε ^ 2 := rfl
  -- the one-dimensional linear functional
  set f : E → ℝ := fun x => ε * inner ℝ x w with hf_def
  have hf : Measurable f := by rw [hf_def]; fun_prop
  -- the joint law map `ω ↦ (X j ω)_j`
  set φ : Ω → (Fin n → E) := fun ω j => X j ω with hφ_def
  have hφ : Measurable φ := measurable_pi_iff.mpr hX
  -- the coordinatewise application of `f`
  set Φ : (Fin n → E) → (Fin n → ℝ) := fun x j => f (x j) with hΦ_def
  have hΦ : Measurable Φ := measurable_pi_iff.mpr (fun j => hf.comp (measurable_pi_apply j))
  -- the real random vector whose partial sums we bound
  set Ψ : Ω → (Fin n → ℝ) := fun ω j => f (X j ω) with hΨ_def
  have hΨ : Measurable Ψ := hΦ.comp hφ
  -- its one-dimensional marginal
  set ν : Measure ℝ := (stdGaussian E).map f with hν_def
  haveI : IsProbabilityMeasure ν := inferInstance
  -- the event on the product space
  set A : Set (Fin n → ℝ) :=
    {y | ∃ k ≤ n, r ≤ |∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), y i|}
    with hA_def
  -- the law of the real random vector is a product of copies of `ν`
  have hmapΨ : μ.map Ψ = Measure.pi (fun _ : Fin n => ν) := by
    have h1 : Ψ = Φ ∘ φ := rfl
    rw [h1, ← Measure.map_map hΦ hφ, hlaw]
    have h2 := Measure.pi_map_pi (μ := fun _ : Fin n => stdGaussian E) (f := fun _ : Fin n => f)
      (fun _ => hf.aemeasurable)
    simpa [hν_def] using h2
  -- the event is measurable
  have hA : MeasurableSet A := by
    rw [hA_def]
    have heq : {y : Fin n → ℝ | ∃ k ≤ n,
          r ≤ |∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), y i|}
        = ⋃ k ∈ Finset.range (n + 1), {y : Fin n → ℝ |
            r ≤ |∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), y i|} := by
      ext y
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_range]
      constructor
      · rintro ⟨k, hk, h⟩; exact ⟨k, Nat.lt_succ_of_le hk, h⟩
      · rintro ⟨k, hk, h⟩; exact ⟨k, Nat.le_of_lt_succ hk, h⟩
    rw [heq]
    exact Finset.measurableSet_biUnion _ (fun k _ =>
      measurableSet_le measurable_const
        (Measurable.abs (Finset.measurable_sum _ (fun i _ => measurable_pi_apply i))))
  -- the standard Gaussian measure is invariant under `x ↦ -x`
  have hstd : (stdGaussian E).map (fun x : E => -x) = stdGaussian E := by
    simpa using ProbabilityTheory.stdGaussian_map (E := E) (F := E) (LinearIsometryEquiv.neg ℝ)
  -- `f` is odd
  have hodd : (fun x : E => -(f x)) = fun x : E => f (-x) := by
    funext x; rw [hf_def]; simp
  -- hence `ν` is symmetric
  have hνsym : ν.map (fun x : ℝ => -x) = ν := by
    have hcomp : (fun x : ℝ => -x) ∘ f = fun x : E => f (-x) := by
      funext x; exact congrFun hodd x
    calc ν.map (fun x : ℝ => -x)
        = ((stdGaussian E).map f).map (fun x : ℝ => -x) := by rw [hν_def]
      _ = (stdGaussian E).map ((fun x : ℝ => -x) ∘ f) := Measure.map_map measurable_neg hf
      _ = (stdGaussian E).map (fun x : E => f (-x)) := by rw [hcomp]
      _ = (stdGaussian E).map (f ∘ (fun x : E => -x)) := rfl
      _ = ((stdGaussian E).map (fun x : E => -x)).map f :=
            (Measure.map_map hf measurable_neg).symm
      _ = (stdGaussian E).map f := by rw [hstd]
      _ = ν := by rw [hν_def]
  -- `⟪·, w⟫` is sub-Gaussian with parameter `‖w‖²`, hence `f` with parameter `ε² ‖w‖²`
  have hbase := Commons.Probability.Gaussian.hasSubgaussianMGF_inner_stdGaussian (E := E) w
  have hscaled : HasSubgaussianMGF (fun x : E => ε * inner ℝ x w) (c * ‖w‖₊ ^ 2)
      (stdGaussian E) := hbase.const_mul ε
  have hνG : HasSubgaussianMGF (fun x : ℝ => x) (c * ‖w‖₊ ^ 2) ν := by
    rw [hν_def]
    exact (HasSubgaussianMGF.id_map_iff hf.aemeasurable).2 hscaled
  -- `ε² ‖w‖² ≤ ε²` because `‖w‖ ≤ 1`; enlarge the parameter to `c = ε²`
  have hle : c * ‖w‖₊ ^ 2 ≤ c := by
    have hw1 : ‖w‖₊ ≤ 1 := by rw [← NNReal.coe_le_coe]; simpa using hw
    calc c * ‖w‖₊ ^ 2 ≤ c * 1 := by
          gcongr
          exact pow_le_one₀ (by positivity : (0 : NNReal) ≤ ‖w‖₊) hw1
      _ = c := mul_one c
  have hG : HasSubgaussianMGF (fun x : ℝ => x) c ν :=
    Commons.Probability.Hoeffding.hasSubgaussianMGF_mono hνG hle
  -- the event on `Ω` is the preimage of `A` under `Ψ`
  have hbridge : {ω | ∃ k ≤ n, r ≤ |∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k),
        ε * inner ℝ (X i ω) w|} = Ψ ⁻¹' A := by
    rw [hΨ_def, hA_def]
    rfl
  calc μ.real {ω | ∃ k ≤ n, r ≤ |∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k),
        ε * inner ℝ (X i ω) w|}
      = (μ.map Ψ).real A := by
        rw [hbridge, MeasureTheory.map_measureReal_apply hΨ hA]
    _ = (Measure.pi (fun _ : Fin n => ν)).real A := by rw [hmapΨ]
    _ ≤ 4 * Real.exp (-r ^ 2 / (2 * (n : ℝ) * (c : ℝ))) :=
        pi_fin_maximal_abs_tail hνsym hG hr n
    _ = 4 * Real.exp (-r ^ 2 / (2 * (n : ℝ) * ε ^ 2)) := by rw [hce]

end Commons.Probability.Reflection
