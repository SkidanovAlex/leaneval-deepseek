import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Order.CompletePartialOrder

namespace Commons.Analysis.GaussianMeasure

open MeasureTheory Real
open scoped Real Topology

/-- The gradient of a scalar function, as a vector. -/
private noncomputable def grad {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (u : E → ℝ) : E → E :=
  fun x => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x)

section Basic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A function which vanishes outside its topological support has zero derivative there. -/
private lemma fderiv_eq_zero_of_not_mem_tsupport {u : E → ℝ} {x : E}
    (hx : x ∉ tsupport u) : fderiv ℝ u x = 0 := by
  have hU : (tsupport u)ᶜ ∈ 𝓝 x := (isClosed_tsupport u).isOpen_compl.mem_nhds hx
  have heq : u =ᶠ[𝓝 x] (fun _ : E => (0 : ℝ)) := by
    filter_upwards [hU] with y hy
    by_contra h
    exact hy (subset_tsupport u (Function.mem_support.mpr h))
  rw [heq.fderiv_eq]
  simp

/-- Outside the topological support, the derivative of a function vanishes identically
in a neighbourhood. -/
private lemma fderiv_eventuallyEq_zero_of_not_mem_tsupport {u : E → ℝ} {x : E}
    (hx : x ∉ tsupport u) : fderiv ℝ u =ᶠ[𝓝 x] (0 : E → E →L[ℝ] ℝ) := by
  have hU : (tsupport u)ᶜ ∈ 𝓝 x := (isClosed_tsupport u).isOpen_compl.mem_nhds hx
  filter_upwards [hU] with y hy
  exact fderiv_eq_zero_of_not_mem_tsupport hy

end Basic

section LaplacianBasic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The Laplacian as a sum of second derivatives along the standard orthonormal basis. -/
private lemma laplacian_eq_sum_fderiv (u : E → ℝ) (x : E) :
    Laplacian.laplacian u x
      = ∑ i, (fderiv ℝ (fderiv ℝ u) x) ((stdOrthonormalBasis ℝ E) i)
          ((stdOrthonormalBasis ℝ E) i) := by
  rw [congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis u) x]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedFDeriv_two_apply]
  simp

/-- The Laplacian of a function vanishing outside its topological support is zero there. -/
private lemma laplacian_eq_zero_of_not_mem_tsupport {u : E → ℝ} {x : E}
    (hx : x ∉ tsupport u) : Laplacian.laplacian u x = 0 := by
  rw [laplacian_eq_sum_fderiv u x]
  have h2 : fderiv ℝ (fderiv ℝ u) x = 0 := by
    rw [(fderiv_eventuallyEq_zero_of_not_mem_tsupport hx).fderiv_eq]
    simp
  simp [h2]

/-- The Laplacian of a `C²` function is continuous. -/
private lemma continuous_laplacian {u : E → ℝ} (hu : ContDiff ℝ 2 u) :
    Continuous (fun x => Laplacian.laplacian u x) := by
  have h2 : Continuous (fun x => fderiv ℝ (fderiv ℝ u) x) :=
    (hu.fderiv_right (m := (1 : WithTop ℕ∞)) (by norm_num)).continuous_fderiv (by norm_num)
  have hfun : (fun x => Laplacian.laplacian u x)
      = fun x => ∑ i, (fderiv ℝ (fderiv ℝ u) x) ((stdOrthonormalBasis ℝ E) i)
          ((stdOrthonormalBasis ℝ E) i) := funext fun x => laplacian_eq_sum_fderiv u x
  rw [hfun]
  refine continuous_finsetSum _ fun i _ => ?_
  exact (h2.clm_apply continuous_const).clm_apply continuous_const

end LaplacianBasic

/-- A compactly supported `C²` function has bounded weighted Laplacian, hence lies in `L²(e^{-f})`
whenever the potential is `C²` with at most polynomial growth and `e^{-f}` gives finite measure. -/
theorem memLp_weightedLaplacian_c2 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (f φ : E → ℝ)
    (hf : ContDiff ℝ 2 f) (hφ : ContDiff ℝ 2 φ) (hcφ : HasCompactSupport φ)
    (hgf : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ x v : E, |fderiv ℝ f x v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖)
    (hμ : IsFiniteMeasure
      (volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-(f x)))))) :
    MemLp (fun x => - Laplacian.laplacian φ x
        + inner ℝ ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x))
            ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ φ x))) 2
      (volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-(f x))))) := by
  haveI := hμ
  have hgradf : Continuous (grad f) :=
    (LinearIsometryEquiv.continuous (InnerProductSpace.toDual ℝ E).symm).comp
      (hf.continuous_fderiv (by norm_num))
  have hgradφ : Continuous (grad φ) :=
    (LinearIsometryEquiv.continuous (InnerProductSpace.toDual ℝ E).symm).comp
      (hφ.continuous_fderiv (by norm_num))
  have hcont : Continuous (fun x => - Laplacian.laplacian φ x + inner ℝ (grad f x) (grad φ x)) :=
    (continuous_laplacian hφ).neg.add (hgradf.inner hgradφ)
  have hzero : ∀ x : E, x ∉ tsupport φ →
      - Laplacian.laplacian φ x + inner ℝ (grad f x) (grad φ x) = 0 := by
    intro x hx
    have h1 : Laplacian.laplacian φ x = 0 := laplacian_eq_zero_of_not_mem_tsupport hx
    have h2 : fderiv ℝ φ x = 0 := fderiv_eq_zero_of_not_mem_tsupport hx
    simp only [grad, h1, h2, map_zero, inner_zero_right, neg_zero, zero_add]
  have hcs : HasCompactSupport
      (fun x => - Laplacian.laplacian φ x + inner ℝ (grad f x) (grad φ x)) :=
    hcφ.mono' (by
      intro x hx
      by_contra hxt
      exact hx (hzero x hxt))
  obtain ⟨M, hM⟩ := hcont.bounded_above_of_compact_support hcs
  exact MemLp.of_bound hcont.aestronglyMeasurable M (ae_of_all _ hM)

end Commons.Analysis.GaussianMeasure