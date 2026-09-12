import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace Commons.Analysis.MeasureTheory

theorem orthonormal_projection_decomp
    {α : Type*} {mα : MeasurableSpace α} {μ : MeasureTheory.Measure α}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (y : ι → α → ℝ) (a g : α → ℝ) (β : ι → ℝ)
    (hYint : ∀ i j, MeasureTheory.Integrable (fun x => y i x * y j x) μ)
    (horth : ∀ i j, (∫ x, y i x * y j x ∂μ) = if i = j then 1 else 0)
    (haint : ∀ j, MeasureTheory.Integrable (fun x => a x * y j x) μ)
    (ha2 : MeasureTheory.Integrable (fun x => (a x)^2) μ)
    (hg : ∀ x, g x = ∑ i : ι, β i * y i x) :
    (∫ x, (a x - g x)^2 ∂μ)
      = (∫ x, (a x - ∑ j : ι, (∫ yv, a yv * y j yv ∂μ) * y j x)^2 ∂μ)
        + (∫ x, (g x - ∑ j : ι, (∫ yv, a yv * y j yv ∂μ) * y j x)^2 ∂μ) := by
  classical
  let c : ι → ℝ := fun j => ∫ yv, a yv * y j yv ∂μ
  let p : α → ℝ := fun x => ∑ j : ι, c j * y j x
  change (∫ x, (a x - g x) ^ 2 ∂μ)
      = (∫ x, (a x - p x) ^ 2 ∂μ) + (∫ x, (g x - p x) ^ 2 ∂μ)
  have hpk_eq : ∀ k : ι, (fun x => p x * y k x) = fun x => ∑ i : ι, c i * (y i x * y k x) := by
    intro k
    funext x
    change (∑ j : ι, c j * y j x) * y k x = ∑ i : ι, c i * (y i x * y k x)
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hpk_int : ∀ k : ι, MeasureTheory.Integrable (fun x => p x * y k x) μ := by
    intro k
    rw [hpk_eq k]
    exact MeasureTheory.integrable_finsetSum Finset.univ
      (fun i _ => (hYint i k).const_mul (c i))
  have hpk_val : ∀ k : ι, (∫ x, p x * y k x ∂μ) = c k := by
    intro k
    rw [hpk_eq k]
    rw [MeasureTheory.integral_finsetSum Finset.univ
      (fun i _ => (hYint i k).const_mul (c i))]
    simp only [MeasureTheory.integral_const_mul]
    simp only [horth]
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq']
    simp
  have hcross_j : ∀ l : ι, (∫ x, (a x - p x) * y l x ∂μ) = 0 := by
    intro l
    have h : (fun x => (a x - p x) * y l x) = fun x => a x * y l x - p x * y l x := by
      funext x; ring
    rw [h, MeasureTheory.integral_sub (haint l) (hpk_int l), hpk_val l]
    have hcl : c l = ∫ x, a x * y l x ∂μ := rfl
    rw [hcl, sub_self]
  have hpg_pt : ∀ x, p x - g x = ∑ i : ι, (c i - β i) * y i x := by
    intro x
    rw [hg x]
    change (∑ i : ι, c i * y i x) - (∑ i : ι, β i * y i x) = ∑ i : ι, (c i - β i) * y i x
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hmain_eq : (fun x => (a x - p x) * (p x - g x))
      = fun x => ∑ i : ι, (c i - β i) * ((a x - p x) * y i x) := by
    funext x
    rw [hpg_pt x, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hap_eq : (fun x => a x * p x) = fun x => ∑ i : ι, c i * (a x * y i x) := by
    funext x
    change a x * (∑ i : ι, c i * y i x) = ∑ i : ι, c i * (a x * y i x)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hap_int : MeasureTheory.Integrable (fun x => a x * p x) μ := by
    rw [hap_eq]
    exact MeasureTheory.integrable_finsetSum Finset.univ
      (fun i _ => (haint i).const_mul (c i))
  have hpp_eq : (fun x => p x * p x)
      = fun x => ∑ i : ι, ∑ j : ι, (c i * c j) * (y i x * y j x) := by
    funext x
    change (∑ i : ι, c i * y i x) * (∑ j : ι, c j * y j x)
        = ∑ i : ι, ∑ j : ι, (c i * c j) * (y i x * y j x)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hpp_int : MeasureTheory.Integrable (fun x => p x * p x) μ := by
    rw [hpp_eq]
    apply MeasureTheory.integrable_finsetSum Finset.univ
    intro i _
    apply MeasureTheory.integrable_finsetSum Finset.univ
    intro j _
    exact (hYint i j).const_mul (c i * c j)
  have haa_int : MeasureTheory.Integrable (fun x => a x * a x) μ := by
    have h : (fun x => a x * a x) = fun x => (a x)^2 := by funext x; ring
    rw [h]; exact ha2
  have hpap_int : MeasureTheory.Integrable (fun x => p x * a x) μ := by
    have h : (fun x => p x * a x) = fun x => a x * p x := by funext x; ring
    rw [h]; exact hap_int
  have hu2 : MeasureTheory.Integrable (fun x => (a x - p x)^2) μ := by
    have h : (fun x => (a x - p x)^2)
        = fun x => a x * a x - a x * p x - (p x * a x - p x * p x) := by
      funext x; ring
    rw [h]
    exact (haa_int.sub hap_int).sub (hpap_int.sub hpp_int)
  have hpg2_eq : (fun x => (p x - g x)^2)
      = fun x => ∑ i : ι, ∑ j : ι, ((c i - β i) * (c j - β j)) * (y i x * y j x) := by
    funext x
    rw [hpg_pt x, pow_two, Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hv2 : MeasureTheory.Integrable (fun x => (p x - g x)^2) μ := by
    rw [hpg2_eq]
    apply MeasureTheory.integrable_finsetSum Finset.univ
    intro i _
    apply MeasureTheory.integrable_finsetSum Finset.univ
    intro j _
    exact (hYint i j).const_mul ((c i - β i) * (c j - β j))
  have hcross_term_int : ∀ i ∈ (Finset.univ : Finset ι),
      MeasureTheory.Integrable (fun x => (c i - β i) * ((a x - p x) * y i x)) μ := by
    intro i _
    have hi : MeasureTheory.Integrable (fun x => (a x - p x) * y i x) μ := by
      have h : (fun x => (a x - p x) * y i x) = fun x => a x * y i x - p x * y i x := by
        funext x; ring
      rw [h]; exact (haint i).sub (hpk_int i)
    exact hi.const_mul (c i - β i)
  have hcross_int : MeasureTheory.Integrable (fun x => (a x - p x) * (p x - g x)) μ := by
    rw [hmain_eq]
    exact MeasureTheory.integrable_finsetSum Finset.univ hcross_term_int
  have hcross_zero : (∫ x, (a x - p x) * (p x - g x) ∂μ) = 0 := by
    rw [hmain_eq, MeasureTheory.integral_finsetSum Finset.univ hcross_term_int]
    apply Finset.sum_eq_zero
    intro i _
    rw [MeasureTheory.integral_const_mul, hcross_j i]
    ring
  have hpt : (fun x => (a x - g x)^2) = fun x => ((a x - p x) + (p x - g x))^2 := by
    funext x; ring
  have hexp : (fun x => ((a x - p x) + (p x - g x))^2)
      = fun x => (a x - p x)^2 + 2 * ((a x - p x) * (p x - g x)) + (p x - g x)^2 := by
    funext x; ring
  have hW_int : MeasureTheory.Integrable (fun x => 2 * ((a x - p x) * (p x - g x))) μ :=
    hcross_int.const_mul 2
  have hUW_int : MeasureTheory.Integrable
      (fun x => (a x - p x)^2 + 2 * ((a x - p x) * (p x - g x))) μ := hu2.add hW_int
  have hflip : (∫ x, (p x - g x)^2 ∂μ) = (∫ x, (g x - p x)^2 ∂μ) := by
    have heq : (fun x => (p x - g x)^2) = fun x => (g x - p x)^2 := by funext x; ring
    rw [heq]
  calc
    (∫ x, (a x - g x)^2 ∂μ)
        = ∫ x, ((a x - p x) + (p x - g x))^2 ∂μ := by rw [hpt]
    _ = ∫ x, (a x - p x)^2 + 2 * ((a x - p x) * (p x - g x)) + (p x - g x)^2 ∂μ := by
          rw [hexp]
    _ = (∫ x, (a x - p x)^2 + 2 * ((a x - p x) * (p x - g x)) ∂μ)
          + (∫ x, (p x - g x)^2 ∂μ) := MeasureTheory.integral_add hUW_int hv2
    _ = ((∫ x, (a x - p x)^2 ∂μ) + (∫ x, 2 * ((a x - p x) * (p x - g x)) ∂μ))
          + (∫ x, (p x - g x)^2 ∂μ) := by rw [MeasureTheory.integral_add hu2 hW_int]
    _ = ((∫ x, (a x - p x)^2 ∂μ) + 2 * (∫ x, (a x - p x) * (p x - g x) ∂μ))
          + (∫ x, (p x - g x)^2 ∂μ) := by rw [MeasureTheory.integral_const_mul]
    _ = ((∫ x, (a x - p x)^2 ∂μ) + 2 * 0) + (∫ x, (p x - g x)^2 ∂μ) := by rw [hcross_zero]
    _ = (∫ x, (a x - p x)^2 ∂μ) + (∫ x, (g x - p x)^2 ∂μ) := by rw [hflip]; ring


end Commons.Analysis.MeasureTheory