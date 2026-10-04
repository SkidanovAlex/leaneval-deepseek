import Mathlib
import Submission.Work.Diff.STE.Torus

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Continuity of the Gagliardo–Nirenberg "regularisation" integrals in the parameter

This file proves `Work.Diff.STE.GN.tendsto_integral_rpow_add_sq_clean`: for continuous
`N M : (ι → ℝ) → ℝ` with `N ≥ 0`, `M ≥ 0` and `s ≥ 0`,

`n ↦ ∫_{unitCube} (N x + (1/(n+1))²)^s · M x  ⟶  ∫_{unitCube} (N x)^s · M x`.

The proof is the dominated convergence theorem: the base `N x + ε²` is bounded below by `0`,
bounded above on the (bounded) cube (since `N` is continuous and the cube is contained in the
compact box `[0,1]^ι`), the supplementary term `ε²` tends to `0` and is at most `1`, and
`y ↦ y^s` is continuous at every `y ≥ 0` for `s ≥ 0`.
-/

namespace Work.Diff.STE.GN

open MeasureTheory

/-! ### Elementary facts about the unit cube -/

/-- The unit cube `(0,1]^ι` is measurable. -/
private lemma measurableSet_unitCube {ι : Type*} [Fintype ι] :
    MeasurableSet (Work.Diff.STE.unitCube (ι := ι)) := by
  rw [Work.Diff.STE.unitCube]
  exact MeasurableSet.pi (Set.Finite.countable Set.finite_univ) fun _ _ => measurableSet_Ioc

/-- The unit cube is contained in the compact box `[0,1]^ι`. -/
private lemma unitCube_subset_box {ι : Type*} :
    Work.Diff.STE.unitCube (ι := ι) ⊆ Set.pi Set.univ (fun _ : ι => Set.Icc (0 : ℝ) 1) := by
  intro x hx
  simp only [Work.Diff.STE.unitCube, Set.mem_pi, Set.mem_univ, true_implies] at hx ⊢
  exact fun j => ⟨le_of_lt (hx j).1, (hx j).2⟩

/-- A continuous real function on `ι → ℝ` is bounded above on the unit cube. -/
private lemma exists_bound_on_unitCube {ι : Type*} [Fintype ι] {F : (ι → ℝ) → ℝ}
    (hF : Continuous F) : ∃ C : ℝ, ∀ x ∈ Work.Diff.STE.unitCube (ι := ι), F x ≤ C := by
  have hK : IsCompact (Set.pi Set.univ (fun _ : ι => Set.Icc (0 : ℝ) 1)) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hF.continuousOn
  refine ⟨C, fun x hx => ?_⟩
  have h1 := hC x (unitCube_subset_box hx)
  rw [Real.norm_eq_abs] at h1
  exact le_trans (le_abs_self (F x)) h1

/-- A constant function is integrable on the unit cube. -/
private lemma integrableOn_unitCube_const {ι : Type*} [Fintype ι] (C : ℝ) :
    Integrable (fun _ : ι → ℝ => C) (volume.restrict (Work.Diff.STE.unitCube (ι := ι))) := by
  have hK : IsCompact (Set.pi Set.univ (fun _ : ι => Set.Icc (0 : ℝ) 1)) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have h1 : IntegrableOn (fun _ : ι → ℝ => C) (Set.pi Set.univ (fun _ : ι => Set.Icc (0 : ℝ) 1))
      volume := ContinuousOn.integrableOn_compact hK continuousOn_const
  exact (h1.mono_set unitCube_subset_box).integrable

/-! ### The auxiliary sequence `ε n = 1/(n+1)` -/

private lemma inv_nonneg (n : ℕ) : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity

private lemma inv_sq_nonneg (n : ℕ) : 0 ≤ (1 / ((n : ℝ) + 1)) ^ 2 := by positivity

private lemma inv_le_one (n : ℕ) : 1 / ((n : ℝ) + 1) ≤ 1 := by
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
  have h : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

private lemma inv_sq_le_one (n : ℕ) : (1 / ((n : ℝ) + 1)) ^ 2 ≤ 1 := by
  calc (1 / ((n : ℝ) + 1)) ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ (inv_nonneg n) (inv_le_one n) 2
    _ = 1 := by norm_num

private lemma tendsto_inv_sq :
    Filter.Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1)) ^ 2) Filter.atTop (nhds 0) := by
  have h : Filter.Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1) : ℝ)) Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  simpa using h.pow 2

/-! ### The dominated convergence argument -/

/-- **Main auxiliary statement.**  For a sequence `c : ℕ → ℝ` with `0 ≤ c n ≤ 1` and `c n → 0`,
the integrals `∫_{cube} (N x + c n)^s M x` converge to `∫_{cube} (N x)^s M x`. -/
private lemma tendsto_integral_rpow_add_of {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ℝ) (hs : 0 ≤ s) (N M : (ι → ℝ) → ℝ) (hN : Continuous N) (hM : Continuous M)
    (hN0 : ∀ x, 0 ≤ N x) (hM0 : ∀ x, 0 ≤ M x)
    (c : ℕ → ℝ) (hc0 : ∀ n, 0 ≤ c n) (hc1 : ∀ n, c n ≤ 1)
    (hc : Filter.Tendsto c Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n : ℕ => ∫ x in Work.Diff.STE.unitCube (ι := ι), (N x + c n) ^ s * M x)
      Filter.atTop
      (nhds (∫ x in Work.Diff.STE.unitCube (ι := ι), (N x) ^ s * M x)) := by
  obtain ⟨CN, hCN⟩ := exists_bound_on_unitCube (ι := ι) hN
  obtain ⟨CM, hCM⟩ := exists_bound_on_unitCube (ι := ι) hM
  have hbase0 : 0 ≤ max CN 0 + 1 := by linarith [le_max_right CN (0 : ℝ)]
  have hB00 : 0 ≤ (max CN 0 + 1) ^ s := Real.rpow_nonneg hbase0 s
  refine MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (Work.Diff.STE.unitCube (ι := ι)))
    (fun _ : ι → ℝ => (max CN 0 + 1) ^ s * max CM 0) ?_ ?_ ?_ ?_
  · intro n
    exact (((Real.continuous_rpow_const hs).comp (hN.add_const _)).mul hM).aestronglyMeasurable
  · exact integrableOn_unitCube_const _
  · intro n
    rw [MeasureTheory.ae_restrict_iff' measurableSet_unitCube]
    filter_upwards with x hx
    have hNx : N x ≤ max CN 0 := le_trans (hCN x hx) (le_max_left _ _)
    have hMx : M x ≤ max CM 0 := le_trans (hCM x hx) (le_max_left _ _)
    have hb0 : 0 ≤ N x + c n := add_nonneg (hN0 x) (hc0 n)
    have hb1 : N x + c n ≤ max CN 0 + 1 := by have := hc1 n; linarith
    have hrpow : (N x + c n) ^ s ≤ (max CN 0 + 1) ^ s := Real.rpow_le_rpow hb0 hb1 hs
    have hnn : 0 ≤ (N x + c n) ^ s * M x := mul_nonneg (Real.rpow_nonneg hb0 s) (hM0 x)
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    exact mul_le_mul hrpow hMx (hM0 x) hB00
  · rw [MeasureTheory.ae_restrict_iff' measurableSet_unitCube]
    filter_upwards with x _
    have hbase : Filter.Tendsto (fun n : ℕ => N x + c n) Filter.atTop (nhds (N x)) := by
      simpa using (tendsto_const_nhds (x := N x)).add hc
    have h1 : Filter.Tendsto (fun n : ℕ => (N x + c n) ^ s) Filter.atTop (nhds ((N x) ^ s)) :=
      ((Real.continuous_rpow_const hs).tendsto (N x)).comp hbase
    simpa using h1.mul_const (M x)

theorem tendsto_integral_rpow_add_sq_clean {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ℝ) (hs : 0 ≤ s) (N M : (ι → ℝ) → ℝ)
    (hN : Continuous N) (hM : Continuous M) (hN0 : ∀ x, 0 ≤ N x) (hM0 : ∀ x, 0 ≤ M x) :
    Filter.Tendsto
      (fun n : ℕ => ∫ x in Work.Diff.STE.unitCube (ι := ι),
        (N x + (1 / ((n : ℝ) + 1)) ^ 2) ^ s * M x)
      Filter.atTop
      (nhds (∫ x in Work.Diff.STE.unitCube (ι := ι), (N x) ^ s * M x)) :=
  tendsto_integral_rpow_add_of (ι := ι) s hs N M hN hM hN0 hM0
    (fun n => (1 / ((n : ℝ) + 1)) ^ 2) inv_sq_nonneg inv_sq_le_one tendsto_inv_sq

end Work.Diff.STE.GN
