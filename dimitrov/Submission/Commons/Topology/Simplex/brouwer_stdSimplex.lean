import Mathlib
import Submission.Commons.Topology.Simplex.exists_approx_fixed_point_stdSimplex

namespace Commons.Topology.Simplex

open scoped BigOperators Topology
open Finset Filter

/-- **Brouwer's fixed point theorem for the standard simplex.**

For `n ≥ 1`, every continuous self-map `f` of the standard `(n-1)`-simplex
`{x : Fin n → ℝ // (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1}` has a fixed point.

The proof uses the quantitative (Sperner) input
`Commons.Topology.Simplex.exists_approx_fixed_point_stdSimplex`: for every `ε > 0` there is `x`
in the simplex with `f x i ≤ x i + ε` for all `i`.  Applying this along the sequence
`ε = 1/(m+1)`, a subsequence converges by compactness of the simplex, and at the limit the
inequalities `f a i ≤ a i` together with `∑ i, f a i = ∑ i, a i = 1` force `f a = a`. -/
theorem brouwer_stdSimplex (n : ℕ) (hn : 0 < n) (f : (Fin n → ℝ) → (Fin n → ℝ))
    (hf : Continuous f)
    (hmaps : ∀ x : Fin n → ℝ, (∀ i, 0 ≤ x i) → (∑ i, x i = 1) →
      (∀ i, 0 ≤ f x i) ∧ (∑ i, f x i) = 1) :
    ∃ x : Fin n → ℝ, (∀ i, 0 ≤ x i) ∧ (∑ i, x i = 1) ∧ f x = x := by
  have hmain : ∀ m : ℕ, ∃ x : Fin n → ℝ, (∀ i, 0 ≤ x i) ∧ (∑ i, x i = 1) ∧
      ∀ i, f x i ≤ x i + (1 / ((m : ℝ) + 1)) :=
    fun m => exists_approx_fixed_point_stdSimplex n hn f hf hmaps (1 / ((m : ℝ) + 1))
      (by positivity)
  choose x hx using hmain
  have hcpt : IsCompact (stdSimplex ℝ (Fin n)) := isCompact_stdSimplex ℝ (Fin n)
  obtain ⟨a, ha_mem, φ, hφ_mono, hφ_tendsto⟩ :=
    IsCompact.tendsto_subseq hcpt (x := x) (fun m => by
      exact ⟨(hx m).1, (hx m).2.1⟩)
  have ha0 : ∀ i, 0 ≤ a i := ha_mem.1
  have ha1 : ∑ i, a i = 1 := ha_mem.2
  have hφlim : Tendsto (fun m : ℕ => ((φ m : ℝ) + 1)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop (1 : ℝ)
      (tendsto_natCast_atTop_atTop.comp hφ_mono.tendsto_atTop))
  have hle : ∀ i, f a i ≤ a i := by
    intro i
    have hf_lim : Tendsto (fun m => f (x (φ m)) i) atTop (nhds (f a i)) :=
      (((continuous_apply i).comp hf).tendsto a).comp hφ_tendsto
    have hx_lim : Tendsto (fun m => x (φ m) i) atTop (nhds (a i)) :=
      (((continuous_apply i).tendsto a)).comp hφ_tendsto
    have hg_lim : Tendsto (fun m => x (φ m) i + ((φ m : ℝ) + 1)⁻¹) atTop (nhds (a i + 0)) :=
      hx_lim.add hφlim
    have := le_of_tendsto_of_tendsto' hf_lim hg_lim (fun m => by
      have h := (hx (φ m)).2.2 i
      rw [one_div] at h
      exact h)
    simpa using this
  refine ⟨a, ha0, ha1, ?_⟩
  funext i
  have hsum : ∑ i, f a i = ∑ i, a i := by rw [(hmaps a ha0 ha1).2, ha1]
  have hzero : ∑ i, (f a i - a i) = 0 := by rw [Finset.sum_sub_distrib, hsum, sub_self]
  have hled : ∀ i, f a i - a i ≤ 0 := fun i => sub_nonpos.mpr (hle i)
  have hall : ∀ i, f a i - a i = 0 := fun i =>
    (Finset.sum_eq_zero_iff_of_nonpos (s := Finset.univ) (fun i _ => hled i)).mp hzero i
      (Finset.mem_univ i)
  have := hall i
  linarith

end Commons.Topology.Simplex
