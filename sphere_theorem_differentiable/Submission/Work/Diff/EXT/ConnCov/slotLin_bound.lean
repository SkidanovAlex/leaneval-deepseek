import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedVariables false

namespace Work.Diff.EXT.ConnCov

open Finset
open scoped BigOperators

/-- Bound for a functional that is linear in each slot separately: if `Ψ` is additive and
homogeneous in every coordinate (`hlin`), if `Ψ` is bounded by `C` on the "pure tensors"
`fun i => b (p i)`, and if `w i = ∑ p, μ i p • b p`, then `|Ψ w|` is bounded by
`C` times the product of the `ℓ¹`-norms of the coefficient vectors `μ i`.

The proof packages `Ψ` as a `MultilinearMap ℝ (fun _ : Fin N => W) ℝ`, expands `w` with
`MultilinearMap.map_sum`, factorises each summand with `MultilinearMap.map_smul_univ`,
and finally applies the product-of-sums identity `Fintype.prod_sum`. -/
theorem slotLin_bound
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {N n : ℕ} (Ψ : (Fin N → W) → ℝ)
    (hlin : ∀ (u : Fin N → W) (i : Fin N) (s t : W) (α β : ℝ),
      Ψ (Function.update u i (α • s + β • t))
        = α * Ψ (Function.update u i s) + β * Ψ (Function.update u i t))
    (b : Fin n → W) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ p : Fin N → Fin n, |Ψ (fun i => b (p i))| ≤ C)
    (μ : Fin N → Fin n → ℝ) (w : Fin N → W)
    (hw : ∀ i, w i = Finset.sum Finset.univ (fun p : Fin n => μ i p • b p)) :
    |Ψ w| ≤ C * Finset.univ.prod (fun i : Fin N =>
      Finset.sum Finset.univ (fun p : Fin n => |μ i p|)) := by
  classical
  -- Package `Ψ` as a genuine multilinear map: `hlin` gives additivity and homogeneity
  -- in each slot.
  let Φ : MultilinearMap ℝ (fun _ : Fin N => W) ℝ :=
    MultilinearMap.mk' Ψ (fun u i s t => by simpa using hlin u i s t 1 1)
      (fun u i c s => by simpa using hlin u i s s c 0)
  have hcoe : ∀ u, Φ u = Ψ u := fun u => rfl
  -- Multilinear expansion of `w`, whose coordinates are sums.
  have hexp : Ψ w = ∑ r : Fin N → Fin n, (∏ i, μ i (r i)) * Ψ (fun i => b (r i)) := by
    rw [show w = (fun i => ∑ p : Fin n, μ i p • b p) from funext hw]
    rw [← hcoe (fun i => ∑ p : Fin n, μ i p • b p)]
    rw [MultilinearMap.map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [MultilinearMap.map_smul_univ, smul_eq_mul, hcoe]
  rw [hexp]
  calc |∑ r : Fin N → Fin n, (∏ i, μ i (r i)) * Ψ (fun i => b (r i))|
      ≤ ∑ r : Fin N → Fin n, |(∏ i, μ i (r i)) * Ψ (fun i => b (r i))| := by
        simpa using Finset.abs_sum_le_sum_abs
          (f := fun r : Fin N → Fin n => (∏ i, μ i (r i)) * Ψ (fun i => b (r i)))
          (s := Finset.univ)
    _ = ∑ r : Fin N → Fin n, (∏ i, |μ i (r i)|) * |Ψ (fun i => b (r i))| := by
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [abs_mul, Finset.abs_prod]
    _ ≤ ∑ r : Fin N → Fin n, (∏ i, |μ i (r i)|) * C := by
        refine Finset.sum_le_sum fun r _ => ?_
        exact mul_le_mul_of_nonneg_left (hb r) (Finset.prod_nonneg fun i _ => abs_nonneg _)
    _ = (∑ r : Fin N → Fin n, ∏ i, |μ i (r i)|) * C := by rw [Finset.sum_mul]
    _ = (∏ i : Fin N, ∑ p : Fin n, |μ i p|) * C := by rw [Fintype.prod_sum]
    _ = C * ∏ i : Fin N, ∑ p : Fin n, |μ i p| := by ring

end Work.Diff.EXT.ConnCov
