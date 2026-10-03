/-
# `rdim` as the supremum of the dimensions of the spans of finitely many elements

For a left `R`-submodule `K ≤ R^n`, the row-wise dimension `rdim rk K` (the supremum of `rk A`
over the matrices whose rows lie in `K`, see `DualityDefs.lean`) agrees with the supremum of
`rdim rk (span (range v))` over all finite families `v` of elements of `K`.

Both inclusions are immediate from the API of `rdim`:

* for a matrix `A` with rows in `K`, the span `W` of its rows satisfies `W ≤ K` and
  `rdim rk W = rk A` (`rdim_eq_rk_rows`), so `rk A` is one of the numbers on the right;
* conversely `rdim rk (span (range v)) ≤ rdim rk K` for a finite family `v` with values in `K`,
  by monotonicity of `rdim` (`rdim_mono`) applied to `span (range v) ≤ K`.
-/
import Mathlib
import Submission.Work.ORHughesFree.SylvesterRank
import Submission.Work.ORHughesFree.NaturalExtension.DualityAPI

set_option autoImplicit false

universe u

open Matrix Work.ORHughesFree

namespace Work.ORHughesFree.NaturalExtension

theorem rdim_eq_sSup_span {R : Type u} [Ring R] [VonNeumannRegularRing R] (rk : SylvesterRank R)
    {n : ℕ} (K : Submodule R (Fin n → R)) :
    rdim rk K = sSup {x : ℝ | ∃ (k : ℕ) (v : Fin k → (Fin n → R)),
      (∀ i, v i ∈ K) ∧ x = rdim rk (Submodule.span R (Set.range v))} := by
  classical
  set S : Set ℝ := {x : ℝ | ∃ (k : ℕ) (v : Fin k → (Fin n → R)),
      (∀ i, v i ∈ K) ∧ x = rdim rk (Submodule.span R (Set.range v))} with hS
  -- Every element of `S` is at most `rdim rk K`, by monotonicity of `rdim`.
  have hle : ∀ y ∈ S, y ≤ rdim rk K := by
    rintro y ⟨k, v, hv, rfl⟩
    exact rdim_mono rk (Submodule.span_le.mpr (Set.range_subset_iff.mpr hv))
  have hne : S.Nonempty :=
    ⟨rdim rk (Submodule.span R (Set.range (fun i : Fin 0 => (Fin.elim0 i : Fin n → R)))),
      0, (fun i : Fin 0 => Fin.elim0 i), (fun i => Fin.elim0 i), rfl⟩
  have hbdd : BddAbove S := ⟨rdim rk K, hle⟩
  refine le_antisymm ?_ (csSup_le hne hle)
  -- `rdim rk K` is itself one of the numbers on the right, via `rdim_eq_rk_rows`.
  unfold rdim
  refine csSup_le (rdim_nonempty rk K) ?_
  rintro x ⟨m, A, hA, rfl⟩
  refine le_csSup hbdd ⟨m, (fun i j => A i j), (fun i => hA i), ?_⟩
  exact (rdim_eq_rk_rows rk A).symm

end Work.ORHughesFree.NaturalExtension
