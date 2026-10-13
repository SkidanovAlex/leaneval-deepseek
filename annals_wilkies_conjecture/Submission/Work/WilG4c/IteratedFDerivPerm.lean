import Mathlib
import Submission.Work.WilG4c.iterDir_perm
import Submission.Work.WilG4c.iterDir_eq_iteratedFDeriv

open scoped Topology

namespace Work.WilG4c

open Work.WilkG4c

/-- Reindexing the `n`-th iterated derivative of a function of `Fin N → ℝ` along an
identification `n = m` of the number of derivative slots.  `iteratedFDeriv` is a function of
its index, and `Fin.cast` transports the direction tuple across the identification. -/
private lemma iteratedFDeriv_cast {N n m : ℕ} (h : n = m) (f : (Fin N → ℝ) → ℝ) (x : Fin N → ℝ)
    (g : Fin n → (Fin N → ℝ)) :
    iteratedFDeriv ℝ n f x g = iteratedFDeriv ℝ m f x (fun i => g (Fin.cast h.symm i)) := by
  subst h
  simp

/-- The `m`-th iterated Fréchet derivative of `f` at `x`, evaluated on the tuple of standard
basis direction vectors `i ↦ single (v i) 1`, is invariant under permuting the indexing
permutation `σ` of the directions.

This is the symmetry of the higher mixed partial derivatives of a `C^m` function, available in
Mathlib only for analytic functions (`ContDiffAt.iteratedFDeriv_comp_perm`).  We obtain it for
`C^m` functions by routing through the iterated directional derivative `iterDir` of
`Submission/Work/WilG4c/Engine.lean`, whose permutation invariance for `C^{|L|}` functions is
proved in `Submission/Work/WilG4c/iterDir_perm.lean` (Clairaut/Schwarz plus an induction on the
number of derivatives). -/
theorem IteratedFDerivPerm {N m : ℕ} {f : (Fin N → ℝ) → ℝ} {x : Fin N → ℝ}
    (hf : ContDiffAt ℝ m f x) (σ : Equiv.Perm (Fin m)) (v : Fin m → Fin N) :
    iteratedFDeriv ℝ m f x (fun i => Pi.single (v (σ i)) 1)
      = iteratedFDeriv ℝ m f x (fun i => Pi.single (v i) 1) := by
  -- `List.ofFn` turns the direction tuples `v` and `v ∘ σ` into lists, which are related by
  -- `List.Perm` because `σ` is a permutation.
  have hlen : (List.ofFn v).length = m := List.length_ofFn
  have hlen' : (List.ofFn (v ∘ σ)).length = m := List.length_ofFn
  have hperm : (List.ofFn (v ∘ σ)).Perm (List.ofFn v) := Equiv.Perm.ofFn_comp_perm σ v
  -- The permutation invariance of the iterated directional derivative.
  have h1 : Work.WilkG4c.iterDir (List.ofFn (v ∘ σ)) f x
      = Work.WilkG4c.iterDir (List.ofFn v) f x :=
    Work.WilG4c.iterDir_perm f hperm x (by rw [hlen']; exact hf)
  let gW' : Fin m → (Fin N → ℝ) := fun i => Pi.single (v (σ i)) 1
  let gW : Fin m → (Fin N → ℝ) := fun i => Pi.single (v i) 1
  let A' : Fin (List.ofFn (v ∘ σ)).length → (Fin N → ℝ) :=
    fun k => Pi.single ((List.ofFn (v ∘ σ)).get k) 1
  let A : Fin (List.ofFn v).length → (Fin N → ℝ) :=
    fun k => Pi.single ((List.ofFn v).get k) 1
  -- `List.get_ofFn` identifies `A'` (resp. `A`) reindexed by `Fin.cast hlen'.symm` (resp.
  -- `Fin.cast hlen.symm`) with the original direction tuple.
  have hA' : (fun i : Fin m => A' (Fin.cast hlen'.symm i)) = gW' := by
    funext i
    simp only [A', gW', List.get_ofFn]
    simp
  have hA : (fun i : Fin m => A (Fin.cast hlen.symm i)) = gW := by
    funext i
    simp only [A, gW, List.get_ofFn]
    simp
  change iteratedFDeriv ℝ m f x gW' = iteratedFDeriv ℝ m f x gW
  -- Chain the two evaluations through `iterDir`, using that `iterDir L f x` is
  -- `iteratedFDeriv ℝ L.length f x` evaluated on `fun k => Pi.single (L.get k) 1`.
  calc iteratedFDeriv ℝ m f x gW'
      = iteratedFDeriv ℝ m f x (fun i => A' (Fin.cast hlen'.symm i)) := by rw [hA']
    _ = iteratedFDeriv ℝ (List.ofFn (v ∘ σ)).length f x A' :=
        (iteratedFDeriv_cast hlen' f x A').symm
    _ = Work.WilkG4c.iterDir (List.ofFn (v ∘ σ)) f x :=
        (Work.WilG4c.iterDir_eq_iteratedFDeriv (List.ofFn (v ∘ σ)) f x
          (by rw [hlen']; exact hf)).symm
    _ = Work.WilkG4c.iterDir (List.ofFn v) f x := h1
    _ = iteratedFDeriv ℝ (List.ofFn v).length f x A :=
        Work.WilG4c.iterDir_eq_iteratedFDeriv (List.ofFn v) f x (by rw [hlen]; exact hf)
    _ = iteratedFDeriv ℝ m f x (fun i => A (Fin.cast hlen.symm i)) :=
        iteratedFDeriv_cast hlen f x A
    _ = iteratedFDeriv ℝ m f x gW := by rw [hA]

end Work.WilG4c
