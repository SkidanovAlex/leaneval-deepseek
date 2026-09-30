import Mathlib
import Submission.Work.BW.siegel_numberField

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Siegel's lemma over a number field, arbitrary finite index types

`Work.BW.siegel_fintype` is the `Fin`-indexed Siegel lemma
`Work.BW.siegel_numberField` transported to arbitrary finite index types `ι` (the rows) and
`κ` (the unknowns).  Everything in the statement is invariant under a reindexing equivalence:

* `Height.logHeight` of a tuple only depends on the tuple up to reindexing
  (`Height.logHeight_comp_equiv`);
* the equation `∑ j, a i j * x j = 0` is reindexed by transporting the coefficients along
  `κ ≃ Fin (Fintype.card κ)`;
* the bound only involves the cardinalities `Fintype.card ι`, `Fintype.card κ`.

So the proof here is: pick `eι : ι ≃ Fin (card ι)`, `eκ : κ ≃ Fin (card κ)`, apply
`siegel_numberField` to the transported matrix `(i, j) ↦ a (eι.symm i) (eκ.symm j)`, and
transport the solution and the height bound back.

## State of this file / routes to a self-contained proof

This file currently reduces the general (`Fintype`) statement to the `Fin`-indexed sibling
`Work.BW.siegel_numberField`.  A self-contained proof of that sibling would follow from the
following pieces, all of which are already available or under construction in this directory:

* `Submission.Work.BW.vaalerSection` — Vaaler's cube-section inequality
  `vol(V ∩ [-1,1]^n) ≥ 2^dim V` (the geometric input for Minkowski I in the kernel lattice);
* `Submission.Work.BW.siegel_short_vector2` — the kernel-lattice/Minkowski step over a number
  field: if the rows are `F`-linearly independent and
  `r^{d(N-M)} ≥ (2^{-r₂}√|disc F|)^{N-M} · ∏ᵢ (N^{d/2} · H(aᵢ))`, then there is a nonzero
  `x ∈ (𝓞 F)^N` with `∑ⱼ aᵢⱼ xⱼ = 0` whose `mixedEmbedding.stdBasis` coordinates are `≤ r`
  (`H` the multiplicative height of the row, built from the `InfinitePlace`/`FinitePlace`
  sup-norms so that the whole factor is invariant under scaling a row by a constant of `F`);
* `Submission.Work.BW.logHeight_le_of_mixed_coord_le` — the coordinate bound gives
  `logHeight x ≤ d log r + r₂ log 2`;
* the elementary arithmetic: `log c_F = ½ log |disc F| - r₂ log 2`, `log‖row‖ ≤ ½ log(dN) + …`,
  plus dropping `F`-dependent rows (`1/(N-M') ≤ 1/(N-M)`, all summands nonnegative).

The two `siegel_*`/`logHeight_*` pieces above are currently being proved in parallel; once they
and the arithmetic are in place, `Work.BW.siegel_numberField` (and hence this file) can be
completed without any `sorry`.
-/

/-!
# Siegel's lemma over a number field, arbitrary finite index types

`Work.BW.siegel_fintype` is the `Fin`-indexed Siegel lemma
`Work.BW.siegel_numberField` transported to arbitrary finite index types `ι` (the rows) and
`κ` (the unknowns).  Everything in the statement is invariant under a reindexing equivalence:

* `Height.logHeight` of a tuple only depends on the tuple up to reindexing
  (`Height.logHeight_comp_equiv`);
* the equation `∑ j, a i j * x j = 0` is reindexed by transporting the coefficients along
  `κ ≃ Fin (Fintype.card κ)`;
* the bound only involves the cardinalities `Fintype.card ι`, `Fintype.card κ`.

So the proof is: pick `eι : ι ≃ Fin (card ι)`, `eκ : κ ≃ Fin (card κ)`, apply
`siegel_numberField` to the transported matrix `(i, j) ↦ a (eι.symm i) (eκ.symm j)`, and
transport the solution and the height bound back.
-/

namespace Work.BW

theorem siegel_fintype {F : Type*} [Field F] [NumberField F] {ι κ : Type*} [Fintype ι]
    [Fintype κ] (hcard : Fintype.card ι < Fintype.card κ) (a : ι → κ → F) :
    ∃ x : κ → NumberField.RingOfIntegers F, x ≠ 0 ∧
      (∀ i, ∑ j, a i j * (x j : F) = 0) ∧
      Height.logHeight (fun j => (x j : F)) ≤
        (1 / 2) * Real.log |((NumberField.discr F : ℤ) : ℝ)| +
          (1 / ((Fintype.card κ : ℝ) - Fintype.card ι)) *
            ∑ i, ((1 / 2) * (Module.finrank ℚ F : ℝ) * Real.log (Fintype.card κ) +
              Height.logHeight (a i)) := by
  classical
  let eι : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let eκ : κ ≃ Fin (Fintype.card κ) := Fintype.equivFin κ
  obtain ⟨x', hx'ne, hx'ann, hx'bd⟩ :=
    siegel_numberField (F := F) hcard (fun i j => a (eι.symm i) (eκ.symm j))
  refine ⟨fun j => x' (eκ j), ?_, ?_, ?_⟩
  · intro h
    apply hx'ne
    funext j
    have hh := congrFun h (eκ.symm j)
    simpa [Function.comp_def, eκ] using hh
  · intro i
    have h := hx'ann (eι i)
    rw [← h]
    exact Fintype.sum_equiv eκ (fun j => a i j * (x' (eκ j) : F))
      (fun j' => a (eι.symm (eι i)) (eκ.symm j') * (x' j' : F)) (fun j => by simp [eι, eκ])
  · have hcomp : Height.logHeight (fun j : κ => (x' (eκ j) : F))
        = Height.logHeight (fun j : Fin (Fintype.card κ) => (x' j : F)) := by
      simpa [Function.comp_def] using
        Height.logHeight_comp_equiv (K := F) eκ (fun j : Fin (Fintype.card κ) => (x' j : F))
    have hsum : (∑ i : ι, ((1 / 2) * (Module.finrank ℚ F : ℝ) * Real.log (Fintype.card κ) +
            Height.logHeight (a i)))
        = ∑ i' : Fin (Fintype.card ι), ((1 / 2) * (Module.finrank ℚ F : ℝ) *
            Real.log (Fintype.card κ) +
            Height.logHeight (fun j' : Fin (Fintype.card κ) => a (eι.symm i') (eκ.symm j'))) := by
      refine Fintype.sum_equiv eι
        (fun i : ι => (1 / 2) * (Module.finrank ℚ F : ℝ) * Real.log (Fintype.card κ) +
          Height.logHeight (a i))
        (fun i' : Fin (Fintype.card ι) => (1 / 2) * (Module.finrank ℚ F : ℝ) *
          Real.log (Fintype.card κ) +
          Height.logHeight (fun j' : Fin (Fintype.card κ) => a (eι.symm i') (eκ.symm j'))) ?_
      intro i
      rw [show eι.symm (eι i) = i from Equiv.symm_apply_apply eι i]
      congr 1
      exact (Height.logHeight_comp_equiv (K := F) eκ.symm (a i)).symm
    rw [hcomp, hsum]
    exact hx'bd

end Work.BW
