import Mathlib
import Submission.Work.ORHughesFree.Epic

/-!
# Matrices attached to a "one-relator style" datum over a ring homomorphism

Let `f : R →+* S` be a ring homomorphism.  Suppose we are given, for `k : Fin n`, a finitely
supported function `v k : S →₀ R` and an element `w k : S`, such that

* `∑_{s ∈ supp (v k)} s * f (v k s) = 0` for every `k` (the "relation"), and
* `∑_k f (v k s) * w k` equals `-d` for `s = 1`, equals `1` for `s = d`, and equals `0` for every
  other `s`.

Then `d` can be written as `X · f(P) · Y` for matrices `X = (x_j)` (`1 × m` over `S`),
`P = (p_{jk})` (`m × n` over `R`) and `Y` (`n × 1` over `S`) such that `X · f(P)` is a row over
`f(R)` and `f(P) · Y` is a column over `f(R)`.

The construction takes the row index set to be the finite set `U \ {1}`, where `U` is the union of
the supports of the `v k`; the row attached to `s` is `p_{s} = (v k s)_k` and its coefficient is
`-s`.  Writing `E^{(s)} = (f (v k s))_k` and `g(s) = ∑_k f (v k s) w k`, the hypothesis on the
`v k` says `∑_{s ∈ U} s • E^{(s)} = 0`, so that `u := E^{(1)} = -∑_{s ∈ U \ {1}} s • E^{(s)}`; and
`g(s) ∈ f(R)` for every `s ∈ U \ {1}`, since `g(d) = 1` and `g` vanishes away from `1` and `d`.
Finally `u · w = ∑_k f (v k 1) w k = -d`, so `u · (-w) = d`.
-/

namespace Work.ORHughesFree.Epic

theorem exists_matrices_of_data {R S : Type} [Ring R] [Ring S] (f : R →+* S)
    (d : S) {n : ℕ} (v : Fin n → S →₀ R) (w : Fin n → S)
    (hv : ∀ k, ∑ s ∈ (v k).support, s * f (v k s) = 0)
    (h1 : (∑ k, f (v k 1) * w k) = -d)
    (hd' : (∑ k, f (v k d) * w k) = 1)
    (h0 : ∀ s, s ≠ 1 → s ≠ d → (∑ k, f (v k s) * w k) = 0) :
    ∃ (m : ℕ) (X : Matrix (Fin 1) (Fin m) S) (P : Matrix (Fin m) (Fin n) R)
      (Y : Matrix (Fin n) (Fin 1) S),
      (∃ P' : Matrix (Fin 1) (Fin n) R, X * P.map f = P'.map f) ∧
      (∃ Q' : Matrix (Fin m) (Fin 1) R, P.map f * Y = Q'.map f) ∧
      d = (X * P.map f * Y) 0 0 := by
  classical
  -- `U` : the finite set of values of `s` occurring in one of the supports.
  set U : Finset S := Finset.univ.biUnion (fun k : Fin n => (v k).support) with hU
  -- `T` : the row index set, `U` with `1` removed.
  set T : Finset S := U.erase 1 with hT
  have hsupp : ∀ k, (v k).support ⊆ U := fun k s hs =>
    Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ k, hs⟩
  -- The relation, summed over all of `U`.
  have hvU : ∀ k, ∑ s ∈ U, s * f (v k s) = 0 := by
    intro k
    refine (Finset.sum_subset (hsupp k) ?_).symm.trans (hv k)
    intro x _ hx
    have hz : v k x = 0 := by
      by_contra h
      exact hx (Finsupp.mem_support_iff.mpr h)
    rw [hz, map_zero, mul_zero]
  -- The relation, with the `s = 1` term isolated.
  have hkey : ∀ k, ∑ s ∈ T, s * f (v k s) = -f (v k 1) := by
    intro k
    by_cases h1U : (1 : S) ∈ U
    · have h := Finset.sum_erase_add U (fun s => s * f (v k s)) h1U
      have hh : (∑ x ∈ U.erase 1, x * f (v k x)) + 1 * f (v k 1) = 0 :=
        h.trans (hvU k)
      rw [hT]
      simpa using eq_neg_of_add_eq_zero_left hh
    · have hTeq : T = U := by
        rw [hT]; exact Finset.erase_eq_of_notMem h1U
      have hz : v k 1 = 0 := by
        by_contra h
        exact h1U (hsupp k (Finsupp.mem_support_iff.mpr h))
      rw [hTeq, hvU k, hz, map_zero, neg_zero]
  -- An enumeration of the finite index set `T`.
  let e : ↥T ≃ Fin T.card := T.equivFin
  let X : Matrix (Fin 1) (Fin T.card) S := Matrix.of (fun _ j => -((e.symm j).1))
  let P : Matrix (Fin T.card) (Fin n) R := Matrix.of (fun j k => v k ((e.symm j).1))
  let Y : Matrix (Fin n) (Fin 1) S := Matrix.of (fun k _ => -w k)
  let P' : Matrix (Fin 1) (Fin n) R := Matrix.of (fun _ k => v k 1)
  let Q' : Matrix (Fin T.card) (Fin 1) R :=
    Matrix.of (fun j _ => if (e.symm j).1 = d then -1 else 0)
  -- `X · f(P)` is the row over `f(R)` given by `(f (v k 1))_k`.
  have hX : X * P.map f = P'.map f := by
    ext i k
    fin_cases i
    rw [Matrix.mul_apply]
    simp only [X, P, P', Matrix.of_apply, Matrix.map_apply]
    have hsum : (∑ j : Fin T.card, ((e.symm j).1) * f (v k ((e.symm j).1))) = -f (v k 1) := by
      have hsum' : (∑ j : Fin T.card, ((e.symm j).1) * f (v k ((e.symm j).1)))
          = ∑ s ∈ T, s * f (v k s) := by
        rw [← Finset.sum_attach T (fun s => s * f (v k s))]
        exact Fintype.sum_equiv e.symm _ _ (fun j => by simp)
      exact hsum'.trans (hkey k)
    have hneg : (∑ j : Fin T.card, -((e.symm j).1) * f (v k ((e.symm j).1)))
        = -(∑ j : Fin T.card, ((e.symm j).1) * f (v k ((e.symm j).1))) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun j _ => neg_mul _ _)
    rw [hneg, hsum, neg_neg]
  -- `f(P) · Y` is the column over `f(R)` with a `-1` in the row indexed by `d`.
  have hY : P.map f * Y = Q'.map f := by
    ext j i
    fin_cases i
    rw [Matrix.mul_apply]
    simp only [P, Y, Q', Matrix.of_apply, Matrix.map_apply]
    have hx1 : (e.symm j).1 ≠ 1 := by
      have : (e.symm j).1 ∈ U.erase 1 := by rw [← hT]; exact (e.symm j).2
      exact (Finset.mem_erase.mp this).1
    have hneg : (∑ k : Fin n, f (v k ((e.symm j).1)) * -w k)
        = -(∑ k : Fin n, f (v k ((e.symm j).1)) * w k) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun k _ => mul_neg _ _)
    by_cases hxd : (e.symm j).1 = d
    · rw [if_pos hxd, map_neg, map_one, hneg]
      rw [show (∑ k : Fin n, f (v k ((e.symm j).1)) * w k) = 1 by rw [hxd]; exact hd']
    · rw [if_neg hxd, hneg, h0 _ hx1 hxd, neg_zero, map_zero]
  -- The product recovers `d`.
  have hfin : (X * P.map f * Y) 0 0 = d := by
    rw [hX, Matrix.mul_apply]
    simp only [P', Y, Matrix.of_apply, Matrix.map_apply]
    have hneg : (∑ k : Fin n, f (v k 1) * -w k) = -(∑ k : Fin n, f (v k 1) * w k) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun k _ => mul_neg _ _)
    rw [hneg, h1, neg_neg]
  exact ⟨T.card, X, P, Y, ⟨P', hX⟩, ⟨Q', hY⟩, hfin.symm⟩

end Work.ORHughesFree.Epic
