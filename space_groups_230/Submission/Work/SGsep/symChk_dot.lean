import Mathlib
import Submission.Work.SGsep.symChk_defs

namespace Work.SGsep

open Work.SG
open scoped BigOperators

/-- A `List.foldl`-accumulated sum over `List.range N` coincides with the `Finset.sum` over
`Finset.range N`. -/
theorem foldl_add_range (f : ℕ → ℤ) (init : ℤ) (N : ℕ) :
    List.foldl (fun acc g => acc + f g) init (List.range N)
      = init + ∑ g ∈ Finset.range N, f g := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.foldl_append, ih, Finset.sum_range_succ]
    simp only [List.foldl_cons, List.foldl_nil]
    ring

/-- `V3.dot` of a vector with a scalar multiple equals `dotZZ` of the corresponding
coordinate functions. -/
theorem dot_dotZZ (a b : Data.V3) (c : ℤ) :
    Data.V3.dot a (Data.V3.smul c b) = dotZZ a.toFun (fun i => c * b.toFun i) := by
  simp [Data.V3.dot, Data.V3.smul, Data.V3.toFun, dotZZ, Fin.sum_univ_three]

/-- **Dot condition ⇒ non-divisibility.** The certificate's dot product `∑_g u_g · (o/p)·z_g`,
computed as a `List.foldl` over `List.range D.gens.length`, equals the `Finset.sum` of `dotZZ` of
the blocks of `u` against `((o/p : ℕ) : ℤ) * (z g).toFun`; hence the `DotCond` non-divisibility
transfers.
Recipe: `(List.foldl (fun acc g => acc + f g) 0 (List.range N)) = ∑ g ∈ Finset.range N, f g`
by induction using `Finset.sum_range_succ`; `Work.SG.Data.V3.dot a b =
Work.SGsep.dotZZ a.toFun b.toFun`; and `Work.SG.Data.V3.smul` is coordinatewise `k * v i`
(with `k : ℤ`). -/
theorem symChk_dot (D : Work.SG.Data.ArithData) (o p : ℕ) (z : ℕ → Work.SG.Data.V3) (u : List ℤ)
    (h : Work.SGsep.DotCond D o p z u) :
    ¬ ((D.n : ℤ) ∣ ∑ g ∈ Finset.range D.gens.length,
        Work.SGsep.dotZZ (Work.SGsep.ublk u g)
          (fun i => ((o / p : ℕ) : ℤ) * (z g).toFun i)) := by
  intro hdiv
  apply h
  have hkey : List.foldl (fun acc g => acc + Data.V3.dot ((Data.blocks u).getD g Data.V3.zero)
        (Data.V3.smul ((o / p : ℕ) : ℤ) (z g))) 0 (List.range D.gens.length)
      = ∑ g ∈ Finset.range D.gens.length, dotZZ (ublk u g)
          (fun i => ((o / p : ℕ) : ℤ) * (z g).toFun i) := by
    rw [foldl_add_range (fun g => Data.V3.dot ((Data.blocks u).getD g Data.V3.zero)
        (Data.V3.smul ((o / p : ℕ) : ℤ) (z g))) 0 D.gens.length]
    simp only [zero_add]
    apply Finset.sum_congr rfl
    intro g _
    rw [ublk]
    exact dot_dotZZ _ _ _
  rw [hkey]
  exact hdiv

end Work.SGsep
