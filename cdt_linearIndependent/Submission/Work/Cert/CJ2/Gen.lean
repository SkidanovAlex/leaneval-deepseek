/-
# Generic data structures and copies used by `Work.Cert.conj2_cert`

The conjunct-2 certificate is a list of 12288 arcs (`Final.arcsAll`) split into 156 chunk lists
whose `arcOK` chains are checked by `okC000 … okC155`.  This file contains the *data-free* generic
vocabulary used to glue those chains and to evaluate the weighted sum: it deliberately imports only
`Defs` (not `Final`), so that lemmas about it can be proved and kernel-checked without loading the
156 chunk modules (which cost ~16 GB).

`merge`, `msort` and `sortedSum` are verbatim copies of the definitions in `Submission.Work.Cert.Final`
(the same bodies, so `rfl` transfers between the two); the copies are here so that the generic lemmas
about them can be stated in a light module.
-/
import Mathlib
import Submission.Work.Cert.Defs

namespace Work.Cert.CJ2

open Work.Cert

/-! ## Arcs and chains of arcs -/

/-- dummy arc, for total functions on lists of arcs. -/
def dummyArc : ArcD := ⟨0, 0, 0, 0, [], 0⟩

/-- first arc of a list (dummy on `[]`). -/
def headArc : List ArcD → ArcD
  | [] => dummyArc
  | a :: _ => a

/-- last arc of a list (dummy on `[]`). -/
def lastArc : List ArcD → ArcD
  | [] => dummyArc
  | [a] => a
  | _ :: t => lastArc t

@[simp] theorem headArc_nil : headArc ([] : List ArcD) = dummyArc := rfl
@[simp] theorem headArc_cons (a : ArcD) (t : List ArcD) : headArc (a :: t) = a := rfl
@[simp] theorem lastArc_nil : lastArc ([] : List ArcD) = dummyArc := rfl
@[simp] theorem lastArc_singleton (a : ArcD) : lastArc [a] = a := rfl
theorem lastArc_cons_cons (a b : ArcD) (t : List ArcD) : lastArc (a :: b :: t) = lastArc (b :: t) := rfl

/-- One step of the chain: consecutive arcs in the *same* circle share the successor's grid point;
a change of circle (which by construction only happens at the last arc of a circle) must end the
previous arc at `(Rk k, 0)`. -/
def linkStep (a b : ArcD) : Bool :=
  if a.k = b.k then arcOK a b.Ex b.Ey else arcOK a (Rk a.k) 0

theorem linkStep_same {a b : ArcD} (h : a.k = b.k) : linkStep a b = arcOK a b.Ex b.Ey := by
  rw [linkStep]; exact if_pos h

theorem linkStep_diff {a b : ArcD} (h : a.k ≠ b.k) : linkStep a b = arcOK a (Rk a.k) 0 := by
  rw [linkStep]; exact if_neg h

/-- `arcsChainTo Fx Fy L`: the arcs of `L` form one continuous chain of leaves; the last arc
ends at the grid point `(Fx, Fy)`. -/
def arcsChainTo (Fx Fy : Int) : List ArcD → Bool
  | [] => true
  | [a] => arcOK a Fx Fy
  | a :: b :: rest => linkStep a b && arcsChainTo Fx Fy (b :: rest)

theorem arcsChainTo_nil (Fx Fy : Int) : arcsChainTo Fx Fy [] = true := rfl
theorem arcsChainTo_singleton (Fx Fy : Int) (a : ArcD) : arcsChainTo Fx Fy [a] = arcOK a Fx Fy := rfl
theorem arcsChainTo_cons_cons (Fx Fy : Int) (a b : ArcD) (t : List ArcD) :
    arcsChainTo Fx Fy (a :: b :: t) = (linkStep a b && arcsChainTo Fx Fy (b :: t)) := rfl

/-! ## The weighted double sum -/

/-- `Σ_{a,b} w_a w_b max v_a v_b` over a list of `(value, weight)` pairs, as a list recursion:
`Dsum (x :: l) = w_x² v_x + 2 w_x Σ_{y ∈ l} w_y max v_x v_y + Dsum l`. -/
def Dsum : List (ℤ × ℤ) → ℤ
  | [] => 0
  | x :: l => x.2 * x.2 * x.1 + 2 * x.2 * ((l.map (fun y => y.2 * max x.1 y.1)).sum) + Dsum l

@[simp] theorem Dsum_nil : Dsum [] = 0 := rfl
theorem Dsum_cons (x : ℤ × ℤ) (l : List (ℤ × ℤ)) :
    Dsum (x :: l) = x.2 * x.2 * x.1 + 2 * x.2 * ((l.map (fun y => y.2 * max x.1 y.1)).sum) + Dsum l :=
  rfl

/-- the same double sum indexed by `Fin l.length`. -/
def DsumFin (l : List (ℤ × ℤ)) : ℤ :=
  ∑ a : Fin l.length, ∑ b : Fin l.length,
    (l.get a).2 * (l.get b).2 * max (l.get a).1 (l.get b).1

/-- the dot product `Σ_i v_i w_i`. -/
def Vsum (l : List (ℤ × ℤ)) : ℤ := (l.map (fun x => x.1 * x.2)).sum

theorem Vsum_nil : Vsum [] = 0 := rfl
theorem Vsum_cons (x : ℤ × ℤ) (l : List (ℤ × ℤ)) :
    Vsum (x :: l) = x.1 * x.2 + Vsum l := by
  simp only [Vsum, List.map_cons, List.sum_cons]

/-! ## Copies of the certificate-sorting definitions of `Final` -/

/-- merge of two lists sorted by the first component (fuel = a bound on the total length). -/
def merge : Nat → List (ℤ × ℤ) → List (ℤ × ℤ) → List (ℤ × ℤ)
  | 0, xs, ys => xs ++ ys
  | _ + 1, [], ys => ys
  | _ + 1, xs, [] => xs
  | f + 1, x :: xs, y :: ys => if x.1 ≤ y.1 then x :: merge f xs (y :: ys) else y :: merge f (x :: xs) ys

/-- merge sort with explicit fuel (depth). -/
def msort : Nat → List (ℤ × ℤ) → List (ℤ × ℤ)
  | 0, xs => xs
  | f + 1, xs =>
      match xs with
      | [] => []
      | [x] => [x]
      | _ =>
        let n := xs.length / 2
        merge (xs.length + 1) (msort f (xs.take n)) (msort f (xs.drop n))

/-- `Σ_i v_i ((c_i)² - (c_{i-1})²)` over a list sorted by value, `c` = cumulative weight. -/
def sortedSum : List (ℤ × ℤ) → ℤ → ℤ → ℤ
  | [], _, acc => acc
  | (v, w) :: rest, c, acc => sortedSum rest (c + w) (acc + v * ((c + w) * (c + w) - c * c))

end Work.Cert.CJ2
