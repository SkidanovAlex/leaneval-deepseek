import Mathlib
import Submission.Work.WilkiesH.Defs

/-!
# Hockey-stick recursion for the number of monomials of bounded degree

`monoCount (n+1) d = ∑_{j ≤ d} monoCount n j`: the number of monomials of total degree `≤ d`
in `n+1` variables equals the number of monomials of total degree `≤ j` in `n` variables,
summed over `j ≤ d`.

Bijectively, an exponent vector `(a_0, …, a_n)` of total degree `a_0 + … + a_n ≤ d` is split
into its last coordinate `a_n` and its initial part `(a_0, …, a_{n-1})`, which has total degree
`a_0 + … + a_{n-1} ≤ d - a_n`.  The construction is a composition of explicit bijections:

* `splitEquiv` : `ExpVec (n+1) d ≃ ExpVecSplit n d` — split off the last coordinate;
* `splitSigmaEquiv` : `ExpVecSplit n d ≃ Σ i : Fin (d+1), ExpVecFibre n d i` — pass to the
  fibre over the value `i` of the last coordinate;
* `fibreEquiv` : `ExpVecFibre n d i ≃ ExpVec n (d - i)` — shrink the codomain of the initial
  part;
* `Finset.sum_range_reflect` — the substitution `i ↦ d - i` on `{0, …, d}`.
-/

namespace Work.WilkiesH.Interp.V2count

open Work.WilkiesH

variable {n d : ℕ}

/-- Append a last coordinate to a function `Fin n → Fin (d+1)`, producing a function on
`Fin (n+1)`.  (This is `Fin.snoc` with the type family made explicit.) -/
def snocLast {n d : ℕ} (f : Fin n → Fin (d + 1)) (c : Fin (d + 1)) :
    Fin (n + 1) → Fin (d + 1) :=
  @Fin.snoc n (fun _ => Fin (d + 1)) f c

@[simp] lemma snocLast_castSucc {n d : ℕ} (f : Fin n → Fin (d + 1)) (c : Fin (d + 1))
    (k : Fin n) : snocLast f c (Fin.castSucc k) = f k :=
  Fin.snoc_castSucc (α := fun _ => Fin (d + 1)) c f k

@[simp] lemma snocLast_last {n d : ℕ} (f : Fin n → Fin (d + 1)) (c : Fin (d + 1)) :
    snocLast f c (Fin.last n) = c :=
  Fin.snoc_last (α := fun _ => Fin (d + 1)) c f

/-- Sum of the first `n` coordinates of an exponent vector in `n + 1` variables. -/
def initSum (α : ExpVec (n + 1) d) : ℕ := ∑ k : Fin n, ExpVec.toFun α (Fin.castSucc k)

/-- The last coordinate of an exponent vector in `n + 1` variables. -/
def lastCoord (α : ExpVec (n + 1) d) : ℕ := ExpVec.toFun α (Fin.last n)

lemma lastCoord_le (α : ExpVec (n + 1) d) : lastCoord α ≤ d := ExpVec.toFun_le α (Fin.last n)

lemma initSum_add_lastCoord_le (α : ExpVec (n + 1) d) : initSum α + lastCoord α ≤ d := by
  have h := α.prop
  rw [Fin.sum_univ_castSucc (f := fun i : Fin (n + 1) => (α.val i : ℕ))] at h
  simpa [initSum, lastCoord, ExpVec.toFun] using h

/-- Exponent vectors of total degree `≤ d` in `n + 1` variables, encoded as the pair
(initial `n` coordinates, last coordinate) satisfying the degree constraint. -/
abbrev ExpVecSplit (n d : ℕ) : Type :=
  {y : (Fin n → Fin (d + 1)) × Fin (d + 1) // (∑ k, (y.1 k : ℕ)) + (y.2 : ℕ) ≤ d}

/-- Split off the last coordinate of an exponent vector. -/
def splitFwd (α : ExpVec (n + 1) d) : ExpVecSplit n d :=
  ⟨(fun k => α.val (Fin.castSucc k), ⟨lastCoord α, Nat.lt_succ_of_le (lastCoord_le α)⟩),
   by simpa [initSum, lastCoord, ExpVec.toFun] using initSum_add_lastCoord_le α⟩

lemma sum_snoc_le (f : Fin n → Fin (d + 1)) (c : Fin (d + 1))
    (h : (∑ k, (f k : ℕ)) + (c : ℕ) ≤ d) :
    (∑ i : Fin (n + 1), ((snocLast f c i : Fin (d + 1)) : ℕ)) ≤ d := by
  rw [Fin.sum_univ_castSucc
    (f := fun i : Fin (n + 1) => ((snocLast f c i : Fin (d + 1)) : ℕ))]
  simp only [snocLast_castSucc, snocLast_last]
  exact h

/-- Reassemble an exponent vector in `n + 1` variables from the pair
(initial part, last coordinate). -/
def splitBack (y : ExpVecSplit n d) : ExpVec (n + 1) d :=
  ⟨snocLast (y.val).1 (y.val).2, sum_snoc_le (y.val).1 (y.val).2 y.property⟩

@[simp] lemma splitFwd_val (α : ExpVec (n + 1) d) :
    (splitFwd α).val
      = (fun k => α.val (Fin.castSucc k), ⟨lastCoord α, Nat.lt_succ_of_le (lastCoord_le α)⟩) :=
  rfl

@[simp] lemma splitBack_val (y : ExpVecSplit n d) :
    (splitBack y).val = snocLast (y.val).1 (y.val).2 := rfl

lemma splitBack_splitFwd (α : ExpVec (n + 1) d) : splitBack (splitFwd α) = α := by
  apply Subtype.ext
  rw [splitBack_val]
  simp only [splitFwd]
  funext i
  refine Fin.lastCases ?_ ?_ i
  · rw [snocLast_last]
    apply Fin.ext
    simp only [lastCoord, ExpVec.toFun]
  · intro k
    simp only [snocLast_castSucc]

lemma splitFwd_splitBack (y : ExpVecSplit n d) : splitFwd (splitBack y) = y := by
  obtain ⟨⟨f, c⟩, h⟩ := y
  apply Subtype.ext
  simp only [splitFwd, splitBack]
  refine Prod.ext ?_ ?_
  · funext k
    simp only [snocLast_castSucc]
  · apply Fin.ext
    simp only [lastCoord, ExpVec.toFun, snocLast_last]

/-- The bijection between exponent vectors in `n + 1` variables and the pair
(initial part, last coordinate). -/
def splitEquiv (n d : ℕ) : ExpVec (n + 1) d ≃ ExpVecSplit n d :=
  ⟨splitFwd, splitBack, fun α => splitBack_splitFwd α, fun y => splitFwd_splitBack y⟩

/-- The fibre of `ExpVecSplit` over the value `i` of the last coordinate. -/
abbrev ExpVecFibre (n d : ℕ) (i : Fin (d + 1)) : Type :=
  {f : Fin n → Fin (d + 1) // (∑ k, (f k : ℕ)) + (i : ℕ) ≤ d}

/-- `ExpVecSplit` as the sigma type of its fibres over the last coordinate. -/
def splitSigmaEquiv (n d : ℕ) : ExpVecSplit n d ≃ (Σ i : Fin (d + 1), ExpVecFibre n d i) :=
  ⟨fun y => ⟨(y.val).2, ⟨(y.val).1, y.property⟩⟩,
   fun z => by obtain ⟨i, ⟨f, h⟩⟩ := z; exact ⟨(f, i), h⟩,
   fun y => by obtain ⟨⟨f, c⟩, h⟩ := y; rfl,
   fun z => by obtain ⟨i, ⟨f, h⟩⟩ := z; rfl⟩

lemma fibre_coord_le (i : Fin (d + 1)) {f : Fin n → Fin (d + 1)}
    (h : (∑ k, (f k : ℕ)) + (i : ℕ) ≤ d) (k : Fin n) : (f k : ℕ) ≤ d - (i : ℕ) := by
  have h1 : (f k : ℕ) ≤ ∑ k, (f k : ℕ) :=
    Finset.single_le_sum (f := fun k : Fin n => (f k : ℕ)) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ k)
  omega

lemma fibre_sum_le (i : Fin (d + 1)) {f : Fin n → Fin (d + 1)}
    (h : (∑ k, (f k : ℕ)) + (i : ℕ) ≤ d) : (∑ k, (f k : ℕ)) ≤ d - (i : ℕ) := by
  omega

lemma fibre_sum_le' (i : Fin (d + 1)) {f : Fin n → Fin (d - (i : ℕ) + 1)}
    (h : (∑ k, (f k : ℕ)) ≤ d - (i : ℕ)) : (∑ k, (f k : ℕ)) + (i : ℕ) ≤ d := by
  have hi : (i : ℕ) ≤ d := Nat.le_of_lt_succ i.isLt
  omega

/-- The fibre over the last coordinate `i` consists of the exponent vectors of total degree
`≤ d - i` in `n` variables. -/
def fibreEquiv (n d : ℕ) (i : Fin (d + 1)) : ExpVecFibre n d i ≃ ExpVec n (d - (i : ℕ)) :=
  ⟨fun f => ⟨fun k => ⟨(f.val k : ℕ), Nat.lt_succ_of_le (fibre_coord_le i f.property k)⟩,
      fibre_sum_le i f.property⟩,
   fun g => ⟨fun k => ⟨(g.val k : ℕ),
       Nat.lt_succ_of_le (le_trans (ExpVec.toFun_le g k) (Nat.sub_le d (i : ℕ)))⟩,
     fibre_sum_le' i g.property⟩,
   fun f => by
     apply Subtype.ext
     funext k
     apply Fin.ext
     rfl,
   fun g => by
     apply Subtype.ext
     funext k
     apply Fin.ext
     rfl⟩

theorem card_ExpVec_succ (n d : ℕ) :
    Fintype.card (Work.WilkiesH.ExpVec (n + 1) d) =
      ∑ j ∈ Finset.range (d + 1), Fintype.card (Work.WilkiesH.ExpVec n j) := by
  rw [Fintype.card_congr (splitEquiv n d), Fintype.card_congr (splitSigmaEquiv n d),
    Fintype.card_sigma]
  have hsum : (∑ i : Fin (d + 1), Fintype.card (ExpVecFibre n d i))
      = ∑ i : Fin (d + 1), Fintype.card (ExpVec n (d - (i : ℕ))) :=
    Finset.sum_congr rfl fun i _ => Fintype.card_congr (fibreEquiv n d i)
  rw [hsum, Fin.sum_univ_eq_sum_range (fun j => Fintype.card (ExpVec n (d - j))) (d + 1)]
  rw [← Finset.sum_range_reflect (fun j => Fintype.card (ExpVec n j)) (d + 1)]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j < d + 1 := Finset.mem_range.mp hj
  exact Fintype.card_congr
    (Equiv.cast (congrArg (fun m => ExpVec n m) (by omega : d - j = (d + 1) - 1 - j)))

end Work.WilkiesH.Interp.V2count
