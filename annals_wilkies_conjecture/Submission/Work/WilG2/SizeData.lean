/-
  WilG2 : size data for compositions of `m`.

  A `SizeData m` is a number of parts together with positive sizes summing to `m`, the sizes being
  indexed by `Fin k` rather than by a list.  This is the same data as a `Composition m`, but the
  `Fin`-indexing removes the recurring `List.ofFn` casts from the main bijection
  (`Submission/Work/WilG2/Bijection.lean`).  The equivalence with `Composition m` is recorded here,
  together with the `Fintype` instance it induces.
-/
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Real.Basic

set_option autoImplicit false
noncomputable section

open Finset

namespace Work.WilG2

/-- Size data for a composition of `m`: a number `k` of parts and positive sizes on `Fin k`
summing to `m`. -/
@[reducible] def SizeData (m : ℕ) : Type :=
  {f : Σ k : ℕ, Fin k → ℕ // (∀ i, 0 < f.2 i) ∧ ∑ i, f.2 i = m}

namespace SizeData

variable {m : ℕ}

/-- The number of parts. -/
@[reducible] def len (x : SizeData m) : ℕ := x.1.1

/-- The sizes of the parts. -/
@[reducible] def sizes (x : SizeData m) : Fin (len x) → ℕ := x.1.2

lemma sizes_pos (x : SizeData m) (i : Fin (len x)) : 0 < sizes x i := x.2.1 i

lemma sizes_sum (x : SizeData m) : ∑ i, sizes x i = m := x.2.2

/-- The size datum with the given sizes. -/
@[reducible] def mk {k : ℕ} (s : Fin k → ℕ) (h : (∀ i, 0 < s i) ∧ ∑ i, s i = m) : SizeData m :=
  ⟨⟨k, s⟩, h⟩

@[simp] lemma len_mk {k : ℕ} (s : Fin k → ℕ) (h : (∀ i, 0 < s i) ∧ ∑ i, s i = m) :
    len (mk s h) = k := rfl

@[simp] lemma sizes_mk {k : ℕ} (s : Fin k → ℕ) (h : (∀ i, 0 < s i) ∧ ∑ i, s i = m) :
    sizes (mk s h) = s := rfl

/-- Two size data of the same length whose sizes agree are equal. -/
lemma eq_of_len_eq_of_sizes_eq {x y : SizeData m} (h : len x = len y)
    (hs : sizes x = sizes y ∘ Fin.cast h) : x = y :=
  Subtype.ext (Fin.sigma_eq_of_eq_comp_cast h hs)

/-- Two size data of the same length whose sizes agree pointwise are equal. -/
lemma eq_of_len_eq_of_sizes_eq' {x y : SizeData m} (h : len x = len y)
    (hs : ∀ i : Fin (len x), sizes x i = sizes y (Fin.cast h i)) : x = y :=
  eq_of_len_eq_of_sizes_eq h (funext hs)

/-- The unflattening of `Fin m` into the parts, according to the sizes. -/
def unflat (x : SizeData m) : Fin m ≃ (Σ i : Fin (len x), Fin (sizes x i)) :=
  (finSigmaFinEquiv.trans (Fin.castOrderIso x.sizes_sum).toEquiv).symm

lemma unflat_symm_apply (x : SizeData m) (j : Fin (len x)) (r : Fin (sizes x j)) :
    ((unflat x).symm ⟨j, r⟩ : ℕ) =
      (∑ i : Fin j.val, sizes x (Fin.castLE j.isLt.le i)) + (r : ℕ) := by
  rw [show unflat x = (finSigmaFinEquiv.trans (Fin.castOrderIso x.sizes_sum).toEquiv).symm from rfl,
    Equiv.symm_symm, Equiv.trans_apply]
  show ((finSigmaFinEquiv (⟨j, r⟩ : (i : Fin (len x)) × Fin (sizes x i))) : ℕ) = _
  rw [finSigmaFinEquiv_apply]

section Bridge

/-- The composition with the given sizes. -/
@[reducible] def toComposition (x : SizeData m) : Composition m where
  blocks := List.ofFn (sizes x)
  blocks_pos := by
    intro i hi
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hi
    exact x.sizes_pos j
  blocks_sum := by
    rw [List.sum_ofFn, x.sizes_sum]

/-- The size data of a composition. -/
@[reducible] def ofComposition (c : Composition m) : SizeData m :=
  mk c.blocksFun ⟨fun i => lt_of_lt_of_le Nat.zero_lt_one (c.one_le_blocksFun i),
    c.sum_blocksFun⟩

@[simp] lemma ofComposition_len (c : Composition m) : len (ofComposition c) = c.length := rfl

@[simp] lemma ofComposition_sizes (c : Composition m) :
    sizes (ofComposition c) = c.blocksFun := rfl

@[simp] lemma toComposition_length (x : SizeData m) :
    (toComposition x).length = len x := List.length_ofFn

lemma toComposition_blocksFun (x : SizeData m) (i : Fin (toComposition x).length) :
    (toComposition x).blocksFun i = sizes x (Fin.cast (toComposition_length x) i) := by
  show (List.ofFn (sizes x)).get i = sizes x (Fin.cast (List.length_ofFn) i)
  rw [List.get_ofFn]

lemma bridge_left (c : Composition m) : toComposition (ofComposition c) = c := by
  apply Composition.ext
  show List.ofFn c.blocksFun = c.blocks
  exact Composition.ofFn_blocksFun c

lemma bridge_right (x : SizeData m) : ofComposition (toComposition x) = x := by
  refine eq_of_len_eq_of_sizes_eq (by rw [ofComposition_len, toComposition_length]) ?_
  funext i
  rw [ofComposition_sizes]
  exact toComposition_blocksFun x i

lemma castOrderIso_toEquiv_apply {n m : ℕ} (h : n = m) (i : Fin n) :
    (((Fin.castOrderIso h).toEquiv : Fin n → Fin m)) i = Fin.cast h i := rfl

/-- Multiplication of part weights only depends on the sizes, which we may transport along the
equivalence with compositions. -/
lemma prod_toComposition_blocksFun (a : ℕ → ℝ) (x : SizeData m) :
    ∏ i : Fin (toComposition x).length, a ((toComposition x).blocksFun i) =
      ∏ i : Fin (len x), a (sizes x i) := by
  refine Fintype.prod_equiv (Fin.castOrderIso (toComposition_length x)).toEquiv _ _ fun i => ?_
  rw [toComposition_blocksFun]
  exact congrArg (fun j => a (sizes x j))
    (castOrderIso_toEquiv_apply (toComposition_length x) i).symm

end Bridge

end SizeData

/-- Size data is the same as compositions. -/
def sizeDataEquiv (m : ℕ) : SizeData m ≃ Composition m where
  toFun := SizeData.toComposition
  invFun := SizeData.ofComposition
  left_inv := SizeData.bridge_right
  right_inv := SizeData.bridge_left

instance instFintypeSizeData (m : ℕ) : Fintype (SizeData m) :=
  Fintype.ofEquiv (Composition m) (sizeDataEquiv m).symm

end Work.WilG2
