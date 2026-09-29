import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Resample.pbDefs
import Submission.Work.Resample.fx
import Submission.Work.Resample.fxTensorErr

/-!
# Axis bridges: shared definitions

This file collects the definitions and elementary lemmas used by
`Submission/Work/Resample/axisBridge.lean` (and by the lemmas about it), which connect the
*list-level* axis application `axisPairs`/`progAxis` (the `slices`/`unslices` layout of
`LayoutLib.applyAlong`) with the *fixed-point level* iteration `fxTensorRec`.

The one-dimensional axis maps given by `Φ : (i : ℕ) → ...` are indexed by natural numbers; the
dimensions `m i` (`ts.getD i 0`) and `n i` (`ss.getD i 0`) are handled as *functions* `ℕ → ℕ`,
so that shifting the family by one axis (`fun i => Φ (i+1)`) has the same type as the family of
the tail dimensions (`fun i => m (i+1)`), definitionally.

* `axisOp` — one axis application at the level of an abstract index function `ℕ → ℤ × ℤ`.
* `axisPairs_ofFn` — `axisPairs` on `List.ofFn` is `List.ofFn` of `axisOp`.
* `chainP D m n Φ A` — the axes `0, …, D-1` applied in increasing order (as `progAxis` does).
* `chainS D m n Φ A` — the same composition, peeling the *first* axis (as `fxTensorRec` does).
* `fxFlat A ss ts Φ` — the `A`-blocked fixed-point iteration: block `a` of the output is
  `fxTensorRec ts ss Φ` applied to block `a` of the input.
-/

set_option autoImplicit false

namespace Work.Resample

open HvdH

/-! ## Elementary list lemmas -/

/-- `List.range`-maps are `List.ofFn`. -/
lemma range_map_eq_ofFn {α : Type} (n : ℕ) (f : ℕ → α) :
    (List.range n).map f = List.ofFn (fun i : Fin n => f i) := by
  induction n with
  | zero => simp
  | succ k ih => rw [List.range_succ, List.map_append, ih, List.ofFn_succ']; simp

/-- `getD` of `List.ofFn` at an in-range index. -/
lemma ofFn_getD {n : ℕ} (ψ : Fin n → ℤ × ℤ) {i : ℕ} (h : i < n) :
    (List.ofFn ψ).getD i (0,0) = ψ ⟨i,h⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_ofFn]

/-- `List.ofFn` does not depend on the (provably equal) index type. -/
lemma ofFn_assoc {α : Type} (A t N : ℕ) (φ : ℕ → α) :
    List.ofFn (fun i : Fin (A * (t*N)) => φ i) = List.ofFn (fun i : Fin (A*t*N) => φ i) := by
  apply List.ext_getElem
  · simp [Nat.mul_assoc]
  · intro i h1 h2
    simp only [List.getElem_ofFn]

/-- `List.ofFn` agrees with its `zget`-clamped version. -/
lemma ofFn_zget {n : ℕ} (u : Fin n → ℤ × ℤ) :
    List.ofFn u = List.ofFn (fun i : Fin n => zget u i) := by
  apply List.ofFn_inj.mpr
  funext i
  exact (fxTE_zget_of_lt u i.isLt).symm

/-- `zget` of a `List.ofFn` is `getD`. -/
lemma zget_ofFn_eq_getD {n : ℕ} (u : Fin n → ℤ × ℤ) (i : ℕ) :
    zget u i = (List.ofFn u).getD i (0,0) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp only [zget]
  split <;> rfl

/-- The product of a prefix of a list is the product of the corresponding `getD` values. -/
lemma prod_take_range_getD (l : List ℕ) {i : ℕ} (hi : i ≤ l.length) :
    (l.take i).prod = ((List.range i).map (fun k => l.getD k 0)).prod := by
  induction i with
  | zero => simp
  | succ k ih =>
    have hk : k < l.length := by omega
    rw [← List.take_concat_get' l k hk, List.prod_append, ih (by omega), List.range_succ,
      List.map_append, List.prod_append]
    simp only [List.prod_cons, List.prod_nil, mul_one, List.map_cons, List.map_nil]
    rw [List.getD_eq_getElem l 0 hk]

/-- The product of a list is the product of its `getD` values. -/
lemma prod_range_getD (l : List ℕ) :
    l.prod = ((List.range l.length).map (fun k => l.getD k 0)).prod := by
  have := prod_take_range_getD l (le_refl l.length)
  simpa using this

/-- The `getD` values of the suffix of a list are the suffix of the list. -/
lemma map_drop_range_getD (l : List ℕ) {i : ℕ} (hi : i ≤ l.length) :
    ((List.range l.length).drop i).map (fun k => l.getD k 0) = l.drop i := by
  apply List.ext_getElem
  · simp [List.length_drop]
  · intro k h1 h2
    have hk : i + k < l.length := by simp only [List.length_drop] at h2; omega
    have hlen : k < ((List.range l.length).drop i).length := by
      simp only [List.length_drop, List.length_range]; omega
    rw [List.getElem_map, List.getElem_drop (h := hlen), List.getElem_range,
      List.getElem_drop (h := h2), List.getD_eq_getElem l 0 hk]

/-- The product of a suffix of a list is the product of the corresponding `getD` values. -/
lemma prod_drop_range_getD (l : List ℕ) {i : ℕ} (hi : i ≤ l.length) :
    (l.drop i).prod = (((List.range l.length).drop i).map (fun k => l.getD k 0)).prod := by
  rw [map_drop_range_getD l hi]

/-! ## One axis application at the index level -/

/-- Apply the one-dimensional map `Φ` along one axis, at the level of index functions.
With `zs = List.ofFn φ`, this is the value at index `idx` of `axisPairs A m n B Φ zs`. -/
noncomputable def axisOp (A m n B : ℕ) (Φ : (Fin m → ℤ × ℤ) → (Fin n → ℤ × ℤ))
    (φ : ℕ → ℤ × ℤ) : ℕ → ℤ × ℤ :=
  fun idx => if h : 0 < n then
    Φ (fun j : Fin m => φ ((idx / (n*B) * m + (j:ℕ)) * B + idx % B))
      ⟨idx / B % n, Nat.mod_lt _ h⟩
  else (0,0)

/-- The index bound guaranteeing that all reads of `axisPairs` are in range. -/
lemma idxbound {A m n B : ℕ} (hn : 0 < n) (hB : 0 < B) (i : ℕ) (hi : i < A * n * B)
    (j : ℕ) (hj : j < m) :
    (i / (n * B) * m + j) * B + i % B < A * m * B := by
  have hr : i % B < B := Nat.mod_lt _ hB
  have hnB : 0 < n * B := Nat.mul_pos hn hB
  have h1 : i / (n * B) < A := (Nat.div_lt_iff_lt_mul hnB).mpr (by rwa [Nat.mul_assoc] at hi)
  have h2 : (i / (n * B) * m + j) < A * m := by
    have h3 : i / (n * B) * m + j < i / (n * B) * m + m := Nat.add_lt_add_left hj _
    have h4 : i / (n * B) * m + m = (i / (n * B) + 1) * m := by ring
    have h5 : (i / (n * B) + 1) * m ≤ A * m :=
      Nat.mul_le_mul_right m (Nat.succ_le_of_lt h1)
    omega
  have h6 : (i / (n * B) * m + j) * B + i % B < (i / (n * B) * m + j) * B + B :=
    Nat.add_lt_add_left hr _
  have h7 : (i / (n * B) * m + j) * B + B ≤ A * m * B := by
    have h8 : (i / (n * B) * m + j + 1) * B ≤ A * m * B :=
      Nat.mul_le_mul_right B (Nat.succ_le_of_lt h2)
    calc (i / (n * B) * m + j) * B + B = (i / (n * B) * m + j + 1) * B := by ring
      _ ≤ A * m * B := h8
  omega

/-- `axisPairs` on a `List.ofFn` is a `List.ofFn`. -/
lemma axisPairs_ofFn {A m n B : ℕ} (hn : 0 < n) (hB : 0 < B)
    (Φ : (Fin m → ℤ × ℤ) → (Fin n → ℤ × ℤ)) (φ : ℕ → ℤ × ℤ) :
    axisPairs A m n B Φ (List.ofFn (fun i : Fin (A*m*B) => φ i)) =
      List.ofFn (fun idx : Fin (A*n*B) => axisOp A m n B Φ φ idx) := by
  simp only [axisPairs]
  rw [range_map_eq_ofFn]
  rw [List.ofFn_inj]
  funext idx
  have hfun : (fun j : Fin m =>
        sliceIn m B (List.ofFn (fun i : Fin (A*m*B) => φ i))
          (↑idx / (n*B) * B + ↑idx % B) ↑j)
      = (fun j : Fin m => φ ((↑idx / (n*B) * m + ↑j) * B + ↑idx % B)) := by
    funext j
    simp only [sliceIn]
    have hdiv : (↑idx / (n*B) * B + ↑idx % B) / B = ↑idx / (n*B) := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hB, Nat.div_eq_of_lt (Nat.mod_lt _ hB),
        Nat.zero_add]
    have hmod : (↑idx / (n*B) * B + ↑idx % B) % B = ↑idx % B := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (Nat.mod_lt _ hB)]
    rw [hdiv, hmod, ofFn_getD _ (idxbound hn hB _ idx.isLt _ j.isLt)]
  rw [hfun, axisOp, dite_eq_left hn,
    List.getD_eq_getElem _ _ (by simpa using Nat.mod_lt (↑idx / B % n) hn), List.getElem_ofFn]

/-! ## The iterated axis application -/

/-- The axes `0, …, D-1`, applied in increasing order to a list seen as `A` blocks of size
`m 0 * … * m (D-1)`.  Axis `i` has outer product `A * n 0 * … * n (i-1)` and inner product
`m (i+1) * … * m (D-1)`. -/
noncomputable def chainP (D : ℕ) (m n : ℕ → ℕ)
    (Φ : (i : ℕ) → (Fin (m i) → ℤ × ℤ) → (Fin (n i) → ℤ × ℤ))
    (A : ℕ) : ℕ → List (ℤ × ℤ) → List (ℤ × ℤ)
  | 0, zs => zs
  | (i + 1), zs => axisPairs (A * ((List.range i).map n).prod) (m i) (n i)
      (((List.range D).drop (i + 1)).map m).prod (Φ i) (chainP D m n Φ A i zs)

/-- The same composition, peeling the first axis: apply axis `0` and then the composition for the
tail dimensions with outer product `A * n 0`, exactly as `fxTensorRec` recurses. -/
noncomputable def chainS : (D : ℕ) → (m n : ℕ → ℕ) →
    ((i : ℕ) → (Fin (m i) → ℤ × ℤ) → (Fin (n i) → ℤ × ℤ)) →
    ℕ → List (ℤ × ℤ) → List (ℤ × ℤ)
  | 0, _, _, _, _, zs => zs
  | (D+1), m, n, Φ, A, zs => chainS D (fun k => m (k+1)) (fun k => n (k+1))
      (fun k => Φ (k+1)) (A * n 0)
      (axisPairs A (m 0) (n 0) (((List.range D).map (fun k => m (k+1))).prod) (Φ 0) zs)

/-! ## The blocked fixed-point iteration -/

/-- Shifting a family of axis maps by one axis, with the tail dimensions. -/
noncomputable def famShift {t s : ℕ} {ts' ss' : List ℕ}
    (Φ : (i : ℕ) → (Fin ((t :: ts').getD i 0) → ℤ × ℤ) → (Fin ((s :: ss').getD i 0) → ℤ × ℤ)) :
    (i : ℕ) → (Fin (ts'.getD i 0) → ℤ × ℤ) → (Fin (ss'.getD i 0) → ℤ × ℤ) :=
  fun i => Φ (i+1)

/-- The tail of the `famShift` family. -/
lemma famShift_zero {t s : ℕ} {ts' ss' : List ℕ}
    (Φ : (i : ℕ) → (Fin ((t :: ts').getD i 0) → ℤ × ℤ) → (Fin ((s :: ss').getD i 0) → ℤ × ℤ)) :
    famShift Φ 0 = Φ 1 := rfl

/-- `fxTensorRec ts ss Φ` applied blockwise: the flat array of `A` consecutive blocks of size
`ts.prod` is mapped to `A` blocks of size `ss.prod`. -/
noncomputable def fxFlat (A : ℕ) (ss ts : List ℕ)
    (Φ : (i : ℕ) → (Fin (ts.getD i 0) → ℤ × ℤ) → (Fin (ss.getD i 0) → ℤ × ℤ))
    (u : Fin (A * ts.prod) → ℤ × ℤ) : Fin (A * ss.prod) → ℤ × ℤ :=
  fun i => if h : 0 < ss.prod then
    fxTensorRec ts ss Φ
      (fun l : Fin ts.prod => zget u ((i:ℕ) / ss.prod * ts.prod + (l:ℕ)))
      ⟨(i:ℕ) % ss.prod, Nat.mod_lt _ h⟩
  else (0,0)

/-- `fxTensorRec` on a cons, with the tail family written as `famShift`. -/
theorem fxTensorRec_cons {s t : ℕ} {ss' ts' : List ℕ}
    (Φ : (i : ℕ) → (Fin ((t :: ts').getD i 0) → ℤ × ℤ) → (Fin ((s :: ss').getD i 0) → ℤ × ℤ))
    (u : Fin ((t :: ts').prod) → ℤ × ℤ) :
    fxTensorRec (t :: ts') (s :: ss') Φ u =
      fxBlockwise s (ts'.prod) (ss'.prod) (fxTensorRec ts' ss' (famShift Φ))
        (axisFx1Gen t s (ts'.prod) (Φ 0) u) := rfl

end Work.Resample
