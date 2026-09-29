import Mathlib
import Submission.Work.Resample.tensorAux
import Submission.Work.Resample.fx
import Submission.Work.Resample.axisDefs

/-!
# Blocks of flat arrays, and the axis iteration with an outer product

This file collects the definitions and elementary lemmas used to compare the list-level axis
iteration `Work.Resample.axisIter` (which applies the one-dimensional maps with the
`slices`/`unslices` layout of `HvdH.LayoutLib.applyAlong`, peeling the *last* axis) with the
`Fin`-indexed fixed-point iteration `Work.Resample.fxTensorRec` (which peels the *first* axis).

* `blk M g zs` — the `g`-th block of size `M` of the list `zs`, padded with `(0,0)`;
* `famShift' Φ` — the tail family `i ↦ Φ (i+1)`;
* `axisIterA A ss ts Φ k` — `axisIter` with an extra outer product `A`, i.e. the iteration on
  flat arrays of length `A * (ss.take k).prod * (ss.drop k).prod`;
* `axisIterA_tail` — the reassociation that lets the first pass be peeled off;
* `fxBlk A ss ts Φ u` — `fxTensorRec ss ts Φ` applied blockwise: the flat array of `A`
  consecutive blocks of size `ss.prod` is mapped to `A` blocks of size `ts.prod`.
-/

set_option autoImplicit false

namespace Work.Resample

open HvdH

/-! ## Blocks -/

lemma default_prod_int : (default : ℤ × ℤ) = (0, 0) := rfl

/-- The `g`-th block of size `M` of the list `zs` (read with `getD`, hence padded by `(0,0)`). -/
def blk (M g : ℕ) (zs : List (ℤ × ℤ)) : List (ℤ × ℤ) :=
  List.ofFn (fun x : Fin M => zs.getD (g * M + (x : ℕ)) (0, 0))

@[simp] lemma blk_length (M g : ℕ) (zs : List (ℤ × ℤ)) : (blk M g zs).length = M := by
  simp [blk]

lemma blk_getD (M g x : ℕ) (zs : List (ℤ × ℤ)) (hx : x < M) :
    (blk M g zs).getD x (0,0) = zs.getD (g * M + x) (0,0) := by
  change (List.ofFn (fun y : Fin M => zs.getD (g * M + (y : ℕ)) (0,0))).getD x (0,0)
      = zs.getD (g * M + x) (0,0)
  rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hx), List.getElem_ofFn]

/-- A list reads back from its own `getD` values. -/
lemma ofFn_getD_self (l : List (ℤ × ℤ)) :
    List.ofFn (fun i : Fin l.length => l.getD (i : ℕ) (0,0)) = l := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    rw [List.getElem_ofFn]
    exact List.getD_eq_getElem l 0 h2

/-- A list of length `N` reads back from its own `getD` values. -/
lemma ofFn_getD_of_length (l : List (ℤ × ℤ)) (N : ℕ) (h : l.length = N) :
    List.ofFn (fun i : Fin N => l.getD (i : ℕ) (0,0)) = l := by
  subst h
  exact ofFn_getD_self l

/-- `List.ofFn` does not see the (provably equal) shape of the index bound proofs. -/
lemma ofFn_eq_of_assoc {α : Type} {N M : ℕ} (hNM : N = M)
    (f : (i : ℕ) → i < N → α) (g : (i : ℕ) → i < M → α)
    (hf : ∀ i (hN : i < N) (hM : i < M), f i hN = g i hM) :
    List.ofFn (fun i : Fin N => f i i.isLt) = List.ofFn (fun i : Fin M => g i i.isLt) := by
  apply List.ext_getElem
  · simp [hNM]
  · intro i h1 h2
    rw [List.getElem_ofFn, List.getElem_ofFn]
    exact hf i _ _

/-- A block reads back to the list it came from. -/
lemma map_range_getD_eq_self (M : ℕ) (l : List (ℤ × ℤ)) (h : l.length = M) :
    (List.range M).map (fun x => l.getD x (0,0)) = l := by
  subst h
  rw [range_map_eq_ofFn l.length (fun x => l.getD x (0,0))]
  exact ofFn_getD_self l

/-! ## Splitting `List.range` into blocks -/

lemma range_map_flatMap_blocks (t M : ℕ) (F : ℕ → ℤ × ℤ) :
    (List.range (t * M)).map F
      = (List.range t).flatMap (fun g => (List.range M).map (fun x => F (g * M + x))) := by
  induction t with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, List.range_add, List.map_append, ih, List.range_succ, List.flatMap_append,
      List.flatMap_cons, List.flatMap_nil, List.append_nil]
    congr 1
    rw [List.map_map]
    rfl

/-- Two block-wise equal families of blocks have the same flattening. -/
lemma flatMap_congr_range {t : ℕ} {f g : ℕ → List (ℤ × ℤ)} (h : ∀ x < t, f x = g x) :
    (List.range t).flatMap f = (List.range t).flatMap g := by
  induction t with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, ih (fun x hx => h x (by omega)), h k (by omega)]

/-- The flattening of a family of blocks of size `M` is the `map` over `range (t*M)` that
re-splits the index. -/
lemma flatMap_range_eq_map (t M : ℕ) (f : ℕ → List (ℤ × ℤ)) (hf : ∀ g < t, (f g).length = M) :
    (List.range t).flatMap f
      = (List.range (t * M)).map (fun i => (f (i / M)).getD (i % M) (0,0)) := by
  induction t with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, ih (fun g hg => hf g (by omega)), Nat.succ_mul, List.range_add]
    rw [List.map_append, List.map_map, ← map_range_getD_eq_self M (f k) (hf k (by omega))]
    congr 1
    apply List.map_congr_left
    intro x hx
    simp only [Function.comp_apply]
    have hx' : x < M := List.mem_range.mp hx
    have hM : 0 < M := Nat.lt_of_le_of_lt (Nat.zero_le x) hx'
    rw [Nat.mul_comm k M, Nat.mul_add_div hM, Nat.div_eq_of_lt hx', Nat.add_zero,
      Nat.mul_add_mod, Nat.mod_eq_of_lt hx']

/-- Reading the `(g,x)`-entry of a concatenation of blocks of size `M`. -/
lemma flatMap_getD (t M : ℕ) (f : ℕ → List (ℤ × ℤ)) (hf : ∀ g < t, (f g).length = M)
    (g x : ℕ) (hg : g < t) (hx : x < M) :
    ((List.range t).flatMap f).getD (g * M + x) (0,0) = (f g).getD x (0,0) := by
  have hM : 0 < M := Nat.lt_of_le_of_lt (Nat.zero_le x) hx
  have h2 : g * M + x < t * M := by
    have h3 : g * M + x < (g + 1) * M := by rw [Nat.add_mul]; simp; omega
    exact lt_of_lt_of_le h3 (Nat.mul_le_mul_right M (Nat.succ_le_of_lt hg))
  rw [flatMap_range_eq_map t M f hf, List.getD_eq_getElem _ _ (by simpa using h2),
    List.getElem_map, List.getElem_range, Nat.mul_comm g M, Nat.mul_add_div hM,
    Nat.div_eq_of_lt hx, Nat.add_zero, Nat.mul_add_mod, Nat.mod_eq_of_lt hx]

/-! ## Index bounds -/

lemma mul_add_lt_mul {m B i j : ℕ} (hj : j < m) (hi : i < B) : j * B + i < m * B := by
  have h1 : j * B + i < j * B + B := Nat.add_lt_add_left hi _
  rw [← Nat.succ_mul] at h1
  exact lt_of_lt_of_le h1 (Nat.mul_le_mul_right B (Nat.succ_le_of_lt hj))

/-! ## The iteration with an outer product -/

/-- The family of slice maps shifted by one axis. -/
def famShift' {s t : ℕ} {ss' ts' : List ℕ}
    (Φ : (i : ℕ) → (Fin ((s :: ss').getD i 0) → ℤ × ℤ) → (Fin ((t :: ts').getD i 0) → ℤ × ℤ)) :
    (i : ℕ) → (Fin (ss'.getD i 0) → ℤ × ℤ) → (Fin (ts'.getD i 0) → ℤ × ℤ) :=
  fun i => Φ (i+1)

lemma famShift'_zero {s t : ℕ} {ss' ts' : List ℕ}
    (Φ : (i : ℕ) → (Fin ((s :: ss').getD i 0) → ℤ × ℤ) → (Fin ((t :: ts').getD i 0) → ℤ × ℤ)) :
    famShift' Φ 0 = Φ 1 := rfl

/-- `axisIterA A ss ts Φ k zs` is `axisIter` on flat arrays with an extra outer product `A`:
after `k` steps the array has length `A * (ts.take k).prod * (ss.drop k).prod`. -/
noncomputable def axisIterA (A : ℕ) (ss ts : List ℕ)
    (Φ : (i : ℕ) → (Fin (ss.getD i 0) → ℤ × ℤ) → (Fin (ts.getD i 0) → ℤ × ℤ)) :
    ℕ → List (ℤ × ℤ) → List (ℤ × ℤ)
  | 0, es => es
  | k + 1, es => axisList (A * (ts.take k).prod) (ss.getD k 0) (ts.getD k 0)
      ((ss.drop (k + 1)).prod) (Φ k) (axisIterA A ss ts Φ k es)

lemma axisIterA_zero (A : ℕ) (ss ts : List ℕ) (Φ) (es : List (ℤ × ℤ)) :
    axisIterA A ss ts Φ 0 es = es := rfl

lemma axisIterA_succ (A : ℕ) (ss ts : List ℕ)
    (Φ : (i : ℕ) → (Fin (ss.getD i 0) → ℤ × ℤ) → (Fin (ts.getD i 0) → ℤ × ℤ)) (k : ℕ)
    (es : List (ℤ × ℤ)) :
    axisIterA A ss ts Φ (k+1) es = axisList (A * (ts.take k).prod) (ss.getD k 0) (ts.getD k 0)
      ((ss.drop (k + 1)).prod) (Φ k) (axisIterA A ss ts Φ k es) := rfl

/-- `axisIter` is the `A = 1` case of `axisIterA`. -/
lemma axisIter_eq_axisIterA_one (ss ts : List ℕ)
    (Φ : (i : ℕ) → (Fin (ss.getD i 0) → ℤ × ℤ) → (Fin (ts.getD i 0) → ℤ × ℤ)) (k : ℕ)
    (es : List (ℤ × ℤ)) : axisIter ss ts Φ k es = axisIterA 1 ss ts Φ k es := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [axisIter, axisIterA, ih, Nat.one_mul]

/-- **The first pass can be peeled off**: the `k+1`-fold iteration on the axes `0, …, k` is the
`k`-fold iteration on the axes `1, …, k` (with outer product `A * t`), applied to the result of
the single pass on axis `0`. -/
lemma axisIterA_tail (A s t : ℕ) (ss' ts' : List ℕ)
    (Φ : (i : ℕ) → (Fin ((s::ss').getD i 0) → ℤ × ℤ) → (Fin ((t::ts').getD i 0) → ℤ × ℤ)) :
    ∀ (k : ℕ) (zs : List (ℤ × ℤ)),
      axisIterA A (s::ss') (t::ts') Φ (k+1) zs
        = axisIterA (A*t) ss' ts' (famShift' Φ) k
            (axisIterA A (s::ss') (t::ts') Φ 1 zs) := by
  intro k
  induction k with
  | zero => intro zs; rfl
  | succ k ih =>
    intro zs
    rw [axisIterA_succ, ih zs]
    simp only [List.take_succ_cons, List.prod_cons, List.drop_succ_cons]
    rw [← Nat.mul_assoc]
    rfl

/-! ## The blockwise fixed-point iteration -/

/-- The blockwise application of `fxTensorRec`: the flat array of `A` consecutive blocks of size
`ss.prod` is mapped to `A` blocks of size `ts.prod`. -/
noncomputable def fxBlk (A : ℕ) (ss ts : List ℕ)
    (Φ : (i : ℕ) → (Fin (ss.getD i 0) → ℤ × ℤ) → (Fin (ts.getD i 0) → ℤ × ℤ))
    (u : Fin (A * ss.prod) → ℤ × ℤ) : Fin (A * ts.prod) → ℤ × ℤ :=
  fun J => if h : 0 < ts.prod then
    fxTensorRec ss ts Φ (fun i : Fin ss.prod =>
      u ⟨(J : ℕ) / ts.prod * ss.prod + (i : ℕ), by
        have hJ : (J : ℕ) / ts.prod < A := (Nat.div_lt_iff_lt_mul h).mpr J.isLt
        have h1 : (J : ℕ) / ts.prod * ss.prod + (i : ℕ)
            < ((J : ℕ) / ts.prod + 1) * ss.prod := by
          rw [Nat.add_mul]
          simpa using Nat.add_lt_add_left i.isLt ((J : ℕ) / ts.prod * ss.prod)
        have h2 : ((J : ℕ) / ts.prod + 1) * ss.prod ≤ A * ss.prod :=
          Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hJ)
        omega⟩) ⟨(J : ℕ) % ts.prod, Nat.mod_lt _ h⟩
  else (0, 0)

/-- The length of one axis pass (independent of the input list). -/
@[simp] lemma axisList_length (A m n B : ℕ)
    (Φ : (Fin m → ℤ × ℤ) → (Fin n → ℤ × ℤ)) (zs : List (ℤ × ℤ)) :
    (axisList A m n B Φ zs).length = A * n * B := by
  simp [axisList, HvdH.unslices]

end Work.Resample
