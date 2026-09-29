import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Resample.auDefs
import Submission.Work.Resample.auKit
import Submission.Work.Kernel.Raw
import Submission.Work.Fx.FxCommon
import Submission.Work.Fx.piDefs

/-!
# Toolkit for the table word `prep` (`Work.Resample.auPrep`)

This module fixes the *values* and the *windows* used by the program that computes the static
parameter block `auPvals p α s t` of the resampling word (paper §4, Lemma 4.9), and proves the
generic bookkeeping lemmas that its construction needs.

## The values

* `auC p α s t k = t·K_k − t·m − s·k` (`K_k = auK s t k`, `m = auM p α`); then
  `auNsq p α s t k i = (auC + t·i)²` (`auNsq_eq_C`).  This is the quantity the word computes
  before squaring: it is `t` times the distance of the `i`-th retained term from `s k / t`.
* `auWtL p α s t k` is the list of the `auL p α` integer values holding the weights of output `k`;
  `auRec p α s t k = cons (int (K_{k+1} − K_k)) (ofList (auWtL …))` (`auRec_eq`).
* `auKs p t` is the list `[cons (int 0) (int (auPi p)), …, cons (int (t−1)) (int (auPi p))]`: the
  list of labels the table word maps over (the payload of each label is the fixed-point `π`).
* `auRecs p α s t = (List.range t).map (fun k => auRec p α s t k)`, so
  `auTable p α s t = ofList (auRecs …)` (`auTable_eq`).
* `auRecOf p α s t : Val → Val` reads the label `k` out of a value `cons (int k) _` and returns
  `auRec p α s t k`: this is the function the element word of the table implements.

## The combinators

`LayoutLib.replicate`/`enumerate` and `KernelLib.mapList` are adapted to the fixed-window form
`Pipe main prog A B c` of `auKit` (`Pipe.replicate`, `Pipe.enumerate`, `Pipe.mapListFun`).
`MapListField` is the `mapList` field of `KernelLib` as a hypothesis, so that the combinators can
be stated for a *given* combinator `comb` (whose use the caller has to write into its program).



## Intended construction of the table word (`Work.Resample.auPrep`)

The goal is a word `prep` with

`WordR main prep (fun vs => ∃ rest, vs = [int p, int α, int s, int t] ++ rest)`
`                  (fun vs out => ∃ rest, vs = [int p, int α, int s, int t] ++ rest ∧`
`                     out = auPvals p α s t ++ rest)   (fun _ => K * (t+1) * (p+1)^K)`

for `2 ≤ s < t < 2^p`, `α ≤ 2^p`, `100 ≤ p`, `α^2 < p`.  It is built in four phases.

1. **π.**  `int p ↦ int (auPrec p)` (`auPrec p = 3p+100`) by `pushVal 3`, `mulS`, `pushVal 100`,
   `add`, then run the given `piSpec` word: the stack becomes `[int (auPi p), int p, int α, int s,
   int t] ++ rest`.
2. **Parameters.**  Rotate the five values into `[int p, int α, int s, int t, int (auPi p)] ++ rest`
   (4 rolls of depth 4), then compute `off = auOff p α s = s*((auM+s-1)/s) - auM` and
   `cop = auCop p α s = (off+2s+2*auM)/s` (`auM p α = (isqrt p + 1)*α`; `sqrt`, `pushVal`,
   `mulS`, `add`, `sub`, `tdiv`, `swap`) and push them, giving
   `[int cop, int off, int p, int α, int s, int t, int (auPi p)] ++ rest`.
3. **The table.**  `pick 4` (π) and `pick 4` (`t`) give `[int t, int (auPi p), …]`; then
   `LayoutLib.replicate` builds `ofList (List.replicate t (int (auPi p)))` and
   `LayoutLib.enumerate` turns it into `ofList (auKs p t)`.  Then the record word of
   `Work.Resample.auRecWord` (a `Pipe` over the window `[cons (int k) (int (auPi p))] ++ [int p,
   int α, int s, int t, int (auPi p)]`) is mapped over `auKs p t` by `KernelLib.mapList`
   (`Pipe.mapListFun`): the stack becomes `ofList (auRecs p α s t) :: [int p, int α, int s, int t,
   int (auPi p)] ++ rest`, i.e. `auTable p α s t` sits on top.  The extra values `int off`, `int cop`
   ride along below in the `rest` of the `mapList`.
4. **Output.**  Finally the window must become `[int off, int cop, int p, auTable p α s t] ++ rest`,
   i.e. `auPvals p α s t ++ rest`: move `auTable` out of the way, roll and drop `α, s, t, π`,
   bring `p` to the front and reorder with `off`, `cop` (`roll`/`drop`/`swap`).

### The record word (`Work.Resample.auRecWord`)

Inside one `mapList` round the record word sees `cons (int k) (int (auPi p)) :: [int p, int α,
int s, int t, int (auPi p)] ++ rest` and must produce `auRec p α s t k :: [int p, int α, int s,
int t, int (auPi p)] ++ rest`, where `auRec p α s t k = cons (int (K_{k+1}-K_k)) (ofList (auWtL p α
s t k))` and `auWtL p α s t k` is the list of the `auL p α` weights of output `k`.

* `unconsV` splits the label into `int k :: int (auPi p) :: …`; the 7 values `int k, int (auPi p),
  int p, int α, int s, int t, int (auPi p)` are then on top (all of size `≤ auSZ p`).
* compute `m = auM p α = (isqrt p+1)*α` and `L = 2m+1` (`sqrt`, `pushVal`, `mulS`, `add`),
  `K_k = (2ks+t)/(2t)` and `K_{k+1} = (2(k+1)s+t)/(2t)` (`mulS`, `add`, `tdiv`; `2t ≠ 0`),
  the slide `int (K_{k+1} - K_k)` and `C = auC p α s t k = t·K_k − t·m − s·k` (`mulS`, `sub`).
* build the inner list: `replicate L` of the payload that the element word needs (e.g.
  `Y = cons (int C) (cons (int t) (cons (int p) (cons (int α) (int (auPi p)))))`, or, simpler,
  keep `int C`, `int t`, `int p`, `int α` immediately below the list as the `rest` of the inner
  `mapList`) followed by `enumerate`, and run `KernelLib.mapList` with the **element word**: the
  element word gets the label `i`, calls `wtSpec` on `[int p, int α, int t, int ((C+t·i)^2),
  int (auPi p)]` and outputs `int (auWt p α t ((C+t·i)^2))`.  `auNsq_eq_C` identifies this with
  `auWt p α t (auNsq p α s t k i)`, so the list built is `auWtL p α s t k`.
* `consV` puts `int (slide)` in front of `ofList (auWtL …)` to form `auRec p α s t k`, and the
  scratch values (`int k`, the copies of `p, α, s, t`, …) are dropped.
* Costs: every value occurring inside one round has size `≤ auSZ p = 10p+400` (the weights by
  `auWtSize`, the `auNsq` values by `auNsqBounds`, `auK`, `auC` by `auSizeBounds`), and the round
  performs `O(1)` library calls plus one inner `mapList` of `auL p α ≤ 4p+1` elements, so its cost
  is `≤ K*(p+1)^K` with `K` a constant.  The size of the *result* `auRec p α s t k` is
  `≤ 100*(p+1)^2` (`auTableSize`), which is the `L` of the outer `mapList`.

### The pre-word (`Work.Resample.auPreChain`)

`pre` turns `[int p, int α, int s, int t]` into
`[ofList (auKs p t), int p, int α, int s, int t, int (auPi p), int (auCop p α s), int (auOff p α s)]`.
Suggested order (each line is one library call; `W` is the value stack, written with the top first;
`m = auM p α = (isqrt p+1)·α`):

1. parameters of the window: `off = auOff p α s = s·((m+s−1)/s) − m`, `cop = auCop p α s =
   (off+2s+2m)/s` (`sqrt`, `pushVal 1`, `add`, `pick`, `mulS`, `tdiv`, `sub`; `auOff_cast`,
   `auCop_cast`, `natCast_div_eq_tdiv` identify the values computed with the definitions of `auDefs`;
   every intermediate value is `≤ 2^{2p+2}`, so `isz ≤ auSZ p`).
   The parameters `int p, int α, int s, int t` must be preserved; the cheapest layout is to keep
   them at the bottom of the window and to return to them with `pick`.  A good sequence is
   `pick 0, sqrt, pushVal 1, add` (→ `√p+1`), `pick α` (`pick 2`), `mulS` (→ `m`), `pick 0`
   (duplicate `m`), `pushVal 1, pick s, roll 2, add, sub` (→ `m+s−1`), `pick s, roll 1, tdiv`
   (→ `q = (m+s−1)/s`), `pick s, mulS` (→ `s·q`), `sub` (→ `off`), `pick 0` (duplicate `off`),
   `pick s, pushVal 2, mulS` (→ `2s`), `pick p, sqrt, pushVal 1, add, pick α, mulS` (→ `m`),
   `pushVal 2, mulS` (→ `2m`), `add, add` (→ `off+2s+2m`), `pick s, roll 1, tdiv` (→ `cop`).
2. rotate the four parameter values above `int cop, int off`: four `roll 5`
   (`[cop, off, p, α, s, t] → [t, cop, off, p, α, s] → … → [p, α, s, t, cop, off]`).
3. π: `pick 0, pushVal 3, mulS, pushVal 100, add` gives `auPrec p`, then the given `piSpec` word
   (`auPi p = uval (auPrec p)` by definition); four `roll 4` rotate the result into
   `[p, α, s, t, auPi p, cop, off]`.
4. the label list: `pick 4` (π), `pick 4` (`t`), `replicate` (`ofList (replicate t (int (auPi p)))`),
   `enumerate` (via `enumerate_replicate` this is `ofList (auKs p t)`).

Cost: `O(1)` calls with values of size `≤ auSZ p`, plus `replicate`/`enumerate` whose cost is
`O(t·p)`; so `K·(t+1)·(p+1)^K` with a constant `K`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Resample

open HvdH
open Work.Fx

/-! ## The values computed by the table word -/

/-- The offset `t·K_k − t·m − s·k` such that `auNsq p α s t k i = (auC + t·i)²`. -/
def auC (p α s t k : ℕ) : ℤ :=
  (t : ℤ) * (auK s t k : ℤ) - (t : ℤ) * (auM p α : ℤ) - (s : ℤ) * (k : ℤ)

theorem auNsq_eq_C (p α s t k i : ℕ) :
    auNsq p α s t k i = (auC p α s t k + (t : ℤ) * (i : ℤ)) ^ 2 := by
  simp only [auNsq, auN, auC]
  ring

/-- The list of the weight values of output `k`. -/
def auWtL (p α s t k : ℕ) : List Val :=
  (List.range (auL p α)).map fun i : ℕ => Val.int (auWt p α t (auNsq p α s t k i))

theorem auWtL_eq (p α s t k : ℕ) :
    auWtL p α s t k
      = (List.range (auL p α)).map (fun i : ℕ => Val.int (auWt p α t (auNsq p α s t k i))) := rfl

theorem auRec_eq (p α s t k : ℕ) :
    auRec p α s t k
      = .cons (.int ((auK s t (k + 1) : ℤ) - (auK s t k : ℤ))) (ofList (auWtL p α s t k)) := rfl

/-- The list of labels of the table word: `k ↦ cons (int k) (int (auPi p))`. -/
def auKs (p t : ℕ) : List Val :=
  (List.range t).map fun k : ℕ => Val.cons (.int (k : ℤ)) (.int (auPi p))

/-- The list of records of the table. -/
def auRecs (p α s t : ℕ) : List Val := (List.range t).map fun k : ℕ => auRec p α s t k

theorem auTable_eq (p α s t : ℕ) : auTable p α s t = ofList (auRecs p α s t) := rfl

/-- The record associated with a label value (the function the element word of the table
implements). -/
def auRecOf (p α s t : ℕ) : Val → Val
  | .cons (.int k) _ => auRec p α s t k.toNat
  | _ => .nil

theorem auRecOf_cons (p α s t : ℕ) (k : ℕ) (v : Val) :
    auRecOf p α s t (.cons (.int (k : ℤ)) v) = auRec p α s t k := by
  simp [auRecOf]

theorem map_auRecOf (p α s t : ℕ) :
    (auKs p t).map (auRecOf p α s t) = auRecs p α s t := by
  simp only [auKs, auRecs, List.map_map, Function.comp_apply]
  apply List.map_congr_left
  intro k _
  exact auRecOf_cons p α s t k (.int (auPi p))

/-- `Forall₂` with a functional relation on the second component. -/
theorem forall₂_map_right {xs : List Val} {ys : List Val} {F : Val → Val}
    (h : List.Forall₂ (fun x y => y = F x) xs ys) : ys = xs.map F := by
  induction h with
  | nil => rfl
  | cons hab _ ih => rw [List.map_cons, ih, hab]

/-! ## `List.replicate` / `List.enumerate` -/

theorem replicate_getD {n : ℕ} {v : Val} {i : ℕ} (hi : i < n) : (List.replicate n v).getD i .nil = v := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_replicate, if_pos hi]
  rfl

theorem replicate_length (n : ℕ) (v : Val) : (List.replicate n v).length = n := List.length_replicate

theorem enumerate_replicate (n : ℕ) (v : Val) :
    (List.range (List.replicate n v).length).map
        (fun i : ℕ => Val.cons (.int (i : ℤ)) ((List.replicate n v).getD i .nil))
      = (List.range n).map (fun i : ℕ => Val.cons (.int (i : ℤ)) v) := by
  rw [replicate_length]
  apply List.map_congr_left
  intro i hi
  rw [replicate_getD (List.mem_range.mp hi)]

/-! ## Fixed-window adapters for `LayoutLib` -/

theorem Pipe.replicate {prog : Cmd} {K : ℕ} (main : Cmd)
    (h : ∀ (m : Cmd) (k : ℕ) (v : Val), WordR m prog
      (fun vs => ∃ rest, vs = .int (k : ℤ) :: v :: rest)
      (fun vs out => ∃ rest, vs = .int (k : ℤ) :: v :: rest ∧
        out = ofList (List.replicate k v) :: rest)
      (fun _ => K * ((k + 1) * (vsz v + 1) + isz (k : ℤ) + 1)))
    {k : ℕ} {v : Val} :
    Pipe main prog [.int (k : ℤ), v] [ofList (List.replicate k v)]
      (K * ((k + 1) * (vsz v + 1) + isz (k : ℤ) + 1)) := by
  intro rest vs hvs s R hR
  have hv2 : vs = .int (k : ℤ) :: v :: rest := by rw [hvs]; rfl
  obtain ⟨out, s', n, ⟨r', hvs', hout⟩, hev, hn, hstk, hoth⟩ :=
    h main k v vs ⟨rest, hv2⟩ s R hR
  have h3 : r' = rest := (cons_inj3 (hvs'.symm.trans hv2)).2.2
  have hpost : out = [ofList (List.replicate k v)] ++ rest := by
    rw [hout, h3]
    simp
  exact ⟨out, s', n, hpost, hev, hn, hstk, hoth⟩

theorem Pipe.enumerate {prog : Cmd} {K : ℕ} (main : Cmd)
    (h : ∀ (m : Cmd) (xs : List Val), WordR m prog
      (fun vs => ∃ rest, vs = ofList xs :: rest)
      (fun vs out => ∃ rest, vs = ofList xs :: rest ∧
        out = ofList ((List.range xs.length).map fun i : ℕ => Val.cons (.int (i : ℤ)) (xs.getD i .nil)) :: rest)
      (fun _ => K * (vsz (ofList xs) + xs.length * ((xs.length).size + 1) + 1)))
    {xs : List Val} :
    Pipe main prog [ofList xs]
      [ofList ((List.range xs.length).map fun i : ℕ => Val.cons (.int (i : ℤ)) (xs.getD i .nil))]
      (K * (vsz (ofList xs) + xs.length * ((xs.length).size + 1) + 1)) := by
  intro rest vs hvs s R hR
  have hv2 : vs = ofList xs :: rest := by rw [hvs]; rfl
  obtain ⟨out, s', n, ⟨r', hvs', hout⟩, hev, hn, hstk, hoth⟩ :=
    h main xs vs ⟨rest, hv2⟩ s R hR
  have hvs'' : ofList xs :: r' = ofList xs :: rest := hvs'.symm.trans hv2
  have h3 : r' = rest := (List.cons.inj hvs'').2
  have hpost : out = [ofList ((List.range xs.length).map
      fun i : ℕ => Val.cons (.int (i : ℤ)) (xs.getD i .nil))] ++ rest := by
    rw [hout, h3]
    simp
  exact ⟨out, s', n, hpost, hev, hn, hstk, hoth⟩

/-! ## The `mapList` field and its fixed-window combinator -/

/-- The `mapList` field of `HvdH.KernelLib` (as a hypothesis, for a *given* combinator). -/
def MapListField (comb : Cmd → Cmd) (K : ℕ) : Prop :=
  ∀ (main q : Cmd) (rest : List Val) (P : Val → Prop) (Q : Val → Val → Prop) (c L : ℕ),
    (∀ x, P x → WordR main q (fun vs => vs = x :: rest)
      (fun _ out => ∃ y, out = y :: rest ∧ Q x y ∧ vsz y ≤ L) (fun _ => c)) →
    ∀ xs : List Val, (∀ x ∈ xs, P x ∧ vsz x ≤ L) →
    WordR main (comb q) (fun vs => vs = ofList xs :: rest)
      (fun _ out => ∃ ys, out = ofList ys :: rest ∧ List.Forall₂ Q xs ys)
      (fun _ => xs.length * (c + K * (L + 1)) + K)

theorem MapListField.of_kernel (hk : KernelLib) : ∃ (comb : Cmd → Cmd) (K : ℕ), MapListField comb K :=
  hk.mapList

/-- Fixed-window form of `mapList`: every element `x` of `xs` is replaced by `F x`. -/
theorem mapListFun {comb : Cmd → Cmd} {Kml : ℕ} (hML : MapListField comb Kml)
    {main q : Cmd} {rest : List Val} {xs : List Val} {F : Val → Val} {c L : ℕ}
    (h : ∀ x ∈ xs, Pipe main q [x] [F x] c)
    (hx : ∀ x ∈ xs, vsz x ≤ L) (hy : ∀ x ∈ xs, vsz (F x) ≤ L) :
    WordR main (comb q) (fun vs => vs = ofList xs :: rest)
      (fun _ out => out = ofList (xs.map F) :: rest)
      (fun _ => xs.length * (c + Kml * (L + 1)) + Kml) := by
  have h1 : WordR main (comb q) (fun vs => vs = ofList xs :: rest)
      (fun _ out => ∃ ys, out = ofList ys :: rest ∧ List.Forall₂ (fun x y => y = F x) xs ys)
      (fun _ => xs.length * (c + Kml * (L + 1)) + Kml) := by
    refine hML main q rest (fun x => x ∈ xs) (fun x y => y = F x) c L ?_ xs ?_
    · intro x hxmem
      refine Work.Kernel.WordR_conseq (h x hxmem rest) ?_ ?_ ?_
      · intro vs hvs; exact hvs
      · intro vs out _ hout
        refine ⟨F x, ?_, rfl, hy x hxmem⟩
        rw [hout]
        rfl
      · intro vs _; exact le_rfl
    · intro x hxmem; exact ⟨hxmem, hx x hxmem⟩
  refine Work.Kernel.WordR_conseq h1 ?_ ?_ ?_
  · intro vs hvs; exact hvs
  · intro vs out _ hout
    obtain ⟨ys, hout', hf⟩ := hout
    rw [hout', forall₂_map_right hf]
  · intro vs _; exact le_rfl

/-- `Pipe` form of `mapListFun`: the list `ofList xs` (on top of a fixed window `rest`) becomes
`ofList (xs.map F)`. -/
theorem Pipe.mapListFun {comb : Cmd → Cmd} {Kml : ℕ} (hML : MapListField comb Kml)
    {main q : Cmd} {rest : List Val} {xs : List Val} {F : Val → Val} {c L : ℕ}
    (h : ∀ x ∈ xs, Pipe main q [x] [F x] c)
    (hx : ∀ x ∈ xs, vsz x ≤ L) (hy : ∀ x ∈ xs, vsz (F x) ≤ L) :
    Pipe main (comb q) (ofList xs :: rest) (ofList (xs.map F) :: rest)
      (xs.length * (c + Kml * (L + 1)) + Kml) := by
  intro r
  have hpost := Work.Resample.mapListFun (main := main) hML h hx hy (rest := rest ++ r)
  exact hpost


/-! ## `auOff` / `auCop` as integers

The pre-word builds the values `auOff p α s`, `auCop p α s` with integer operations
(`sub`, `mulS`, `tdiv`), so it needs the cast lemmas identifying the *integer* value it computes
with the natural-number definitions of `auDefs`. -/

/-- For a positive divisor, natural division is `Int.tdiv` on the nonnegative casts. -/
theorem natCast_div_eq_tdiv (m : ℕ) {s : ℕ} (hs : 1 ≤ s) :
    ((m / s : ℕ) : ℤ) = Int.tdiv (m : ℤ) ((s : ℕ) : ℤ) := by
  rw [Int.natCast_div, Int.tdiv_eq_ediv, if_pos (Or.inl (Int.natCast_nonneg m)), add_zero]

theorem auOff_cast (p α s : ℕ) (hs : 1 ≤ s) :
    ((auOff p α s : ℕ) : ℤ) =
      (s : ℤ) * (((auM p α + s - 1) / s : ℕ) : ℤ) - (auM p α : ℤ) := by
  have hs0 : 0 < s := by omega
  have hle : auM p α ≤ s * ((auM p α + s - 1) / s) := by
    have h2 := Nat.div_add_mod (auM p α + s - 1) s
    have h3 : (auM p α + s - 1) % s ≤ s - 1 := Nat.le_sub_one_of_lt (Nat.mod_lt _ hs0)
    omega
  rw [auOff, Nat.cast_sub hle, Nat.cast_mul]

theorem auCop_cast (p α s : ℕ) (hs : 1 ≤ s) :
    ((auCop p α s : ℕ) : ℤ) =
      Int.tdiv (((auOff p α s : ℕ) : ℤ) + 2 * (s : ℤ) + 2 * (auM p α : ℤ)) (s : ℤ) := by
  rw [auCop, natCast_div_eq_tdiv _ hs]
  push_cast
  ring


/-- A flexible size bound: a value of `N` bits with `N ≤ 10p + 398` fits `auSZ p`. -/
theorem isz_le_auSZ_of_lt {z : ℤ} {p N : ℕ} (h : z.natAbs < 2 ^ N) (hN : N ≤ 10 * p + 398) :
    isz z ≤ auSZ p := by
  have h1 : z.natAbs.size ≤ N := Nat.size_le.mpr h
  simp only [isz, auSZ]
  omega

end Work.Resample
