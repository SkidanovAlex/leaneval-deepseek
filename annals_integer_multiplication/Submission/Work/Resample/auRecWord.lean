import Mathlib
import Submission.Work.Resample.auKit
import Submission.Work.Resample.auPrepDefs
import Submission.Work.Resample.auRecArith
import Submission.Work.Resample.auMLWord
import Submission.Work.Resample.auKWord
import Submission.Work.Resample.auWtLWord

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.Resample

open HvdH
open Work.Fx

/-!
# The record word `auRecWord` (paper Lemma 4.9, element of the table word)

`auRecWord` builds, inside one round of the table `mapList`, the record

`auRec p α s t k = cons (int (K_{k+1} - K_k)) (ofList (auWtL p α s t k))`

out of the label `cons (int k) (int (auPi p))` and the parameters `int p, int α, int s, int t,
int (auPi p)`, from a word that evaluates a single weight (`hElem`).

The proof is a hand-written `Pipe` chain over the fixed window
`[label, int p, int α, int s, int t, int (auPi p)]`, built out of the library words of
`KernelLib`/`IntLib`/`LayoutLib` through the adapters of `auKit`/`auPrepDefs`.

This file provides (a) an adapter layer for windows of `int`-values, (b) the cost
bookkeeping, and (c) the chain itself.
-/

/-! ## Windows of integer values -/

/-- Total `isz`-size of a list of integers (the `szl` of the corresponding value list). -/
def szI (l : List ℤ) : ℕ := (l.map isz).sum

theorem szI_cons (z : ℤ) (l : List ℤ) : szI (z :: l) = isz z + szI l := by
  simp [szI]

theorem szl_map_int (l : List ℤ) : szl (l.map Val.int) = szI l := by
  unfold szl szI
  rw [List.map_map]
  exact congrArg List.sum (List.map_congr_left (fun z _ => vsz_int z))

theorem getD_map_int {A : List ℤ} {j : ℕ} (hj : j < A.length) :
    (A.map Val.int).getD j .nil = Val.int (A.getD j 0) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hj, Option.map_some, Option.getD_some]
  rfl

theorem take_map_int (l : List ℤ) (n : ℕ) :
    (l.map Val.int).take n = (l.take n).map Val.int := by
  rw [← List.map_take]

theorem szl_take_map_int (A : List ℤ) (j : ℕ) :
    szl ((A.map Val.int).take (j + 1)) = szI (A.take (j + 1)) := by
  rw [take_map_int, szl_map_int]

theorem szI_le_of {l : List ℤ} {B : ℕ} (h : ∀ z ∈ l, isz z ≤ B) : szI l ≤ l.length * B := by
  induction l with
  | nil => simp [szI]
  | cons a t ih =>
    have ha : isz a ≤ B := h a (List.mem_cons_self)
    have ht : ∀ z ∈ t, isz z ≤ B := fun z hz => h z (List.mem_cons_of_mem _ hz)
    have := ih ht
    rw [szI_cons, List.length_cons]
    nlinarith [Nat.zero_le (szI t)]

/-- Fixed-window spec for windows of integer values: same as `Pipe` after encoding by `Val.int`. -/
def IPipe (main prog : Cmd) (A B : List ℤ) (c : ℕ) : Prop :=
  Pipe main prog (A.map Val.int) (B.map Val.int) c

/-! ## Adapters -/

theorem IPipe.bin {main prog : Cmd} {P : ℤ → ℤ → Prop} {f : ℤ → ℤ → ℤ} {C : ℤ → ℤ → ℕ}
    (h : BinOp main prog P f C) {a b : ℤ} (hab : P a b) {T : List ℤ} :
    IPipe main prog (a :: b :: T) (f a b :: T) (C a b) := by
  have h1 : Pipe main prog [Val.int a, Val.int b] [Val.int (f a b)] (C a b) := Pipe.binOp h hab
  simpa [IPipe, List.map_cons] using Pipe.appendTail (T.map Val.int) h1

theorem IPipe.un {main prog : Cmd} {P : ℤ → Prop} {f : ℤ → ℤ} {C : ℤ → ℕ}
    (h : UnOp main prog P f C) {a : ℤ} (ha : P a) {T : List ℤ} :
    IPipe main prog (a :: T) (f a :: T) (C a) := by
  have h1 : Pipe main prog [Val.int a] [Val.int (f a)] (C a) := Pipe.unOp h ha
  simpa [IPipe, List.map_cons] using Pipe.appendTail (T.map Val.int) h1

theorem IPipe.pushOn {main : Cmd} {progV : Val → Cmd} {K : ℕ}
    (h : ∀ (m : Cmd) (v : Val), WordR m (progV v) (fun _ => True)
      (fun vs out => out = v :: vs) (fun _ => K * (vsz v + 1))) (z : ℤ) (T : List ℤ) :
    IPipe main (progV (.int z)) T (z :: T) (K * (isz z + 1)) := by
  have h1 : Pipe main (progV (Val.int z)) ([] : List Val) [Val.int z] (K * (isz z + 1)) := by
    simpa [vsz_int] using Pipe.pushVal h (Val.int z)
  simpa [IPipe, List.map_cons] using Pipe.appendTail (T.map Val.int) h1

theorem IPipe.appendTail {main prog : Cmd} {A B : List ℤ} {c : ℕ} (T : List ℤ)
    (h : IPipe main prog A B c) : IPipe main prog (A ++ T) (B ++ T) c := by
  simpa [IPipe, List.map_append] using Pipe.appendTail (T.map Val.int) h

theorem IPipe.dropAt {prog : Cmd} {K : ℕ} (main : Cmd)
    (h : ∀ m : Cmd, WordR m prog (fun vs => vs ≠ [])
      (fun vs out => ∃ v rest, vs = v :: rest ∧ out = rest)
      (fun vs => K * (vsz (vs.headD .nil) + 1)))
    {a : ℤ} {T : List ℤ} : IPipe main prog (a :: T) T (K * (isz a + 1)) := by
  have h1 : Pipe main prog [Val.int a] [] (K * (isz a + 1)) := by
    simpa [vsz_int] using Pipe.drop main h (Val.int a)
  simpa [IPipe, List.map_cons] using Pipe.appendTail (T.map Val.int) h1

theorem IPipe.dupAt {prog : Cmd} {K : ℕ} (main : Cmd)
    (h : ∀ m : Cmd, WordR m prog (fun vs => vs ≠ [])
      (fun vs out => ∃ v rest, vs = v :: rest ∧ out = v :: v :: rest)
      (fun vs => K * (vsz (vs.headD .nil) + 1)))
    {a : ℤ} {T : List ℤ} : IPipe main prog (a :: T) (a :: a :: T) (K * (isz a + 1)) := by
  have h1 : Pipe main prog [Val.int a] [Val.int a, Val.int a] (K * (isz a + 1)) := by
    simpa [vsz_int] using Pipe.dup main h (Val.int a)
  simpa [IPipe, List.map_cons] using Pipe.appendTail (T.map Val.int) h1

theorem IPipe.swapAt {prog : Cmd} {K : ℕ} (main : Cmd)
    (h : ∀ m : Cmd, WordR m prog (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = b :: a :: rest)
      (fun vs => K * (vsz (vs.getD 0 .nil) + vsz (vs.getD 1 .nil) + 1)))
    {a b : ℤ} {T : List ℤ} :
    IPipe main prog (a :: b :: T) (b :: a :: T) (K * (isz a + isz b + 1)) := by
  have h1 : Pipe main prog [Val.int a, Val.int b] [Val.int b, Val.int a]
      (K * (isz a + isz b + 1)) := by
    simpa [vsz_int] using Pipe.swap main h (Val.int a) (Val.int b)
  simpa [IPipe, List.map_cons] using Pipe.appendTail (T.map Val.int) h1

theorem IPipe.pickAt {prog : ℕ → Cmd} {K : ℕ} (main : Cmd)
    (h : ∀ (m : Cmd) (k : ℕ), WordR m (prog k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs)
      (fun vs => K * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    {A : List ℤ} {j : ℕ} (hj : j < A.length) {z : ℤ} (hz : A.getD j 0 = z) :
    IPipe main (prog j) A (z :: A) (K * (j + 1) * (szI (A.take (j + 1)) + 1)) := by
  have hlen : j < (A.map Val.int).length := by simpa using hj
  have hv : (A.map Val.int).getD j .nil = Val.int z := by
    rw [getD_map_int hj, hz]
  exact Pipe.le (Pipe.pickAt main h hlen hv) (le_of_eq (by rw [szl_take_map_int]))

theorem IPipe.rollAt {prog : ℕ → Cmd} {K : ℕ} (main : Cmd)
    (h : ∀ (m : Cmd) (k : ℕ), WordR m (prog k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs.eraseIdx k)
      (fun vs => K * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    {A : List ℤ} {j : ℕ} (hj : j < A.length) {z : ℤ} (hz : A.getD j 0 = z) :
    IPipe main (prog j) A (z :: A.eraseIdx j) (K * (j + 1) * (szI (A.take (j + 1)) + 1)) := by
  have hlen : j < (A.map Val.int).length := by simpa using hj
  have hv : (A.map Val.int).getD j .nil = Val.int z := by
    rw [getD_map_int hj, hz]
  have hB : (A.map Val.int).getD j .nil :: (A.map Val.int).eraseIdx j
      = (z :: A.eraseIdx j).map Val.int := by
    rw [hv, List.eraseIdx_map, List.map_cons]
  have h1 : Pipe main (prog j) (A.map Val.int) ((z :: A.eraseIdx j).map Val.int)
      (K * (j + 1) * (szl ((A.map Val.int).take (j + 1)) + 1)) := by
    rw [← hB]
    exact Pipe.roll main h hlen
  exact Pipe.le h1 (le_of_eq (by rw [szl_take_map_int]))

/-! ## `Pipe` level helpers -/

theorem Pipe.unconsVAt {prog : Cmd} {K : ℕ} (main : Cmd)
    (h : ∀ m : Cmd, WordR m prog (fun vs => ∃ a b rest, vs = .cons a b :: rest)
      (fun vs out => ∃ a b rest, vs = .cons a b :: rest ∧ out = a :: b :: rest) (fun _ => K))
    {a b : Val} {T : List Val} : Pipe main prog (.cons a b :: T) (a :: b :: T) K := by
  intro rest vs hvs s R hR
  have hv2 : vs = .cons a b :: (T ++ rest) := by rw [hvs]; rfl
  obtain ⟨out, s', n, ⟨a', b', r', hvs', hout⟩, hev, hn, hstk, hoth⟩ :=
    h main vs ⟨a, b, T ++ rest, hv2⟩ s R hR
  obtain ⟨h1, h2, h3⟩ := Work.Fx.val_cons_inj3 (hvs'.symm.trans hv2)
  exact ⟨out, s', n, by rw [hout, h1, h2, h3]; rfl, hev, hn, hstk, hoth⟩

theorem Pipe.consVAt {prog : Cmd} {K : ℕ} (main : Cmd)
    (h : ∀ m : Cmd, WordR m prog (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = .cons a b :: rest) (fun _ => K))
    {a b : Val} {T : List Val} : Pipe main prog (a :: b :: T) (.cons a b :: T) K := by
  intro rest vs hvs s R hR
  have hv2 : vs = a :: b :: (T ++ rest) := by rw [hvs]; rfl
  obtain ⟨out, s', n, ⟨a', b', r', hvs', hout⟩, hev, hn, hstk, hoth⟩ :=
    h main vs (by rw [hv2]; simp) s R hR
  obtain ⟨h1, h2, h3⟩ := Work.Fx.cons_inj3 (hvs'.symm.trans hv2)
  refine ⟨out, s', n, ?_, hev, hn, hstk, hoth⟩
  rw [hout, h1, h2, h3]
  rfl

/-! ## Cost bookkeeping -/

theorem pow_two_le (p : ℕ) (hp : 100 ≤ p) : 2 ≤ (p + 1) ^ 2 := by nlinarith

theorem pow_ge_one (p k : ℕ) : 1 ≤ (p + 1) ^ k := by
  induction k with
  | zero => simp
  | succ j ih =>
    calc (1 : ℕ) = 1 * 1 := by ring
      _ ≤ (p + 1) ^ j * (p + 1) :=
          Nat.mul_le_mul ih (Nat.succ_le_succ (Nat.zero_le p))

theorem sq_le_sq_sq (p : ℕ) : (p + 1) ^ 2 * (p + 1) ^ 2 = (p + 1) ^ 4 := by
  rw [← pow_add]

theorem leR_add {K KS p u v : ℕ} (hK : K ≤ KS) (hu : u ≤ (p + 1) ^ 2) (hv : v ≤ (p + 1) ^ 2)
    (hp : 100 ≤ p) (hKS : 4 ≤ KS) : K * (u + v) ≤ KS * (p + 1) ^ KS := by
  have h1 : 2 ≤ (p + 1) ^ 2 := pow_two_le p hp
  calc K * (u + v) ≤ KS * (2 * (p + 1) ^ 2) := Nat.mul_le_mul hK (by nlinarith [hu, hv])
    _ ≤ KS * ((p + 1) ^ 2 * (p + 1) ^ 2) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ h1)
    _ = KS * (p + 1) ^ 4 := by rw [sq_le_sq_sq]
    _ ≤ KS * (p + 1) ^ KS := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hKS)

theorem leR_mul {K KS p u v : ℕ} (hK : K ≤ KS) (hu : u ≤ (p + 1) ^ 2) (hv : v ≤ (p + 1) ^ 2)
    (hp : 100 ≤ p) (hKS : 4 ≤ KS) : K * (u * v) ≤ KS * (p + 1) ^ KS := by
  calc K * (u * v) ≤ KS * ((p + 1) ^ 2 * (p + 1) ^ 2) := Nat.mul_le_mul hK (Nat.mul_le_mul hu hv)
    _ = KS * (p + 1) ^ 4 := by rw [sq_le_sq_sq]
    _ ≤ KS * (p + 1) ^ KS := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hKS)

theorem leR_sq {K KS p u : ℕ} (hK : K ≤ KS) (hu : u ≤ (p + 1) ^ 2)
    (hp : 100 ≤ p) (hKS : 4 ≤ KS) : K * u ^ 2 ≤ KS * (p + 1) ^ KS := by
  have h1 : u ^ 2 ≤ (p + 1) ^ 4 := by
    calc u ^ 2 ≤ ((p + 1) ^ 2) ^ 2 := Nat.pow_le_pow_left hu 2
      _ = (p + 1) ^ 4 := by rw [← pow_mul]
  calc K * u ^ 2 ≤ KS * (p + 1) ^ 4 := Nat.mul_le_mul hK h1
    _ ≤ KS * (p + 1) ^ KS := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hKS)

theorem leR_one {K KS p u : ℕ} (hK : K ≤ KS) (hu : u ≤ (p + 1) ^ 2)
    (hp : 100 ≤ p) (hKS : 4 ≤ KS) : K * (u + 1) ≤ KS * (p + 1) ^ KS := by
  have h3 : (p + 1) ^ 2 + 1 ≤ (p + 1) ^ 4 := by
    have h2 : 2 ≤ (p + 1) ^ 2 := pow_two_le p hp
    nlinarith [h2]
  calc K * (u + 1) ≤ KS * ((p + 1) ^ 2 + 1) := Nat.mul_le_mul hK (by omega)
    _ ≤ KS * (p + 1) ^ 4 := Nat.mul_le_mul_left _ h3
    _ ≤ KS * (p + 1) ^ KS := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hKS)

theorem leR_const {K KS p : ℕ} (hK : K ≤ KS) (hKS : 4 ≤ KS) : K ≤ KS * (p + 1) ^ KS := by
  calc K ≤ KS := hK
    _ ≤ KS * 1 := by rw [Nat.mul_one]
    _ ≤ KS * (p + 1) ^ KS := Nat.mul_le_mul_left _ (pow_ge_one p KS)

/-- Bound for the cost `K * (j+1) * (S + 1)` of a `pick`/`roll` with window size `≤ 16` and all
entry sizes `≤ (p+1)^2`. -/
theorem leR_roll {K KS p j S : ℕ} (hK : K ≤ KS) (hj : j + 1 ≤ 16) (hS : S ≤ 16 * (p + 1) ^ 2)
    (hp : 100 ≤ p) (hKS : 8 ≤ KS) : K * (j + 1) * (S + 1) ≤ KS * (p + 1) ^ KS := by
  have h1 : 400 * (p + 1) ^ 2 + 16 ≤ (p + 1) ^ 8 := by
    have h2 : (101 : ℕ) ^ 6 ≤ (p + 1) ^ 6 :=
      Nat.pow_le_pow_left (by omega : (101 : ℕ) ≤ p + 1) 6
    have h3 : (401 : ℕ) ≤ (101 : ℕ) ^ 6 := by norm_num
    have h4 : (p + 1) ^ 2 * 401 ≤ (p + 1) ^ 2 * (p + 1) ^ 6 := Nat.mul_le_mul_left _ (le_trans h3 h2)
    have h5 : (p + 1) ^ 2 * (p + 1) ^ 6 = (p + 1) ^ 8 := by rw [← pow_add]
    have h6 : (p + 1) ^ 2 ≥ 1 := pow_ge_one p 2
    rw [h5] at h4
    nlinarith [h4, h6]
  calc K * (j + 1) * (S + 1) ≤ (KS * 16) * (16 * (p + 1) ^ 2 + 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul hK hj) (by omega)
    _ = KS * (16 * (16 * (p + 1) ^ 2 + 1)) := by rw [Nat.mul_assoc]
    _ ≤ KS * (p + 1) ^ 8 := Nat.mul_le_mul_left _ (by nlinarith [h1])
    _ ≤ KS * (p + 1) ^ KS := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hKS)

theorem Pipe.compMul {main p q : Cmd} {A B D : List Val} {R m : ℕ}
    (h1 : Pipe main p A B (m * R)) (h2 : Pipe main q B D R) :
    Pipe main (.seq p q) A D ((m + 1) * R) := by
  refine Pipe.le (Pipe.comp h1 h2) ?_
  rw [Nat.add_mul, Nat.one_mul]

theorem IPipe.compMul {main p q : Cmd} {A B D : List ℤ} {R m : ℕ}
    (h1 : IPipe main p A B (m * R)) (h2 : IPipe main q B D R) :
    IPipe main (.seq p q) A D ((m + 1) * R) := by
  simpa [IPipe] using Pipe.compMul (main := main)
    (A := A.map Val.int) (B := B.map Val.int) (D := D.map Val.int) h1 h2


/-! ## Val-level helpers for the chain -/

theorem Pipe.rollAt {prog : ℕ → Cmd} {K : ℕ} (main : Cmd)
    (h : ∀ (m : Cmd) (k : ℕ), WordR m (prog k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs.eraseIdx k)
      (fun vs => K * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    {A : List Val} {j : ℕ} (hj : j < A.length) {B : List Val}
    (hB : A.getD j .nil :: A.eraseIdx j = B) :
    Pipe main (prog j) A B (K * (j + 1) * (szl (A.take (j + 1)) + 1)) := by
  rw [← hB]
  exact Pipe.roll main h hj

/-- Membership bound for an explicitly listed window of `int`-values. -/
theorem vsz_mem_int_cons {B : ℕ} {z : ℤ} {l : List Val} (hz : isz z ≤ B)
    (hl : ∀ v ∈ l, vsz v ≤ B) : ∀ v ∈ (Val.int z :: l), vsz v ≤ B := by
  intro v hv
  rcases List.mem_cons.mp hv with h | h
  · subst h; simpa [vsz_int] using hz
  · exact hl v h

theorem szl_take_le16 {A : List Val} {B j : ℕ} (h : ∀ v ∈ A, vsz v ≤ B) (hj : j + 1 ≤ 16) :
    szl (A.take (j + 1)) ≤ 16 * B := by
  refine le_trans (szl_le_len_mul (fun v hv => h v (List.mem_of_mem_take hv))) ?_
  exact Nat.mul_le_mul_right _ (le_trans (List.length_take_le _ _) hj)

theorem leR_add1 {K KS p u v : ℕ} (hK : K ≤ KS) (hu : u ≤ (p + 1) ^ 2) (hv : v ≤ (p + 1) ^ 2)
    (hp : 100 ≤ p) (hKS : 4 ≤ KS) : K * (u + v + 1) ≤ KS * (p + 1) ^ KS := by
  have hX : 3 ≤ (p + 1) ^ 2 := by nlinarith
  have hX1 : 1 ≤ (p + 1) ^ 2 := pow_ge_one p 2
  have hub : u + v + 1 ≤ 2 * (p + 1) ^ 2 + 1 := by nlinarith [hu, hv, hX1]
  calc K * (u + v + 1) ≤ KS * (2 * (p + 1) ^ 2 + 1) := Nat.mul_le_mul hK hub
    _ ≤ KS * (p + 1) ^ 4 := by
        apply Nat.mul_le_mul_left
        have h4 : (p + 1) ^ 4 = (p + 1) ^ 2 * (p + 1) ^ 2 := (sq_le_sq_sq p).symm
        rw [h4]; nlinarith [hX, hX1]
    _ ≤ KS * (p + 1) ^ KS := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hKS)

theorem leR_mulK {K KS p u v : ℕ} (hK : K ≤ KS) (hu : u ≤ (p + 1) ^ 2) (hv : v ≤ (p + 1) ^ 2)
    (hp : 100 ≤ p) (hKS : 4 ≤ KS) : K * u * v ≤ KS * (p + 1) ^ KS := by
  calc K * u * v ≤ KS * (p + 1) ^ 2 * (p + 1) ^ 2 := by
        apply Nat.mul_le_mul
        · exact Nat.mul_le_mul hK hu
        · exact hv
    _ = KS * (p + 1) ^ 4 := by rw [Nat.mul_assoc, sq_le_sq_sq]
    _ ≤ KS * (p + 1) ^ KS := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hKS)

theorem leR_pow {K KS p : ℕ} (hK : K ≤ KS) : K * (p + 1) ^ K ≤ KS * (p + 1) ^ KS :=
  Nat.mul_le_mul hK (Nat.pow_le_pow_right (by omega) hK)

/-- `roll`/`pick` cost bound in the presence of one large list value (`ofList (auWtL …)`). -/
theorem leR_rollV {K KS p j S : ℕ} (hK : K ≤ KS) (hj : j + 1 ≤ 16) (hS : S ≤ 16 * (p + 1) ^ 4)
    (hp : 100 ≤ p) (hKS : 10 ≤ KS) : K * (j + 1) * (S + 1) ≤ KS * (p + 1) ^ KS := by
  have h6 : 16 * (16 * (p + 1) ^ 4 + 1) ≤ (p + 1) ^ 6 := by
    have hp1 : (p + 1) ^ 2 ≥ 101 ^ 2 := Nat.pow_le_pow_left (by omega : (101:ℕ) ≤ p + 1) 2
    have h4 : (p + 1) ^ 6 = (p + 1) ^ 4 * (p + 1) ^ 2 := by rw [← pow_add]
    rw [h4]
    nlinarith [hp1, pow_ge_one p 4]
  calc K * (j + 1) * (S + 1) ≤ KS * 16 * (16 * (p + 1) ^ 4 + 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul hK hj) (by omega)
    _ = KS * (16 * (16 * (p + 1) ^ 4 + 1)) := by rw [Nat.mul_assoc]
    _ ≤ KS * (p + 1) ^ 6 := Nat.mul_le_mul_left _ h6
    _ ≤ KS * (p + 1) ^ KS := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))

/-- `vsz` of `ofList (auWtL …)`: bounded by the number of weights times the weight size bound. -/
theorem szl_ofList_le (l : List Val) : vsz (ofList l) = szl l + (l.length + 1) := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    show vsz (Val.cons a (ofList t)) = szl (a :: t) + ((a :: t).length + 1)
    rw [vsz_cons, szl_cons, ih, List.length_cons]
    ring


/-- General membership bound for an explicitly listed window. -/
theorem vsz_mem_cons {B : ℕ} {a : Val} {l : List Val} (ha : vsz a ≤ B)
    (hl : ∀ v ∈ l, vsz v ≤ B) : ∀ v ∈ (a :: l), vsz v ≤ B := by
  intro v hv
  rcases List.mem_cons.mp hv with h | h
  · subst h; exact ha
  · exact hl v h

theorem sq_le_four (p : ℕ) : (p + 1) ^ 2 ≤ (p + 1) ^ 4 :=
  Nat.pow_le_pow_right (by omega) (by omega)



/-- Absorbing a factor `n ≤ (p+1)^8` into a cost of the shape `K * (p+1)^K`. -/
theorem mul_pow_absorb {n K p : ℕ} (h : n ≤ (p + 1) ^ 8) :
    n * (K * (p + 1) ^ K) ≤ (K + 8) * (p + 1) ^ (K + 8) := by
  have e1 : (p + 1) ^ (K + 8) = (p + 1) ^ K * (p + 1) ^ 8 := pow_add _ _ _
  have e2 : (p + 1) ^ 8 * (p + 1) ^ K = (p + 1) ^ (K + 8) := by rw [e1, Nat.mul_comm]
  calc n * (K * (p + 1) ^ K) = K * (n * (p + 1) ^ K) := by ring
    _ ≤ K * ((p + 1) ^ 8 * (p + 1) ^ K) :=
          Nat.mul_le_mul le_rfl (Nat.mul_le_mul h le_rfl)
    _ = K * (p + 1) ^ (K + 8) := by rw [e2]
    _ ≤ (K + 8) * (p + 1) ^ (K + 8) := Nat.mul_le_mul (by omega) le_rfl

/-! ## The record word -/

theorem auRecWord (hk : HvdH.KernelLib) (hi : HvdH.IntLib) (hl : HvdH.LayoutLib)
    (hElem : ∃ (progE : HvdH.Cmd) (KE : ℕ), ∀ (main : HvdH.Cmd) (p α t : ℕ) (C : ℤ) (i : ℕ),
      HvdH.isz C ≤ Work.Resample.auSZ p → HvdH.isz ((i : ℕ) : ℤ) ≤ Work.Resample.auSZ p →
      (1 ≤ t) → (t < 2 ^ p) → (α ≤ 2 ^ p) →
      (C + (t : ℤ) * (i : ℤ)) ^ 2 ≤ (2 : ℤ) ^ (4 * p + 8) →
      Work.Resample.Pipe main progE
        [HvdH.Val.cons (HvdH.Val.int (i : ℤ)) (HvdH.Val.int (Work.Resample.auPi p)),
          HvdH.Val.int C, HvdH.Val.int (t : ℤ), HvdH.Val.int (p : ℤ), HvdH.Val.int (α : ℤ)]
        [HvdH.Val.int (Work.Resample.auWt p α t ((C + (t : ℤ) * (i : ℤ)) ^ 2)),
          HvdH.Val.int C, HvdH.Val.int (t : ℤ), HvdH.Val.int (p : ℤ), HvdH.Val.int (α : ℤ)]
        (KE * (p + 1) ^ KE)) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p α s t k : ℕ) (hs : 2 ≤ s) (hst : s < t)
      (htp : t < 2 ^ p) (hα : 2 ≤ α) (hp : 100 ≤ p) (hαp : α ^ 2 < p) (hklt : k < t)
      (hWtsz : ∀ (N : ℤ), 0 ≤ N → HvdH.isz (Work.Resample.auWt p α t N) ≤ Work.Resample.auSZ p)
      (hNbd : ∀ i < Work.Resample.auL p α, 0 ≤ Work.Resample.auNsq p α s t k i ∧
        Work.Resample.auNsq p α s t k i ≤ (2 : ℤ) ^ (4 * p + 8)),
      Work.Resample.Pipe main prog
        (HvdH.Val.cons (HvdH.Val.int (k : ℤ)) (HvdH.Val.int (Work.Resample.auPi p)) ::
          [HvdH.Val.int (p : ℤ), HvdH.Val.int (α : ℤ), HvdH.Val.int (s : ℤ),
            HvdH.Val.int (t : ℤ), HvdH.Val.int (Work.Resample.auPi p)])
        (Work.Resample.auRec p α s t k ::
          [HvdH.Val.int (p : ℤ), HvdH.Val.int (α : ℤ), HvdH.Val.int (s : ℤ),
            HvdH.Val.int (t : ℤ), HvdH.Val.int (Work.Resample.auPi p)])
        (K * (p + 1) ^ K) := by
  -- the library words
  obtain ⟨pDup, kDup, hDup⟩ := hk.dup
  obtain ⟨pDrop, kDrop, hDrop⟩ := hk.drop
  obtain ⟨pSwap, kSwap, hSwap⟩ := hk.swap
  obtain ⟨pPick, kPick, hPick⟩ := hk.pick
  obtain ⟨pRoll, kRoll, hRoll⟩ := hk.roll
  obtain ⟨pUncons, kUncons, hUncons⟩ := hk.unconsV
  obtain ⟨pConsV, kConsV, hConsV⟩ := hk.consV
  obtain ⟨pMul, kMul, hMul⟩ := hi.mulS
  obtain ⟨pSub, kSub, hSub⟩ := hi.sub
  -- the pieces
  obtain ⟨pML, kML, hML⟩ := auMLWord hk hi
  obtain ⟨pKW, kKW, hKW⟩ := auKWord hk hi
  obtain ⟨pB, kB, hB⟩ := auWtLWord hk hl hElem
  -- the constant
  let KS : ℕ := kDup + kDrop + kSwap + kPick + kRoll + kUncons + kConsV + kMul + kSub
    + kML + kKW + kB + 20
  have hKS4 : 4 ≤ KS := by simp only [KS]; omega
  have hKS10 : 10 ≤ KS := by simp only [KS]; omega
  have hKS_dup : kDup ≤ KS := by simp only [KS]; omega
  have hKS_drop : kDrop ≤ KS := by simp only [KS]; omega
  have hKS_swap : kSwap ≤ KS := by simp only [KS]; omega
  have hKS_pick : kPick ≤ KS := by simp only [KS]; omega
  have hKS_roll : kRoll ≤ KS := by simp only [KS]; omega
  have hKS_uncons : kUncons ≤ KS := by simp only [KS]; omega
  have hKS_cons : kConsV ≤ KS := by simp only [KS]; omega
  have hKS_mul : kMul ≤ KS := by simp only [KS]; omega
  have hKS_sub : kSub ≤ KS := by simp only [KS]; omega
  have hKS_ML : kML ≤ KS := by simp only [KS]; omega
  have hKS_KW : kKW ≤ KS := by simp only [KS]; omega
  have hKS_B : kB ≤ KS := by simp only [KS]; omega
  -- the program
  let P1 : Cmd := pUncons
  let P2 : Cmd := .seq P1 (pPick 3)
  let P3 : Cmd := .seq P2 (pPick 3)
  let P4 : Cmd := .seq P3 pML
  let P5 : Cmd := .seq P4 pSwap
  let P6 : Cmd := .seq P5 (pPick 7)
  let P7 : Cmd := .seq P6 (pPick 7)
  let P8 : Cmd := .seq P7 (pPick 4)
  let P9 : Cmd := .seq P8 pKW
  let P10 : Cmd := .seq P9 pDup
  let P11 : Cmd := .seq P10 (pPick 2)
  let P12 : Cmd := .seq P11 pSub
  let P13 : Cmd := .seq P12 (pPick 1)
  let P14 : Cmd := .seq P13 (pPick 11)
  let P15 : Cmd := .seq P14 pMul
  let P16 : Cmd := .seq P15 (pPick 5)
  let P17 : Cmd := .seq P16 (pPick 12)
  let P18 : Cmd := .seq P17 pMul
  let P19 : Cmd := .seq P18 pSwap
  let P20 : Cmd := .seq P19 pSub
  let P21 : Cmd := .seq P20 (pPick 6)
  let P22 : Cmd := .seq P21 (pPick 11)
  let P23 : Cmd := .seq P22 pMul
  let P24 : Cmd := .seq P23 pSwap
  let P25 : Cmd := .seq P24 pSub
  let P26 : Cmd := .seq P25 (pRoll 1)
  let P27 : Cmd := .seq P26 (pPick 9)
  let P28 : Cmd := .seq P27 (pPick 9)
  let P29 : Cmd := .seq P28 (pPick 13)
  let P30 : Cmd := .seq P29 (pRoll 4)
  let P31 : Cmd := .seq P30 (pRoll 10)
  let P32 : Cmd := .seq P31 (pRoll 8)
  let P33 : Cmd := .seq P32 pB
  let P34 : Cmd := .seq P33 (pRoll 6)
  let P35 : Cmd := .seq P34 pDrop
  let P36 : Cmd := .seq P35 (pRoll 6)
  let P37 : Cmd := .seq P36 pDrop
  let P38 : Cmd := .seq P37 (pRoll 6)
  let P39 : Cmd := .seq P38 pDrop
  let P40 : Cmd := .seq P39 (pRoll 6)
  let P41 : Cmd := .seq P40 pDrop
  let P42 : Cmd := .seq P41 (pRoll 1)
  let P43 : Cmd := .seq P42 pDrop
  let P44 : Cmd := .seq P43 (pRoll 1)
  let P45 : Cmd := .seq P44 pDrop
  let P46 : Cmd := .seq P45 (pRoll 1)
  let P47 : Cmd := .seq P46 pDrop
  let P48 : Cmd := .seq P47 (pRoll 1)
  let P49 : Cmd := .seq P48 pDrop
  let P50 : Cmd := .seq P49 (pRoll 1)
  let P51 : Cmd := .seq P50 pConsV
  refine ⟨P51, KS + 8, ?_⟩
  intro main p α s t k hs hst htp hα hp hαp hklt hWtsz hNbd
  let RB : ℕ := KS * (p + 1) ^ KS
  -- facts from `auRecArith`
  obtain ⟨hAr, -, -⟩ := auRecArith p α s t k hs hst htp hα hp hαp hklt
  obtain ⟨hPiS, hMle, hLle, hLsz, hKksz, hKk1sz, hCsz, hksz, hssz, htsz, hpsz, hasz, hI⟩ := hAr
  have hSZsq : auSZ p ≤ (p + 1) ^ 2 := by simp only [auSZ]; nlinarith
  -- the values
  let kI : ℤ := (k : ℤ)
  let pI : ℤ := (p : ℤ)
  let aI : ℤ := (α : ℤ)
  let sI : ℤ := (s : ℤ)
  let tI : ℤ := (t : ℤ)
  let piI : ℤ := auPi p
  let mI : ℤ := ((auM p α : ℕ) : ℤ)
  let LI : ℤ := ((auL p α : ℕ) : ℤ)
  let KkI : ℤ := ((auK s t k : ℕ) : ℤ)
  let Kk1I : ℤ := ((auK s t (k + 1) : ℕ) : ℤ)
  let slI : ℤ := ((auK s t (k + 1) : ℕ) : ℤ) - ((auK s t k : ℕ) : ℤ)
  let tKkI : ℤ := (t : ℤ) * ((auK s t k : ℕ) : ℤ)
  let tmI : ℤ := (t : ℤ) * ((auM p α : ℕ) : ℤ)
  let skI : ℤ := (s : ℤ) * (k : ℤ)
  let C1I : ℤ := (t : ℤ) * ((auK s t k : ℕ) : ℤ) - (t : ℤ) * ((auM p α : ℕ) : ℤ)
  let CI : ℤ := auC p α s t k
  let recI : Val := ofList (auWtL p α s t k)
  -- sharp size bounds
  have hs_tI : isz tI ≤ p + 2 := by
    show isz ((t : ℕ) : ℤ) ≤ p + 2
    rw [isz, Int.natAbs_natCast]
    have h := Nat.size_le.mpr htp
    omega
  have hs_kI : isz kI ≤ p + 2 := by
    show isz ((k : ℕ) : ℤ) ≤ p + 2
    rw [isz, Int.natAbs_natCast]
    have h := Nat.size_le.mpr (lt_of_lt_of_le hklt (le_of_lt htp))
    omega
  have hs_sI : isz sI ≤ p + 2 := by
    show isz ((s : ℕ) : ℤ) ≤ p + 2
    rw [isz, Int.natAbs_natCast]
    have h := Nat.size_le.mpr (lt_of_lt_of_le hst (le_of_lt htp))
    omega
  have hs_pI : isz pI ≤ p + 2 := by
    show isz ((p : ℕ) : ℤ) ≤ p + 2
    rw [isz, Int.natAbs_natCast]
    have h := Nat.size_le.mpr (Nat.lt_two_pow_self (n := p))
    omega
  have hs_aI : isz aI ≤ p + 2 := by
    show isz ((α : ℕ) : ℤ) ≤ p + 2
    rw [isz, Int.natAbs_natCast]
    have hαp' : α < p := by nlinarith [hαp, hα]
    have h := Nat.size_le.mpr (lt_of_lt_of_le hαp' (le_of_lt (Nat.lt_two_pow_self (n := p))))
    omega
  have hs_piI : isz piI ≤ 10 * p + 400 := by simpa only [auSZ] using hPiS
  have hs_LI : isz LI ≤ 10 * p + 400 := by simpa only [auSZ] using hLsz
  have hs_KkI : isz KkI ≤ 10 * p + 400 := by simpa only [auSZ] using hKksz
  have hs_Kk1I : isz Kk1I ≤ 10 * p + 400 := by simpa only [auSZ] using hKk1sz
  have hs_mI : isz mI ≤ p + 4 := by
    have hp2 : p < 2 ^ p := Nat.lt_two_pow_self
    have h4 : 2 * p < 2 ^ (p + 1) := by
      have h := Nat.mul_lt_mul_of_pos_left hp2 (by norm_num : 0 < 2)
      calc 2 * p < 2 * 2 ^ p := h
        _ = 2 ^ (p + 1) := by rw [pow_succ]; ring
    have h5 : auM p α < 2 ^ (p + 2) :=
      lt_of_lt_of_le (lt_of_le_of_lt hMle h4) (Nat.pow_le_pow_right (by norm_num) (by omega))
    have h6 : (auM p α).size ≤ p + 2 := Nat.size_le.mpr h5
    show isz ((auM p α : ℕ) : ℤ) ≤ p + 4
    rw [isz, Int.natAbs_natCast]
    omega
  have hs_tKkI : isz tKkI ≤ 11 * p + 402 := by
    have h := isz_mul_le tI KkI
    show isz (tI * KkI) ≤ 11 * p + 402
    linarith [h, hs_tI, hs_KkI]
  have hs_tmI : isz tmI ≤ 2 * p + 6 := by
    have h := isz_mul_le tI mI
    show isz (tI * mI) ≤ 2 * p + 6
    linarith [h, hs_tI, hs_mI]
  have hs_skI : isz skI ≤ 2 * p + 4 := by
    have h := isz_mul_le sI kI
    show isz (sI * kI) ≤ 2 * p + 4
    linarith [h, hs_sI, hs_kI]
  have hs_C1I : isz C1I ≤ 11 * p + 403 := by
    have h := isz_sub_le tKkI tmI
    have h2 : max (isz tKkI) (isz tmI) ≤ 11 * p + 402 := max_le hs_tKkI (by omega)
    show isz (tKkI - tmI) ≤ 11 * p + 403
    linarith [h, h2]
  have hs_CI : isz CI ≤ 11 * p + 404 := by
    have h := isz_sub_le C1I skI
    have h2 : max (isz C1I) (isz skI) ≤ 11 * p + 403 := max_le hs_C1I (by omega)
    show isz (C1I - skI) ≤ 11 * p + 404
    linarith [h, h2]
  have hs_slI : isz slI ≤ 10 * p + 401 := by
    have h := isz_sub_le Kk1I KkI
    have h2 : max (isz Kk1I) (isz KkI) ≤ 10 * p + 400 := max_le hs_Kk1I hs_KkI
    show isz (Kk1I - KkI) ≤ 10 * p + 401
    linarith [h, h2]
  -- numeric facts, in `p` only
  have hN2 : 10 * p + 400 ≤ (p + 1) ^ 2 := by nlinarith
  have hN3 : 11 * p + 402 ≤ (p + 1) ^ 2 := by nlinarith
  have hN4 : 11 * p + 404 ≤ (p + 1) ^ 2 := by nlinarith
  have hN5 : p + 4 ≤ (p + 1) ^ 2 := by nlinarith
  have hN6 : 2 * p + 6 ≤ (p + 1) ^ 2 := by nlinarith
  have hN7 : 10 * p + 401 ≤ (p + 1) ^ 2 := by nlinarith
  have hN8 : p + 2 ≤ (p + 1) ^ 2 := by nlinarith
  have hN9 : 11 * p + 403 ≤ (p + 1) ^ 2 := by nlinarith
  have hN10 : 2 * p + 4 ≤ (p + 1) ^ 2 := by nlinarith
  -- usable size bounds
  have hb_kI : isz kI ≤ (p + 1) ^ 2 := le_trans hs_kI hN8
  have hb_pI : isz pI ≤ (p + 1) ^ 2 := le_trans hs_pI hN8
  have hb_aI : isz aI ≤ (p + 1) ^ 2 := le_trans hs_aI hN8
  have hb_sI : isz sI ≤ (p + 1) ^ 2 := le_trans hs_sI hN8
  have hb_tI : isz tI ≤ (p + 1) ^ 2 := le_trans hs_tI hN8
  have hb_piI : isz piI ≤ (p + 1) ^ 2 := le_trans hs_piI hN2
  have hb_LI : isz LI ≤ (p + 1) ^ 2 := le_trans hs_LI hN2
  have hb_KkI : isz KkI ≤ (p + 1) ^ 2 := le_trans hs_KkI hN2
  have hb_Kk1I : isz Kk1I ≤ (p + 1) ^ 2 := le_trans hs_Kk1I hN2
  have hb_mI : isz mI ≤ (p + 1) ^ 2 := le_trans hs_mI hN5
  have hb_tKkI : isz tKkI ≤ (p + 1) ^ 2 := le_trans hs_tKkI hN3
  have hb_tmI : isz tmI ≤ (p + 1) ^ 2 := le_trans hs_tmI hN6
  have hb_skI : isz skI ≤ (p + 1) ^ 2 := le_trans hs_skI hN10
  have hb_C1I : isz C1I ≤ (p + 1) ^ 2 := le_trans hs_C1I hN9
  have hb_CI : isz CI ≤ (p + 1) ^ 2 := le_trans hs_CI hN4
  have hb_slI : isz slI ≤ (p + 1) ^ 2 := le_trans hs_slI hN7
  have hrecI : vsz recI ≤ (p + 1) ^ 4 := by
    have h1 : szl (auWtL p α s t k) ≤ auL p α * auSZ p := by
      have hmem : ∀ v ∈ auWtL p α s t k, vsz v ≤ auSZ p := by
        intro v hv
        rw [auWtL_eq, List.mem_map] at hv
        obtain ⟨i, hi, rfl⟩ := hv
        rw [vsz_int]
        exact hWtsz _ (hNbd i (List.mem_range.mp hi)).1
      have h2 := szl_le_len_mul hmem
      rwa [auWtL_eq, List.length_map, List.length_range] at h2
    have h3 : szl (auWtL p α s t k) ≤ (4 * p + 1) * (10 * p + 400) :=
      le_trans h1 (Nat.mul_le_mul hLle (le_of_eq rfl))
    have hN11 : (4 * p + 1) * (10 * p + 400) + (4 * p + 1 + 1) ≤ (p + 1) ^ 4 := by nlinarith
    have h4 : szl (auWtL p α s t k) + (auL p α + 1)
        ≤ (4 * p + 1) * (10 * p + 400) + (4 * p + 1 + 1) :=
      Nat.add_le_add h3 (by omega)
    simp only [recI, auWtL_eq, szl_ofList_le, List.length_map, List.length_range]
    exact le_trans h4 hN11
  -- the windows and the chain
  -- windows
  let W0 : List Val := (Val.cons (Val.int (k : ℤ)) (Val.int (auPi p)) :: [Val.int (p : ℤ), Val.int (α : ℤ), Val.int (s : ℤ), Val.int (t : ℤ), Val.int (auPi p)])
  -- windows
  let W1 : List Val := [.int ((k : ℤ)), .int (auPi p), .int ((p : ℤ)), .int ((α : ℤ)), .int ((s : ℤ)), .int ((t : ℤ)), .int (auPi p)]
  let W2 : List Val := [.int ((α : ℤ)), .int ((k : ℤ)), .int (auPi p), .int ((p : ℤ)), .int ((α : ℤ)), .int ((s : ℤ)), .int ((t : ℤ)), .int (auPi p)]
  let W3 : List Val := [.int ((p : ℤ)), .int ((α : ℤ)), .int ((k : ℤ)), .int (auPi p), .int ((p : ℤ)), .int ((α : ℤ)), .int ((s : ℤ)), .int ((t : ℤ)), .int (auPi p)]
  let W4 : List Val := [.int (((auM p α : ℕ) : ℤ)), .int (((auL p α : ℕ) : ℤ)), .int ((k : ℤ)), .int (auPi p), .int ((p : ℤ)), .int ((α : ℤ)), .int ((s : ℤ)), .int ((t : ℤ)), .int (auPi p)]
  let W5 : List Val := [.int (((auL p α : ℕ) : ℤ)), .int (((auM p α : ℕ) : ℤ)), .int ((k : ℤ)), .int (auPi p), .int ((p : ℤ)), .int ((α : ℤ)), .int ((s : ℤ)), .int ((t : ℤ)), .int (auPi p)]
  let W6 : List Val := [.int ((t : ℤ)), .int (((auL p α : ℕ) : ℤ)), .int (((auM p α : ℕ) : ℤ)), .int ((k : ℤ)), .int (auPi p), .int ((p : ℤ)), .int ((α : ℤ)), .int ((s : ℤ)), .int ((t : ℤ)), .int (auPi p)]
  let W7 : List Val := [.int ((s : ℤ)), .int ((t : ℤ)), .int (((auL p α : ℕ) : ℤ)), .int (((auM p α : ℕ) : ℤ)), .int ((k : ℤ)), .int (auPi p), .int ((p : ℤ)), .int ((α : ℤ)), .int ((s : ℤ)), .int ((t : ℤ)), .int (auPi p)]
  let W8 : List Val := [.int ((k : ℤ)), .int ((s : ℤ)), .int ((t : ℤ)), .int (((auL p α : ℕ) : ℤ)), .int (((auM p α : ℕ) : ℤ)), .int ((k : ℤ)), .int (auPi p), .int ((p : ℤ)), .int ((α : ℤ)), .int ((s : ℤ)), .int ((t : ℤ)), .int (auPi p)]
  let W9 : List Val := [.int (((auK s t k : ℕ) : ℤ)), .int (((auK s t (k+1) : ℕ) : ℤ)), .int (((auL p α : ℕ) : ℤ)), .int (((auM p α : ℕ) : ℤ)), .int ((k : ℤ)), .int (auPi p), .int ((p : ℤ)), .int ((α : ℤ)), .int ((s : ℤ)), .int ((t : ℤ)), .int (auPi p)]
  let W10 : List Val := [.int (((auK s t k : ℕ) : ℤ)), .int (((auK s t k : ℕ) : ℤ)), .int (((auK s t (k+1) : ℕ) : ℤ)), .int (((auL p α : ℕ) : ℤ)), .int (((auM p α : ℕ) : ℤ)), .int ((k : ℤ)), .int (auPi p), .int ((p : ℤ)), .int ((α : ℤ)), .int ((s : ℤ)), .int ((t : ℤ)), .int (auPi p)]
  let W11 : List Val := [.int (((auK s t (k+1) : ℕ) : ℤ)), .int (((auK s t k : ℕ) : ℤ)), .int (((auK s t k : ℕ) : ℤ)), .int (((auK s t (k+1) : ℕ) : ℤ)), .int (((auL p α : ℕ) : ℤ)), .int (((auM p α : ℕ) : ℤ)), .int ((k : ℤ)), .int (auPi p), .int ((p : ℤ)), .int ((α : ℤ)), .int ((s : ℤ)), .int ((t : ℤ)), .int (auPi p)]
  let W12 : List Val := [.int (((auK s t (k+1) : ℕ) : ℤ) - ((auK s t k : ℕ) : ℤ)), .int (((auK s t k : ℕ) : ℤ)), .int (((auK s t (k+1) : ℕ) : ℤ)), .int (((auL p α : ℕ) : ℤ)), .int (((auM p α : ℕ) : ℤ)), .int ((k : ℤ)), .int (auPi p), .int ((p : ℤ)), .int ((α : ℤ)), .int ((s : ℤ)), .int ((t : ℤ)), .int (auPi p)]
  let W13 : List Val := [.int (((auK s t k : ℕ) : ℤ)), .int (((auK s t (k+1) : ℕ) : ℤ) - ((auK s t k : ℕ) : ℤ)), .int (((auK s t k : ℕ) : ℤ)), .int (((auK s t (k+1) : ℕ) : ℤ)), .int (((auL p α : ℕ) : ℤ)), .int (((auM p α : ℕ) : ℤ)), .int ((k : ℤ)), .int (auPi p), .int ((p : ℤ)), .int ((α : ℤ)), .int ((s : ℤ)), .int ((t : ℤ)), .int (auPi p)]
  let W14 : List Val := [.int ((t : ℤ)), .int (((auK s t k : ℕ) : ℤ)), .int (((auK s t (k+1) : ℕ) : ℤ) - ((auK s t k : ℕ) : ℤ)), .int (((auK s t k : ℕ) : ℤ)), .int (((auK s t (k+1) : ℕ) : ℤ)), .int (((auL p α : ℕ) : ℤ)), .int (((auM p α : ℕ) : ℤ)), .int ((k : ℤ)), .int (auPi p), .int ((p : ℤ)), .int ((α : ℤ)), .int ((s : ℤ)), .int ((t : ℤ)), .int (auPi p)]
  let W15 : List Val := [.int ((t : ℤ) * ((auK s t k : ℕ) : ℤ)), .int (((auK s t (k+1) : ℕ) : ℤ) - ((auK s t k : ℕ) : ℤ)), .int (((auK s t k : ℕ) : ℤ)), .int (((auK s t (k+1) : ℕ) : ℤ)), .int (((auL p α : ℕ) : ℤ)), .int (((auM p α : ℕ) : ℤ)), .int ((k : ℤ)), .int (auPi p), .int ((p : ℤ)), .int ((α : ℤ)), .int ((s : ℤ)), .int ((t : ℤ)), .int (auPi p)]
  let W16 : List Val := [.int (((auM p α : ℕ) : ℤ)), .int ((t : ℤ) * ((auK s t k : ℕ) : ℤ)), .int (((auK s t (k+1) : ℕ) : ℤ) - ((auK s t k : ℕ) : ℤ)), .int (((auK s t k : ℕ) : ℤ)), .int (((auK s t (k+1) : ℕ) : ℤ)), .int (((auL p α : ℕ) : ℤ)), .int (((auM p α : ℕ) : ℤ)), .int ((k : ℤ)), .int (auPi p), .int ((p : ℤ)), .int ((α : ℤ)), .int ((s : ℤ)), .int ((t : ℤ)), .int (auPi p)]
  let W17 : List Val := [.int ((t : ℤ)), .int (((auM p α : ℕ) : ℤ)), .int ((t : ℤ) * ((auK s t k : ℕ) : ℤ)), .int (((auK s t (k+1) : ℕ) : ℤ) - ((auK s t k : ℕ) : ℤ)), .int (((auK s t k : ℕ) : ℤ)), .int (((auK s t (k+1) : ℕ) : ℤ)), .int (((auL p α : ℕ) : ℤ)), .int (((auM p α : ℕ) : ℤ)), .int ((k : ℤ)), .int (auPi p), .int ((p : ℤ)), .int ((α : ℤ)), .int ((s : ℤ)), .int ((t : ℤ)), .int (auPi p)]
  let W18 : List Val := [.int ((t : ℤ) * ((auM p α : ℕ) : ℤ)), .int ((t : ℤ) * ((auK s t k : ℕ) : ℤ)), .int (((auK s t (k+1) : ℕ) : ℤ) - ((auK s t k : ℕ) : ℤ)), .int (((auK s t k : ℕ) : ℤ)), .int (((auK s t (k+1) : ℕ) : ℤ)), .int (((auL p α : ℕ) : ℤ)), .int (((auM p α : ℕ) : ℤ)), .int ((k : ℤ)), .int (auPi p), .int ((p : ℤ)), .int ((α : ℤ)), .int ((s : ℤ)), .int ((t : ℤ)), .int (auPi p)]
  let W19 : List Val := [.int ((t : ℤ) * ((auK s t k : ℕ) : ℤ)), .int ((t : ℤ) * ((auM p α : ℕ) : ℤ)), .int (((auK s t (k+1) : ℕ) : ℤ) - ((auK s t k : ℕ) : ℤ)), .int (((auK s t k : ℕ) : ℤ)), .int (((auK s t (k+1) : ℕ) : ℤ)), .int (((auL p α : ℕ) : ℤ)), .int (((auM p α : ℕ) : ℤ)), .int ((k : ℤ)), .int (auPi p), .int ((p : ℤ)), .int ((α : ℤ)), .int ((s : ℤ)), .int ((t : ℤ)), .int (auPi p)]
  let W20 : List Val := [.int ((t : ℤ) * ((auK s t k : ℕ) : ℤ) - (t : ℤ) * ((auM p α : ℕ) : ℤ)), .int (((auK s t (k+1) : ℕ) : ℤ) - ((auK s t k : ℕ) : ℤ)), .int (((auK s t k : ℕ) : ℤ)), .int (((auK s t (k+1) : ℕ) : ℤ)), .int (((auL p α : ℕ) : ℤ)), .int (((auM p α : ℕ) : ℤ)), .int ((k : ℤ)), .int (auPi p), .int ((p : ℤ)), .int ((α : ℤ)), .int ((s : ℤ)), .int ((t : ℤ)), .int (auPi p)]
  let W21 : List Val := [.int ((k : ℤ)), .int ((t : ℤ) * ((auK s t k : ℕ) : ℤ) - (t : ℤ) * ((auM p α : ℕ) : ℤ)), .int (((auK s t (k+1) : ℕ) : ℤ) - ((auK s t k : ℕ) : ℤ)), .int (((auK s t k : ℕ) : ℤ)), .int (((auK s t (k+1) : ℕ) : ℤ)), .int (((auL p α : ℕ) : ℤ)), .int (((auM p α : ℕ) : ℤ)), .int ((k : ℤ)), .int (auPi p), .int ((p : ℤ)), .int ((α : ℤ)), .int ((s : ℤ)), .int ((t : ℤ)), .int (auPi p)]
  let W22 : List Val := [.int ((s : ℤ)), .int ((k : ℤ)), .int ((t : ℤ) * ((auK s t k : ℕ) : ℤ) - (t : ℤ) * ((auM p α : ℕ) : ℤ)), .int (((auK s t (k+1) : ℕ) : ℤ) - ((auK s t k : ℕ) : ℤ)), .int (((auK s t k : ℕ) : ℤ)), .int (((auK s t (k+1) : ℕ) : ℤ)), .int (((auL p α : ℕ) : ℤ)), .int (((auM p α : ℕ) : ℤ)), .int ((k : ℤ)), .int (auPi p), .int ((p : ℤ)), .int ((α : ℤ)), .int ((s : ℤ)), .int ((t : ℤ)), .int (auPi p)]
  let W23 : List Val := [.int ((s : ℤ) * (k : ℤ)), .int ((t : ℤ) * ((auK s t k : ℕ) : ℤ) - (t : ℤ) * ((auM p α : ℕ) : ℤ)), .int (((auK s t (k+1) : ℕ) : ℤ) - ((auK s t k : ℕ) : ℤ)), .int (((auK s t k : ℕ) : ℤ)), .int (((auK s t (k+1) : ℕ) : ℤ)), .int (((auL p α : ℕ) : ℤ)), .int (((auM p α : ℕ) : ℤ)), .int ((k : ℤ)), .int (auPi p), .int ((p : ℤ)), .int ((α : ℤ)), .int ((s : ℤ)), .int ((t : ℤ)), .int (auPi p)]
  let W24 : List Val := [.int ((t : ℤ) * ((auK s t k : ℕ) : ℤ) - (t : ℤ) * ((auM p α : ℕ) : ℤ)), .int ((s : ℤ) * (k : ℤ)), .int (((auK s t (k+1) : ℕ) : ℤ) - ((auK s t k : ℕ) : ℤ)), .int (((auK s t k : ℕ) : ℤ)), .int (((auK s t (k+1) : ℕ) : ℤ)), .int (((auL p α : ℕ) : ℤ)), .int (((auM p α : ℕ) : ℤ)), .int ((k : ℤ)), .int (auPi p), .int ((p : ℤ)), .int ((α : ℤ)), .int ((s : ℤ)), .int ((t : ℤ)), .int (auPi p)]
  let W25 : List Val := [.int (auC p α s t k), .int (((auK s t (k+1) : ℕ) : ℤ) - ((auK s t k : ℕ) : ℤ)), .int (((auK s t k : ℕ) : ℤ)), .int (((auK s t (k+1) : ℕ) : ℤ)), .int (((auL p α : ℕ) : ℤ)), .int (((auM p α : ℕ) : ℤ)), .int ((k : ℤ)), .int (auPi p), .int ((p : ℤ)), .int ((α : ℤ)), .int ((s : ℤ)), .int ((t : ℤ)), .int (auPi p)]
  let W26 : List Val := [.int (((auK s t (k+1) : ℕ) : ℤ) - ((auK s t k : ℕ) : ℤ)), .int (auC p α s t k), .int (((auK s t k : ℕ) : ℤ)), .int (((auK s t (k+1) : ℕ) : ℤ)), .int (((auL p α : ℕ) : ℤ)), .int (((auM p α : ℕ) : ℤ)), .int ((k : ℤ)), .int (auPi p), .int ((p : ℤ)), .int ((α : ℤ)), .int ((s : ℤ)), .int ((t : ℤ)), .int (auPi p)]
  let W27 : List Val := [.int ((α : ℤ)), .int (((auK s t (k+1) : ℕ) : ℤ) - ((auK s t k : ℕ) : ℤ)), .int (auC p α s t k), .int (((auK s t k : ℕ) : ℤ)), .int (((auK s t (k+1) : ℕ) : ℤ)), .int (((auL p α : ℕ) : ℤ)), .int (((auM p α : ℕ) : ℤ)), .int ((k : ℤ)), .int (auPi p), .int ((p : ℤ)), .int ((α : ℤ)), .int ((s : ℤ)), .int ((t : ℤ)), .int (auPi p)]
  let W28 : List Val := [.int ((p : ℤ)), .int ((α : ℤ)), .int (((auK s t (k+1) : ℕ) : ℤ) - ((auK s t k : ℕ) : ℤ)), .int (auC p α s t k), .int (((auK s t k : ℕ) : ℤ)), .int (((auK s t (k+1) : ℕ) : ℤ)), .int (((auL p α : ℕ) : ℤ)), .int (((auM p α : ℕ) : ℤ)), .int ((k : ℤ)), .int (auPi p), .int ((p : ℤ)), .int ((α : ℤ)), .int ((s : ℤ)), .int ((t : ℤ)), .int (auPi p)]
  let W29 : List Val := [.int ((t : ℤ)), .int ((p : ℤ)), .int ((α : ℤ)), .int (((auK s t (k+1) : ℕ) : ℤ) - ((auK s t k : ℕ) : ℤ)), .int (auC p α s t k), .int (((auK s t k : ℕ) : ℤ)), .int (((auK s t (k+1) : ℕ) : ℤ)), .int (((auL p α : ℕ) : ℤ)), .int (((auM p α : ℕ) : ℤ)), .int ((k : ℤ)), .int (auPi p), .int ((p : ℤ)), .int ((α : ℤ)), .int ((s : ℤ)), .int ((t : ℤ)), .int (auPi p)]
  let W30 : List Val := [.int (auC p α s t k), .int ((t : ℤ)), .int ((p : ℤ)), .int ((α : ℤ)), .int (((auK s t (k+1) : ℕ) : ℤ) - ((auK s t k : ℕ) : ℤ)), .int (((auK s t k : ℕ) : ℤ)), .int (((auK s t (k+1) : ℕ) : ℤ)), .int (((auL p α : ℕ) : ℤ)), .int (((auM p α : ℕ) : ℤ)), .int ((k : ℤ)), .int (auPi p), .int ((p : ℤ)), .int ((α : ℤ)), .int ((s : ℤ)), .int ((t : ℤ)), .int (auPi p)]
  let W31 : List Val := [.int (auPi p), .int (auC p α s t k), .int ((t : ℤ)), .int ((p : ℤ)), .int ((α : ℤ)), .int (((auK s t (k+1) : ℕ) : ℤ) - ((auK s t k : ℕ) : ℤ)), .int (((auK s t k : ℕ) : ℤ)), .int (((auK s t (k+1) : ℕ) : ℤ)), .int (((auL p α : ℕ) : ℤ)), .int (((auM p α : ℕ) : ℤ)), .int ((k : ℤ)), .int ((p : ℤ)), .int ((α : ℤ)), .int ((s : ℤ)), .int ((t : ℤ)), .int (auPi p)]
  let W32 : List Val := [.int (((auL p α : ℕ) : ℤ)), .int (auPi p), .int (auC p α s t k), .int ((t : ℤ)), .int ((p : ℤ)), .int ((α : ℤ)), .int (((auK s t (k+1) : ℕ) : ℤ) - ((auK s t k : ℕ) : ℤ)), .int (((auK s t k : ℕ) : ℤ)), .int (((auK s t (k+1) : ℕ) : ℤ)), .int (((auM p α : ℕ) : ℤ)), .int ((k : ℤ)), .int ((p : ℤ)), .int ((α : ℤ)), .int ((s : ℤ)), .int ((t : ℤ)), .int (auPi p)]
  let W33 : List Val := [recI, .int (auC p α s t k), .int ((t : ℤ)), .int ((p : ℤ)), .int ((α : ℤ)), .int (((auK s t (k+1) : ℕ) : ℤ) - ((auK s t k : ℕ) : ℤ)), .int (((auK s t k : ℕ) : ℤ)), .int (((auK s t (k+1) : ℕ) : ℤ)), .int (((auM p α : ℕ) : ℤ)), .int ((k : ℤ)), .int ((p : ℤ)), .int ((α : ℤ)), .int ((s : ℤ)), .int ((t : ℤ)), .int (auPi p)]
  let W34 : List Val := [.int (((auK s t k : ℕ) : ℤ)), recI, .int (auC p α s t k), .int ((t : ℤ)), .int ((p : ℤ)), .int ((α : ℤ)), .int (((auK s t (k+1) : ℕ) : ℤ) - ((auK s t k : ℕ) : ℤ)), .int (((auK s t (k+1) : ℕ) : ℤ)), .int (((auM p α : ℕ) : ℤ)), .int ((k : ℤ)), .int ((p : ℤ)), .int ((α : ℤ)), .int ((s : ℤ)), .int ((t : ℤ)), .int (auPi p)]
  let W35 : List Val := [recI, .int (auC p α s t k), .int ((t : ℤ)), .int ((p : ℤ)), .int ((α : ℤ)), .int (((auK s t (k+1) : ℕ) : ℤ) - ((auK s t k : ℕ) : ℤ)), .int (((auK s t (k+1) : ℕ) : ℤ)), .int (((auM p α : ℕ) : ℤ)), .int ((k : ℤ)), .int ((p : ℤ)), .int ((α : ℤ)), .int ((s : ℤ)), .int ((t : ℤ)), .int (auPi p)]
  let W36 : List Val := [.int (((auK s t (k+1) : ℕ) : ℤ)), recI, .int (auC p α s t k), .int ((t : ℤ)), .int ((p : ℤ)), .int ((α : ℤ)), .int (((auK s t (k+1) : ℕ) : ℤ) - ((auK s t k : ℕ) : ℤ)), .int (((auM p α : ℕ) : ℤ)), .int ((k : ℤ)), .int ((p : ℤ)), .int ((α : ℤ)), .int ((s : ℤ)), .int ((t : ℤ)), .int (auPi p)]
  let W37 : List Val := [recI, .int (auC p α s t k), .int ((t : ℤ)), .int ((p : ℤ)), .int ((α : ℤ)), .int (((auK s t (k+1) : ℕ) : ℤ) - ((auK s t k : ℕ) : ℤ)), .int (((auM p α : ℕ) : ℤ)), .int ((k : ℤ)), .int ((p : ℤ)), .int ((α : ℤ)), .int ((s : ℤ)), .int ((t : ℤ)), .int (auPi p)]
  let W38 : List Val := [.int (((auM p α : ℕ) : ℤ)), recI, .int (auC p α s t k), .int ((t : ℤ)), .int ((p : ℤ)), .int ((α : ℤ)), .int (((auK s t (k+1) : ℕ) : ℤ) - ((auK s t k : ℕ) : ℤ)), .int ((k : ℤ)), .int ((p : ℤ)), .int ((α : ℤ)), .int ((s : ℤ)), .int ((t : ℤ)), .int (auPi p)]
  let W39 : List Val := [recI, .int (auC p α s t k), .int ((t : ℤ)), .int ((p : ℤ)), .int ((α : ℤ)), .int (((auK s t (k+1) : ℕ) : ℤ) - ((auK s t k : ℕ) : ℤ)), .int ((k : ℤ)), .int ((p : ℤ)), .int ((α : ℤ)), .int ((s : ℤ)), .int ((t : ℤ)), .int (auPi p)]
  let W40 : List Val := [.int ((k : ℤ)), recI, .int (auC p α s t k), .int ((t : ℤ)), .int ((p : ℤ)), .int ((α : ℤ)), .int (((auK s t (k+1) : ℕ) : ℤ) - ((auK s t k : ℕ) : ℤ)), .int ((p : ℤ)), .int ((α : ℤ)), .int ((s : ℤ)), .int ((t : ℤ)), .int (auPi p)]
  let W41 : List Val := [recI, .int (auC p α s t k), .int ((t : ℤ)), .int ((p : ℤ)), .int ((α : ℤ)), .int (((auK s t (k+1) : ℕ) : ℤ) - ((auK s t k : ℕ) : ℤ)), .int ((p : ℤ)), .int ((α : ℤ)), .int ((s : ℤ)), .int ((t : ℤ)), .int (auPi p)]
  let W42 : List Val := [.int (auC p α s t k), recI, .int ((t : ℤ)), .int ((p : ℤ)), .int ((α : ℤ)), .int (((auK s t (k+1) : ℕ) : ℤ) - ((auK s t k : ℕ) : ℤ)), .int ((p : ℤ)), .int ((α : ℤ)), .int ((s : ℤ)), .int ((t : ℤ)), .int (auPi p)]
  let W43 : List Val := [recI, .int ((t : ℤ)), .int ((p : ℤ)), .int ((α : ℤ)), .int (((auK s t (k+1) : ℕ) : ℤ) - ((auK s t k : ℕ) : ℤ)), .int ((p : ℤ)), .int ((α : ℤ)), .int ((s : ℤ)), .int ((t : ℤ)), .int (auPi p)]
  let W44 : List Val := [.int ((t : ℤ)), recI, .int ((p : ℤ)), .int ((α : ℤ)), .int (((auK s t (k+1) : ℕ) : ℤ) - ((auK s t k : ℕ) : ℤ)), .int ((p : ℤ)), .int ((α : ℤ)), .int ((s : ℤ)), .int ((t : ℤ)), .int (auPi p)]
  let W45 : List Val := [recI, .int ((p : ℤ)), .int ((α : ℤ)), .int (((auK s t (k+1) : ℕ) : ℤ) - ((auK s t k : ℕ) : ℤ)), .int ((p : ℤ)), .int ((α : ℤ)), .int ((s : ℤ)), .int ((t : ℤ)), .int (auPi p)]
  let W46 : List Val := [.int ((p : ℤ)), recI, .int ((α : ℤ)), .int (((auK s t (k+1) : ℕ) : ℤ) - ((auK s t k : ℕ) : ℤ)), .int ((p : ℤ)), .int ((α : ℤ)), .int ((s : ℤ)), .int ((t : ℤ)), .int (auPi p)]
  let W47 : List Val := [recI, .int ((α : ℤ)), .int (((auK s t (k+1) : ℕ) : ℤ) - ((auK s t k : ℕ) : ℤ)), .int ((p : ℤ)), .int ((α : ℤ)), .int ((s : ℤ)), .int ((t : ℤ)), .int (auPi p)]
  let W48 : List Val := [.int ((α : ℤ)), recI, .int (((auK s t (k+1) : ℕ) : ℤ) - ((auK s t k : ℕ) : ℤ)), .int ((p : ℤ)), .int ((α : ℤ)), .int ((s : ℤ)), .int ((t : ℤ)), .int (auPi p)]
  let W49 : List Val := [recI, .int (((auK s t (k+1) : ℕ) : ℤ) - ((auK s t k : ℕ) : ℤ)), .int ((p : ℤ)), .int ((α : ℤ)), .int ((s : ℤ)), .int ((t : ℤ)), .int (auPi p)]
  let W50 : List Val := [.int (((auK s t (k+1) : ℕ) : ℤ) - ((auK s t k : ℕ) : ℤ)), recI, .int ((p : ℤ)), .int ((α : ℤ)), .int ((s : ℤ)), .int ((t : ℤ)), .int (auPi p)]
  let W51 : List Val := (auRec p α s t k :: [Val.int (p : ℤ), Val.int (α : ℤ), Val.int (s : ℤ), Val.int (t : ℤ), Val.int (auPi p)])
  -- chain
  have hs1 : Pipe main pUncons W0 W1 RB := by
    refine Pipe.le (Pipe.unconsVAt main hUncons) (leR_const hKS_uncons hKS4)
  have hc1 : Pipe main P1 W0 W1 (1 * RB) := Pipe.le hs1 (by simp)
  have hs2 : Pipe main (pPick 3) W1 W2 RB := by
    have hmem : ∀ w ∈ W1, vsz w ≤ (p+1)^2 := vsz_mem_cons (by simpa [vsz_int] using hb_kI) (vsz_mem_cons (by simpa [vsz_int] using hb_piI) (vsz_mem_cons (by simpa [vsz_int] using hb_pI) (vsz_mem_cons (by simpa [vsz_int] using hb_aI) (vsz_mem_cons (by simpa [vsz_int] using hb_sI) (vsz_mem_cons (by simpa [vsz_int] using hb_tI) (vsz_mem_cons (by simpa [vsz_int] using hb_piI) ((by simp))))))))
    refine Pipe.le (Pipe.pickAt main hPick (A := W1) (k := 3) (by simp [W1]) (v := .int ((α : ℤ))) (by simp [W1])) ?_
    exact leR_roll hKS_pick (by omega) (szl_take_le16 hmem (by omega)) hp (by omega)
  have hc2 : Pipe main P2 W0 W2 (2 * RB) := Pipe.compMul hc1 hs2
  have hs3 : Pipe main (pPick 3) W2 W3 RB := by
    have hmem : ∀ w ∈ W2, vsz w ≤ (p+1)^2 := vsz_mem_cons (by simpa [vsz_int] using hb_aI) (vsz_mem_cons (by simpa [vsz_int] using hb_kI) (vsz_mem_cons (by simpa [vsz_int] using hb_piI) (vsz_mem_cons (by simpa [vsz_int] using hb_pI) (vsz_mem_cons (by simpa [vsz_int] using hb_aI) (vsz_mem_cons (by simpa [vsz_int] using hb_sI) (vsz_mem_cons (by simpa [vsz_int] using hb_tI) (vsz_mem_cons (by simpa [vsz_int] using hb_piI) ((by simp)))))))))
    refine Pipe.le (Pipe.pickAt main hPick (A := W2) (k := 3) (by simp [W2]) (v := .int ((p : ℤ))) (by simp [W2])) ?_
    exact leR_roll hKS_pick (by omega) (szl_take_le16 hmem (by omega)) hp (by omega)
  have hc3 : Pipe main P3 W0 W3 (3 * RB) := Pipe.compMul hc2 hs3
  have hs4 : Pipe main pML W3 W4 RB := by
    refine Pipe.le (Pipe.appendTail [.int ((k : ℤ)), .int (auPi p), .int ((p : ℤ)), .int ((α : ℤ)), .int ((s : ℤ)), .int ((t : ℤ)), .int (auPi p)] (hML main p α hp hαp)) (leR_pow hKS_ML)
  have hc4 : Pipe main P4 W0 W4 (4 * RB) := Pipe.compMul hc3 hs4
  have hs5 : Pipe main pSwap W4 W5 RB := by
    refine Pipe.le (Pipe.appendTail [.int ((k : ℤ)), .int (auPi p), .int ((p : ℤ)), .int ((α : ℤ)), .int ((s : ℤ)), .int ((t : ℤ)), .int (auPi p)] (Pipe.swap main hSwap (Val.int (((auM p α : ℕ) : ℤ))) (Val.int (((auL p α : ℕ) : ℤ))))) ?_
    exact leR_add1 hKS_swap ((by simpa [vsz_int] using hb_mI)) ((by simpa [vsz_int] using hb_LI)) hp hKS4
  have hc5 : Pipe main P5 W0 W5 (5 * RB) := Pipe.compMul hc4 hs5
  have hs6 : Pipe main (pPick 7) W5 W6 RB := by
    have hmem : ∀ w ∈ W5, vsz w ≤ (p+1)^2 := vsz_mem_cons (by simpa [vsz_int] using hb_LI) (vsz_mem_cons (by simpa [vsz_int] using hb_mI) (vsz_mem_cons (by simpa [vsz_int] using hb_kI) (vsz_mem_cons (by simpa [vsz_int] using hb_piI) (vsz_mem_cons (by simpa [vsz_int] using hb_pI) (vsz_mem_cons (by simpa [vsz_int] using hb_aI) (vsz_mem_cons (by simpa [vsz_int] using hb_sI) (vsz_mem_cons (by simpa [vsz_int] using hb_tI) (vsz_mem_cons (by simpa [vsz_int] using hb_piI) ((by simp))))))))))
    refine Pipe.le (Pipe.pickAt main hPick (A := W5) (k := 7) (by simp [W5]) (v := .int ((t : ℤ))) (by simp [W5])) ?_
    exact leR_roll hKS_pick (by omega) (szl_take_le16 hmem (by omega)) hp (by omega)
  have hc6 : Pipe main P6 W0 W6 (6 * RB) := Pipe.compMul hc5 hs6
  have hs7 : Pipe main (pPick 7) W6 W7 RB := by
    have hmem : ∀ w ∈ W6, vsz w ≤ (p+1)^2 := vsz_mem_cons (by simpa [vsz_int] using hb_tI) (vsz_mem_cons (by simpa [vsz_int] using hb_LI) (vsz_mem_cons (by simpa [vsz_int] using hb_mI) (vsz_mem_cons (by simpa [vsz_int] using hb_kI) (vsz_mem_cons (by simpa [vsz_int] using hb_piI) (vsz_mem_cons (by simpa [vsz_int] using hb_pI) (vsz_mem_cons (by simpa [vsz_int] using hb_aI) (vsz_mem_cons (by simpa [vsz_int] using hb_sI) (vsz_mem_cons (by simpa [vsz_int] using hb_tI) (vsz_mem_cons (by simpa [vsz_int] using hb_piI) ((by simp)))))))))))
    refine Pipe.le (Pipe.pickAt main hPick (A := W6) (k := 7) (by simp [W6]) (v := .int ((s : ℤ))) (by simp [W6])) ?_
    exact leR_roll hKS_pick (by omega) (szl_take_le16 hmem (by omega)) hp (by omega)
  have hc7 : Pipe main P7 W0 W7 (7 * RB) := Pipe.compMul hc6 hs7
  have hs8 : Pipe main (pPick 4) W7 W8 RB := by
    have hmem : ∀ w ∈ W7, vsz w ≤ (p+1)^2 := vsz_mem_cons (by simpa [vsz_int] using hb_sI) (vsz_mem_cons (by simpa [vsz_int] using hb_tI) (vsz_mem_cons (by simpa [vsz_int] using hb_LI) (vsz_mem_cons (by simpa [vsz_int] using hb_mI) (vsz_mem_cons (by simpa [vsz_int] using hb_kI) (vsz_mem_cons (by simpa [vsz_int] using hb_piI) (vsz_mem_cons (by simpa [vsz_int] using hb_pI) (vsz_mem_cons (by simpa [vsz_int] using hb_aI) (vsz_mem_cons (by simpa [vsz_int] using hb_sI) (vsz_mem_cons (by simpa [vsz_int] using hb_tI) (vsz_mem_cons (by simpa [vsz_int] using hb_piI) ((by simp))))))))))))
    refine Pipe.le (Pipe.pickAt main hPick (A := W7) (k := 4) (by simp [W7]) (v := .int ((k : ℤ))) (by simp [W7])) ?_
    exact leR_roll hKS_pick (by omega) (szl_take_le16 hmem (by omega)) hp (by omega)
  have hc8 : Pipe main P8 W0 W8 (8 * RB) := Pipe.compMul hc7 hs8
  have hs9 : Pipe main pKW W8 W9 RB := by
    refine Pipe.le (Pipe.appendTail [.int (((auL p α : ℕ) : ℤ)), .int (((auM p α : ℕ) : ℤ)), .int ((k : ℤ)), .int (auPi p), .int ((p : ℤ)), .int ((α : ℤ)), .int ((s : ℤ)), .int ((t : ℤ)), .int (auPi p)] (hKW main p s t k hp (by omega) htp hst hklt)) (leR_pow hKS_KW)
  have hc9 : Pipe main P9 W0 W9 (9 * RB) := Pipe.compMul hc8 hs9
  have hs10 : Pipe main pDup W9 W10 RB := by
    refine Pipe.le (Pipe.appendTail [.int (((auK s t (k+1) : ℕ) : ℤ)), .int (((auL p α : ℕ) : ℤ)), .int (((auM p α : ℕ) : ℤ)), .int ((k : ℤ)), .int (auPi p), .int ((p : ℤ)), .int ((α : ℤ)), .int ((s : ℤ)), .int ((t : ℤ)), .int (auPi p)] (Pipe.dup main hDup (Val.int (((auK s t k : ℕ) : ℤ))))) ?_
    exact leR_one hKS_dup ((by simpa [vsz_int] using hb_KkI)) hp hKS4
  have hc10 : Pipe main P10 W0 W10 (10 * RB) := Pipe.compMul hc9 hs10
  have hs11 : Pipe main (pPick 2) W10 W11 RB := by
    have hmem : ∀ w ∈ W10, vsz w ≤ (p+1)^2 := vsz_mem_cons (by simpa [vsz_int] using hb_KkI) (vsz_mem_cons (by simpa [vsz_int] using hb_KkI) (vsz_mem_cons (by simpa [vsz_int] using hb_Kk1I) (vsz_mem_cons (by simpa [vsz_int] using hb_LI) (vsz_mem_cons (by simpa [vsz_int] using hb_mI) (vsz_mem_cons (by simpa [vsz_int] using hb_kI) (vsz_mem_cons (by simpa [vsz_int] using hb_piI) (vsz_mem_cons (by simpa [vsz_int] using hb_pI) (vsz_mem_cons (by simpa [vsz_int] using hb_aI) (vsz_mem_cons (by simpa [vsz_int] using hb_sI) (vsz_mem_cons (by simpa [vsz_int] using hb_tI) (vsz_mem_cons (by simpa [vsz_int] using hb_piI) ((by simp)))))))))))))
    refine Pipe.le (Pipe.pickAt main hPick (A := W10) (k := 2) (by simp [W10]) (v := .int (((auK s t (k+1) : ℕ) : ℤ))) (by simp [W10])) ?_
    exact leR_roll hKS_pick (by omega) (szl_take_le16 hmem (by omega)) hp (by omega)
  have hc11 : Pipe main P11 W0 W11 (11 * RB) := Pipe.compMul hc10 hs11
  have hs12 : Pipe main pSub W11 W12 RB := by
    refine Pipe.le (Pipe.appendTail [.int (((auK s t k : ℕ) : ℤ)), .int (((auK s t (k+1) : ℕ) : ℤ)), .int (((auL p α : ℕ) : ℤ)), .int (((auM p α : ℕ) : ℤ)), .int ((k : ℤ)), .int (auPi p), .int ((p : ℤ)), .int ((α : ℤ)), .int ((s : ℤ)), .int ((t : ℤ)), .int (auPi p)] (Pipe.binOp (hSub main) trivial)) ?_
    exact leR_add hKS_sub ((by simpa [vsz_int] using hb_Kk1I)) ((by simpa [vsz_int] using hb_KkI)) hp hKS4
  have hc12 : Pipe main P12 W0 W12 (12 * RB) := Pipe.compMul hc11 hs12
  have hs13 : Pipe main (pPick 1) W12 W13 RB := by
    have hmem : ∀ w ∈ W12, vsz w ≤ (p+1)^2 := vsz_mem_cons (by simpa [vsz_int] using hb_slI) (vsz_mem_cons (by simpa [vsz_int] using hb_KkI) (vsz_mem_cons (by simpa [vsz_int] using hb_Kk1I) (vsz_mem_cons (by simpa [vsz_int] using hb_LI) (vsz_mem_cons (by simpa [vsz_int] using hb_mI) (vsz_mem_cons (by simpa [vsz_int] using hb_kI) (vsz_mem_cons (by simpa [vsz_int] using hb_piI) (vsz_mem_cons (by simpa [vsz_int] using hb_pI) (vsz_mem_cons (by simpa [vsz_int] using hb_aI) (vsz_mem_cons (by simpa [vsz_int] using hb_sI) (vsz_mem_cons (by simpa [vsz_int] using hb_tI) (vsz_mem_cons (by simpa [vsz_int] using hb_piI) ((by simp)))))))))))))
    refine Pipe.le (Pipe.pickAt main hPick (A := W12) (k := 1) (by simp [W12]) (v := .int (((auK s t k : ℕ) : ℤ))) (by simp [W12])) ?_
    exact leR_roll hKS_pick (by omega) (szl_take_le16 hmem (by omega)) hp (by omega)
  have hc13 : Pipe main P13 W0 W13 (13 * RB) := Pipe.compMul hc12 hs13
  have hs14 : Pipe main (pPick 11) W13 W14 RB := by
    have hmem : ∀ w ∈ W13, vsz w ≤ (p+1)^2 := vsz_mem_cons (by simpa [vsz_int] using hb_KkI) (vsz_mem_cons (by simpa [vsz_int] using hb_slI) (vsz_mem_cons (by simpa [vsz_int] using hb_KkI) (vsz_mem_cons (by simpa [vsz_int] using hb_Kk1I) (vsz_mem_cons (by simpa [vsz_int] using hb_LI) (vsz_mem_cons (by simpa [vsz_int] using hb_mI) (vsz_mem_cons (by simpa [vsz_int] using hb_kI) (vsz_mem_cons (by simpa [vsz_int] using hb_piI) (vsz_mem_cons (by simpa [vsz_int] using hb_pI) (vsz_mem_cons (by simpa [vsz_int] using hb_aI) (vsz_mem_cons (by simpa [vsz_int] using hb_sI) (vsz_mem_cons (by simpa [vsz_int] using hb_tI) (vsz_mem_cons (by simpa [vsz_int] using hb_piI) ((by simp))))))))))))))
    refine Pipe.le (Pipe.pickAt main hPick (A := W13) (k := 11) (by simp [W13]) (v := .int ((t : ℤ))) (by simp [W13])) ?_
    exact leR_roll hKS_pick (by omega) (szl_take_le16 hmem (by omega)) hp (by omega)
  have hc14 : Pipe main P14 W0 W14 (14 * RB) := Pipe.compMul hc13 hs14
  have hs15 : Pipe main pMul W14 W15 RB := by
    refine Pipe.le (Pipe.appendTail [.int (((auK s t (k+1) : ℕ) : ℤ) - ((auK s t k : ℕ) : ℤ)), .int (((auK s t k : ℕ) : ℤ)), .int (((auK s t (k+1) : ℕ) : ℤ)), .int (((auL p α : ℕ) : ℤ)), .int (((auM p α : ℕ) : ℤ)), .int ((k : ℤ)), .int (auPi p), .int ((p : ℤ)), .int ((α : ℤ)), .int ((s : ℤ)), .int ((t : ℤ)), .int (auPi p)] (Pipe.binOp (hMul main) trivial)) ?_
    exact leR_mulK hKS_mul ((by simpa [vsz_int] using hb_tI)) ((by simpa [vsz_int] using hb_KkI)) hp hKS4
  have hc15 : Pipe main P15 W0 W15 (15 * RB) := Pipe.compMul hc14 hs15
  have hs16 : Pipe main (pPick 5) W15 W16 RB := by
    have hmem : ∀ w ∈ W15, vsz w ≤ (p+1)^2 := vsz_mem_cons (by simpa [vsz_int] using hb_tKkI) (vsz_mem_cons (by simpa [vsz_int] using hb_slI) (vsz_mem_cons (by simpa [vsz_int] using hb_KkI) (vsz_mem_cons (by simpa [vsz_int] using hb_Kk1I) (vsz_mem_cons (by simpa [vsz_int] using hb_LI) (vsz_mem_cons (by simpa [vsz_int] using hb_mI) (vsz_mem_cons (by simpa [vsz_int] using hb_kI) (vsz_mem_cons (by simpa [vsz_int] using hb_piI) (vsz_mem_cons (by simpa [vsz_int] using hb_pI) (vsz_mem_cons (by simpa [vsz_int] using hb_aI) (vsz_mem_cons (by simpa [vsz_int] using hb_sI) (vsz_mem_cons (by simpa [vsz_int] using hb_tI) (vsz_mem_cons (by simpa [vsz_int] using hb_piI) ((by simp))))))))))))))
    refine Pipe.le (Pipe.pickAt main hPick (A := W15) (k := 5) (by simp [W15]) (v := .int (((auM p α : ℕ) : ℤ))) (by simp [W15])) ?_
    exact leR_roll hKS_pick (by omega) (szl_take_le16 hmem (by omega)) hp (by omega)
  have hc16 : Pipe main P16 W0 W16 (16 * RB) := Pipe.compMul hc15 hs16
  have hs17 : Pipe main (pPick 12) W16 W17 RB := by
    have hmem : ∀ w ∈ W16, vsz w ≤ (p+1)^2 := vsz_mem_cons (by simpa [vsz_int] using hb_mI) (vsz_mem_cons (by simpa [vsz_int] using hb_tKkI) (vsz_mem_cons (by simpa [vsz_int] using hb_slI) (vsz_mem_cons (by simpa [vsz_int] using hb_KkI) (vsz_mem_cons (by simpa [vsz_int] using hb_Kk1I) (vsz_mem_cons (by simpa [vsz_int] using hb_LI) (vsz_mem_cons (by simpa [vsz_int] using hb_mI) (vsz_mem_cons (by simpa [vsz_int] using hb_kI) (vsz_mem_cons (by simpa [vsz_int] using hb_piI) (vsz_mem_cons (by simpa [vsz_int] using hb_pI) (vsz_mem_cons (by simpa [vsz_int] using hb_aI) (vsz_mem_cons (by simpa [vsz_int] using hb_sI) (vsz_mem_cons (by simpa [vsz_int] using hb_tI) (vsz_mem_cons (by simpa [vsz_int] using hb_piI) ((by simp)))))))))))))))
    refine Pipe.le (Pipe.pickAt main hPick (A := W16) (k := 12) (by simp [W16]) (v := .int ((t : ℤ))) (by simp [W16])) ?_
    exact leR_roll hKS_pick (by omega) (szl_take_le16 hmem (by omega)) hp (by omega)
  have hc17 : Pipe main P17 W0 W17 (17 * RB) := Pipe.compMul hc16 hs17
  have hs18 : Pipe main pMul W17 W18 RB := by
    refine Pipe.le (Pipe.appendTail [.int ((t : ℤ) * ((auK s t k : ℕ) : ℤ)), .int (((auK s t (k+1) : ℕ) : ℤ) - ((auK s t k : ℕ) : ℤ)), .int (((auK s t k : ℕ) : ℤ)), .int (((auK s t (k+1) : ℕ) : ℤ)), .int (((auL p α : ℕ) : ℤ)), .int (((auM p α : ℕ) : ℤ)), .int ((k : ℤ)), .int (auPi p), .int ((p : ℤ)), .int ((α : ℤ)), .int ((s : ℤ)), .int ((t : ℤ)), .int (auPi p)] (Pipe.binOp (hMul main) trivial)) ?_
    exact leR_mulK hKS_mul ((by simpa [vsz_int] using hb_tI)) ((by simpa [vsz_int] using hb_mI)) hp hKS4
  have hc18 : Pipe main P18 W0 W18 (18 * RB) := Pipe.compMul hc17 hs18
  have hs19 : Pipe main pSwap W18 W19 RB := by
    refine Pipe.le (Pipe.appendTail [.int (((auK s t (k+1) : ℕ) : ℤ) - ((auK s t k : ℕ) : ℤ)), .int (((auK s t k : ℕ) : ℤ)), .int (((auK s t (k+1) : ℕ) : ℤ)), .int (((auL p α : ℕ) : ℤ)), .int (((auM p α : ℕ) : ℤ)), .int ((k : ℤ)), .int (auPi p), .int ((p : ℤ)), .int ((α : ℤ)), .int ((s : ℤ)), .int ((t : ℤ)), .int (auPi p)] (Pipe.swap main hSwap (Val.int ((t : ℤ) * ((auM p α : ℕ) : ℤ))) (Val.int ((t : ℤ) * ((auK s t k : ℕ) : ℤ))))) ?_
    exact leR_add1 hKS_swap ((by simpa [vsz_int] using hb_tmI)) ((by simpa [vsz_int] using hb_tKkI)) hp hKS4
  have hc19 : Pipe main P19 W0 W19 (19 * RB) := Pipe.compMul hc18 hs19
  have hs20 : Pipe main pSub W19 W20 RB := by
    refine Pipe.le (Pipe.appendTail [.int (((auK s t (k+1) : ℕ) : ℤ) - ((auK s t k : ℕ) : ℤ)), .int (((auK s t k : ℕ) : ℤ)), .int (((auK s t (k+1) : ℕ) : ℤ)), .int (((auL p α : ℕ) : ℤ)), .int (((auM p α : ℕ) : ℤ)), .int ((k : ℤ)), .int (auPi p), .int ((p : ℤ)), .int ((α : ℤ)), .int ((s : ℤ)), .int ((t : ℤ)), .int (auPi p)] (Pipe.binOp (hSub main) trivial)) ?_
    exact leR_add hKS_sub ((by simpa [vsz_int] using hb_tKkI)) ((by simpa [vsz_int] using hb_tmI)) hp hKS4
  have hc20 : Pipe main P20 W0 W20 (20 * RB) := Pipe.compMul hc19 hs20
  have hs21 : Pipe main (pPick 6) W20 W21 RB := by
    have hmem : ∀ w ∈ W20, vsz w ≤ (p+1)^2 := vsz_mem_cons (by simpa [vsz_int] using hb_C1I) (vsz_mem_cons (by simpa [vsz_int] using hb_slI) (vsz_mem_cons (by simpa [vsz_int] using hb_KkI) (vsz_mem_cons (by simpa [vsz_int] using hb_Kk1I) (vsz_mem_cons (by simpa [vsz_int] using hb_LI) (vsz_mem_cons (by simpa [vsz_int] using hb_mI) (vsz_mem_cons (by simpa [vsz_int] using hb_kI) (vsz_mem_cons (by simpa [vsz_int] using hb_piI) (vsz_mem_cons (by simpa [vsz_int] using hb_pI) (vsz_mem_cons (by simpa [vsz_int] using hb_aI) (vsz_mem_cons (by simpa [vsz_int] using hb_sI) (vsz_mem_cons (by simpa [vsz_int] using hb_tI) (vsz_mem_cons (by simpa [vsz_int] using hb_piI) ((by simp))))))))))))))
    refine Pipe.le (Pipe.pickAt main hPick (A := W20) (k := 6) (by simp [W20]) (v := .int ((k : ℤ))) (by simp [W20])) ?_
    exact leR_roll hKS_pick (by omega) (szl_take_le16 hmem (by omega)) hp (by omega)
  have hc21 : Pipe main P21 W0 W21 (21 * RB) := Pipe.compMul hc20 hs21
  have hs22 : Pipe main (pPick 11) W21 W22 RB := by
    have hmem : ∀ w ∈ W21, vsz w ≤ (p+1)^2 := vsz_mem_cons (by simpa [vsz_int] using hb_kI) (vsz_mem_cons (by simpa [vsz_int] using hb_C1I) (vsz_mem_cons (by simpa [vsz_int] using hb_slI) (vsz_mem_cons (by simpa [vsz_int] using hb_KkI) (vsz_mem_cons (by simpa [vsz_int] using hb_Kk1I) (vsz_mem_cons (by simpa [vsz_int] using hb_LI) (vsz_mem_cons (by simpa [vsz_int] using hb_mI) (vsz_mem_cons (by simpa [vsz_int] using hb_kI) (vsz_mem_cons (by simpa [vsz_int] using hb_piI) (vsz_mem_cons (by simpa [vsz_int] using hb_pI) (vsz_mem_cons (by simpa [vsz_int] using hb_aI) (vsz_mem_cons (by simpa [vsz_int] using hb_sI) (vsz_mem_cons (by simpa [vsz_int] using hb_tI) (vsz_mem_cons (by simpa [vsz_int] using hb_piI) ((by simp)))))))))))))))
    refine Pipe.le (Pipe.pickAt main hPick (A := W21) (k := 11) (by simp [W21]) (v := .int ((s : ℤ))) (by simp [W21])) ?_
    exact leR_roll hKS_pick (by omega) (szl_take_le16 hmem (by omega)) hp (by omega)
  have hc22 : Pipe main P22 W0 W22 (22 * RB) := Pipe.compMul hc21 hs22
  have hs23 : Pipe main pMul W22 W23 RB := by
    refine Pipe.le (Pipe.appendTail [.int ((t : ℤ) * ((auK s t k : ℕ) : ℤ) - (t : ℤ) * ((auM p α : ℕ) : ℤ)), .int (((auK s t (k+1) : ℕ) : ℤ) - ((auK s t k : ℕ) : ℤ)), .int (((auK s t k : ℕ) : ℤ)), .int (((auK s t (k+1) : ℕ) : ℤ)), .int (((auL p α : ℕ) : ℤ)), .int (((auM p α : ℕ) : ℤ)), .int ((k : ℤ)), .int (auPi p), .int ((p : ℤ)), .int ((α : ℤ)), .int ((s : ℤ)), .int ((t : ℤ)), .int (auPi p)] (Pipe.binOp (hMul main) trivial)) ?_
    exact leR_mulK hKS_mul ((by simpa [vsz_int] using hb_sI)) ((by simpa [vsz_int] using hb_kI)) hp hKS4
  have hc23 : Pipe main P23 W0 W23 (23 * RB) := Pipe.compMul hc22 hs23
  have hs24 : Pipe main pSwap W23 W24 RB := by
    refine Pipe.le (Pipe.appendTail [.int (((auK s t (k+1) : ℕ) : ℤ) - ((auK s t k : ℕ) : ℤ)), .int (((auK s t k : ℕ) : ℤ)), .int (((auK s t (k+1) : ℕ) : ℤ)), .int (((auL p α : ℕ) : ℤ)), .int (((auM p α : ℕ) : ℤ)), .int ((k : ℤ)), .int (auPi p), .int ((p : ℤ)), .int ((α : ℤ)), .int ((s : ℤ)), .int ((t : ℤ)), .int (auPi p)] (Pipe.swap main hSwap (Val.int ((s : ℤ) * (k : ℤ))) (Val.int ((t : ℤ) * ((auK s t k : ℕ) : ℤ) - (t : ℤ) * ((auM p α : ℕ) : ℤ))))) ?_
    exact leR_add1 hKS_swap ((by simpa [vsz_int] using hb_skI)) ((by simpa [vsz_int] using hb_C1I)) hp hKS4
  have hc24 : Pipe main P24 W0 W24 (24 * RB) := Pipe.compMul hc23 hs24
  have hs25 : Pipe main pSub W24 W25 RB := by
    refine Pipe.le (Pipe.appendTail [.int (((auK s t (k+1) : ℕ) : ℤ) - ((auK s t k : ℕ) : ℤ)), .int (((auK s t k : ℕ) : ℤ)), .int (((auK s t (k+1) : ℕ) : ℤ)), .int (((auL p α : ℕ) : ℤ)), .int (((auM p α : ℕ) : ℤ)), .int ((k : ℤ)), .int (auPi p), .int ((p : ℤ)), .int ((α : ℤ)), .int ((s : ℤ)), .int ((t : ℤ)), .int (auPi p)] (Pipe.binOp (hSub main) trivial)) ?_
    exact leR_add hKS_sub ((by simpa [vsz_int] using hb_C1I)) ((by simpa [vsz_int] using hb_skI)) hp hKS4
  have hc25 : Pipe main P25 W0 W25 (25 * RB) := Pipe.compMul hc24 hs25
  have hs26 : Pipe main (pRoll 1) W25 W26 RB := by
    have hmem : ∀ w ∈ W25, vsz w ≤ (p+1)^2 := vsz_mem_cons (by simpa [vsz_int] using hb_CI) (vsz_mem_cons (by simpa [vsz_int] using hb_slI) (vsz_mem_cons (by simpa [vsz_int] using hb_KkI) (vsz_mem_cons (by simpa [vsz_int] using hb_Kk1I) (vsz_mem_cons (by simpa [vsz_int] using hb_LI) (vsz_mem_cons (by simpa [vsz_int] using hb_mI) (vsz_mem_cons (by simpa [vsz_int] using hb_kI) (vsz_mem_cons (by simpa [vsz_int] using hb_piI) (vsz_mem_cons (by simpa [vsz_int] using hb_pI) (vsz_mem_cons (by simpa [vsz_int] using hb_aI) (vsz_mem_cons (by simpa [vsz_int] using hb_sI) (vsz_mem_cons (by simpa [vsz_int] using hb_tI) (vsz_mem_cons (by simpa [vsz_int] using hb_piI) ((by simp))))))))))))))
    refine Pipe.le (Pipe.rollAt main hRoll (A := W25) (j := 1) (by simp [W25]) (B := W26) ?_) ?_
    · simp only [W25, W26, List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, List.eraseIdx_nil]
    exact leR_roll hKS_roll (by omega) (szl_take_le16 hmem (by omega)) hp (by omega)
  have hc26 : Pipe main P26 W0 W26 (26 * RB) := Pipe.compMul hc25 hs26
  have hs27 : Pipe main (pPick 9) W26 W27 RB := by
    have hmem : ∀ w ∈ W26, vsz w ≤ (p+1)^2 := vsz_mem_cons (by simpa [vsz_int] using hb_slI) (vsz_mem_cons (by simpa [vsz_int] using hb_CI) (vsz_mem_cons (by simpa [vsz_int] using hb_KkI) (vsz_mem_cons (by simpa [vsz_int] using hb_Kk1I) (vsz_mem_cons (by simpa [vsz_int] using hb_LI) (vsz_mem_cons (by simpa [vsz_int] using hb_mI) (vsz_mem_cons (by simpa [vsz_int] using hb_kI) (vsz_mem_cons (by simpa [vsz_int] using hb_piI) (vsz_mem_cons (by simpa [vsz_int] using hb_pI) (vsz_mem_cons (by simpa [vsz_int] using hb_aI) (vsz_mem_cons (by simpa [vsz_int] using hb_sI) (vsz_mem_cons (by simpa [vsz_int] using hb_tI) (vsz_mem_cons (by simpa [vsz_int] using hb_piI) ((by simp))))))))))))))
    refine Pipe.le (Pipe.pickAt main hPick (A := W26) (k := 9) (by simp [W26]) (v := .int ((α : ℤ))) (by simp [W26])) ?_
    exact leR_roll hKS_pick (by omega) (szl_take_le16 hmem (by omega)) hp (by omega)
  have hc27 : Pipe main P27 W0 W27 (27 * RB) := Pipe.compMul hc26 hs27
  have hs28 : Pipe main (pPick 9) W27 W28 RB := by
    have hmem : ∀ w ∈ W27, vsz w ≤ (p+1)^2 := vsz_mem_cons (by simpa [vsz_int] using hb_aI) (vsz_mem_cons (by simpa [vsz_int] using hb_slI) (vsz_mem_cons (by simpa [vsz_int] using hb_CI) (vsz_mem_cons (by simpa [vsz_int] using hb_KkI) (vsz_mem_cons (by simpa [vsz_int] using hb_Kk1I) (vsz_mem_cons (by simpa [vsz_int] using hb_LI) (vsz_mem_cons (by simpa [vsz_int] using hb_mI) (vsz_mem_cons (by simpa [vsz_int] using hb_kI) (vsz_mem_cons (by simpa [vsz_int] using hb_piI) (vsz_mem_cons (by simpa [vsz_int] using hb_pI) (vsz_mem_cons (by simpa [vsz_int] using hb_aI) (vsz_mem_cons (by simpa [vsz_int] using hb_sI) (vsz_mem_cons (by simpa [vsz_int] using hb_tI) (vsz_mem_cons (by simpa [vsz_int] using hb_piI) ((by simp)))))))))))))))
    refine Pipe.le (Pipe.pickAt main hPick (A := W27) (k := 9) (by simp [W27]) (v := .int ((p : ℤ))) (by simp [W27])) ?_
    exact leR_roll hKS_pick (by omega) (szl_take_le16 hmem (by omega)) hp (by omega)
  have hc28 : Pipe main P28 W0 W28 (28 * RB) := Pipe.compMul hc27 hs28
  have hs29 : Pipe main (pPick 13) W28 W29 RB := by
    have hmem : ∀ w ∈ W28, vsz w ≤ (p+1)^2 := vsz_mem_cons (by simpa [vsz_int] using hb_pI) (vsz_mem_cons (by simpa [vsz_int] using hb_aI) (vsz_mem_cons (by simpa [vsz_int] using hb_slI) (vsz_mem_cons (by simpa [vsz_int] using hb_CI) (vsz_mem_cons (by simpa [vsz_int] using hb_KkI) (vsz_mem_cons (by simpa [vsz_int] using hb_Kk1I) (vsz_mem_cons (by simpa [vsz_int] using hb_LI) (vsz_mem_cons (by simpa [vsz_int] using hb_mI) (vsz_mem_cons (by simpa [vsz_int] using hb_kI) (vsz_mem_cons (by simpa [vsz_int] using hb_piI) (vsz_mem_cons (by simpa [vsz_int] using hb_pI) (vsz_mem_cons (by simpa [vsz_int] using hb_aI) (vsz_mem_cons (by simpa [vsz_int] using hb_sI) (vsz_mem_cons (by simpa [vsz_int] using hb_tI) (vsz_mem_cons (by simpa [vsz_int] using hb_piI) ((by simp))))))))))))))))
    refine Pipe.le (Pipe.pickAt main hPick (A := W28) (k := 13) (by simp [W28]) (v := .int ((t : ℤ))) (by simp [W28])) ?_
    exact leR_roll hKS_pick (by omega) (szl_take_le16 hmem (by omega)) hp (by omega)
  have hc29 : Pipe main P29 W0 W29 (29 * RB) := Pipe.compMul hc28 hs29
  have hs30 : Pipe main (pRoll 4) W29 W30 RB := by
    have hmem : ∀ w ∈ W29, vsz w ≤ (p+1)^2 := vsz_mem_cons (by simpa [vsz_int] using hb_tI) (vsz_mem_cons (by simpa [vsz_int] using hb_pI) (vsz_mem_cons (by simpa [vsz_int] using hb_aI) (vsz_mem_cons (by simpa [vsz_int] using hb_slI) (vsz_mem_cons (by simpa [vsz_int] using hb_CI) (vsz_mem_cons (by simpa [vsz_int] using hb_KkI) (vsz_mem_cons (by simpa [vsz_int] using hb_Kk1I) (vsz_mem_cons (by simpa [vsz_int] using hb_LI) (vsz_mem_cons (by simpa [vsz_int] using hb_mI) (vsz_mem_cons (by simpa [vsz_int] using hb_kI) (vsz_mem_cons (by simpa [vsz_int] using hb_piI) (vsz_mem_cons (by simpa [vsz_int] using hb_pI) (vsz_mem_cons (by simpa [vsz_int] using hb_aI) (vsz_mem_cons (by simpa [vsz_int] using hb_sI) (vsz_mem_cons (by simpa [vsz_int] using hb_tI) (vsz_mem_cons (by simpa [vsz_int] using hb_piI) ((by simp)))))))))))))))))
    refine Pipe.le (Pipe.rollAt main hRoll (A := W29) (j := 4) (by simp [W29]) (B := W30) ?_) ?_
    · simp only [W29, W30, List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, List.eraseIdx_nil]
    exact leR_roll hKS_roll (by omega) (szl_take_le16 hmem (by omega)) hp (by omega)
  have hc30 : Pipe main P30 W0 W30 (30 * RB) := Pipe.compMul hc29 hs30
  have hs31 : Pipe main (pRoll 10) W30 W31 RB := by
    have hmem : ∀ w ∈ W30, vsz w ≤ (p+1)^2 := vsz_mem_cons (by simpa [vsz_int] using hb_CI) (vsz_mem_cons (by simpa [vsz_int] using hb_tI) (vsz_mem_cons (by simpa [vsz_int] using hb_pI) (vsz_mem_cons (by simpa [vsz_int] using hb_aI) (vsz_mem_cons (by simpa [vsz_int] using hb_slI) (vsz_mem_cons (by simpa [vsz_int] using hb_KkI) (vsz_mem_cons (by simpa [vsz_int] using hb_Kk1I) (vsz_mem_cons (by simpa [vsz_int] using hb_LI) (vsz_mem_cons (by simpa [vsz_int] using hb_mI) (vsz_mem_cons (by simpa [vsz_int] using hb_kI) (vsz_mem_cons (by simpa [vsz_int] using hb_piI) (vsz_mem_cons (by simpa [vsz_int] using hb_pI) (vsz_mem_cons (by simpa [vsz_int] using hb_aI) (vsz_mem_cons (by simpa [vsz_int] using hb_sI) (vsz_mem_cons (by simpa [vsz_int] using hb_tI) (vsz_mem_cons (by simpa [vsz_int] using hb_piI) ((by simp)))))))))))))))))
    refine Pipe.le (Pipe.rollAt main hRoll (A := W30) (j := 10) (by simp [W30]) (B := W31) ?_) ?_
    · simp only [W30, W31, List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, List.eraseIdx_nil]
    exact leR_roll hKS_roll (by omega) (szl_take_le16 hmem (by omega)) hp (by omega)
  have hc31 : Pipe main P31 W0 W31 (31 * RB) := Pipe.compMul hc30 hs31
  have hs32 : Pipe main (pRoll 8) W31 W32 RB := by
    have hmem : ∀ w ∈ W31, vsz w ≤ (p+1)^2 := vsz_mem_cons (by simpa [vsz_int] using hb_piI) (vsz_mem_cons (by simpa [vsz_int] using hb_CI) (vsz_mem_cons (by simpa [vsz_int] using hb_tI) (vsz_mem_cons (by simpa [vsz_int] using hb_pI) (vsz_mem_cons (by simpa [vsz_int] using hb_aI) (vsz_mem_cons (by simpa [vsz_int] using hb_slI) (vsz_mem_cons (by simpa [vsz_int] using hb_KkI) (vsz_mem_cons (by simpa [vsz_int] using hb_Kk1I) (vsz_mem_cons (by simpa [vsz_int] using hb_LI) (vsz_mem_cons (by simpa [vsz_int] using hb_mI) (vsz_mem_cons (by simpa [vsz_int] using hb_kI) (vsz_mem_cons (by simpa [vsz_int] using hb_pI) (vsz_mem_cons (by simpa [vsz_int] using hb_aI) (vsz_mem_cons (by simpa [vsz_int] using hb_sI) (vsz_mem_cons (by simpa [vsz_int] using hb_tI) (vsz_mem_cons (by simpa [vsz_int] using hb_piI) ((by simp)))))))))))))))))
    refine Pipe.le (Pipe.rollAt main hRoll (A := W31) (j := 8) (by simp [W31]) (B := W32) ?_) ?_
    · simp only [W31, W32, List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, List.eraseIdx_nil]
    exact leR_roll hKS_roll (by omega) (szl_take_le16 hmem (by omega)) hp (by omega)
  have hc32 : Pipe main P32 W0 W32 (32 * RB) := Pipe.compMul hc31 hs32
  have hs33 : Pipe main pB W32 W33 RB := by
    refine Pipe.le (Pipe.appendTail [.int (((auK s t (k+1) : ℕ) : ℤ) - ((auK s t k : ℕ) : ℤ)), .int (((auK s t k : ℕ) : ℤ)), .int (((auK s t (k+1) : ℕ) : ℤ)), .int (((auM p α : ℕ) : ℤ)), .int ((k : ℤ)), .int ((p : ℤ)), .int ((α : ℤ)), .int ((s : ℤ)), .int ((t : ℤ)), .int (auPi p)] (hB main p α s t k hs hst htp hα hp hαp hklt hLle hLsz hCsz hI hNbd hWtsz)) (leR_pow hKS_B)
  have hc33 : Pipe main P33 W0 W33 (33 * RB) := Pipe.compMul hc32 hs33
  have hs34 : Pipe main (pRoll 6) W33 W34 RB := by
    have hmem : ∀ w ∈ W33, vsz w ≤ (p+1)^4 := vsz_mem_cons hrecI (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_CI (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_tI (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_pI (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_aI (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_slI (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_KkI (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_Kk1I (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_mI (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_kI (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_pI (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_aI (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_sI (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_tI (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_piI (sq_le_four p)) ((by simp))))))))))))))))
    refine Pipe.le (Pipe.rollAt main hRoll (A := W33) (j := 6) (by simp [W33]) (B := W34) ?_) ?_
    · simp only [W33, W34, List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, List.eraseIdx_nil]
    exact leR_rollV hKS_roll (by omega) (szl_take_le16 hmem (by omega)) hp (by omega)
  have hc34 : Pipe main P34 W0 W34 (34 * RB) := Pipe.compMul hc33 hs34
  have hs35 : Pipe main pDrop W34 W35 RB := by
    refine Pipe.le (Pipe.appendTail W35 (Pipe.drop main hDrop (Val.int (((auK s t k : ℕ) : ℤ))))) ?_
    exact leR_one hKS_drop ((by simpa [vsz_int] using hb_KkI)) hp hKS4
  have hc35 : Pipe main P35 W0 W35 (35 * RB) := Pipe.compMul hc34 hs35
  have hs36 : Pipe main (pRoll 6) W35 W36 RB := by
    have hmem : ∀ w ∈ W35, vsz w ≤ (p+1)^4 := vsz_mem_cons hrecI (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_CI (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_tI (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_pI (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_aI (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_slI (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_Kk1I (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_mI (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_kI (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_pI (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_aI (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_sI (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_tI (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_piI (sq_le_four p)) ((by simp)))))))))))))))
    refine Pipe.le (Pipe.rollAt main hRoll (A := W35) (j := 6) (by simp [W35]) (B := W36) ?_) ?_
    · simp only [W35, W36, List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, List.eraseIdx_nil]
    exact leR_rollV hKS_roll (by omega) (szl_take_le16 hmem (by omega)) hp (by omega)
  have hc36 : Pipe main P36 W0 W36 (36 * RB) := Pipe.compMul hc35 hs36
  have hs37 : Pipe main pDrop W36 W37 RB := by
    refine Pipe.le (Pipe.appendTail W37 (Pipe.drop main hDrop (Val.int (((auK s t (k+1) : ℕ) : ℤ))))) ?_
    exact leR_one hKS_drop ((by simpa [vsz_int] using hb_Kk1I)) hp hKS4
  have hc37 : Pipe main P37 W0 W37 (37 * RB) := Pipe.compMul hc36 hs37
  have hs38 : Pipe main (pRoll 6) W37 W38 RB := by
    have hmem : ∀ w ∈ W37, vsz w ≤ (p+1)^4 := vsz_mem_cons hrecI (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_CI (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_tI (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_pI (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_aI (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_slI (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_mI (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_kI (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_pI (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_aI (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_sI (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_tI (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_piI (sq_le_four p)) ((by simp))))))))))))))
    refine Pipe.le (Pipe.rollAt main hRoll (A := W37) (j := 6) (by simp [W37]) (B := W38) ?_) ?_
    · simp only [W37, W38, List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, List.eraseIdx_nil]
    exact leR_rollV hKS_roll (by omega) (szl_take_le16 hmem (by omega)) hp (by omega)
  have hc38 : Pipe main P38 W0 W38 (38 * RB) := Pipe.compMul hc37 hs38
  have hs39 : Pipe main pDrop W38 W39 RB := by
    refine Pipe.le (Pipe.appendTail W39 (Pipe.drop main hDrop (Val.int (((auM p α : ℕ) : ℤ))))) ?_
    exact leR_one hKS_drop ((by simpa [vsz_int] using hb_mI)) hp hKS4
  have hc39 : Pipe main P39 W0 W39 (39 * RB) := Pipe.compMul hc38 hs39
  have hs40 : Pipe main (pRoll 6) W39 W40 RB := by
    have hmem : ∀ w ∈ W39, vsz w ≤ (p+1)^4 := vsz_mem_cons hrecI (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_CI (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_tI (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_pI (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_aI (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_slI (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_kI (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_pI (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_aI (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_sI (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_tI (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_piI (sq_le_four p)) ((by simp)))))))))))))
    refine Pipe.le (Pipe.rollAt main hRoll (A := W39) (j := 6) (by simp [W39]) (B := W40) ?_) ?_
    · simp only [W39, W40, List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, List.eraseIdx_nil]
    exact leR_rollV hKS_roll (by omega) (szl_take_le16 hmem (by omega)) hp (by omega)
  have hc40 : Pipe main P40 W0 W40 (40 * RB) := Pipe.compMul hc39 hs40
  have hs41 : Pipe main pDrop W40 W41 RB := by
    refine Pipe.le (Pipe.appendTail W41 (Pipe.drop main hDrop (Val.int ((k : ℤ))))) ?_
    exact leR_one hKS_drop ((by simpa [vsz_int] using hb_kI)) hp hKS4
  have hc41 : Pipe main P41 W0 W41 (41 * RB) := Pipe.compMul hc40 hs41
  have hs42 : Pipe main (pRoll 1) W41 W42 RB := by
    have hmem : ∀ w ∈ W41, vsz w ≤ (p+1)^4 := vsz_mem_cons hrecI (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_CI (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_tI (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_pI (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_aI (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_slI (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_pI (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_aI (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_sI (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_tI (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_piI (sq_le_four p)) ((by simp))))))))))))
    refine Pipe.le (Pipe.rollAt main hRoll (A := W41) (j := 1) (by simp [W41]) (B := W42) ?_) ?_
    · simp only [W41, W42, List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, List.eraseIdx_nil]
    exact leR_rollV hKS_roll (by omega) (szl_take_le16 hmem (by omega)) hp (by omega)
  have hc42 : Pipe main P42 W0 W42 (42 * RB) := Pipe.compMul hc41 hs42
  have hs43 : Pipe main pDrop W42 W43 RB := by
    refine Pipe.le (Pipe.appendTail W43 (Pipe.drop main hDrop (Val.int (auC p α s t k)))) ?_
    exact leR_one hKS_drop ((by simpa [vsz_int] using hb_CI)) hp hKS4
  have hc43 : Pipe main P43 W0 W43 (43 * RB) := Pipe.compMul hc42 hs43
  have hs44 : Pipe main (pRoll 1) W43 W44 RB := by
    have hmem : ∀ w ∈ W43, vsz w ≤ (p+1)^4 := vsz_mem_cons hrecI (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_tI (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_pI (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_aI (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_slI (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_pI (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_aI (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_sI (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_tI (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_piI (sq_le_four p)) ((by simp)))))))))))
    refine Pipe.le (Pipe.rollAt main hRoll (A := W43) (j := 1) (by simp [W43]) (B := W44) ?_) ?_
    · simp only [W43, W44, List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, List.eraseIdx_nil]
    exact leR_rollV hKS_roll (by omega) (szl_take_le16 hmem (by omega)) hp (by omega)
  have hc44 : Pipe main P44 W0 W44 (44 * RB) := Pipe.compMul hc43 hs44
  have hs45 : Pipe main pDrop W44 W45 RB := by
    refine Pipe.le (Pipe.appendTail W45 (Pipe.drop main hDrop (Val.int ((t : ℤ))))) ?_
    exact leR_one hKS_drop ((by simpa [vsz_int] using hb_tI)) hp hKS4
  have hc45 : Pipe main P45 W0 W45 (45 * RB) := Pipe.compMul hc44 hs45
  have hs46 : Pipe main (pRoll 1) W45 W46 RB := by
    have hmem : ∀ w ∈ W45, vsz w ≤ (p+1)^4 := vsz_mem_cons hrecI (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_pI (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_aI (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_slI (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_pI (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_aI (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_sI (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_tI (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_piI (sq_le_four p)) ((by simp))))))))))
    refine Pipe.le (Pipe.rollAt main hRoll (A := W45) (j := 1) (by simp [W45]) (B := W46) ?_) ?_
    · simp only [W45, W46, List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, List.eraseIdx_nil]
    exact leR_rollV hKS_roll (by omega) (szl_take_le16 hmem (by omega)) hp (by omega)
  have hc46 : Pipe main P46 W0 W46 (46 * RB) := Pipe.compMul hc45 hs46
  have hs47 : Pipe main pDrop W46 W47 RB := by
    refine Pipe.le (Pipe.appendTail W47 (Pipe.drop main hDrop (Val.int ((p : ℤ))))) ?_
    exact leR_one hKS_drop ((by simpa [vsz_int] using hb_pI)) hp hKS4
  have hc47 : Pipe main P47 W0 W47 (47 * RB) := Pipe.compMul hc46 hs47
  have hs48 : Pipe main (pRoll 1) W47 W48 RB := by
    have hmem : ∀ w ∈ W47, vsz w ≤ (p+1)^4 := vsz_mem_cons hrecI (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_aI (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_slI (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_pI (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_aI (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_sI (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_tI (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_piI (sq_le_four p)) ((by simp)))))))))
    refine Pipe.le (Pipe.rollAt main hRoll (A := W47) (j := 1) (by simp [W47]) (B := W48) ?_) ?_
    · simp only [W47, W48, List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, List.eraseIdx_nil]
    exact leR_rollV hKS_roll (by omega) (szl_take_le16 hmem (by omega)) hp (by omega)
  have hc48 : Pipe main P48 W0 W48 (48 * RB) := Pipe.compMul hc47 hs48
  have hs49 : Pipe main pDrop W48 W49 RB := by
    refine Pipe.le (Pipe.appendTail W49 (Pipe.drop main hDrop (Val.int ((α : ℤ))))) ?_
    exact leR_one hKS_drop ((by simpa [vsz_int] using hb_aI)) hp hKS4
  have hc49 : Pipe main P49 W0 W49 (49 * RB) := Pipe.compMul hc48 hs49
  have hs50 : Pipe main (pRoll 1) W49 W50 RB := by
    have hmem : ∀ w ∈ W49, vsz w ≤ (p+1)^4 := vsz_mem_cons hrecI (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_slI (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_pI (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_aI (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_sI (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_tI (sq_le_four p)) (vsz_mem_cons (by simpa [vsz_int] using le_trans hb_piI (sq_le_four p)) ((by simp))))))))
    refine Pipe.le (Pipe.rollAt main hRoll (A := W49) (j := 1) (by simp [W49]) (B := W50) ?_) ?_
    · simp only [W49, W50, List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, List.eraseIdx_nil]
    exact leR_rollV hKS_roll (by omega) (szl_take_le16 hmem (by omega)) hp (by omega)
  have hc50 : Pipe main P50 W0 W50 (50 * RB) := Pipe.compMul hc49 hs50
  have hs51 : Pipe main pConsV W50 W51 RB := by
    refine Pipe.le (Pipe.consVAt main hConsV) (leR_const hKS_cons hKS4)
  have hc51 : Pipe main P51 W0 W51 (51 * RB) := Pipe.compMul hc50 hs51
  -- the final cost bound
  refine Pipe.le hc51 ?_
  have h1 : (51 : ℕ) ≤ (p + 1) ^ 8 := by
    have hp1 : (101 : ℕ) ≤ p + 1 := by omega
    have h2 : 1 ≤ p + 1 := by omega
    calc (51 : ℕ) ≤ 101 := by norm_num
      _ ≤ p + 1 := hp1
      _ = (p + 1) ^ 1 := (pow_one _).symm
      _ ≤ (p + 1) ^ 8 := Nat.pow_le_pow_right h2 (by norm_num)
  simp only [RB]
  exact mul_pow_absorb h1

end Work.Resample
