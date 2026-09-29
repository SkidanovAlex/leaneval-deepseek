import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Resample.auDefs
import Submission.Work.Fx.FxCommon
import Submission.Work.Fx.piDefs

/-!
# Toolkit and size/cost bounds for the weight word (`Work.Resample.auWtWord`)

## `Pipe`

`Pipe main prog A B c` is a `WordR` spec for a word that transforms the *fixed* window `A` of
values at the top of the value stack into the *fixed* window `B`, leaving everything below it
untouched, at cost `<= c`.  This is the shape in which the library words of `KernelLib` /
`IntLib` are chained by hand inside `KernelLib.loop`.  (Same interface as `Work.Fx.Pipe`.)

## Sizes and costs

* `auSZ p` is a uniform bound `isz v <= auSZ p` for every integer value occurring in the
  program (loop state included), where `p` is the precision exponent read from the stack;
* `auSB p KS` bounds the cost of one primitive arithmetic step, provided every word of
  `KernelLib`/`IntLib` has constant `<= KS` (`au_le_one`, `au_le_two`, `au_le_three`,
  `au_le_sq`, `au_le_roll`).

## The fixed values

`auEn p = 2^auPrec p`, `auEnP p = 2^(auPrec p - p)`, `auEn2 p α = 2^(auPrec p - p)·(2α)`,
`auBnd p = (p+10)·2^auPrec p` and the guard flag `auFlg p α t N` are the values the word
computes.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.Resample

open HvdH Computability
open Work.Fx

/-! ## `Pipe`: words acting on a fixed window of values -/

def Pipe (main prog : Cmd) (A B : List Val) (c : ℕ) : Prop :=
  ∀ rest : List Val,
    WordR main prog (fun vs => vs = A ++ rest) (fun _ out => out = B ++ rest) (fun _ => c)

theorem Pipe.le {main prog : Cmd} {A B : List Val} {c c' : ℕ} (h : Pipe main prog A B c)
    (hc : c ≤ c') : Pipe main prog A B c' := by
  intro rest vs hvs s R hR
  obtain ⟨out, s', n, hout, hev, hn, hstk, hoth⟩ := h rest vs hvs s R hR
  exact ⟨out, s', n, hout, hev, le_trans hn hc, hstk, hoth⟩

theorem Pipe.rw {main prog : Cmd} {A B B' : List Val} {c : ℕ} (h : Pipe main prog A B c)
    (hB : B = B') : Pipe main prog A B' c := hB ▸ h

theorem Pipe.comp {main p q : Cmd} {A B D : List Val} {c d : ℕ} (h1 : Pipe main p A B c)
    (h2 : Pipe main q B D d) : Pipe main (.seq p q) A D (c + d) := by
  intro rest vs hvs s R hR
  obtain ⟨mid, s', n1, hmid, hev1, hn1, hstk1, hoth1⟩ := h1 rest vs hvs s R hR
  obtain ⟨out, s'', n2, hout, hev2, hn2, hstk2, hoth2⟩ := h2 rest mid hmid s' R hstk1
  exact ⟨out, s'', n1 + n2, hout, Eval.seq hev1 hev2, Nat.add_le_add hn1 hn2, hstk2,
    fun k hk => by rw [hoth2 k hk, hoth1 k hk]⟩

theorem Pipe.appendTail {main prog : Cmd} {A B : List Val} {c : ℕ} (T : List Val)
    (h : Pipe main prog A B c) : Pipe main prog (A ++ T) (B ++ T) c := by
  intro rest vs hvs s R hR
  obtain ⟨out, s', n, hout, hev, hn, hstk, hoth⟩ :=
    h (T ++ rest) vs (by rw [hvs, List.append_assoc]) s R
      (by simpa only [hvs, List.append_assoc] using hR)
  exact ⟨out, s', n, by rw [hout, List.append_assoc], hev, hn, hstk, hoth⟩

/-! ## Adapters for the library words -/

theorem Pipe.pushVal {main : Cmd} {prog : Val → Cmd} {K : ℕ}
    (h : ∀ (m : Cmd) (v : Val), WordR m (prog v) (fun _ => True)
      (fun vs out => out = v :: vs) (fun _ => K * (vsz v + 1))) (v : Val) :
    Pipe main (prog v) [] [v] (K * (vsz v + 1)) := by
  intro rest vs hvs s R hR
  have hrs : vs = rest := by rw [hvs, List.nil_append]
  obtain ⟨out, s', n, hout, hev, hn, hstk, hoth⟩ := h main v vs trivial s R hR
  exact ⟨out, s', n, by rw [hout, hrs]; rfl, hev, hn, hstk, hoth⟩

theorem Pipe.binOp {main prog : Cmd} {P : ℤ → ℤ → Prop} {f : ℤ → ℤ → ℤ} {C : ℤ → ℤ → ℕ}
    (h : BinOp main prog P f C) {a b : ℤ} (hab : P a b) :
    Pipe main prog [.int a, .int b] [.int (f a b)] (C a b) := by
  intro rest vs hvs s R hR
  have hv2 : vs = .int a :: .int b :: rest := by rw [hvs]; rfl
  obtain ⟨out, s', n, ⟨a', b', rest', hvs', hout⟩, hev, hn, hstk, hoth⟩ :=
    h vs ⟨a, b, rest, hv2, hab⟩ s R hR
  obtain ⟨h1, h2, h3⟩ := int_cons_inj3 (hvs'.symm.trans hv2)
  have hn' : n ≤ C a b := by rw [hv2] at hn; exact hn
  exact ⟨out, s', n, by rw [hout, h1, h2, h3]; rfl, hev, hn', hstk, hoth⟩

theorem Pipe.unOp {main prog : Cmd} {P : ℤ → Prop} {f : ℤ → ℤ} {C : ℤ → ℕ}
    (h : UnOp main prog P f C) {a : ℤ} (ha : P a) :
    Pipe main prog [.int a] [.int (f a)] (C a) := by
  intro rest vs hvs s R hR
  have hv2 : vs = .int a :: rest := by rw [hvs]; rfl
  obtain ⟨out, s', n, ⟨a', rest', hvs', hout⟩, hev, hn, hstk, hoth⟩ :=
    h vs ⟨a, rest, hv2, ha⟩ s R hR
  have h1 := List.cons.inj (hvs'.symm.trans hv2)
  have ha' : a' = a := Val.int.inj h1.1
  have hn' : n ≤ C a := by rw [hv2] at hn; exact hn
  exact ⟨out, s', n, by rw [hout, ha', h1.2]; rfl, hev, hn', hstk, hoth⟩

theorem Pipe.swap {prog : Cmd} {K : ℕ} (main : Cmd)
    (h : ∀ m : Cmd, WordR m prog (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = b :: a :: rest)
      (fun vs => K * (vsz (vs.getD 0 .nil) + vsz (vs.getD 1 .nil) + 1)))
    (a b : Val) : Pipe main prog [a, b] [b, a] (K * (vsz a + vsz b + 1)) := by
  intro rest vs hvs s R hR
  have hv2 : vs = a :: b :: rest := by rw [hvs]; rfl
  obtain ⟨out, s', n, ⟨a', b', rest', hvs', hout⟩, hev, hn, hstk, hoth⟩ :=
    h main vs (by rw [hv2]; simp) s R hR
  obtain ⟨h1, h2, h3⟩ := cons_inj3 (hvs'.symm.trans hv2)
  have hn' : n ≤ K * (vsz a + vsz b + 1) := by
    rw [hv2] at hn
    simpa only [List.getD_cons_zero, List.getD_cons_succ] using hn
  exact ⟨out, s', n, by rw [hout, h1, h2, h3]; rfl, hev, hn', hstk, hoth⟩

theorem Pipe.drop {prog : Cmd} {K : ℕ} (main : Cmd)
    (h : ∀ m : Cmd, WordR m prog (fun vs => vs ≠ [])
      (fun vs out => ∃ v rest, vs = v :: rest ∧ out = rest)
      (fun vs => K * (vsz (vs.headD .nil) + 1)))
    (a : Val) : Pipe main prog [a] [] (K * (vsz a + 1)) := by
  intro rest vs hvs s R hR
  have hv2 : vs = a :: rest := by rw [hvs]; rfl
  obtain ⟨out, s', n, ⟨v, rest', hvs', hout⟩, hev, hn, hstk, hoth⟩ :=
    h main vs (by rw [hv2]; simp) s R hR
  have h1 := List.cons.inj (hvs'.symm.trans hv2)
  have hn' : n ≤ K * (vsz a + 1) := by
    rw [hv2] at hn; simpa only [List.headD_cons] using hn
  exact ⟨out, s', n, by rw [hout, h1.2]; rfl, hev, hn', hstk, hoth⟩

theorem Pipe.dup {prog : Cmd} {K : ℕ} (main : Cmd)
    (h : ∀ m : Cmd, WordR m prog (fun vs => vs ≠ [])
      (fun vs out => ∃ v rest, vs = v :: rest ∧ out = v :: v :: rest)
      (fun vs => K * (vsz (vs.headD .nil) + 1)))
    (a : Val) : Pipe main prog [a] [a, a] (K * (vsz a + 1)) := by
  intro rest vs hvs s R hR
  have hv2 : vs = a :: rest := by rw [hvs]; rfl
  obtain ⟨out, s', n, ⟨v, rest', hvs', hout⟩, hev, hn, hstk, hoth⟩ :=
    h main vs (by rw [hv2]; simp) s R hR
  have h1 := List.cons.inj (hvs'.symm.trans hv2)
  have hn' : n ≤ K * (vsz a + 1) := by
    rw [hv2] at hn; simpa only [List.headD_cons] using hn
  exact ⟨out, s', n, by rw [hout, h1.1, h1.2]; rfl, hev, hn', hstk, hoth⟩

theorem szl_take_le (A : List Val) (m : ℕ) : szl (A.take m) ≤ szl A := by
  have h := szl_append (A.take m) (A.drop m)
  rw [List.take_append_drop] at h
  omega

theorem szl_le_len_mul {A : List Val} {n : ℕ} (h : ∀ v ∈ A, vsz v ≤ n) :
    szl A ≤ A.length * n := by
  induction A with
  | nil => simp [szl]
  | cons a t ih =>
    have ha : vsz a ≤ n := h a (by simp)
    have ht : ∀ v ∈ t, vsz v ≤ n := fun v hv => h v (by simp [hv])
    have := ih ht
    rw [szl_cons, List.length_cons]
    nlinarith [Nat.zero_le (vsz a), Nat.zero_le (szl t)]

theorem Pipe.pick {prog : ℕ → Cmd} {K : ℕ} (main : Cmd)
    (h : ∀ (m : Cmd) (k : ℕ), WordR m (prog k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs)
      (fun vs => K * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    {A : List Val} {k : ℕ} (hk : k < A.length) :
    Pipe main (prog k) A (A.getD k .nil :: A) (K * (k + 1) * (szl (A.take (k + 1)) + 1)) := by
  intro rest vs hvs s R hR
  have hlt : k < vs.length := by rw [hvs]; simp only [List.length_append]; omega
  obtain ⟨out, s', n, hout, hev, hn, hstk, hoth⟩ := h main k vs hlt s R hR
  have hn' : n ≤ K * (k + 1) * (szl (A.take (k + 1)) + 1) := by
    have h : n ≤ K * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1) := hn
    rw [hvs, List.take_append_of_le_length (by omega)] at h
    simpa [szl] using h
  refine ⟨out, s', n, ?_, hev, hn', hstk, hoth⟩
  rw [hout, hvs, getD_append_of_lt hk]
  rfl

theorem Pipe.roll {prog : ℕ → Cmd} {K : ℕ} (main : Cmd)
    (h : ∀ (m : Cmd) (k : ℕ), WordR m (prog k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs.eraseIdx k)
      (fun vs => K * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    {A : List Val} {k : ℕ} (hk : k < A.length) :
    Pipe main (prog k) A (A.getD k .nil :: A.eraseIdx k)
      (K * (k + 1) * (szl (A.take (k + 1)) + 1)) := by
  intro rest vs hvs s R hR
  have hlt : k < vs.length := by rw [hvs]; simp only [List.length_append]; omega
  obtain ⟨out, s', n, hout, hev, hn, hstk, hoth⟩ := h main k vs hlt s R hR
  have hn' : n ≤ K * (k + 1) * (szl (A.take (k + 1)) + 1) := by
    have h : n ≤ K * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1) := hn
    rw [hvs, List.take_append_of_le_length (by omega)] at h
    simpa [szl] using h
  refine ⟨out, s', n, ?_, hev, hn', hstk, hoth⟩
  rw [hout, hvs, getD_append_of_lt hk, eraseIdx_append_of_lt hk, List.cons_append]

/-! ## Cost helpers -/


theorem Pipe.pushOnAny {main prog : Cmd} {v : Val} {c : ℕ} {T : List Val}
    (h : WordR main prog (fun _ => True) (fun vs out => out = v :: vs) (fun _ => c)) :
    Pipe main prog T (v :: T) c := by
  intro rest vs hvs s R hR
  obtain ⟨out, s', n, hout, hev, hn, hstk, hoth⟩ := h vs trivial s R hR
  exact ⟨out, s', n, by rw [hout, hvs]; rfl, hev, hn, hstk, hoth⟩

theorem Pipe.pickAt {prog : ℕ → Cmd} {K : ℕ} (main : Cmd)
    (h : ∀ (m : Cmd) (k : ℕ), WordR m (prog k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs)
      (fun vs => K * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    {A : List Val} {k : ℕ} (hk : k < A.length) {v : Val} (hv : A.getD k .nil = v) :
    Pipe main (prog k) A (v :: A) (K * (k + 1) * (szl (A.take (k + 1)) + 1)) := by
  refine Pipe.rw (Pipe.pick main h hk) ?_
  rw [hv]
/-! ## Uniform size and cost bounds -/

/-- Uniform bound on `isz` for every value occurring in the weight program. -/
def auSZ (p : ℕ) : ℕ := 10 * p + 400

/-- Uniform bound on the cost of one primitive arithmetic step. -/
def auSB (p KS : ℕ) : ℕ := KS * (auSZ p + 8) ^ 2

theorem auSZ_ge (p : ℕ) : 400 ≤ auSZ p := by simp only [auSZ]; omega

theorem auSB_mono {p KS KS' : ℕ} (h : KS ≤ KS') : auSB p KS ≤ auSB p KS' :=
  Nat.mul_le_mul_right _ h

theorem au_le_one {K KS p : ℕ} (hK : K ≤ KS) {v : ℕ} (hv : v ≤ auSZ p) :
    K * (v + 1) ≤ auSB p KS := by
  rw [auSB]
  calc K * (v + 1) ≤ KS * (v + 1) := Nat.mul_le_mul_right _ hK
    _ ≤ KS * (auSZ p + 8) ^ 2 :=
        Nat.mul_le_mul_left _ (by nlinarith [auSZ_ge p, Nat.zero_le v])

theorem au_le_two {K KS p : ℕ} (hK : K ≤ KS) {u v : ℕ} (hu : u ≤ auSZ p) (hv : v ≤ auSZ p) :
    K * (u + v) ≤ auSB p KS := by
  rw [auSB]
  calc K * (u + v) ≤ KS * (2 * auSZ p) := Nat.mul_le_mul hK (by omega)
    _ ≤ KS * (auSZ p + 8) ^ 2 := Nat.mul_le_mul_left _ (by nlinarith [auSZ_ge p])

theorem au_le_three {K KS p : ℕ} (hK : K ≤ KS) {u v w : ℕ} (hu : u ≤ auSZ p)
    (hv : v ≤ auSZ p) (hw : w ≤ auSZ p) : K * (u + v + w) ≤ auSB p KS := by
  rw [auSB]
  calc K * (u + v + w) ≤ KS * (3 * auSZ p) := Nat.mul_le_mul hK (by omega)
    _ ≤ KS * (auSZ p + 8) ^ 2 := Nat.mul_le_mul_left _ (by nlinarith [auSZ_ge p])

theorem au_le_sq {K KS p : ℕ} (hK : K ≤ KS) {u : ℕ} (hu : u ≤ auSZ p) :
    K * u ^ 2 ≤ auSB p KS := by
  rw [auSB]
  calc K * u ^ 2 ≤ KS * (auSZ p) ^ 2 := Nat.mul_le_mul hK (Nat.pow_le_pow_left hu 2)
    _ ≤ KS * (auSZ p + 8) ^ 2 := Nat.mul_le_mul_left _ (by nlinarith [auSZ_ge p])

theorem au_le_roll {K KS p : ℕ} (hK : K ≤ KS) {A : List Val} {k : ℕ}
    (hk : k ≤ 15) (hAlen : A.length ≤ 16) (hA : ∀ v ∈ A, vsz v ≤ auSZ p) :
    K * (k + 1) * ((szl (A.take (k + 1))) + 1) ≤ auSB p KS := by
  have hlen : (A.take (k + 1)).length ≤ 16 := by
    rw [List.length_take]
    omega
  have hsum : szl (A.take (k + 1)) ≤ 16 * auSZ p :=
    le_trans (szl_le_len_mul (A := A.take (k + 1)) (n := auSZ p)
      (fun v hv => hA v (List.mem_of_mem_take hv))) (Nat.mul_le_mul_right _ hlen)
  have hle : 16 * (16 * auSZ p + 1) ≤ (auSZ p + 8) ^ 2 := by
    nlinarith [auSZ_ge p]
  rw [auSB]
  calc K * (k + 1) * (szl (A.take (k + 1)) + 1)
      ≤ KS * 16 * (16 * auSZ p + 1) := Nat.mul_le_mul (Nat.mul_le_mul hK (by omega)) (by omega)
    _ = KS * (16 * (16 * auSZ p + 1)) := by ring
    _ ≤ KS * (auSZ p + 8) ^ 2 := Nat.mul_le_mul_left _ hle

/-- `szl` of a window whose entries are all bounded. -/
theorem szl_le_of_mem {A : List Val} {M : ℕ} (h : ∀ v ∈ A, vsz v ≤ M) :
    szl A ≤ A.length * M := szl_le_len_mul h

/-! ## Integer values used by the program -/

/-- `2 ^ auPrec p` -/
def auEn (p : ℕ) : ℤ := (2 : ℤ) ^ auPrec p

/-- `2 ^ (auPrec p - p)` -/
def auEnP (p : ℕ) : ℤ := (2 : ℤ) ^ (auPrec p - p)

/-- `2^(auPrec p - p) · (2α)`, the denominator of the final division -/
def auEn2 (p α : ℕ) : ℤ := auEnP p * (2 * (α : ℤ))

/-- `(p+10) · 2^auPrec p`, the guard bound -/
def auBnd (p : ℕ) : ℤ := ((p + 10 : ℕ) : ℤ) * auEn p

/-- the guard flag: `1` iff the exponent exceeds the guard bound (weight `0`) -/
def auFlg (p α t : ℕ) (N : ℤ) : ℤ := if auBnd p < auZ p α t N then 1 else 0

/-! ## Size bounds for the individual values -/


theorem three_mul_add_le (p : ℕ) : 3 * p + 100 ≤ 103 * 2 ^ p := by
  have hp : p ≤ 2 ^ p := le_of_lt (Nat.lt_two_pow_self (n := p))
  have h1 : 3 * p ≤ 3 * 2 ^ p := Nat.mul_le_mul_left 3 hp
  have h2 : (100 : ℕ) ≤ 100 * 2 ^ p := by
    have h3 : 1 ≤ 2 ^ p := Nat.one_le_two_pow
    nlinarith
  calc 3 * p + 100 ≤ 3 * 2 ^ p + 100 * 2 ^ p := by omega
    _ = 103 * 2 ^ p := by ring

theorem isz_pow2_le {p k : ℕ} (hk : k + 3 ≤ auSZ p) : isz ((2 : ℤ) ^ k) ≤ auSZ p := by
  have hsz : auSZ p = 10 * p + 400 := rfl
  rw [isz, Int.natAbs_pow]
  have h2 : ((2 : ℤ)).natAbs = 2 := by norm_num
  rw [h2]
  have h1 : (2 ^ k).size ≤ k + 1 := by
    rw [Nat.size_le]
    exact Nat.pow_lt_pow_right one_lt_two (by omega)
  omega

theorem isz_le_pow2 {p m : ℕ} (h : m ≤ 2 ^ p) : isz ((m : ℤ)) ≤ auSZ p := by
  have hsz : auSZ p = 10 * p + 400 := rfl
  rw [isz, Int.natAbs_natCast]
  have h1 : m.size ≤ p + 1 := by
    rw [Nat.size_le]
    calc m ≤ 2 ^ p := h
      _ < 2 ^ (p + 1) := Nat.pow_lt_pow_right one_lt_two (by omega)
  omega

theorem isz_const_le (p : ℕ) {m : ℕ} (h : m ≤ 400) : isz ((m : ℤ)) ≤ auSZ p := by
  have hsz : auSZ p = 10 * p + 400 := rfl
  rw [isz, Int.natAbs_natCast]
  have h1 : m.size ≤ 9 := by
    rw [Nat.size_le]
    exact lt_of_le_of_lt h (by norm_num)
  omega

theorem isz_auPrec_le (p : ℕ) : isz ((auPrec p : ℕ) : ℤ) ≤ auSZ p := by
  have hsz : auSZ p = 10 * p + 400 := rfl
  rw [isz, Int.natAbs_natCast]
  have h1 : auPrec p < 2 ^ (p + 8) := by
    have h4 : 103 * 2 ^ p < 256 * 2 ^ p :=
      Nat.mul_lt_mul_of_pos_right (by norm_num) (Nat.two_pow_pos p)
    calc auPrec p = 3 * p + 100 := rfl
      _ ≤ 103 * 2 ^ p := three_mul_add_le p
      _ < 256 * 2 ^ p := h4
      _ = 2 ^ (p + 8) := by
          rw [show (256 : ℕ) = 2 ^ 8 by norm_num, ← pow_add, Nat.add_comm]
  have h2 : (auPrec p).size ≤ p + 8 := Nat.size_le.mpr h1
  omega

theorem isz_auNstep_le (p : ℕ) : isz ((auNstep p : ℕ) : ℤ) ≤ auSZ p := by
  have hsz : auSZ p = 10 * p + 400 := rfl
  rw [isz, Int.natAbs_natCast]
  have h1 : auNstep p < 2 ^ (p + 9) := by
    have h4 : 206 * 2 ^ p < 256 * 2 ^ p :=
      Nat.mul_lt_mul_of_pos_right (by norm_num) (Nat.two_pow_pos p)
    calc auNstep p = 2 * (3 * p + 100) := rfl
      _ ≤ 2 * (103 * 2 ^ p) := Nat.mul_le_mul_left 2 (three_mul_add_le p)
      _ = 206 * 2 ^ p := by ring
      _ < 256 * 2 ^ p := h4
      _ = 2 ^ (p + 8) := by
          rw [show (256 : ℕ) = 2 ^ 8 by norm_num, ← pow_add, Nat.add_comm]
      _ ≤ 2 ^ (p + 9) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : (auNstep p).size ≤ p + 9 := Nat.size_le.mpr h1
  omega

theorem isz_auEn_le (p : ℕ) : isz (auEn p) ≤ auSZ p := by
  rw [auEn]
  exact isz_pow2_le (by simp only [auPrec, auSZ]; omega)

theorem natAbs_auEnP_le (p : ℕ) : (auEnP p).natAbs ≤ 2 ^ (2 * p + 100) := by
  rw [auEnP, Int.natAbs_pow]
  have h2 : ((2 : ℤ)).natAbs = 2 := by norm_num
  rw [h2]
  apply Nat.pow_le_pow_right (by norm_num)
  simp only [auPrec]; omega

theorem isz_auEnP_le (p : ℕ) : isz (auEnP p) ≤ auSZ p := by
  have hsz : auSZ p = 10 * p + 400 := rfl
  rw [isz]
  have h1 : (auEnP p).natAbs < 2 ^ (2 * p + 101) :=
    lt_of_le_of_lt (natAbs_auEnP_le p) (Nat.pow_lt_pow_right one_lt_two (by omega))
  have h2 : ((auEnP p).natAbs).size ≤ 2 * p + 101 := Nat.size_le.mpr h1
  omega

theorem natAbs_auEn2_le (p α : ℕ) (hα : α ≤ 2 ^ p) : (auEn2 p α).natAbs ≤ 2 ^ (3 * p + 101) := by
  rw [auEn2, Int.natAbs_mul]
  have h1 : (2 * (α : ℤ)).natAbs ≤ 2 ^ (p + 1) := by
    rw [show (2 * (α : ℤ)) = ((2 * α : ℕ) : ℤ) by push_cast; ring, Int.natAbs_natCast]
    calc 2 * α ≤ 2 * 2 ^ p := Nat.mul_le_mul_left 2 hα
      _ = 2 ^ (p + 1) := by rw [pow_succ]; ring
  calc (auEnP p).natAbs * (2 * (α : ℤ)).natAbs
      ≤ 2 ^ (2 * p + 100) * 2 ^ (p + 1) := Nat.mul_le_mul (natAbs_auEnP_le p) h1
    _ = 2 ^ (3 * p + 101) := by rw [← pow_add]; ring_nf

theorem isz_auEn2_le (p α : ℕ) (hα : α ≤ 2 ^ p) : isz (auEn2 p α) ≤ auSZ p := by
  have hsz : auSZ p = 10 * p + 400 := rfl
  rw [isz]
  have h1 : (auEn2 p α).natAbs < 2 ^ (3 * p + 102) :=
    lt_of_le_of_lt (natAbs_auEn2_le p α hα) (Nat.pow_lt_pow_right one_lt_two (by omega))
  have h2 : ((auEn2 p α).natAbs).size ≤ 3 * p + 102 := Nat.size_le.mpr h1
  omega

theorem auEn_pos (p : ℕ) : 0 < auEn p := by rw [auEn]; positivity

theorem natAbs_auBnd_le (p : ℕ) : (auBnd p).natAbs ≤ 2 ^ (4 * p + 104) := by
  rw [auBnd, Int.natAbs_mul, Int.natAbs_natCast, auEn, Int.natAbs_pow]
  have h2 : ((2 : ℤ)).natAbs = 2 := by norm_num
  rw [h2]
  have hp : p ≤ 2 ^ p := le_of_lt (Nat.lt_two_pow_self (n := p))
  have h4 : 1 ≤ 2 ^ p := Nat.one_le_two_pow
  have hp10 : p + 10 ≤ 2 ^ (p + 4) := by
    have h3 : 2 ^ (p + 4) = 16 * 2 ^ p := by rw [pow_add]; ring
    have h5 : p + 10 ≤ 16 * 2 ^ p := by nlinarith
    omega
  calc (p + 10) * 2 ^ auPrec p ≤ 2 ^ (p + 4) * 2 ^ auPrec p := Nat.mul_le_mul_right _ hp10
    _ = 2 ^ (4 * p + 104) := by
        rw [← pow_add]
        congr 1
        simp only [auPrec]; ring

theorem isz_auBnd_le (p : ℕ) : isz (auBnd p) ≤ auSZ p := by
  have hsz : auSZ p = 10 * p + 400 := rfl
  rw [isz]
  have h1 : (auBnd p).natAbs < 2 ^ (4 * p + 105) :=
    lt_of_le_of_lt (natAbs_auBnd_le p) (Nat.pow_lt_pow_right one_lt_two (by omega))
  have h2 : ((auBnd p).natAbs).size ≤ 4 * p + 105 := Nat.size_le.mpr h1
  omega

theorem auBnd_nonneg (p : ℕ) : 0 ≤ auBnd p := by
  rw [auBnd]
  exact mul_nonneg (Int.natCast_nonneg _) (le_of_lt (auEn_pos p))

/-! ## The fixed-point value of `π` -/

theorem Dval_natAbs_le (n : ℕ) : (Work.Fx.Dval n).natAbs ≤ 2 ^ (4 * n + 1) := by
  rw [Work.Fx.Dval, Int.natAbs_natCast]
  apply le_of_lt
  rw [Nat.sqrt_lt']
  have hC : Work.Fx.C0c n = ((2 : ℕ) ^ (8 * n + 1) : ℤ) := by
    rw [Work.Fx.C0c]
    congr 1
    simp only [Work.Fx.qq]
    ring
  have h1 : (Work.Fx.C0c n - Work.Fx.aval n n).toNat ≤ 2 ^ (8 * n + 1) := by
    rw [Int.toNat_le, hC]
    push_cast
    exact Int.sub_le_self _ (Work.Fx.sq_nonneg' n n)
  have h2 : (2 : ℕ) ^ (8 * n + 1) < ((2 : ℕ) ^ (4 * n + 1)) ^ 2 := by
    rw [← pow_mul]
    exact Nat.pow_lt_pow_right one_lt_two (by omega)
  exact lt_of_le_of_lt h1 h2

theorem Nval_nonneg (n : ℕ) : 0 ≤ Work.Fx.Nval n := by
  rw [Work.Fx.Nval]
  have h1 : 0 ≤ Work.Fx.Dval n * 2 ^ (2 * n + 1) :=
    mul_nonneg (Int.natCast_nonneg _) (pow_nonneg (by norm_num) _)
  have h2 : 0 < (2 : ℤ) ^ (Work.Fx.qq n - 1) := pow_pos (by norm_num) _
  linarith

theorem Nval_natAbs_le (n : ℕ) : (Work.Fx.Nval n).natAbs ≤ 2 ^ (6 * n + 3) := by
  have hD := Dval_natAbs_le n
  have hDn : 0 ≤ Work.Fx.Dval n := Int.natCast_nonneg _
  have h3 : ((2 : ℤ) ^ (Work.Fx.qq n - 1)).natAbs = 2 ^ (Work.Fx.qq n - 1) := by
    rw [Int.natAbs_pow]
    have h2 : ((2 : ℤ)).natAbs = 2 := by norm_num
    rw [h2]
  have hDmul : (Work.Fx.Dval n * 2 ^ (2 * n + 1)).natAbs
      = (Work.Fx.Dval n).natAbs * 2 ^ (2 * n + 1) := by
    rw [Int.natAbs_mul, Int.natAbs_pow]
    norm_num
  rw [Work.Fx.Nval]
  calc (Work.Fx.Dval n * 2 ^ (2 * n + 1) + 2 ^ (Work.Fx.qq n - 1)).natAbs
      ≤ (Work.Fx.Dval n * 2 ^ (2 * n + 1)).natAbs
          + ((2 : ℤ) ^ (Work.Fx.qq n - 1)).natAbs := Int.natAbs_add_le _ _
    _ = (Work.Fx.Dval n).natAbs * 2 ^ (2 * n + 1) + 2 ^ (Work.Fx.qq n - 1) := by
        rw [hDmul, h3]
    _ ≤ 2 ^ (4 * n + 1) * 2 ^ (2 * n + 1) + 2 ^ (4 * n) := by
        have h4 : 2 ^ (Work.Fx.qq n - 1) ≤ 2 ^ (4 * n) := by
          apply Nat.pow_le_pow_right (by norm_num)
          simp only [Work.Fx.qq]; omega
        exact Nat.add_le_add (Nat.mul_le_mul_right _ hD) h4
    _ = 2 ^ (6 * n + 2) + 2 ^ (4 * n) := by rw [← pow_add]; ring_nf
    _ ≤ 2 ^ (6 * n + 3) := by
        have h6 : 2 ^ (4 * n) ≤ 2 ^ (6 * n + 2) :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
        have h7 : 2 ^ (6 * n + 2) + 2 ^ (6 * n + 2) = 2 ^ (6 * n + 3) := by
          calc 2 ^ (6 * n + 2) + 2 ^ (6 * n + 2) = 2 * 2 ^ (6 * n + 2) := by ring
            _ = 2 ^ (6 * n + 3) := by
                rw [show 6 * n + 3 = 6 * n + 2 + 1 by omega, pow_succ]; ring
        omega

theorem uval_natAbs_le (n : ℕ) : (Work.Fx.uval n).natAbs ≤ 2 ^ (2 * n + 3) := by
  have hb : (0 : ℤ) ≤ (2 : ℤ) ^ Work.Fx.qq n := pow_nonneg (by norm_num) _
  have hf : Work.Fx.uval n = Work.Fx.Nval n / (2 : ℤ) ^ Work.Fx.qq n := by
    rw [Work.Fx.uval, Int.fdiv_eq_ediv, if_pos (Or.inl hb), sub_zero]
  have hb2 : ((2 : ℤ) ^ Work.Fx.qq n).natAbs = 2 ^ (4 * n) := by
    rw [Int.natAbs_pow]
    have h2 : ((2 : ℤ)).natAbs = 2 := by norm_num
    rw [h2, show Work.Fx.qq n = 4 * n from rfl]
  rw [hf, Int.natAbs_ediv, if_pos (Or.inl (Nval_nonneg n)), add_zero, hb2]
  refine Nat.div_le_of_le_mul ?_
  calc (Work.Fx.Nval n).natAbs ≤ 2 ^ (6 * n + 3) := Nval_natAbs_le n
    _ = 2 ^ (4 * n) * 2 ^ (2 * n + 3) := by
        rw [← pow_add]
        congr 1
        ring

theorem natAbs_auPi_le (p : ℕ) : (auPi p).natAbs ≤ 2 ^ (6 * p + 205) := by
  have h := uval_natAbs_le (auPrec p)
  simp only [auPi]
  calc (Work.Fx.uval (auPrec p)).natAbs ≤ 2 ^ (2 * auPrec p + 3) := h
    _ = 2 ^ (6 * p + 203) := by
        congr 1
        simp only [auPrec]
        ring
    _ ≤ 2 ^ (6 * p + 205) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- `isz (auPi p) ≤ auSZ p`: the fixed-point value of `π` fits the uniform size bound. -/
theorem isz_auPi_le (p : ℕ) : isz (auPi p) ≤ auSZ p := by
  have hsz : auSZ p = 10 * p + 400 := rfl
  have h : (auPi p).natAbs ≤ 2 ^ (6 * p + 203) := by
    have h0 := uval_natAbs_le (auPrec p)
    simp only [auPi]
    calc (Work.Fx.uval (auPrec p)).natAbs ≤ 2 ^ (2 * auPrec p + 3) := h0
      _ = 2 ^ (6 * p + 203) := by
          congr 1
          simp only [auPrec]
          ring
  rw [isz]
  have h1 : (auPi p).natAbs < 2 ^ (6 * p + 204) :=
    lt_of_le_of_lt h (Nat.pow_lt_pow_right one_lt_two (by omega))
  have h2 : ((auPi p).natAbs).size ≤ 6 * p + 204 := Nat.size_le.mpr h1
  omega

theorem auPi_nonneg (p : ℕ) : 0 ≤ auPi p := by
  rw [auPi, Work.Fx.uval, Int.fdiv_eq_ediv]
  have hb : (0 : ℤ) ≤ (2 : ℤ) ^ Work.Fx.qq (auPrec p) := pow_nonneg (by norm_num) _
  rw [if_pos (Or.inl hb)]
  exact Int.ediv_nonneg (Nval_nonneg _) hb

theorem auZ_nonneg (p α t : ℕ) (N : ℤ) (hN : 0 ≤ N) : 0 ≤ auZ p α t N := by
  rw [auZ]
  refine Int.tdiv_nonneg (mul_nonneg (auPi_nonneg p) hN) ?_
  exact mul_nonneg (sq_nonneg _) (sq_nonneg _)

theorem natAbs_auZ_le (p α t : ℕ) (N : ℤ) (hN : N.natAbs ≤ 2 ^ (4 * p + 8)) :
    (auZ p α t N).natAbs ≤ 2 ^ (10 * p + 213) := by
  rw [auZ, Int.natAbs_tdiv]
  have h2 : (auPi p * N).natAbs ≤ 2 ^ (10 * p + 213) := by
    rw [Int.natAbs_mul]
    calc (auPi p).natAbs * N.natAbs ≤ 2 ^ (6 * p + 205) * 2 ^ (4 * p + 8) :=
          Nat.mul_le_mul (natAbs_auPi_le p) hN
      _ = 2 ^ (10 * p + 213) := by rw [← pow_add]; ring_nf
  exact le_trans (Nat.div_le_self _ _) h2

theorem isz_auZ_le (p α t : ℕ) (N : ℤ) (hN : N.natAbs ≤ 2 ^ (4 * p + 8)) :
    isz (auZ p α t N) ≤ auSZ p := by
  have hsz : auSZ p = 10 * p + 400 := rfl
  rw [isz]
  have h1 : (auZ p α t N).natAbs < 2 ^ (10 * p + 214) :=
    lt_of_le_of_lt (natAbs_auZ_le p α t N hN) (Nat.pow_lt_pow_right one_lt_two (by omega))
  have h2 : ((auZ p α t N).natAbs).size ≤ 10 * p + 214 := Nat.size_le.mpr h1
  omega

theorem natAbs_auZ_guard (p α t : ℕ) (N : ℤ) (h0 : 0 ≤ auZ p α t N)
    (h : auZ p α t N ≤ auBnd p) : (auZ p α t N).natAbs ≤ 2 ^ (4 * p + 110) := by
  have h1 : (auZ p α t N : ℤ) ≤ ((auBnd p).natAbs : ℤ) :=
    le_trans h Int.le_natAbs
  have h2 : (auZ p α t N).natAbs ≤ (auBnd p).natAbs := by
    have h3 : ((auZ p α t N).natAbs : ℤ) ≤ ((auBnd p).natAbs : ℤ) := by
      rwa [← Int.natAbs_of_nonneg h0] at h1
    exact_mod_cast h3
  calc (auZ p α t N).natAbs ≤ (auBnd p).natAbs := h2
    _ ≤ 2 ^ (4 * p + 104) := natAbs_auBnd_le p
    _ ≤ 2 ^ (4 * p + 110) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem isz_auFlg_le (p α t : ℕ) (N : ℤ) : isz (auFlg p α t N) ≤ auSZ p := by
  rw [auFlg]
  split
  · exact isz_const_le p (by norm_num)
  · exact isz_const_le p (by norm_num)

end Work.Resample
