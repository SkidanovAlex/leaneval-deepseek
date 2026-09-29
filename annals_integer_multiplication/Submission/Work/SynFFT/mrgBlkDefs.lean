import Mathlib
import Submission.Work.SynFFT.kit2

/-!
# SynFFT, the interleave ("merge") block pass: shared definitions and `WordR` plumbing

`HasMrgBlk` (`Submission/Work/SynFFT/kit2.lean`) asks for a word which, given the `2s`
coefficient vectors of one block, approximating an array `u`, produces the *interleave*
`mrgN r s u` — i.e. the list whose `q`-th entry is the `(q/2 + (q%2)*s)`-th input entry.

At the list level the interleaved list is obtained by cutting the block into its two halves
`ws.take s` and `ws.drop s` and concatenating the pairs `(ws_i, ws_{i+s})`:

`mrgBlkL s ws = ((List.range s).map (fun i => [ws i, ws (i+s)])).flatten`.

This module fixes that object and collects the `WordR` plumbing used to build the pieces of
the block pass.  The plumbing lemmas in the namespace `Work.SynFFT.MrgKit` are copied from
`Submission/Work/SynFFT/hasYMul.lean` (which does not currently build, due to a heartbeat
timeout in its final assembly, so it cannot be imported; the copies are verbatim).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace Work.SynFFT

open HvdH
open Computability

/-- The `2s` coefficient vectors of the interleave of one block, as the concatenation of the
pairs `(ws_i, ws_{i+s})` for `i < s`.  For `ws.length = 2s` this is exactly the list
representing `mrgN r s u`. -/
def mrgBlkL (s : ℕ) (ws : List (List (ℤ × ℤ))) : List (List (ℤ × ℤ)) :=
  ((List.range s).map (fun i => [ws.getD i [], ws.getD (i + s) []])).flatten

/-- `cvecs` commutes with `take`. -/
lemma cvecs_take (s : ℕ) (ws : List (List (ℤ × ℤ))) :
    cvecs (ws.take s) = (cvecs ws).take s := by
  simp [cvecs, List.map_take]

/-- `cvecs` commutes with `drop`. -/
lemma cvecs_drop (s : ℕ) (ws : List (List (ℤ × ℤ))) :
    cvecs (ws.drop s) = (cvecs ws).drop s := by
  simp [cvecs, List.map_drop]

end Work.SynFFT

namespace Work.SynFFT.MrgKit

open HvdH
open Computability

local infixr:68 " ;;; " => HvdH.Cmd.seq

/-! ## Size bookkeeping -/

theorem encodeNat_len (n : ℕ) : (encodeNat n).length = n.size := by
  have hpos : ∀ p : PosNum, (encodePosNum p).length = PosNum.natSize p := by
    intro p
    induction p with
    | one => rfl
    | bit0 n ih => simp [encodePosNum, PosNum.natSize, ih]
    | bit1 n ih => simp [encodePosNum, PosNum.natSize, ih]
  have hnum : ∀ n : Num, (encodeNum n).length = Num.natSize n := by
    intro n
    cases n with
    | zero => rfl
    | pos p => simp [encodeNum, Num.natSize, hpos p]
  show (encodeNum (↑n : Num)).length = n.size
  rw [hnum, Num.natSize_to_nat, Num.to_of_nat]

theorem vsz_int' (z : ℤ) : vsz (.int z) = isz z := by
  show ((if z < 0 then Glyph.neg else Glyph.pos) ::
    ((encodeNat z.natAbs).map Glyph.bit ++ [Glyph.iend])).length = isz z
  rw [List.length_cons, List.length_append, List.length_map, List.length_singleton,
    encodeNat_len, isz]

theorem vsz_cons' (a b : Val) : vsz (.cons a b) = vsz a + vsz b + 1 := by
  simp [vsz, Val.enc, List.length_append]

theorem vsz_cfxVal' (z : ℤ × ℤ) : vsz (cfxVal z) = isz z.1 + isz z.2 + 1 := by
  simp [cfxVal, vsz_cons', vsz_int']

theorem vsz_ofList (xs : List Val) : vsz (ofList xs) = xs.length + (xs.map vsz).sum + 1 := by
  induction xs with
  | nil => rfl
  | cons a t ih =>
    have h : vsz (Val.cons a (ofList t)) = vsz a + vsz (ofList t) + 1 := by simp [vsz, Val.enc]
    rw [show ofList (a :: t) = Val.cons a (ofList t) from rfl, h, ih]
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    ring

theorem sum_le_of_forall {α : Type} (f : α → ℕ) : ∀ (xs : List α) (B : ℕ),
    (∀ x ∈ xs, f x ≤ B) → (xs.map f).sum ≤ xs.length * B
  | [], B, _ => by simp
  | a :: t, B, h => by
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have ha : f a ≤ B := h a (by simp)
    have ht : ∀ x ∈ t, f x ≤ B := fun x hx => h x (by simp [hx])
    have ih := sum_le_of_forall f t B ht
    nlinarith

theorem natAbs_le_two_pow (p : ℕ) (z : ℤ × ℤ) (h : inDisc p z) : z.1.natAbs ≤ 2^p := by
  have h3 : (4:ℤ)^p = (2^p)^2 := by
    rw [show (4:ℤ) = 2^2 by norm_num, ← pow_mul, mul_comm 2 p, pow_mul]
  have key : z.1 ^ 2 ≤ (2^p : ℤ)^2 := by
    calc z.1 ^ 2 ≤ z.1 ^ 2 + z.2 ^ 2 := by nlinarith [sq_nonneg z.2]
      _ ≤ 4 ^ p := h
      _ = (2^p)^2 := h3
  have := (Int.natAbs_le_iff_sq_le (a := z.1) (b := (2^p : ℤ))).2 key
  simpa using this

theorem isz_le_of_inDisc (p : ℕ) (z : ℤ × ℤ) (h : inDisc p z) : isz z.1 ≤ p + 3 := by
  have h1 : z.1.natAbs ≤ 2^p := natAbs_le_two_pow p z h
  have h2 : z.1.natAbs.size ≤ p + 1 := by
    have : z.1.natAbs.size ≤ (2^p).size := Nat.size_le_size h1
    rwa [Nat.size_pow] at this
  simp only [isz]; omega

theorem isz_le_of_inDisc' (p : ℕ) (z : ℤ × ℤ) (h : inDisc p z) : isz z.2 ≤ p + 3 :=
  isz_le_of_inDisc p (z.2, z.1) (by unfold inDisc at *; nlinarith [h])

theorem vsz_cfxVal_le (p : ℕ) (z : ℤ × ℤ) (h : inDisc p z) : vsz (cfxVal z) ≤ 2*p + 7 := by
  have h1 : isz z.1 ≤ p + 3 := isz_le_of_inDisc p z h
  have h2 : isz z.2 ≤ p + 3 := isz_le_of_inDisc' p z h
  rw [vsz_cfxVal']
  omega

theorem isz_neg' (a : ℤ) : isz (-a) = isz a := by simp [isz]

theorem isz_le_abs (e : ℤ) (r : ℕ) (h : |e| ≤ (r:ℤ)) : isz e ≤ r.size + 2 := by
  have h1 : (e.natAbs : ℤ) ≤ (r:ℤ) := by rw [← Int.abs_eq_natAbs]; exact h
  have h2 : e.natAbs ≤ r := by exact_mod_cast h1
  have h3 : e.natAbs.size ≤ r.size := Nat.size_le_size h2
  simp only [isz]; omega

theorem size_le_three (r : ℕ) : r.size + 2 ≤ 3 * (r + 1) := by
  have h : r.size ≤ r := (Nat.size_le).mpr Nat.lt_two_pow_self
  omega

theorem size_sq_le (r : ℕ) : (r.size + 3)^2 ≤ 18 * (r + 1) := by
  have key : ∀ k : ℕ, (k + 3)^2 ≤ 9 * 2^k := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih =>
      have hstep : (k + 1 + 3)^2 ≤ 2 * (k + 3)^2 := by
        have hid : 2*(k+3)^2 = (k+4)^2 + (k^2+4*k+2) := by ring
        rw [show k+1+3 = k+4 by omega, hid]; omega
      calc (k + 1 + 3)^2 ≤ 2 * (k + 3)^2 := hstep
        _ ≤ 2 * (9 * 2^k) := Nat.mul_le_mul_left 2 ih
        _ = 9 * 2^(k+1) := by rw [pow_succ]; ring
  rcases Nat.eq_zero_or_pos r with h | h
  · subst h; simp
  · have hpos : 1 ≤ r.size := Nat.size_pos.mpr h
    have hmin : 2^(r.size - 1) ≤ r := (Nat.lt_size (m := r.size - 1) (n := r)).mp (by omega)
    have hpow : (2:ℕ)^(r.size) = 2 * 2^(r.size - 1) := by
      conv_lhs => rw [show r.size = (r.size - 1) + 1 by omega]
      rw [pow_succ']
    calc (r.size + 3)^2 ≤ 9 * 2^(r.size) := key r.size
      _ = 9 * (2 * 2^(r.size - 1)) := by rw [hpow]
      _ ≤ 9 * (2 * (r + 1)) := Nat.mul_le_mul_left 9 (Nat.mul_le_mul_left 2 (by omega))
      _ = 18 * (r + 1) := by ring

theorem vsz_cvecVal_le (p r : ℕ) (w : List (ℤ × ℤ)) (hw : w.length = r)
    (h : ∀ z ∈ w, inDisc p z) : vsz (cvecVal w) ≤ 13 * (r + 1) * (p + 1) := by
  have h1 : vsz (cvecVal w) = w.length + (w.map fun z => vsz (cfxVal z)).sum + 1 := by
    rw [cvecVal, vsz_ofList, List.length_map, List.map_map]
    rfl
  have h2 : ∀ z ∈ w, vsz (cfxVal z) ≤ 2*p + 7 := fun z hz => vsz_cfxVal_le p z (h z hz)
  have h3 : (w.map fun z => vsz (cfxVal z)).sum ≤ w.length * (2*p+7) :=
    sum_le_of_forall _ w (2*p+7) h2
  rw [h1, hw] at *
  have : r * (2*p+7) + r + 1 ≤ 13 * (r+1) * (p+1) := by nlinarith
  omega

theorem inDisc_sign (p : ℕ) (z : ℤ × ℤ) (m : ℤ) (hm : m = 1 ∨ m = -1) (h : inDisc p z) :
    inDisc p (m * z.1, m * z.2) := by
  unfold inDisc at *
  rcases hm with rfl | rfl
  · simpa using h
  · simpa using h

theorem vsz_ofList_le_of_bound (xs : List Val) (B N : ℕ) (h : ∀ v ∈ xs, vsz v ≤ B)
    (hN : xs.length ≤ N) : vsz (ofList xs) ≤ N * (B + 1) + 1 := by
  rw [vsz_ofList]
  have hsum : (xs.map vsz).sum ≤ xs.length * B := sum_le_of_forall vsz xs B h
  nlinarith

theorem fmod_nonneg' (a b : ℤ) (hb : 0 < b) : 0 ≤ a.fmod b := by
  rw [Int.fmod_eq_emod, if_pos (Or.inl (le_of_lt hb))]
  simpa using Int.emod_nonneg a (ne_of_gt hb)

theorem fmod_lt' (a b : ℤ) (hb : 0 < b) : a.fmod b < b := by
  rw [Int.fmod_eq_emod, if_pos (Or.inl (le_of_lt hb))]
  simpa using Int.emod_lt_of_pos a hb

theorem fmod_self_max (r : ℕ) (e : ℤ) (he : |e| ≤ (r:ℤ)) :
    (-e).fmod (max (r:ℤ) 1) = (-e).fmod (r:ℤ) := by
  rcases Nat.eq_zero_or_pos r with h | h
  · subst h
    have he0 : e = 0 := by simpa using he
    rw [he0]
    norm_num [Int.fmod_eq_emod]
  · rw [max_eq_left (by omega : (1:ℤ) ≤ (r:ℤ))]

theorem isz_add_bound (r : ℕ) (e f : ℤ) (he : |e| ≤ (r:ℤ)) (hf0 : 0 ≤ f) (hfr : f ≤ (r:ℤ)) :
    isz (e + f) ≤ 4 * (r + 1) := by
  have habs : |e + f| ≤ 2 * (r:ℤ) := by
    have h1 : |f| ≤ (r:ℤ) := by rw [abs_of_nonneg hf0]; exact hfr
    linarith [abs_add_le e f, he, h1]
  have hnat : (e + f).natAbs ≤ 2 * r := by
    have h1 : ((e + f).natAbs : ℤ) ≤ ((2 * r : ℕ) : ℤ) := by
      rw [Int.abs_eq_natAbs] at habs
      exact_mod_cast habs
    exact_mod_cast h1
  have hsize : (e + f).natAbs.size ≤ r.size + 1 := by
    have h2 : (2 * r).size ≤ r.size + 1 := by
      rw [Nat.size_le, pow_succ]
      nlinarith [Nat.lt_size_self r]
    exact le_trans (Nat.size_le_size hnat) h2
  have h3 : r.size + 3 ≤ 4 * (r + 1) := by
    have h : r.size ≤ r := (Nat.size_le).mpr Nat.lt_two_pow_self
    omega
  simp only [isz]
  omega

/-! ## `WordR` plumbing -/

theorem WordR_weaken {main p : Cmd} {P P' : List Val → Prop} {Q Q' : List Val → List Val → Prop}
    {C C' : List Val → ℕ} (h : WordR main p P Q C) (hP : ∀ vs, P' vs → P vs)
    (hQ : ∀ vs out, P' vs → Q vs out → Q' vs out) (hC : ∀ vs, P' vs → C vs ≤ C' vs) :
    WordR main p P' Q' C' := by
  intro vs hvs s R hR
  obtain ⟨out, s', n, hQh, he, hn, hstk, hoth⟩ := h vs (hP vs hvs) s R hR
  exact ⟨out, s', n, hQ vs out hvs hQh, he, le_trans hn (hC vs hvs), hstk, hoth⟩

theorem WordR_conseqC {main p : Cmd} {Pre : List Val → Prop} {Post : List Val → List Val → Prop}
    {C : List Val → ℕ} {A B : List Val} {D : ℕ}
    (h : WordR main p Pre Post C) (hPre : Pre A) (hPost : ∀ out, Post A out → out = B)
    (hC : C A ≤ D) :
    WordR main p (fun vs => vs = A) (fun _ out => out = B) (fun _ => D) :=
  WordR_weaken h (fun vs hvs => by rw [hvs]; exact hPre)
    (fun vs out hvs hq => by rw [hvs] at hq; exact hPost out hq)
    (fun vs hvs => by rw [hvs]; exact hC)

theorem WordR_seqC {main p q : Cmd} {A B Cc : List Val} {c1 c2 : ℕ}
    (h1 : WordR main p (fun vs => vs = A) (fun _ out => out = B) (fun _ => c1))
    (h2 : WordR main q (fun vs => vs = B) (fun _ out => out = Cc) (fun _ => c2)) :
    WordR main (p ;;; q) (fun vs => vs = A) (fun _ out => out = Cc) (fun _ => c1 + c2) := by
  intro vs hvs s R hR
  rw [hvs] at hR
  obtain ⟨mid, s₂, n₁, hQ, he₁, hn₁, hstk₁, hoth₁⟩ := h1 A rfl s R hR
  rw [hQ] at hstk₁
  obtain ⟨out, s₃, n₂, hQ', he₂, hn₂, hstk₂, hoth₂⟩ := h2 B rfl s₂ R hstk₁
  exact ⟨out, s₃, n₁ + n₂, hQ', Eval.seq he₁ he₂, Nat.add_le_add hn₁ hn₂, hstk₂,
    fun k hk => by rw [hoth₂ k hk, hoth₁ k hk]⟩

/-! ## Concretisation of the individual library words -/

theorem pickStep {main : Cmd} {pickP : ℕ → Cmd} {Kp : ℕ}
    (h : ∀ k, WordR main (pickP k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs)
      (fun vs => Kp * (k+1) * (((vs.take (k+1)).map vsz).sum + 1)))
    (k : ℕ) (A : List Val) (hk' : k < A.length) (D : ℕ)
    (hD : Kp * (k+1) * (((A.take (k+1)).map vsz).sum + 1) ≤ D) :
    WordR main (pickP k) (fun vs => vs = A) (fun _ out => out = A.getD k .nil :: A) (fun _ => D) :=
  WordR_conseqC (h k) hk' (fun out hout => hout) hD

theorem rollStep {main : Cmd} {rollP : ℕ → Cmd} {Kr : ℕ}
    (h : ∀ k, WordR main (rollP k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs.eraseIdx k)
      (fun vs => Kr * (k+1) * (((vs.take (k+1)).map vsz).sum + 1)))
    (k : ℕ) (A : List Val) (hk' : k < A.length) (D : ℕ)
    (hD : Kr * (k+1) * (((A.take (k+1)).map vsz).sum + 1) ≤ D) :
    WordR main (rollP k) (fun vs => vs = A) (fun _ out => out = A.getD k .nil :: A.eraseIdx k)
      (fun _ => D) :=
  WordR_conseqC (h k) hk' (fun out hout => hout) hD

theorem swapStep {main : Cmd} {swapP : Cmd} {Ksw : ℕ}
    (h : WordR main swapP (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = b :: a :: rest)
      (fun vs => Ksw * (vsz (vs.getD 0 .nil) + vsz (vs.getD 1 .nil) + 1)))
    (A : List Val) (hA : 2 ≤ A.length) (D : ℕ)
    (hD : Ksw * (vsz (A.getD 0 .nil) + vsz (A.getD 1 .nil) + 1) ≤ D) :
    WordR main swapP (fun vs => vs = A)
      (fun _ out => out = A.getD 1 .nil :: A.getD 0 .nil :: A.drop 2) (fun _ => D) := by
  refine WordR_conseqC h hA ?_ hD
  intro out hout
  obtain ⟨a, b, r, hA', hout'⟩ := hout
  rw [hout', hA']
  simp

theorem kdropStep {main : Cmd} {kdrP : Cmd} {Kdr : ℕ}
    (h : WordR main kdrP (fun vs => vs ≠ [])
      (fun vs out => ∃ v rest, vs = v :: rest ∧ out = rest)
      (fun vs => Kdr * (vsz (vs.headD .nil) + 1)))
    (A : List Val) (hA : 1 ≤ A.length) (D : ℕ)
    (hD : Kdr * (vsz (A.headD .nil) + 1) ≤ D) :
    WordR main kdrP (fun vs => vs = A) (fun _ out => out = A.drop 1) (fun _ => D) := by
  have hne : A ≠ [] := by rintro rfl; simp at hA
  refine WordR_conseqC h hne ?_ hD
  intro out hout
  obtain ⟨v, r, hA', hout'⟩ := hout
  rw [hout', hA']
  simp

theorem dupStep {main : Cmd} {dupP : Cmd} {Kd : ℕ}
    (h : WordR main dupP (fun vs => vs ≠ [])
      (fun vs out => ∃ v rest, vs = v :: rest ∧ out = v :: v :: rest)
      (fun vs => Kd * (vsz (vs.headD .nil) + 1)))
    (v : Val) (t : List Val) (D : ℕ) (hD : Kd * (vsz v + 1) ≤ D) :
    WordR main dupP (fun vs => vs = v :: t) (fun _ out => out = v :: v :: t) (fun _ => D) := by
  refine WordR_conseqC h (by simp) ?_ (by simpa using hD)
  intro out hout
  obtain ⟨v', t', h1, h2⟩ := hout
  simp only [List.cons.injEq] at h1
  obtain ⟨rfl, rfl⟩ := h1
  exact h2

theorem negStep {main : Cmd} {negP : Cmd} {Kn : ℕ}
    (h : UnOp main negP (fun _ => True) (fun a => -a) (fun a => Kn * isz a))
    (a : ℤ) (t : List Val) (D : ℕ) (hD : Kn * isz a ≤ D) :
    WordR main negP (fun vs => vs = .int a :: t) (fun _ out => out = .int (-a) :: t)
      (fun _ => D) := by
  unfold UnOp at h
  refine WordR_conseqC h ⟨a, t, rfl, trivial⟩ ?_ hD
  intro out hout
  obtain ⟨a', t', h1, hout'⟩ := hout
  simp only [List.cons.injEq, Val.int.injEq] at h1
  obtain ⟨rfl, rfl⟩ := h1
  exact hout'

theorem addStep {main : Cmd} {addP : Cmd} {Ka : ℕ}
    (h : BinOp main addP (fun _ _ => True) (· + ·) (fun a b => Ka * (isz a + isz b)))
    (a b : ℤ) (t : List Val) (D : ℕ) (hD : Ka * (isz a + isz b) ≤ D) :
    WordR main addP (fun vs => vs = .int a :: .int b :: t) (fun _ out => out = .int (a + b) :: t)
      (fun _ => D) := by
  unfold BinOp at h
  refine WordR_conseqC h ⟨a, b, t, rfl, trivial⟩ ?_ hD
  intro out hout
  obtain ⟨a', b', t', h1, hout'⟩ := hout
  simp only [List.cons.injEq, Val.int.injEq] at h1
  obtain ⟨rfl, rfl, rfl⟩ := h1
  exact hout'

theorem maxStep {main : Cmd} {maxP : Cmd} {Km : ℕ}
    (h : BinOp main maxP (fun _ _ => True) max (fun a b => Km * (isz a + isz b)))
    (a b : ℤ) (t : List Val) (D : ℕ) (hD : Km * (isz a + isz b) ≤ D) :
    WordR main maxP (fun vs => vs = .int a :: .int b :: t) (fun _ out => out = .int (max a b) :: t)
      (fun _ => D) := by
  unfold BinOp at h
  refine WordR_conseqC h ⟨a, b, t, rfl, trivial⟩ ?_ hD
  intro out hout
  obtain ⟨a', b', t', h1, hout'⟩ := hout
  simp only [List.cons.injEq, Val.int.injEq] at h1
  obtain ⟨rfl, rfl, rfl⟩ := h1
  exact hout'

theorem mulStep {main : Cmd} {mulP : Cmd} {Km : ℕ}
    (h : BinOp main mulP (fun _ _ => True) (· * ·) (fun a b => Km * isz a * isz b))
    (a b : ℤ) (t : List Val) (D : ℕ) (hD : Km * isz a * isz b ≤ D) :
    WordR main mulP (fun vs => vs = .int a :: .int b :: t) (fun _ out => out = .int (a * b) :: t)
      (fun _ => D) := by
  unfold BinOp at h
  refine WordR_conseqC h ⟨a, b, t, rfl, trivial⟩ ?_ hD
  intro out hout
  obtain ⟨a', b', t', h1, hout'⟩ := hout
  simp only [List.cons.injEq, Val.int.injEq] at h1
  obtain ⟨rfl, rfl, rfl⟩ := h1
  exact hout'

theorem fmodStep {main : Cmd} {fmodP : Cmd} {Kf : ℕ}
    (h : BinOp main fmodP (fun _ b => 0 < b) Int.fmod (fun a b => Kf * isz a * isz b))
    (a b : ℤ) (t : List Val) (hb : 0 < b) (D : ℕ) (hD : Kf * isz a * isz b ≤ D) :
    WordR main fmodP (fun vs => vs = .int a :: .int b :: t) (fun _ out => out = .int (a.fmod b) :: t)
      (fun _ => D) := by
  unfold BinOp at h
  refine WordR_conseqC h ⟨a, b, t, rfl, hb⟩ ?_ hD
  intro out hout
  obtain ⟨a', b', t', h1, hout'⟩ := hout
  simp only [List.cons.injEq, Val.int.injEq] at h1
  obtain ⟨rfl, rfl, rfl⟩ := h1
  exact hout'

theorem consStep {main : Cmd} {consP : Cmd} {Kcv : ℕ}
    (h : WordR main consP (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = .cons a b :: rest) (fun _ => Kcv))
    (a b : Val) (t : List Val) (D : ℕ) (hD : Kcv ≤ D) :
    WordR main consP (fun vs => vs = a :: b :: t) (fun _ out => out = .cons a b :: t)
      (fun _ => D) := by
  refine WordR_conseqC h (by simp) ?_ (by simpa using hD)
  intro out hout
  obtain ⟨a', b', t', h1, hout'⟩ := hout
  simp only [List.cons.injEq, Val.cons.injEq] at h1
  obtain ⟨rfl, rfl, rfl⟩ := h1
  exact hout'

theorem uncStep {main : Cmd} {uncP : Cmd} {Kuc : ℕ}
    (h : WordR main uncP (fun vs => ∃ a b rest, vs = .cons a b :: rest)
      (fun vs out => ∃ a b rest, vs = .cons a b :: rest ∧ out = a :: b :: rest) (fun _ => Kuc))
    (a b : Val) (t : List Val) (D : ℕ) (hD : Kuc ≤ D) :
    WordR main uncP (fun vs => vs = .cons a b :: t) (fun _ out => out = a :: b :: t)
      (fun _ => D) := by
  refine WordR_conseqC h ⟨a, b, t, rfl⟩ ?_ (by simpa using hD)
  intro out hout
  obtain ⟨a', b', t', h1, hout'⟩ := hout
  simp only [List.cons.injEq, Val.cons.injEq] at h1
  rcases h1 with ⟨⟨rfl, rfl⟩, rfl⟩
  exact hout'

theorem pushStep {main : Cmd} {pushP : Val → Cmd} {Kpv : ℕ}
    (h : ∀ v, WordR main (pushP v) (fun _ => True) (fun vs out => out = v :: vs)
      (fun _ => Kpv * (vsz v + 1)))
    (v : Val) (A : List Val) (D : ℕ) (hD : Kpv * (vsz v + 1) ≤ D) :
    WordR main (pushP v) (fun vs => vs = A) (fun _ out => out = v :: A) (fun _ => D) :=
  WordR_conseqC (h v) trivial (fun out hout => hout) hD

theorem layDropStep {main : Cmd} {ldrP : Cmd} {Kld : ℕ}
    (h : ∀ (k : ℕ) (xs : List Val), WordR main ldrP
      (fun vs => ∃ rest, vs = .int k :: ofList xs :: rest)
      (fun vs out => ∃ rest, vs = .int k :: ofList xs :: rest ∧ out = ofList (xs.drop k) :: rest)
      (fun _ => Kld * (vsz (ofList xs) + isz k + 1)))
    (k : ℕ) (kv : ℤ) (hkv : kv = (k : ℤ)) (xs : List Val) (t : List Val) (D : ℕ)
    (hD : Kld * (vsz (ofList xs) + isz k + 1) ≤ D) :
    WordR main ldrP (fun vs => vs = .int kv :: ofList xs :: t)
      (fun _ out => out = ofList (xs.drop k) :: t) (fun _ => D) := by
  refine WordR_conseqC (h k xs) ?_ ?_ hD
  · exact ⟨t, by rw [hkv]⟩
  · intro out hout
    obtain ⟨r, hr1, hr2⟩ := hout
    simp only [List.cons.injEq] at hr1
    obtain ⟨-, -, rfl⟩ := hr1
    exact hr2

theorem layTakeStep {main : Cmd} {ltkP : Cmd} {Kt : ℕ}
    (h : ∀ (k : ℕ) (xs : List Val), WordR main ltkP
      (fun vs => ∃ rest, vs = .int k :: ofList xs :: rest)
      (fun vs out => ∃ rest, vs = .int k :: ofList xs :: rest ∧ out = ofList (xs.take k) :: rest)
      (fun _ => Kt * (vsz (ofList xs) + isz k + 1)))
    (k : ℕ) (kv : ℤ) (hkv : kv = (k : ℤ)) (xs : List Val) (t : List Val) (D : ℕ)
    (hD : Kt * (vsz (ofList xs) + isz k + 1) ≤ D) :
    WordR main ltkP (fun vs => vs = .int kv :: ofList xs :: t)
      (fun _ out => out = ofList (xs.take k) :: t) (fun _ => D) := by
  refine WordR_conseqC (h k xs) ?_ ?_ hD
  · exact ⟨t, by rw [hkv]⟩
  · intro out hout
    obtain ⟨r, hr1, hr2⟩ := hout
    simp only [List.cons.injEq] at hr1
    obtain ⟨-, -, rfl⟩ := hr1
    exact hr2

theorem appStep {main : Cmd} {appP : Cmd} {Kap : ℕ}
    (h : ∀ (xs ys : List Val), WordR main appP
      (fun vs => ∃ rest, vs = ofList xs :: ofList ys :: rest)
      (fun vs out => ∃ rest, vs = ofList xs :: ofList ys :: rest ∧ out = ofList (xs ++ ys) :: rest)
      (fun _ => Kap * (vsz (ofList xs) + 1)))
    (xs ys : List Val) (t : List Val) (D : ℕ) (hD : Kap * (vsz (ofList xs) + 1) ≤ D) :
    WordR main appP (fun vs => vs = ofList xs :: ofList ys :: t)
      (fun _ out => out = ofList (xs ++ ys) :: t) (fun _ => D) := by
  refine WordR_conseqC (h xs ys) ⟨t, rfl⟩ ?_ hD
  intro out hout
  obtain ⟨r, hr1, hr2⟩ := hout
  simp only [List.cons.injEq] at hr1
  obtain ⟨-, -, rfl⟩ := hr1
  exact hr2

theorem signStep {main : Cmd} {izC : Cmd → Cmd → Cmd} {pushP : Val → Cmd} {Kiz Kpv : ℕ}
    (hiz : ∀ (q₁ q₂ : Cmd) (z : ℤ) (rest : List Val) (Q₁ Q₂ : List Val → Prop) (c₁ c₂ : ℕ),
      (z = 0 → WordR main q₁ (fun vs => vs = rest) (fun _ out => Q₁ out) (fun _ => c₁)) →
      (z ≠ 0 → WordR main q₂ (fun vs => vs = rest) (fun _ out => Q₂ out) (fun _ => c₂)) →
      WordR main (izC q₁ q₂) (fun vs => vs = .int z :: rest)
        (fun _ out => (z = 0 → Q₁ out) ∧ (z ≠ 0 → Q₂ out))
        (fun _ => Kiz * (isz z + 1) + max c₁ c₂))
    (hpush : ∀ v, WordR main (pushP v) (fun _ => True) (fun vs out => out = v :: vs)
      (fun _ => Kpv * (vsz v + 1)))
    (z : ℤ) (t : List Val) (D : ℕ)
    (hD : Kiz * (isz z + 1) + max (Kpv * (vsz (.int 1) + 1)) (Kpv * (vsz (.int (-1)) + 1)) ≤ D) :
    WordR main (izC (pushP (.int 1)) (pushP (.int (-1))))
      (fun vs => vs = .int z :: t) (fun _ out => out = .int (if z = 0 then 1 else -1) :: t)
      (fun _ => D) := by
  refine WordR_conseqC (hiz (pushP (.int 1)) (pushP (.int (-1))) z t
    (fun out => out = .int (if z = 0 then (1:ℤ) else -1) :: t)
    (fun out => out = .int (if z = 0 then (1:ℤ) else -1) :: t)
    (Kpv * (vsz (.int 1) + 1)) (Kpv * (vsz (.int (-1)) + 1)) ?_ ?_) rfl ?_ hD
  · intro hz0
    refine WordR_conseqC (hpush (.int 1)) trivial ?_ le_rfl
    intro out hout
    rw [hout, hz0]; simp
  · intro hz0
    refine WordR_conseqC (hpush (.int (-1))) trivial ?_ le_rfl
    intro out hout
    rw [hout]
    rw [if_neg hz0]
  · intro out hout
    by_cases hz : z = 0
    · exact hout.1 hz
    · exact hout.2 hz

theorem mapStep {main : Cmd} {mapP : Cmd → Cmd} {Kml : ℕ}
    (h : ∀ (q : Cmd) (rest : List Val) (P : Val → Prop) (Q : Val → Val → Prop) (c L : ℕ),
      (∀ x, P x → WordR main q (fun vs => vs = x :: rest)
        (fun _ out => ∃ y, out = y :: rest ∧ Q x y ∧ vsz y ≤ L) (fun _ => c)) →
      ∀ xs : List Val, (∀ x ∈ xs, P x ∧ vsz x ≤ L) →
      WordR main (mapP q) (fun vs => vs = ofList xs :: rest)
        (fun _ out => ∃ ys, out = ofList ys :: rest ∧ List.Forall₂ Q xs ys)
        (fun _ => xs.length * (c + Kml * (L + 1)) + Kml))
    (q : Cmd) (rest : List Val) (P : Val → Prop) (Q : Val → Val → Prop) (c L : ℕ)
    (hq : ∀ x, P x → WordR main q (fun vs => vs = x :: rest)
        (fun _ out => ∃ y, out = y :: rest ∧ Q x y ∧ vsz y ≤ L) (fun _ => c))
    (xs : List Val) (hxs : ∀ x ∈ xs, P x ∧ vsz x ≤ L) (B : Val)
    (hB : ∀ ys, List.Forall₂ Q xs ys → B = ofList ys)
    (D : ℕ) (hD : xs.length * (c + Kml * (L + 1)) + Kml ≤ D) :
    WordR main (mapP q) (fun vs => vs = ofList xs :: rest) (fun _ out => out = B :: rest)
      (fun _ => D) := by
  have hspec := h q rest P Q c L hq xs hxs
  refine WordR_weaken hspec (fun vs hvs => hvs) ?_ (fun vs _ => hD)
  intro vs out hvs hQ
  obtain ⟨ys, hout, hF⟩ := hQ
  rw [hout, hB ys hF]

theorem vsz_take_sum_le_getD (A : List Val) (j B : ℕ)
    (h : ∀ i, i < j → vsz (A.getD i .nil) ≤ B) : ((A.take j).map vsz).sum ≤ j * B := by
  induction A generalizing j with
  | nil => cases j <;> simp
  | cons a A ih =>
    cases j with
    | zero => simp
    | succ j =>
      rw [List.take_succ_cons, List.map_cons, List.sum_cons]
      have h1 : vsz a ≤ B := by
        have := h 0 (by omega)
        simpa using this
      have h2 : ((A.take j).map vsz).sum ≤ j * B := by
        refine ih j (fun i hi => ?_)
        have := h (i+1) (by omega)
        simpa using this
      nlinarith

end Work.SynFFT.MrgKit
