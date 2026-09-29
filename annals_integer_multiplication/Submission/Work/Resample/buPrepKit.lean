import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Resample.buKit
import Submission.Work.Resample.auPiWord
import Submission.Work.Resample.buEntrySizes
import Submission.Work.Resample.buPrepSmall
import Submission.Work.Resample.buAllCosts
import Submission.Work.Resample.buWdSize
import Submission.Work.Resample.buPiFromP
import Submission.Work.Resample.buNFromParams
import Submission.Work.Resample.buMFromParams
import Submission.Work.Resample.buSignElem
import Submission.Work.Resample.buSignsWord
import Submission.Work.Resample.buWtElem
import Submission.Work.Resample.buWdElem
import Submission.Work.Resample.buHornerWord
import Submission.Work.Resample.buDwWord
import Submission.Work.Resample.buKeyElem
import Submission.Work.Resample.buKeysWordB

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Work.Resample
open HvdH

open Work.Fx

/-- A `WordR` with existential suffix pre/post is a `Pipe`. -/
theorem buPipeToWordR {main prog : Cmd} {A B : List Val} {c : ℕ} (h : Pipe main prog A B c) :
    WordR main prog (fun vs => ∃ rest, vs = A ++ rest)
      (fun vs out => ∃ rest, vs = A ++ rest ∧ out = B ++ rest) (fun _ => c) := by
  intro vs ⟨rest, hvs⟩ s R hR
  obtain ⟨out, s', n, hout, hev, hn, hstk, hoth⟩ := h rest vs hvs s R hR
  exact ⟨out, s', n, ⟨rest, hvs, hout⟩, hev, hn, hstk, hoth⟩

theorem buPipeOfExists {main prog : Cmd} {A B : List Val} {c : ℕ}
    (h : WordR main prog (fun vs => ∃ rest, vs = A ++ rest)
      (fun vs out => ∃ rest, vs = A ++ rest ∧ out = B ++ rest) (fun _ => c)) :
    Pipe main prog A B c := by
  intro rest vs hvs s R hR
  obtain ⟨out, s', n, ⟨r, hvs', hout⟩, hev, hn, hstk, hoth⟩ := h vs ⟨rest, hvs⟩ s R hR
  have hA : A ++ r = A ++ rest := hvs'.symm.trans hvs
  have hr : r = rest := List.append_cancel_left hA
  exact ⟨out, s', n, by rw [hout, hr], hev, hn, hstk, hoth⟩

/-- `n` successive rolls of index `k`. -/
def buRollN (prog : ℕ → Cmd) (k : ℕ) : ℕ → Cmd
  | 0 => .skip
  | 1 => prog k
  | (n + 2) => .seq (buRollN prog k (n + 1)) (prog k)

/-- One roll of index `4` on a five-value window, moving the last to the front. -/
theorem buRoll4 (main : Cmd) {prog : ℕ → Cmd} {K M : ℕ}
    (h : ∀ (m : Cmd) (j : ℕ), WordR m (prog j) (fun vs => j < vs.length)
      (fun vs out => out = vs.getD j .nil :: vs.eraseIdx j)
      (fun vs => K * (j + 1) * (((vs.take (j + 1)).map vsz).sum + 1)))
    (p q r s t : Val) (hp : vsz p ≤ M) (hq : vsz q ≤ M) (hr : vsz r ≤ M) (hs : vsz s ≤ M)
    (ht : vsz t ≤ M) :
    Pipe main (prog 4) [p, q, r, s, t] [t, p, q, r, s] (K * 5 * (5 * M + 1)) := by
  have h1 := Pipe.roll main h (A := [p, q, r, s, t]) (k := 4) (by simp)
  refine Pipe.le (by simpa using h1) ?_
  simp only [szl, List.take_cons, List.take_nil, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil]
  nlinarith

/-- One roll of index `6` on a seven-value window. -/
theorem buRoll6 (main : Cmd) {prog : ℕ → Cmd} {K M : ℕ}
    (h : ∀ (m : Cmd) (j : ℕ), WordR m (prog j) (fun vs => j < vs.length)
      (fun vs out => out = vs.getD j .nil :: vs.eraseIdx j)
      (fun vs => K * (j + 1) * (((vs.take (j + 1)).map vsz).sum + 1)))
    (p q r s t u v : Val) (hp : vsz p ≤ M) (hq : vsz q ≤ M) (hr : vsz r ≤ M) (hs : vsz s ≤ M)
    (ht : vsz t ≤ M) (hu : vsz u ≤ M) (hv : vsz v ≤ M) :
    Pipe main (prog 6) [p, q, r, s, t, u, v] [v, p, q, r, s, t, u] (K * 7 * (7 * M + 1)) := by
  have h1 := Pipe.roll main h (A := [p, q, r, s, t, u, v]) (k := 6) (by simp)
  refine Pipe.le (by simpa using h1) ?_
  simp only [szl, List.take_cons, List.take_nil, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil]
  nlinarith

/-- One roll of index `7` on an eight-value window. -/
theorem buRoll7 (main : Cmd) {prog : ℕ → Cmd} {K M : ℕ}
    (h : ∀ (m : Cmd) (j : ℕ), WordR m (prog j) (fun vs => j < vs.length)
      (fun vs out => out = vs.getD j .nil :: vs.eraseIdx j)
      (fun vs => K * (j + 1) * (((vs.take (j + 1)).map vsz).sum + 1)))
    (p q r s t u v w : Val) (hp : vsz p ≤ M) (hq : vsz q ≤ M) (hr : vsz r ≤ M) (hs : vsz s ≤ M)
    (ht : vsz t ≤ M) (hu : vsz u ≤ M) (hv : vsz v ≤ M) (hw : vsz w ≤ M) :
    Pipe main (prog 7) [p, q, r, s, t, u, v, w] [w, p, q, r, s, t, u, v] (K * 8 * (8 * M + 1)) := by
  have h1 := Pipe.roll main h (A := [p, q, r, s, t, u, v, w]) (k := 7) (by simp)
  refine Pipe.le (by simpa using h1) ?_
  simp only [szl, List.take_cons, List.take_nil, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil]
  nlinarith

/-- Four rolls of index `4`: `[x,a,b,c,d] ↦ [a,b,c,d,x]` (insert below a four-block). -/
theorem buInsert4 (main : Cmd) {prog : ℕ → Cmd} {K M : ℕ}
    (h : ∀ (m : Cmd) (j : ℕ), WordR m (prog j) (fun vs => j < vs.length)
      (fun vs out => out = vs.getD j .nil :: vs.eraseIdx j)
      (fun vs => K * (j + 1) * (((vs.take (j + 1)).map vsz).sum + 1)))
    (x a b c d : Val) (hx : vsz x ≤ M) (ha : vsz a ≤ M) (hb : vsz b ≤ M) (hc : vsz c ≤ M)
    (hd : vsz d ≤ M) :
    Pipe main (buRollN prog 4 4) [x, a, b, c, d] [a, b, c, d, x] (4 * (K * 5 * (5 * M + 1))) := by
  have c1 := buRoll4 main h x a b c d hx ha hb hc hd
  have c2 := buRoll4 main h d x a b c hd hx ha hb hc
  have c3 := buRoll4 main h c d x a b hc hd hx ha hb
  have c4 := buRoll4 main h b c d x a hb hc hd hx ha
  have m1 := Pipe.comp c1 c2
  have m2 := Pipe.comp m1 c3
  have m3 := Pipe.comp m2 c4
  exact Pipe.le (by simpa [buRollN] using m3) (le_of_eq (by ring))

/-- Six rolls of index `6`: `[x,a,b,c,d,e,f] ↦ [a,b,c,d,e,f,x]` (insert below a six-block). -/
theorem buInsert6 (main : Cmd) {prog : ℕ → Cmd} {K M : ℕ}
    (h : ∀ (m : Cmd) (j : ℕ), WordR m (prog j) (fun vs => j < vs.length)
      (fun vs out => out = vs.getD j .nil :: vs.eraseIdx j)
      (fun vs => K * (j + 1) * (((vs.take (j + 1)).map vsz).sum + 1)))
    (x a b c d e f : Val) (hx : vsz x ≤ M) (ha : vsz a ≤ M) (hb : vsz b ≤ M) (hc : vsz c ≤ M)
    (hd : vsz d ≤ M) (he : vsz e ≤ M) (hf : vsz f ≤ M) :
    Pipe main (buRollN prog 6 6) [x, a, b, c, d, e, f] [a, b, c, d, e, f, x]
      (6 * (K * 7 * (7 * M + 1))) := by
  have c1 := buRoll6 main h x a b c d e f hx ha hb hc hd he hf
  have c2 := buRoll6 main h f x a b c d e hf hx ha hb hc hd he
  have c3 := buRoll6 main h e f x a b c d he hf hx ha hb hc hd
  have c4 := buRoll6 main h d e f x a b c hd he hf hx ha hb hc
  have c5 := buRoll6 main h c d e f x a b hc hd he hf hx ha hb
  have c6 := buRoll6 main h b c d e f x a hb hc hd he hf hx ha
  have m1 := Pipe.comp c1 c2
  have m2 := Pipe.comp m1 c3
  have m3 := Pipe.comp m2 c4
  have m4 := Pipe.comp m3 c5
  have m5 := Pipe.comp m4 c6
  exact Pipe.le (by simpa [buRollN] using m5) (le_of_eq (by ring))

/-- Seven rolls of index `7`: `[x,a,…,g] ↦ [a,…,g,x]` (insert below the seven-value block). -/
theorem buInsert7 (main : Cmd) {prog : ℕ → Cmd} {K M : ℕ}
    (h : ∀ (m : Cmd) (j : ℕ), WordR m (prog j) (fun vs => j < vs.length)
      (fun vs out => out = vs.getD j .nil :: vs.eraseIdx j)
      (fun vs => K * (j + 1) * (((vs.take (j + 1)).map vsz).sum + 1)))
    (x a b c d e f g : Val) (hx : vsz x ≤ M) (ha : vsz a ≤ M) (hb : vsz b ≤ M) (hc : vsz c ≤ M)
    (hd : vsz d ≤ M) (he : vsz e ≤ M) (hf : vsz f ≤ M) (hg : vsz g ≤ M) :
    Pipe main (buRollN prog 7 7) [x, a, b, c, d, e, f, g] [a, b, c, d, e, f, g, x]
      (7 * (K * 8 * (8 * M + 1))) := by
  have c1 := buRoll7 main h x a b c d e f g hx ha hb hc hd he hf hg
  have c2 := buRoll7 main h g x a b c d e f hg hx ha hb hc hd he hf
  have c3 := buRoll7 main h f g x a b c d e hf hg hx ha hb hc hd he
  have c4 := buRoll7 main h e f g x a b c d he hf hg hx ha hb hc hd
  have c5 := buRoll7 main h d e f g x a b c hd he hf hg hx ha hb hc
  have c6 := buRoll7 main h c d e f g x a b hc hd he hf hg hx ha hb
  have c7 := buRoll7 main h b c d e f g x a hb hc hd he hf hg hx ha
  have m1 := Pipe.comp c1 c2
  have m2 := Pipe.comp m1 c3
  have m3 := Pipe.comp m2 c4
  have m4 := Pipe.comp m3 c5
  have m5 := Pipe.comp m4 c6
  have m6 := Pipe.comp m5 c7
  exact Pipe.le (by simpa [buRollN] using m6) (le_of_eq (by ring))

/-- Roll index `6` then drop: remove the seventh value of the window. -/
theorem buDropSeventh (main : Cmd) {prog : ℕ → Cmd} {progD : Cmd} {K Kd M : ℕ}
    (h : ∀ (m : Cmd) (j : ℕ), WordR m (prog j) (fun vs => j < vs.length)
      (fun vs out => out = vs.getD j .nil :: vs.eraseIdx j)
      (fun vs => K * (j + 1) * (((vs.take (j + 1)).map vsz).sum + 1)))
    (hD : ∀ m : Cmd, WordR m progD (fun vs => vs ≠ [])
      (fun vs out => ∃ v r, vs = v :: r ∧ out = r)
      (fun vs => Kd * (vsz (vs.headD .nil) + 1)))
    (a b c d e f g : Val) (ha : vsz a ≤ M) (hb : vsz b ≤ M) (hc : vsz c ≤ M) (hd : vsz d ≤ M)
    (he : vsz e ≤ M) (hf : vsz f ≤ M) (hg : vsz g ≤ M) :
    Pipe main (.seq (prog 6) progD) [a, b, c, d, e, f, g] [a, b, c, d, e, f]
      (K * 7 * (7 * M + 1) + Kd * (M + 1)) := by
  have c1 := buRoll6 main h a b c d e f g ha hb hc hd he hf hg
  have h2 := Pipe.appendTail [a, b, c, d, e, f] (Pipe.drop main hD g)
  refine Pipe.le (Pipe.comp c1 h2) ?_
  nlinarith [hg]

/-! ### The roll steps with an explicit tail (cheap to apply) -/

/-- Four rolls below a four-block, with the tail appended on both sides. -/
theorem buInsert4T (main : Cmd) {prog : ℕ → Cmd} {K M : ℕ}
    (h : ∀ (m : Cmd) (j : ℕ), WordR m (prog j) (fun vs => j < vs.length)
      (fun vs out => out = vs.getD j .nil :: vs.eraseIdx j)
      (fun vs => K * (j + 1) * (((vs.take (j + 1)).map vsz).sum + 1)))
    (x a b c d : Val) (T : List Val) (hx : vsz x ≤ M) (ha : vsz a ≤ M) (hb : vsz b ≤ M)
    (hc : vsz c ≤ M) (hd : vsz d ≤ M) :
    Pipe main (buRollN prog 4 4) ([x, a, b, c, d] ++ T) ([a, b, c, d, x] ++ T)
      (4 * (K * 5 * (5 * M + 1))) :=
  Pipe.appendTail T (buInsert4 main h x a b c d hx ha hb hc hd)

/-- Six rolls below a six-block, with the tail appended on both sides. -/
theorem buInsert6T (main : Cmd) {prog : ℕ → Cmd} {K M : ℕ}
    (h : ∀ (m : Cmd) (j : ℕ), WordR m (prog j) (fun vs => j < vs.length)
      (fun vs out => out = vs.getD j .nil :: vs.eraseIdx j)
      (fun vs => K * (j + 1) * (((vs.take (j + 1)).map vsz).sum + 1)))
    (x a b c d e f : Val) (T : List Val) (hx : vsz x ≤ M) (ha : vsz a ≤ M) (hb : vsz b ≤ M)
    (hc : vsz c ≤ M) (hd : vsz d ≤ M) (he : vsz e ≤ M) (hf : vsz f ≤ M) :
    Pipe main (buRollN prog 6 6) ([x, a, b, c, d, e, f] ++ T) ([a, b, c, d, e, f, x] ++ T)
      (6 * (K * 7 * (7 * M + 1))) :=
  Pipe.appendTail T (buInsert6 main h x a b c d e f hx ha hb hc hd he hf)

/-- Seven rolls below a seven-block, with the tail appended on both sides. -/
theorem buInsert7T (main : Cmd) {prog : ℕ → Cmd} {K M : ℕ}
    (h : ∀ (m : Cmd) (j : ℕ), WordR m (prog j) (fun vs => j < vs.length)
      (fun vs out => out = vs.getD j .nil :: vs.eraseIdx j)
      (fun vs => K * (j + 1) * (((vs.take (j + 1)).map vsz).sum + 1)))
    (x a b c d e f g : Val) (T : List Val) (hx : vsz x ≤ M) (ha : vsz a ≤ M) (hb : vsz b ≤ M)
    (hc : vsz c ≤ M) (hd : vsz d ≤ M) (he : vsz e ≤ M) (hf : vsz f ≤ M) (hg : vsz g ≤ M) :
    Pipe main (buRollN prog 7 7) ([x, a, b, c, d, e, f, g] ++ T) ([a, b, c, d, e, f, g, x] ++ T)
      (7 * (K * 8 * (8 * M + 1))) :=
  Pipe.appendTail T (buInsert7 main h x a b c d e f g hx ha hb hc hd he hf hg)

/-- Roll index `6` then drop, with the tail appended on both sides. -/
theorem buRoll6DropT (main : Cmd) {prog : ℕ → Cmd} {progD : Cmd} {K Kd M : ℕ}
    (h : ∀ (m : Cmd) (j : ℕ), WordR m (prog j) (fun vs => j < vs.length)
      (fun vs out => out = vs.getD j .nil :: vs.eraseIdx j)
      (fun vs => K * (j + 1) * (((vs.take (j + 1)).map vsz).sum + 1)))
    (hD : ∀ m : Cmd, WordR m progD (fun vs => vs ≠ [])
      (fun vs out => ∃ v r, vs = v :: r ∧ out = r)
      (fun vs => Kd * (vsz (vs.headD .nil) + 1)))
    (a b c d e f g : Val) (T : List Val) (ha : vsz a ≤ M) (hb : vsz b ≤ M) (hc : vsz c ≤ M)
    (hd : vsz d ≤ M) (he : vsz e ≤ M) (hf : vsz f ≤ M) (hg : vsz g ≤ M) :
    Pipe main (.seq (prog 6) progD) ([a, b, c, d, e, f, g] ++ T) ([a, b, c, d, e, f] ++ T)
      (K * 7 * (7 * M + 1) + Kd * (M + 1)) :=
  Pipe.appendTail T (buDropSeventh main h hD a b c d e f g ha hb hc hd he hf hg)


/-- The right-nested sum of eighteen copies of `X`. -/
theorem buSum18 {X Y : ℕ} (h : 18 * X ≤ Y) : X + (X + (X + (X + (X + (X + (X + (X + (X + (X + (X + (X + (X + (X + (X + (X + (X + X)))))))))))))))) ≤ Y := by
  have h2 : X + (X + (X + (X + (X + (X + (X + (X + (X + (X + (X + (X + (X + (X + (X + (X + (X + X)))))))))))))))) = 18 * X := by ring
  rw [h2]
  exact h

open Work.Fx



/-! ### Elementary bounds for the cost accounting -/

theorem le_pow_K {p K : ℕ} (hp : 2 ≤ p) : K ≤ (p + 1) ^ (2 * K) := by
  have h1 : K ≤ 2 ^ K := le_of_lt (Nat.lt_two_pow_self)
  have h2 : (2 : ℕ) ^ K ≤ (p + 1) ^ K := Nat.pow_le_pow_left (by omega : 2 ≤ p + 1) K
  calc K ≤ 2 ^ K := h1
    _ ≤ (p + 1) ^ K := h2
    _ ≤ (p + 1) ^ (2 * K) := Nat.pow_le_pow_right (by omega) (by omega)

theorem bk_mul_pow_le_pow {p K E : ℕ} (hp : 2 ≤ p) (h : 2 * K ≤ E) :
    K * (p + 1) ^ K ≤ (p + 1) ^ E := by
  have h1 : K ≤ (p + 1) ^ K := le_trans (le_of_lt (Nat.lt_two_pow_self))
    (Nat.pow_le_pow_left (by omega) K)
  calc K * (p + 1) ^ K ≤ (p + 1) ^ K * (p + 1) ^ K := Nat.mul_le_mul_right _ h1
    _ = (p + 1) ^ (2 * K) := by rw [← pow_add]; ring_nf
    _ ≤ (p + 1) ^ E := Nat.pow_le_pow_right (by omega) h

theorem mul_pow_le_pow3 {p K E : ℕ} (hp : 2 ≤ p) (h : 3 * K ≤ E) :
    K * (p + 1) ^ K ≤ (p + 1) ^ E := by
  have h1 : K ≤ (p + 1) ^ (2 * K) := le_pow_K hp
  calc K * (p + 1) ^ K ≤ (p + 1) ^ (2 * K) * (p + 1) ^ K := Nat.mul_le_mul_right _ h1
    _ = (p + 1) ^ (3 * K) := by rw [← pow_add]; ring_nf
    _ ≤ (p + 1) ^ E := Nat.pow_le_pow_right (by omega) h

theorem pow_le_tmul (p t E : ℕ) : (p + 1) ^ E ≤ (t + 1) * (p + 1) ^ E := by
  have h := Nat.mul_le_mul_right ((p + 1) ^ E) (show 1 ≤ t + 1 by omega)
  simpa [Nat.one_mul, Nat.mul_comm] using h

theorem small_le_pow {p : ℕ} (hp : 100 ≤ p) {c : ℕ} (hc : c ≤ 100) : c ≤ (p + 1) ^ 7 := by
  calc c ≤ 100 := hc
    _ ≤ 2 ^ 7 := by norm_num
    _ ≤ (p + 1) ^ 7 := Nat.pow_le_pow_left (by omega) 7

theorem bk_buSZ_add_one_le (p : ℕ) (hp : 100 ≤ p) : buSZ p + 1 ≤ (p + 1) ^ 4 := by
  have h1 : buSZ p + 1 ≤ 100 * p ^ 3 := by
    simp only [buSZ]
    nlinarith [hp]
  have h2 : 100 * p ^ 3 ≤ (p + 1) ^ 3 * (p + 1) := by
    have h3 : p ^ 3 ≤ (p + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    calc 100 * p ^ 3 ≤ (p + 1) * (p + 1) ^ 3 := Nat.mul_le_mul (by omega) h3
      _ = (p + 1) ^ 3 * (p + 1) := by ring
  calc buSZ p + 1 ≤ 100 * p ^ 3 := h1
    _ ≤ (p + 1) ^ 3 * (p + 1) := h2
    _ = (p + 1) ^ 4 := by ring

theorem bk_egM_add_one_le (p α : ℕ) (hp : 1 ≤ p) : egM p α + 1 ≤ (p + 1) ^ 5 := by
  have h1 : egM p α + 1 ≤ 2 * (p + 1) := by
    have := egM_le p α
    omega
  calc egM p α + 1 ≤ 2 * (p + 1) := h1
    _ ≤ (p + 1) * (p + 1) := by
        have : (2 : ℕ) ≤ p + 1 := by omega
        exact Nat.mul_le_mul_right _ this
    _ = (p + 1) ^ 2 := by ring
    _ ≤ (p + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)

/-! ### Size estimates for the block and the five entries -/

/-- `vsz` of a cons-list of values. -/
theorem bk_vsz_ofList_val (l : List Val) : vsz (ofList l) = l.length + 1 + (l.map vsz).sum := by
  induction l with
  | nil => simp [ofList, vsz, Val.enc]
  | cons v vs ih =>
    rw [show ofList (v :: vs) = Val.cons v (ofList vs) from rfl, vsz_cons, ih]
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    ring

/-- `vsz` of the integer list value `zl l`. -/
theorem bk_vsz_zl (l : List ℤ) : vsz (zl l) = l.length + 1 + (l.map isz).sum := by
  rw [zl, bk_vsz_ofList_val, List.length_map, List.map_map]
  have h : (l.map (vsz ∘ Val.int)) = (l.map isz) := by
    apply List.map_congr_left
    intro z _
    exact vsz_int z
  rw [h]

/-- `(-1)^{j+1}` has three glyphs. -/
theorem bk_isz_neg_one_pow (j : ℕ) : isz ((-1 : ℤ) ^ (j + 1)) = 3 := by
  have h : (((-1 : ℤ) ^ (j + 1)).natAbs) = 1 := by
    rw [Int.natAbs_pow]
    have h2 : ((-1 : ℤ)).natAbs = 1 := by norm_num
    rw [h2, one_pow]
  simp only [isz, h]
  norm_num

/-- The sum of `isz` over the sign list. -/
theorem bk_sum_isz_neg_one_pow (n : ℕ) :
    ((List.range n).map (isz ∘ fun j => (-1 : ℤ) ^ (j + 1))).sum = 3 * n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Function.comp_apply,
      bk_isz_neg_one_pow]
    ring

theorem isz_nat_le_pow {p A n : ℕ} (hA : A + 3 ≤ buSZ p) (h : n ≤ 2 ^ A) : isz ((n : ℤ)) ≤ buSZ p := by
  refine isz_le_buSZ_of (p := p) (A := A) hA ?_
  rw [Int.natAbs_natCast]
  exact h

theorem isz_buSZ_p (p : ℕ) : isz ((p : ℤ)) ≤ buSZ p :=
  isz_nat_le_pow (p := p) (A := p) (n := p) (by simp only [buSZ]; omega)
    (le_of_lt (Nat.lt_two_pow_self))

theorem isz_buSZ_alpha (p α : ℕ) (hαp : α ^ 2 < p) : isz ((α : ℤ)) ≤ buSZ p := by
  have h : α ≤ p := by nlinarith
  exact isz_nat_le_pow (p := p) (A := p) (n := α) (by simp only [buSZ]; omega)
    (le_trans h (le_of_lt (Nat.lt_two_pow_self)))

theorem isz_buSZ_s (p s t : ℕ) (hst : s < t) (htp : t < 2 ^ p) : isz ((s : ℤ)) ≤ buSZ p :=
  isz_nat_le_pow (p := p) (A := p) (n := s) (by simp only [buSZ]; omega) (le_of_lt (lt_trans hst htp))

theorem isz_buSZ_t (p t : ℕ) (htp : t < 2 ^ p) : isz ((t : ℤ)) ≤ buSZ p :=
  isz_nat_le_pow (p := p) (A := p) (n := t) (by simp only [buSZ]; omega) (le_of_lt htp)

/-- Every entry of the canonical block has `vsz ≤ buSZ p`. -/
theorem vsz_buCB_entries (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hα : 2 ≤ α) (hp : 100 ≤ p)
    (htp : t < 2 ^ p) (hαp : α ^ 2 < p) : ∀ v ∈ buCB p α s t, vsz v ≤ buSZ p := by
  intro v hv
  simp only [buCB, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [vsz_int]; exact isz_buSZ_p p
  · rw [vsz_int]; exact isz_buSZ_alpha p α hαp
  · rw [vsz_int]; exact isz_buSZ_s p s t hst htp
  · rw [vsz_int]; exact isz_buSZ_t p t htp
  · rw [vsz_int]; exact isz_egM_le p α
  · rw [vsz_int]; exact isz_egN_le p α s t (by omega) (lt_trans hst htp) (by omega)
  · rw [vsz_int]; exact isz_auPi_le_buSZ p

/-- `egN p α s t ≤ p + 1`, from the paper's hypothesis `θ ≥ p/α⁴`. -/
theorem bk_egN_le_p1 (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hα : 2 ≤ α) (hαp : α ^ 2 < p)
    (hθ : (p : ℝ) / (α : ℝ) ^ 4 ≤ (t : ℝ) / s - 1) : egN p α s t ≤ p + 1 := by
  have hspos : 0 < s := by omega
  have hsR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hspos
  have htsR : (0 : ℝ) < ((t - s : ℕ) : ℝ) := by
    have : 0 < t - s := Nat.sub_pos_of_lt hst
    exact_mod_cast this
  have hkeyR : (p : ℝ) * (s : ℝ) ≤ (α : ℝ) ^ 4 * ((t : ℝ) - (s : ℝ)) := by
    have h1 : ((p : ℝ) / (α : ℝ) ^ 4) ≤ ((t : ℝ) - (s : ℝ)) / (s : ℝ) := by
      have h0 : (t : ℝ) / (s : ℝ) - 1 = ((t : ℝ) - (s : ℝ)) / (s : ℝ) := by
        field_simp
      rw [← h0]
      exact hθ
    have h2 : (0 : ℝ) ≤ (α : ℝ) ^ 4 * (s : ℝ) := by positivity
    have h3 : ((p : ℝ) / (α : ℝ) ^ 4) * ((α : ℝ) ^ 4 * (s : ℝ)) ≤
        (((t : ℝ) - (s : ℝ)) / (s : ℝ)) * ((α : ℝ) ^ 4 * (s : ℝ)) :=
      mul_le_mul_of_nonneg_right h1 h2
    have h4 : ((p : ℝ) / (α : ℝ) ^ 4) * ((α : ℝ) ^ 4 * (s : ℝ)) = (p : ℝ) * (s : ℝ) := by
      field_simp
    have h5 : (((t : ℝ) - (s : ℝ)) / (s : ℝ)) * ((α : ℝ) ^ 4 * (s : ℝ)) =
        (α : ℝ) ^ 4 * ((t : ℝ) - (s : ℝ)) := by
      field_simp
    linarith
  have hkey : p * s ≤ α ^ 4 * (t - s) := by
    have hcast : ((t : ℝ) - (s : ℝ)) = ((t - s : ℕ) : ℝ) := by
      rw [Nat.cast_sub (le_of_lt hst)]
    rw [hcast] at hkeyR
    exact_mod_cast hkeyR
  have h2 : (p * s - 1) / (α ^ 2 * (t - s)) ≤ α ^ 2 := by
    refine Nat.div_le_of_le_mul ?_
    have hp5 : 0 < p := by nlinarith [hαp, hα]
    have hb : p * s - 1 < α ^ 2 * (α ^ 2 * (t - s)) := by
      calc p * s - 1 < p * s := Nat.sub_lt (Nat.mul_pos hp5 (by omega)) (by norm_num)
        _ ≤ α ^ 4 * (t - s) := hkey
        _ = α ^ 2 * (α ^ 2 * (t - s)) := by ring
    calc p * s - 1 ≤ α ^ 2 * (α ^ 2 * (t - s)) := le_of_lt hb
      _ = α ^ 2 * (t - s) * α ^ 2 := by ring
  have h8 : α ^ 2 + 1 ≤ p + 1 := by omega
  have h9 : egN p α s t = (p * s - 1) / (α ^ 2 * (t - s)) + 1 := rfl
  omega

theorem bk_vsz_buL11_le (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hα : 2 ≤ α) (hαp : α ^ 2 < p)
    (hθ : (p : ℝ) / (α : ℝ) ^ 4 ≤ (t : ℝ) / s - 1) :
    vsz (buL11 p α s t) ≤ 4 * (p + 1) := by
  have hN : egN p α s t ≤ p + 1 := bk_egN_le_p1 p α s t hs hst hα hαp hθ
  have h1 : (List.range (egN p α s t - 1)).length = egN p α s t - 1 := List.length_range
  rw [buL11, bk_vsz_zl, List.length_map, h1, List.map_map, bk_sum_isz_neg_one_pow]
  omega



theorem rot7_mono {K M M' : ℕ} (h : M ≤ M') : K * 8 * (8 * M + 1) ≤ K * 8 * (8 * M' + 1) := by
  have h1 : 8 * M + 1 ≤ 8 * M' + 1 := by omega
  exact Nat.mul_le_mul_left (K * 8) h1

theorem rot_cost_general {p t E M K : ℕ} (hp : 100 ≤ p) (hM : M ≤ (t + 1) * (p + 1) ^ 20)
    (hBIG : 7 * (K * 8 * (8 * (2 * ((t + 1) * (p + 1) ^ 20)) + 1)) ≤ (t + 1) * (p + 1) ^ E) :
    7 * (K * 8 * (8 * M + 1)) ≤ (t + 1) * (p + 1) ^ E := by
  have h2 : M ≤ 2 * ((t + 1) * (p + 1) ^ 20) :=
    le_trans hM (le_mul_of_one_le_left (Nat.zero_le _) (by norm_num : (1 : ℕ) ≤ 2))
  exact le_trans (Nat.mul_le_mul_left 7 (rot7_mono h2)) hBIG

theorem add_bound {p t E a b : ℕ} (hp : 100 ≤ p) (ha : a ≤ (t + 1) * (p + 1) ^ E)
    (hb : b ≤ (t + 1) * (p + 1) ^ E) : a + b ≤ (t + 1) * (p + 1) ^ (E + 1) := by
  have h2 : (t + 1) * (p + 1) ^ (E + 1) = ((t + 1) * (p + 1) ^ E) * (p + 1) := by
    rw [pow_succ]
    ring_nf
  rw [h2]
  have h3 : (2 : ℕ) ≤ p + 1 := by omega
  calc a + b ≤ (t + 1) * (p + 1) ^ E + (t + 1) * (p + 1) ^ E := Nat.add_le_add ha hb
    _ = 2 * ((t + 1) * (p + 1) ^ E) := by ring_nf
    _ ≤ (p + 1) * ((t + 1) * (p + 1) ^ E) := Nat.mul_le_mul_right _ h3
    _ = ((t + 1) * (p + 1) ^ E) * (p + 1) := by ring_nf

theorem big_le {p t E E' : ℕ} (h : E ≤ E') : (t + 1) * (p + 1) ^ E ≤ (t + 1) * (p + 1) ^ E' :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) h)

def qP (p : ℕ) : Val := Val.int (p : ℤ)
def qA (α : ℕ) : Val := Val.int (α : ℤ)
def qS (s : ℕ) : Val := Val.int (s : ℤ)
def qT (t : ℕ) : Val := Val.int (t : ℤ)
def qM (p α : ℕ) : Val := Val.int ((egM p α : ℕ) : ℤ)
def qN (p α s t : ℕ) : Val := Val.int ((egN p α s t : ℕ) : ℤ)
def qPi (p : ℕ) : Val := Val.int (auPi p)
def BuSizes (p α s t : ℕ) : Prop :=
  vsz (buL7 p α s t) ≤ (t + 1) * (p + 1) ^ 20 ∧ vsz (buL8 p α s t) ≤ (t + 1) * (p + 1) ^ 20 ∧
  vsz (buL9 p α s t) ≤ (t + 1) * (p + 1) ^ 20 ∧ vsz (buL10 p α s t) ≤ (t + 1) * (p + 1) ^ 20

def BuSmall (p α s t E : ℕ) : Prop :=
  vsz (buL11 p α s t) ≤ (t + 1) * (p + 1) ^ 20 ∧ buSZ p ≤ (t + 1) * (p + 1) ^ 20 ∧
  buSZ p + 1 ≤ (p + 1) ^ 4 ∧ egN p α s t + 1 ≤ (p + 1) ^ 2 ∧
  egM p α + 1 ≤ (p + 1) ^ 5 ∧ (18 : ℕ) ≤ (p + 1) ^ 5 ∧
  18 * ((t + 1) * (p + 1) ^ E) ≤ (t + 1) * (p + 1) ^ (E + 5)

def BuCosts (p t E α s KN KM KP Kroll Kdrop Kdup K11 K10 K9 K8 K7 : ℕ) : Prop :=
  KN * (p + 1) ^ KN ≤ (t + 1) * (p + 1) ^ E ∧
  4 * (Kroll * 5 * (5 * buSZ p + 1)) ≤ (t + 1) * (p + 1) ^ E ∧
  KM * (p + 1) ^ KM ≤ (t + 1) * (p + 1) ^ E ∧
  Kdup * (buSZ p + 1) ≤ (t + 1) * (p + 1) ^ E ∧
  KP * (p + 1) ^ KP ≤ (t + 1) * (p + 1) ^ E ∧
  6 * (Kroll * 7 * (7 * buSZ p + 1)) ≤ (t + 1) * (p + 1) ^ E ∧
  K11 * (egN p α s t + 1) * (p + 1) ^ K11 ≤ (t + 1) * (p + 1) ^ E ∧
  K10 * (egM p α + 1) * (s + 1) * (p + 1) ^ K10 ≤ (t + 1) * (p + 1) ^ E ∧
  K9 * (s + 1) * (p + 1) ^ K9 ≤ (t + 1) * (p + 1) ^ E ∧
  K8 * (s + 1) * (p + 1) ^ K8 ≤ (t + 1) * (p + 1) ^ E ∧
  K7 * (t + 1) * (p + 1) ^ K7 ≤ (t + 1) * (p + 1) ^ E ∧
  7 * (Kroll * 8 * (8 * (2 * ((t + 1) * (p + 1) ^ 20)) + 1)) ≤ (t + 1) * (p + 1) ^ E ∧
  (Kroll * 7 * (7 * buSZ p + 1) + Kdrop * (buSZ p + 1) ≤ (t + 1) * (p + 1) ^ E)

/-! ### The core assembly of the table word -/

theorem buPrepCore (KL : HvdH.KernelLib) (IL : HvdH.IntLib) (LL : HvdH.LayoutLib)
    (piProg : Cmd) (KP : ℕ)
    (piSpec : ∀ (main : Cmd) (p : ℕ), 100 ≤ p →
      Pipe main piProg [Val.int (p : ℤ)] [Val.int (auPi p)] (KP * (p + 1) ^ KP))
    (nProg : Cmd) (KN : ℕ)
    (nSpec : ∀ (main : Cmd) (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hα : 2 ≤ α) (hp : 100 ≤ p)
      (htp : t < 2 ^ p) (hαp : α ^ 2 < p),
      Pipe main nProg [Val.int (p : ℤ), Val.int (α : ℤ), Val.int (s : ℤ), Val.int (t : ℤ)]
        ([Val.int ((egN p α s t : ℕ) : ℤ)] ++
          [Val.int (p : ℤ), Val.int (α : ℤ), Val.int (s : ℤ), Val.int (t : ℤ)])
        (KN * (p + 1) ^ KN))
    (mProg : Cmd) (KM : ℕ)
    (mSpec : ∀ (main : Cmd) (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hα : 2 ≤ α) (hp : 100 ≤ p)
      (htp : t < 2 ^ p) (hαp : α ^ 2 < p),
      Pipe main mProg [Val.int (p : ℤ), Val.int (α : ℤ), Val.int (s : ℤ), Val.int (t : ℤ)]
        ([Val.int ((egM p α : ℕ) : ℤ)] ++
          [Val.int (p : ℤ), Val.int (α : ℤ), Val.int (s : ℤ), Val.int (t : ℤ)])
        (KM * (p + 1) ^ KM))
    (signsProg : Cmd) (K11 : ℕ)
    (signsSpec : ∀ (main : Cmd) (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hα : 2 ≤ α)
      (hp : 100 ≤ p) (htp : t < 2 ^ p) (hαp : α ^ 2 < p),
      Pipe main signsProg (buCB p α s t) (buL11 p α s t :: buCB p α s t)
        (K11 * (egN p α s t + 1) * (p + 1) ^ K11))
    (colsProg : Cmd) (K10 : ℕ)
    (colsSpec : ∀ (main : Cmd) (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hα : 2 ≤ α)
      (hp : 100 ≤ p) (htp : t < 2 ^ p) (hαp : α ^ 2 < p),
      Pipe main colsProg (buCB p α s t) (buL10 p α s t :: buCB p α s t)
        (K10 * (egM p α + 1) * (s + 1) * (p + 1) ^ K10))
    (dwProg : Cmd) (K9 : ℕ)
    (dwSize : ∀ (p α s t : ℕ), α ^ 2 ≤ p → 0 < s → s < 2 ^ p → 100 ≤ p → ∀ ℓ : ℤ,
      isz (buWd p α s t ℓ) ≤ buSZ p)
    (dwSpec : ∀ (main : Cmd) (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hα : 2 ≤ α)
      (hp : 100 ≤ p) (htp : t < 2 ^ p) (hαp : α ^ 2 < p),
      (∀ ℓ : ℤ, isz (buWd p α s t ℓ) ≤ buSZ p) →
      Pipe main dwProg (buCB p α s t) (buL9 p α s t :: buCB p α s t)
        (K9 * (s + 1) * (p + 1) ^ K9))
    (keysProg : Cmd) (K8 : ℕ)
    (keysSpec : ∀ (main : Cmd) (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hα : 2 ≤ α)
      (hp : 100 ≤ p) (htp : t < 2 ^ p) (hαp : α ^ 2 < p),
      Pipe main keysProg (buCB p α s t) (buL8 p α s t :: buCB p α s t)
        (K8 * (s + 1) * (p + 1) ^ K8))
    (lamProg : Cmd) (K7 : ℕ)
    (lamSpec : ∀ (main : Cmd) (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hcop : Nat.Coprime s t)
      (hα : 2 ≤ α) (hp : 100 ≤ p) (htp : t < 2 ^ p) (hαp : α ^ 2 < p),
      Pipe main lamProg (buCB p α s t) (buL7 p α s t :: buCB p α s t)
        (K7 * (t + 1) * (p + 1) ^ K7))
    (hEntrySizes : ∀ (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hα : 2 ≤ α) (hp : 100 ≤ p)
      (htp : t < 2 ^ p) (hαp : α ^ 2 < p)
      (hθ : (p : ℝ) / (α : ℝ) ^ 4 ≤ (t : ℝ) / s - 1), BuSizes p α s t)
    (hPrepSmall : ∀ (p α s t E : ℕ) (hs : 2 ≤ s) (hst : s < t) (hα : 2 ≤ α) (hp : 100 ≤ p)
      (htp : t < 2 ^ p) (hαp : α ^ 2 < p)
      (hθ : (p : ℝ) / (α : ℝ) ^ 4 ≤ (t : ℝ) / s - 1) (hE : 100 ≤ E), BuSmall p α s t E)
    (hCosts : ∀ (p t E : ℕ), 100 ≤ p → 100 ≤ E → ∀ (α s : ℕ), s + 1 ≤ t + 1 →
      egM p α + 1 ≤ (p + 1) ^ 5 → buSZ p + 1 ≤ (p + 1) ^ 4 → egN p α s t + 1 ≤ (p + 1) ^ 2 →
      ∀ (KN KM KP Kroll Kdrop Kdup K11 K10 K9 K8 K7 : ℕ),
      3 * KN ≤ E → 3 * KM ≤ E → 3 * KP ≤ E → 3 * Kroll ≤ E → 3 * Kdrop ≤ E → 3 * Kdup ≤ E →
      3 * K11 ≤ E → 3 * K10 ≤ E → 3 * K9 ≤ E → 3 * K8 ≤ E → 3 * K7 ≤ E →
      BuCosts p t E α s KN KM KP Kroll Kdrop Kdup K11 K10 K9 K8 K7) :
    ∃ (prep : Cmd) (K : ℕ), ∀ (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hcop : Nat.Coprime s t)
      (htp : t < 2 ^ p) (hα : 2 ≤ α) (hp : 100 ≤ p) (hαp : α ^ 2 < p)
      (hθ : (p : ℝ) / (α : ℝ) ^ 4 ≤ (t : ℝ) / s - 1) (main : Cmd),
      WordR main prep
        (fun vs => ∃ rest,
          vs = [Val.int (p : ℤ), Val.int (α : ℤ), Val.int (s : ℤ), Val.int (t : ℤ)] ++ rest)
        (fun vs out => ∃ rest,
          vs = [Val.int (p : ℤ), Val.int (α : ℤ), Val.int (s : ℤ), Val.int (t : ℤ)] ++ rest ∧
          out = [Val.int (p : ℤ), Val.int (α : ℤ), Val.int (s : ℤ), Val.int (t : ℤ),
            Val.int ((egM p α : ℕ) : ℤ), Val.int ((egN p α s t : ℕ) : ℤ), buL7 p α s t,
            buL8 p α s t, buL9 p α s t, buL10 p α s t, buL11 p α s t] ++ rest)
        (fun _ => K * (t + 1) * (p + 1) ^ K) := by
  obtain ⟨rollProg, Kroll, hRoll⟩ := KL.roll
  obtain ⟨dropProg, Kdrop, hDrop⟩ := KL.drop
  obtain ⟨dupProg, Kdup, hDup⟩ := KL.dup
  set KS : ℕ := Kroll + Kdrop + Kdup + KP + KN + KM + K11 + K10 + K9 + K8 + K7 + 100 with hKSdef
  set E : ℕ := 4 * KS + 100 with hEdef
  have hEroll : 3 * Kroll ≤ E := by omega
  have hEdrop : 3 * Kdrop ≤ E := by omega
  have hEdup : 3 * Kdup ≤ E := by omega
  have hEP : 3 * KP ≤ E := by omega
  have hEN : 3 * KN ≤ E := by omega
  have hEM : 3 * KM ≤ E := by omega
  have hE11 : 3 * K11 ≤ E := by omega
  have hE10 : 3 * K10 ≤ E := by omega
  have hE9 : 3 * K9 ≤ E := by omega
  have hE8 : 3 * K8 ≤ E := by omega
  have hE7 : 3 * K7 ≤ E := by omega
  let r4 : Cmd := buRollN rollProg 4 4
  let r6 : Cmd := buRollN rollProg 6 6
  let r7 : Cmd := buRollN rollProg 7 7
  let prep : Cmd := .seq nProg (.seq r4 (.seq mProg (.seq r4 (.seq dupProg (.seq piProg
    (.seq r6 (.seq signsProg (.seq r7 (.seq colsProg (.seq r7 (.seq dwProg (.seq r7
    (.seq keysProg (.seq r7 (.seq lamProg (.seq r7 (.seq (rollProg 6) dropProg)))))))))))))))))
  refine ⟨prep, E + 5, ?_⟩
  intro p α s t hs hst hcop htp hα hp hαp hθ main
  have hp2 : 2 ≤ p := by omega
  have hE100 : 100 ≤ E := by simp only [E, KS]; omega
  have hES := hEntrySizes p α s t hs hst hα hp htp hαp hθ
  simp only [BuSizes] at hES
  obtain ⟨hsz7, hsz8, hsz9, hsz10⟩ := hES
  clear hEntrySizes
  have hPS := hPrepSmall p α s t E hs hst hα hp htp hαp hθ hE100
  simp only [BuSmall] at hPS
  obtain ⟨hsz11, hsmall, hBK, hN1, hα5, h18, ht5⟩ := hPS
  clear hPrepSmall
  have hst1 : s + 1 ≤ t + 1 := by omega
  have hBC := hCosts p t E hp hE100 α s hst1 hα5 hBK hN1 KN KM KP Kroll Kdrop Kdup K11 K10 K9
    K8 K7 hEN hEM hEP hEroll hEdrop hEdup hE11 hE10 hE9 hE8 hE7
  simp only [BuCosts] at hBC
  obtain ⟨hb1, hb4, hbM, hbDup, hbPi, hb6, hb11, hb10, hb9, hb8, hb7, hbR7, hbDrop⟩ := hBC
  clear hCosts
  have hbP : vsz (qP p) ≤ buSZ p := by simp only [qP]; rw [vsz_int]; exact isz_buSZ_p p
  have hbA : vsz (qA α) ≤ buSZ p := by simp only [qA]; rw [vsz_int]; exact isz_buSZ_alpha p α hαp
  have hbS : vsz (qS s) ≤ buSZ p := by simp only [qS]; rw [vsz_int]; exact isz_buSZ_s p s t hst htp
  have hbT : vsz (qT t) ≤ buSZ p := by simp only [qT]; rw [vsz_int]; exact isz_buSZ_t p t htp
  have hbMv : vsz (qM p α) ≤ buSZ p := by simp only [qM]; rw [vsz_int]; exact isz_egM_le p α
  have hbNv : vsz (qN p α s t) ≤ buSZ p := by
    simp only [qN]; rw [vsz_int]
    exact isz_egN_le p α s t (by omega) (lt_trans hst htp) (by omega)
  have hbPi' : vsz (qPi p) ≤ buSZ p := by simp only [qPi]; rw [vsz_int]; exact isz_auPi_le_buSZ p
  have hsP : vsz (qP p) ≤ (t + 1) * (p + 1) ^ 20 := le_trans hbP hsmall
  have hsA : vsz (qA α) ≤ (t + 1) * (p + 1) ^ 20 := le_trans hbA hsmall
  have hsS : vsz (qS s) ≤ (t + 1) * (p + 1) ^ 20 := le_trans hbS hsmall
  have hsT : vsz (qT t) ≤ (t + 1) * (p + 1) ^ 20 := le_trans hbT hsmall
  have hsM : vsz (qM p α) ≤ (t + 1) * (p + 1) ^ 20 := le_trans hbMv hsmall
  have hsN : vsz (qN p α s t) ≤ (t + 1) * (p + 1) ^ 20 := le_trans hbNv hsmall
  have hsPi : vsz (qPi p) ≤ (t + 1) * (p + 1) ^ 20 := le_trans hbPi' hsmall
  -- step 1
  have hs1 : Pipe main nProg [qP p, qA α, qS s, qT t]
      ([qN p α s t] ++ [qP p, qA α, qS s, qT t]) ((t + 1) * (p + 1) ^ E) :=
    Pipe.le (nSpec main p α s t hs hst hα hp htp hαp) hb1
  -- step 2
  have hs2 : Pipe main (buRollN rollProg 4 4) ([qN p α s t] ++ [qP p, qA α, qS s, qT t])
      ([qP p, qA α, qS s, qT t, qN p α s t]) ((t + 1) * (p + 1) ^ E) :=
    Pipe.le (buInsert4 main hRoll (qN p α s t) (qP p) (qA α) (qS s) (qT t)
      hbNv hbP hbA hbS hbT) hb4
  -- step 3
  have hs3 : Pipe main mProg [qP p, qA α, qS s, qT t, qN p α s t]
      ([qM p α] ++ [qP p, qA α, qS s, qT t, qN p α s t]) ((t + 1) * (p + 1) ^ E) :=
    Pipe.le (Pipe.appendTail (A := [qP p, qA α, qS s, qT t])
      (B := [qM p α] ++ [qP p, qA α, qS s, qT t]) [qN p α s t]
      (mSpec main p α s t hs hst hα hp htp hαp)) hbM
  -- step 4
  have hs4 : Pipe main (buRollN rollProg 4 4)
      ([qM p α] ++ [qP p, qA α, qS s, qT t, qN p α s t])
      ([qP p, qA α, qS s, qT t, qM p α] ++ [qN p α s t]) ((t + 1) * (p + 1) ^ E) :=
    Pipe.le (Pipe.appendTail (A := [qM p α, qP p, qA α, qS s, qT t])
      (B := [qP p, qA α, qS s, qT t, qM p α]) [qN p α s t]
      (buInsert4 main hRoll (qM p α) (qP p) (qA α) (qS s) (qT t) hbMv hbP hbA hbS hbT)) hb4
  -- step 5
  have hs5 : Pipe main dupProg [qP p, qA α, qS s, qT t, qM p α, qN p α s t]
      ([qP p, qP p, qA α, qS s, qT t, qM p α, qN p α s t]) ((t + 1) * (p + 1) ^ E) := by
    refine Pipe.le (Pipe.appendTail (A := [qP p]) (B := [qP p, qP p])
      [qA α, qS s, qT t, qM p α, qN p α s t] (Pipe.dup main hDup (qP p))) ?_
    exact le_trans (Nat.mul_le_mul_left Kdup (Nat.add_le_add_right hbP 1)) hbDup
  -- step 6
  have hs6 : Pipe main piProg ([qP p, qP p, qA α, qS s, qT t, qM p α, qN p α s t])
      ([qPi p] ++ [qP p, qA α, qS s, qT t, qM p α, qN p α s t]) ((t + 1) * (p + 1) ^ E) :=
    Pipe.le (Pipe.appendTail (A := [qP p]) (B := [qPi p])
      [qP p, qA α, qS s, qT t, qM p α, qN p α s t] (piSpec main p hp)) hbPi
  -- step 7
  have hs7 : Pipe main (buRollN rollProg 6 6)
      ([qPi p] ++ [qP p, qA α, qS s, qT t, qM p α, qN p α s t])
      (buCB p α s t) ((t + 1) * (p + 1) ^ E) :=
    Pipe.le (buInsert6 main hRoll (qPi p) (qP p) (qA α) (qS s) (qT t) (qM p α) (qN p α s t)
      hbPi' hbP hbA hbS hbT hbMv hbNv) hb6
  -- step 8
  have hs8 : Pipe main signsProg (buCB p α s t) ([buL11 p α s t] ++ buCB p α s t)
      ((t + 1) * (p + 1) ^ E) :=
    Pipe.le (signsSpec main p α s t hs hst hα hp htp hαp) hb11
  -- step 9
  have hs9 : Pipe main (buRollN rollProg 7 7) ([buL11 p α s t] ++ buCB p α s t)
      (buCB p α s t ++ [buL11 p α s t]) ((t + 1) * (p + 1) ^ E) := by
    refine Pipe.le (buInsert7 main hRoll (buL11 p α s t) (qP p) (qA α) (qS s) (qT t)
      (qM p α) (qN p α s t) (qPi p) hsz11 hsP hsA hsS hsT hsM hsN hsPi) ?_
    refine le_trans (Nat.mul_le_mul_left 7 (rot7_mono ?_)) hbR7
    exact le_mul_of_one_le_left (Nat.zero_le _) (by norm_num : (1 : ℕ) ≤ 2)
  -- step 10
  have hs10 : Pipe main colsProg (buCB p α s t ++ [buL11 p α s t])
      ([buL10 p α s t] ++ buCB p α s t ++ [buL11 p α s t]) ((t + 1) * (p + 1) ^ E) :=
    Pipe.le (Pipe.appendTail (A := buCB p α s t) (B := buL10 p α s t :: buCB p α s t)
      [buL11 p α s t] (colsSpec main p α s t hs hst hα hp htp hαp)) hb10
  -- step 11
  have hs11 : Pipe main (buRollN rollProg 7 7)
      ([buL10 p α s t] ++ buCB p α s t ++ [buL11 p α s t])
      (buCB p α s t ++ [buL10 p α s t, buL11 p α s t]) ((t + 1) * (p + 1) ^ E) := by
    refine Pipe.le (buInsert7T main hRoll (buL10 p α s t) (qP p) (qA α) (qS s) (qT t) (qM p α)
      (qN p α s t) (qPi p) [buL11 p α s t] hsz10 hsP hsA hsS hsT hsM hsN hsPi) ?_
    refine le_trans (Nat.mul_le_mul_left 7 (rot7_mono ?_)) hbR7
    exact le_mul_of_one_le_left (Nat.zero_le _) (by norm_num : (1 : ℕ) ≤ 2)
  -- step 12
  have hs12 : Pipe main dwProg (buCB p α s t ++ [buL10 p α s t, buL11 p α s t])
      ([buL9 p α s t] ++ buCB p α s t ++ [buL10 p α s t, buL11 p α s t])
      ((t + 1) * (p + 1) ^ E) :=
    Pipe.le (Pipe.appendTail (A := buCB p α s t) (B := buL9 p α s t :: buCB p α s t)
      [buL10 p α s t, buL11 p α s t]
      (dwSpec main p α s t hs hst hα hp htp hαp
        (dwSize p α s t (le_of_lt hαp) (by omega) (lt_trans hst htp) hp))) hb9
  -- step 13
  have hs13 : Pipe main (buRollN rollProg 7 7)
      ([buL9 p α s t] ++ buCB p α s t ++ [buL10 p α s t, buL11 p α s t])
      (buCB p α s t ++ [buL9 p α s t, buL10 p α s t, buL11 p α s t])
      ((t + 1) * (p + 1) ^ E) := by
    refine Pipe.le (buInsert7T main hRoll (buL9 p α s t) (qP p) (qA α) (qS s) (qT t) (qM p α)
      (qN p α s t) (qPi p) [buL10 p α s t, buL11 p α s t]
      hsz9 hsP hsA hsS hsT hsM hsN hsPi) ?_
    refine le_trans (Nat.mul_le_mul_left 7 (rot7_mono ?_)) hbR7
    exact le_mul_of_one_le_left (Nat.zero_le _) (by norm_num : (1 : ℕ) ≤ 2)
  -- step 14
  have hs14 : Pipe main keysProg
      (buCB p α s t ++ [buL9 p α s t, buL10 p α s t, buL11 p α s t])
      ([buL8 p α s t] ++ buCB p α s t ++ [buL9 p α s t, buL10 p α s t, buL11 p α s t])
      ((t + 1) * (p + 1) ^ E) :=
    Pipe.le (Pipe.appendTail (A := buCB p α s t) (B := buL8 p α s t :: buCB p α s t)
      [buL9 p α s t, buL10 p α s t, buL11 p α s t]
      (keysSpec main p α s t hs hst hα hp htp hαp)) hb8
  -- step 15
  have hs15 : Pipe main (buRollN rollProg 7 7)
      ([buL8 p α s t] ++ buCB p α s t ++ [buL9 p α s t, buL10 p α s t, buL11 p α s t])
      (buCB p α s t ++ [buL8 p α s t, buL9 p α s t, buL10 p α s t, buL11 p α s t])
      ((t + 1) * (p + 1) ^ E) := by
    refine Pipe.le (buInsert7T main hRoll (buL8 p α s t) (qP p) (qA α) (qS s) (qT t) (qM p α)
      (qN p α s t) (qPi p) [buL9 p α s t, buL10 p α s t, buL11 p α s t]
      hsz8 hsP hsA hsS hsT hsM hsN hsPi) ?_
    refine le_trans (Nat.mul_le_mul_left 7 (rot7_mono ?_)) hbR7
    exact le_mul_of_one_le_left (Nat.zero_le _) (by norm_num : (1 : ℕ) ≤ 2)
  -- step 16
  have hs16 : Pipe main lamProg
      (buCB p α s t ++ [buL8 p α s t, buL9 p α s t, buL10 p α s t, buL11 p α s t])
      ([buL7 p α s t] ++ buCB p α s t ++
        [buL8 p α s t, buL9 p α s t, buL10 p α s t, buL11 p α s t])
      ((t + 1) * (p + 1) ^ E) :=
    Pipe.le (Pipe.appendTail (A := buCB p α s t) (B := buL7 p α s t :: buCB p α s t)
      [buL8 p α s t, buL9 p α s t, buL10 p α s t, buL11 p α s t]
      (lamSpec main p α s t hs hst hcop hα hp htp hαp)) hb7
  -- step 17
  have hs17 : Pipe main (buRollN rollProg 7 7)
      ([buL7 p α s t] ++ buCB p α s t ++
        [buL8 p α s t, buL9 p α s t, buL10 p α s t, buL11 p α s t])
      (buCB p α s t ++
        [buL7 p α s t, buL8 p α s t, buL9 p α s t, buL10 p α s t, buL11 p α s t])
      ((t + 1) * (p + 1) ^ E) := by
    refine Pipe.le (buInsert7T main hRoll (buL7 p α s t) (qP p) (qA α) (qS s) (qT t) (qM p α)
      (qN p α s t) (qPi p) [buL8 p α s t, buL9 p α s t, buL10 p α s t, buL11 p α s t]
      hsz7 hsP hsA hsS hsT hsM hsN hsPi) ?_
    refine le_trans (Nat.mul_le_mul_left 7 (rot7_mono ?_)) hbR7
    exact le_mul_of_one_le_left (Nat.zero_le _) (by norm_num : (1 : ℕ) ≤ 2)
  -- step 18
  have hs18 : Pipe main (.seq (rollProg 6) dropProg)
      ([qP p, qA α, qS s, qT t, qM p α, qN p α s t, qPi p] ++
        [buL7 p α s t, buL8 p α s t, buL9 p α s t, buL10 p α s t, buL11 p α s t])
      ([qP p, qA α, qS s, qT t, qM p α, qN p α s t] ++
        [buL7 p α s t, buL8 p α s t, buL9 p α s t, buL10 p α s t, buL11 p α s t])
      ((t + 1) * (p + 1) ^ E) :=
    Pipe.le (buRoll6DropT main hRoll hDrop (qP p) (qA α) (qS s) (qT t) (qM p α)
      (qN p α s t) (qPi p) [buL7 p α s t, buL8 p α s t, buL9 p α s t, buL10 p α s t,
      buL11 p α s t] hbP hbA hbS hbT hbMv hbNv hbPi') hbDrop
  clear piSpec nSpec mSpec signsSpec colsSpec dwSpec dwSize keysSpec lamSpec
  have hc16 := Pipe.comp hs17 hs18
  have hc15 := Pipe.comp hs16 hc16
  have hc14 := Pipe.comp hs15 hc15
  have hc13 := Pipe.comp hs14 hc14
  have hc12 := Pipe.comp hs13 hc13
  have hc11 := Pipe.comp hs12 hc12
  have hc10 := Pipe.comp hs11 hc11
  have hc9 := Pipe.comp hs10 hc10
  have hc8 := Pipe.comp hs9 hc9
  have hc7 := Pipe.comp hs8 hc8
  have hc6 := Pipe.comp hs7 hc7
  have hc5 := Pipe.comp hs6 hc6
  have hc4 := Pipe.comp hs5 hc5
  have hc3 := Pipe.comp hs4 hc4
  have hc2 := Pipe.comp hs3 hc3
  have hc1 := Pipe.comp hs2 hc2
  have hcall := Pipe.comp hs1 hc1
  refine buPipeToWordR (Pipe.le hcall ?_)
  have hY : (t + 1) * (p + 1) ^ (E + 5) ≤ (E + 5) * (t + 1) * (p + 1) ^ (E + 5) := by
    calc (t + 1) * (p + 1) ^ (E + 5) ≤ (E + 5) * ((t + 1) * (p + 1) ^ (E + 5)) :=
          le_mul_of_one_le_left (Nat.zero_le _) (by omega : (1 : ℕ) ≤ E + 5)
      _ = (E + 5) * (t + 1) * (p + 1) ^ (E + 5) := (Nat.mul_assoc _ _ _).symm
  exact le_trans (buSum18 ht5) hY

/-! ### Assembly of the table word from all the sub-words

`buPrepCore` is the composition of the eight sub-words; here they are obtained from the library
Props (`KL`, `IL`, `LL`) and the arithmetic estimates, except the two whose modules are built
separately: the columns word (`buL10`) and the `λ`-keys word (`buL7`), which are passed in. -/

theorem buPrepOfTwo (KL : HvdH.KernelLib) (IL : HvdH.IntLib) (LL : HvdH.LayoutLib)
    (colsProg : Cmd) (K10 : ℕ)
    (h10 : ∀ (main : Cmd) (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hα : 2 ≤ α)
      (hp : 100 ≤ p) (htp : t < 2 ^ p) (hαp : α ^ 2 < p),
      Pipe main colsProg (buCB p α s t) (buL10 p α s t :: buCB p α s t)
        (K10 * (egM p α + 1) * (s + 1) * (p + 1) ^ K10))
    (lamProg : Cmd) (K7 : ℕ)
    (h7 : ∀ (main : Cmd) (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hcop : Nat.Coprime s t)
      (hα : 2 ≤ α) (hp : 100 ≤ p) (htp : t < 2 ^ p) (hαp : α ^ 2 < p),
      Pipe main lamProg (buCB p α s t) (buL7 p α s t :: buCB p α s t)
        (K7 * (t + 1) * (p + 1) ^ K7)) :
    ∃ (prep : Cmd) (K : ℕ),
    ∀ (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hcop : Nat.Coprime s t) (htp : t < 2 ^ p)
      (hα : 2 ≤ α) (hp : 100 ≤ p) (hαp : α ^ 2 < p)
      (hθ : (p : ℝ) / (α : ℝ) ^ 4 ≤ (t : ℝ) / s - 1)
      (main : Cmd) (N : ℕ) (Cm : ℕ → ℕ), Monotone Cm → MulBelow main N Cm → K * p < N →
    WordR main prep
      (fun vs => ∃ rest, vs = .int p :: .int α :: .int s :: .int t :: rest)
      (fun vs out => ∃ rest, vs = .int p :: .int α :: .int s :: .int t :: rest ∧
        out = buTabList p α s t (by omega) hcop.symm ++ rest)
      (fun _ => K * (t + 1) * (p + 1) ^ K) := by
  obtain ⟨piProg, KP, hPi⟩ := buPiFromP KL IL
  obtain ⟨nProg, KN, hN⟩ := buNFromParams KL IL
  obtain ⟨mProg, KM, hM⟩ := buMFromParams KL IL
  obtain ⟨signElem, Kse, hSe⟩ := buSignElem KL IL
  obtain ⟨signsProg, K11, h11⟩ := buSignsWord KL IL LL signElem Kse hSe
  obtain ⟨hornerProg, Kh, hh⟩ := buHornerWord KL IL
  obtain ⟨wtElem, Kwe, hWe⟩ := buWtElem KL IL hornerProg Kh hh
  obtain ⟨dwElem, Kde, hDe⟩ := buWdElem KL IL hornerProg Kh hh
  obtain ⟨dwProg, K9, h9⟩ := buDwWord KL IL LL dwElem Kde hDe
  obtain ⟨keyElem, Kke, hKe⟩ := buKeyElem KL IL
  obtain ⟨keysProg, K8, h8⟩ := buKeysWordB KL IL LL keyElem Kke hKe
  obtain ⟨prep, K, hprep⟩ := buPrepCore KL IL LL piProg KP hPi nProg KN hN mProg KM hM
    signsProg K11 h11 colsProg K10 h10 dwProg K9
    (fun p α s t hαp hs hsp hp ℓ => (buWdSize p α s t ℓ hαp hs hsp hp).2) h9
    keysProg K8 h8 lamProg K7 h7
    (fun p α s t hs hst hα hp htp hαp hθ => buEntrySizes p α s t hs hst hα hp htp hαp hθ)
    (fun p α s t E hs hst hα hp htp hαp hθ hE =>
      buPrepSmall p α s t E hs hst hα hp htp hαp hθ hE)
    (fun p t E hp hE α s => buAllCosts p t E hp hE α s)
  refine ⟨prep, K, ?_⟩
  intro p α s t hs hst hcop htp hα hp hαp hθ main N Cm _ _ _
  exact hprep p α s t hs hst hcop htp hα hp hαp hθ main

end Work.Resample
