import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.KronP.defs
import Submission.Work.ConvR.basic
import Submission.Work.ConvR.permTop
import Submission.Work.ConvR.dropUnder

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000

namespace Work.KronP

open HvdH

theorem map_eq_listMap {α β : Type} (f : α → β) (l : List α) : l.map f = List.map f l := by
  induction l with
  | nil => rfl
  | cons a as ih => simp only [List.map_cons, ih]

theorem map_length_eq {α β : Type} (f : α → β) (l : List α) : (l.map f).length = l.length := by
  rw [map_eq_listMap]
  exact List.length_map _

theorem toZl_length (A : List ℕ) : (toZl A).length = A.length := by
  induction A with
  | nil => rfl
  | cons a as ih =>
    show ((a : ℤ) :: toZl as).length = (a :: as).length
    simp only [List.length_cons, ih]

theorem deltaL_length (A : List ℕ) (r : ℕ) : (deltaL A r).length = min r (A.length - r) := by
  simp only [deltaL, zsubL, List.length_zipWith, List.length_take, List.length_drop, toZl_length,
    Nat.min_assoc, Nat.min_eq_right (Nat.sub_le _ _)]

theorem getD_zipWith_eq {f : ℤ → ℤ → ℤ} (l₁ l₂ : List ℤ) (i : ℕ)
    (h : i < (l₁.zipWith f l₂).length) :
    (l₁.zipWith f l₂).getD i 0 = f (l₁.getD i 0) (l₂.getD i 0) := by
  induction l₁ generalizing l₂ i with
  | nil => simp at h
  | cons a as ih =>
    cases l₂ with
    | nil => simp at h
    | cons b bs =>
      cases i with
      | zero => rfl
      | succ j =>
        have h' : j < (as.zipWith f bs).length := by simpa using h
        show (as.zipWith f bs).getD j 0 = f (as.getD j 0) (bs.getD j 0)
        exact ih bs j h'

theorem getD_take_eq {l : List ℤ} {r i : ℕ} (h : i < (l.take r).length) :
    (l.take r).getD i 0 = l.getD i 0 := by
  induction r generalizing l i with
  | zero => simp at h
  | succ r' ih =>
    cases l with
    | nil => simp at h
    | cons a as =>
      cases i with
      | zero => rfl
      | succ j =>
        have h' : j < (as.take r').length := by simpa using h
        show (as.take r').getD j 0 = as.getD j 0
        exact ih h'

theorem getD_drop_eq {l : List ℤ} {r i : ℕ} (h : i < (l.drop r).length) :
    (l.drop r).getD i 0 = l.getD (i + r) 0 := by
  rw [List.getD_eq_getElem _ _ h, List.getElem_drop,
    ← List.getD_eq_getElem l 0 (by rw [List.length_drop] at h; omega)]
  rw [Nat.add_comm]

theorem toZl_getD {A : List ℕ} {i : ℕ} (h : i < A.length) :
    (toZl A).getD i 0 = (A.getD i 0 : ℤ) := by
  induction A generalizing i with
  | nil => simp at h
  | cons a as ih =>
    cases i with
    | zero => rfl
    | succ j =>
      have h' : j < as.length := by simpa using h
      show (toZl as).getD j 0 = (as.getD j 0 : ℤ)
      exact ih h'

/-! ## Word-calculus helpers (constant-cost steps) -/

theorem wc_ofWordR {main : Cmd} {p : Cmd} {P : List Val → Prop} {Q : List Val → List Val → Prop}
    {C : List Val → ℕ} {B : ℕ} (h : WordR main p P Q C) (hB : ∀ vs, P vs → C vs ≤ B) :
    Work.ConvR.WordC main p P Q B := by
  intro vs hP s R hR
  obtain ⟨out, s', n, hQ, he, hn, hstk, hoth⟩ := h vs hP s R hR
  exact ⟨out, s', n, hQ, he, le_trans hn (hB vs hP), hstk, hoth⟩

theorem wc_chain {main : Cmd} {p q : Cmd} {P : List Val → Prop} {S : List Val}
    {R : List Val → Prop} {C C' : ℕ}
    (h1 : Work.ConvR.WordC main p P (fun _ out => out = S) C)
    (h2 : Work.ConvR.WordC main q (fun vs => vs = S) (fun _ out => R out) C') :
    Work.ConvR.WordC main (.seq p q) P (fun _ out => R out) (C + C') := by
  intro vs hP s R0 hR0
  obtain ⟨m, s1, n1, hm, he1, hn1, hstk1, hoth1⟩ := h1 vs hP s R0 hR0
  rw [hm] at hstk1
  obtain ⟨out, s2, n2, hQ2, he2, hn2, hstk2, hoth2⟩ := h2 S rfl s1 R0 hstk1
  exact ⟨out, s2, n1 + n2, hQ2, Eval.seq he1 he2, Nat.add_le_add hn1 hn2, hstk2,
    fun k hk => by rw [hoth2 k hk, hoth1 k hk]⟩

theorem wc_chainN {main : Cmd} {p q : Cmd} {P : List Val → Prop} {S : List Val}
    {R : List Val → Prop} {n BIG X : ℕ}
    (h1 : Work.ConvR.WordC main p P (fun _ out => out = S) (1 + n * (BIG * X)))
    (h2 : Work.ConvR.WordC main q (fun vs => vs = S) (fun _ out => R out) (BIG * X)) :
    Work.ConvR.WordC main (.seq p q) P (fun _ out => R out) (1 + (n + 1) * (BIG * X)) := by
  rw [show 1 + (n + 1) * (BIG * X) = (1 + n * (BIG * X)) + BIG * X by ring]
  exact wc_chain h1 h2

theorem wc_skipN {main : Cmd} (S : List Val) (BIG X : ℕ) :
    Work.ConvR.WordC main (.skip : Cmd) (fun vs => vs = S) (fun _ out => out = S)
      (1 + 0 * (BIG * X)) := by
  rw [Nat.zero_mul, Nat.add_zero]
  intro vs hvs s R hR
  exact ⟨S, s, 1, rfl, Eval.skip s, le_rfl, by rw [hR, hvs], fun k _ => rfl⟩

theorem capBound {n BIG X : ℕ} (hX : 1 ≤ X) : 1 + n * (BIG * X) ≤ (n * BIG + 1) * X := by
  have h : n * (BIG * X) = (n * BIG) * X := by ring
  rw [h]
  calc 1 + n * BIG * X ≤ X + n * BIG * X := Nat.add_le_add_right hX _
    _ = (n * BIG + 1) * X := by ring

theorem wc_conseq' {main : Cmd} {p : Cmd} {P P' : List Val → Prop}
    {Q Q' : List Val → List Val → Prop} {C : ℕ}
    (h : Work.ConvR.WordC main p P Q C) (hP : ∀ vs, P' vs → P vs)
    (hQ : ∀ vs out, P' vs → Q vs out → Q' vs out) :
    Work.ConvR.WordC main p P' Q' C := by
  intro vs hvs s R hR
  obtain ⟨out, s', n, hQh, he, hn, hstk, hoth⟩ := h vs (hP vs hvs) s R hR
  exact ⟨out, s', n, hQ vs out hvs hQh, he, hn, hstk, hoth⟩

theorem costK {Klib stuff BIG X : ℕ} (hK : Klib ≤ BIG) (hs : stuff ≤ X) :
    Klib * stuff ≤ BIG * X := Nat.mul_le_mul hK hs

theorem costKc {Klib stuff BIG X c : ℕ} (hs : stuff ≤ c * X) (hK : c * Klib ≤ BIG) :
    Klib * stuff ≤ BIG * X := by
  calc Klib * stuff ≤ Klib * (c * X) := Nat.mul_le_mul_left Klib hs
    _ = (c * Klib) * X := by ring
    _ ≤ BIG * X := Nat.mul_le_mul_right X hK

theorem wc_skip {main : Cmd} (S : List Val) :
    Work.ConvR.WordC main (.skip : Cmd) (fun vs => vs = S) (fun _ out => out = S) 1 := by
  intro vs hvs s R hR
  exact ⟨S, s, 1, rfl, Eval.skip s, le_rfl, by rw [hR, hvs], fun k _ => rfl⟩

theorem wc_pick {main : Cmd} {pickP : ℕ → Cmd} {PK : ℕ}
    (hpick : ∀ (k : ℕ), WordR main (pickP k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs)
      (fun vs => PK * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    (L : List Val) (k : ℕ) (hk : k < L.length) (C : ℕ)
    (hC : PK * (k + 1) * (((L.take (k + 1)).map vsz).sum + 1) ≤ C) :
    Work.ConvR.WordC main (pickP k) (fun vs => vs = L) (fun _ out => out = L.getD k .nil :: L) C := by
  intro vs hvs s R hR
  obtain ⟨out, s', n, hQ, he, hn, hstk, hoth⟩ :=
    hpick k L (by show k < L.length; exact hk) s R (by show s.stk 0 = encs L ++ R; rw [hR, hvs])
  exact ⟨out, s', n, hQ, he, le_trans hn hC, hstk, hoth⟩

theorem wc_roll {main : Cmd} {rollP : ℕ → Cmd} {RK : ℕ}
    (hroll : ∀ (k : ℕ), WordR main (rollP k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs.eraseIdx k)
      (fun vs => RK * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    (L : List Val) (k : ℕ) (hk : k < L.length) (C : ℕ)
    (hC : RK * (k + 1) * (((L.take (k + 1)).map vsz).sum + 1) ≤ C) :
    Work.ConvR.WordC main (rollP k) (fun vs => vs = L)
      (fun _ out => out = L.getD k .nil :: L.eraseIdx k) C := by
  intro vs hvs s R hR
  obtain ⟨out, s', n, hQ, he, hn, hstk, hoth⟩ :=
    hroll k L (by show k < L.length; exact hk) s R (by show s.stk 0 = encs L ++ R; rw [hR, hvs])
  exact ⟨out, s', n, hQ, he, le_trans hn hC, hstk, hoth⟩

theorem wc_swap {main : Cmd} {swapP : Cmd} {SK : ℕ}
    (hswap : WordR main swapP (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = b :: a :: rest)
      (fun vs => SK * (vsz (vs.getD 0 .nil) + vsz (vs.getD 1 .nil) + 1)))
    (a b : Val) (W : List Val) (C : ℕ) (hC : SK * (vsz a + vsz b + 1) ≤ C) :
    Work.ConvR.WordC main swapP (fun vs => vs = a :: b :: W) (fun _ out => out = b :: a :: W) C := by
  intro vs hvs s R hR
  obtain ⟨out, s', n, hQ, he, hn, hstk, hoth⟩ :=
    hswap (a :: b :: W) (by simp) s R (by rw [hR, hvs])
  obtain ⟨a', b', rest, hv', hout⟩ := hQ
  obtain ⟨h1, h2⟩ := (List.cons.injEq _ _ _ _).mp hv'
  obtain ⟨h3, h4⟩ := (List.cons.injEq _ _ _ _).mp h2
  refine ⟨out, s', n, ?_, he, ?_, hstk, hoth⟩
  · rw [hout, ← h1, ← h3, ← h4]
  · refine le_trans hn ?_
    show SK * (vsz ((a :: b :: W).getD 0 .nil) + vsz ((a :: b :: W).getD 1 .nil) + 1) ≤ C
    have ht : vsz ((a :: b :: W).getD 0 .nil) + vsz ((a :: b :: W).getD 1 .nil) + 1
        = vsz a + vsz b + 1 := by simp
    rw [ht]
    exact hC

theorem wc_unc {main : Cmd} {uncP : Cmd} {UK : ℕ}
    (hunc : WordR main uncP (fun vs => ∃ a b rest, vs = .cons a b :: rest)
      (fun vs out => ∃ a b rest, vs = .cons a b :: rest ∧ out = a :: b :: rest)
      (fun _ => UK))
    (a b : Val) (W : List Val) (C : ℕ) (hC : UK ≤ C) :
    Work.ConvR.WordC main uncP (fun vs => vs = .cons a b :: W) (fun _ out => out = a :: b :: W) C := by
  intro vs hvs s R hR
  obtain ⟨out, s', n, hQ, he, hn, hstk, hoth⟩ :=
    hunc (.cons a b :: W) ⟨a, b, W, rfl⟩ s R (by rw [hR, hvs])
  obtain ⟨a', b', rest, hv', hout⟩ := hQ
  obtain ⟨hv1, h2⟩ := (List.cons.injEq _ _ _ _).mp hv'
  obtain ⟨h1, h3⟩ := (Val.cons.injEq _ _ _ _).mp hv1
  refine ⟨out, s', n, ?_, he, le_trans hn hC, hstk, hoth⟩
  rw [hout, ← h1, ← h3, ← h2]

theorem wc_drop {main : Cmd} {dropP : Cmd} {DK : ℕ}
    (hdrop : WordR main dropP (fun vs => vs ≠ [])
      (fun vs out => ∃ v rest, vs = v :: rest ∧ out = rest)
      (fun vs => DK * (vsz (vs.headD .nil) + 1)))
    (v : Val) (W : List Val) (C : ℕ) (hC : DK * (vsz v + 1) ≤ C) :
    Work.ConvR.WordC main dropP (fun vs => vs = v :: W) (fun _ out => out = W) C := by
  intro vs hvs s R hR
  have hne : v :: W ≠ ([] : List Val) := by simp
  obtain ⟨out, s', n, hQ, he, hn, hstk, hoth⟩ := hdrop (v :: W) hne s R (by rw [hR, hvs])
  obtain ⟨v', rest, hv', hout⟩ := hQ
  obtain ⟨h1, h2⟩ := (List.cons.injEq _ _ _ _).mp hv'
  have hout' : out = W := by rw [hout, h2]
  refine ⟨W, s', n, rfl, he, ?_, ?_, hoth⟩
  · refine le_trans hn ?_
    show DK * (vsz ((v :: W).headD .nil) + 1) ≤ C
    have ht : vsz ((v :: W).headD .nil) + 1 = vsz v + 1 := by simp
    rw [ht]
    exact hC
  · rw [hout'] at hstk; exact hstk

theorem wc_take {main : Cmd} {takeP : Cmd} {TK : ℕ}
    (htake : ∀ (k : ℕ) (xs : List Val), WordR main takeP
      (fun vs => ∃ rest, vs = Val.int (k : ℤ) :: ofList xs :: rest)
      (fun vs out => ∃ rest, vs = Val.int (k : ℤ) :: ofList xs :: rest ∧
        out = ofList (xs.take k) :: rest)
      (fun _ => TK * (vsz (ofList xs) + isz (k : ℤ) + 1)))
    (k : ℕ) (xs : List Val) (W : List Val) (C : ℕ)
    (hC : TK * (vsz (ofList xs) + isz (k : ℤ) + 1) ≤ C) :
    Work.ConvR.WordC main takeP (fun vs => vs = Val.int (k : ℤ) :: ofList xs :: W)
      (fun _ out => out = ofList (xs.take k) :: W) C := by
  intro vs hvs s R hR
  obtain ⟨out, s', n, hQ, he, hn, hstk, hoth⟩ :=
    htake k xs (Val.int (k : ℤ) :: ofList xs :: W) ⟨W, rfl⟩ s R (by rw [hR, hvs])
  obtain ⟨rest, hv, hout⟩ := hQ
  have hrest : W = rest := ((List.cons.injEq _ _ _ _).mp ((List.cons.injEq _ _ _ _).mp hv).2).2
  refine ⟨out, s', n, ?_, he, le_trans hn hC, hstk, hoth⟩
  rw [hout, ← hrest]

theorem wc_ldrop {main : Cmd} {ldropP : Cmd} {LK : ℕ}
    (hldrop : ∀ (k : ℕ) (xs : List Val), WordR main ldropP
      (fun vs => ∃ rest, vs = Val.int (k : ℤ) :: ofList xs :: rest)
      (fun vs out => ∃ rest, vs = Val.int (k : ℤ) :: ofList xs :: rest ∧
        out = ofList (xs.drop k) :: rest)
      (fun _ => LK * (vsz (ofList xs) + isz (k : ℤ) + 1)))
    (k : ℕ) (xs : List Val) (W : List Val) (C : ℕ)
    (hC : LK * (vsz (ofList xs) + isz (k : ℤ) + 1) ≤ C) :
    Work.ConvR.WordC main ldropP (fun vs => vs = Val.int (k : ℤ) :: ofList xs :: W)
      (fun _ out => out = ofList (xs.drop k) :: W) C := by
  intro vs hvs s R hR
  obtain ⟨out, s', n, hQ, he, hn, hstk, hoth⟩ :=
    hldrop k xs (Val.int (k : ℤ) :: ofList xs :: W) ⟨W, rfl⟩ s R (by rw [hR, hvs])
  obtain ⟨rest, hv, hout⟩ := hQ
  have hrest : W = rest := ((List.cons.injEq _ _ _ _).mp ((List.cons.injEq _ _ _ _).mp hv).2).2
  refine ⟨out, s', n, ?_, he, le_trans hn hC, hstk, hoth⟩
  rw [hout, ← hrest]

theorem wc_perm {main : Cmd} {PP : List ℕ → Cmd} {Kr : ℕ}
    (hperm : ∀ (n : ℕ) (σ : List ℕ) (head tail : List Val), head.length = n → σ.length = n →
      σ.Perm (List.range n) →
      WordR main (PP σ) (fun vs => vs = head ++ tail)
        (fun _ out => out = σ.map (fun i => head.getD i .nil) ++ tail)
        (fun _ => Kr * (n + 1) * (n + 1) * (((head.map vsz).sum) + 1)))
    (σ : List ℕ) (head tail : List Val) (n C : ℕ) (hn : head.length = n) (hσ : σ.length = n)
    (hpm : σ.Perm (List.range n))
    (hC : Kr * (n + 1) * (n + 1) * ((head.map vsz).sum + 1) ≤ C) :
    Work.ConvR.WordC main (PP σ) (fun vs => vs = head ++ tail)
      (fun _ out => out = σ.map (fun i => head.getD i .nil) ++ tail) C :=
  wc_ofWordR (hperm n σ head tail hn hσ hpm) (fun _ _ => hC)

/-! ## Size and arithmetic lemmas -/

theorem cost_mul_le {Klib stuff B X : ℕ} (hK : 60 * Klib ≤ B) (hs : stuff ≤ 60 * X) :
    Klib * stuff ≤ B * X := by
  calc Klib * stuff ≤ Klib * (60 * X) := Nat.mul_le_mul_left Klib hs
    _ = (60 * Klib) * X := by ring
    _ ≤ B * X := Nat.mul_le_mul_right X hK

theorem sum_map_le_const {α : Type} {l : List α} {g : α → ℕ} {L : ℕ}
    (h : ∀ x ∈ l, g x ≤ L) : (l.map g).sum ≤ l.length * L := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, List.length_cons]
    have h0 : g a ≤ L := h a (by simp)
    have h1 : ∀ x ∈ l, g x ≤ L := fun x hx => h x (by simp [hx])
    calc g a + (l.map g).sum ≤ L + l.length * L := Nat.add_le_add h0 (ih h1)
      _ = (l.length + 1) * L := by ring

theorem sum_map_le_of_mem {l : List ℤ} {L : ℕ} (h : ∀ x ∈ l, isz x ≤ L) :
    (l.map isz).sum ≤ l.length * L := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, List.length_cons]
    have h0 : isz a ≤ L := h a (by simp)
    have h1 : ∀ x ∈ l, isz x ≤ L := fun x hx => h x (by simp [hx])
    calc isz a + (l.map isz).sum ≤ L + l.length * L := Nat.add_le_add h0 (ih h1)
      _ = (l.length + 1) * L := by ring

theorem vsz_intList_le' {A : List ℕ} {r p : ℕ} (hlen : A.length = 2 * r)
    (hb : ∀ m, m < 2 * r → A.getD m 0 < 2 ^ (3 * p)) :
    vsz (intList A) ≤ 8 * ((r + 1) * (p + 1) ^ 2) := by
  have h1 : ∀ t ∈ A, t.size ≤ 3 * p := by
    intro t ht
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ht
    have hlt : A[i] < 2 ^ (3 * p) := by
      rw [← List.getD_eq_getElem A 0 hi]
      exact hb i (by omega)
    exact Nat.size_le.mpr hlt
  have h2 : (A.map (fun t => t.size + 3)).sum ≤ A.length * (3 * p + 3) := by
    calc (A.map (fun t => t.size + 3)).sum ≤ (A.map (fun _ => 3 * p + 3)).sum := by
          apply List.sum_le_sum
          intro t ht
          have := h1 t ht
          omega
      _ = A.length * (3 * p + 3) := Work.ConvR.sum_map_const A (3 * p + 3)
  have h3 := Work.ConvR.vsz_intList_le A
  have h4 : A.length * (3 * p + 3) + A.length + 2 ≤ 8 * ((r + 1) * (p + 1) ^ 2) := by
    rw [hlen]
    have hp1 : (p : ℕ) + 1 ≤ (p + 1) ^ 2 := by
      calc p + 1 ≤ (p + 1) * (p + 1) := Nat.le_mul_self _
        _ = (p + 1) ^ 2 := by ring
    have h5 : 2 * r * (3 * p + 3) = 6 * (r * (p + 1)) := by ring
    have h6 : 6 * (r * (p + 1)) ≤ 6 * ((r + 1) * (p + 1)) :=
      Nat.mul_le_mul_left 6 (Nat.mul_le_mul (Nat.le_succ r) (le_refl (p + 1)))
    have h7 : 6 * ((r + 1) * (p + 1)) ≤ 6 * ((r + 1) * (p + 1) ^ 2) :=
      Nat.mul_le_mul_left 6 (Nat.mul_le_mul_left (r + 1) hp1)
    have h9 : 1 ≤ (p + 1) ^ 2 := by
      calc 1 ≤ p + 1 := Nat.succ_le_succ (Nat.zero_le p)
        _ ≤ (p + 1) * (p + 1) := Nat.le_mul_self _
        _ = (p + 1) ^ 2 := by ring
    have h10 : r + 1 ≤ (r + 1) * (p + 1) ^ 2 := by
      calc r + 1 = (r + 1) * 1 := (Nat.mul_one _).symm
        _ ≤ (r + 1) * (p + 1) ^ 2 := Nat.mul_le_mul_left _ h9
    have h8 : 2 * r + 2 ≤ 2 * ((r + 1) * (p + 1) ^ 2) := by
      calc 2 * r + 2 = 2 * (r + 1) := by ring
        _ ≤ 2 * ((r + 1) * (p + 1) ^ 2) := Nat.mul_le_mul_left 2 h10
    linarith
  linarith

theorem isz_natCast_le (n : ℕ) : isz (n : ℤ) ≤ n + 2 := by
  have h : n.size ≤ n := Nat.size_le.mpr (Nat.lt_two_pow_self (n := n))
  simp only [isz, Int.natAbs_natCast]
  omega

theorem zsVal_sz_le {l : List ℤ} {r p : ℕ} (hlen : l.length = r)
    (h : ∀ x ∈ l, x.natAbs ≤ 2 ^ (3 * p + 1)) :
    vsz (zsVal l) ≤ 5 * ((r + 1) * (p + 1) ^ 2) := by
  have h1 : ∀ x ∈ l, isz x ≤ 3 * p + 4 := by
    intro x hx
    have hx' := h x hx
    have h2 := Work.ConvR.isz_le_of_natAbs_le (p := 3 * p + 1) hx'
    omega
  have h2 := vsz_zsVal_le (L := 3 * p + 4) h1
  rw [hlen] at h2
  have h3 : r * (3 * p + 4) + r + 1 ≤ 5 * ((r + 1) * (p + 1) ^ 2) := by
    have hp1 : (p : ℕ) + 1 ≤ (p + 1) ^ 2 := by
      calc p + 1 ≤ (p + 1) * (p + 1) := Nat.le_mul_self _
        _ = (p + 1) ^ 2 := by ring
    have h5 : r * (3 * p + 4) ≤ 4 * (r * (p + 1)) := by
      calc r * (3 * p + 4) = r * (3 * p) + 4 * r := by ring
        _ ≤ r * (4 * p) + 4 * r := Nat.add_le_add_right (Nat.mul_le_mul_left r (by omega)) _
        _ = 4 * (r * (p + 1)) := by ring
    have h6 : 4 * (r * (p + 1)) ≤ 4 * ((r + 1) * (p + 1)) :=
      Nat.mul_le_mul_left 4 (Nat.mul_le_mul (Nat.le_succ r) (le_refl (p + 1)))
    have h7 : 4 * ((r + 1) * (p + 1)) ≤ 4 * ((r + 1) * (p + 1) ^ 2) :=
      Nat.mul_le_mul_left 4 (Nat.mul_le_mul_left (r + 1) hp1)
    have h9 : 1 ≤ (p + 1) ^ 2 := by
      calc 1 ≤ p + 1 := Nat.succ_le_succ (Nat.zero_le p)
        _ ≤ (p + 1) * (p + 1) := Nat.le_mul_self _
        _ = (p + 1) ^ 2 := by ring
    have h10 : r + 1 ≤ (r + 1) * (p + 1) ^ 2 := by
      calc r + 1 = (r + 1) * 1 := (Nat.mul_one _).symm
        _ ≤ (r + 1) * (p + 1) ^ 2 := Nat.mul_le_mul_left _ h9
    linarith
  linarith

theorem cvecVal_sz_le {w : List (ℤ × ℤ)} {r p : ℕ} (hlen : w.length = r)
    (h : ∀ z ∈ w, z.1.natAbs ≤ 2 ^ (3 * p + 1) ∧ z.2.natAbs ≤ 2 ^ (3 * p + 1)) :
    vsz (cvecVal w) ≤ 12 * ((r + 1) * (p + 1) ^ 2) := by
  have h1 : ∀ z ∈ w, vsz (cfxVal z) ≤ 10 * (p + 1) := by
    intro z hz
    obtain ⟨ha, hb⟩ := h z hz
    have h2 : isz z.1 ≤ 3 * p + 4 := by
      have := Work.ConvR.isz_le_of_natAbs_le (p := 3 * p + 1) ha
      omega
    have h3 : isz z.2 ≤ 3 * p + 4 := by
      have := Work.ConvR.isz_le_of_natAbs_le (p := 3 * p + 1) hb
      omega
    rw [show cfxVal z = Val.cons (.int z.1) (.int z.2) from rfl, Work.ConvR.vsz_cons,
      Work.ConvR.vsz_int, Work.ConvR.vsz_int]
    omega
  have h4 : ((w.map cfxVal).map vsz).sum ≤ w.length * (10 * (p + 1)) := by
    rw [List.map_map]
    refine sum_map_le_const ?_
    intro z hz
    exact h1 z hz
  rw [show cvecVal w = ofList (w.map cfxVal) from rfl, Work.ConvR.vsz_ofList, List.length_map]
  rw [hlen] at h4 ⊢
  have h9 : 1 ≤ (p + 1) ^ 2 := by
    calc 1 ≤ p + 1 := Nat.succ_le_succ (Nat.zero_le p)
      _ ≤ (p + 1) * (p + 1) := Nat.le_mul_self _
      _ = (p + 1) ^ 2 := by ring
  have h10 : r + 1 ≤ (r + 1) * (p + 1) ^ 2 := by
    calc r + 1 = (r + 1) * 1 := (Nat.mul_one _).symm
      _ ≤ (r + 1) * (p + 1) ^ 2 := Nat.mul_le_mul_left _ h9
  have h11 : 10 * (r * (p + 1)) ≤ 10 * ((r + 1) * (p + 1)) :=
    Nat.mul_le_mul_left 10 (Nat.mul_le_mul (Nat.le_succ r) (le_refl (p + 1)))
  have h12 : 10 * ((r + 1) * (p + 1)) ≤ 10 * ((r + 1) * (p + 1) ^ 2) :=
    Nat.mul_le_mul_left 10 (Nat.mul_le_mul_left (r + 1) (by
      calc p + 1 ≤ (p + 1) * (p + 1) := Nat.le_mul_self _
        _ = (p + 1) ^ 2 := by ring))
  have h13 : r + 1 ≤ (r + 1) * (p + 1) ^ 2 := h10
  linarith


/-! ## `ℤ`/`ℕ` and list lemmas -/

theorem natAbs_sum_le_map' (l : List ℤ) : l.sum.natAbs ≤ (l.map Int.natAbs).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have h : (a + l.sum).natAbs ≤ a.natAbs + l.sum.natAbs := Int.natAbs_add_le a l.sum
    simpa using le_trans h (Nat.add_le_add_left ih _)

theorem digitOffset_natAbs_le' (p N : ℕ) (hp : 1 ≤ p) :
    (digitOffset p N).natAbs ≤ N * 2 ^ (3 * p * N) := by
  have h1 : ∀ m ∈ List.range N,
      ((2 : ℤ) ^ (3 * p - 1) * (2 : ℤ) ^ (3 * p * m)).natAbs ≤ 2 ^ (3 * p * N) := by
    intro m hm
    rw [List.mem_range] at hm
    rw [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_pow]
    norm_num
    rw [← pow_add]
    apply Nat.pow_le_pow_right (by norm_num)
    have hm1 : m + 1 ≤ N := hm
    have h3 : 3 * p * (m + 1) ≤ 3 * p * N := Nat.mul_le_mul_left _ hm1
    have hr : 3 * p * (m + 1) = 3 * p * m + 3 * p := by ring
    omega
  have h2 : (digitOffset p N).natAbs
      ≤ ((List.range N).map (fun _ => 2 ^ (3 * p * N))).sum := by
    unfold digitOffset
    have h3 := natAbs_sum_le_map'
      ((List.range N).map (fun m => (2 : ℤ) ^ (3 * p - 1) * (2 : ℤ) ^ (3 * p * m)))
    rw [List.map_map] at h3
    simp only [Function.comp_def] at h3
    refine le_trans h3 ?_
    apply List.sum_le_sum
    intro m hm
    exact h1 m hm
  refine le_trans h2 ?_
  rw [Work.ConvR.sum_map_const]
  simp

theorem isz_digitOffset_le' (p N : ℕ) (hp : 1 ≤ p) :
    isz (digitOffset p N) ≤ 3 * p * N + N.size + 4 := by
  have h1 := digitOffset_natAbs_le' p N hp
  have h2 : (N * 2 ^ (3 * p * N)).size ≤ 3 * p * N + N.size + 1 := by
    apply Nat.size_le.mpr
    have hN : N < 2 ^ N.size := Nat.lt_size_self N
    have h2a : N * 2 ^ (3 * p * N) < 2 ^ N.size * 2 ^ (3 * p * N) :=
      Nat.mul_lt_mul_of_pos_right hN (by positivity)
    rw [← pow_add] at h2a
    have h2b : 2 ^ (N.size + 3 * p * N) < 2 ^ (3 * p * N + N.size + 1) := by
      apply Nat.pow_lt_pow_right (by norm_num)
      omega
    exact lt_trans h2a h2b
  have h3 : (digitOffset p N).natAbs.size ≤ 3 * p * N + N.size + 1 :=
    le_trans (Nat.size_le_size h1) h2
  simp only [isz]
  omega

theorem int_natAbs_pow2 (k : ℕ) : (((2 : ℤ) ^ k).natAbs) = 2 ^ k := by
  rw [Int.natAbs_pow]
  norm_num

theorem int_tdiv_eq_zero_of_natAbs_lt {a b : ℤ} (hb : b ≠ 0) (h : a.natAbs < b.natAbs) :
    a.tdiv b = 0 := by
  have h1 : (a.tdiv b).natAbs = 0 := by
    rw [Int.natAbs_tdiv]
    exact Nat.div_eq_of_lt h
  rwa [Int.natAbs_eq_zero] at h1

theorem tdivCap (p r : ℕ) (a : ℤ) (ha : a.natAbs ≤ 2 ^ (3 * p + 1)) :
    Int.tdiv a ((2 : ℤ) ^ (min (p + Nat.clog 2 r) (3 * p + 3))) =
      Int.tdiv a ((2 : ℤ) ^ (p + Nat.clog 2 r)) := by
  rcases le_total (p + Nat.clog 2 r) (3 * p + 3) with h | h
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right h]
    have ha1 : a.natAbs < 2 ^ (3 * p + 3) := by
      have h2 : (2:ℕ) ^ (3 * p + 1) < 2 ^ (3 * p + 3) :=
        Nat.pow_lt_pow_right (by norm_num) (by omega)
      omega
    have ha2 : a.natAbs < 2 ^ (p + Nat.clog 2 r) := by
      have h2 : (2:ℕ) ^ (3 * p + 3) ≤ 2 ^ (p + Nat.clog 2 r) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    rw [int_tdiv_eq_zero_of_natAbs_lt (a := a) (b := (2 : ℤ) ^ (3 * p + 3))
        (by positivity) (by rwa [int_natAbs_pow2]),
      int_tdiv_eq_zero_of_natAbs_lt (a := a) (b := (2 : ℤ) ^ (p + Nat.clog 2 r))
        (by positivity) (by rwa [int_natAbs_pow2])]

theorem minSubMax (a b : ℤ) : min a b = a - max (a - b) 0 := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, max_eq_right (by omega : a - b ≤ 0), sub_zero]
  · rw [min_eq_right h, max_eq_left (by omega : (0:ℤ) ≤ a - b)]
    ring

theorem minCast (u v : ℕ) : min ((u : ℤ)) ((v : ℤ)) = ((min u v : ℕ) : ℤ) := by
  rcases le_total u v with h | h
  · rw [Nat.min_eq_left h, min_eq_left (by exact_mod_cast h)]
  · rw [Nat.min_eq_right h, min_eq_right (by exact_mod_cast h)]

theorem mem_zipWith' {α β γ : Type} {f : α → β → γ} {l₁ : List α} {l₂ : List β} {c : γ}
    (h : c ∈ l₁.zipWith f l₂) : ∃ a b, a ∈ l₁ ∧ b ∈ l₂ ∧ f a b = c := by
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp h
  have hi1 : i < l₁.length := by
    have h2 := hi; rw [List.length_zipWith] at h2
    exact lt_of_lt_of_le h2 (Nat.min_le_left _ _)
  have hi2 : i < l₂.length := by
    have h2 := hi; rw [List.length_zipWith] at h2
    exact lt_of_lt_of_le h2 (Nat.min_le_right _ _)
  exact ⟨l₁[i], l₂[i], List.getElem_mem hi1, List.getElem_mem hi2, by rw [← hget, List.getElem_zipWith]⟩

theorem getD_map_int {l : List ℤ} {i : ℕ} (h : i < l.length) :
    (l.map Val.int).getD i .nil = Val.int (l.getD i 0) := by
  rw [List.getD_eq_getElem _ _ (by simpa using h), List.getD_eq_getElem _ _ h, List.getElem_map]

theorem eq_of_getD {l₁ l₂ : List Val} (hlen : l₁.length = l₂.length)
    (h : ∀ i, l₁.getD i .nil = l₂.getD i .nil) : l₁ = l₂ := by
  apply List.ext_getElem hlen
  intro i h1 h2
  rw [← List.getD_eq_getElem l₁ .nil h1, ← List.getD_eq_getElem l₂ .nil h2]
  exact h i

theorem zipWith_int_eq {l₁ l₂ : List ℤ} {zs : List Val} {f : ℤ → ℤ → ℤ}
    (hlen : l₁.length = l₂.length) (hlen2 : zs.length = l₁.length)
    (h : ∀ i, i < l₁.length → zs.getD i .nil = Val.int (f (l₁.getD i 0) (l₂.getD i 0))) :
    zs = (l₁.zipWith f l₂).map Val.int := by
  apply List.ext_getElem
  · rw [hlen2, List.length_map, List.length_zipWith, hlen, min_self]
  · intro i h1 h2
    have hi1 : i < l₁.length := by rw [hlen2] at h1; exact h1
    have hzip : i < (l₁.zipWith f l₂).length := by
      rw [List.length_zipWith, ← hlen, min_self]; exact hi1
    have lhs : zs[i] = Val.int (f (l₁.getD i 0) (l₂.getD i 0)) := by
      rw [← List.getD_eq_getElem zs .nil h1]
      exact h i hi1
    rw [lhs, List.getElem_map, List.getElem_zipWith (h := hzip)]
    have hi2' : i < l₂.length := by rw [← hlen]; exact hi1
    show Val.int (f (l₁.getD i 0) (l₂.getD i 0)) = Val.int (f l₁[i] l₂[i])
    rw [List.getD_eq_getElem l₁ 0 hi1, List.getD_eq_getElem l₂ 0 hi2']

theorem zipWith_pair_eq {l₁ l₂ : List ℤ} {D : ℤ} {zs : List Val}
    (hlen : l₁.length = l₂.length) (hlen2 : zs.length = l₁.length)
    (h : ∀ i, i < l₁.length →
      zs.getD i .nil = cfxVal (Int.tdiv (l₁.getD i 0) D, Int.tdiv (l₂.getD i 0) D)) :
    zs = (l₁.zipWith (fun a b => (Int.tdiv a D, Int.tdiv b D)) l₂).map cfxVal := by
  apply List.ext_getElem
  · rw [hlen2, List.length_map, List.length_zipWith, hlen, min_self]
  · intro i h1 h2
    have hi1 : i < l₁.length := by rw [hlen2] at h1; exact h1
    have hzip : i < (l₁.zipWith (fun a b => (Int.tdiv a D, Int.tdiv b D)) l₂).length := by
      rw [List.length_zipWith, ← hlen, min_self]; exact hi1
    have lhs : zs[i] = cfxVal (Int.tdiv (l₁.getD i 0) D, Int.tdiv (l₂.getD i 0) D) := by
      rw [← List.getD_eq_getElem zs .nil h1]
      exact h i hi1
    rw [lhs, List.getElem_map, List.getElem_zipWith (h := hzip)]
    show cfxVal (Int.tdiv (l₁.getD i 0) D, Int.tdiv (l₂.getD i 0) D) =
      cfxVal (Int.tdiv l₁[i] D, Int.tdiv l₂[i] D)
    rw [List.getD_eq_getElem l₁ 0 hi1, List.getD_eq_getElem l₂ 0 (by have h := hi1; rw [hlen] at h; exact h)]

theorem int_natAbs_sub_le_of_lt {m n L : ℕ} (h1 : m < 2 ^ L) (h2 : n < 2 ^ L) :
    (((m : ℤ) - (n : ℤ)).natAbs) ≤ 2 ^ L := by
  rcases le_total m n with h | h
  · have he : (m : ℤ) - (n : ℤ) = -(((n - m : ℕ)) : ℤ) := by
      rw [Nat.cast_sub h]; ring
    rw [he, Int.natAbs_neg, Int.natAbs_natCast]
    omega
  · have he : (m : ℤ) - (n : ℤ) = ((m - n : ℕ) : ℤ) := by
      rw [Nat.cast_sub h]
    rw [he, Int.natAbs_natCast]
    omega

theorem int_natAbs_sub_le' {a b : ℤ} {L : ℕ} (h1 : a.natAbs ≤ 2 ^ L) (h2 : b.natAbs ≤ 2 ^ L) :
    (a - b).natAbs ≤ 2 ^ (L + 1) := by
  have h := Int.natAbs_sub_le a b
  have h3 : (2:ℕ) ^ L + 2 ^ L = 2 ^ (L + 1) := by rw [pow_succ]; ring
  omega

theorem int_natAbs_add_le' {a b : ℤ} {L : ℕ} (h1 : a.natAbs ≤ 2 ^ L) (h2 : b.natAbs ≤ 2 ^ L) :
    (a + b).natAbs ≤ 2 ^ (L + 1) := by
  have h := Int.natAbs_add_le a b
  have h3 : (2:ℕ) ^ L + 2 ^ L = 2 ^ (L + 1) := by rw [pow_succ]; ring
  omega

theorem deltaL_mem_bound {A : List ℕ} {r p : ℕ}
    (hb : ∀ m, m < A.length → A.getD m 0 < 2 ^ (3 * p)) :
    ∀ x ∈ deltaL A r, x.natAbs ≤ 2 ^ (3 * p) := by
  intro x hx
  obtain ⟨i, hi, hxi⟩ := List.mem_iff_getElem.mp hx
  rw [← hxi, ← List.getD_eq_getElem _ _ hi]
  have hlen : (deltaL A r).length = min r (A.length - r) := deltaL_length A r
  have hi2 : i < min r (A.length - r) := by rwa [hlen] at hi
  have hir : i < r := lt_of_lt_of_le hi2 (Nat.min_le_left _ _)
  have hiar : i + r < A.length := by
    have := lt_of_lt_of_le hi2 (Nat.min_le_right _ _); omega
  have hiA : i < A.length := by omega
  have h1 : A.getD i 0 < 2 ^ (3 * p) := hb i hiA
  have h2 : A.getD (i + r) 0 < 2 ^ (3 * p) := hb (i + r) hiar
  have hzw : i < (List.take r (toZl A) |>.zipWith (· - ·) (List.drop r (toZl A))).length := by
    rw [List.length_zipWith, List.length_take, List.length_drop, toZl_length]
    omega
  rw [show (deltaL A r) = (List.take r (toZl A)).zipWith (· - ·) (List.drop r (toZl A)) from rfl,
    getD_zipWith_eq _ _ i hzw]
  have ht : i < ((toZl A).take r).length := by rw [List.length_take, toZl_length]; omega
  have hd : i < ((toZl A).drop r).length := by rw [List.length_drop, toZl_length]; omega
  rw [getD_take_eq ht, getD_drop_eq hd, toZl_getD hiA, toZl_getD hiar]
  exact int_natAbs_sub_le_of_lt h1 h2

theorem D0L_length (A00 A11 : List ℕ) (r : ℕ) :
    (D0L r A00 A11).length = min (min r (A00.length - r)) (min r (A11.length - r)) := by
  rw [D0L, zsubL, List.length_zipWith, deltaL_length, deltaL_length]

theorem D1L_length (A01 A10 : List ℕ) (r : ℕ) :
    (D1L r A01 A10).length = min (min r (A01.length - r)) (min r (A10.length - r)) := by
  rw [D1L, zaddL, List.length_zipWith, deltaL_length, deltaL_length]

theorem D0L_mem_bound {A00 A11 : List ℕ} {r p : ℕ}
    (h00 : ∀ x ∈ deltaL A00 r, x.natAbs ≤ 2 ^ (3 * p))
    (h11 : ∀ x ∈ deltaL A11 r, x.natAbs ≤ 2 ^ (3 * p)) :
    ∀ x ∈ D0L r A00 A11, x.natAbs ≤ 2 ^ (3 * p + 1) := by
  intro x hx
  rw [D0L, zsubL] at hx
  obtain ⟨a, b, ha, hb, rfl⟩ := mem_zipWith' hx
  have := int_natAbs_sub_le' (h00 a ha) (h11 b hb)
  rwa [show 3 * p + 1 = 3 * p + 1 from rfl]

theorem D1L_mem_bound {A01 A10 : List ℕ} {r p : ℕ}
    (h01 : ∀ x ∈ deltaL A01 r, x.natAbs ≤ 2 ^ (3 * p))
    (h10 : ∀ x ∈ deltaL A10 r, x.natAbs ≤ 2 ^ (3 * p)) :
    ∀ x ∈ D1L r A01 A10, x.natAbs ≤ 2 ^ (3 * p + 1) := by
  intro x hx
  rw [D1L, zaddL] at hx
  obtain ⟨a, b, ha, hb, rfl⟩ := mem_zipWith' hx
  have := int_natAbs_add_le' (h01 a ha) (h10 b hb)
  rwa [show 3 * p + 1 = 3 * p + 1 from rfl]

theorem kronW_length (p r : ℕ) (A00 A01 A10 A11 : List ℕ) :
    (kronW p r A00 A01 A10 A11).length = min (D0L r A00 A11).length (D1L r A01 A10).length := by
  rw [kronW, List.length_zipWith]

theorem kronW_mem_bound {A00 A01 A10 A11 : List ℕ} {r p : ℕ}
    (h0 : ∀ x ∈ D0L r A00 A11, x.natAbs ≤ 2 ^ (3 * p + 1))
    (h1 : ∀ x ∈ D1L r A01 A10, x.natAbs ≤ 2 ^ (3 * p + 1)) :
    ∀ z ∈ kronW p r A00 A01 A10 A11,
      z.1.natAbs ≤ 2 ^ (3 * p + 1) ∧ z.2.natAbs ≤ 2 ^ (3 * p + 1) := by
  intro z hz
  rw [kronW] at hz
  obtain ⟨a, b, ha, hb, hf⟩ := mem_zipWith' hz
  rw [← hf]
  refine ⟨?_, ?_⟩
  · rw [Int.natAbs_tdiv]
    exact le_trans (Nat.div_le_self _ _) (h0 a ha)
  · rw [Int.natAbs_tdiv]
    exact le_trans (Nat.div_le_self _ _) (h1 b hb)

theorem intList_injective : Function.Injective intList := by
  intro l
  induction l with
  | nil =>
    intro m h
    cases m with
    | nil => rfl
    | cons y ys => simp [intList, ofList] at h
  | cons x xs ih =>
    intro m h
    cases m with
    | nil => simp [intList, ofList] at h
    | cons y ys =>
      have h' : (x : ℤ) = (y : ℤ) ∧ intList xs = intList ys := by
        simpa [intList, ofList, Val.cons.injEq] using h
      rw [Int.natCast_inj.mp h'.1, ih h'.2]

theorem forall₂_unique {α β : Type} {R : α → β → Prop}
    (hR : ∀ a b b', R a b → R a b' → b = b') :
    ∀ {l : List α} {m m' : List β}, List.Forall₂ R l m → List.Forall₂ R l m' → m = m' := by
  intro l
  induction l with
  | nil =>
    intro m m' h1 h2
    cases h1
    cases h2
    rfl
  | cons a l ih =>
    intro m m' h1 h2
    cases h1 with
    | cons hab h1' =>
      cases h2 with
      | cons hab' h2' =>
        rw [hR a _ _ hab hab', ih h1' h2']

theorem forall₂_four {α β : Type} {R : α → β → Prop} {a1 a2 a3 a4 : α} {m : List β}
    (h : List.Forall₂ R [a1, a2, a3, a4] m) :
    ∃ b1 b2 b3 b4, m = [b1, b2, b3, b4] ∧ R a1 b1 ∧ R a2 b2 ∧ R a3 b3 ∧ R a4 b4 := by
  cases h with
  | cons h1 h =>
    cases h with
    | cons h2 h =>
      cases h with
      | cons h3 h =>
        cases h with
        | cons h4 h =>
          cases h
          exact ⟨_, _, _, _, rfl, h1, h2, h3, h4⟩

theorem Xfacts (r p : ℕ) :
    1 ≤ (r + 1) * (p + 1) ^ 2 ∧ r ≤ (r + 1) * (p + 1) ^ 2 ∧
    p ≤ (r + 1) * (p + 1) ^ 2 ∧ r * p ≤ (r + 1) * (p + 1) ^ 2 ∧
    r + 1 ≤ (r + 1) * (p + 1) ^ 2 ∧ p + 1 ≤ (r + 1) * (p + 1) ^ 2 ∧
    (p + 1) ^ 2 ≤ (r + 1) * (p + 1) ^ 2 ∧ (r + 1) * (p + 1) ≤ (r + 1) * (p + 1) ^ 2 ∧
    r * (3 * p + 5) ≤ 10 * ((r + 1) * (p + 1) ^ 2) := by
  have hp2 : (p:ℕ) + 1 ≤ (p + 1) ^ 2 := by
    calc p + 1 ≤ (p + 1) * (p + 1) := Nat.le_mul_self _
      _ = (p + 1) ^ 2 := by ring
  have h1 : 1 ≤ (p + 1) ^ 2 := le_trans (Nat.succ_le_succ (Nat.zero_le p)) hp2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith [Nat.zero_le r, Nat.zero_le p, hp2, h1]


/-! ## extra word helpers -/

theorem wc_dup {main : Cmd} {dupP : Cmd} {DupK : ℕ}
    (hdup : WordR main dupP (fun vs => vs ≠ [])
      (fun vs out => ∃ v rest, vs = v :: rest ∧ out = v :: v :: rest)
      (fun vs => DupK * (vsz (vs.headD .nil) + 1)))
    (a : Val) (W : List Val) (C : ℕ) (hC : DupK * (vsz a + 1) ≤ C) :
    Work.ConvR.WordC main dupP (fun vs => vs = a :: W) (fun _ out => out = a :: a :: W) C := by
  intro vs hvs s R hR
  have hne : a :: W ≠ ([] : List Val) := by simp
  obtain ⟨out, s', n, hQ, he, hn, hstk, hoth⟩ := hdup (a :: W) hne s R (by rw [hR, hvs])
  obtain ⟨v', rest, hv', hout⟩ := hQ
  obtain ⟨h1, h2⟩ := (List.cons.injEq _ _ _ _).mp hv'
  have hout' : out = a :: a :: W := by rw [hout, ← h1, ← h2]
  refine ⟨out, s', n, hout', he, ?_, hstk, hoth⟩
  refine le_trans hn ?_
  show DupK * (vsz ((a :: W).headD .nil) + 1) ≤ C
  have ht : vsz ((a :: W).headD .nil) + 1 = vsz a + 1 := by simp
  rw [ht]; exact hC

theorem wc_bin {main : Cmd} {qP : Cmd} {QK : ℕ} {f : ℤ → ℤ → ℤ} {P : ℤ → ℤ → Prop}
    (hq : BinOp main qP P f (fun a b => QK * (isz a + isz b)))
    {x y : ℤ} (hP : P x y) (W : List Val) (C : ℕ) (hC : QK * (isz x + isz y) ≤ C) :
    Work.ConvR.WordC main qP (fun vs => vs = Val.int x :: Val.int y :: W)
      (fun _ out => out = Val.int (f x y) :: W) C := by
  intro vs hvs s R hR
  obtain ⟨out, s', n, hQ, he, hn, hstk, hoth⟩ :=
    hq (Val.int x :: Val.int y :: W) ⟨x, y, W, rfl, hP⟩ s R (by rw [hR, hvs])
  obtain ⟨a', b', rest, hv, hout⟩ := hQ
  obtain ⟨e1, e2⟩ := (List.cons.injEq _ _ _ _).mp hv
  obtain ⟨e3, e4⟩ := (List.cons.injEq _ _ _ _).mp e2
  have ha : a' = x := ((Val.int.injEq x a').mp e1).symm
  have hb : b' = y := ((Val.int.injEq y b').mp e3).symm
  refine ⟨out, s', n, ?_, he, ?_, hstk, hoth⟩
  · rw [hout, ha, hb, e4]
  · refine le_trans hn ?_
    show QK * (isz x + isz y) ≤ C
    exact hC

theorem wc_pushVal {main : Cmd} {pushP : Val → Cmd} {PUK : ℕ}
    (hpush : ∀ v : Val, WordR main (pushP v) (fun _ => True)
      (fun vs out => out = v :: vs) (fun _ => PUK * (vsz v + 1)))
    (v : Val) (W : List Val) (C : ℕ) (hC : PUK * (vsz v + 1) ≤ C) :
    Work.ConvR.WordC main (pushP v) (fun vs => vs = W) (fun _ out => out = v :: W) C := by
  refine wc_conseq' (wc_ofWordR (hpush v) (B := C) (fun _ _ => hC)) (fun _ _ => trivial)
    (fun vs out hvs h => by rw [h, hvs])

theorem wc_un {main : Cmd} {qP : Cmd} {f : ℤ → ℤ} {P : ℤ → Prop} {cost : ℤ → ℕ}
    (hq : UnOp main qP P f cost) {x : ℤ} (hP : P x) (W : List Val) (C : ℕ)
    (hC : cost x ≤ C) :
    Work.ConvR.WordC main qP (fun vs => vs = Val.int x :: W)
      (fun _ out => out = Val.int (f x) :: W) C := by
  intro vs hvs s R hR
  obtain ⟨out, s', n, hQ, he, hn, hstk, hoth⟩ :=
    hq (Val.int x :: W) ⟨x, W, rfl, hP⟩ s R (by rw [hR, hvs])
  obtain ⟨a', rest, hv, hout⟩ := hQ
  obtain ⟨e1, e2⟩ := (List.cons.injEq _ _ _ _).mp hv
  have ha : a' = x := ((Val.int.injEq x a').mp e1).symm
  refine ⟨out, s', n, ?_, he, ?_, hstk, hoth⟩
  · rw [hout, ha, e2]
  · refine le_trans hn ?_
    show cost x ≤ C
    exact hC

theorem intList_eq_map (A : List ℕ) : intList A = ofList (List.map Val.int (toZl A)) := by
  induction A with
  | nil => rfl
  | cons a as ih =>
    show Val.cons (Val.int (a : ℤ)) (intList as) =
      Val.cons (Val.int (a : ℤ)) (ofList (List.map Val.int (toZl as)))
    rw [ih]

theorem isz_tdiv_le (a b : ℤ) : isz (a.tdiv b) ≤ isz a := by
  have h : (a.tdiv b).natAbs ≤ a.natAbs := by
    rw [Int.natAbs_tdiv]; exact Nat.div_le_self _ _
  have h2 := Nat.size_le_size h
  simp only [isz]; omega

theorem size_add_le (x y : ℕ) : (x + y).size ≤ x.size + y.size + 1 := by
  apply Nat.size_le.mpr
  calc x + y < 2 ^ x.size + 2 ^ y.size := Nat.add_lt_add (Nat.lt_size_self x) (Nat.lt_size_self y)
    _ ≤ 2 ^ (x.size + y.size) + 2 ^ (x.size + y.size) := by
        apply Nat.add_le_add <;> apply Nat.pow_le_pow_right (by norm_num) <;> omega
    _ = 2 ^ (x.size + y.size + 1) := by rw [pow_succ]; ring

theorem isz_sub_le (a b : ℤ) : isz (a - b) ≤ isz a + isz b := by
  have h : (a - b).natAbs ≤ a.natAbs + b.natAbs := Int.natAbs_sub_le a b
  have h2 : (a.natAbs + b.natAbs).size ≤ a.natAbs.size + b.natAbs.size + 1 := size_add_le _ _
  have h3 : (a - b).natAbs.size ≤ a.natAbs.size + b.natAbs.size + 1 :=
    le_trans (Nat.size_le_size h) h2
  simp only [isz]; omega

theorem isz_max_zero_le (a : ℤ) : isz (max 0 a) ≤ isz a + 2 := by
  rcases le_total 0 a with h | h
  · rw [max_eq_right h]; omega
  · rw [max_eq_left h]
    have h0 : (0 : ℕ).size = 0 := by decide
    simp only [isz, Int.natAbs_zero, h0]
    omega

theorem clog2_le (r : ℕ) : Nat.clog 2 r ≤ r :=
  (Nat.clog_le_iff_le_pow (by norm_num)).mpr (Nat.lt_two_pow_self.le)

/-- per-element body of a `zipWith` over `Val.int`-lists -/
theorem zipBody {main : Cmd} {qP : Cmd} {QK : ℕ} {f : ℤ → ℤ → ℤ} {P : ℤ → ℤ → Prop}
    (rest : List Val) (hq : BinOp main qP P f (fun a b => QK * (isz a + isz b)))
    {c L : ℕ} (hc : QK * (2 * L) ≤ c)
    (hbd : ∀ a b, P a b → isz a ≤ L → isz b ≤ L → isz (f a b) ≤ L) :
    ∀ x y : Val, (∃ a b, x = Val.int a ∧ y = Val.int b ∧ P a b ∧ isz a ≤ L ∧ isz b ≤ L) →
      WordR main qP (fun vs => vs = x :: y :: rest)
        (fun _ out => ∃ z, out = z :: rest ∧
          (∃ a b, x = Val.int a ∧ y = Val.int b ∧ z = Val.int (f a b)) ∧ vsz z ≤ L)
        (fun _ => c) := by
  intro x y hxy
  obtain ⟨a0, b0, rfl, rfl, hP, hLa, hLb⟩ := hxy
  intro vs hvs s R hR
  obtain ⟨out, s', n, hQ, he, hn, hstk, hoth⟩ :=
    hq (Val.int a0 :: Val.int b0 :: rest) ⟨a0, b0, rest, rfl, hP⟩ s R (by rw [hR, hvs])
  obtain ⟨a', b', rest', hv, hout⟩ := hQ
  obtain ⟨e1, e2⟩ := (List.cons.injEq _ _ _ _).mp hv
  obtain ⟨e3, e4⟩ := (List.cons.injEq _ _ _ _).mp e2
  have ha : a' = a0 := ((Val.int.injEq a0 a').mp e1).symm
  have hb : b' = b0 := ((Val.int.injEq b0 b').mp e3).symm
  refine ⟨out, s', n, ⟨Val.int (f a0 b0), ?_, ?_, ?_⟩, he, ?_, hstk, hoth⟩
  · rw [hout, ha, hb, e4]
  · exact ⟨a0, b0, rfl, rfl, rfl⟩
  · rw [Work.ConvR.vsz_int]; exact hbd a0 b0 hP hLa hLb
  · refine le_trans hn ?_
    show QK * (isz a0 + isz b0) ≤ c
    exact le_trans (Nat.mul_le_mul_left QK (by omega)) hc

theorem isz_add_le (a b : ℤ) : isz (a + b) ≤ isz a + isz b := by
  have h : (a + b).natAbs ≤ a.natAbs + b.natAbs := Int.natAbs_add_le a b
  have h2 : (a.natAbs + b.natAbs).size ≤ a.natAbs.size + b.natAbs.size + 1 := size_add_le _ _
  have h3 : (a + b).natAbs.size ≤ a.natAbs.size + b.natAbs.size + 1 :=
    le_trans (Nat.size_le_size h) h2
  simp only [isz]; omega

theorem Xge (r p : ℕ) :
    1 ≤ (r + 1) * (p + 1) ^ 2 ∧ p ≤ (r + 1) * (p + 1) ^ 2 ∧
    r ≤ (r + 1) * (p + 1) ^ 2 ∧ p + 1 ≤ (r + 1) * (p + 1) ^ 2 ∧
    r + 1 ≤ (r + 1) * (p + 1) ^ 2 ∧ r * p ≤ (r + 1) * (p + 1) ^ 2 ∧
    (p + 1) ^ 2 ≤ (r + 1) * (p + 1) ^ 2 ∧ (r + 1) * (p + 1) ≤ (r + 1) * (p + 1) ^ 2 := by
  have hp2 : (p:ℕ) + 1 ≤ (p + 1) ^ 2 := by
    calc p + 1 ≤ (p + 1) * (p + 1) := Nat.le_mul_self _
      _ = (p + 1) ^ 2 := by ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith [Nat.zero_le r, Nat.zero_le p, hp2]

theorem small_isz (r p : ℕ) :
    isz (p : ℤ) ≤ 4 * ((r + 1) * (p + 1) ^ 2) ∧
    isz (r : ℤ) ≤ 4 * ((r + 1) * (p + 1) ^ 2) ∧
    isz (3 : ℤ) ≤ 8 * ((r + 1) * (p + 1) ^ 2) ∧
    isz (0 : ℤ) ≤ 8 * ((r + 1) * (p + 1) ^ 2) ∧
    isz ((3 * p : ℕ) : ℤ) ≤ 8 * ((r + 1) * (p + 1) ^ 2) ∧
    isz ((3 * p + 3 : ℕ) : ℤ) ≤ 8 * ((r + 1) * (p + 1) ^ 2) ∧
    isz ((Nat.clog 2 r : ℕ) : ℤ) ≤ 4 * ((r + 1) * (p + 1) ^ 2) ∧
    isz ((p : ℤ) + ((Nat.clog 2 r : ℕ) : ℤ)) ≤ 8 * ((r + 1) * (p + 1) ^ 2) := by
  obtain ⟨hX1, hpX, hrX, hp1X, hr1X, hrpX, hp2X, hrp1X⟩ := Xge r p
  have hp2 : isz (p : ℤ) ≤ p + 2 := isz_natCast_le p
  have hr2 : isz (r : ℤ) ≤ r + 2 := isz_natCast_le r
  have h3p : isz ((3 * p : ℕ) : ℤ) ≤ 3 * p + 2 := isz_natCast_le (3 * p)
  have h3p3 : isz ((3 * p + 3 : ℕ) : ℤ) ≤ 3 * p + 5 := by
    have := isz_natCast_le (3 * p + 3); omega
  have hcl : isz ((Nat.clog 2 r : ℕ) : ℤ) ≤ r + 2 := by
    have h := isz_natCast_le (Nat.clog 2 r)
    have h2 := clog2_le r
    omega
  have hsz3 : isz (3 : ℤ) ≤ 8 * ((r + 1) * (p + 1) ^ 2) := by
    have h2 : ((3 : ℤ).natAbs).size ≤ 2 := Nat.size_le.mpr (by norm_num)
    simp only [isz]
    omega
  have hsz0 : isz (0 : ℤ) ≤ 8 * ((r + 1) * (p + 1) ^ 2) := by
    have h2 : ((0 : ℤ).natAbs).size ≤ 2 := Nat.size_le.mpr (by norm_num)
    simp only [isz]
    omega
  have hadd : isz ((p : ℤ) + ((Nat.clog 2 r : ℕ) : ℤ)) ≤ isz (p:ℤ) + isz ((Nat.clog 2 r : ℕ):ℤ) :=
    isz_add_le _ _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-! ## helpers for the remaining words -/

theorem cast_mul_int (n p : ℕ) : (((n * p : ℕ)) : ℤ) = (n : ℤ) * (p : ℤ) := by
  push_cast; ring

theorem cast_add_int (n p : ℕ) : (((n + p : ℕ)) : ℤ) = (n : ℤ) + (p : ℤ) := by
  push_cast; ring

/-- cost bookkeeping for a word whose cost is `Klib * k * stuff` -/
theorem costStepL {Klib k stuff BIG X c : ℕ} (hstuff : k * stuff ≤ c * X) (hK : c * Klib ≤ BIG) :
    Klib * k * stuff ≤ BIG * X := by
  calc Klib * k * stuff = Klib * (k * stuff) := by ring
    _ ≤ Klib * (c * X) := Nat.mul_le_mul_left _ hstuff
    _ = (c * Klib) * X := by ring
    _ ≤ BIG * X := Nat.mul_le_mul_right _ hK

/-- cost weakening for a `WordC` with constant cost -/
theorem wc_cost_le {main : Cmd} {p : Cmd} {P : List Val → Prop} {Q : List Val → List Val → Prop}
    {C C' : ℕ} (h : Work.ConvR.WordC main p P Q C) (hC : C ≤ C') :
    Work.ConvR.WordC main p P Q C' := by
  intro vs hvs s R hR
  obtain ⟨out, s', n, hQ, he, hn, hstk, hoth⟩ := h vs hvs s R hR
  exact ⟨out, s', n, hQ, he, le_trans hn hC, hstk, hoth⟩

/-- `consV` on a fixed two-element prefix -/
theorem wc_consV {main : Cmd} {consP : Cmd} {CK : ℕ}
    (hcons : WordR main consP (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = .cons a b :: rest)
      (fun _ => CK))
    (a b : Val) (W : List Val) (C : ℕ) (hC : CK ≤ C) :
    Work.ConvR.WordC main consP (fun vs => vs = a :: b :: W)
      (fun _ out => out = .cons a b :: W) C := by
  intro vs hvs s R hR
  obtain ⟨out, s', n, hQ, he, hn, hstk, hoth⟩ := hcons (a :: b :: W) (by simp) s R (by rw [hR, hvs])
  obtain ⟨a', b', rest, hv', hout⟩ := hQ
  obtain ⟨h1, h2⟩ := (List.cons.injEq _ _ _ _).mp hv'
  obtain ⟨h3, h4⟩ := (List.cons.injEq _ _ _ _).mp h2
  refine ⟨out, s', n, ?_, he, le_trans hn hC, hstk, hoth⟩
  rw [hout, ← h1, ← h3, ← h4]

/-- strengthen the integer predicate of a `BinOp` -/
theorem binOp_ss {main : Cmd} {qP : Cmd} {f : ℤ → ℤ → ℤ} {C : ℤ → ℤ → ℕ} {P P' : ℤ → ℤ → Prop}
    (h : BinOp main qP P f C) (hPP : ∀ a b, P' a b → P a b) : BinOp main qP P' f C := by
  intro vs hvs s R hR
  obtain ⟨a, b, rest, hv, hP'⟩ := hvs
  obtain ⟨out, s', n, hQ, he, hn, hstk, hoth⟩ := h vs ⟨a, b, rest, hv, hPP a b hP'⟩ s R hR
  exact ⟨out, s', n, hQ, he, hn, hstk, hoth⟩

/-- schoolbook multiplication wrapper -/
theorem wc_mul {main : Cmd} {qP : Cmd} {QK : ℕ}
    (hq : BinOp main qP (fun _ _ => True) (· * ·) (fun a b => QK * isz a * isz b))
    (x y : ℤ) (W : List Val) (C : ℕ) (hC : QK * isz x * isz y ≤ C) :
    Work.ConvR.WordC main qP (fun vs => vs = Val.int x :: Val.int y :: W)
      (fun _ out => out = Val.int (x * y) :: W) C := by
  intro vs hvs s R hR
  obtain ⟨out, s', n, hQ, he, hn, hstk, hoth⟩ :=
    hq (Val.int x :: Val.int y :: W) ⟨x, y, W, rfl, trivial⟩ s R (by rw [hR, hvs])
  obtain ⟨a', b', rest, hv, hout⟩ := hQ
  obtain ⟨e1, e2⟩ := (List.cons.injEq _ _ _ _).mp hv
  obtain ⟨e3, e4⟩ := (List.cons.injEq _ _ _ _).mp e2
  have ha : a' = x := ((Val.int.injEq x a').mp e1).symm
  have hb : b' = y := ((Val.int.injEq y b').mp e3).symm
  refine ⟨out, s', n, ?_, he, ?_, hstk, hoth⟩
  · rw [hout, ha, hb, e4]
  · refine le_trans hn ?_
    show QK * isz x * isz y ≤ C
    exact hC

theorem vsz_ofList_take_le (l : List Val) (k : ℕ) : vsz (ofList (l.take k)) ≤ vsz (ofList l) := by
  rw [Work.ConvR.vsz_ofList, Work.ConvR.vsz_ofList, List.length_take]
  have h1 : ((l.take k).map vsz).sum ≤ (l.map vsz).sum := by
    have h := List.take_append_drop k l
    calc ((l.take k).map vsz).sum ≤ ((l.take k).map vsz).sum + ((l.drop k).map vsz).sum :=
          Nat.le_add_right _ _
      _ = (((l.take k) ++ (l.drop k)).map vsz).sum := by rw [List.map_append, List.sum_append]
      _ = (l.map vsz).sum := by rw [h]
  omega

theorem vsz_ofList_drop_le (l : List Val) (k : ℕ) : vsz (ofList (l.drop k)) ≤ vsz (ofList l) := by
  rw [Work.ConvR.vsz_ofList, Work.ConvR.vsz_ofList, List.length_drop]
  have h1 : ((l.drop k).map vsz).sum ≤ (l.map vsz).sum := by
    have h := List.take_append_drop k l
    calc ((l.drop k).map vsz).sum ≤ ((l.take k).map vsz).sum + ((l.drop k).map vsz).sum :=
          Nat.le_add_left _ _
      _ = (((l.take k) ++ (l.drop k)).map vsz).sum := by rw [List.map_append, List.sum_append]
      _ = (l.map vsz).sum := by rw [h]
  omega

theorem isz_natCast_le_three (n p : ℕ) (h : n < 2 ^ (3 * p)) : isz ((n : ℤ)) ≤ 3 * p + 3 := by
  have h1 : ((n : ℤ)).natAbs ≤ 2 ^ (3 * p) := by rw [Int.natAbs_natCast]; omega
  have h2 := Work.ConvR.isz_le_of_natAbs_le h1
  omega

/-! ## `shiftCapBody`: the capped shift exponent `min (p + κ) (3p + 3)` -/

theorem shiftCapBody (hK : HvdH.KernelLib) (hI : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p r : ℕ) (V : List HvdH.Val), 1 ≤ p →
      HvdH.WordR main prog (fun vs => vs = HvdH.Val.int (p : ℤ) :: HvdH.Val.int (r : ℤ) :: V)
        (fun _ out => out = HvdH.Val.int ((min (p + Nat.clog 2 r) (3 * p + 3) : ℕ) : ℤ) :: V)
        (fun _ => K * ((r + 1) * (p + 1) ^ 2)) := by
  obtain ⟨dupP, DupK, hdup⟩ := hK.dup
  obtain ⟨swapP, SWK, hswap⟩ := hK.swap
  obtain ⟨rollP, ROK, hroll⟩ := hK.roll
  obtain ⟨pushP, PUK, hpush⟩ := hK.pushVal
  obtain ⟨clP, CLK, hcl⟩ := hI.clog2
  obtain ⟨addP, ADK, hadd⟩ := hI.add
  obtain ⟨subP, SUK, hsub⟩ := hI.sub
  obtain ⟨mulP, MUK, hmul⟩ := hI.mulS
  obtain ⟨maxP, MAK, hmax⟩ := hI.max
  refine ⟨List.foldl (fun a b => Cmd.seq a b) Cmd.skip
    [dupP, pushP (.int 3), mulP, pushP (.int 3), addP, rollP 2, clP, rollP 2, addP, dupP,
      rollP 2, swapP, subP, pushP (.int 0), maxP, swapP, subP],
    17 * (100000 * (DupK + SWK + ROK + PUK + CLK + ADK + SUK + MUK + MAK + 1)) + 1, ?_⟩
  intro main p r V hp
  set BIG : ℕ := 100000 * (DupK + SWK + ROK + PUK + CLK + ADK + SUK + MUK + MAK + 1) with hBIG
  obtain ⟨hX1, hpX, hrX, hp1X, hr1X, hrpX, hp2X, hrp1X⟩ := Xge r p
  obtain ⟨hsp, hsr, hs3, hs0, hs3p, hs3p3, hscl, hspc⟩ := small_isz r p
  have hsz3c : isz (3 : ℤ) ≤ 4 := by
    have h2 : ((3 : ℤ).natAbs).size ≤ 2 := Nat.size_le.mpr (by norm_num)
    simp only [isz] at h2 ⊢
    omega
  have h3p : isz (3 * (p : ℤ)) ≤ 8 * ((r + 1) * (p + 1) ^ 2) := by
    have h := isz_natCast_le (3 * p)
    rw [cast_mul_int 3 p] at h
    nlinarith [h, hpX, hX1]
  have h3p3 : isz (3 * (p : ℤ) + 3) ≤ 8 * ((r + 1) * (p + 1) ^ 2) := by
    have h := isz_natCast_le (3 * p + 3)
    rw [cast_add_int (3 * p) 3, cast_mul_int 3 p] at h
    nlinarith [h, hpX, hX1]
  have hAc : isz ((p : ℤ) + ((Nat.clog 2 r : ℕ) : ℤ)) ≤ 8 * ((r + 1) * (p + 1) ^ 2) := hspc
  have hsub1 : isz ((p : ℤ) + ((Nat.clog 2 r : ℕ) : ℤ) - (3 * (p : ℤ) + 3))
      ≤ 16 * ((r + 1) * (p + 1) ^ 2) := by
    have h := isz_sub_le ((p : ℤ) + ((Nat.clog 2 r : ℕ) : ℤ)) (3 * (p : ℤ) + 3)
    linarith [h, hAc, h3p3]
  have hmax1 : isz (max 0 ((p : ℤ) + ((Nat.clog 2 r : ℕ) : ℤ) - (3 * (p : ℤ) + 3)))
      ≤ 32 * ((r + 1) * (p + 1) ^ 2) := by
    have h := isz_max_zero_le ((p : ℤ) + ((Nat.clog 2 r : ℕ) : ℤ) - (3 * (p : ℤ) + 3))
    linarith [h, hsub1, hX1]
  have hP : (p : ℤ) + ((Nat.clog 2 r : ℕ) : ℤ) = ((p + Nat.clog 2 r : ℕ) : ℤ) :=
    Nat.cast_add _ _
  have hQ : (3 : ℤ) * (p : ℤ) + 3 = ((3 * p + 3 : ℕ) : ℤ) := by push_cast; ring
  have step1 : Work.ConvR.WordC main dupP
      (fun vs => vs = Val.int (p : ℤ) :: Val.int (r : ℤ) :: V)
      (fun _ out => out = Val.int (p : ℤ) :: Val.int (p : ℤ) :: Val.int (r : ℤ) :: V)
      (BIG * ((r + 1) * (p + 1) ^ 2)) :=
    wc_dup (hdup main) (Val.int (p : ℤ)) (Val.int (r : ℤ) :: V)
      (BIG * ((r + 1) * (p + 1) ^ 2))
      (costKc (c := 1024) (by simp only [Work.ConvR.vsz_int]; nlinarith [hsp, hX1]) (by omega))
  have step2 : Work.ConvR.WordC main (pushP (.int 3))
      (fun vs => vs = Val.int (p : ℤ) :: Val.int (p : ℤ) :: Val.int (r : ℤ) :: V)
      (fun _ out => out = Val.int 3 :: Val.int (p : ℤ) :: Val.int (p : ℤ) :: Val.int (r : ℤ) :: V)
      (BIG * ((r + 1) * (p + 1) ^ 2)) :=
    wc_pushVal (hpush main) (Val.int 3)
      (Val.int (p : ℤ) :: Val.int (p : ℤ) :: Val.int (r : ℤ) :: V)
      (BIG * ((r + 1) * (p + 1) ^ 2))
      (costKc (c := 1024) (by simp only [Work.ConvR.vsz_int]; nlinarith [hsz3c, hX1]) (by omega))
  have step3 : Work.ConvR.WordC main mulP
      (fun vs => vs = Val.int 3 :: Val.int (p : ℤ) :: Val.int (p : ℤ) :: Val.int (r : ℤ) :: V)
      (fun _ out => out = Val.int (3 * (p : ℤ)) :: Val.int (p : ℤ) :: Val.int (r : ℤ) :: V)
      (BIG * ((r + 1) * (p + 1) ^ 2)) :=
    wc_mul (hmul main) (3 : ℤ) (p : ℤ) (Val.int (p : ℤ) :: Val.int (r : ℤ) :: V)
      (BIG * ((r + 1) * (p + 1) ^ 2))
      (costStepL (c := 1024) (by nlinarith [hsz3c, hsp, hX1]) (by omega))
  have step4 : Work.ConvR.WordC main (pushP (.int 3))
      (fun vs => vs = Val.int (3 * (p : ℤ)) :: Val.int (p : ℤ) :: Val.int (r : ℤ) :: V)
      (fun _ out => out = Val.int 3 :: Val.int (3 * (p : ℤ)) :: Val.int (p : ℤ) :: Val.int (r : ℤ) :: V)
      (BIG * ((r + 1) * (p + 1) ^ 2)) :=
    wc_pushVal (hpush main) (Val.int 3)
      (Val.int (3 * (p : ℤ)) :: Val.int (p : ℤ) :: Val.int (r : ℤ) :: V)
      (BIG * ((r + 1) * (p + 1) ^ 2))
      (costKc (c := 1024) (by simp only [Work.ConvR.vsz_int]; nlinarith [hsz3c, hX1]) (by omega))
  have step5 : Work.ConvR.WordC main addP
      (fun vs => vs = Val.int 3 :: Val.int (3 * (p : ℤ)) :: Val.int (p : ℤ) :: Val.int (r : ℤ) :: V)
      (fun _ out => out = Val.int (3 + 3 * (p : ℤ)) :: Val.int (p : ℤ) :: Val.int (r : ℤ) :: V)
      (BIG * ((r + 1) * (p + 1) ^ 2)) :=
    wc_bin (hadd main) (x := (3 : ℤ)) (y := (3 * (p : ℤ))) (trivial)
      (Val.int (p : ℤ) :: Val.int (r : ℤ) :: V) (BIG * ((r + 1) * (p + 1) ^ 2))
      (costKc (c := 1024) (by nlinarith [hsz3c, h3p, hX1]) (by omega))
  have step5b : Work.ConvR.WordC main addP
      (fun vs => vs = Val.int 3 :: Val.int (3 * (p : ℤ)) :: Val.int (p : ℤ) :: Val.int (r : ℤ) :: V)
      (fun _ out => out = Val.int (3 * (p : ℤ) + 3) :: Val.int (p : ℤ) :: Val.int (r : ℤ) :: V)
      (BIG * ((r + 1) * (p + 1) ^ 2)) :=
    wc_conseq' step5 (fun _ h => h) (fun vs out hvs hQ => by
      rw [hQ]
      exact congrArg (fun z : ℤ => Val.int z :: Val.int (p : ℤ) :: Val.int (r : ℤ) :: V)
        (by ring))
  have step6 : Work.ConvR.WordC main (rollP 2)
      (fun vs => vs = Val.int (3 * (p : ℤ) + 3) :: Val.int (p : ℤ) :: Val.int (r : ℤ) :: V)
      (fun _ out => out = Val.int (r : ℤ) :: Val.int (3 * (p : ℤ) + 3) :: Val.int (p : ℤ) :: V)
      (BIG * ((r + 1) * (p + 1) ^ 2)) :=
    wc_roll (hroll main)
      (Val.int (3 * (p : ℤ) + 3) :: Val.int (p : ℤ) :: Val.int (r : ℤ) :: V) 2
      (by simp) (BIG * ((r + 1) * (p + 1) ^ 2))
      (costStepL (c := 1024) (by
        simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil, Work.ConvR.vsz_int]
        nlinarith [h3p3, hsp, hsr, hX1]) (by omega))
  have step7 : Work.ConvR.WordC main clP
      (fun vs => vs = Val.int (r : ℤ) :: Val.int (3 * (p : ℤ) + 3) :: Val.int (p : ℤ) :: V)
      (fun _ out => out = Val.int (((Nat.clog 2 r : ℕ) : ℤ)) :: Val.int (3 * (p : ℤ) + 3) ::
        Val.int (p : ℤ) :: V)
      (BIG * ((r + 1) * (p + 1) ^ 2)) :=
    wc_un (hcl main) (x := (r : ℤ)) (Int.ofNat_nonneg r)
      (Val.int (3 * (p : ℤ) + 3) :: Val.int (p : ℤ) :: V)
      (BIG * ((r + 1) * (p + 1) ^ 2))
      (costKc (c := 1024) (by nlinarith [hsr, hX1]) (by omega))
  have step8 : Work.ConvR.WordC main (rollP 2)
      (fun vs => vs = Val.int (((Nat.clog 2 r : ℕ) : ℤ)) :: Val.int (3 * (p : ℤ) + 3) ::
        Val.int (p : ℤ) :: V)
      (fun _ out => out = Val.int (p : ℤ) :: Val.int (((Nat.clog 2 r : ℕ) : ℤ)) ::
        Val.int (3 * (p : ℤ) + 3) :: V)
      (BIG * ((r + 1) * (p + 1) ^ 2)) :=
    wc_roll (hroll main)
      (Val.int (((Nat.clog 2 r : ℕ) : ℤ)) :: Val.int (3 * (p : ℤ) + 3) :: Val.int (p : ℤ) :: V) 2
      (by simp) (BIG * ((r + 1) * (p + 1) ^ 2))
      (costStepL (c := 1024) (by
        simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil, Work.ConvR.vsz_int]
        nlinarith [hscl, h3p3, hsp, hX1]) (by omega))
  have step9 : Work.ConvR.WordC main addP
      (fun vs => vs = Val.int (p : ℤ) :: Val.int (((Nat.clog 2 r : ℕ) : ℤ)) ::
        Val.int (3 * (p : ℤ) + 3) :: V)
      (fun _ out => out = Val.int ((p : ℤ) + ((Nat.clog 2 r : ℕ) : ℤ)) ::
        Val.int (3 * (p : ℤ) + 3) :: V)
      (BIG * ((r + 1) * (p + 1) ^ 2)) :=
    wc_bin (hadd main) (x := (p : ℤ)) (y := ((Nat.clog 2 r : ℕ) : ℤ)) (trivial)
      (Val.int (3 * (p : ℤ) + 3) :: V) (BIG * ((r + 1) * (p + 1) ^ 2))
      (costKc (c := 1024) (by nlinarith [hsp, hscl, hX1]) (by omega))
  have step10 : Work.ConvR.WordC main dupP
      (fun vs => vs = Val.int ((p : ℤ) + ((Nat.clog 2 r : ℕ) : ℤ)) ::
        Val.int (3 * (p : ℤ) + 3) :: V)
      (fun _ out => out = Val.int ((p : ℤ) + ((Nat.clog 2 r : ℕ) : ℤ)) ::
        Val.int ((p : ℤ) + ((Nat.clog 2 r : ℕ) : ℤ)) :: Val.int (3 * (p : ℤ) + 3) :: V)
      (BIG * ((r + 1) * (p + 1) ^ 2)) :=
    wc_dup (hdup main) (Val.int ((p : ℤ) + ((Nat.clog 2 r : ℕ) : ℤ)))
      (Val.int (3 * (p : ℤ) + 3) :: V) (BIG * ((r + 1) * (p + 1) ^ 2))
      (costKc (c := 1024) (by simp only [Work.ConvR.vsz_int]; nlinarith [hspc, hX1]) (by omega))
  have step11 : Work.ConvR.WordC main (rollP 2)
      (fun vs => vs = Val.int ((p : ℤ) + ((Nat.clog 2 r : ℕ) : ℤ)) ::
        Val.int ((p : ℤ) + ((Nat.clog 2 r : ℕ) : ℤ)) :: Val.int (3 * (p : ℤ) + 3) :: V)
      (fun _ out => out = Val.int (3 * (p : ℤ) + 3) ::
        Val.int ((p : ℤ) + ((Nat.clog 2 r : ℕ) : ℤ)) ::
        Val.int ((p : ℤ) + ((Nat.clog 2 r : ℕ) : ℤ)) :: V)
      (BIG * ((r + 1) * (p + 1) ^ 2)) :=
    wc_roll (hroll main)
      (Val.int ((p : ℤ) + ((Nat.clog 2 r : ℕ) : ℤ)) ::
        Val.int ((p : ℤ) + ((Nat.clog 2 r : ℕ) : ℤ)) :: Val.int (3 * (p : ℤ) + 3) :: V) 2
      (by simp) (BIG * ((r + 1) * (p + 1) ^ 2))
      (costStepL (c := 1024) (by
        simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil, Work.ConvR.vsz_int]
        nlinarith [hspc, h3p3, hX1]) (by omega))
  have step12 : Work.ConvR.WordC main swapP
      (fun vs => vs = Val.int (3 * (p : ℤ) + 3) ::
        Val.int ((p : ℤ) + ((Nat.clog 2 r : ℕ) : ℤ)) ::
        Val.int ((p : ℤ) + ((Nat.clog 2 r : ℕ) : ℤ)) :: V)
      (fun _ out => out = Val.int ((p : ℤ) + ((Nat.clog 2 r : ℕ) : ℤ)) ::
        Val.int (3 * (p : ℤ) + 3) ::
        Val.int ((p : ℤ) + ((Nat.clog 2 r : ℕ) : ℤ)) :: V)
      (BIG * ((r + 1) * (p + 1) ^ 2)) :=
    wc_swap (hswap main) (Val.int (3 * (p : ℤ) + 3))
      (Val.int ((p : ℤ) + ((Nat.clog 2 r : ℕ) : ℤ)))
      (Val.int ((p : ℤ) + ((Nat.clog 2 r : ℕ) : ℤ)) :: V)
      (BIG * ((r + 1) * (p + 1) ^ 2))
      (costKc (c := 1024) (by simp only [Work.ConvR.vsz_int]; nlinarith [h3p3, hspc, hX1])
        (by omega))
  have step13 : Work.ConvR.WordC main subP
      (fun vs => vs = Val.int ((p : ℤ) + ((Nat.clog 2 r : ℕ) : ℤ)) ::
        Val.int (3 * (p : ℤ) + 3) ::
        Val.int ((p : ℤ) + ((Nat.clog 2 r : ℕ) : ℤ)) :: V)
      (fun _ out => out = Val.int ((p : ℤ) + ((Nat.clog 2 r : ℕ) : ℤ) - (3 * (p : ℤ) + 3)) ::
        Val.int ((p : ℤ) + ((Nat.clog 2 r : ℕ) : ℤ)) :: V)
      (BIG * ((r + 1) * (p + 1) ^ 2)) :=
    wc_bin (hsub main) (x := (p : ℤ) + ((Nat.clog 2 r : ℕ) : ℤ)) (y := (3 * (p : ℤ) + 3))
      (trivial) (Val.int ((p : ℤ) + ((Nat.clog 2 r : ℕ) : ℤ)) :: V)
      (BIG * ((r + 1) * (p + 1) ^ 2))
      (costKc (c := 1024) (by nlinarith [hspc, h3p3, hX1]) (by omega))
  have step14 : Work.ConvR.WordC main (pushP (.int 0))
      (fun vs => vs = Val.int ((p : ℤ) + ((Nat.clog 2 r : ℕ) : ℤ) - (3 * (p : ℤ) + 3)) ::
        Val.int ((p : ℤ) + ((Nat.clog 2 r : ℕ) : ℤ)) :: V)
      (fun _ out => out = Val.int 0 ::
        Val.int ((p : ℤ) + ((Nat.clog 2 r : ℕ) : ℤ) - (3 * (p : ℤ) + 3)) ::
        Val.int ((p : ℤ) + ((Nat.clog 2 r : ℕ) : ℤ)) :: V)
      (BIG * ((r + 1) * (p + 1) ^ 2)) :=
    wc_pushVal (hpush main) (Val.int 0)
      (Val.int ((p : ℤ) + ((Nat.clog 2 r : ℕ) : ℤ) - (3 * (p : ℤ) + 3)) ::
        Val.int ((p : ℤ) + ((Nat.clog 2 r : ℕ) : ℤ)) :: V)
      (BIG * ((r + 1) * (p + 1) ^ 2))
      (costKc (c := 1024) (by simp only [Work.ConvR.vsz_int]; nlinarith [hs0, hX1]) (by omega))
  have step15 : Work.ConvR.WordC main maxP
      (fun vs => vs = Val.int 0 ::
        Val.int ((p : ℤ) + ((Nat.clog 2 r : ℕ) : ℤ) - (3 * (p : ℤ) + 3)) ::
        Val.int ((p : ℤ) + ((Nat.clog 2 r : ℕ) : ℤ)) :: V)
      (fun _ out => out = Val.int (max 0 ((p : ℤ) + ((Nat.clog 2 r : ℕ) : ℤ) - (3 * (p : ℤ) + 3))) ::
        Val.int ((p : ℤ) + ((Nat.clog 2 r : ℕ) : ℤ)) :: V)
      (BIG * ((r + 1) * (p + 1) ^ 2)) :=
    wc_bin (hmax main) (x := (0 : ℤ))
      (y := (p : ℤ) + ((Nat.clog 2 r : ℕ) : ℤ) - (3 * (p : ℤ) + 3)) (trivial)
      (Val.int ((p : ℤ) + ((Nat.clog 2 r : ℕ) : ℤ)) :: V)
      (BIG * ((r + 1) * (p + 1) ^ 2))
      (costKc (c := 1024) (by
        have h := isz_sub_le ((p : ℤ) + ((Nat.clog 2 r : ℕ) : ℤ)) (3 * (p : ℤ) + 3)
        nlinarith [hs0, h, hspc, h3p3, hX1]) (by omega))
  have step16 : Work.ConvR.WordC main swapP
      (fun vs => vs = Val.int (max 0 ((p : ℤ) + ((Nat.clog 2 r : ℕ) : ℤ) - (3 * (p : ℤ) + 3))) ::
        Val.int ((p : ℤ) + ((Nat.clog 2 r : ℕ) : ℤ)) :: V)
      (fun _ out => out = Val.int ((p : ℤ) + ((Nat.clog 2 r : ℕ) : ℤ)) ::
        Val.int (max 0 ((p : ℤ) + ((Nat.clog 2 r : ℕ) : ℤ) - (3 * (p : ℤ) + 3))) :: V)
      (BIG * ((r + 1) * (p + 1) ^ 2)) :=
    wc_swap (hswap main)
      (Val.int (max 0 ((p : ℤ) + ((Nat.clog 2 r : ℕ) : ℤ) - (3 * (p : ℤ) + 3))))
      (Val.int ((p : ℤ) + ((Nat.clog 2 r : ℕ) : ℤ))) V
      (BIG * ((r + 1) * (p + 1) ^ 2))
      (costKc (c := 1024) (by simp only [Work.ConvR.vsz_int]; nlinarith [hmax1, hspc, hX1])
        (by omega))
  have step17 : Work.ConvR.WordC main subP
      (fun vs => vs = Val.int ((p : ℤ) + ((Nat.clog 2 r : ℕ) : ℤ)) ::
        Val.int (max 0 ((p : ℤ) + ((Nat.clog 2 r : ℕ) : ℤ) - (3 * (p : ℤ) + 3))) :: V)
      (fun _ out => out = Val.int (((p : ℤ) + ((Nat.clog 2 r : ℕ) : ℤ)) -
        max 0 ((p : ℤ) + ((Nat.clog 2 r : ℕ) : ℤ) - (3 * (p : ℤ) + 3))) :: V)
      (BIG * ((r + 1) * (p + 1) ^ 2)) :=
    wc_bin (hsub main) (x := (p : ℤ) + ((Nat.clog 2 r : ℕ) : ℤ))
      (y := max 0 ((p : ℤ) + ((Nat.clog 2 r : ℕ) : ℤ) - (3 * (p : ℤ) + 3))) (trivial) V
      (BIG * ((r + 1) * (p + 1) ^ 2))
      (costKc (c := 1024) (by nlinarith [hspc, hmax1, hX1]) (by omega))
  have hall : Work.ConvR.WordC main
      (List.foldl (fun a b => Cmd.seq a b) Cmd.skip
        [dupP, pushP (.int 3), mulP, pushP (.int 3), addP, rollP 2, clP, rollP 2, addP, dupP,
          rollP 2, swapP, subP, pushP (.int 0), maxP, swapP, subP])
      (fun vs => vs = Val.int (p : ℤ) :: Val.int (r : ℤ) :: V)
      (fun _ out => out = Val.int (((p : ℤ) + ((Nat.clog 2 r : ℕ) : ℤ)) -
        max 0 ((p : ℤ) + ((Nat.clog 2 r : ℕ) : ℤ) - (3 * (p : ℤ) + 3))) :: V)
      (1 + 17 * (BIG * ((r + 1) * (p + 1) ^ 2))) := by
    have h1 := wc_chainN (wc_skipN (Val.int (p : ℤ) :: Val.int (r : ℤ) :: V) BIG
      ((r + 1) * (p + 1) ^ 2)) step1
    have h2 := wc_chainN h1 step2
    have h3 := wc_chainN h2 step3
    have h4 := wc_chainN h3 step4
    have h5 := wc_chainN h4 step5b
    have h6 := wc_chainN h5 step6
    have h7 := wc_chainN h6 step7
    have h8 := wc_chainN h7 step8
    have h9 := wc_chainN h8 step9
    have h10 := wc_chainN h9 step10
    have h11 := wc_chainN h10 step11
    have h12 := wc_chainN h11 step12
    have h13 := wc_chainN h12 step13
    have h14 := wc_chainN h13 step14
    have h15 := wc_chainN h14 step15
    have h16 := wc_chainN h15 step16
    have h17 := wc_chainN h16 step17
    exact h17
  have hval : ((p : ℤ) + ((Nat.clog 2 r : ℕ) : ℤ)) -
      max 0 ((p : ℤ) + ((Nat.clog 2 r : ℕ) : ℤ) - (3 * (p : ℤ) + 3)) =
      ((min (p + Nat.clog 2 r) (3 * p + 3) : ℕ) : ℤ) := by
    rw [hP, hQ, max_comm, ← minSubMax, ← minCast]
  intro vs hvs s R hR
  obtain ⟨out, s', n, hQ, he, hn, hstk, hoth⟩ := hall vs hvs s R hR
  refine ⟨out, s', n, ?_, he, ?_, hstk, hoth⟩
  · rw [hQ, hval]
  · refine le_trans hn ?_
    exact capBound (n := 17) (BIG := BIG) (X := ((r + 1) * (p + 1) ^ 2)) hX1

/-! ## `pairDivBody`: divide a pair of integers by `2^k` -/

theorem pairDivBody (hK : HvdH.KernelLib) (hI : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ),
      ∀ (main : HvdH.Cmd) (k : ℤ) (V : List HvdH.Val) (a b : ℤ), 0 ≤ k →
        HvdH.WordR main prog
          (fun vs => vs = HvdH.Val.int a :: HvdH.Val.int b :: HvdH.Val.int k :: V)
          (fun _ out => out = HvdH.cfxVal (Int.tdiv a (2 ^ k.toNat), Int.tdiv b (2 ^ k.toNat)) ::
            HvdH.Val.int k :: V)
          (fun _ => K * (HvdH.isz a + HvdH.isz b + HvdH.isz k + 1)) := by
  obtain ⟨pickP, PK, hpick⟩ := hK.pick
  obtain ⟨swapP, SWK, hswap⟩ := hK.swap
  obtain ⟨rollP, ROK, hroll⟩ := hK.roll
  obtain ⟨consP, CK, hcons⟩ := hK.consV
  obtain ⟨shrP, SHK, hshr⟩ := hI.shrT
  refine ⟨List.foldl (fun a b => Cmd.seq a b) Cmd.skip
    [pickP 2, swapP, shrP, pickP 2, rollP 2, shrP, swapP, consP],
    8 * (60 * (PK + SWK + ROK + CK + SHK + 1)) + 1, ?_⟩
  intro main k V a b hk
  set BIG : ℕ := 60 * (PK + SWK + ROK + CK + SHK + 1) with hBIG
  set Z : ℕ := isz a + isz b + isz k + 1 with hZ
  have hZ1 : 1 ≤ Z := by omega
  have hq1 : isz (a.tdiv (2 ^ k.toNat)) ≤ isz a := isz_tdiv_le _ _
  have hq2 : isz (b.tdiv (2 ^ k.toNat)) ≤ isz b := isz_tdiv_le _ _
  have h1 : Work.ConvR.WordC main (pickP 2)
      (fun vs => vs = Val.int a :: Val.int b :: Val.int k :: V)
      (fun _ out => out = Val.int k :: Val.int a :: Val.int b :: Val.int k :: V) (BIG * Z) := by
    refine wc_pick (hpick main) (Val.int a :: Val.int b :: Val.int k :: V) 2 (by simp) (BIG * Z) ?_
    refine costStepL (c := 60) ?_ (by omega)
    simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, Work.ConvR.vsz_int]
    nlinarith [hZ, hZ1]
  have h2 : Work.ConvR.WordC main swapP
      (fun vs => vs = Val.int k :: Val.int a :: Val.int b :: Val.int k :: V)
      (fun _ out => out = Val.int a :: Val.int k :: Val.int b :: Val.int k :: V) (BIG * Z) := by
    refine wc_swap (hswap main) (Val.int k) (Val.int a) (Val.int b :: Val.int k :: V) (BIG * Z) ?_
    refine costKc (c := 60) ?_ (by omega)
    simp only [Work.ConvR.vsz_int]
    nlinarith [hZ, hZ1]
  have h3 : Work.ConvR.WordC main shrP
      (fun vs => vs = Val.int a :: Val.int k :: Val.int b :: Val.int k :: V)
      (fun _ out => out = Val.int (a.tdiv (2 ^ k.toNat)) :: Val.int b :: Val.int k :: V)
      (BIG * Z) := by
    refine wc_bin (hshr main) (x := a) (y := k) hk (Val.int b :: Val.int k :: V) (BIG * Z) ?_
    refine costKc (c := 60) ?_ (by omega)
    nlinarith [hZ, hZ1]
  have h4 : Work.ConvR.WordC main (pickP 2)
      (fun vs => vs = Val.int (a.tdiv (2 ^ k.toNat)) :: Val.int b :: Val.int k :: V)
      (fun _ out => out = Val.int k :: Val.int (a.tdiv (2 ^ k.toNat)) :: Val.int b ::
        Val.int k :: V) (BIG * Z) := by
    refine wc_pick (hpick main)
      (Val.int (a.tdiv (2 ^ k.toNat)) :: Val.int b :: Val.int k :: V) 2 (by simp) (BIG * Z) ?_
    refine costStepL (c := 60) ?_ (by omega)
    simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, Work.ConvR.vsz_int]
    nlinarith [hZ, hZ1, hq1]
  have h5 : Work.ConvR.WordC main (rollP 2)
      (fun vs => vs = Val.int k :: Val.int (a.tdiv (2 ^ k.toNat)) :: Val.int b ::
        Val.int k :: V)
      (fun _ out => out = Val.int b :: Val.int k :: Val.int (a.tdiv (2 ^ k.toNat)) ::
        Val.int k :: V) (BIG * Z) := by
    refine wc_roll (hroll main)
      (Val.int k :: Val.int (a.tdiv (2 ^ k.toNat)) :: Val.int b :: Val.int k :: V) 2
      (by simp) (BIG * Z) ?_
    refine costStepL (c := 60) ?_ (by omega)
    simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, Work.ConvR.vsz_int]
    nlinarith [hZ, hZ1, hq1]
  have h6 : Work.ConvR.WordC main shrP
      (fun vs => vs = Val.int b :: Val.int k :: Val.int (a.tdiv (2 ^ k.toNat)) ::
        Val.int k :: V)
      (fun _ out => out = Val.int (b.tdiv (2 ^ k.toNat)) :: Val.int (a.tdiv (2 ^ k.toNat)) ::
        Val.int k :: V) (BIG * Z) := by
    refine wc_bin (hshr main) (x := b) (y := k) hk
      (Val.int (a.tdiv (2 ^ k.toNat)) :: Val.int k :: V) (BIG * Z) ?_
    refine costKc (c := 60) ?_ (by omega)
    nlinarith [hZ, hZ1]
  have h7 : Work.ConvR.WordC main swapP
      (fun vs => vs = Val.int (b.tdiv (2 ^ k.toNat)) :: Val.int (a.tdiv (2 ^ k.toNat)) ::
        Val.int k :: V)
      (fun _ out => out = Val.int (a.tdiv (2 ^ k.toNat)) :: Val.int (b.tdiv (2 ^ k.toNat)) ::
        Val.int k :: V) (BIG * Z) := by
    refine wc_swap (hswap main) (Val.int (b.tdiv (2 ^ k.toNat)))
      (Val.int (a.tdiv (2 ^ k.toNat))) (Val.int k :: V) (BIG * Z) ?_
    refine costKc (c := 60) ?_ (by omega)
    simp only [Work.ConvR.vsz_int]
    nlinarith [hZ, hZ1, hq1, hq2]
  have h8 : Work.ConvR.WordC main consP
      (fun vs => vs = Val.int (a.tdiv (2 ^ k.toNat)) :: Val.int (b.tdiv (2 ^ k.toNat)) ::
        Val.int k :: V)
      (fun _ out => out = cfxVal (Int.tdiv a (2 ^ k.toNat), Int.tdiv b (2 ^ k.toNat)) ::
        Val.int k :: V) (BIG * Z) :=
    wc_consV (hcons main) (Val.int (a.tdiv (2 ^ k.toNat))) (Val.int (b.tdiv (2 ^ k.toNat)))
      (Val.int k :: V) (BIG * Z) (by nlinarith [hZ1, hBIG])
  have hall : Work.ConvR.WordC main
      (List.foldl (fun a b => Cmd.seq a b) Cmd.skip
        [pickP 2, swapP, shrP, pickP 2, rollP 2, shrP, swapP, consP])
      (fun vs => vs = Val.int a :: Val.int b :: Val.int k :: V)
      (fun _ out => out = cfxVal (Int.tdiv a (2 ^ k.toNat), Int.tdiv b (2 ^ k.toNat)) ::
        Val.int k :: V)
      (1 + 8 * (BIG * Z)) := by
    have g1 := wc_chainN (wc_skipN (Val.int a :: Val.int b :: Val.int k :: V) BIG Z) h1
    have g2 := wc_chainN g1 h2
    have g3 := wc_chainN g2 h3
    have g4 := wc_chainN g3 h4
    have g5 := wc_chainN g4 h5
    have g6 := wc_chainN g5 h6
    have g7 := wc_chainN g6 h7
    have g8 := wc_chainN g7 h8
    exact g8
  intro vs hvs s R hR
  obtain ⟨out, s', n, hQ, he, hn, hstk, hoth⟩ := hall vs hvs s R hR
  exact ⟨out, s', n, hQ, he, le_trans hn (capBound (n := 8) (BIG := BIG) (X := Z) hZ1),
    hstk, hoth⟩

/-! ## `deltaBody`: the negacyclic fold `Δ A = A[0..r) - A[r..2r)` -/

theorem deltaBody (hK : HvdH.KernelLib) (hI : HvdH.IntLib) (hL : HvdH.LayoutLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ),
      ∀ (main : HvdH.Cmd) (p r : ℕ) (A : List ℕ) (V : List HvdH.Val),
        A.length = 2 * r → (∀ m, m < 2 * r → A.getD m 0 < 2 ^ (3 * p)) →
        2 ≤ r → 1 ≤ p →
        HvdH.WordR main prog
          (fun vs => vs = HvdH.ofList ((toZl A).map HvdH.Val.int) ::
            HvdH.Val.int (r : ℤ) :: V)
          (fun _ out => out = HvdH.ofList ((deltaL A r).map HvdH.Val.int) ::
            HvdH.Val.int (r : ℤ) :: V)
          (fun _ => K * ((r + 1) * (p + 1) ^ 2)) := by
  obtain ⟨dupP, DupK, hdup⟩ := hK.dup
  obtain ⟨swapP, SWK, hswap⟩ := hK.swap
  obtain ⟨rollP, ROK, hroll⟩ := hK.roll
  obtain ⟨pickP, PK, hpick⟩ := hK.pick
  obtain ⟨takeP, TAK, htake⟩ := hL.take
  obtain ⟨ldropP, LDK, hldrop⟩ := hL.drop
  obtain ⟨zipP, ZK, hzip⟩ := hK.zipWith
  obtain ⟨subP, SUK, hsub⟩ := hI.sub
  refine ⟨List.foldl (fun a b => Cmd.seq a b) Cmd.skip
    [dupP, pickP 2, takeP, pickP 2, rollP 2, swapP, ldropP, swapP, zipP subP],
    9 * (100000 * (DupK + SWK + ROK + PK + TAK + LDK + ZK + SUK + 1)) + 1, ?_⟩
  intro main p r A V hAlen hb hr hp
  set BIG : ℕ := 100000 * (DupK + SWK + ROK + PK + TAK + LDK + ZK + SUK + 1) with hBIG
  obtain ⟨hX1, hpX, hrX, hp1X, hr1X, hrpX, hp2X, hrp1X⟩ := Xge r p
  set x0 : Val := ofList ((toZl A).map Val.int) with hx0
  set Tx : Val := ofList (((toZl A).take r).map Val.int) with hTx
  set Dx : Val := ofList (((toZl A).drop r).map Val.int) with hDx
  set Cr : Val := Val.int (r : ℤ) with hCr
  set L : ℕ := 3 * p + 4 with hLdef
  have hszA : vsz x0 ≤ 8 * ((r + 1) * (p + 1) ^ 2) := by
    rw [hx0, ← intList_eq_map]
    exact vsz_intList_le' hAlen hb
  have hszTx : vsz Tx ≤ 8 * ((r + 1) * (p + 1) ^ 2) := by
    rw [hTx, List.map_take]
    exact le_trans (vsz_ofList_take_le ((toZl A).map Val.int) r) hszA
  have hszDx : vsz Dx ≤ 8 * ((r + 1) * (p + 1) ^ 2) := by
    rw [hDx, List.map_drop]
    exact le_trans (vsz_ofList_drop_le ((toZl A).map Val.int) r) hszA
  have hszR : isz (r : ℤ) ≤ 4 * ((r + 1) * (p + 1) ^ 2) := by
    have h := isz_natCast_le r; omega
  have q1 : Work.ConvR.WordC main dupP (fun vs => vs = x0 :: Cr :: V)
      (fun _ out => out = x0 :: x0 :: Cr :: V) (BIG * ((r + 1) * (p + 1) ^ 2)) :=
    wc_dup (hdup main) x0 (Cr :: V) (BIG * ((r + 1) * (p + 1) ^ 2))
      (costKc (c := 1024) (by rw [hx0]; linarith [hszA, hX1]) (by omega))
  have q2 : Work.ConvR.WordC main (pickP 2)
      (fun vs => vs = x0 :: x0 :: Cr :: V) (fun _ out => out = Cr :: x0 :: x0 :: Cr :: V)
      (BIG * ((r + 1) * (p + 1) ^ 2)) := by
    refine wc_pick (hpick main) (x0 :: x0 :: Cr :: V) 2 (by simp) (BIG * ((r + 1) * (p + 1) ^ 2)) ?_
    refine costStepL (c := 1024) ?_ (by omega)
    rw [hCr]
    simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, Work.ConvR.vsz_int]
    nlinarith [hszA, hszR, hX1]
  have q3 : Work.ConvR.WordC main takeP
      (fun vs => vs = Cr :: x0 :: x0 :: Cr :: V) (fun _ out => out = Tx :: x0 :: Cr :: V)
      (BIG * ((r + 1) * (p + 1) ^ 2)) := by
    have h1 := wc_take (htake main) r ((toZl A).map Val.int) (x0 :: Cr :: V)
      (BIG * ((r + 1) * (p + 1) ^ 2)) (by
        rw [← hx0]
        refine costKc (c := 1024) ?_ (by omega)
        linarith [hszA, hszR, hX1])
    refine wc_conseq' h1 ?_ ?_
    · intro vs hvs
      rw [hvs, hCr, hx0]
    · intro vs out hvs hQ
      rw [hQ, hTx, List.map_take]
  have q4 : Work.ConvR.WordC main (pickP 2)
      (fun vs => vs = Tx :: x0 :: Cr :: V) (fun _ out => out = Cr :: Tx :: x0 :: Cr :: V)
      (BIG * ((r + 1) * (p + 1) ^ 2)) := by
    refine wc_pick (hpick main) (Tx :: x0 :: Cr :: V) 2 (by simp) (BIG * ((r + 1) * (p + 1) ^ 2)) ?_
    refine costStepL (c := 1024) ?_ (by omega)
    rw [hCr]
    simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, Work.ConvR.vsz_int]
    nlinarith [hszTx, hszA, hszR, hX1]
  have q5 : Work.ConvR.WordC main (rollP 2)
      (fun vs => vs = Cr :: Tx :: x0 :: Cr :: V) (fun _ out => out = x0 :: Cr :: Tx :: Cr :: V)
      (BIG * ((r + 1) * (p + 1) ^ 2)) := by
    refine wc_roll (hroll main) (Cr :: Tx :: x0 :: Cr :: V) 2 (by simp)
      (BIG * ((r + 1) * (p + 1) ^ 2)) ?_
    refine costStepL (c := 1024) ?_ (by omega)
    rw [hCr]
    simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, Work.ConvR.vsz_int]
    nlinarith [hszTx, hszA, hszR, hX1]
  have q6 : Work.ConvR.WordC main swapP
      (fun vs => vs = x0 :: Cr :: Tx :: Cr :: V) (fun _ out => out = Cr :: x0 :: Tx :: Cr :: V)
      (BIG * ((r + 1) * (p + 1) ^ 2)) := by
    refine wc_swap (hswap main) x0 Cr (Tx :: Cr :: V) (BIG * ((r + 1) * (p + 1) ^ 2)) ?_
    refine costKc (c := 1024) ?_ (by omega)
    rw [hCr]
    simp only [Work.ConvR.vsz_int]
    nlinarith [hszA, hszR, hX1]
  have q7 : Work.ConvR.WordC main ldropP
      (fun vs => vs = Cr :: x0 :: Tx :: Cr :: V) (fun _ out => out = Dx :: Tx :: Cr :: V)
      (BIG * ((r + 1) * (p + 1) ^ 2)) := by
    have h1 := wc_ldrop (hldrop main) r ((toZl A).map Val.int) (Tx :: Cr :: V)
      (BIG * ((r + 1) * (p + 1) ^ 2)) (by
        rw [← hx0]
        refine costKc (c := 1024) ?_ (by omega)
        linarith [hszA, hszR, hX1])
    refine wc_conseq' h1 ?_ ?_
    · intro vs hvs
      rw [hvs, hCr, hx0]
    · intro vs out hvs hQ
      rw [hQ, hDx, List.map_drop]
  have q8 : Work.ConvR.WordC main swapP
      (fun vs => vs = Dx :: Tx :: Cr :: V) (fun _ out => out = Tx :: Dx :: Cr :: V)
      (BIG * ((r + 1) * (p + 1) ^ 2)) := by
    refine wc_swap (hswap main) Dx Tx (Cr :: V) (BIG * ((r + 1) * (p + 1) ^ 2)) ?_
    refine costKc (c := 1024) ?_ (by omega)
    nlinarith [hszDx, hszTx, hX1]
  set TL : List ℤ := List.take r (toZl A) with hTL
  set DL : List ℤ := List.drop r (toZl A) with hDL
  have hTLlen : TL.length = r := by
    rw [hTL, List.length_take, toZl_length, hAlen, Nat.min_eq_left (by omega)]
  have hDLlen : DL.length = r := by
    rw [hDL, List.length_drop, toZl_length, hAlen]; omega
  have hsubP : BinOp main subP (fun a b : ℤ => a.natAbs ≤ 2 ^ (3 * p) ∧ b.natAbs ≤ 2 ^ (3 * p))
      (fun a b => a - b) (fun a b => SUK * (isz a + isz b)) :=
    binOp_ss (hsub main) (fun _ _ _ => trivial)
  have hbody := zipBody (main := main) (qP := subP) (QK := SUK) (f := (· - ·))
    (P := fun a b : ℤ => a.natAbs ≤ 2 ^ (3 * p) ∧ b.natAbs ≤ 2 ^ (3 * p))
    (Cr :: V) hsubP (c := SUK * (2 * L)) (L := L) le_rfl
    (fun a b hP _ _ => by
      have h1 := int_natAbs_sub_le' hP.1 hP.2
      have h2 := Work.ConvR.isz_le_of_natAbs_le h1
      simp only [hLdef] at h2 ⊢
      omega)
  have hPmem : ∀ i, i < (List.map Val.int TL).length →
      (∃ a b, (List.map Val.int TL).getD i .nil = Val.int a ∧
        (List.map Val.int DL).getD i .nil = Val.int b ∧
        (a.natAbs ≤ 2 ^ (3 * p) ∧ b.natAbs ≤ 2 ^ (3 * p)) ∧ isz a ≤ L ∧ isz b ≤ L) := by
    intro i hi
    have hiTL : i < TL.length := by simpa [List.length_map] using hi
    have hi1 : i < r := by rw [hTLlen] at hiTL; exact hiTL
    have hltA : i < A.length := by omega
    have hltA2 : i + r < A.length := by omega
    have hiDL : i < DL.length := by rw [hDLlen]; exact hi1
    refine ⟨(A.getD i 0 : ℤ), (A.getD (i + r) 0 : ℤ), ?_, ?_, ⟨?_, ?_⟩, ?_, ?_⟩
    · rw [getD_map_int hiTL, hTL, getD_take_eq (l := toZl A) (r := r) (by rw [← hTL]; exact hiTL), toZl_getD hltA]
    · rw [getD_map_int hiDL, hDL, getD_drop_eq (l := toZl A) (r := r) (by rw [← hDL]; exact hiDL), toZl_getD hltA2]
    · have h := hb i (by omega)
      rw [Int.natAbs_natCast]; exact h.le
    · have h := hb (i + r) (by omega)
      rw [Int.natAbs_natCast]; exact h.le
    · have h := isz_natCast_le_three (A.getD i 0) p (hb i (by omega))
      simp only [hLdef] at h ⊢; omega
    · have h := isz_natCast_le_three (A.getD (i + r) 0) p (hb (i + r) (by omega))
      simp only [hLdef] at h ⊢; omega
  have hLmem : ∀ x ∈ (List.map Val.int TL ++ List.map Val.int DL), vsz x ≤ L := by
    intro x hx
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      rw [Work.ConvR.vsz_int]
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hy
      have hltA : i < A.length := by omega
      rw [← List.getD_eq_getElem TL 0 hi, hTL,
        getD_take_eq (l := toZl A) (r := r) (by rw [← hTL]; exact hi), toZl_getD hltA]
      have h := isz_natCast_le_three (A.getD i 0) p (hb i (by omega))
      simp only [hLdef] at h ⊢; omega
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      rw [Work.ConvR.vsz_int]
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hy
      have hltA2 : i + r < A.length := by omega
      rw [← List.getD_eq_getElem DL 0 hi, hDL,
        getD_drop_eq (l := toZl A) (r := r) (by rw [← hDL]; exact hi), toZl_getD hltA2]
      have h := isz_natCast_le_three (A.getD (i + r) 0) p (hb (i + r) (by omega))
      simp only [hLdef] at h ⊢; omega
  have hq9 := hzip main subP (Cr :: V)
    (fun x y => ∃ a b, x = Val.int a ∧ y = Val.int b ∧
      (a.natAbs ≤ 2 ^ (3 * p) ∧ b.natAbs ≤ 2 ^ (3 * p)) ∧ isz a ≤ L ∧ isz b ≤ L)
    (fun x y z => ∃ a b, x = Val.int a ∧ y = Val.int b ∧ z = Val.int (a - b))
    (SUK * (2 * L)) L hbody (List.map Val.int TL) (List.map Val.int DL)
    (by rw [List.length_map, List.length_map, hTLlen, hDLlen]) hPmem hLmem
  have q9 : Work.ConvR.WordC main (zipP subP)
      (fun vs => vs = Tx :: Dx :: Cr :: V)
      (fun _ out => out = ofList ((deltaL A r).map Val.int) :: Cr :: V)
      (BIG * ((r + 1) * (p + 1) ^ 2)) := by
    refine wc_conseq' (wc_ofWordR hq9 ?_) ?_ ?_
    · intro vs hvs
      show (List.map Val.int TL).length * (SUK * (2 * L) + ZK * (L + 1)) + ZK
        ≤ BIG * ((r + 1) * (p + 1) ^ 2)
      rw [show (List.map Val.int TL).length = r from by rw [List.length_map, hTLlen]]
      have h2L : 2 * L ≤ 14 * (p + 1) := by simp only [hLdef]; omega
      have hL1 : L + 1 ≤ 7 * (p + 1) := by simp only [hLdef]; omega
      have hrp' : r * (p + 1) ≤ (r + 1) * (p + 1) ^ 2 := by nlinarith
      have hSB : 14 * SUK + 8 * ZK ≤ BIG := by omega
      calc r * (SUK * (2 * L) + ZK * (L + 1)) + ZK
          ≤ r * (SUK * (14 * (p + 1)) + ZK * (7 * (p + 1))) + ZK := by
            apply Nat.add_le_add_right
            apply Nat.mul_le_mul_left
            exact Nat.add_le_add (Nat.mul_le_mul_left _ h2L) (Nat.mul_le_mul_left _ hL1)
        _ = 14 * SUK * (r * (p + 1)) + 7 * ZK * (r * (p + 1)) + ZK := by ring
        _ ≤ 14 * SUK * ((r + 1) * (p + 1) ^ 2) + 7 * ZK * ((r + 1) * (p + 1) ^ 2)
              + ZK * ((r + 1) * (p + 1) ^ 2) := by
            refine Nat.add_le_add (Nat.add_le_add ?_ ?_) ?_
            · exact Nat.mul_le_mul_left _ hrp'
            · exact Nat.mul_le_mul_left _ hrp'
            · calc ZK = ZK * 1 := (Nat.mul_one ZK).symm
                _ ≤ ZK * ((r + 1) * (p + 1) ^ 2) := Nat.mul_le_mul_left _ hX1
        _ = (14 * SUK + 8 * ZK) * ((r + 1) * (p + 1) ^ 2) := by ring
        _ ≤ BIG * ((r + 1) * (p + 1) ^ 2) := Nat.mul_le_mul_right _ hSB
    · intro vs hvs
      rw [hvs, hTx, hDx]
      try rfl
    · intro vs out hvs hQ
      obtain ⟨zs, hout, hzlen, hzs⟩ := hQ
      rw [hout]
      congr 1
      have hlen1 : TL.length = DL.length := by rw [hTLlen, hDLlen]
      have hlen2 : zs.length = TL.length := by rw [hzlen, List.length_map]
      have hpoint : ∀ i, i < TL.length →
          zs.getD i .nil = Val.int ((· - ·) (TL.getD i 0) (DL.getD i 0)) := by
        intro i hi
        have hi2 : i < (List.map Val.int TL).length := by simpa [List.length_map] using hi
        have hiD : i < DL.length := by rw [hDLlen]; omega
        obtain ⟨a, b, ha, hb2, hf⟩ := hzs i hi2
        have ha' : a = TL.getD i 0 := by
          apply (Val.int.injEq a _).mp
          rw [← ha, getD_map_int hi]
        have hb' : b = DL.getD i 0 := by
          apply (Val.int.injEq b _).mp
          rw [← hb2, getD_map_int hiD]
        rw [hf, ha', hb']
      have hmain := zipWith_int_eq (f := (· - ·)) hlen1 hlen2 hpoint
      rw [hmain, hTL, hDL]
      try rfl
  have hall : Work.ConvR.WordC main
      (List.foldl (fun a b => Cmd.seq a b) Cmd.skip
        [dupP, pickP 2, takeP, pickP 2, rollP 2, swapP, ldropP, swapP, zipP subP])
      (fun vs => vs = ofList ((toZl A).map Val.int) :: Val.int (r : ℤ) :: V)
      (fun _ out => out = ofList ((deltaL A r).map Val.int) :: Val.int (r : ℤ) :: V)
      (1 + 9 * (BIG * ((r + 1) * (p + 1) ^ 2))) := by
    have g0 := wc_skipN (main := main) (ofList ((toZl A).map Val.int) :: Val.int (r : ℤ) :: V) BIG
      ((r + 1) * (p + 1) ^ 2)
    have g1 := wc_chainN g0 q1
    have g2 := wc_chainN g1 q2
    have g3 := wc_chainN g2 q3
    have g4 := wc_chainN g3 q4
    have g5 := wc_chainN g4 q5
    have g6 := wc_chainN g5 q6
    have g7 := wc_chainN g6 q7
    have g8 := wc_chainN g7 q8
    have g9 := wc_chainN g8 q9
    exact g9
  intro vs hvs s R hR
  obtain ⟨out, s', n, hQ, he, hn, hstk, hoth⟩ := hall vs hvs s R hR
  exact ⟨out, s', n, hQ, he,
    le_trans hn (capBound (n := 9) (BIG := BIG) (X := ((r + 1) * (p + 1) ^ 2)) hX1),
    hstk, hoth⟩

/-! ## size helpers for `combineDBody` -/

theorem zsVal_size' {A : List ℕ} {r p : ℕ} (hlen : A.length = 2 * r)
    (hb : ∀ m, m < A.length → A.getD m 0 < 2 ^ (3 * p)) :
    vsz (zsVal (deltaL A r)) ≤ 5 * ((r + 1) * (p + 1) ^ 2) := by
  have h1 : (deltaL A r).length = r := by rw [deltaL_length, hlen]; omega
  have h2 := deltaL_mem_bound (A := A) (r := r) (p := p) hb
  exact zsVal_sz_le (l := deltaL A r) (r := r) (p := p) h1
    (by intro x hx; have := h2 x hx; omega)

theorem D0L_size' {A00 A11 : List ℕ} {r p : ℕ} (h0 : A00.length = 2 * r)
    (h1 : A11.length = 2 * r) (hb0 : ∀ m, m < A00.length → A00.getD m 0 < 2 ^ (3 * p))
    (hb1 : ∀ m, m < A11.length → A11.getD m 0 < 2 ^ (3 * p)) :
    vsz (zsVal (D0L r A00 A11)) ≤ 5 * ((r + 1) * (p + 1) ^ 2) := by
  have hlen : (D0L r A00 A11).length = r := by rw [D0L_length, h0, h1]; omega
  refine zsVal_sz_le hlen ?_
  intro x hx
  have h2 := D0L_mem_bound (r := r) (p := p)
    (deltaL_mem_bound (A := A00) (r := r) (p := p) hb0)
    (deltaL_mem_bound (A := A11) (r := r) (p := p) hb1) x hx
  omega

theorem D1L_size' {A01 A10 : List ℕ} {r p : ℕ} (h0 : A01.length = 2 * r)
    (h1 : A10.length = 2 * r) (hb0 : ∀ m, m < A01.length → A01.getD m 0 < 2 ^ (3 * p))
    (hb1 : ∀ m, m < A10.length → A10.getD m 0 < 2 ^ (3 * p)) :
    vsz (zsVal (D1L r A01 A10)) ≤ 5 * ((r + 1) * (p + 1) ^ 2) := by
  have hlen : (D1L r A01 A10).length = r := by rw [D1L_length, h0, h1]; omega
  refine zsVal_sz_le hlen ?_
  intro x hx
  have h2 := D1L_mem_bound (r := r) (p := p)
    (deltaL_mem_bound (A := A01) (r := r) (p := p) hb0)
    (deltaL_mem_bound (A := A10) (r := r) (p := p) hb1) x hx
  omega

theorem getD_mem_of_lt' {l : List ℤ} {j : ℕ} (hj : j < l.length) : l.getD j 0 ∈ l := by
  rw [List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem hj

theorem zsVal_eq_ofList (l : List ℤ) : zsVal l = ofList (List.map Val.int l) := rfl

/-! ## `combineDBody`: the D0/D1 combination `Δ A00 - Δ A11`, `Δ A01 + Δ A10` -/

theorem combineDBody (hK : HvdH.KernelLib) (hI : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ),
      ∀ (main : HvdH.Cmd) (p r : ℕ) (A00 A11 A01 A10 : List ℕ) (V : List HvdH.Val),
        A00.length = 2 * r → A11.length = 2 * r → A01.length = 2 * r → A10.length = 2 * r →
        (∀ m, m < 2 * r → A00.getD m 0 < 2 ^ (3 * p)) →
        (∀ m, m < 2 * r → A11.getD m 0 < 2 ^ (3 * p)) →
        (∀ m, m < 2 * r → A01.getD m 0 < 2 ^ (3 * p)) →
        (∀ m, m < 2 * r → A10.getD m 0 < 2 ^ (3 * p)) →
        2 ≤ r → 1 ≤ p →
        HvdH.WordR main prog
          (fun vs => vs = HvdH.ofList [zsVal (deltaL A00 r), zsVal (deltaL A11 r),
              zsVal (deltaL A01 r), zsVal (deltaL A10 r)] :: V)
          (fun _ out => out = zsVal (D0L r A00 A11) :: zsVal (D1L r A01 A10) :: V)
          (fun _ => K * ((r + 1) * (p + 1) ^ 2)) := by
  obtain ⟨uncP, UK, hunc⟩ := hK.unconsV
  obtain ⟨rollP, ROK, hroll⟩ := hK.roll
  obtain ⟨dropP, DRK, hdrop⟩ := hK.drop
  obtain ⟨swapP, SWK, hswap⟩ := hK.swap
  obtain ⟨zipP, ZK, hzip⟩ := hK.zipWith
  obtain ⟨permP, Kr, hperm⟩ := Work.ConvR.permTop hK
  obtain ⟨subP, SUK, hsub⟩ := hI.sub
  obtain ⟨addP, ADK, hadd⟩ := hI.add
  refine ⟨List.foldl (fun a b => Cmd.seq a b) Cmd.skip
    [uncP, rollP 1, uncP, rollP 1, uncP, rollP 1, uncP, rollP 1, dropP, permP [3, 2, 1, 0],
      zipP subP, permP [1, 2, 0], zipP addP, swapP],
    14 * (100000 * (UK + ROK + DRK + SWK + ZK + Kr + SUK + ADK + 1)) + 1, ?_⟩
  intro main p r A00 A11 A01 A10 V hA00 hA11 hA01 hA10 hb00 hb11 hb01 hb10 hr hp
  set BIG : ℕ := 100000 * (UK + ROK + DRK + SWK + ZK + Kr + SUK + ADK + 1) with hBIG
  obtain ⟨hX1, hpX, hrX, hp1X, hr1X, hrpX, hp2X, hrp1X⟩ := Xge r p
  have hX12 : 12 ≤ (r + 1) * (p + 1) ^ 2 := by
    have h1 : 3 ≤ r + 1 := by omega
    have h2 : 4 ≤ (p + 1) ^ 2 := by nlinarith
    calc 12 = 3 * 4 := by norm_num
      _ ≤ (r + 1) * (p + 1) ^ 2 := Nat.mul_le_mul h1 h2
  set z1 : Val := zsVal (deltaL A00 r) with hz1
  set z2 : Val := zsVal (deltaL A11 r) with hz2
  set z3 : Val := zsVal (deltaL A01 r) with hz3
  set z4 : Val := zsVal (deltaL A10 r) with hz4
  set D0 : Val := zsVal (D0L r A00 A11) with hD0
  set D1 : Val := zsVal (D1L r A01 A10) with hD1
  set L8 : ℕ := 8 * (p + 1) with hL8def
  have hs1 : vsz z1 ≤ 5 * ((r + 1) * (p + 1) ^ 2) := by
    rw [hz1]; exact zsVal_size' hA00 (fun m hm => hb00 m (by omega))
  have hs2 : vsz z2 ≤ 5 * ((r + 1) * (p + 1) ^ 2) := by
    rw [hz2]; exact zsVal_size' hA11 (fun m hm => hb11 m (by omega))
  have hs3 : vsz z3 ≤ 5 * ((r + 1) * (p + 1) ^ 2) := by
    rw [hz3]; exact zsVal_size' hA01 (fun m hm => hb01 m (by omega))
  have hs4 : vsz z4 ≤ 5 * ((r + 1) * (p + 1) ^ 2) := by
    rw [hz4]; exact zsVal_size' hA10 (fun m hm => hb10 m (by omega))
  have hD0s : vsz D0 ≤ 5 * ((r + 1) * (p + 1) ^ 2) := by
    rw [hD0]; exact D0L_size' hA00 hA11 (fun m hm => hb00 m (by omega)) (fun m hm => hb11 m (by omega))
  have hD1s : vsz D1 ≤ 5 * ((r + 1) * (p + 1) ^ 2) := by
    rw [hD1]; exact D1L_size' hA01 hA10 (fun m hm => hb01 m (by omega)) (fun m hm => hb10 m (by omega))
  have hUB : UK ≤ BIG := by omega
  have hRoB : ROK ≤ BIG := by omega
  have hDrB : DRK ≤ BIG := by omega
  have hSwB : SWK ≤ BIG := by omega
  have hZkB : ZK ≤ BIG := by omega
  have hKrB : Kr ≤ BIG := by omega
  have hSuB : SUK ≤ BIG := by omega
  have hAdB : ADK ≤ BIG := by omega
  set m1 : Val := ofList [z2, z3, z4] with hm1
  set m2 : Val := ofList [z3, z4] with hm2
  set m3 : Val := ofList [z4] with hm3
  have hs_m1 : vsz m1 ≤ 16 * ((r + 1) * (p + 1) ^ 2) := by
    rw [hm1, Work.ConvR.vsz_ofList]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    linarith [hs2, hs3, hs4, hX12]
  have hs_m2 : vsz m2 ≤ 16 * ((r + 1) * (p + 1) ^ 2) := by
    rw [hm2, Work.ConvR.vsz_ofList]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    linarith [hs3, hs4, hX12]
  have hs_m3 : vsz m3 ≤ 16 * ((r + 1) * (p + 1) ^ 2) := by
    rw [hm3, Work.ConvR.vsz_ofList]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    linarith [hs4, hX12]
  have hnil : vsz (Val.nil) = 1 := rfl
  have s1 : Work.ConvR.WordC main uncP (fun vs => vs = ofList [z1, z2, z3, z4] :: V)
      (fun _ out => out = z1 :: m1 :: V) (BIG * ((r + 1) * (p + 1) ^ 2)) := by
    refine wc_unc (hunc main) z1 (ofList [z2, z3, z4]) V _ ?_
    exact le_trans hUB (by nlinarith [hX1])
  have s2 : Work.ConvR.WordC main (rollP 1) (fun vs => vs = z1 :: m1 :: V)
      (fun _ out => out = m1 :: z1 :: V) (BIG * ((r + 1) * (p + 1) ^ 2)) := by
    refine wc_roll (hroll main) (z1 :: m1 :: V) 1 (by simp) _ ?_
    refine costStepL (c := 60) ?_ (by omega)
    simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, Work.ConvR.vsz_int]
    linarith [hs1, hs_m1, hX12]
  have s3 : Work.ConvR.WordC main uncP (fun vs => vs = m1 :: z1 :: V)
      (fun _ out => out = z2 :: m2 :: z1 :: V) (BIG * ((r + 1) * (p + 1) ^ 2)) := by
    refine wc_unc (hunc main) z2 (ofList [z3, z4]) (z1 :: V) _ ?_
    exact le_trans hUB (by nlinarith [hX1])
  have s4 : Work.ConvR.WordC main (rollP 1) (fun vs => vs = z2 :: m2 :: z1 :: V)
      (fun _ out => out = m2 :: z2 :: z1 :: V) (BIG * ((r + 1) * (p + 1) ^ 2)) := by
    refine wc_roll (hroll main) (z2 :: m2 :: z1 :: V) 1 (by simp) _ ?_
    refine costStepL (c := 60) ?_ (by omega)
    simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, Work.ConvR.vsz_int]
    linarith [hs2, hs_m2, hX12]
  have s5 : Work.ConvR.WordC main uncP (fun vs => vs = m2 :: z2 :: z1 :: V)
      (fun _ out => out = z3 :: m3 :: z2 :: z1 :: V) (BIG * ((r + 1) * (p + 1) ^ 2)) := by
    refine wc_unc (hunc main) z3 (ofList [z4]) (z2 :: z1 :: V) _ ?_
    exact le_trans hUB (by nlinarith [hX1])
  have s6 : Work.ConvR.WordC main (rollP 1) (fun vs => vs = z3 :: m3 :: z2 :: z1 :: V)
      (fun _ out => out = m3 :: z3 :: z2 :: z1 :: V) (BIG * ((r + 1) * (p + 1) ^ 2)) := by
    refine wc_roll (hroll main) (z3 :: m3 :: z2 :: z1 :: V) 1 (by simp) _ ?_
    refine costStepL (c := 60) ?_ (by omega)
    simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, Work.ConvR.vsz_int]
    linarith [hs3, hs_m3, hX12]
  have s7 : Work.ConvR.WordC main uncP (fun vs => vs = m3 :: z3 :: z2 :: z1 :: V)
      (fun _ out => out = z4 :: Val.nil :: z3 :: z2 :: z1 :: V)
      (BIG * ((r + 1) * (p + 1) ^ 2)) := by
    refine wc_unc (hunc main) z4 Val.nil (z3 :: z2 :: z1 :: V) _ ?_
    exact le_trans hUB (by nlinarith [hX1])
  have s7b : Work.ConvR.WordC main (rollP 1)
      (fun vs => vs = z4 :: Val.nil :: z3 :: z2 :: z1 :: V)
      (fun _ out => out = Val.nil :: z4 :: z3 :: z2 :: z1 :: V)
      (BIG * ((r + 1) * (p + 1) ^ 2)) := by
    refine wc_roll (hroll main) (z4 :: Val.nil :: z3 :: z2 :: z1 :: V) 1 (by simp) _ ?_
    refine costStepL (c := 1024) ?_ (by omega)
    simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil]
    rw [hnil]
    linarith [hs4, hX12]
  have s8 : Work.ConvR.WordC main dropP (fun vs => vs = Val.nil :: z4 :: z3 :: z2 :: z1 :: V)
      (fun _ out => out = z4 :: z3 :: z2 :: z1 :: V) (BIG * ((r + 1) * (p + 1) ^ 2)) := by
    refine wc_drop (hdrop main) Val.nil (z4 :: z3 :: z2 :: z1 :: V) _ ?_
    refine costKc (c := 1024) ?_ (by omega)
    rw [hnil]; linarith [hX12]
  have s9 : Work.ConvR.WordC main (permP [3, 2, 1, 0])
      (fun vs => vs = z4 :: z3 :: z2 :: z1 :: V) (fun _ out => out = z1 :: z2 :: z3 :: z4 :: V)
      (BIG * ((r + 1) * (p + 1) ^ 2)) := by
    refine wc_perm (hperm main) [3, 2, 1, 0] [z4, z3, z2, z1] V 4 _ (by simp) (by simp)
      (by decide) ?_
    refine costStepL (c := 1024) ?_ (by omega)
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    linarith [hs1, hs2, hs3, hs4, hX1]
  let hP1 : Val → Val → Prop := fun x y => ∃ a b, x = Val.int a ∧ y = Val.int b ∧
    (a.natAbs ≤ 2 ^ (3 * p) ∧ b.natAbs ≤ 2 ^ (3 * p)) ∧ isz a ≤ L8 ∧ isz b ≤ L8
  have hsuP : BinOp main subP (fun a b : ℤ => a.natAbs ≤ 2 ^ (3 * p) ∧ b.natAbs ≤ 2 ^ (3 * p))
      (fun a b => a - b) (fun a b => SUK * (isz a + isz b)) :=
    binOp_ss (hsub main) (fun _ _ _ => trivial)
  have hbody1 : ∀ x y, hP1 x y →
      WordR main subP (fun vs => vs = x :: y :: z3 :: z4 :: V)
        (fun _ out => ∃ z, out = z :: z3 :: z4 :: V ∧
          (∃ a b, x = Val.int a ∧ y = Val.int b ∧ z = Val.int (a - b)) ∧ vsz z ≤ L8)
        (fun _ => SUK * (2 * L8)) := by
    intro x y hxy
    exact zipBody (z3 :: z4 :: V) hsuP (c := SUK * (2 * L8)) (L := L8) (le_rfl)
      (fun a b hP _ _ => by
        have h1 := int_natAbs_sub_le' hP.1 hP.2
        have h2 := Work.ConvR.isz_le_of_natAbs_le h1
        simp only [hL8def] at h2 ⊢
        omega) x y hxy
  have hz1len : (deltaL A00 r).length = (deltaL A11 r).length := by
    rw [deltaL_length, deltaL_length, hA00, hA11]
  have hPmem1 : ∀ i, i < (List.map Val.int (deltaL A00 r)).length →
      hP1 ((List.map Val.int (deltaL A00 r)).getD i .nil)
        ((List.map Val.int (deltaL A11 r)).getD i .nil) := by
    intro i hi
    have hi1 : i < (deltaL A00 r).length := by simpa [List.length_map] using hi
    have hi2 : i < (deltaL A11 r).length := by rw [← hz1len]; exact hi1
    refine ⟨(deltaL A00 r).getD i 0, (deltaL A11 r).getD i 0, ?_, ?_, ⟨?_, ?_⟩, ?_, ?_⟩
    · exact getD_map_int hi1
    · exact getD_map_int hi2
    · exact deltaL_mem_bound (A := A00) (r := r) (p := p) (fun m hm => hb00 m (by omega))
        _ (getD_mem_of_lt' hi1)
    · exact deltaL_mem_bound (A := A11) (r := r) (p := p) (fun m hm => hb11 m (by omega))
        _ (getD_mem_of_lt' hi2)
    · have h := deltaL_mem_bound (A := A00) (r := r) (p := p) (fun m hm => hb00 m (by omega))
        _ (getD_mem_of_lt' hi1)
      have h2 := Work.ConvR.isz_le_of_natAbs_le (p := 3 * p) h
      simp only [hL8def] at h2 ⊢; omega
    · have h := deltaL_mem_bound (A := A11) (r := r) (p := p) (fun m hm => hb11 m (by omega))
        _ (getD_mem_of_lt' hi2)
      have h2 := Work.ConvR.isz_le_of_natAbs_le (p := 3 * p) h
      simp only [hL8def] at h2 ⊢; omega
  have hLmem1 : ∀ x ∈ (List.map Val.int (deltaL A00 r) ++ List.map Val.int (deltaL A11 r)),
      vsz x ≤ L8 := by
    intro x hx
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
      have hi1 : i < (deltaL A00 r).length := by simpa [List.length_map] using hi
      rw [List.getElem_map, Work.ConvR.vsz_int, ← List.getD_eq_getElem (deltaL A00 r) 0 hi1]
      have h := deltaL_mem_bound (A := A00) (r := r) (p := p) (fun m hm => hb00 m (by omega))
        _ (getD_mem_of_lt' hi1)
      have h2 := Work.ConvR.isz_le_of_natAbs_le (p := 3 * p) h
      simp only [hL8def] at h2 ⊢; omega
    · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
      have hi2 : i < (deltaL A11 r).length := by simpa [List.length_map] using hi
      rw [List.getElem_map, Work.ConvR.vsz_int, ← List.getD_eq_getElem (deltaL A11 r) 0 hi2]
      have h := deltaL_mem_bound (A := A11) (r := r) (p := p) (fun m hm => hb11 m (by omega))
        _ (getD_mem_of_lt' hi2)
      have h2 := Work.ConvR.isz_le_of_natAbs_le (p := 3 * p) h
      simp only [hL8def] at h2 ⊢; omega
  have hzp1 := hzip main subP (z3 :: z4 :: V) hP1
    (fun x y z => ∃ a b, x = Val.int a ∧ y = Val.int b ∧ z = Val.int (a - b))
    (SUK * (2 * L8)) L8 hbody1 (List.map Val.int (deltaL A00 r)) (List.map Val.int (deltaL A11 r))
    (by rw [List.length_map, List.length_map, hz1len]) hPmem1 hLmem1
  have zz1 : Work.ConvR.WordC main (zipP subP)
      (fun vs => vs = z1 :: z2 :: z3 :: z4 :: V)
      (fun _ out => out = D0 :: z3 :: z4 :: V) (BIG * ((r + 1) * (p + 1) ^ 2)) := by
    refine wc_conseq' (wc_ofWordR hzp1 ?_) ?_ ?_
    · intro vs hvs
      rw [show (List.map Val.int (deltaL A00 r)).length = r from by rw [List.length_map, deltaL_length, hA00]; omega]
      have h2L : 2 * L8 ≤ 26 * (p + 1) := by simp only [hL8def]; omega
      have hL1 : L8 + 1 ≤ 11 * (p + 1) := by simp only [hL8def]; omega
      have hrp' : r * (p + 1) ≤ (r + 1) * (p + 1) ^ 2 := by nlinarith
      have hSB : 26 * SUK + 12 * ZK ≤ BIG := by omega
      calc r * (SUK * (2 * L8) + ZK * (L8 + 1)) + ZK
          ≤ r * (SUK * (26 * (p + 1)) + ZK * (11 * (p + 1))) + ZK := by
            apply Nat.add_le_add_right
            apply Nat.mul_le_mul_left
            exact Nat.add_le_add (Nat.mul_le_mul_left _ h2L) (Nat.mul_le_mul_left _ hL1)
        _ = 26 * SUK * (r * (p + 1)) + 11 * ZK * (r * (p + 1)) + ZK := by ring
        _ ≤ 26 * SUK * ((r + 1) * (p + 1) ^ 2) + 11 * ZK * ((r + 1) * (p + 1) ^ 2)
              + ZK * ((r + 1) * (p + 1) ^ 2) := by
            refine Nat.add_le_add (Nat.add_le_add ?_ ?_) ?_
            · exact Nat.mul_le_mul_left _ hrp'
            · exact Nat.mul_le_mul_left _ hrp'
            · calc ZK = ZK * 1 := (Nat.mul_one ZK).symm
                _ ≤ ZK * ((r + 1) * (p + 1) ^ 2) := Nat.mul_le_mul_left _ hX1
        _ = (26 * SUK + 12 * ZK) * ((r + 1) * (p + 1) ^ 2) := by ring
        _ ≤ BIG * ((r + 1) * (p + 1) ^ 2) := Nat.mul_le_mul_right _ hSB
    · intro vs hvs
      rw [hvs, hz1, hz2, zsVal_eq_ofList, zsVal_eq_ofList]
      try rfl
    · intro vs out hvs hQ
      obtain ⟨zs, hout, hzlen, hzs⟩ := hQ
      rw [hout, hD0]
      congr 1
      have hlen1 : (deltaL A00 r).length = (deltaL A11 r).length := hz1len
      have hlen2 : zs.length = (deltaL A00 r).length := by rw [hzlen, List.length_map]
      have hpoint : ∀ i, i < (deltaL A00 r).length →
          zs.getD i .nil = Val.int ((· - ·) ((deltaL A00 r).getD i 0) ((deltaL A11 r).getD i 0)) := by
        intro i hi
        have hi' : i < (List.map Val.int (deltaL A00 r)).length := by simpa [List.length_map] using hi
        obtain ⟨a, b, ha, hb2, hf⟩ := hzs i hi'
        have ha' : a = (deltaL A00 r).getD i 0 := by
          apply (Val.int.injEq a _).mp
          rw [← ha, getD_map_int hi]
        have hb' : b = (deltaL A11 r).getD i 0 := by
          apply (Val.int.injEq b _).mp
          rw [← hb2, getD_map_int (by rw [← hz1len]; exact hi)]
        rw [hf, ha', hb']
      have hmain := zipWith_int_eq (f := (· - ·)) hlen1 hlen2 hpoint
      rw [hmain]
      try rfl
  have s10 : Work.ConvR.WordC main (permP [1, 2, 0])
      (fun vs => vs = D0 :: z3 :: z4 :: V) (fun _ out => out = z3 :: z4 :: D0 :: V)
      (BIG * ((r + 1) * (p + 1) ^ 2)) := by
    refine wc_perm (hperm main) [1, 2, 0] [D0, z3, z4] V 3 _ (by simp) (by simp) (by decide) ?_
    refine costStepL (c := 1024) ?_ (by omega)
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    linarith [hD0s, hs3, hs4, hX1]
  let hP2 : Val → Val → Prop := fun x y => ∃ a b, x = Val.int a ∧ y = Val.int b ∧
    (a.natAbs ≤ 2 ^ (3 * p) ∧ b.natAbs ≤ 2 ^ (3 * p)) ∧ isz a ≤ L8 ∧ isz b ≤ L8
  have haddP : BinOp main addP (fun a b : ℤ => a.natAbs ≤ 2 ^ (3 * p) ∧ b.natAbs ≤ 2 ^ (3 * p))
      (fun a b => a + b) (fun a b => ADK * (isz a + isz b)) :=
    binOp_ss (hadd main) (fun _ _ _ => trivial)
  have hbody2 : ∀ x y, hP2 x y →
      WordR main addP (fun vs => vs = x :: y :: D0 :: V)
        (fun _ out => ∃ z, out = z :: D0 :: V ∧
          (∃ a b, x = Val.int a ∧ y = Val.int b ∧ z = Val.int (a + b)) ∧ vsz z ≤ L8)
        (fun _ => ADK * (2 * L8)) := by
    intro x y hxy
    exact zipBody (D0 :: V) haddP (c := ADK * (2 * L8)) (L := L8) (le_rfl)
      (fun a b hP _ _ => by
        have h1 := int_natAbs_add_le' hP.1 hP.2
        have h2 := Work.ConvR.isz_le_of_natAbs_le h1
        simp only [hL8def] at h2 ⊢
        omega) x y hxy
  have hz2len : (deltaL A01 r).length = (deltaL A10 r).length := by
    rw [deltaL_length, deltaL_length, hA01, hA10]
  have hPmem2 : ∀ i, i < (List.map Val.int (deltaL A01 r)).length →
      hP2 ((List.map Val.int (deltaL A01 r)).getD i .nil)
        ((List.map Val.int (deltaL A10 r)).getD i .nil) := by
    intro i hi
    have hi1 : i < (deltaL A01 r).length := by simpa [List.length_map] using hi
    have hi2 : i < (deltaL A10 r).length := by rw [← hz2len]; exact hi1
    refine ⟨(deltaL A01 r).getD i 0, (deltaL A10 r).getD i 0, ?_, ?_, ⟨?_, ?_⟩, ?_, ?_⟩
    · exact getD_map_int hi1
    · exact getD_map_int hi2
    · exact deltaL_mem_bound (A := A01) (r := r) (p := p) (fun m hm => hb01 m (by omega))
        _ (getD_mem_of_lt' hi1)
    · exact deltaL_mem_bound (A := A10) (r := r) (p := p) (fun m hm => hb10 m (by omega))
        _ (getD_mem_of_lt' hi2)
    · have h := deltaL_mem_bound (A := A01) (r := r) (p := p) (fun m hm => hb01 m (by omega))
        _ (getD_mem_of_lt' hi1)
      have h2 := Work.ConvR.isz_le_of_natAbs_le (p := 3 * p) h
      simp only [hL8def] at h2 ⊢; omega
    · have h := deltaL_mem_bound (A := A10) (r := r) (p := p) (fun m hm => hb10 m (by omega))
        _ (getD_mem_of_lt' hi2)
      have h2 := Work.ConvR.isz_le_of_natAbs_le (p := 3 * p) h
      simp only [hL8def] at h2 ⊢; omega
  have hLmem2 : ∀ x ∈ (List.map Val.int (deltaL A01 r) ++ List.map Val.int (deltaL A10 r)),
      vsz x ≤ L8 := by
    intro x hx
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
      have hi1 : i < (deltaL A01 r).length := by simpa [List.length_map] using hi
      rw [List.getElem_map, Work.ConvR.vsz_int, ← List.getD_eq_getElem (deltaL A01 r) 0 hi1]
      have h := deltaL_mem_bound (A := A01) (r := r) (p := p) (fun m hm => hb01 m (by omega))
        _ (getD_mem_of_lt' hi1)
      have h2 := Work.ConvR.isz_le_of_natAbs_le (p := 3 * p) h
      simp only [hL8def] at h2 ⊢; omega
    · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
      have hi2 : i < (deltaL A10 r).length := by simpa [List.length_map] using hi
      rw [List.getElem_map, Work.ConvR.vsz_int, ← List.getD_eq_getElem (deltaL A10 r) 0 hi2]
      have h := deltaL_mem_bound (A := A10) (r := r) (p := p) (fun m hm => hb10 m (by omega))
        _ (getD_mem_of_lt' hi2)
      have h2 := Work.ConvR.isz_le_of_natAbs_le (p := 3 * p) h
      simp only [hL8def] at h2 ⊢; omega
  have hzp2 := hzip main addP (D0 :: V) hP2
    (fun x y z => ∃ a b, x = Val.int a ∧ y = Val.int b ∧ z = Val.int (a + b))
    (ADK * (2 * L8)) L8 hbody2 (List.map Val.int (deltaL A01 r)) (List.map Val.int (deltaL A10 r))
    (by rw [List.length_map, List.length_map, hz2len]) hPmem2 hLmem2
  have zz2 : Work.ConvR.WordC main (zipP addP)
      (fun vs => vs = z3 :: z4 :: D0 :: V) (fun _ out => out = D1 :: D0 :: V)
      (BIG * ((r + 1) * (p + 1) ^ 2)) := by
    refine wc_conseq' (wc_ofWordR hzp2 ?_) ?_ ?_
    · intro vs hvs
      rw [show (List.map Val.int (deltaL A01 r)).length = r from by rw [List.length_map, deltaL_length, hA01]; omega]
      have h2L : 2 * L8 ≤ 26 * (p + 1) := by simp only [hL8def]; omega
      have hL1 : L8 + 1 ≤ 11 * (p + 1) := by simp only [hL8def]; omega
      have hrp' : r * (p + 1) ≤ (r + 1) * (p + 1) ^ 2 := by nlinarith
      have hSB : 26 * ADK + 12 * ZK ≤ BIG := by omega
      calc r * (ADK * (2 * L8) + ZK * (L8 + 1)) + ZK
          ≤ r * (ADK * (26 * (p + 1)) + ZK * (11 * (p + 1))) + ZK := by
            apply Nat.add_le_add_right
            apply Nat.mul_le_mul_left
            exact Nat.add_le_add (Nat.mul_le_mul_left _ h2L) (Nat.mul_le_mul_left _ hL1)
        _ = 26 * ADK * (r * (p + 1)) + 11 * ZK * (r * (p + 1)) + ZK := by ring
        _ ≤ 26 * ADK * ((r + 1) * (p + 1) ^ 2) + 11 * ZK * ((r + 1) * (p + 1) ^ 2)
              + ZK * ((r + 1) * (p + 1) ^ 2) := by
            refine Nat.add_le_add (Nat.add_le_add ?_ ?_) ?_
            · exact Nat.mul_le_mul_left _ hrp'
            · exact Nat.mul_le_mul_left _ hrp'
            · calc ZK = ZK * 1 := (Nat.mul_one ZK).symm
                _ ≤ ZK * ((r + 1) * (p + 1) ^ 2) := Nat.mul_le_mul_left _ hX1
        _ = (26 * ADK + 12 * ZK) * ((r + 1) * (p + 1) ^ 2) := by ring
        _ ≤ BIG * ((r + 1) * (p + 1) ^ 2) := Nat.mul_le_mul_right _ hSB
    · intro vs hvs
      rw [hvs, hz3, hz4, zsVal_eq_ofList, zsVal_eq_ofList]
      try rfl
    · intro vs out hvs hQ
      obtain ⟨zs, hout, hzlen, hzs⟩ := hQ
      rw [hout, hD1]
      congr 1
      have hlen2 : zs.length = (deltaL A01 r).length := by rw [hzlen, List.length_map]
      have hpoint : ∀ i, i < (deltaL A01 r).length →
          zs.getD i .nil = Val.int ((· + ·) ((deltaL A01 r).getD i 0) ((deltaL A10 r).getD i 0)) := by
        intro i hi
        have hi' : i < (List.map Val.int (deltaL A01 r)).length := by simpa [List.length_map] using hi
        obtain ⟨a, b, ha, hb2, hf⟩ := hzs i hi'
        have ha' : a = (deltaL A01 r).getD i 0 := by
          apply (Val.int.injEq a _).mp
          rw [← ha, getD_map_int hi]
        have hb' : b = (deltaL A10 r).getD i 0 := by
          apply (Val.int.injEq b _).mp
          rw [← hb2, getD_map_int (by rw [← hz2len]; exact hi)]
        rw [hf, ha', hb']
      have hmain := zipWith_int_eq (f := (· + ·)) hz2len hlen2 hpoint
      rw [hmain]
      try rfl
  have s13 : Work.ConvR.WordC main swapP (fun vs => vs = D1 :: D0 :: V)
      (fun _ out => out = D0 :: D1 :: V) (BIG * ((r + 1) * (p + 1) ^ 2)) := by
    refine wc_swap (hswap main) D1 D0 V _ ?_
    refine costKc (c := 1024) ?_ (by omega)
    linarith [hD1s, hD0s, hX12]
  have hall : Work.ConvR.WordC main
      (List.foldl (fun a b => Cmd.seq a b) Cmd.skip
        [uncP, rollP 1, uncP, rollP 1, uncP, rollP 1, uncP, rollP 1, dropP, permP [3, 2, 1, 0],
          zipP subP, permP [1, 2, 0], zipP addP, swapP])
      (fun vs => vs = ofList [z1, z2, z3, z4] :: V)
      (fun _ out => out = D0 :: D1 :: V)
      (1 + 14 * (BIG * ((r + 1) * (p + 1) ^ 2))) := by
    have g0 := wc_skipN (main := main) (ofList [z1, z2, z3, z4] :: V) BIG
      ((r + 1) * (p + 1) ^ 2)
    have g1 := wc_chainN g0 s1
    have g2 := wc_chainN g1 s2
    have g3 := wc_chainN g2 s3
    have g4 := wc_chainN g3 s4
    have g5 := wc_chainN g4 s5
    have g6 := wc_chainN g5 s6
    have g7 := wc_chainN g6 s7
    have g7b := wc_chainN g7 s7b
    have g8 := wc_chainN g7b s8
    have g9 := wc_chainN g8 s9
    have g10 := wc_chainN g9 zz1
    have g11 := wc_chainN g10 s10
    have g12 := wc_chainN g11 zz2
    have g13 := wc_chainN g12 s13
    exact g13
  intro vs hvs s R hR
  obtain ⟨out, s', n, hQ, he, hn, hstk, hoth⟩ := hall vs hvs s R hR
  refine ⟨out, s', n, ?_, he, ?_, hstk, hoth⟩
  · rw [hQ, hD0, hD1]
    try rfl
  · refine le_trans hn ?_
    exact capBound (n := 14) (BIG := BIG) (X := ((r + 1) * (p + 1) ^ 2)) hX1

/-- `KernelLib.conseq` with all implicit arguments inferred -/
theorem wr_conseq {main : Cmd} {p : Cmd} {P P' : List Val → Prop}
    {Q Q' : List Val → List Val → Prop} {C C' : List Val → ℕ}
    (hK : HvdH.KernelLib) (h : WordR main p P Q C) (hP : ∀ vs, P' vs → P vs)
    (hQ : ∀ vs out, P' vs → Q vs out → Q' vs out) (hC : ∀ vs, P' vs → C vs ≤ C' vs) :
    WordR main p P' Q' C' :=
  hK.conseq main p P P' Q Q' C C' h hP hQ hC

theorem combine (hK : HvdH.KernelLib) (hI : HvdH.IntLib) (hL : HvdH.LayoutLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ),
      ∀ (main : HvdH.Cmd) (p r : ℕ) (A00 A01 A10 A11 : List ℕ) (rest : List HvdH.Val),
      A00.length = 2 * r → A01.length = 2 * r → A10.length = 2 * r → A11.length = 2 * r →
      (∀ A ∈ [A00, A01, A10, A11], ∀ m, m < 2 * r → A.getD m 0 < 2 ^ (3 * p)) →
      2 ≤ r → 1 ≤ p →
      HvdH.WordR main prog
        (fun vs => vs = HvdH.ofList [HvdH.intList A00, HvdH.intList A11, HvdH.intList A01,
              HvdH.intList A10] ::
            HvdH.Val.int (3 * p : ℤ) :: HvdH.Val.int (2 * r : ℤ) ::
            HvdH.Val.int (Work.KronP.digitOffset p (2 * r)) ::
            HvdH.Val.int ((2 : ℤ) ^ (p + Nat.clog 2 r)) ::
            HvdH.Val.int (p : ℤ) :: HvdH.Val.int (r : ℤ) :: rest)
        (fun _ out => out = HvdH.cvecVal (Work.KronP.kronW p r A00 A01 A10 A11) :: rest)
        (fun _ => K * (r + 1) * (p + 1) ^ 2) := by
  obtain ⟨permP, Kr, hperm⟩ := Work.ConvR.permTop hK
  obtain ⟨pickP, PK, hpick⟩ := hK.pick
  obtain ⟨swapP, SWK, hswap⟩ := hK.swap
  obtain ⟨mapP, MK, hmap⟩ := hK.mapList
  obtain ⟨zipP, ZK, hzip⟩ := hK.zipWith
  obtain ⟨duP, DuK, hdu⟩ := Work.ConvR.dropUnder hK
  obtain ⟨scProg, Ksc, hsc⟩ := shiftCapBody hK hI
  obtain ⟨dlProg, Kdl, hdl⟩ := deltaBody hK hI hL
  obtain ⟨cdProg, Kcd, hcd⟩ := combineDBody hK hI
  obtain ⟨pdProg, Kpd, hpd⟩ := pairDivBody hK hI
  refine ⟨List.foldl (fun a b => Cmd.seq a b) Cmd.skip
    [permP [5, 6, 0, 1, 2, 3, 4], pickP 1, swapP, scProg, permP [2, 1, 0, 3, 4, 5, 6],
      mapP dlProg, cdProg, permP [0, 1, 3, 2, 4, 5, 6, 7], zipP pdProg, duP, duP, duP],
    12 * (100000 * (Kr + PK + SWK + MK + ZK + DuK + Ksc + Kdl + Kcd + Kpd + 1)) + 1, ?_⟩
  intro main p r A00 A01 A10 A11 rest hA00 hA01 hA10 hA11 hball hr hp
  set BIG : ℕ := 100000 * (Kr + PK + SWK + MK + ZK + DuK + Ksc + Kdl + Kcd + Kpd + 1) with hBIG
  obtain ⟨hX1, hpX, hrX, hp1X, hr1X, hrpX, hp2X, hrp1X⟩ := Xge r p
  have hX12 : 12 ≤ (r + 1) * (p + 1) ^ 2 := by
    have h1 : 3 ≤ r + 1 := by omega
    have h2 : 4 ≤ (p + 1) ^ 2 := by nlinarith
    calc 12 = 3 * 4 := by norm_num
      _ ≤ (r + 1) * (p + 1) ^ 2 := Nat.mul_le_mul h1 h2
  have hb00 : ∀ m, m < 2 * r → A00.getD m 0 < 2 ^ (3 * p) := fun m hm => hball A00 (by simp) m hm
  have hb01 : ∀ m, m < 2 * r → A01.getD m 0 < 2 ^ (3 * p) := fun m hm => hball A01 (by simp) m hm
  have hb10 : ∀ m, m < 2 * r → A10.getD m 0 < 2 ^ (3 * p) := fun m hm => hball A10 (by simp) m hm
  have hb11 : ∀ m, m < 2 * r → A11.getD m 0 < 2 ^ (3 * p) := fun m hm => hball A11 (by simp) m hm
  set L0 : Val := ofList [intList A00, intList A11, intList A01, intList A10] with hL0
  set C3p : Val := Val.int (3 * (p : ℤ)) with hC3p
  set C2r : Val := Val.int (2 * (r : ℤ)) with hC2r
  set CC : Val := Val.int (digitOffset p (2 * r)) with hCC
  set CD : Val := Val.int ((2 : ℤ) ^ (p + Nat.clog 2 r)) with hCD
  set Cp : Val := Val.int (p : ℤ) with hCp
  set Cr : Val := Val.int (r : ℤ) with hCr
  set Ck : Val := Val.int (((min (p + Nat.clog 2 r) (3 * p + 3) : ℕ) : ℤ)) with hCk
  set Dl : Val := ofList [zsVal (deltaL A00 r), zsVal (deltaL A11 r), zsVal (deltaL A01 r),
    zsVal (deltaL A10 r)] with hDl
  set D0 : Val := zsVal (D0L r A00 A11) with hD0
  set D1 : Val := zsVal (D1L r A01 A10) with hD1
  set Res : Val := cvecVal (kronW p r A00 A01 A10 A11) with hRes
  have hsA00 : vsz (intList A00) ≤ 8 * ((r + 1) * (p + 1) ^ 2) := vsz_intList_le' hA00 hb00
  have hsA11 : vsz (intList A11) ≤ 8 * ((r + 1) * (p + 1) ^ 2) := vsz_intList_le' hA11 hb11
  have hsA01 : vsz (intList A01) ≤ 8 * ((r + 1) * (p + 1) ^ 2) := vsz_intList_le' hA01 hb01
  have hsA10 : vsz (intList A10) ≤ 8 * ((r + 1) * (p + 1) ^ 2) := vsz_intList_le' hA10 hb10
  have hsL0 : vsz L0 ≤ 37 * ((r + 1) * (p + 1) ^ 2) := by
    rw [hL0, Work.ConvR.vsz_ofList]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    linarith [hsA00, hsA11, hsA01, hsA10, hX1]
  have hC3p' : isz (3 * (p : ℤ)) ≤ 8 * ((r + 1) * (p + 1) ^ 2) := by
    have h := isz_natCast_le (3 * p)
    rw [cast_mul_int 3 p] at h
    nlinarith [h, hpX, hX1]
  have hC2r' : isz (2 * (r : ℤ)) ≤ 8 * ((r + 1) * (p + 1) ^ 2) := by
    have h := isz_natCast_le (2 * r)
    rw [cast_mul_int 2 r] at h
    nlinarith [h, hrX, hX1]
  have hCp' : isz (p : ℤ) ≤ 4 * ((r + 1) * (p + 1) ^ 2) := by
    have h := isz_natCast_le p; omega
  have hCr' : isz (r : ℤ) ≤ 4 * ((r + 1) * (p + 1) ^ 2) := by
    have h := isz_natCast_le r; omega
  have hCC' : isz (digitOffset p (2 * r)) ≤ 12 * ((r + 1) * (p + 1) ^ 2) := by
    have h := isz_digitOffset_le' p (2 * r) hp
    have h2 : (2 * r).size ≤ 2 * r := Nat.size_le.mpr (Nat.lt_two_pow_self (n := 2 * r))
    nlinarith [h, h2, hrX, hrpX, hX1]
  have hCD' : isz ((2 : ℤ) ^ (p + Nat.clog 2 r)) ≤ 8 * ((r + 1) * (p + 1) ^ 2) := by
    have hcl := clog2_le r
    have hsz : ((2 : ℤ) ^ (p + Nat.clog 2 r)).natAbs = 2 ^ (p + Nat.clog 2 r) := int_natAbs_pow2 _
    have h : ((2 : ℤ) ^ (p + Nat.clog 2 r)).natAbs.size ≤ p + Nat.clog 2 r + 1 := by
      rw [hsz]
      exact Nat.size_le.mpr (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self _))
    simp only [isz]
    omega
  have hCk' : isz (((min (p + Nat.clog 2 r) (3 * p + 3) : ℕ) : ℤ)) ≤ 8 * ((r + 1) * (p + 1) ^ 2) := by
    have h := isz_natCast_le (min (p + Nat.clog 2 r) (3 * p + 3))
    have h2 : min (p + Nat.clog 2 r) (3 * p + 3) ≤ 3 * p + 3 := Nat.min_le_right _ _
    nlinarith [h, h2, hpX, hX1]
  have hsD0 : vsz D0 ≤ 5 * ((r + 1) * (p + 1) ^ 2) := by
    rw [hD0]
    exact D0L_size' hA00 hA11 (fun m hm => hb00 m (by omega)) (fun m hm => hb11 m (by omega))
  have hsD1 : vsz D1 ≤ 5 * ((r + 1) * (p + 1) ^ 2) := by
    rw [hD1]
    exact D1L_size' hA01 hA10 (fun m hm => hb01 m (by omega)) (fun m hm => hb10 m (by omega))
  have hsDl : vsz Dl ≤ 25 * ((r + 1) * (p + 1) ^ 2) := by
    rw [hDl, Work.ConvR.vsz_ofList]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    have h1 : vsz (zsVal (deltaL A00 r)) ≤ 5 * ((r + 1) * (p + 1) ^ 2) :=
      zsVal_size' hA00 (fun m hm => hb00 m (by omega))
    have h2 : vsz (zsVal (deltaL A11 r)) ≤ 5 * ((r + 1) * (p + 1) ^ 2) :=
      zsVal_size' hA11 (fun m hm => hb11 m (by omega))
    have h3 : vsz (zsVal (deltaL A01 r)) ≤ 5 * ((r + 1) * (p + 1) ^ 2) :=
      zsVal_size' hA01 (fun m hm => hb01 m (by omega))
    have h4 : vsz (zsVal (deltaL A10 r)) ≤ 5 * ((r + 1) * (p + 1) ^ 2) :=
      zsVal_size' hA10 (fun m hm => hb10 m (by omega))
    linarith [h1, h2, h3, h4, hX1]
  have hkronlen : (kronW p r A00 A01 A10 A11).length = r := by
    rw [kronW_length, D0L_length, D1L_length, hA00, hA11, hA01, hA10]; omega
  have hsRes : vsz Res ≤ 12 * ((r + 1) * (p + 1) ^ 2) := by
    rw [hRes]
    refine cvecVal_sz_le hkronlen ?_
    intro z hz
    exact kronW_mem_bound
      (D0L_mem_bound (deltaL_mem_bound (A := A00) (r := r) (p := p) (fun m hm => hb00 m (by omega)))
        (deltaL_mem_bound (A := A11) (r := r) (p := p) (fun m hm => hb11 m (by omega))))
      (D1L_mem_bound (deltaL_mem_bound (A := A01) (r := r) (p := p) (fun m hm => hb01 m (by omega)))
        (deltaL_mem_bound (A := A10) (r := r) (p := p) (fun m hm => hb10 m (by omega)))) z hz
  have hKrB : Kr ≤ BIG := by omega
  have hPkB : PK ≤ BIG := by omega
  have hSwB : SWK ≤ BIG := by omega
  have hMkB : MK ≤ BIG := by omega
  have hZkB : ZK ≤ BIG := by omega
  have hDuB : DuK ≤ BIG := by omega
  have hScB : Ksc ≤ BIG := by omega
  have hDlB : Kdl ≤ BIG := by omega
  have hCdB : Kcd ≤ BIG := by omega
  have hPdB : Kpd ≤ BIG := by omega
  have st1 : Work.ConvR.WordC main (permP [5, 6, 0, 1, 2, 3, 4])
      (fun vs => vs = L0 :: C3p :: C2r :: CC :: CD :: Cp :: Cr :: rest)
      (fun _ out => out = Cp :: Cr :: L0 :: C3p :: C2r :: CC :: CD :: rest)
      (BIG * ((r + 1) * (p + 1) ^ 2)) := by
    refine wc_perm (hperm main) [5, 6, 0, 1, 2, 3, 4] [L0, C3p, C2r, CC, CD, Cp, Cr] rest 7
      _ (by simp) (by simp) (by decide) ?_
    refine costStepL (c := 10000) ?_ (by omega)
    simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil]
    rw [hC3p, hC2r, hCC, hCD, hCp, hCr]
    simp only [Work.ConvR.vsz_int]
    nlinarith [hsL0, hC3p', hC2r', hCC', hCD', hCp', hCr', hX12]
  have st2 : Work.ConvR.WordC main (pickP 1)
      (fun vs => vs = Cp :: Cr :: L0 :: C3p :: C2r :: CC :: CD :: rest)
      (fun _ out => out = Cr :: Cp :: Cr :: L0 :: C3p :: C2r :: CC :: CD :: rest)
      (BIG * ((r + 1) * (p + 1) ^ 2)) := by
    refine wc_pick (hpick main) (Cp :: Cr :: L0 :: C3p :: C2r :: CC :: CD :: rest) 1
      (by simp) _ ?_
    refine costStepL (c := 10000) ?_ (by omega)
    simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil]
    rw [hCp, hCr]
    simp only [Work.ConvR.vsz_int]
    linarith [hCp', hCr', hX12]
  have st3 : Work.ConvR.WordC main swapP
      (fun vs => vs = Cr :: Cp :: Cr :: L0 :: C3p :: C2r :: CC :: CD :: rest)
      (fun _ out => out = Cp :: Cr :: Cr :: L0 :: C3p :: C2r :: CC :: CD :: rest)
      (BIG * ((r + 1) * (p + 1) ^ 2)) := by
    refine wc_swap (hswap main) Cr Cp (Cr :: L0 :: C3p :: C2r :: CC :: CD :: rest) _ ?_
    refine costKc (c := 1024) ?_ (by omega)
    rw [hCp, hCr]
    simp only [Work.ConvR.vsz_int]
    linarith [hCp', hCr', hX12]
  have st4 : Work.ConvR.WordC main scProg
      (fun vs => vs = Cp :: Cr :: Cr :: L0 :: C3p :: C2r :: CC :: CD :: rest)
      (fun _ out => out = Ck :: Cr :: L0 :: C3p :: C2r :: CC :: CD :: rest)
      (BIG * ((r + 1) * (p + 1) ^ 2)) := by
    have h1 := hsc main p r (Cr :: L0 :: C3p :: C2r :: CC :: CD :: rest) hp
    refine wc_conseq' (wc_ofWordR h1 ?_) ?_ ?_
    · intro vs hvs
      exact costKc (c := 1) (by omega) (by omega)
    · intro vs hvs
      rw [hvs, hCp, hCr]
      try rfl
    · intro vs out hvs hQ
      rw [hQ, hCk]
      try rfl
  have st5 : Work.ConvR.WordC main (permP [2, 1, 0, 3, 4, 5, 6])
      (fun vs => vs = Ck :: Cr :: L0 :: C3p :: C2r :: CC :: CD :: rest)
      (fun _ out => out = L0 :: Cr :: Ck :: C3p :: C2r :: CC :: CD :: rest)
      (BIG * ((r + 1) * (p + 1) ^ 2)) := by
    refine wc_perm (hperm main) [2, 1, 0, 3, 4, 5, 6] [Ck, Cr, L0, C3p, C2r, CC, CD] rest 7
      _ (by simp) (by simp) (by decide) ?_
    refine costStepL (c := 10000) ?_ (by omega)
    simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil]
    rw [hCk, hCr, hC3p, hC2r, hCC, hCD]
    simp only [Work.ConvR.vsz_int]
    nlinarith [hCk', hCr', hsL0, hC3p', hC2r', hCC', hCD', hX12]
  have hbody : ∀ x, (∃ A, x = intList A ∧ A.length = 2 * r ∧
        (∀ m, m < A.length → A.getD m 0 < 2 ^ (3 * p))) →
      WordR main dlProg (fun vs => vs = x :: (Cr :: Ck :: C3p :: C2r :: CC :: CD :: rest))
        (fun _ out => ∃ y, out = y :: (Cr :: Ck :: C3p :: C2r :: CC :: CD :: rest) ∧
          (∃ A, x = intList A ∧ A.length = 2 * r ∧
            (∀ m, m < A.length → A.getD m 0 < 2 ^ (3 * p)) ∧ y = zsVal (deltaL A r)) ∧
          vsz y ≤ 8 * ((r + 1) * (p + 1) ^ 2))
        (fun _ => Kdl * ((r + 1) * (p + 1) ^ 2)) := by
    intro x hx
    obtain ⟨A, hxA, hAlen, hAb⟩ := hx
    have h1 := hdl main p r A (Ck :: C3p :: C2r :: CC :: CD :: rest) hAlen
      (fun m hm => hAb m (by rw [hAlen]; exact hm)) hr hp
    refine wr_conseq hK h1 ?_ ?_ ?_
    · intro vs hvs
      rw [hvs, hxA, intList_eq_map, hCr]
      try rfl
    · intro vs out hvs hQ
      refine ⟨ofList ((deltaL A r).map Val.int), ?_, ⟨A, hxA, hAlen, hAb, ?_⟩, ?_⟩
      · rw [hQ, hCr]
        try rfl
      · rw [← zsVal_eq_ofList]
      · rw [← zsVal_eq_ofList]
        exact le_trans (zsVal_size' hAlen hAb) (by nlinarith [hX1])
    · intro vs hvs
      exact le_rfl
  have hxs : ∀ x ∈ [intList A00, intList A11, intList A01, intList A10],
      (∃ A, x = intList A ∧ A.length = 2 * r ∧ (∀ m, m < A.length → A.getD m 0 < 2 ^ (3 * p))) ∧
      vsz x ≤ 8 * ((r + 1) * (p + 1) ^ 2) := by
    intro x hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with hx | hx | hx | hx
    · subst hx
      exact ⟨⟨A00, rfl, hA00, fun m hm => hb00 m (by omega)⟩, hsA00⟩
    · subst hx
      exact ⟨⟨A11, rfl, hA11, fun m hm => hb11 m (by omega)⟩, hsA11⟩
    · subst hx
      exact ⟨⟨A01, rfl, hA01, fun m hm => hb01 m (by omega)⟩, hsA01⟩
    · subst hx
      exact ⟨⟨A10, rfl, hA10, fun m hm => hb10 m (by omega)⟩, hsA10⟩
  have hmapres := hmap main dlProg (Cr :: Ck :: C3p :: C2r :: CC :: CD :: rest)
    (fun x => ∃ A, x = intList A ∧ A.length = 2 * r ∧
      (∀ m, m < A.length → A.getD m 0 < 2 ^ (3 * p)))
    (fun x y => ∃ A, x = intList A ∧ A.length = 2 * r ∧
      (∀ m, m < A.length → A.getD m 0 < 2 ^ (3 * p)) ∧ y = zsVal (deltaL A r))
    (Kdl * ((r + 1) * (p + 1) ^ 2)) (8 * ((r + 1) * (p + 1) ^ 2)) hbody
    [intList A00, intList A11, intList A01, intList A10] hxs
  have hQfun : ∀ a b b', (∃ A, a = intList A ∧ A.length = 2 * r ∧
        (∀ m, m < A.length → A.getD m 0 < 2 ^ (3 * p)) ∧ b = zsVal (deltaL A r)) →
      (∃ A, a = intList A ∧ A.length = 2 * r ∧
        (∀ m, m < A.length → A.getD m 0 < 2 ^ (3 * p)) ∧ b' = zsVal (deltaL A r)) → b = b' := by
    intro a b b' h1 h2
    obtain ⟨A1, ha1, -, -, hb1⟩ := h1
    obtain ⟨A2, ha2, -, -, hb2⟩ := h2
    have he : A1 = A2 := intList_injective (by rw [← ha1, ha2])
    rw [hb1, hb2, he]
  have st6 : Work.ConvR.WordC main (mapP dlProg)
      (fun vs => vs = L0 :: Cr :: Ck :: C3p :: C2r :: CC :: CD :: rest)
      (fun _ out => out = Dl :: Cr :: Ck :: C3p :: C2r :: CC :: CD :: rest)
      (BIG * ((r + 1) * (p + 1) ^ 2)) := by
    refine wc_conseq' (wc_ofWordR hmapres ?_) ?_ ?_
    · intro vs hvs
      have hSB : 4 * Kdl + 33 * MK ≤ BIG := by omega
      have h1 : 4 * (Kdl * ((r + 1) * (p + 1) ^ 2) + MK * (8 * ((r + 1) * (p + 1) ^ 2) + 1))
          + MK ≤ (4 * Kdl + 33 * MK) * ((r + 1) * (p + 1) ^ 2) := by nlinarith [hX12]
      calc 4 * (Kdl * ((r + 1) * (p + 1) ^ 2) + MK * (8 * ((r + 1) * (p + 1) ^ 2) + 1)) + MK
          ≤ (4 * Kdl + 33 * MK) * ((r + 1) * (p + 1) ^ 2) := h1
        _ ≤ BIG * ((r + 1) * (p + 1) ^ 2) := Nat.mul_le_mul_right _ hSB
    · intro vs hvs
      rw [hvs, hL0]
      try rfl
    · intro vs out hvs hQ
      obtain ⟨ys, hout, hforall⟩ := hQ
      have hcand : List.Forall₂ (fun x y => ∃ A, x = intList A ∧ A.length = 2 * r ∧
          (∀ m, m < A.length → A.getD m 0 < 2 ^ (3 * p)) ∧ y = zsVal (deltaL A r))
          [intList A00, intList A11, intList A01, intList A10]
          [zsVal (deltaL A00 r), zsVal (deltaL A11 r), zsVal (deltaL A01 r), zsVal (deltaL A10 r)] :=
        .cons ⟨A00, rfl, hA00, fun m hm => hb00 m (by omega), rfl⟩
          (.cons ⟨A11, rfl, hA11, fun m hm => hb11 m (by omega), rfl⟩
            (.cons ⟨A01, rfl, hA01, fun m hm => hb01 m (by omega), rfl⟩
              (.cons ⟨A10, rfl, hA10, fun m hm => hb10 m (by omega), rfl⟩ .nil)))
      have hysEq := forall₂_unique hQfun hforall hcand
      rw [hout, hysEq, hDl]
      try rfl
  have st7 : Work.ConvR.WordC main cdProg
      (fun vs => vs = Dl :: Cr :: Ck :: C3p :: C2r :: CC :: CD :: rest)
      (fun _ out => out = D0 :: D1 :: Cr :: Ck :: C3p :: C2r :: CC :: CD :: rest)
      (BIG * ((r + 1) * (p + 1) ^ 2)) := by
    have h1 := hcd main p r A00 A11 A01 A10 (Cr :: Ck :: C3p :: C2r :: CC :: CD :: rest)
      hA00 hA11 hA01 hA10 (fun m hm => hb00 m (by omega)) (fun m hm => hb11 m (by omega))
      (fun m hm => hb01 m (by omega)) (fun m hm => hb10 m (by omega)) hr hp
    refine wc_conseq' (wc_ofWordR h1 ?_) ?_ ?_
    · intro vs hvs
      exact costKc (c := 1) (by omega) (by omega)
    · intro vs hvs
      rw [hvs, hDl]
      try rfl
    · intro vs out hvs hQ
      rw [hQ, hD0, hD1]
      try rfl
  have st8 : Work.ConvR.WordC main (permP [0, 1, 3, 2, 4, 5, 6, 7])
      (fun vs => vs = D0 :: D1 :: Cr :: Ck :: C3p :: C2r :: CC :: CD :: rest)
      (fun _ out => out = D0 :: D1 :: Ck :: Cr :: C3p :: C2r :: CC :: CD :: rest)
      (BIG * ((r + 1) * (p + 1) ^ 2)) := by
    refine wc_perm (hperm main) [0, 1, 3, 2, 4, 5, 6, 7] [D0, D1, Cr, Ck, C3p, C2r, CC, CD]
      rest 8 _ (by simp) (by simp) (by decide) ?_
    refine costStepL (c := 10000) ?_ (by omega)
    simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil]
    rw [hD0, hD1, hCr, hCk, hC3p, hC2r, hCC, hCD]
    simp only [Work.ConvR.vsz_int]
    nlinarith [hsD0, hsD1, hCr', hCk', hC3p', hC2r', hCC', hCD', hX12]
  have hbody9 : ∀ x y, (∃ a b, x = Val.int a ∧ y = Val.int b ∧
        a.natAbs ≤ 2 ^ (3 * p + 1) ∧ b.natAbs ≤ 2 ^ (3 * p + 1)) →
      WordR main pdProg (fun vs => vs = x :: y :: (Ck :: Cr :: C3p :: C2r :: CC :: CD :: rest))
        (fun _ out => ∃ z, out = z :: (Ck :: Cr :: C3p :: C2r :: CC :: CD :: rest) ∧
          (∃ a b, x = Val.int a ∧ y = Val.int b ∧ z =
            cfxVal (Int.tdiv a ((2 : ℤ) ^ (p + Nat.clog 2 r)),
              Int.tdiv b ((2 : ℤ) ^ (p + Nat.clog 2 r)))) ∧ vsz z ≤ 8 * (p + 1))
        (fun _ => Kpd * (2 * (8 * (p + 1)) + 4 * (p + 1) + 1)) := by
    intro x y hxy
    obtain ⟨a0, b0, rfl, rfl, ha, hb⟩ := hxy
    have h1 := hpd main (((min (p + Nat.clog 2 r) (3 * p + 3) : ℕ) : ℤ))
      (Cr :: C3p :: C2r :: CC :: CD :: rest) a0 b0 (by positivity)
    refine wr_conseq hK h1 ?_ ?_ ?_
    · intro vs hvs
      rw [hvs, hCk]
      try rfl
    · intro vs out hvs hQ
      refine ⟨Val.cons (.int (Int.tdiv a0 ((2:ℤ) ^ (p + Nat.clog 2 r))))
        (.int (Int.tdiv b0 ((2:ℤ) ^ (p + Nat.clog 2 r)))), ?_, ?_, ?_⟩
      · have hval : cfxVal (Int.tdiv a0 (2 ^ (((min (p + Nat.clog 2 r) (3 * p + 3) : ℕ) : ℤ)).toNat),
            Int.tdiv b0 (2 ^ (((min (p + Nat.clog 2 r) (3 * p + 3) : ℕ) : ℤ)).toNat)) =
            cfxVal (Int.tdiv a0 ((2 : ℤ) ^ (p + Nat.clog 2 r)),
              Int.tdiv b0 ((2 : ℤ) ^ (p + Nat.clog 2 r))) := by
          simp only [Int.toNat_natCast]
          rw [tdivCap p r a0 ha, tdivCap p r b0 hb]
        rw [hQ, hval, ← hCk]
        try rfl
      · exact ⟨a0, b0, rfl, rfl, rfl⟩
      · show vsz (Val.cons (.int (Int.tdiv a0 ((2:ℤ) ^ (p + Nat.clog 2 r))))
          (.int (Int.tdiv b0 ((2:ℤ) ^ (p + Nat.clog 2 r))))) ≤ 8 * (p + 1)
        rw [Work.ConvR.vsz_cons, Work.ConvR.vsz_int, Work.ConvR.vsz_int]
        have hq1 : ((Int.tdiv a0 ((2:ℤ) ^ (p + Nat.clog 2 r)))).natAbs ≤ 2 ^ (3 * p + 1) :=
          le_trans (by rw [Int.natAbs_tdiv]; exact Nat.div_le_self _ _) ha
        have hq2 : ((Int.tdiv b0 ((2:ℤ) ^ (p + Nat.clog 2 r)))).natAbs ≤ 2 ^ (3 * p + 1) :=
          le_trans (by rw [Int.natAbs_tdiv]; exact Nat.div_le_self _ _) hb
        have h3 := Work.ConvR.isz_le_of_natAbs_le (p := 3 * p + 1) hq1
        have h4 := Work.ConvR.isz_le_of_natAbs_le (p := 3 * p + 1) hq2
        omega
    · intro vs hvs
      have hck : isz (((min (p + Nat.clog 2 r) (3 * p + 3) : ℕ) : ℤ)) ≤ 4 * (p + 1) := by
        have h := isz_natCast_le (min (p + Nat.clog 2 r) (3 * p + 3))
        have h2 : min (p + Nat.clog 2 r) (3 * p + 3) ≤ 3 * p + 3 := Nat.min_le_right _ _
        omega
      have ha2 : isz a0 ≤ 3 * p + 4 := by
        have := Work.ConvR.isz_le_of_natAbs_le (p := 3 * p + 1) ha; omega
      have hb2 : isz b0 ≤ 3 * p + 4 := by
        have := Work.ConvR.isz_le_of_natAbs_le (p := 3 * p + 1) hb; omega
      show Kpd * (isz a0 + isz b0 +
        isz ((min (p + Nat.clog 2 r) (3 * p + 3) : ℕ) : ℤ) + 1) ≤
        Kpd * (2 * (8 * (p + 1)) + 4 * (p + 1) + 1)
      have h3 : isz a0 + isz b0 + isz ((min (p + Nat.clog 2 r) (3 * p + 3) : ℕ) : ℤ) + 1 ≤
          2 * (8 * (p + 1)) + 4 * (p + 1) + 1 := by omega
      exact Nat.mul_le_mul_left _ h3
  have hzipres := hzip main pdProg (Ck :: Cr :: C3p :: C2r :: CC :: CD :: rest)
    (fun x y => ∃ a b, x = Val.int a ∧ y = Val.int b ∧
      a.natAbs ≤ 2 ^ (3 * p + 1) ∧ b.natAbs ≤ 2 ^ (3 * p + 1))
    (fun x y z => ∃ a b, x = Val.int a ∧ y = Val.int b ∧ z =
      cfxVal (Int.tdiv a ((2 : ℤ) ^ (p + Nat.clog 2 r)),
        Int.tdiv b ((2 : ℤ) ^ (p + Nat.clog 2 r))))
    (Kpd * (2 * (8 * (p + 1)) + 4 * (p + 1) + 1)) (8 * (p + 1)) hbody9
    (List.map Val.int (D0L r A00 A11)) (List.map Val.int (D1L r A01 A10))
    (by rw [List.length_map, List.length_map, D0L_length, D1L_length, hA00, hA11, hA01, hA10])
    (by
      intro i hi
      have hdl : (D0L r A00 A11).length = (D1L r A01 A10).length := by
        rw [D0L_length, D1L_length, hA00, hA11, hA01, hA10]
      have hi1 : i < (D0L r A00 A11).length := by simpa [List.length_map] using hi
      have hi2 : i < (D1L r A01 A10).length := by rw [← hdl]; exact hi1
      refine ⟨(D0L r A00 A11).getD i 0, (D1L r A01 A10).getD i 0, ?_, ?_, ?_, ?_⟩
      · exact getD_map_int hi1
      · exact getD_map_int hi2
      · exact D0L_mem_bound (deltaL_mem_bound (A := A00) (r := r) (p := p) (fun m hm => hb00 m (by omega)))
          (deltaL_mem_bound (A := A11) (r := r) (p := p) (fun m hm => hb11 m (by omega)))
          _ (getD_mem_of_lt' hi1)
      · exact D1L_mem_bound (deltaL_mem_bound (A := A01) (r := r) (p := p) (fun m hm => hb01 m (by omega)))
          (deltaL_mem_bound (A := A10) (r := r) (p := p) (fun m hm => hb10 m (by omega)))
          _ (getD_mem_of_lt' hi2))
    (by
      intro x hx
      rw [List.mem_append] at hx
      rcases hx with hx | hx
      · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
        have hi1 : i < (D0L r A00 A11).length := by simpa [List.length_map] using hi
        rw [List.getElem_map, Work.ConvR.vsz_int, ← List.getD_eq_getElem (D0L r A00 A11) 0 hi1]
        have h := D0L_mem_bound (deltaL_mem_bound (A := A00) (r := r) (p := p) (fun m hm => hb00 m (by omega)))
          (deltaL_mem_bound (A := A11) (r := r) (p := p) (fun m hm => hb11 m (by omega)))
          _ (getD_mem_of_lt' hi1)
        have h2 := Work.ConvR.isz_le_of_natAbs_le (p := 3 * p + 1) h
        omega
      · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
        have hi2 : i < (D1L r A01 A10).length := by simpa [List.length_map] using hi
        rw [List.getElem_map, Work.ConvR.vsz_int, ← List.getD_eq_getElem (D1L r A01 A10) 0 hi2]
        have h := D1L_mem_bound (deltaL_mem_bound (A := A01) (r := r) (p := p) (fun m hm => hb01 m (by omega)))
          (deltaL_mem_bound (A := A10) (r := r) (p := p) (fun m hm => hb10 m (by omega)))
          _ (getD_mem_of_lt' hi2)
        have h2 := Work.ConvR.isz_le_of_natAbs_le (p := 3 * p + 1) h
        omega)
  have st9 : Work.ConvR.WordC main (zipP pdProg)
      (fun vs => vs = D0 :: D1 :: Ck :: Cr :: C3p :: C2r :: CC :: CD :: rest)
      (fun _ out => out = Res :: Ck :: Cr :: C3p :: C2r :: CC :: CD :: rest)
      (BIG * ((r + 1) * (p + 1) ^ 2)) := by
    refine wc_conseq' (wc_ofWordR hzipres ?_) ?_ ?_
    · intro vs hvs
      rw [show (List.map Val.int (D0L r A00 A11)).length = r from by
        rw [List.length_map, D0L_length, hA00, hA11]; omega]
      have h2L : 2 * (8 * (p + 1)) ≤ 26 * (p + 1) := by omega
      have hL1 : 8 * (p + 1) + 1 ≤ 11 * (p + 1) := by omega
      have hrp' : r * (p + 1) ≤ (r + 1) * (p + 1) ^ 2 := by nlinarith
      have hSB : 26 * Kpd + 12 * ZK ≤ BIG := by omega
      calc r * (Kpd * (2 * (8 * (p + 1)) + 4 * (p + 1) + 1) + ZK * (8 * (p + 1) + 1)) + ZK
          ≤ r * (Kpd * (26 * (p + 1)) + ZK * (11 * (p + 1))) + ZK := by
            apply Nat.add_le_add_right
            apply Nat.mul_le_mul_left
            apply Nat.add_le_add
            · have hb : 2 * (8 * (p + 1)) + 4 * (p + 1) + 1 ≤ 26 * (p + 1) := by omega
              calc Kpd * (2 * (8 * (p + 1)) + 4 * (p + 1) + 1) ≤ Kpd * (26 * (p + 1)) :=
                    Nat.mul_le_mul_left _ hb
                _ = Kpd * (26 * (p + 1)) := rfl
            · calc ZK * (8 * (p + 1) + 1) ≤ ZK * (11 * (p + 1)) :=
                    Nat.mul_le_mul_left _ hL1
                _ = ZK * (11 * (p + 1)) := rfl
        _ = 26 * Kpd * (r * (p + 1)) + 11 * ZK * (r * (p + 1)) + ZK := by ring
        _ ≤ 26 * Kpd * ((r + 1) * (p + 1) ^ 2) + 11 * ZK * ((r + 1) * (p + 1) ^ 2)
              + ZK * ((r + 1) * (p + 1) ^ 2) := by
            refine Nat.add_le_add (Nat.add_le_add ?_ ?_) ?_
            · exact Nat.mul_le_mul_left _ hrp'
            · exact Nat.mul_le_mul_left _ hrp'
            · calc ZK = ZK * 1 := (Nat.mul_one ZK).symm
                _ ≤ ZK * ((r + 1) * (p + 1) ^ 2) := Nat.mul_le_mul_left _ hX1
        _ = (26 * Kpd + 12 * ZK) * ((r + 1) * (p + 1) ^ 2) := by ring
        _ ≤ BIG * ((r + 1) * (p + 1) ^ 2) := Nat.mul_le_mul_right _ hSB
    · intro vs hvs
      rw [hvs, hD0, hD1]
      try rfl
    · intro vs out hvs hQ
      obtain ⟨zs, hout, hzlen, hzs⟩ := hQ
      rw [hout, hRes]
      congr 1
      have hzdl : (D0L r A00 A11).length = (D1L r A01 A10).length := by
        rw [D0L_length, D1L_length, hA00, hA11, hA01, hA10]
      have hlen2 : zs.length = (D0L r A00 A11).length := by
        rw [hzlen, List.length_map]
      have hpoint : ∀ i, i < (D0L r A00 A11).length →
          zs.getD i .nil = cfxVal (Int.tdiv ((D0L r A00 A11).getD i 0) ((2 : ℤ) ^ (p + Nat.clog 2 r)),
            Int.tdiv ((D1L r A01 A10).getD i 0) ((2 : ℤ) ^ (p + Nat.clog 2 r))) := by
        intro i hi
        have hi' : i < (List.map Val.int (D0L r A00 A11)).length := by simpa [List.length_map] using hi
        obtain ⟨a, b, ha, hb2, hf⟩ := hzs i hi'
        have ha' : a = (D0L r A00 A11).getD i 0 := by
          apply (Val.int.injEq a _).mp
          rw [← ha, getD_map_int hi]
        have hb' : b = (D1L r A01 A10).getD i 0 := by
          apply (Val.int.injEq b _).mp
          rw [← hb2, getD_map_int (by rw [← hzdl]; exact hi)]
        rw [hf, ha', hb']
      have hmain := zipWith_pair_eq (D := (2 : ℤ) ^ (p + Nat.clog 2 r)) hzdl hlen2 hpoint
      rw [hmain]
      try rfl
  have st10 : Work.ConvR.WordC main duP
      (fun vs => vs = Res :: Ck :: Cr :: C3p :: C2r :: CC :: CD :: rest)
      (fun _ out => out = Res :: C3p :: C2r :: CC :: CD :: rest)
      (BIG * ((r + 1) * (p + 1) ^ 2)) := by
    refine wc_cost_le (hdu main Res Ck Cr (C3p :: C2r :: CC :: CD :: rest)) ?_
    refine costKc (c := 1024) ?_ (by omega)
    rw [hCk, hCr]
    simp only [Work.ConvR.vsz_int]
    nlinarith [hsRes, hCk', hCr', hX12]
  have st11 : Work.ConvR.WordC main duP
      (fun vs => vs = Res :: C3p :: C2r :: CC :: CD :: rest)
      (fun _ out => out = Res :: CC :: CD :: rest) (BIG * ((r + 1) * (p + 1) ^ 2)) := by
    refine wc_cost_le (hdu main Res C3p C2r (CC :: CD :: rest)) ?_
    refine costKc (c := 1024) ?_ (by omega)
    rw [hC3p, hC2r]
    simp only [Work.ConvR.vsz_int]
    nlinarith [hsRes, hC3p', hC2r', hX12]
  have st12 : Work.ConvR.WordC main duP
      (fun vs => vs = Res :: CC :: CD :: rest) (fun _ out => out = Res :: rest)
      (BIG * ((r + 1) * (p + 1) ^ 2)) := by
    refine wc_cost_le (hdu main Res CC CD rest) ?_
    refine costKc (c := 1024) ?_ (by omega)
    rw [hCC, hCD]
    simp only [Work.ConvR.vsz_int]
    nlinarith [hsRes, hCC', hCD', hX12]
  have hall : Work.ConvR.WordC main
      (List.foldl (fun a b => Cmd.seq a b) Cmd.skip
        [permP [5, 6, 0, 1, 2, 3, 4], pickP 1, swapP, scProg, permP [2, 1, 0, 3, 4, 5, 6],
          mapP dlProg, cdProg, permP [0, 1, 3, 2, 4, 5, 6, 7], zipP pdProg, duP, duP, duP])
      (fun vs => vs = L0 :: C3p :: C2r :: CC :: CD :: Cp :: Cr :: rest)
      (fun _ out => out = Res :: rest)
      (1 + 12 * (BIG * ((r + 1) * (p + 1) ^ 2))) := by
    have g0 := wc_skipN (main := main) (L0 :: C3p :: C2r :: CC :: CD :: Cp :: Cr :: rest) BIG
      ((r + 1) * (p + 1) ^ 2)
    have g1 := wc_chainN g0 st1
    have g2 := wc_chainN g1 st2
    have g3 := wc_chainN g2 st3
    have g4 := wc_chainN g3 st4
    have g5 := wc_chainN g4 st5
    have g6 := wc_chainN g5 st6
    have g7 := wc_chainN g6 st7
    have g8 := wc_chainN g7 st8
    have g9 := wc_chainN g8 st9
    have g10 := wc_chainN g9 st10
    have g11 := wc_chainN g10 st11
    have g12 := wc_chainN g11 st12
    exact g12
  intro vs hvs s R hR
  obtain ⟨out, s', n, hQ, he, hn, hstk, hoth⟩ := hall vs hvs s R hR
  refine ⟨out, s', n, ?_, he, ?_, hstk, hoth⟩
  · rw [hQ, hRes]
    try rfl
  · refine le_trans hn ?_
    calc 1 + 12 * (BIG * ((r + 1) * (p + 1) ^ 2))
        ≤ (12 * BIG + 1) * ((r + 1) * (p + 1) ^ 2) :=
          capBound (n := 12) (BIG := BIG) (X := ((r + 1) * (p + 1) ^ 2)) hX1
      _ = (12 * BIG + 1) * (r + 1) * (p + 1) ^ 2 := by ring

end Work.KronP
