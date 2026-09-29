import Mathlib
import Submission.Work.Fx.FxExpCore
import Submission.Work.Fx.expStepErr
import Submission.Work.Fx.scaleCommon

/-!
# Assembly kit for the `cis` word (paper Lemma 2.12)

`Work.Fx.Cis` provides the window-plumbing used to build the `cis` word out of the library
words of `KernelLib`/`IntLib` and of the existential words `pi` and `expc` of
`Work.Fx.NumWords`:

* `Pipe main prog A B c`: the word maps the fixed window `A` (topmost values of the value
  stack) to the fixed window `B`, cost `c`;
* `PipeQ main prog A Q c`: same, but the resulting window only has to satisfy the predicate `Q`
  (this is what an existential word such as `pi`/`expc` produces);
* composition lemmas `Pipe.comp`, `PipeQ.comp`, `PipeQ.compDet`, `PipeQ.compEx1`,
  `PipeQ.compEx2`, and the final conversion `PipeQ.toWordR` back to a `WordR` triple with
  existential rest;
* the size bound `Xb p j k = p + isz j + isz k + 64` and the uniform per-step cost bound
  `CB X KS = KS * X ^ 32`, with lemmas bounding the cost of every library word by `CB`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.Fx.Cis

open HvdH

noncomputable section

/-! ## `Pipe` (window plumbing, as in `Work.Fx.piWord`) -/

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

/-! ## `PipeQ`: window plumbing with an existential postcondition -/

/-- `PipeQ main prog A Q c`: `prog` maps the window `A` (on top of any fixed list of values) to
*some* window `o` satisfying `Q o`, at cost at most `c`. -/
def PipeQ (main prog : Cmd) (A : List Val) (Q : List Val → Prop) (c : ℕ) : Prop :=
  ∀ rest : List Val,
    WordR main prog (fun vs => vs = A ++ rest) (fun _ out => ∃ o, out = o ++ rest ∧ Q o)
      (fun _ => c)

/-- A deterministic `Pipe` is a `PipeQ` with the predicate `o = B`. -/
theorem Pipe.toPipeQ {main p : Cmd} {A B : List Val} {c : ℕ} (h : Pipe main p A B c) :
    PipeQ main p A (fun o => o = B) c := by
  intro rest vs hvs s R hR
  obtain ⟨out, s', n, hout, hev, hn, hstk, hoth⟩ := h rest vs hvs s R hR
  exact ⟨out, s', n, ⟨B, hout, rfl⟩, hev, hn, hstk, hoth⟩

theorem PipeQ.le {main p : Cmd} {A : List Val} {Q : List Val → Prop} {c c' : ℕ}
    (h : PipeQ main p A Q c) (hc : c ≤ c') : PipeQ main p A Q c' := by
  intro rest vs hvs s R hR
  obtain ⟨out, s', n, hp, hev, hn, hstk, hoth⟩ := h rest vs hvs s R hR
  exact ⟨out, s', n, hp, hev, le_trans hn hc, hstk, hoth⟩

theorem PipeQ.mono {main p : Cmd} {A : List Val} {Q Q' : List Val → Prop} {c : ℕ}
    (h : PipeQ main p A Q c) (hQ : ∀ o, Q o → Q' o) : PipeQ main p A Q' c := by
  intro rest vs hvs s R hR
  obtain ⟨out, s', n, ⟨o, hout, hQo⟩, hev, hn, hstk, hoth⟩ := h rest vs hvs s R hR
  exact ⟨out, s', n, ⟨o, hout, hQ o hQo⟩, hev, hn, hstk, hoth⟩

/-- Rewriting the input window and weakening the postcondition of a `PipeQ`. -/
theorem PipeQ.congr {main p : Cmd} {A A' : List Val} {Q Q' : List Val → Prop} {c : ℕ}
    (h : PipeQ main p A Q c) (hA : A = A') (hQ : ∀ o, Q o → Q' o) : PipeQ main p A' Q' c := by
  intro rest vs hvs s R hR
  rw [← hA] at hvs
  obtain ⟨out, s', n, ⟨o, hout, hQo⟩, hev, hn, hstk, hoth⟩ := h rest vs hvs s R hR
  exact ⟨out, s', n, ⟨o, hout, hQ o hQo⟩, hev, hn, hstk, hoth⟩

/-- Sequential composition of two `PipeQ`s, the second depending on the intermediate window. -/
theorem PipeQ.comp {main p q : Cmd} {A : List Val} {Q Q' : List Val → Prop} {c d : ℕ}
    (h1 : PipeQ main p A Q c) (h2 : ∀ o, Q o → PipeQ main q o Q' d) :
    PipeQ main (.seq p q) A Q' (c + d) := by
  intro rest vs hvs s R hR
  obtain ⟨mid, s', n1, ⟨o, hmid, hQo⟩, hev1, hn1, hstk1, hoth1⟩ := h1 rest vs hvs s R hR
  obtain ⟨out, s'', n2, ⟨o', hout, hQ'o⟩, hev2, hn2, hstk2, hoth2⟩ :=
    h2 o hQo rest mid hmid s' R hstk1
  exact ⟨out, s'', n1 + n2, ⟨o', hout, hQ'o⟩, Eval.seq hev1 hev2, Nat.add_le_add hn1 hn2, hstk2,
    fun k hk => by rw [hoth2 k hk, hoth1 k hk]⟩

/-- Composition of a deterministic `Pipe` with a `PipeQ`. -/
theorem PipeQ.compDet {main p q : Cmd} {A B : List Val} {Q : List Val → Prop} {c d : ℕ}
    (h1 : Pipe main p A B c) (h2 : PipeQ main q B Q d) : PipeQ main (.seq p q) A Q (c + d) :=
  PipeQ.comp (Pipe.toPipeQ h1) (fun o ho => by rw [ho]; exact h2)

/-- Composition where the first word returns one unknown integer (e.g. the `π` word). -/
theorem PipeQ.compEx1 {main p q : Cmd} {A : List Val} {P : ℤ → Prop} {Q : List Val → Prop}
    {c d : ℕ} (h1 : PipeQ main p A (fun o => ∃ u : ℤ, o = [Val.int u] ∧ P u) c)
    (h2 : ∀ u : ℤ, P u → PipeQ main q [Val.int u] Q d) :
    PipeQ main (.seq p q) A Q (c + d) :=
  PipeQ.comp h1 (fun o ho => by rcases ho with ⟨u, rfl, hu⟩; exact h2 u hu)

/-- Composition where the first word returns two unknown integers (e.g. the `expc` word). -/
theorem PipeQ.compEx2 {main p q : Cmd} {A : List Val} {P : ℤ → ℤ → Prop} {Q : List Val → Prop}
    {c d : ℕ} (h1 : PipeQ main p A (fun o => ∃ u v : ℤ, o = [Val.int u, Val.int v] ∧ P u v) c)
    (h2 : ∀ u v : ℤ, P u v → PipeQ main q [Val.int u, Val.int v] Q d) :
    PipeQ main (.seq p q) A Q (c + d) :=
  PipeQ.comp h1 (fun o ho => by rcases ho with ⟨u, v, rfl, huv⟩; exact h2 u v huv)

/-- Final conversion: a `PipeQ` is a `WordR` triple whose pre/post stack contents are the
window `A` / the window `o` followed by the untouched rest of the stack. -/
theorem PipeQ.toWordR {main p : Cmd} {A : List Val} {Q : List Val → Prop} {c : ℕ}
    (h : PipeQ main p A Q c) :
    WordR main p (fun vs => ∃ rest, vs = A ++ rest)
      (fun _ out => ∃ o rest, out = o ++ rest ∧ Q o) (fun _ => c) := by
  intro vs ⟨rest, hvs⟩ s R hR
  obtain ⟨out, s', n, ⟨o, hout, hQ⟩, hev, hn, hstk, hoth⟩ := h rest vs hvs s R hR
  exact ⟨out, s', n, ⟨o, rest, hout, hQ⟩, hev, hn, hstk, hoth⟩

/-! ## `pushVal` on any window -/

theorem Pipe.pushOnAny {main prog : Cmd} {v : Val} {c : ℕ} {T : List Val}
    (h : WordR main prog (fun _ => True) (fun vs out => out = v :: vs) (fun _ => c)) :
    Pipe main prog T (v :: T) c := by
  intro rest vs hvs s R hR
  obtain ⟨out, s', n, hout, hev, hn, hstk, hoth⟩ := h vs trivial s R hR
  exact ⟨out, s', n, by rw [hout, hvs]; rfl, hev, hn, hstk, hoth⟩

/-! ## Size bound and uniform cost bound -/

/-- The size scale of the `cis` word: precision `p` plus the sizes of `j` and `k` plus a
constant margin large enough for every intermediate value. -/
def Xb (p : ℕ) (j : ℤ) (k : ℕ) : ℕ := p + isz j + isz k + 64

/-- The uniform per-step cost bound. -/
def CB (X KS : ℕ) : ℕ := KS * X ^ 32

theorem two_le_isz (z : ℤ) : 2 ≤ isz z := by simp only [isz]; omega

theorem isz_natCast_le (n : ℕ) : isz (n : ℤ) ≤ n + 2 := by
  have h : (n : ℤ).natAbs = n := Int.natAbs_natCast n
  have h1 : n.size ≤ n := Nat.size_le.mpr (Nat.lt_two_pow_self (n := n))
  simp only [isz, h]; omega

theorem Xb_ge (p : ℕ) (j : ℤ) (k : ℕ) (hp : 100 ≤ p) : 168 ≤ Xb p j k := by
  have h1 : 2 ≤ isz j := two_le_isz j
  have h2 : 2 ≤ isz (k : ℤ) := two_le_isz (k : ℤ)
  simp only [Xb]; omega

theorem isz_le_Xb_p (p : ℕ) (j : ℤ) (k : ℕ) : isz (p : ℤ) ≤ Xb p j k := by
  have h1 : isz (p : ℤ) ≤ p + 2 := isz_natCast_le p
  have h2 : 0 ≤ isz j := by have := two_le_isz j; omega
  have h3 : 0 ≤ isz (k : ℤ) := by have := two_le_isz (k : ℤ); omega
  simp only [Xb]; omega

theorem isz_le_Xb_j (p : ℕ) (j : ℤ) (k : ℕ) : isz j ≤ Xb p j k := by simp only [Xb]; omega

theorem isz_le_Xb_k (p : ℕ) (j : ℤ) (k : ℕ) : isz (k : ℤ) ≤ Xb p j k := by simp only [Xb]; omega

theorem isz_le_Xb_of_le {p : ℕ} {j : ℤ} {k n : ℕ} (h : n + 2 ≤ Xb p j k) :
    isz (n : ℤ) ≤ Xb p j k := by
  have h1 : isz (n : ℤ) ≤ n + 2 := isz_natCast_le n
  omega

theorem isz_two : isz (2 : ℤ) = 4 := by
  have h : (2 : ℤ).natAbs = 2 := rfl
  have h2 : (2 : ℕ).size = 2 := by decide
  simp only [isz, h, h2]

theorem isz_sixty : isz (60 : ℤ) = 8 := by
  have h : (60 : ℤ).natAbs = 60 := rfl
  have h2 : (60 : ℕ).size = 6 := by decide
  simp only [isz, h, h2]

theorem isz_neg64 : isz (-64 : ℤ) = 9 := by
  have h : (-64 : ℤ).natAbs = 64 := rfl
  have h2 : (64 : ℕ).size = 7 := by decide
  simp only [isz, h, h2]

/-- `Int.fmod j k` has no more bits than `k` (for `0 < k`). -/
theorem isz_fmod_le {j : ℤ} {k : ℕ} (hk : 1 ≤ k) : isz (Int.fmod j k) ≤ isz (k : ℤ) := by
  have hkZ : (0 : ℤ) < (k : ℤ) := by exact_mod_cast hk
  have h0 : 0 ≤ Int.fmod j k := by
    rw [Int.fmod_eq_emod_of_nonneg j (le_of_lt hkZ)]
    exact Int.emod_nonneg j (ne_of_gt hkZ)
  have h1 : Int.fmod j k < (k : ℤ) := by
    rw [Int.fmod_eq_emod_of_nonneg j (le_of_lt hkZ)]
    exact Int.emod_lt_of_pos j hkZ
  have h2 : (Int.fmod j k).natAbs ≤ k := by
    have h3 : (((Int.fmod j k).natAbs : ℕ) : ℤ) ≤ (k : ℤ) := by
      rw [Int.natAbs_of_nonneg h0]
      exact le_of_lt h1
    exact_mod_cast h3
  have h3 : (Int.fmod j k).natAbs.size ≤ k.size := Nat.size_mono' h2
  have h4 : ((k : ℤ)).natAbs = k := Int.natAbs_natCast k
  simp only [isz, h4]
  omega

theorem isz_fmod_le_Xb (p : ℕ) (j : ℤ) (k : ℕ) (hk : 1 ≤ k) :
    isz (Int.fmod j k) ≤ Xb p j k :=
  le_trans (isz_fmod_le hk) (isz_le_Xb_k p j k)

/-- `isz (p + 60) ≤ Xb p j k`. -/
theorem isz_p_add_sixty_le_Xb (p : ℕ) (j : ℤ) (k : ℕ) (hp : 100 ≤ p) :
    isz ((p : ℤ) + 60) ≤ Xb p j k := by
  have h1 : isz ((p : ℤ) + 60) ≤ max (isz (p : ℤ)) (isz (60 : ℤ)) + 1 := isz_add_le _ _
  have h2 : isz (p : ℤ) ≤ p + 2 := isz_natCast_le p
  have h3 : isz (60 : ℤ) = 8 := isz_sixty
  have h4 : 2 ≤ isz j := two_le_isz j
  have h5 : 2 ≤ isz (k : ℤ) := two_le_isz (k : ℤ)
  simp only [Xb] at *
  omega

/-- `isz (2 * a) ≤ isz a + 4`. -/
theorem isz_two_mul_le (a : ℤ) : isz (2 * a) ≤ isz a + 4 := by
  have h1 : isz (2 * a) ≤ isz (2 : ℤ) + isz a := isz_mul_le 2 a
  have h2 : isz (2 : ℤ) = 4 := isz_two
  omega

/-- The integer produced by the `π` word at precision `p + 60` has at most `Xb p j k` bits. -/
theorem isz_u_le_Xb {p : ℕ} {j : ℤ} {k : ℕ} (hp : 100 ≤ p) {u : ℤ}
    (hu : |(u : ℝ) - 2 ^ (p + 60) * Real.pi| ≤ 1) : isz u ≤ Xb p j k := by
  have hpi : Real.pi < 4 := Real.pi_lt_four
  have hX1 : (1 : ℝ) ≤ 2 ^ (p + 60) := one_le_pow₀ (by norm_num)
  have hXpos : (0 : ℝ) < 2 ^ (p + 60) := by positivity
  have hX8 : (2 : ℝ) ^ (p + 63) = 8 * 2 ^ (p + 60) := by
    rw [show p + 63 = p + 60 + 3 by omega, pow_add]
    norm_num
    ring
  have hu' : |(u : ℝ)| ≤ 2 ^ (p + 60) * Real.pi + 1 := by
    have h := abs_le.mp hu
    rw [abs_le]
    have hX : (0 : ℝ) < 2 ^ (p + 60) * Real.pi := by positivity
    constructor
    · linarith [h.1, hX]
    · linarith [h.2]
  have hlt : (2 : ℝ) ^ (p + 60) * Real.pi + 1 < 8 * 2 ^ (p + 60) := by
    have h4 : (2 : ℝ) ^ (p + 60) * Real.pi < 4 * 2 ^ (p + 60) := by
      have h := mul_lt_mul_of_pos_right hpi hXpos
      linarith
    nlinarith [h4, hX1]
  have hbound : |(u : ℝ)| < (2 : ℝ) ^ (p + 63) := by
    rw [hX8]
    linarith
  have hnat : u.natAbs < 2 ^ (p + 63) := by
    have hcast : ((u.natAbs : ℕ) : ℝ) < ((2 ^ (p + 63) : ℕ) : ℝ) := by
      rw [Nat.cast_natAbs, Int.cast_abs]
      push_cast
      exact hbound
    exact_mod_cast hcast
  have hsize : u.natAbs.size ≤ p + 63 := Nat.size_le.mpr hnat
  have h4 : 2 ≤ isz j := two_le_isz j
  have h5 : 2 ≤ isz (k : ℤ) := two_le_isz (k : ℤ)
  simp only [isz, Xb]
  omega

/-! ### Bounding the cost of a single library word by `CB` -/

private theorem sq_le_pow32 {X : ℕ} (hX : 1 ≤ X) : X * X ≤ X ^ 32 := by
  calc X * X = X ^ 2 := by ring
    _ ≤ X ^ 32 := Nat.pow_le_pow_right (by omega) (by norm_num)

private theorem two_mul_le_sq {X : ℕ} (hX : 2 ≤ X) : 2 * X ≤ X * X := by nlinarith

private theorem forty_le_sq {X : ℕ} (hX : 45 ≤ X) : 5 * (8 * X + 1) ≤ X * X := by
  have h : 45 * X ≤ X * X := by nlinarith
  nlinarith

/-- `K * (u + v) ≤ CB X KS` for `u, v ≤ X` (`add`/`sub`/`lt`: linear cost). -/
theorem le_CB_add {K KS X u v : ℕ} (hK : K ≤ KS) (hu : u ≤ X) (hv : v ≤ X) (hX : 2 ≤ X) :
    K * (u + v) ≤ CB X KS := by
  rw [CB]
  refine le_trans (Nat.mul_le_mul hK (show u + v ≤ 2 * X by omega)) ?_
  exact Nat.mul_le_mul_left KS (le_trans (two_mul_le_sq hX) (sq_le_pow32 (by omega)))

/-- `K * u * v ≤ CB X KS` for `u, v ≤ X` (`mulS`/`tdiv`/`gcd`: quadratic cost). -/
theorem le_CB_mul {K KS X u v : ℕ} (hK : K ≤ KS) (hu : u ≤ X) (hv : v ≤ X) (hX : 2 ≤ X) :
    K * u * v ≤ CB X KS := by
  rw [CB]
  calc K * u * v ≤ (KS * X) * v := Nat.mul_le_mul_right v (Nat.mul_le_mul hK hu)
    _ ≤ (KS * X) * X := Nat.mul_le_mul_left (KS * X) hv
    _ = KS * (X * X) := by ring
    _ ≤ KS * X ^ 32 := Nat.mul_le_mul_left KS (sq_le_pow32 (by omega))

/-- `K * (v + 1) ≤ CB X KS` for `v ≤ X` (`push`/`drop` of one value). -/
theorem le_CB_one {K KS X v : ℕ} (hK : K ≤ KS) (hv : v ≤ X) (hX : 2 ≤ X) :
    K * (v + 1) ≤ CB X KS := by
  rw [CB]
  refine le_trans (Nat.mul_le_mul hK (show v + 1 ≤ 2 * X by omega)) ?_
  exact Nat.mul_le_mul_left KS (le_trans (two_mul_le_sq hX) (sq_le_pow32 (by omega)))

/-- `K * u ≤ CB X KS` for `u ≤ X`. -/
theorem le_CB_un1 {K KS X u : ℕ} (hK : K ≤ KS) (hu : u ≤ X) (hX : 1 ≤ X) :
    K * u ≤ CB X KS := by
  rw [CB]
  calc K * u ≤ KS * X := Nat.mul_le_mul hK hu
    _ ≤ KS * (X * X) := Nat.mul_le_mul_left KS (by
        have h : 1 * X ≤ X * X := Nat.mul_le_mul_right X hX
        simpa using h)
    _ ≤ KS * X ^ 32 := Nat.mul_le_mul_left KS (sq_le_pow32 hX)

/-- A constant cost `K ≤ KS` is at most `CB X KS`. -/
theorem le_CB_const {K KS X : ℕ} (hK : K ≤ KS) (hX : 1 ≤ X) : K ≤ CB X KS := by
  rw [CB]
  calc K ≤ KS := hK
    _ = KS * 1 := (Nat.mul_one KS).symm
    _ ≤ KS * X ^ 32 := Nat.mul_le_mul_left KS (Nat.one_le_pow 32 X hX)

/-- `szl` of a window all of whose members have size `≤ X` and which has length `≤ 8`. -/
theorem szl_le_eight (A : List Val) {X : ℕ} (h : ∀ v ∈ A, vsz v ≤ X) (hA : A.length ≤ 8) :
    szl A ≤ 8 * X := by
  calc szl A ≤ A.length * X := szl_le_len_mul h
    _ ≤ 8 * X := Nat.mul_le_mul_right X hA

/-- The cost of `pick`/`roll` at index `k` on a window of length `≤ 8` with sizes `≤ X`. -/
theorem le_CB_roll {K KS X k : ℕ} (hK : K ≤ KS) (hk : k + 1 ≤ 5) {A : List Val}
    (hA : ∀ v ∈ A, vsz v ≤ X) (hAlen : A.length ≤ 8) (hX : 45 ≤ X) :
    K * (k + 1) * (szl (A.take (k + 1)) + 1) ≤ CB X KS := by
  have hsub : ∀ v ∈ A.take (k + 1), vsz v ≤ X := fun v hv => hA v (List.mem_of_mem_take hv)
  have h1 : szl (A.take (k + 1)) ≤ 8 * X := by
    have hlen : (A.take (k + 1)).length ≤ 8 := by
      rw [List.length_take]; omega
    exact szl_le_eight _ hsub hlen
  have h2 : szl (A.take (k + 1)) + 1 ≤ 8 * X + 1 := by omega
  rw [CB]
  calc K * (k + 1) * (szl (A.take (k + 1)) + 1)
      ≤ (KS * 5) * (8 * X + 1) := Nat.mul_le_mul (Nat.mul_le_mul hK hk) h2
    _ = KS * (5 * (8 * X + 1)) := by ring
    _ ≤ KS * (X * X) := Nat.mul_le_mul_left KS (forty_le_sq hX)
    _ ≤ KS * X ^ 32 := Nat.mul_le_mul_left KS (sq_le_pow32 (by omega))

/-- The cost of `swap`/`consV`-style words on a two-element window with sizes `≤ X`. -/
theorem le_CB_two {K KS X u v : ℕ} (hK : K ≤ KS) (hu : u ≤ X) (hv : v ≤ X) (hX : 3 ≤ X) :
    K * (u + v + 1) ≤ CB X KS := by
  rw [CB]
  refine le_trans (Nat.mul_le_mul hK (show u + v + 1 ≤ 2 * (X + 1) by omega)) ?_
  refine le_trans (Nat.mul_le_mul_left KS (show 2 * (X + 1) ≤ X * X by nlinarith)) ?_
  exact Nat.mul_le_mul_left KS (sq_le_pow32 (by omega))

/-- The cost of `consV` (constant). -/
theorem le_CB_consV {K KS X : ℕ} (hK : K ≤ KS) (hX : 1 ≤ X) : K ≤ CB X KS :=
  le_CB_const hK hX

end

end Work.Fx.Cis
