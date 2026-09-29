import Mathlib
import Submission.HvdH.Interfaces

/-!
# Shared helpers for the Fx area (fixed-point complex words)

* size bookkeeping for `Val` (`szl`, `vsz`, `isz`),
* `Spec`, a "window" formulation of `WordR` that composes easily,
* adapters turning the `KernelLib` / `IntLib` words into `Spec`s.
-/

set_option autoImplicit false

namespace Work.Fx

open HvdH Computability

/-! ## Size bookkeeping -/

/-- Total encoding size of a list of values. -/
def szl (l : List Val) : ℕ := (l.map vsz).sum

@[simp] theorem szl_nil : szl ([] : List Val) = 0 := rfl

theorem szl_cons (a : Val) (l : List Val) : szl (a :: l) = vsz a + szl l := by
  simp [szl]

theorem szl_append (l₁ l₂ : List Val) : szl (l₁ ++ l₂) = szl l₁ + szl l₂ := by
  simp [szl]

theorem szl_singleton (a : Val) : szl [a] = vsz a := by simp [szl]

theorem encodeNat_length (n : ℕ) : (encodeNat n).length = n.size := by
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

theorem vsz_int (z : ℤ) : vsz (.int z) = isz z := by
  show ((if z < 0 then Glyph.neg else Glyph.pos) ::
    ((encodeNat z.natAbs).map Glyph.bit ++ [Glyph.iend])).length = isz z
  rw [List.length_cons, List.length_append, List.length_map, List.length_singleton,
    encodeNat_length, isz]

theorem vsz_nil : vsz (.nil) = 1 := rfl

theorem vsz_cons (a b : Val) : vsz (.cons a b) = vsz a + vsz b + 1 := by
  simp [vsz, Val.enc, List.length_append]

theorem vsz_cfxVal (z : ℤ × ℤ) : vsz (cfxVal z) = isz z.1 + isz z.2 + 1 := by
  simp [cfxVal, vsz_cons, vsz_int, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

theorem one_le_vsz (v : Val) : 1 ≤ vsz v := by
  cases v with
  | int z => rw [vsz_int]; simp [isz]
  | nil => simp [vsz_nil]
  | cons a b => rw [vsz_cons]; omega

theorem le_szl {l : List Val} {v : Val} (hv : v ∈ l) : vsz v ≤ szl l := by
  induction l with
  | nil => simp at hv
  | cons a t ih =>
    rcases List.mem_cons.mp hv with rfl | hv
    · rw [szl_cons]; omega
    · have := ih hv; rw [szl_cons]; omega

theorem vsz_getD_le_szl (l : List Val) {i : ℕ} (hi : i < l.length) : vsz (l.getD i .nil) ≤ szl l := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a t ih =>
    cases i with
    | zero => simp only [List.getD_cons_zero, szl_cons]; omega
    | succ j =>
      rw [List.getD_cons_succ, szl_cons]
      have h := ih (by simpa using hi)
      omega

/-! ### Arithmetic on sizes -/

theorem Nat.size_mono' {a b : ℕ} (h : a ≤ b) : a.size ≤ b.size := by
  rw [Nat.size_le]; exact lt_of_le_of_lt h (Nat.lt_size_self b)

theorem natAbs_add_size_le (a b : ℤ) :
    (a + b).natAbs.size ≤ max a.natAbs.size b.natAbs.size + 1 := by
  rw [Nat.size_le, pow_succ]
  have ha : a.natAbs < 2 ^ max a.natAbs.size b.natAbs.size :=
    lt_of_lt_of_le (Nat.lt_size_self _) (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
  have hb : b.natAbs < 2 ^ max a.natAbs.size b.natAbs.size :=
    lt_of_lt_of_le (Nat.lt_size_self _) (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
  have := Int.natAbs_add_le a b
  omega

theorem natAbs_sub_size_le (a b : ℤ) :
    (a - b).natAbs.size ≤ max a.natAbs.size b.natAbs.size + 1 := by
  have h : a - b = a + -b := by ring
  rw [h]
  simpa using natAbs_add_size_le a (-b)

theorem natAbs_mul_size_le (a b : ℤ) :
    (a * b).natAbs.size ≤ a.natAbs.size + b.natAbs.size := by
  rw [Int.natAbs_mul, Nat.size_le, pow_add]
  exact Nat.mul_lt_mul'' (Nat.lt_size_self _) (Nat.lt_size_self _)

theorem natAbs_tdiv_size_le (a b : ℤ) : (a.tdiv b).natAbs.size ≤ a.natAbs.size := by
  rw [Int.natAbs_tdiv, Nat.size_le]
  exact lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.lt_size_self _)

theorem natAbs_tdiv_le (a b : ℤ) : (a.tdiv b).natAbs ≤ a.natAbs := by
  rw [Int.natAbs_tdiv]; exact Nat.div_le_self _ _

theorem isz_add_le (a b : ℤ) : isz (a + b) ≤ max (isz a) (isz b) + 1 := by
  have := natAbs_add_size_le a b; simp only [isz]; omega

theorem isz_sub_le (a b : ℤ) : isz (a - b) ≤ max (isz a) (isz b) + 1 := by
  have := natAbs_sub_size_le a b; simp only [isz]; omega

theorem isz_mul_le (a b : ℤ) : isz (a * b) ≤ isz a + isz b := by
  have := natAbs_mul_size_le a b; simp only [isz]; omega

theorem isz_tdiv_le (a b : ℤ) : isz (a.tdiv b) ≤ isz a := by
  have := natAbs_tdiv_size_le a b; simp only [isz]; omega

theorem isz_neg (a : ℤ) : isz (-a) = isz a := by simp [isz]

theorem isz_le_of_natAbs_lt {a : ℤ} {n : ℕ} (h : a.natAbs < 2 ^ n) : isz a ≤ n + 2 := by
  have : a.natAbs.size ≤ n := Nat.size_le.mpr h
  simp only [isz]; omega

/-! ## `Spec`: words acting on a window at the top of the value stack -/

/-- `Spec main p n P Q C`: on every value stack whose top `n` values form a window `top` with `P top`,
the word `p` replaces the window by `out` with `Q top out`, at cost `≤ C top`; the values below the
window and all other stacks are untouched. -/
def Spec (main : Cmd) (p : Cmd) (n : ℕ) (P : List Val → Prop) (Q : List Val → List Val → Prop)
    (C : List Val → ℕ) : Prop :=
  ∀ (top rest : List Val), top.length = n → P top →
    WordR main p (fun vs => vs = top ++ rest) (fun _ out => ∃ o, out = o ++ rest ∧ Q top o)
      (fun _ => C top)

theorem Spec.use {main p : Cmd} {n : ℕ} {P : List Val → Prop} {Q : List Val → List Val → Prop}
    {C : List Val → ℕ} (h : Spec main p n P Q C) {top rest : List Val} (ht : top.length = n)
    (hP : P top) :
    WordR main p (fun vs => vs = top ++ rest) (fun _ out => ∃ o, out = o ++ rest ∧ Q top o)
      (fun _ => C top) := h top rest ht hP

/-- Consequence rule for `Spec`. -/
theorem Spec.mono (hk : KernelLib) {main p : Cmd} {n : ℕ} {P Q P' Q' : _} {C C' : List Val → ℕ}
    (h : Spec main p n P Q C) (hP : ∀ t, t.length = n → P' t → P t)
    (hQ : ∀ t o, t.length = n → P' t → Q t o → Q' t o)
    (hC : ∀ t, t.length = n → P' t → C t ≤ C' t) : Spec main p n P' Q' C' := by
  intro top rest ht hP'
  refine hk.conseq (main := main) (p := p)
    (P := fun vs => vs = top ++ rest) (P' := fun vs => vs = top ++ rest)
    (Q := fun _ out => ∃ o, out = o ++ rest ∧ Q top o)
    (Q' := fun _ out => ∃ o, out = o ++ rest ∧ Q' top o)
    (C := fun _ => C top) (C' := fun _ => C' top)
    (h top rest ht (hP top ht hP')) (fun vs hv => hv) ?_ ?_
  · intro vs out hv hQo
    rcases hQo with ⟨o, hout, hQo⟩
    exact ⟨o, hout, hQ top o ht hP' hQo⟩
  · intro vs hv
    exact hC top ht hP'

/-- Sequential composition of two `Spec`s. -/
theorem Spec.seq (hk : KernelLib) {main p q : Cmd} {n m : ℕ} {P Q P' Q' : _} {C C' : List Val → ℕ}
    {B : List Val → ℕ} (h1 : Spec main p n P Q C) (h2 : Spec main q m P' Q' C')
    (hlen : ∀ t o, t.length = n → P t → Q t o → o.length = m)
    (hpre : ∀ t o, t.length = n → P t → Q t o → P' o)
    (hcost : ∀ t o, t.length = n → P t → Q t o → C' o ≤ B t) :
    Spec main (.seq p q) n P (fun t out => ∃ o, Q t o ∧ Q' o out) (fun t => C t + B t) := by
  intro top rest ht hP
  have h2' : WordR main q (fun vs => ∃ o, vs = o ++ rest ∧ Q top o ∧ P' o)
      (fun vs out => ∃ o, vs = o ++ rest ∧ Q top o ∧ ∃ o', out = o' ++ rest ∧ Q' o o')
      (fun _ => B top) := by
    intro vs hvs s R hR
    rcases hvs with ⟨o, hvs_eq, hQ, hPo⟩
    subst hvs_eq
    obtain ⟨out, s', k, ⟨o', hout_eq, hQ'⟩, hEv, hCost, hStk, hOth⟩ :=
      h2 o rest (hlen top o ht hP hQ) hPo (o ++ rest) rfl s R hR
    exact ⟨out, s', k, ⟨o, rfl, hQ, o', hout_eq, hQ'⟩, hEv, le_trans hCost (hcost top o ht hP hQ),
      hStk, hOth⟩
  refine hk.conseq (main := main) (p := (.seq p q))
    (P := fun vs => vs = top ++ rest) (P' := fun vs => vs = top ++ rest)
    (Q := fun vs out => ∃ mid, (∃ o, mid = o ++ rest ∧ Q top o) ∧
        (∃ o, mid = o ++ rest ∧ Q top o ∧ ∃ o', out = o' ++ rest ∧ Q' o o'))
    (Q' := fun vs out => ∃ o, out = o ++ rest ∧ (∃ o', Q top o' ∧ Q' o' o))
    (C := fun vs => (fun _ => C top) vs + (fun _ => B top) vs)
    (C' := fun _ => C top + B top)
    (hk.seq (main := main) (p := p) (q := q)
      (P := fun vs => vs = top ++ rest) (Q := fun _ out => ∃ o, out = o ++ rest ∧ Q top o)
      (C := fun _ => C top) (P' := fun vs => ∃ o, vs = o ++ rest ∧ Q top o ∧ P' o)
      (Q' := fun vs out => ∃ o, vs = o ++ rest ∧ Q top o ∧ ∃ o', out = o' ++ rest ∧ Q' o o')
      (C' := fun _ => B top)
      (B := fun _ => B top) (h1 top rest ht hP) h2' ?_) (fun vs hv => hv) ?_ (fun vs _ => le_rfl)
  · intro vs mid hvs hmid
    rcases hmid with ⟨o, hmid_eq, hQo⟩
    exact ⟨⟨o, hmid_eq, hQo, hpre top o ht hP hQo⟩, le_rfl⟩
  · intro vs out hv h
    rcases h with ⟨mid, hA, hB⟩
    rcases hA with ⟨o1, hm1, hQ1⟩
    rcases hB with ⟨o2, hm2, hQ2, o3, hout, hQ3⟩
    exact ⟨o3, hout, o2, hQ2, hQ3⟩

/-- Sequential composition for two words with *deterministic* windows. -/
theorem Spec.seq_det (hk : KernelLib) {main p q : Cmd} {n m : ℕ} {A B D : List Val}
    {C : List Val → ℕ} {c : ℕ}
    (h1 : Spec main p n (fun t => t = A) (fun _ o => o = B) C)
    (h2 : Spec main q m (fun t => t = B) (fun _ o => o = D) (fun _ => c)) (hB : B.length = m) :
    Spec main (.seq p q) n (fun t => t = A) (fun _ o => o = D) (fun t => C t + c) := by
  refine Spec.mono hk (Spec.seq hk h1 h2 ?_ ?_ ?_) (fun t _ h => h) ?_ (fun t _ _ => le_rfl)
  · intro t o ht hP hQ; rw [hQ]; exact hB
  · intro t o ht hP hQ; rw [hQ]
  · intro t o ht hP hQ; exact le_rfl
  · intro t o ht hP hQ
    rcases hQ with ⟨o', ho', hout⟩
    exact hout

/-- Consequence rule with an upper bound on the window size. -/
theorem Spec.bound (hk : KernelLib) {main p : Cmd} {n : ℕ} {P Q : _} {C : List Val → ℕ}
    (h : Spec main p n P Q C) {K M : ℕ} (hC : ∀ t, t.length = n → P t → C t ≤ K * (M + 1)) :
    Spec main p n P Q (fun _ => K * (M + 1)) :=
  Spec.mono hk h (fun t _ h => h) (fun t o _ _ h => h) (fun t ht hP => hC t ht hP)

/-! ### Basic list helpers -/

theorem cons_tail_eq {a b : Val} {l l' : List Val} (h : a :: l = b :: l') : l = l' :=
  (List.cons.inj h).2

theorem cons_inj3 {a b a' b' : Val} {l l' : List Val} (h : a :: b :: l = a' :: b' :: l') :
    a = a' ∧ b = b' ∧ l = l' := by
  have h1 := List.cons.inj h
  have h2 := List.cons.inj h1.2
  exact ⟨h1.1, h2.1, h2.2⟩

theorem val_cons_inj3 {a b a' b' : Val} {l l' : List Val}
    (h : Val.cons a b :: l = Val.cons a' b' :: l') : a = a' ∧ b = b' ∧ l = l' := by
  have h1 := List.cons.inj h
  have h2 := Val.cons.inj h1.1
  exact ⟨h2.1, h2.2, h1.2⟩

theorem int_cons_inj3 {a b a' b' : ℤ} {l l' : List Val}
    (h : Val.int a :: Val.int b :: l = Val.int a' :: Val.int b' :: l') :
    a = a' ∧ b = b' ∧ l = l' := by
  have h1 := cons_inj3 h
  exact ⟨Val.int.inj h1.1, Val.int.inj h1.2.1, h1.2.2⟩

theorem tail_eq_of_append_eq {A B rest rest' : List Val} (hA : A.length = B.length)
    (h : A ++ rest = B ++ rest') : rest = rest' := by
  have h1 : (A ++ rest).drop A.length = (B ++ rest').drop B.length := by rw [h, hA]
  simpa [List.drop_left] using h1

theorem take_succ_of_length {l rest : List Val} {k : ℕ} (h : l.length = k + 1) :
    (l ++ rest).take (k + 1) = l := by
  rw [← h, List.take_left]

theorem getD_append_of_lt {l rest : List Val} {k : ℕ} (h : k < l.length) :
    (l ++ rest).getD k .nil = l.getD k .nil := by
  induction l generalizing k with
  | nil => simp at h
  | cons a t ih =>
    cases k with
    | zero => simp
    | succ j =>
      rw [List.getD_cons_succ, List.cons_append, List.getD_cons_succ, ih]
      simpa using h

theorem eraseIdx_append_of_lt {l rest : List Val} {k : ℕ} (h : k < l.length) :
    (l ++ rest).eraseIdx k = l.eraseIdx k ++ rest := by
  induction l generalizing k with
  | nil => simp at h
  | cons a t ih =>
    cases k with
    | zero => rfl
    | succ j =>
      rw [List.cons_append, List.eraseIdx_cons_succ, ih (by simpa using h),
        List.eraseIdx_cons_succ, List.cons_append]

theorem getD_eraseIdx_append {l rest : List Val} {k : ℕ} (h : k < l.length) :
    ((l ++ rest).getD k .nil) :: ((l ++ rest).eraseIdx k) =
      (l.getD k .nil :: l.eraseIdx k) ++ rest := by
  rw [getD_append_of_lt h, eraseIdx_append_of_lt h]
  rfl

/-- `binCost C` is a function of the window only. -/
theorem binCost_cons_int (C : ℤ → ℤ → ℕ) (a b : ℤ) (l : List Val) :
    binCost C (.int a :: .int b :: l) = C a b := rfl

/-- `unCost C` is a function of the window only. -/
theorem unCost_cons_int (C : ℤ → ℕ) (a : ℤ) (l : List Val) :
    unCost C (.int a :: l) = C a := rfl

/-! ### Adapters: `IntLib` words -/

/-- `BinOp` as a `Spec` on a window of two integers. -/
theorem Spec.binOp (hk : KernelLib) {main p : Cmd} {P : ℤ → ℤ → Prop} {f : ℤ → ℤ → ℤ}
    {C : ℤ → ℤ → ℕ} (h : BinOp main p P f C) :
    Spec main p 2 (fun t => ∃ a b, t = [.int a, .int b] ∧ P a b)
      (fun t o => ∃ a b, t = [.int a, .int b] ∧ o = [.int (f a b)]) (binCost C) := by
  intro top rest ht hP
  rcases hP with ⟨a, b, rfl, hPab⟩
  refine hk.conseq (main := main) (p := p)
    (P := fun vs => ∃ a b rest, vs = .int a :: .int b :: rest ∧ P a b)
    (Q := fun vs out => ∃ a b rest, vs = .int a :: .int b :: rest ∧ out = .int (f a b) :: rest)
    (C := binCost C)
    (P' := fun vs => vs = [.int a, .int b] ++ rest)
    (Q' := fun _ out => ∃ o, out = o ++ rest ∧
      ∃ a₂ b₂, ([.int a, .int b] : List Val) = [.int a₂, .int b₂] ∧ o = [.int (f a₂ b₂)])
    (C' := fun _ => binCost C [.int a, .int b]) h ?_ ?_ ?_
  · intro vs hv
    exact ⟨a, b, rest, hv, hPab⟩
  · intro vs out hv hQ
    rcases hQ with ⟨a', b', rest', hvs, hout⟩
    obtain ⟨h1, h2, h3⟩ := int_cons_inj3 (hvs.symm.trans (by simpa using hv))
    exact ⟨[.int (f a' b')], by rw [hout, h3]; rfl, a', b', by rw [h1, h2], rfl⟩
  · intro vs hv
    rw [hv, List.cons_append]
    exact le_rfl

/-- `UnOp` as a `Spec` on a window of one integer. -/
theorem Spec.unOp (hk : KernelLib) {main p : Cmd} {P : ℤ → Prop} {f : ℤ → ℤ} {C : ℤ → ℕ}
    (h : UnOp main p P f C) :
    Spec main p 1 (fun t => ∃ a, t = [.int a] ∧ P a)
      (fun t o => ∃ a, t = [.int a] ∧ o = [.int (f a)]) (unCost C) := by
  intro top rest ht hP
  rcases hP with ⟨a, rfl, hPa⟩
  refine hk.conseq (main := main) (p := p)
    (P := fun vs => ∃ a rest, vs = .int a :: rest ∧ P a)
    (Q := fun vs out => ∃ a rest, vs = .int a :: rest ∧ out = .int (f a) :: rest)
    (C := unCost C)
    (P' := fun vs => vs = [.int a] ++ rest)
    (Q' := fun _ out => ∃ o, out = o ++ rest ∧ ∃ a₂, ([.int a] : List Val) = [.int a₂] ∧ o = [.int (f a₂)])
    (C' := fun _ => unCost C [.int a]) h ?_ ?_ ?_
  · intro vs hv
    exact ⟨a, rest, hv, hPa⟩
  · intro vs out hv hQ
    rcases hQ with ⟨a', rest', hvs, hout⟩
    have h1 := List.cons.inj (hvs.symm.trans (by simpa using hv))
    have ha : a' = a := Val.int.inj h1.1
    have hr : rest' = rest := h1.2
    exact ⟨[.int (f a')], by rw [hout, hr]; rfl, a', by rw [ha], rfl⟩
  · intro vs hv
    rw [hv, List.cons_append]
    exact le_rfl

/-! ### Adapters: `KernelLib` words -/

theorem Spec.swapK (hk : KernelLib) {main prog : Cmd} {K : ℕ}
    (h : WordR main prog (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = b :: a :: rest)
      (fun vs => K * (vsz (vs.getD 0 .nil) + vsz (vs.getD 1 .nil) + 1))) :
    Spec main prog 2 (fun _ => True) (fun t o => ∃ a b, t = [a, b] ∧ o = [b, a])
      (fun t => K * (vsz (t.getD 0 .nil) + vsz (t.getD 1 .nil) + 1)) := by
  intro top rest ht _
  obtain ⟨a, b, rfl⟩ : ∃ a b, top = [a, b] := by
    match top with
    | [a, b] => exact ⟨a, b, rfl⟩
  refine hk.conseq (main := main) (p := prog)
    (P := fun vs => 2 ≤ vs.length)
    (Q := fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = b :: a :: rest)
    (C := fun vs => K * (vsz (vs.getD 0 .nil) + vsz (vs.getD 1 .nil) + 1))
    (P' := fun vs => vs = [a, b] ++ rest)
    (Q' := fun _ out => ∃ o, out = o ++ rest ∧ ∃ a₂ b₂, ([a, b] : List Val) = [a₂, b₂] ∧ o = [b₂, a₂])
    (C' := fun _ => K * (vsz a + vsz b + 1)) h ?_ ?_ ?_
  · intro vs hv
    rw [hv, List.length_append]
    simp
  · intro vs out hv hQ
    rcases hQ with ⟨a', b', rest', hvs, hout⟩
    obtain ⟨h1, h2, h3⟩ := cons_inj3 (hvs.symm.trans (by simpa using hv))
    exact ⟨[b', a'], by rw [hout, h3]; rfl, a', b', by rw [h1, h2], rfl⟩
  · intro vs hv
    rw [hv]
    simp [List.getD_cons_zero, List.getD_cons_succ]

theorem Spec.dupK (hk : KernelLib) {main prog : Cmd} {K : ℕ}
    (h : WordR main prog (fun vs => vs ≠ [])
      (fun vs out => ∃ v rest, vs = v :: rest ∧ out = v :: v :: rest)
      (fun vs => K * (vsz (vs.headD .nil) + 1))) :
    Spec main prog 1 (fun _ => True) (fun t o => ∃ v, t = [v] ∧ o = [v, v])
      (fun t => K * (vsz (t.getD 0 .nil) + 1)) := by
  intro top rest ht _
  obtain ⟨a, rfl⟩ : ∃ a, top = [a] := by
    match top with
    | [a] => exact ⟨a, rfl⟩
  refine hk.conseq (main := main) (p := prog)
    (P := fun vs => vs ≠ [])
    (Q := fun vs out => ∃ v rest, vs = v :: rest ∧ out = v :: v :: rest)
    (C := fun vs => K * (vsz (vs.headD .nil) + 1))
    (P' := fun vs => vs = [a] ++ rest)
    (Q' := fun _ out => ∃ o, out = o ++ rest ∧ ∃ v, ([a] : List Val) = [v] ∧ o = [v, v])
    (C' := fun _ => K * (vsz a + 1)) h ?_ ?_ ?_
  · intro vs hv
    rw [hv]
    exact List.cons_ne_nil a rest
  · intro vs out hv hQ
    rcases hQ with ⟨v, rest', hvs, hout⟩
    have h1 := List.cons.inj (hvs.symm.trans (by simpa using hv))
    have ha : v = a := h1.1
    have hr : rest' = rest := h1.2
    exact ⟨[v, v], by rw [hout, hr]; rfl, v, by rw [ha], rfl⟩
  · intro vs hv
    rw [hv]
    exact le_rfl

theorem Spec.dropK (hk : KernelLib) {main prog : Cmd} {K : ℕ}
    (h : WordR main prog (fun vs => vs ≠ [])
      (fun vs out => ∃ v rest, vs = v :: rest ∧ out = rest)
      (fun vs => K * (vsz (vs.headD .nil) + 1))) :
    Spec main prog 1 (fun _ => True) (fun _ o => o = [])
      (fun t => K * (vsz (t.getD 0 .nil) + 1)) := by
  intro top rest ht _
  obtain ⟨a, rfl⟩ : ∃ a, top = [a] := by
    match top with
    | [a] => exact ⟨a, rfl⟩
  refine hk.conseq (main := main) (p := prog)
    (P := fun vs => vs ≠ [])
    (Q := fun vs out => ∃ v rest, vs = v :: rest ∧ out = rest)
    (C := fun vs => K * (vsz (vs.headD .nil) + 1))
    (P' := fun vs => vs = [a] ++ rest)
    (Q' := fun _ out => ∃ o, out = o ++ rest ∧ o = [])
    (C' := fun _ => K * (vsz a + 1)) h ?_ ?_ ?_
  · intro vs hv
    rw [hv]
    exact List.cons_ne_nil a rest
  · intro vs out hv hQ
    rcases hQ with ⟨v, rest', hvs, hout⟩
    have h1 := List.cons.inj (hvs.symm.trans (by simpa using hv))
    exact ⟨[], by rw [hout, h1.2]; rfl, rfl⟩
  · intro vs hv
    rw [hv]
    exact le_rfl

theorem Spec.pushValK (hk : KernelLib) {main prog : Cmd} {K : ℕ} {v : Val}
    (h : WordR main prog (fun _ => True) (fun vs out => out = v :: vs) (fun _ => K * (vsz v + 1))) :
    Spec main prog 0 (fun _ => True) (fun _ o => o = [v]) (fun _ => K * (vsz v + 1)) := by
  intro top rest ht _
  match top with
  | [] =>
    refine hk.conseq (main := main) (p := prog)
      (P := fun _ => True) (Q := fun vs out => out = v :: vs) (C := fun _ => K * (vsz v + 1))
      (P' := fun vs => vs = rest) (Q' := fun _ out => ∃ o, out = o ++ rest ∧ o = [v])
      (C' := fun _ => K * (vsz v + 1)) h ?_ ?_ ?_
    · intro vs hv; exact trivial
    · intro vs out hv hQ
      exact ⟨[v], by rw [hQ, hv]; rfl, rfl⟩
    · intro vs hv; exact le_rfl

theorem Spec.consVK (hk : KernelLib) {main prog : Cmd} {K : ℕ}
    (h : WordR main prog (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = .cons a b :: rest)
      (fun _ => K)) :
    Spec main prog 2 (fun _ => True) (fun t o => ∃ a b, t = [a, b] ∧ o = [.cons a b])
      (fun _ => K) := by
  intro top rest ht _
  obtain ⟨a, b, rfl⟩ : ∃ a b, top = [a, b] := by
    match top with
    | [a, b] => exact ⟨a, b, rfl⟩
  refine hk.conseq (main := main) (p := prog)
    (P := fun vs => 2 ≤ vs.length)
    (Q := fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = .cons a b :: rest)
    (C := fun _ => K)
    (P' := fun vs => vs = [a, b] ++ rest)
    (Q' := fun _ out => ∃ o, out = o ++ rest ∧ ∃ a₂ b₂, ([a, b] : List Val) = [a₂, b₂] ∧ o = [.cons a₂ b₂])
    (C' := fun _ => K) h ?_ ?_ ?_
  · intro vs hv
    rw [hv]; simp
  · intro vs out hv hQ
    rcases hQ with ⟨a', b', rest', hvs, hout⟩
    obtain ⟨h1, h2, h3⟩ := cons_inj3 (hvs.symm.trans (by simpa using hv))
    exact ⟨[.cons a' b'], by rw [hout, h3]; rfl, a', b', by rw [h1, h2], rfl⟩
  · intro vs hv; exact le_rfl

theorem Spec.unconsVK (hk : KernelLib) {main prog : Cmd} {K : ℕ}
    (h : WordR main prog (fun vs => ∃ a b rest, vs = .cons a b :: rest)
      (fun vs out => ∃ a b rest, vs = .cons a b :: rest ∧ out = a :: b :: rest)
      (fun _ => K)) :
    Spec main prog 1 (fun t => ∃ a b, t = [.cons a b])
      (fun t o => ∃ a b, t = [.cons a b] ∧ o = [a, b]) (fun _ => K) := by
  intro top rest ht hP
  rcases hP with ⟨a, b, rfl⟩
  refine hk.conseq (main := main) (p := prog)
    (P := fun vs => ∃ a b rest, vs = .cons a b :: rest)
    (Q := fun vs out => ∃ a b rest, vs = .cons a b :: rest ∧ out = a :: b :: rest)
    (C := fun _ => K)
    (P' := fun vs => vs = [.cons a b] ++ rest)
    (Q' := fun _ out => ∃ o, out = o ++ rest ∧
      ∃ a₂ b₂, ([.cons a b] : List Val) = [.cons a₂ b₂] ∧ o = [a₂, b₂])
    (C' := fun _ => K) h ?_ ?_ ?_
  · intro vs hv
    exact ⟨a, b, rest, hv⟩
  · intro vs out hv hQ
    rcases hQ with ⟨a', b', rest', hvs, hout⟩
    obtain ⟨h1, h2, h3⟩ := val_cons_inj3 (hvs.symm.trans (by simpa using hv))
    exact ⟨[a', b'], by rw [hout, h3]; rfl, a', b', by rw [h1, h2], rfl⟩
  · intro vs hv; exact le_rfl

theorem Spec.rollK (hk : KernelLib) {main prog : Cmd} {K k : ℕ}
    (h : WordR main prog (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs.eraseIdx k)
      (fun vs => K * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1))) :
    Spec main prog (k + 1) (fun _ => True) (fun t o => o = t.getD k .nil :: t.eraseIdx k)
      (fun t => K * (k + 1) * (szl t + 1)) := by
  intro top rest ht _
  have hk_len : k < top.length := by omega
  refine hk.conseq (main := main) (p := prog)
    (P := fun vs => k < vs.length)
    (Q := fun vs out => out = vs.getD k .nil :: vs.eraseIdx k)
    (C := fun vs => K * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1))
    (P' := fun vs => vs = top ++ rest)
    (Q' := fun _ out => ∃ o, out = o ++ rest ∧ o = top.getD k .nil :: top.eraseIdx k)
    (C' := fun _ => K * (k + 1) * (szl top + 1)) h ?_ ?_ ?_
  · intro vs hv
    rw [hv]
    have : (top ++ rest).length = top.length + rest.length := List.length_append ..
    omega
  · intro vs out hv hQ
    rw [hv] at hQ
    exact ⟨top.getD k .nil :: top.eraseIdx k, by rw [hQ, getD_eraseIdx_append hk_len], rfl⟩
  · intro vs hv
    rw [hv, take_succ_of_length (by omega)]
    rfl

theorem Spec.pickK (hk : KernelLib) {main prog : Cmd} {K k : ℕ}
    (h : WordR main prog (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs)
      (fun vs => K * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1))) :
    Spec main prog (k + 1) (fun _ => True) (fun t o => o = t.getD k .nil :: t)
      (fun t => K * (k + 1) * (szl t + 1)) := by
  intro top rest ht _
  have hk_len : k < top.length := by omega
  refine hk.conseq (main := main) (p := prog)
    (P := fun vs => k < vs.length)
    (Q := fun vs out => out = vs.getD k .nil :: vs)
    (C := fun vs => K * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1))
    (P' := fun vs => vs = top ++ rest)
    (Q' := fun _ out => ∃ o, out = o ++ rest ∧ o = top.getD k .nil :: top)
    (C' := fun _ => K * (k + 1) * (szl top + 1)) h ?_ ?_ ?_
  · intro vs hv
    rw [hv]
    have : (top ++ rest).length = top.length + rest.length := List.length_append ..
    omega
  · intro vs out hv hQ
    rw [hv] at hQ
    exact ⟨top.getD k .nil :: top, by rw [hQ, getD_append_of_lt hk_len, List.cons_append], rfl⟩
  · intro vs hv
    rw [hv, take_succ_of_length (by omega)]
    rfl

end Work.Fx
