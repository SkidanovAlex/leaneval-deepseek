import Mathlib
import Submission.Work.Fx.ExpDefs

/-!
# The prelude of `Work.Fx.expCplx`: building the seed state and the dummy list
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.Fx

open HvdH

namespace ExpAsm

open HvdH

/-! ## WordR-level exact-window helpers -/

theorem w_exact {main p : Cmd} {P : List Val → Prop} {Q : List Val → List Val → Prop}
    {C : List Val → ℕ} {A B : List Val} {c : ℕ}
    (h : WordR main p P Q C) (hpre : P A) (hpost : ∀ out, Q A out → out = B) (hc : C A ≤ c) :
    WordR main p (fun vs => vs = A) (fun _ out => out = B) (fun _ => c) := by
  intro vs hvs s R hs
  subst vs
  obtain ⟨out, s', n, hPost, hev, hn, hstk, hfr⟩ := h A hpre s R hs
  exact ⟨out, s', n, hpost out hPost, hev, le_trans hn hc, hstk, hfr⟩

theorem w_seq2 {main p q : Cmd} {A mid B : List Val} {c1 c2 : ℕ}
    (h1 : WordR main p (fun vs => vs = A) (fun _ out => out = mid) (fun _ => c1))
    (h2 : WordR main q (fun vs => vs = mid) (fun _ out => out = B) (fun _ => c2)) :
    WordR main (Cmd.seq p q) (fun vs => vs = A) (fun _ out => out = B) (fun _ => c1 + c2) := by
  intro vs hvs s R hs
  subst vs
  obtain ⟨m, s1, n1, hm, hev1, hn1, hstk1, hfr1⟩ := h1 A rfl s R hs
  obtain ⟨out, s2, n2, hB, hev2, hn2, hstk2, hfr2⟩ := h2 m hm s1 R hstk1
  exact ⟨out, s2, n1 + n2, hB, Eval.seq hev1 hev2, Nat.add_le_add hn1 hn2, hstk2,
    fun k hk => by rw [hfr2 k hk, hfr1 k hk]⟩

theorem w_binOp {main prog : Cmd} {P : ℤ → ℤ → Prop} {f : ℤ → ℤ → ℤ} {C : ℤ → ℤ → ℕ}
    (h : BinOp main prog P f C) {a b : ℤ} {rest : List Val} (hP : P a b) {c : ℕ}
    (hc : C a b ≤ c) :
    WordR main prog (fun vs => vs = .int a :: .int b :: rest)
      (fun _ out => out = .int (f a b) :: rest) (fun _ => c) := by
  refine w_exact h ⟨a, b, rest, rfl, hP⟩ ?_ ?_
  · intro out hQ
    rcases hQ with ⟨a', b', rest', hvs, hout⟩
    obtain ⟨h1, h2⟩ := List.cons.inj hvs
    obtain ⟨ha, hr⟩ := List.cons.inj h2
    rw [hout, ← Val.int.inj h1, ← Val.int.inj ha, ← hr]
  · simpa only [binCost] using hc

theorem w_unOp {main prog : Cmd} {P : ℤ → Prop} {f : ℤ → ℤ} {C : ℤ → ℕ}
    (h : UnOp main prog P f C) {a : ℤ} {rest : List Val} (hP : P a) {c : ℕ} (hc : C a ≤ c) :
    WordR main prog (fun vs => vs = .int a :: rest) (fun _ out => out = .int (f a) :: rest)
      (fun _ => c) := by
  refine w_exact h ⟨a, rest, rfl, hP⟩ ?_ ?_
  · intro out hQ
    rcases hQ with ⟨a', rest', hvs, hout⟩
    obtain ⟨h1, h2⟩ := List.cons.inj hvs
    rw [hout, ← Val.int.inj h1, ← h2]
  · simpa only [unCost] using hc

theorem w_pick {main : Cmd} {prog : ℕ → Cmd} {K : ℕ}
    (h : ∀ k, WordR main (prog k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs)
      (fun vs => K * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    (k : ℕ) (A : List Val) (v : Val) (hget : A.getD k .nil = v) (hk : k < A.length) {c : ℕ}
    (hc : K * (k + 1) * (((A.take (k + 1)).map vsz).sum + 1) ≤ c) :
    WordR main (prog k) (fun vs => vs = A) (fun _ out => out = v :: A) (fun _ => c) := by
  refine w_exact (h k) hk ?_ hc
  intro out hout
  rw [hout, hget]

theorem w_roll {main : Cmd} {prog : ℕ → Cmd} {K : ℕ}
    (h : ∀ k, WordR main (prog k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs.eraseIdx k)
      (fun vs => K * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    (k : ℕ) (A : List Val) (v : Val) (hget : A.getD k .nil = v) (hk : k < A.length) {c : ℕ}
    (hc : K * (k + 1) * (((A.take (k + 1)).map vsz).sum + 1) ≤ c) :
    WordR main (prog k) (fun vs => vs = A) (fun _ out => out = v :: A.eraseIdx k) (fun _ => c) := by
  refine w_exact (h k) hk ?_ hc
  intro out hout
  rw [hout, hget]

theorem w_drop {main prog : Cmd} {K : ℕ}
    (h : WordR main prog (fun vs => vs ≠ [])
      (fun vs out => ∃ v rest, vs = v :: rest ∧ out = rest)
      (fun vs => K * (vsz (vs.headD .nil) + 1)))
    (a : Val) (rest : List Val) {c : ℕ} (hc : K * (vsz a + 1) ≤ c) :
    WordR main prog (fun vs => vs = a :: rest) (fun _ out => out = rest) (fun _ => c) := by
  refine w_exact h ?_ ?_ ?_
  · simp
  · intro out hQ
    rcases hQ with ⟨v, rest', hvs, hout⟩
    obtain ⟨h1, h2⟩ := List.cons.inj hvs
    rw [hout, ← h2]
  · simpa [List.headD] using hc

theorem w_swap {main prog : Cmd} {K : ℕ}
    (h : WordR main prog (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = b :: a :: rest)
      (fun vs => K * (vsz (vs.getD 0 .nil) + vsz (vs.getD 1 .nil) + 1)))
    (a b : Val) (rest : List Val) {c : ℕ} (hc : K * (vsz a + vsz b + 1) ≤ c) :
    WordR main prog (fun vs => vs = a :: b :: rest) (fun _ out => out = b :: a :: rest)
      (fun _ => c) := by
  refine w_exact h ?_ ?_ ?_
  · simp
  · intro out hQ
    rcases hQ with ⟨a', b', rest', hvs, hout⟩
    obtain ⟨h1, h2⟩ := List.cons.inj hvs
    obtain ⟨h3, h4⟩ := List.cons.inj h2
    rw [hout, ← h1, ← h3, ← h4]
  · simpa [List.getD] using hc

theorem w_pushVal {main prog : Cmd} {K : ℕ} {v : Val}
    (h : WordR main prog (fun _ => True) (fun vs out => out = v :: vs) (fun _ => K * (vsz v + 1))) :
    (A : List Val) → {c : ℕ} → K * (vsz v + 1) ≤ c →
    WordR main prog (fun vs => vs = A) (fun _ out => out = v :: A) (fun _ => c) := by
  intro A c hc
  refine w_exact h trivial ?_ hc
  intro out hout
  rw [hout]

theorem w_chunk {main prog : Cmd} {K : ℕ}
    (h : ∀ (x b N : ℕ), 1 ≤ b → x < 2 ^ (b * N) →
      WordR main prog (fun vs => ∃ rest, vs = .int (x : ℤ) :: .int (b : ℤ) :: .int (N : ℤ) :: rest)
        (fun vs out => ∃ rest, vs = .int (x : ℤ) :: .int (b : ℤ) :: .int (N : ℤ) :: rest ∧
          out = intList (chunks x b N) :: rest)
        (fun _ => K * (isz (x : ℤ) + N * (b + 1) + isz (b : ℤ) + isz (N : ℤ))))
    (x b N : ℕ) (hb : 1 ≤ b) (hx : x < 2 ^ (b * N)) (rest : List Val) {c : ℕ}
    (hc : K * (isz (x : ℤ) + N * (b + 1) + isz (b : ℤ) + isz (N : ℤ)) ≤ c) :
    WordR main prog (fun vs => vs = .int (x : ℤ) :: .int (b : ℤ) :: .int (N : ℤ) :: rest)
      (fun _ out => out = intList (chunks x b N) :: rest) (fun _ => c) := by
  refine w_exact (h x b N hb hx) ⟨rest, rfl⟩ ?_ hc
  intro out hQ
  rcases hQ with ⟨rest', hvs, hout⟩
  obtain ⟨e1, e2⟩ := List.cons.inj hvs
  obtain ⟨e2, e3⟩ := List.cons.inj e2
  obtain ⟨e3, e4⟩ := List.cons.inj e3
  rw [hout, ← e4]

/-! ## List bookkeeping -/

theorem sum_map_le (l : List Val) {S : ℕ} (h : ∀ v ∈ l, vsz v ≤ S) :
    (l.map vsz).sum ≤ l.length * S := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.map_cons, List.sum_cons, List.length_cons]
    have ha : vsz a ≤ S := h a (by simp)
    have ht : ∀ v ∈ t, vsz v ≤ S := fun v hv => h v (by simp [hv])
    have := ih ht
    nlinarith

theorem sum_take_le {A : List Val} {S : ℕ} (h : ∀ v ∈ A, vsz v ≤ S) (k : ℕ) :
    ((A.take (k + 1)).map vsz).sum ≤ (k + 1) * S := by
  have h1 : ((A.take (k + 1)).map vsz).sum ≤ (A.take (k + 1)).length * S :=
    sum_map_le (A.take (k + 1)) (fun v hv => h v (List.mem_of_mem_take hv))
  have h2 : (A.take (k + 1)).length ≤ k + 1 := by
    rw [List.length_take]; exact min_le_left _ _
  exact le_trans h1 (Nat.mul_le_mul_right S h2)

end ExpAsm
end Work.Fx
