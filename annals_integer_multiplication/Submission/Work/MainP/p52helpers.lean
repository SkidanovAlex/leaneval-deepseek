import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Kernel.Raw
import Submission.Work.ConvR.basic
import Submission.Work.ConvR.permTop
import Submission.Work.ConvR.dropUnder

/-! # Auxiliaries for `Work.MainP.prop52`: cost allowance and `WordC` step words -/

set_option autoImplicit false
set_option maxRecDepth 4000

namespace Work.MainP

open HvdH

/-! ## Uniform cost allowance -/

/-- Uniform allowance for one elementary step of the §5.2 pipeline: `KB` dominates all the
constants of the area `Prop`s, `SB` all the encoding sizes and `Pm` the numerical sizes of the
parameters. -/
def ALLOW (KB SB Pm : ℕ) : ℕ := 1000000 * (KB + 1) * (SB + 1 + Pm)

theorem nat_mul4 {a b c d : ℕ} (h1 : a ≤ c) (h2 : b ≤ d) : a * b ≤ c * d :=
  Nat.mul_le_mul h1 h2

theorem pick_cost_le {Kp KB SB Pm k s : ℕ} (hK : Kp ≤ KB) (hk : k ≤ 10) (hs : s ≤ 12 * SB) :
    Kp * (k + 1) * (s + 1) ≤ ALLOW KB SB Pm := by
  rw [ALLOW]
  have h1 : Kp * (k + 1) ≤ KB * 11 := Nat.mul_le_mul hK (by omega)
  have h2 : s + 1 ≤ 13 * (SB + 1) := by omega
  have h3 : Kp * (k + 1) * (s + 1) ≤ (KB * 11) * (13 * (SB + 1)) := Nat.mul_le_mul h1 h2
  exact le_trans h3 (by nlinarith)

theorem perm_cost_le {KP KB SB Pm n s : ℕ} (hK : KP ≤ KB) (hn : n ≤ 13) (hs : s ≤ 13 * SB) :
    KP * (n + 1) * (n + 1) * (s + 1) ≤ ALLOW KB SB Pm := by
  rw [ALLOW]
  have ha : KP * (n + 1) ≤ KB * 14 := Nat.mul_le_mul hK (by omega)
  have h1 : KP * (n + 1) * (n + 1) ≤ KB * 14 * 14 := Nat.mul_le_mul ha (by omega)
  have h2 : s + 1 ≤ 14 * (SB + 1) := by omega
  have h3 : KP * (n + 1) * (n + 1) * (s + 1) ≤ (KB * 14 * 14) * (14 * (SB + 1)) :=
    Nat.mul_le_mul h1 h2
  exact le_trans h3 (by nlinarith)

theorem roll_cost_le {Kr KB SB Pm k s : ℕ} (hK : Kr ≤ KB) (hk : k ≤ 5) (hs : s ≤ 3 * SB) :
    Kr * (k + 1) * (s + 1) ≤ ALLOW KB SB Pm := by
  rw [ALLOW]
  have h1 : Kr * (k + 1) ≤ KB * 6 := Nat.mul_le_mul hK (by omega)
  have h2 : s + 1 ≤ 4 * (SB + 1) := by omega
  have h3 : Kr * (k + 1) * (s + 1) ≤ (KB * 6) * (4 * (SB + 1)) := Nat.mul_le_mul h1 h2
  exact le_trans h3 (by nlinarith)

theorem drop_cost_le {Kd KB SB Pm s : ℕ} (hK : Kd ≤ KB) (hs : s ≤ SB) :
    Kd * (s + 1) ≤ ALLOW KB SB Pm := by
  rw [ALLOW]
  have h3 : Kd * (s + 1) ≤ KB * (SB + 1) := Nat.mul_le_mul hK (by omega)
  exact le_trans h3 (by nlinarith)

theorem arith_cost_le {Km KB SB Pm a b S : ℕ} (hK : Km ≤ KB) (ha : a ≤ S) (hb : b ≤ S)
    (hP : S * S ≤ Pm) : Km * a * b ≤ ALLOW KB SB Pm := by
  rw [ALLOW]
  have h2 : Km * a ≤ KB * S := Nat.mul_le_mul hK ha
  have h1 : Km * a * b ≤ KB * (S * S) := by
    calc Km * a * b ≤ (KB * S) * S := Nat.mul_le_mul h2 hb
      _ = KB * (S * S) := Nat.mul_assoc KB S S
  have h3 : KB * (S * S) ≤ KB * Pm := Nat.mul_le_mul_left KB hP
  exact le_trans h1 (le_trans h3 (by nlinarith))

theorem arith1_cost_le {Ku KB SB Pm a b S : ℕ} (hK : Ku ≤ KB) (ha : a ≤ S) (hb : b ≤ S)
    (hS : 2 ≤ S) (hP : S * S ≤ Pm) : Ku * (a + b) ≤ ALLOW KB SB Pm := by
  rw [ALLOW]
  have h2 : a + b ≤ 2 * S := by omega
  have h1 : Ku * (a + b) ≤ KB * (2 * S) := Nat.mul_le_mul hK h2
  have h3 : 2 * S ≤ S * S := by nlinarith
  exact le_trans h1 (le_trans (Nat.mul_le_mul_left KB (le_trans h3 hP)) (by nlinarith))

/-- A conjugation word on a vector of length `s`: cost `K(s+1)(p+1)+K`. -/
theorem conj_cost_le {Kcj KB SB Pm s p : ℕ} (hK : Kcj ≤ KB) (hs : (s + 1) * (p + 1) ≤ SB) :
    Kcj * (s + 1) * (p + 1) + Kcj ≤ ALLOW KB SB Pm := by
  rw [ALLOW]
  have h1 : Kcj * (s + 1) * (p + 1) ≤ KB * SB := by
    calc Kcj * (s + 1) * (p + 1) = Kcj * ((s + 1) * (p + 1)) := Nat.mul_assoc Kcj (s + 1) (p + 1)
      _ ≤ KB * SB := Nat.mul_le_mul hK hs
  have h2 : Kcj ≤ KB := hK
  nlinarith [h1, h2]

/-- A product `K * f` with `f` bounded by an explicit small number. -/
theorem tiny_cost_le {K KB SB Pm f0 : ℕ} (hK : K ≤ KB) (hf0 : f0 ≤ SB + 1 + Pm) :
    K * f0 ≤ ALLOW KB SB Pm := by
  rw [ALLOW]
  calc K * f0 ≤ KB * (SB + 1 + Pm) := Nat.mul_le_mul hK hf0
    _ ≤ 1000000 * (KB + 1) * (SB + 1 + Pm) := by nlinarith

/-! ## Step words on a window above a tail -/

/-- A `roll` on the window `L` above an arbitrary tail. -/
theorem rollStepT (hK : KernelLib) {main : Cmd} {rollP : ℕ → Cmd} {Kr : ℕ}
    (hroll : ∀ (main : Cmd) (k : ℕ), WordR main (rollP k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs.eraseIdx k)
      (fun vs => Kr * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    (k : ℕ) (L L' rest : List Val) (C : ℕ) (hk : k < L.length)
    (hL' : L.getD k .nil :: L.eraseIdx k = L')
    (hC : Kr * (k + 1) * (((L.take (k + 1)).map vsz).sum + 1) ≤ C) :
    Work.ConvR.WordC main (rollP k) (fun vs => vs = L ++ rest) (fun _ out => out = L' ++ rest) C := by
  refine Work.ConvR.WordC.rollStep hK (main := main) (rollP := rollP) (KR := Kr) hroll
    (L := L ++ rest) (L' := L' ++ rest) (k := k) (C := C) ?_ ?_ ?_
  · show k < (L ++ rest).length
    rw [List.length_append]; exact lt_of_lt_of_le hk (Nat.le_add_right _ _)
  · show (L ++ rest).getD k .nil :: (L ++ rest).eraseIdx k = L' ++ rest
    rw [Work.ConvR.getD_append_lt hk, Work.ConvR.eraseIdx_append_lt hk, ← List.cons_append, hL']
  · show Kr * (k + 1) * ((((L ++ rest).take (k + 1)).map vsz).sum + 1) ≤ C
    rw [List.take_append_of_le_length (Nat.succ_le_of_lt hk)]
    exact hC

/-- A `permTop` on the window `head` above an arbitrary tail, with the image list `head'` given
explicitly. -/
theorem permStepT {main : Cmd} {permP : List ℕ → Cmd} {KP : ℕ}
    (hperm : ∀ (main : Cmd) (n : ℕ) (σ : List ℕ) (head tail : List Val),
      head.length = n → σ.length = n → σ.Perm (List.range n) →
      WordR main (permP σ) (fun vs => vs = head ++ tail)
        (fun _ out => out = σ.map (fun i => head.getD i .nil) ++ tail)
        (fun _ => KP * (n + 1) * (n + 1) * (((head.map vsz).sum) + 1)))
    (n : ℕ) (σ : List ℕ) (head head' tail : List Val) (C : ℕ)
    (h1 : head.length = n) (h2 : σ.length = n) (h3 : σ.Perm (List.range n))
    (h4 : σ.map (fun i => head.getD i .nil) = head')
    (hC : KP * (n + 1) * (n + 1) * (((head.map vsz).sum) + 1) ≤ C) :
    Work.ConvR.WordC main (permP σ) (fun vs => vs = head ++ tail)
      (fun _ out => out = head' ++ tail) C := by
  intro vs hvs s R hR
  obtain ⟨out, s', n', hq, he, hn, hstk, hoth⟩ := hperm main n σ head tail h1 h2 h3 vs hvs s R hR
  exact ⟨out, s', n', by rw [hq, h4], he, le_trans hn hC, hstk, hoth⟩

/-- A `dup` of the head above an arbitrary tail. -/
theorem dupStepT {main : Cmd} {dupP : Cmd} {Kd : ℕ}
    (hdup : ∀ main : Cmd, WordR main dupP (fun vs => vs ≠ [])
      (fun vs out => ∃ v rest, vs = v :: rest ∧ out = v :: v :: rest)
      (fun vs => Kd * (vsz (vs.headD .nil) + 1)))
    (v : Val) (rest : List Val) (C : ℕ) (hC : Kd * (vsz v + 1) ≤ C) :
    Work.ConvR.WordC main dupP (fun vs => vs = v :: rest) (fun _ out => out = v :: v :: rest) C := by
  intro vs hvs s R hR
  obtain ⟨out, s', n, hq, he, hn, hstk, hoth⟩ := hdup main vs (by rw [hvs]; simp) s R hR
  refine ⟨out, s', n, ?_, he, ?_, ?_, hoth⟩
  · obtain ⟨v', rest', hv', hout⟩ := hq
    rw [hvs] at hv'
    simp only [List.cons.injEq] at hv'
    obtain ⟨rfl, rfl⟩ := hv'
    exact hout
  · have hβ : n ≤ Kd * (vsz (vs.headD .nil) + 1) := hn
    have hhead : vs.headD .nil = v := by rw [hvs]; rfl
    rw [hhead] at hβ
    exact le_trans hβ hC
  · exact hstk

/-- A `pushVal` of a constant above an arbitrary tail. -/
theorem pushStepT {main : Cmd} {pushP : Val → Cmd} {Kp : ℕ}
    (hpv : ∀ (main : Cmd) (v : Val), WordR main (pushP v) (fun _ => True)
      (fun vs out => out = v :: vs) (fun _ => Kp * (vsz v + 1)))
    (v : Val) (rest : List Val) (C : ℕ) (hC : Kp * (vsz v + 1) ≤ C) :
    Work.ConvR.WordC main (pushP v) (fun vs => vs = rest) (fun _ out => out = v :: rest) C := by
  intro vs hvs s R hR
  obtain ⟨out, s', n, hq, he, hn, hstk, hoth⟩ := hpv main v vs trivial s R hR
  exact ⟨out, s', n, by rw [hq, hvs], he, le_trans hn hC, hstk, hoth⟩

/-- A `mulS` on the two head integers above an arbitrary tail. -/
theorem mulStepT {main : Cmd} {mulP : Cmd} {Km : ℕ}
    (hmul : ∀ main : Cmd, BinOp main mulP (fun _ _ => True) (· * ·) (fun a b => Km * isz a * isz b))
    (a b : ℤ) (rest : List Val) (C : ℕ) (hC : Km * isz a * isz b ≤ C) :
    Work.ConvR.WordC main mulP (fun vs => vs = .int a :: .int b :: rest)
      (fun _ out => out = .int (a * b) :: rest) C := by
  intro vs hvs s R hR
  obtain ⟨out, s', n, hq, he, hn, hstk, hoth⟩ :=
    hmul main vs (by rw [hvs]; exact ⟨a, b, rest, rfl, trivial⟩) s R hR
  refine ⟨out, s', n, ?_, he, ?_, ?_, hoth⟩
  · obtain ⟨a', b', rest', hv', hout⟩ := hq
    rw [hvs] at hv'
    have h1 : a = a' ∧ b = b' ∧ rest = rest' := by
      simpa [List.cons.injEq, Val.int.injEq] using hv'
    obtain ⟨rfl, rfl, rfl⟩ := h1
    exact hout
  · have hβ : n ≤ Km * isz a * isz b := by
      rw [hvs] at hn
      exact hn
    exact le_trans hβ hC
  · exact hstk

/-- A `pow2` on the head integer above an arbitrary tail. -/
theorem powStepT {main : Cmd} {powP : Cmd} {Kw : ℕ}
    (hpow : ∀ main : Cmd, UnOp main powP (fun k => 0 ≤ k) (fun k => 2 ^ k.toNat)
      (fun k => Kw * (k.toNat + isz k)))
    (k : ℤ) (rest : List Val) (C : ℕ) (hk : 0 ≤ k) (hC : Kw * (k.toNat + isz k) ≤ C) :
    Work.ConvR.WordC main powP (fun vs => vs = .int k :: rest)
      (fun _ out => out = .int (2 ^ k.toNat) :: rest) C := by
  intro vs hvs s R hR
  obtain ⟨out, s', n, hq, he, hn, hstk, hoth⟩ :=
    hpow main vs (by rw [hvs]; exact ⟨k, rest, rfl, hk⟩) s R hR
  refine ⟨out, s', n, ?_, he, ?_, ?_, hoth⟩
  · obtain ⟨a', rest', hv', hout⟩ := hq
    rw [hvs] at hv'
    have h1 : k = a' ∧ rest = rest' := by
      simpa [List.cons.injEq, Val.int.injEq] using hv'
    obtain ⟨rfl, rfl⟩ := h1
    exact hout
  · have hβ : n ≤ Kw * (k.toNat + isz k) := by
      rw [hvs] at hn
      exact hn
    exact le_trans hβ hC
  · exact hstk

/-- Sequential composition for two `WordC`s with a one-argument intermediate predicate. -/
theorem seqC (hK : KernelLib) {main p q : Cmd} {P Qi R : List Val → Prop} {c1 c2 : ℕ}
    (h1 : Work.ConvR.WordC main p P (fun _ out => Qi out) c1)
    (h2 : Work.ConvR.WordC main q Qi (fun _ out => R out) c2) :
    Work.ConvR.WordC main (.seq p q) P (fun _ out => R out) (c1 + c2) := by
  refine hK.conseq (main := main) (p := .seq p q)
    (P := P) (Q := fun _ out => ∃ mid, Qi mid ∧ R out) (C := fun _ => c1 + c2)
    (P' := P) (Q' := fun _ out => R out) (C' := fun _ => c1 + c2)
    (hK.seq main p q P (fun _ out => Qi out) (fun _ => c1) Qi (fun _ out => R out)
      (fun _ => c2) (fun _ => c2) h1 h2 (fun vs mid _ hq => ⟨hq, le_rfl⟩))
    (fun vs h => h) (fun vs out _ hq => by obtain ⟨mid, hQi, hR⟩ := hq; exact hR)
    (fun vs _ => le_rfl)


/-! ## The concrete size bounds of the §5.2 pipeline -/

/-- The uniform encoding-size bound `SB` of the cost accounting: `8` times the sum of the six
encoding sizes met by the pipeline. -/
def SB0 (p α : ℕ) (ss ts : List ℕ) : ℕ :=
  8 * (Work.ConvR.cvecSz p ss.prod + vsz (intList ss) + vsz (intList ts) + isz (p : ℤ) +
    isz (α : ℤ) + isz (2 ^ (2 * D * α ^ 2) : ℤ) + 1)

/-- The numerical-size bound `Pm` of the cost accounting. -/
def Pm0 (p : ℕ) : ℕ := (p + 16) * (p + 16)

end Work.MainP

