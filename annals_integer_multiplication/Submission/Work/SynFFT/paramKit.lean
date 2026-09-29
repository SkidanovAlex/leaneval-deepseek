import Mathlib
import Submission.Work.SynFFT.kit2
import Submission.Work.SynFFT.mrgBlkDefs

/-! # `Work.SynFFT.paramKit` — plumbing for the twiddle-parameter word -/

set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace Work.SynFFT

open HvdH

theorem subStep {main : Cmd} {subP : Cmd} {Ks : ℕ}
    (h : BinOp main subP (fun _ _ => True) (· - ·) (fun a b => Ks * (isz a + isz b)))
    (a b : ℤ) (t : List Val) (D : ℕ) (hD : Ks * (isz a + isz b) ≤ D) :
    WordR main subP (fun vs => vs = .int a :: .int b :: t) (fun _ out => out = .int (a - b) :: t)
      (fun _ => D) := by
  unfold BinOp at h
  refine MrgKit.WordR_conseqC h ⟨a, b, t, rfl, trivial⟩ ?_ hD
  intro out hout
  obtain ⟨a', b', t', h1, hout'⟩ := hout
  simp only [List.cons.injEq, Val.int.injEq] at h1
  obtain ⟨rfl, rfl, rfl⟩ := h1
  exact hout'

theorem shlStep {main : Cmd} {shlP : Cmd} {Ks : ℕ}
    (h : BinOp main shlP (fun _ k => 0 ≤ k) (fun a k => a * 2 ^ k.toNat)
      (fun a k => Ks * (isz a + k.toNat + isz k)))
    (a k : ℤ) (hk : 0 ≤ k) (t : List Val) (D : ℕ) (hD : Ks * (isz a + k.toNat + isz k) ≤ D) :
    WordR main shlP (fun vs => vs = .int a :: .int k :: t)
      (fun _ out => out = .int (a * 2 ^ k.toNat) :: t) (fun _ => D) := by
  unfold BinOp at h
  refine MrgKit.WordR_conseqC h ⟨a, k, t, rfl, hk⟩ ?_ hD
  intro out hout
  obtain ⟨a', k', t', h1, hout'⟩ := hout
  simp only [List.cons.injEq, Val.int.injEq] at h1
  obtain ⟨rfl, rfl, rfl⟩ := h1
  exact hout'

theorem ltStep {main : Cmd} {ltP : Cmd} {Ks : ℕ}
    (h : BinOp main ltP (fun _ _ => True) (fun a b => if a < b then 1 else 0)
      (fun a b => Ks * (isz a + isz b)))
    (a b : ℤ) (t : List Val) (D : ℕ) (hD : Ks * (isz a + isz b) ≤ D) :
    WordR main ltP (fun vs => vs = .int a :: .int b :: t)
      (fun _ out => out = .int (if a < b then 1 else 0) :: t) (fun _ => D) := by
  unfold BinOp at h
  refine MrgKit.WordR_conseqC h ⟨a, b, t, rfl, trivial⟩ ?_ hD
  intro out hout
  obtain ⟨a', b', t', h1, hout'⟩ := hout
  simp only [List.cons.injEq, Val.int.injEq] at h1
  obtain ⟨rfl, rfl, rfl⟩ := h1
  exact hout'

/-! ## cost helpers -/

theorem WordR_costNorm {main p : Cmd} {A : List Val} {Bpost : List Val → Prop}
    {c1 c2 : ℕ}
    (h : WordR main p (fun vs => vs = A) (fun _ out => Bpost out) (fun _ => c1))
    (hle : c1 ≤ c2) :
    WordR main p (fun vs => vs = A) (fun _ out => Bpost out) (fun _ => c2) := by
  intro vs hvs s R hR
  obtain ⟨out, s', n, hpost, hev, hn, hstk, hoth⟩ := h vs hvs s R hR
  exact ⟨out, s', n, hpost, hev, le_trans hn hle, hstk, hoth⟩

theorem stepBudget {Kx MB Cs a : ℕ} (ha : a ≤ 1000 * (3 * (MB + 1)))
    (hCs : Cs = Kx * (MB + 1) * 10000000) : Kx * a ≤ Cs := by
  rw [hCs]
  calc Kx * a ≤ Kx * (1000 * (3 * (MB + 1))) := Nat.mul_le_mul_left _ ha
    _ = 3000 * Kx * (MB + 1) := by ring
    _ ≤ Kx * (MB + 1) * 10000000 := by nlinarith [Nat.zero_le Kx, Nat.zero_le MB]

theorem pickrollCost {Kx Kp MB Cs : ℕ} {A : List Val} {k : ℕ} (hk : k ≤ 12)
    (hsmall : ∀ i, i < k + 1 → vsz (A.getD i Val.nil) ≤ 3 * (MB + 1)) (hK : Kp ≤ Kx)
    (hCs : Cs = Kx * (MB + 1) * 10000000) :
    Kp * (k + 1) * (((A.take (k + 1)).map vsz).sum + 1) ≤ Cs := by
  have h1 : ((A.take (k + 1)).map vsz).sum ≤ (k + 1) * (3 * (MB + 1)) :=
    MrgKit.vsz_take_sum_le_getD A (k + 1) (3 * (MB + 1)) hsmall
  have hk13 : k + 1 ≤ 13 := by omega
  have hsum : ((A.take (k + 1)).map vsz).sum + 1 ≤ 13 * (3 * (MB + 1)) + 1 := by
    have h5 : (k + 1) * (3 * (MB + 1)) ≤ 13 * (3 * (MB + 1)) := Nat.mul_le_mul_right _ hk13
    omega
  have h2 : Kp * (k + 1) * (((A.take (k + 1)).map vsz).sum + 1)
      ≤ (Kx * 13) * (13 * (3 * (MB + 1)) + 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul hK hk13) hsum
  have h3 : (Kx * 13) * (13 * (3 * (MB + 1)) + 1)
      ≤ Kx * (13 * (13 * (3 * (MB + 1)) + 1)) := le_of_eq (by ring)
  have h4 : Kx * (13 * (13 * (3 * (MB + 1)) + 1)) ≤ Cs :=
    stepBudget (Kx := Kx) (MB := MB) (Cs := Cs)
      (a := 13 * (13 * (3 * (MB + 1)) + 1)) (by nlinarith) hCs
  linarith

theorem binCost' {Kx Kb MB Cs a : ℕ} (hK : Kb ≤ Kx) (ha : a ≤ 30 * (3 * (MB + 1)))
    (hCs : Cs = Kx * (MB + 1) * 10000000) : Kb * a ≤ Cs :=
  le_trans (Nat.mul_le_mul hK ha)
    (stepBudget (Kx := Kx) (MB := MB) (Cs := Cs) (a := 30 * (3 * (MB + 1)))
      (by nlinarith) hCs)

theorem mulCost' {Kx Kb MB Cs a b : ℕ} (hK : Kb ≤ Kx) (ha : a ≤ 4) (hb : b ≤ 3 * (MB + 1))
    (hCs : Cs = Kx * (MB + 1) * 10000000) : Kb * a * b ≤ Cs := by
  rw [Nat.mul_assoc]
  refine le_trans (Nat.mul_le_mul hK (Nat.mul_le_mul ha hb))
    (stepBudget (Kx := Kx) (MB := MB) (Cs := Cs) (a := 4 * (3 * (MB + 1)))
      (by nlinarith) hCs)

theorem pushCost' {Kx Kb MB Cs : ℕ} {v : Val} (hK : Kb ≤ Kx) (hv : vsz v ≤ 3 * (MB + 1))
    (hCs : Cs = Kx * (MB + 1) * 10000000) : Kb * (vsz v + 1) ≤ Cs :=
  le_trans (Nat.mul_le_mul hK (by omega : vsz v + 1 ≤ 4 * (3 * (MB + 1))))
    (stepBudget (Kx := Kx) (MB := MB) (Cs := Cs) (a := 4 * (3 * (MB + 1)))
      (by nlinarith) hCs)

/-! ## size arithmetic -/

theorem isz_le_size (y : ℤ) (n : ℕ) (h : y.natAbs ≤ n) : isz y ≤ n.size + 2 := by
  simp only [isz]
  exact Nat.add_le_add_right (Nat.size_le_size h) 2

theorem isz_le_two_mul (r : ℕ) (y : ℤ) (h : y.natAbs ≤ 2 * r) : isz y ≤ r.size + 3 := by
  have h1 : y.natAbs.size ≤ (2 * r).size := Nat.size_le_size h
  have h2 : (2 * r).size ≤ r.size + 1 := by
    rw [Nat.size_le, pow_succ]
    nlinarith [Nat.lt_size_self r]
  simp only [isz]
  omega

/-! ## The parameter word -/


end Work.SynFFT
