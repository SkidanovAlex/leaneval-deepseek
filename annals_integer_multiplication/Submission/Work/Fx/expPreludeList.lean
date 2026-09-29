import Mathlib
import Submission.Work.Fx.ExpDefs
import Submission.Work.Layout.replicateWord

/-!
# `Work.Fx.expPreludeList`

`int k :: nil :: rest ↦ ofList (replicate k (int 1)) :: rest` (with the frame `rest` untouched).

Route: `swap` brings the `nil` to the top, `drop` removes it, `pushVal (int 1)` inserts a `1`,
a second `swap` restores the order `int k :: int 1 :: rest`, and `Work.Layout.replicateWord`
(`LayoutLib.replicate`, proved in the Layout area) replaces the two values by the list of `k`
ones.  The cost constant is `O((k+1)^K)`; all we need about `k` is `isz k ≤ k + 2`.
-/

set_option autoImplicit false

namespace Work.Fx

open HvdH

/-! ## `isz` of a natural number -/

theorem isz_natCast_le_x1 (k : ℕ) : isz (k : ℤ) ≤ k + 2 := by
  have h : ((k : ℤ).natAbs) = k := Int.natAbs_natCast k
  simp only [isz, h]
  have h2 : k.size ≤ k := Nat.size_le.mpr (Nat.lt_two_pow_self (n := k))
  omega

theorem isz_one_eq : isz (1 : ℤ) = 3 := by decide

/-! ## A chain rule for deterministic windows -/

theorem wrdSeqDet (hk : KernelLib) {main p q : Cmd} {A B D : List Val} {c1 c2 : ℕ}
    (h1 : WordR main p (fun vs => vs = A) (fun _ out => out = B) (fun _ => c1))
    (h2 : WordR main q (fun vs => vs = B) (fun _ out => out = D) (fun _ => c2)) :
    WordR main (.seq p q) (fun vs => vs = A) (fun _ out => out = D) (fun _ => c1 + c2) := by
  refine hk.conseq (main := main) (p := .seq p q)
    (P := fun vs => vs = A) (P' := fun vs => vs = A)
    (Q := fun _ out => ∃ mid, mid = B ∧ out = D) (Q' := fun _ out => out = D)
    (C := fun _ => c1 + c2) (C' := fun _ => c1 + c2)
    (hk.seq (main := main) (p := p) (q := q)
      (P := fun vs => vs = A) (Q := fun _ out => out = B) (C := fun _ => c1)
      (P' := fun vs => vs = B) (Q' := fun _ out => out = D) (C' := fun _ => c2)
      (B := fun _ => c2) h1 h2 (fun vs mid hv hm => ⟨hm, le_rfl⟩))
    (fun vs hv => hv) (fun vs out hv hq => by rcases hq with ⟨mid, hm, hd⟩; exact hd) (fun vs hv => le_rfl)

/-! ## The five stages -/

/-- `int k :: nil :: rest ↦ nil :: int k :: rest` (a swap). -/
theorem stageSwap1 (hk : KernelLib) {main sP : Cmd} {Ks k : ℕ} {R : List Val}
    (hs : WordR main sP (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = b :: a :: rest)
      (fun vs => Ks * (vsz (vs.getD 0 .nil) + vsz (vs.getD 1 .nil) + 1))) :
    WordR main sP
      (fun vs => vs = [Val.int (k : ℤ), Val.nil] ++ R)
      (fun _ out => out = [Val.nil, Val.int (k : ℤ)] ++ R)
      (fun _ => Ks * (isz (k : ℤ) + 8)) := by
  refine hk.conseq (main := main) (p := sP)
    (P := fun vs => 2 ≤ vs.length)
    (P' := fun vs => vs = [Val.int (k : ℤ), Val.nil] ++ R)
    (Q := fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = b :: a :: rest)
    (Q' := fun _ out => out = [Val.nil, Val.int (k : ℤ)] ++ R)
    (C := fun vs => Ks * (vsz (vs.getD 0 .nil) + vsz (vs.getD 1 .nil) + 1))
    (C' := fun _ => Ks * (isz (k : ℤ) + 8)) hs ?_ ?_ ?_
  · intro vs hv
    rw [hv]
    simp
  · intro vs out hv hQ
    rcases hQ with ⟨a, b, rest, hvs, hout⟩
    rw [hv] at hvs
    simp only [List.cons_append, List.nil_append] at hvs
    obtain ⟨ha, hb, hrest⟩ : a = Val.int (k : ℤ) ∧ b = Val.nil ∧ rest = R := by
      have h1 := List.cons.inj hvs
      have h2 := List.cons.inj h1.2
      exact ⟨h1.1.symm, h2.1.symm, h2.2.symm⟩
    rw [hout, ha, hb, hrest]
    simp only [List.cons_append, List.nil_append]
  · intro vs hv
    rw [hv]
    simp only [List.cons_append, List.nil_append, List.getD_cons_zero, List.getD_cons_succ]
    rw [vsz_int, vsz_nil]
    exact Nat.mul_le_mul_left Ks (by omega)

/-- `nil :: int k :: rest ↦ int k :: rest` (drop the `nil`). -/
theorem stageDrop (hk : KernelLib) {main dP : Cmd} {Kd k : ℕ} {R : List Val}
    (hd : WordR main dP (fun vs => vs ≠ [])
      (fun vs out => ∃ v rest, vs = v :: rest ∧ out = rest)
      (fun vs => Kd * (vsz (vs.headD .nil) + 1))) :
    WordR main dP
      (fun vs => vs = [Val.nil, Val.int (k : ℤ)] ++ R)
      (fun _ out => out = [Val.int (k : ℤ)] ++ R)
      (fun _ => Kd * (isz (k : ℤ) + 8)) := by
  refine hk.conseq (main := main) (p := dP)
    (P := fun vs => vs ≠ [])
    (P' := fun vs => vs = [Val.nil, Val.int (k : ℤ)] ++ R)
    (Q := fun vs out => ∃ v rest, vs = v :: rest ∧ out = rest)
    (Q' := fun _ out => out = [Val.int (k : ℤ)] ++ R)
    (C := fun vs => Kd * (vsz (vs.headD .nil) + 1))
    (C' := fun _ => Kd * (isz (k : ℤ) + 8)) hd ?_ ?_ ?_
  · intro vs hv
    rw [hv]
    simp
  · intro vs out hv hQ
    rcases hQ with ⟨v, rest, hvs, hout⟩
    rw [hv] at hvs
    simp only [List.cons_append, List.nil_append] at hvs
    have h1 := List.cons.inj hvs
    rw [hout, ← h1.2]
    simp only [List.cons_append, List.nil_append]
  · intro vs hv
    rw [hv]
    simp only [List.cons_append, List.nil_append, List.headD_cons]
    rw [vsz_nil]
    exact Nat.mul_le_mul_left Kd (by omega)

/-- `int k :: rest ↦ int 1 :: int k :: rest`. -/
theorem stagePushOne (hk : KernelLib) {main pP : Cmd} {Kp k : ℕ} {R : List Val}
    (hp : WordR main pP (fun _ => True)
      (fun vs out => out = Val.int (1 : ℤ) :: vs)
      (fun _ => Kp * (vsz (Val.int (1 : ℤ)) + 1))) :
    WordR main pP
      (fun vs => vs = [Val.int (k : ℤ)] ++ R)
      (fun _ out => out = [Val.int (1 : ℤ), Val.int (k : ℤ)] ++ R)
      (fun _ => Kp * (isz (k : ℤ) + 8)) := by
  refine hk.conseq (main := main) (p := pP)
    (P := fun _ => True)
    (P' := fun vs => vs = [Val.int (k : ℤ)] ++ R)
    (Q := fun vs out => out = Val.int (1 : ℤ) :: vs)
    (Q' := fun _ out => out = [Val.int (1 : ℤ), Val.int (k : ℤ)] ++ R)
    (C := fun _ => Kp * (vsz (Val.int (1 : ℤ)) + 1))
    (C' := fun _ => Kp * (isz (k : ℤ) + 8)) hp ?_ ?_ ?_
  · intro vs hv
    trivial
  · intro vs out hv hQ
    rw [hQ, hv]
    simp only [List.cons_append, List.nil_append]
  · intro vs hv
    rw [vsz_int, isz_one_eq]
    exact Nat.mul_le_mul_left Kp (by omega)

/-- `int 1 :: int k :: rest ↦ int k :: int 1 :: rest` (a swap). -/
theorem stageSwap2 (hk : KernelLib) {main sP : Cmd} {Ks k : ℕ} {R : List Val}
    (hs : WordR main sP (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = b :: a :: rest)
      (fun vs => Ks * (vsz (vs.getD 0 .nil) + vsz (vs.getD 1 .nil) + 1))) :
    WordR main sP
      (fun vs => vs = [Val.int (1 : ℤ), Val.int (k : ℤ)] ++ R)
      (fun _ out => out = [Val.int (k : ℤ), Val.int (1 : ℤ)] ++ R)
      (fun _ => Ks * (isz (k : ℤ) + 8)) := by
  refine hk.conseq (main := main) (p := sP)
    (P := fun vs => 2 ≤ vs.length)
    (P' := fun vs => vs = [Val.int (1 : ℤ), Val.int (k : ℤ)] ++ R)
    (Q := fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = b :: a :: rest)
    (Q' := fun _ out => out = [Val.int (k : ℤ), Val.int (1 : ℤ)] ++ R)
    (C := fun vs => Ks * (vsz (vs.getD 0 .nil) + vsz (vs.getD 1 .nil) + 1))
    (C' := fun _ => Ks * (isz (k : ℤ) + 8)) hs ?_ ?_ ?_
  · intro vs hv
    rw [hv]
    simp
  · intro vs out hv hQ
    rcases hQ with ⟨a, b, rest, hvs, hout⟩
    rw [hv] at hvs
    simp only [List.cons_append, List.nil_append] at hvs
    obtain ⟨ha, hb, hrest⟩ : a = Val.int (1 : ℤ) ∧ b = Val.int (k : ℤ) ∧ rest = R := by
      have h1 := List.cons.inj hvs
      have h2 := List.cons.inj h1.2
      exact ⟨h1.1.symm, h2.1.symm, h2.2.symm⟩
    rw [hout, ha, hb, hrest]
    simp only [List.cons_append, List.nil_append]
  · intro vs hv
    rw [hv]
    simp only [List.cons_append, List.nil_append, List.getD_cons_zero, List.getD_cons_succ]
    rw [vsz_int, vsz_int, isz_one_eq]
    exact Nat.mul_le_mul_left Ks (by omega)

/-- `int k :: int 1 :: rest ↦ ofList (replicate k (int 1)) :: rest`. -/
theorem stageReplicate (hk : KernelLib) {main rP : Cmd} {Kr k : ℕ} {R : List Val}
    (hr : WordR main rP
      (fun vs => ∃ rest, vs = Val.int (k : ℤ) :: Val.int (1 : ℤ) :: rest)
      (fun vs out => ∃ rest, vs = Val.int (k : ℤ) :: Val.int (1 : ℤ) :: rest ∧
        out = ofList (List.replicate k (Val.int (1 : ℤ))) :: rest)
      (fun _ => Kr * ((k + 1) * (vsz (Val.int (1 : ℤ)) + 1) + isz (k : ℤ) + 1))) :
    WordR main rP
      (fun vs => vs = [Val.int (k : ℤ), Val.int (1 : ℤ)] ++ R)
      (fun _ out => out = [ofList (List.replicate k (Val.int (1 : ℤ)))] ++ R)
      (fun _ => Kr * (8 * (k + 1) + isz (k : ℤ) + 8)) := by
  refine hk.conseq (main := main) (p := rP)
    (P := fun vs => ∃ rest, vs = Val.int (k : ℤ) :: Val.int (1 : ℤ) :: rest)
    (P' := fun vs => vs = [Val.int (k : ℤ), Val.int (1 : ℤ)] ++ R)
    (Q := fun vs out => ∃ rest, vs = Val.int (k : ℤ) :: Val.int (1 : ℤ) :: rest ∧
      out = ofList (List.replicate k (Val.int (1 : ℤ))) :: rest)
    (Q' := fun _ out => out = [ofList (List.replicate k (Val.int (1 : ℤ)))] ++ R)
    (C := fun _ => Kr * ((k + 1) * (vsz (Val.int (1 : ℤ)) + 1) + isz (k : ℤ) + 1))
    (C' := fun _ => Kr * (8 * (k + 1) + isz (k : ℤ) + 8)) hr ?_ ?_ ?_
  · intro vs hv
    refine ⟨R, ?_⟩
    rw [hv]
    simp only [List.cons_append, List.nil_append]
  · intro vs out hv hQ
    rcases hQ with ⟨rest, hvs, hout⟩
    rw [hv] at hvs
    simp only [List.cons_append, List.nil_append] at hvs
    have h1 := List.cons.inj hvs
    have h2 := List.cons.inj h1.2
    rw [hout, ← h2.2]
    simp only [List.cons_append, List.nil_append]
  · intro vs hv
    rw [vsz_int, isz_one_eq]
    exact Nat.mul_le_mul_left Kr (by omega)

theorem expPreludeList (hk : HvdH.KernelLib) (hi : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (k : ℕ) (R : List HvdH.Val),
      HvdH.WordR main prog
        (fun vs => vs = [HvdH.Val.int (k : ℤ), HvdH.Val.nil] ++ R)
        (fun _ out => out = [HvdH.ofList (List.replicate k (HvdH.Val.int 1))] ++ R)
        (fun _ => K * (k + 1) ^ K) := by
  obtain ⟨sP, Ks, hs⟩ := hk.swap
  obtain ⟨dP, Kd, hd⟩ := hk.drop
  obtain ⟨pvP, Kp, hpv⟩ := hk.pushVal
  obtain ⟨rP, Kr, hr⟩ := Work.Layout.replicateWord hi
  refine ⟨Cmd.seq sP (Cmd.seq dP (Cmd.seq (pvP (Val.int (1 : ℤ))) (Cmd.seq sP rP))),
    10 * (2 * Ks + Kd + Kp) + 18 * Kr + 2, ?_⟩
  intro main k R
  have h1 := stageSwap1 hk (hs main) (k := k) (R := R)
  have h2 := stageDrop hk (hd main) (k := k) (R := R)
  have h3 := stagePushOne hk (hpv main (Val.int (1 : ℤ))) (k := k) (R := R)
  have h4 := stageSwap2 hk (hs main) (k := k) (R := R)
  have h5 := stageReplicate hk (hr main k (Val.int (1 : ℤ))) (R := R)
  have h45 := wrdSeqDet hk h4 h5
  have h345 := wrdSeqDet hk h3 h45
  have h2345 := wrdSeqDet hk h2 h345
  have h := wrdSeqDet hk h1 h2345
  refine hk.conseq (main := main)
    (p := Cmd.seq sP (Cmd.seq dP (Cmd.seq (pvP (Val.int (1 : ℤ))) (Cmd.seq sP rP))))
    (P := fun vs => vs = [Val.int (k : ℤ), Val.nil] ++ R)
    (P' := fun vs => vs = [Val.int (k : ℤ), Val.nil] ++ R)
    (Q := fun _ out => out = [ofList (List.replicate k (Val.int (1 : ℤ)))] ++ R)
    (Q' := fun _ out => out = [ofList (List.replicate k (Val.int (1 : ℤ)))] ++ R)
    (C := fun _ => Ks * (isz (k : ℤ) + 8) +
      (Kd * (isz (k : ℤ) + 8) + (Kp * (isz (k : ℤ) + 8) +
        (Ks * (isz (k : ℤ) + 8) + Kr * (8 * (k + 1) + isz (k : ℤ) + 8)))))
    (C' := fun _ => (10 * (2 * Ks + Kd + Kp) + 18 * Kr + 2) * (k + 1) ^ (10 * (2 * Ks + Kd + Kp) + 18 * Kr + 2))
    h (fun vs hv => hv) (fun vs out hv hq => hq) ?_
  · intro vs hv
    have hisz : isz (k : ℤ) ≤ k + 2 := isz_natCast_le_x1 k
    have hpow : k + 1 ≤ (k + 1) ^ (10 * (2 * Ks + Kd + Kp) + 18 * Kr + 2) :=
      calc k + 1 = (k + 1) ^ 1 := (pow_one _).symm
        _ ≤ (k + 1) ^ (10 * (2 * Ks + Kd + Kp) + 18 * Kr + 2) :=
            Nat.pow_le_pow_right (by omega) (by omega)
    have hmul : 10 * (2 * Ks + Kd + Kp) + 18 * Kr ≤ 10 * (2 * Ks + Kd + Kp) + 18 * Kr + 2 := by omega
    have hstep1 : Ks * (isz (k : ℤ) + 8) +
        (Kd * (isz (k : ℤ) + 8) + (Kp * (isz (k : ℤ) + 8) +
          (Ks * (isz (k : ℤ) + 8) + Kr * (8 * (k + 1) + isz (k : ℤ) + 8))))
        ≤ (10 * (2 * Ks + Kd + Kp) + 18 * Kr) * (k + 1) := by
      nlinarith [hisz]
    calc Ks * (isz (k : ℤ) + 8) +
        (Kd * (isz (k : ℤ) + 8) + (Kp * (isz (k : ℤ) + 8) +
          (Ks * (isz (k : ℤ) + 8) + Kr * (8 * (k + 1) + isz (k : ℤ) + 8))))
        ≤ (10 * (2 * Ks + Kd + Kp) + 18 * Kr) * (k + 1) := hstep1
      _ ≤ (10 * (2 * Ks + Kd + Kp) + 18 * Kr + 2) * (k + 1) :=
          Nat.mul_le_mul_right _ (by omega)
      _ ≤ (10 * (2 * Ks + Kd + Kp) + 18 * Kr + 2) *
            (k + 1) ^ (10 * (2 * Ks + Kd + Kp) + 18 * Kr + 2) :=
          Nat.mul_le_mul_left _ hpow

end Work.Fx
