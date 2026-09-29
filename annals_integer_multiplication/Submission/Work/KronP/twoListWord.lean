import Mathlib
import Submission.Work.KronP.defs
import Submission.Work.KronP.twoListCost

/-!
# `Work.KronP.twoListWord`

The word that replaces the top two values `a`, `b` of the value stack by the list value
`ofList [a, b] = cons a (cons b nil)`.

The program is `push nil ;;; roll 2 ;;; consV ;;; swap ;;; consV`:

* `push nil`    : `[a, b | tl]`          → `[nil, a, b | tl]`
* `roll 2`      : `[nil, a, b | tl]`     → `[b, nil, a | tl]`
* `consV`       : `[b, nil, a | tl]`     → `[cons b nil, a | tl]`
* `swap`        : `[cons b nil, a | tl]` → `[a, cons b nil | tl]`
* `consV`       : `[a, cons b nil | tl]` → `[cons a (cons b nil) | tl]`

The last line is exactly `[ofList [a, b] | tl]`.  The cost is
`K * (vsz a + vsz b + 3)` with `K = 2*Kp + 3*Kr + Ks + 2*Kc`, where `Kp`, `Kr`, `Kc`, `Ks` are the
constants of `KernelLib.pushVal`, `KernelLib.roll`, `KernelLib.consV`, `KernelLib.swap`.
-/

namespace Work.KronP

open HvdH

local infixr:68 " ;;; " => HvdH.Cmd.seq

private theorem vsz_nil_val : vsz (Val.nil) = 1 := rfl

theorem twoListWord (hK : HvdH.KernelLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ),
      ∀ (main : HvdH.Cmd) (a b : HvdH.Val) (tl : List HvdH.Val),
        HvdH.WordR main prog
          (fun vs => vs = a :: b :: tl)
          (fun _ out => out = HvdH.ofList [a, b] :: tl)
          (fun _ => K * (HvdH.vsz a + HvdH.vsz b + 3)) := by
  obtain ⟨pushP, Kp, hpush⟩ := hK.pushVal
  obtain ⟨rollP, Kr, hroll⟩ := hK.roll
  obtain ⟨consP, Kc, hcons⟩ := hK.consV
  obtain ⟨swapP, Ks, hswap⟩ := hK.swap
  refine ⟨pushP Val.nil ;;; rollP 2 ;;; consP ;;; swapP ;;; consP,
    2 * Kp + 3 * Kr + Ks + 2 * Kc, ?_⟩
  intro main a b tl
  -- stage 1 : push `nil` on top
  have s1 : HvdH.WordR main (pushP Val.nil) (fun vs => vs = a :: b :: tl)
      (fun _ out => out = Val.nil :: a :: b :: tl) (fun _ => Kp * 2) := by
    refine hK.conseq main (pushP Val.nil) (fun _ => True) (fun vs => vs = a :: b :: tl)
      (fun vs out => out = Val.nil :: vs) (fun _ out => out = Val.nil :: a :: b :: tl)
      (fun _ => Kp * (vsz Val.nil + 1)) (fun _ => Kp * 2)
      (hpush main Val.nil) ?_ ?_ ?_
    · intro vs _
      trivial
    · intro vs out hv hq
      rw [hv] at hq
      exact hq
    · intro vs _
      rw [vsz_nil_val]
  -- stage 2 : `roll 2` brings `b` to the top
  have s2 : HvdH.WordR main (rollP 2) (fun vs => vs = Val.nil :: a :: b :: tl)
      (fun _ out => out = b :: Val.nil :: a :: tl)
      (fun _ => Kr * 3 * (vsz a + vsz b + 2)) := by
    refine hK.conseq main (rollP 2) (fun vs => 2 < vs.length)
      (fun vs => vs = Val.nil :: a :: b :: tl)
      (fun vs out => out = vs.getD 2 .nil :: vs.eraseIdx 2)
      (fun _ out => out = b :: Val.nil :: a :: tl)
      (fun vs => Kr * (2 + 1) * (((vs.take (2 + 1)).map vsz).sum + 1))
      (fun _ => Kr * 3 * (vsz a + vsz b + 2))
      (hroll main 2) ?_ ?_ ?_
    · intro vs hv
      rw [hv]
      simp only [List.length_cons]
      omega
    · intro vs out hv hq
      rw [hv] at hq
      rw [hq]
      simp
    · intro vs hv
      rw [hv]
      have hsum : (((List.take (2 + 1) (Val.nil :: a :: b :: tl)).map vsz).sum + 1)
          = vsz a + vsz b + 2 := by
        simp only [List.take, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          vsz_nil_val, Nat.add_zero]
        omega
      rw [hsum]
  -- stage 3 : `consV` forms `cons b nil`
  have s3 : HvdH.WordR main consP (fun vs => vs = b :: Val.nil :: a :: tl)
      (fun _ out => out = Val.cons b Val.nil :: a :: tl) (fun _ => Kc) := by
    refine hK.conseq main consP (fun vs => 2 ≤ vs.length)
      (fun vs => vs = b :: Val.nil :: a :: tl)
      (fun vs out => ∃ (x y : Val) (r : List Val), vs = x :: y :: r ∧ out = Val.cons x y :: r)
      (fun _ out => out = Val.cons b Val.nil :: a :: tl)
      (fun _ => Kc) (fun _ => Kc) (hcons main) ?_ ?_ ?_
    · intro vs hv
      rw [hv]
      simp only [List.length_cons]
      omega
    · intro vs out hv hq
      obtain ⟨x, y, r, hvs, hout⟩ := hq
      rw [hv] at hvs
      simp only [List.cons.injEq] at hvs
      obtain ⟨h1, h2, h3⟩ := hvs
      rw [← h1, ← h2, ← h3] at hout
      exact hout
    · intro vs _
      exact le_rfl
  -- stage 4 : `swap` puts `a` back on top
  have s4 : HvdH.WordR main swapP (fun vs => vs = Val.cons b Val.nil :: a :: tl)
      (fun _ out => out = a :: Val.cons b Val.nil :: tl)
      (fun _ => Ks * (vsz a + vsz b + 3)) := by
    refine hK.conseq main swapP (fun vs => 2 ≤ vs.length)
      (fun vs => vs = Val.cons b Val.nil :: a :: tl)
      (fun vs out => ∃ (x y : Val) (r : List Val), vs = x :: y :: r ∧ out = y :: x :: r)
      (fun _ out => out = a :: Val.cons b Val.nil :: tl)
      (fun vs => Ks * (vsz (vs.getD 0 .nil) + vsz (vs.getD 1 .nil) + 1))
      (fun _ => Ks * (vsz a + vsz b + 3)) (hswap main) ?_ ?_ ?_
    · intro vs hv
      rw [hv]
      simp only [List.length_cons]
      omega
    · intro vs out hv hq
      obtain ⟨x, y, r, hvs, hout⟩ := hq
      rw [hv] at hvs
      simp only [List.cons.injEq] at hvs
      obtain ⟨h1, h2, h3⟩ := hvs
      rw [← h1, ← h2, ← h3] at hout
      exact hout
    · intro vs hv
      rw [hv]
      simp only [List.getD_cons_zero, List.getD_cons_succ]
      have harg : vsz (Val.cons b Val.nil) + vsz a + 1 = vsz a + vsz b + 3 := by
        rw [Work.ConvR.vsz_cons, vsz_nil_val]
        ring
      rw [harg]
  -- stage 5 : `consV` forms `cons a (cons b nil)`
  have s5 : HvdH.WordR main consP (fun vs => vs = a :: Val.cons b Val.nil :: tl)
      (fun _ out => out = Val.cons a (Val.cons b Val.nil) :: tl) (fun _ => Kc) := by
    refine hK.conseq main consP (fun vs => 2 ≤ vs.length)
      (fun vs => vs = a :: Val.cons b Val.nil :: tl)
      (fun vs out => ∃ (x y : Val) (r : List Val), vs = x :: y :: r ∧ out = Val.cons x y :: r)
      (fun _ out => out = Val.cons a (Val.cons b Val.nil) :: tl)
      (fun _ => Kc) (fun _ => Kc) (hcons main) ?_ ?_ ?_
    · intro vs hv
      rw [hv]
      simp only [List.length_cons]
      omega
    · intro vs out hv hq
      obtain ⟨x, y, r, hvs, hout⟩ := hq
      rw [hv] at hvs
      simp only [List.cons.injEq] at hvs
      obtain ⟨h1, h2, h3⟩ := hvs
      rw [← h1, ← h2, ← h3] at hout
      exact hout
    · intro vs _
      exact le_rfl
  -- assembly : `swap ;;; consV`
  have s45 : HvdH.WordR main (swapP ;;; consP)
      (fun vs => vs = Val.cons b Val.nil :: a :: tl)
      (fun _ out => out = Val.cons a (Val.cons b Val.nil) :: tl)
      (fun _ => Ks * (vsz a + vsz b + 3) + Kc) := by
    refine hK.conseq main (swapP ;;; consP)
      (fun vs => vs = Val.cons b Val.nil :: a :: tl)
      (fun vs => vs = Val.cons b Val.nil :: a :: tl)
      (fun vs out => ∃ mid, mid = a :: Val.cons b Val.nil :: tl ∧
        out = Val.cons a (Val.cons b Val.nil) :: tl)
      (fun _ out => out = Val.cons a (Val.cons b Val.nil) :: tl)
      (fun _ => Ks * (vsz a + vsz b + 3) + Kc)
      (fun _ => Ks * (vsz a + vsz b + 3) + Kc)
      (hK.seq main swapP consP
        (fun vs => vs = Val.cons b Val.nil :: a :: tl)
        (fun _ out => out = a :: Val.cons b Val.nil :: tl)
        (fun _ => Ks * (vsz a + vsz b + 3))
        (fun vs => vs = a :: Val.cons b Val.nil :: tl)
        (fun _ out => out = Val.cons a (Val.cons b Val.nil) :: tl)
        (fun _ => Kc) (fun _ => Kc)
        s4 s5 (fun vs mid hv hq => ⟨hq, le_rfl⟩))
      ?_ ?_ ?_
    · intro vs hv
      exact hv
    · intro vs out hv hq
      obtain ⟨mid, _, ho⟩ := hq
      exact ho
    · intro vs _
      exact le_rfl
  -- assembly : `consV ;;; swap ;;; consV`
  have s345 : HvdH.WordR main (consP ;;; swapP ;;; consP)
      (fun vs => vs = b :: Val.nil :: a :: tl)
      (fun _ out => out = Val.cons a (Val.cons b Val.nil) :: tl)
      (fun _ => Kc + (Ks * (vsz a + vsz b + 3) + Kc)) := by
    refine hK.conseq main (consP ;;; swapP ;;; consP)
      (fun vs => vs = b :: Val.nil :: a :: tl)
      (fun vs => vs = b :: Val.nil :: a :: tl)
      (fun vs out => ∃ mid, mid = Val.cons b Val.nil :: a :: tl ∧
        out = Val.cons a (Val.cons b Val.nil) :: tl)
      (fun _ out => out = Val.cons a (Val.cons b Val.nil) :: tl)
      (fun _ => Kc + (Ks * (vsz a + vsz b + 3) + Kc))
      (fun _ => Kc + (Ks * (vsz a + vsz b + 3) + Kc))
      (hK.seq main consP (swapP ;;; consP)
        (fun vs => vs = b :: Val.nil :: a :: tl)
        (fun _ out => out = Val.cons b Val.nil :: a :: tl)
        (fun _ => Kc)
        (fun vs => vs = Val.cons b Val.nil :: a :: tl)
        (fun _ out => out = Val.cons a (Val.cons b Val.nil) :: tl)
        (fun _ => Ks * (vsz a + vsz b + 3) + Kc)
        (fun _ => Ks * (vsz a + vsz b + 3) + Kc)
        s3 s45 (fun vs mid hv hq => ⟨hq, le_rfl⟩))
      ?_ ?_ ?_
    · intro vs hv
      exact hv
    · intro vs out hv hq
      obtain ⟨mid, _, ho⟩ := hq
      exact ho
    · intro vs _
      exact le_rfl
  -- assembly : `roll 2 ;;; consV ;;; swap ;;; consV`
  have s2345 : HvdH.WordR main (rollP 2 ;;; consP ;;; swapP ;;; consP)
      (fun vs => vs = Val.nil :: a :: b :: tl)
      (fun _ out => out = Val.cons a (Val.cons b Val.nil) :: tl)
      (fun _ => Kr * 3 * (vsz a + vsz b + 2) + (Kc + (Ks * (vsz a + vsz b + 3) + Kc))) := by
    refine hK.conseq main (rollP 2 ;;; consP ;;; swapP ;;; consP)
      (fun vs => vs = Val.nil :: a :: b :: tl)
      (fun vs => vs = Val.nil :: a :: b :: tl)
      (fun vs out => ∃ mid, mid = b :: Val.nil :: a :: tl ∧
        out = Val.cons a (Val.cons b Val.nil) :: tl)
      (fun _ out => out = Val.cons a (Val.cons b Val.nil) :: tl)
      (fun _ => Kr * 3 * (vsz a + vsz b + 2) + (Kc + (Ks * (vsz a + vsz b + 3) + Kc)))
      (fun _ => Kr * 3 * (vsz a + vsz b + 2) + (Kc + (Ks * (vsz a + vsz b + 3) + Kc)))
      (hK.seq main (rollP 2) (consP ;;; swapP ;;; consP)
        (fun vs => vs = Val.nil :: a :: b :: tl)
        (fun _ out => out = b :: Val.nil :: a :: tl)
        (fun _ => Kr * 3 * (vsz a + vsz b + 2))
        (fun vs => vs = b :: Val.nil :: a :: tl)
        (fun _ out => out = Val.cons a (Val.cons b Val.nil) :: tl)
        (fun _ => Kc + (Ks * (vsz a + vsz b + 3) + Kc))
        (fun _ => Kc + (Ks * (vsz a + vsz b + 3) + Kc))
        s2 s345 (fun vs mid hv hq => ⟨hq, le_rfl⟩))
      ?_ ?_ ?_
    · intro vs hv
      exact hv
    · intro vs out hv hq
      obtain ⟨mid, _, ho⟩ := hq
      exact ho
    · intro vs _
      exact le_rfl
  -- assembly : the whole program
  have sfull : HvdH.WordR main (pushP Val.nil ;;; rollP 2 ;;; consP ;;; swapP ;;; consP)
      (fun vs => vs = a :: b :: tl)
      (fun _ out => out = Val.cons a (Val.cons b Val.nil) :: tl)
      (fun _ => Kp * 2 + (Kr * 3 * (vsz a + vsz b + 2) +
        (Kc + (Ks * (vsz a + vsz b + 3) + Kc)))) := by
    refine hK.conseq main (pushP Val.nil ;;; rollP 2 ;;; consP ;;; swapP ;;; consP)
      (fun vs => vs = a :: b :: tl)
      (fun vs => vs = a :: b :: tl)
      (fun vs out => ∃ mid, mid = Val.nil :: a :: b :: tl ∧
        out = Val.cons a (Val.cons b Val.nil) :: tl)
      (fun _ out => out = Val.cons a (Val.cons b Val.nil) :: tl)
      (fun _ => Kp * 2 + (Kr * 3 * (vsz a + vsz b + 2) +
        (Kc + (Ks * (vsz a + vsz b + 3) + Kc))))
      (fun _ => Kp * 2 + (Kr * 3 * (vsz a + vsz b + 2) +
        (Kc + (Ks * (vsz a + vsz b + 3) + Kc))))
      (hK.seq main (pushP Val.nil) (rollP 2 ;;; consP ;;; swapP ;;; consP)
        (fun vs => vs = a :: b :: tl)
        (fun _ out => out = Val.nil :: a :: b :: tl)
        (fun _ => Kp * 2)
        (fun vs => vs = Val.nil :: a :: b :: tl)
        (fun _ out => out = Val.cons a (Val.cons b Val.nil) :: tl)
        (fun _ => Kr * 3 * (vsz a + vsz b + 2) + (Kc + (Ks * (vsz a + vsz b + 3) + Kc)))
        (fun _ => Kr * 3 * (vsz a + vsz b + 2) + (Kc + (Ks * (vsz a + vsz b + 3) + Kc)))
        s1 s2345 (fun vs mid hv hq => ⟨hq, le_rfl⟩))
      ?_ ?_ ?_
    · intro vs hv
      exact hv
    · intro vs out hv hq
      obtain ⟨mid, _, ho⟩ := hq
      exact ho
    · intro vs _
      exact le_rfl
  -- final reshaping : the cost bound and `ofList [a, b]`
  refine hK.conseq main (pushP Val.nil ;;; rollP 2 ;;; consP ;;; swapP ;;; consP)
    (fun vs => vs = a :: b :: tl) (fun vs => vs = a :: b :: tl)
    (fun _ out => out = Val.cons a (Val.cons b Val.nil) :: tl)
    (fun _ out => out = ofList [a, b] :: tl)
    (fun _ => Kp * 2 + (Kr * 3 * (vsz a + vsz b + 2) +
      (Kc + (Ks * (vsz a + vsz b + 3) + Kc))))
    (fun _ => (2 * Kp + 3 * Kr + Ks + 2 * Kc) * (vsz a + vsz b + 3))
    sfull ?_ ?_ ?_
  · intro vs hv
    exact hv
  · intro vs out hv hq
    rw [hq]
    rfl
  · intro vs _
    exact twoListCost Kp Kr Kc Ks (vsz a) (vsz b)

end Work.KronP
