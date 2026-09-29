import Mathlib
import Submission.Work.KronP.defs

namespace Work.KronP

open HvdH

/-!
# `Work.KronP.mapFstWord`

The word that replaces a vector `xs : List (ℤ × ℤ)` of fixed-point complex values
(encoded as `cvecVal xs`) by the value vector of its real parts (`zsVal (xs.map Prod.fst)`),
using `KernelLib.mapList` with the one-element program

`unconsV ;;; roll 1 ;;; drop`

which maps `cfxVal z = cons (int z.1) (int z.2)` to `int z.1`.

The cost is linear in the total size `xs.length * (L + 1)`, where `L` bounds the encoding size
of every `cfxVal z` (so that `L + 1` bounds the cost of touching one element).
-/

/-- `stepQ x y`: `x` is a fixed-point complex value `cfxVal z` and `y` is its real part. -/
private def stepQ (x y : Val) : Prop := ∃ z : ℤ × ℤ, x = cfxVal z ∧ y = .int z.1

/-- Under `List.Forall₂ stepQ`, a list of values is the list of real parts of the
corresponding complex values. -/
private theorem forall2_stepQ_map_cfx {xs : List (ℤ × ℤ)} {ys : List Val}
    (h : List.Forall₂ stepQ (xs.map cfxVal) ys) :
    ys = xs.map (fun z => Val.int z.1) := by
  induction xs generalizing ys with
  | nil =>
    simp only [List.map_nil, List.forall₂_nil_left_iff] at h
    exact h
  | cons z zs ih =>
    rw [List.map_cons, List.forall₂_cons_left_iff] at h
    obtain ⟨y, ys', h1, h2, rfl⟩ := h
    obtain ⟨z', hz', hy⟩ := h1
    have hzz : z' = z := by
      have h' := hz'
      simp only [cfxVal, Val.cons.injEq, Val.int.injEq] at h'
      exact Prod.ext h'.1.symm h'.2.symm
    subst hzz
    rw [hy, ih h2]
    rfl

/-- The result of `mapList` with `stepQ` is exactly `zsVal (xs.map Prod.fst)`. -/
private theorem ofList_stepQ {xs : List (ℤ × ℤ)} {ys : List Val}
    (h : List.Forall₂ stepQ (xs.map cfxVal) ys) :
    ofList ys = zsVal (xs.map Prod.fst) := by
  rw [forall2_stepQ_map_cfx h]
  simp [zsVal, ofList, List.map_map, Function.comp_def]

/-- Cost arithmetic for the final assembly. -/
private theorem cost_total (Cs Km n L : ℕ) :
    n * (Cs * (L + 1) + Km * (L + 1)) + Km ≤ (Cs + 2 * Km + 1) * (n * (L + 1) + L + 1) := by
  have h1 : n * (Cs * (L + 1) + Km * (L + 1)) = (Cs + Km) * (n * (L + 1)) := by ring
  rw [h1]
  have h2 : Km ≤ Km * (L + 1) := by
    calc Km = Km * 1 := by ring
      _ ≤ Km * (L + 1) := Nat.mul_le_mul_left _ (by omega)
  have h3 : (Cs + Km) * (n * (L + 1)) ≤ (Cs + 2 * Km + 1) * (n * (L + 1)) :=
    Nat.mul_le_mul_right _ (by omega)
  have h4 : Km * (L + 1) ≤ (Cs + 2 * Km + 1) * (L + 1) := Nat.mul_le_mul_right _ (by omega)
  calc (Cs + Km) * (n * (L + 1)) + Km
      ≤ (Cs + 2 * Km + 1) * (n * (L + 1)) + Km * (L + 1) := by omega
    _ ≤ (Cs + 2 * Km + 1) * (n * (L + 1)) + (Cs + 2 * Km + 1) * (L + 1) := by omega
    _ = (Cs + 2 * Km + 1) * (n * (L + 1) + L + 1) := by ring

/-- Cost arithmetic for the one-element program: three stages of cost `Ca * (L+1)`. -/
private theorem cost_step (Ca L : ℕ) :
    Ca * (L + 1) + Ca * (L + 1) + Ca * (L + 1) ≤ (3 * Ca + 1) * (L + 1) := by
  nlinarith [Nat.zero_le L, Nat.zero_le Ca]

/-- A product of two bounds. -/
private theorem stage_le (c A L Ca : ℕ) (hA : A ≤ L) (hc : c ≤ Ca) : c * A ≤ Ca * (L + 1) := by
  calc c * A ≤ Ca * A := Nat.mul_le_mul_right _ hc
    _ ≤ Ca * L := Nat.mul_le_mul_left _ hA
    _ ≤ Ca * (L + 1) := Nat.mul_le_mul_left _ (by omega)

private theorem le_mul_succ (c L : ℕ) : c ≤ c * (L + 1) :=
  Nat.le_mul_of_pos_right c (by omega : 0 < L + 1)

theorem mapFstWord (hK : HvdH.KernelLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ),
      ∀ (main : HvdH.Cmd) (xs : List (ℤ × ℤ)) (L : ℕ) (tl : List HvdH.Val),
        (∀ z ∈ xs, HvdH.vsz (HvdH.cfxVal z) ≤ L) →
        HvdH.WordR main prog
          (fun vs => vs = HvdH.cvecVal xs :: tl)
          (fun _ out => out = Work.KronP.zsVal (xs.map Prod.fst) :: tl)
          (fun _ => K * (xs.length * (L + 1) + L + 1)) := by
  obtain ⟨unP, Ku, hu⟩ := hK.unconsV
  obtain ⟨rollP, Kr, hr⟩ := hK.roll
  obtain ⟨dropP, Kd, hd⟩ := hK.drop
  obtain ⟨mapP, Km, hm⟩ := hK.mapList
  refine ⟨mapP (HvdH.Cmd.seq (HvdH.Cmd.seq unP (rollP 1)) dropP),
    (3 * (Ku + 2 * Kr + Kd + 1) + 1) + 2 * Km + 1, ?_⟩
  intro main xs L tl hS
  have hstep : ∀ (x : Val) (rest : List Val), (∃ z : ℤ × ℤ, x = cfxVal z) → vsz x ≤ L →
      WordR main (HvdH.Cmd.seq (HvdH.Cmd.seq unP (rollP 1)) dropP)
        (fun vs => vs = x :: rest)
        (fun _ out => ∃ y, out = y :: rest ∧ stepQ x y ∧ vsz y ≤ L)
        (fun _ => (3 * (Ku + 2 * Kr + Kd + 1) + 1) * (L + 1)) := by
    intro x rest hx hxL
    obtain ⟨z, rfl⟩ := hx
    have hvs : vsz (cfxVal z) = isz z.1 + isz z.2 + 1 := by
      simp only [cfxVal, Work.ConvR.vsz_cons, Work.ConvR.vsz_int]
    have hxsz : isz z.1 + isz z.2 + 1 ≤ L := by
      rwa [hvs] at hxL
    have hz2 : isz z.2 + 1 ≤ L := by omega
    -- stage 1: `cons (int z.1) (int z.2) -> int z.1 :: int z.2 :: rest`
    have hA : WordR main unP (fun vs => vs = cfxVal z :: rest)
        (fun _ out => out = .int z.1 :: .int z.2 :: rest)
        (fun _ => (Ku + 2 * Kr + Kd + 1) * (L + 1)) := by
      refine hK.conseq main unP
        (fun vs => ∃ (a b : Val) (r : List Val), vs = .cons a b :: r)
        (fun vs => vs = cfxVal z :: rest)
        (fun vs out => ∃ (a b : Val) (r : List Val), vs = .cons a b :: r ∧ out = a :: b :: r)
        (fun _ out => out = .int z.1 :: .int z.2 :: rest)
        (fun _ => Ku)
        (fun _ => (Ku + 2 * Kr + Kd + 1) * (L + 1))
        (hu main) ?_ ?_ ?_
      · intro vs hv
        rw [hv]
        exact ⟨.int z.1, .int z.2, rest, rfl⟩
      · intro vs out hv hq
        obtain ⟨a, b, r, hvs', hout⟩ := hq
        rw [hv] at hvs'
        have h' : a = .int z.1 ∧ b = .int z.2 ∧ r = rest := by
          have h2 := hvs'
          simp only [cfxVal, List.cons.injEq, Val.cons.injEq] at h2
          exact ⟨h2.1.1.symm, h2.1.2.symm, h2.2.symm⟩
        rw [hout, h'.1, h'.2.1, h'.2.2]
      · intro vs _
        exact le_trans (le_mul_succ Ku L) (Nat.mul_le_mul_right _ (by omega))
    -- stage 2: `roll 1` moves `int z.2` to the top
    have hB : WordR main (rollP 1) (fun vs => vs = .int z.1 :: .int z.2 :: rest)
        (fun _ out => out = .int z.2 :: .int z.1 :: rest)
        (fun _ => (Ku + 2 * Kr + Kd + 1) * (L + 1)) := by
      refine hK.conseq main (rollP 1)
        (fun vs => 1 < vs.length)
        (fun vs => vs = .int z.1 :: .int z.2 :: rest)
        (fun vs out => out = vs.getD 1 .nil :: vs.eraseIdx 1)
        (fun _ out => out = .int z.2 :: .int z.1 :: rest)
        (fun vs => Kr * (1 + 1) * (((vs.take (1 + 1)).map vsz).sum + 1))
        (fun _ => (Ku + 2 * Kr + Kd + 1) * (L + 1))
        (hr main 1) ?_ ?_ ?_
      · intro vs hv
        rw [hv]
        simp
      · intro vs out hv hq
        rw [hv] at hq
        rw [hq]
        simp
      · intro vs hv
        rw [hv]
        have h2 : ((List.map vsz [Val.int z.1, Val.int z.2]).sum + 1)
            = isz z.1 + isz z.2 + 1 := by
          simp [Work.ConvR.vsz_int]
        rw [show (List.take (1 + 1) (Val.int z.1 :: Val.int z.2 :: rest))
              = [Val.int z.1, Val.int z.2] from rfl, h2]
        exact stage_le (Kr * 2) (isz z.1 + isz z.2 + 1) L (Ku + 2 * Kr + Kd + 1) hxsz (by omega)
    -- stage 3: `drop` removes `int z.2`
    have hC : WordR main dropP (fun vs => vs = .int z.2 :: .int z.1 :: rest)
        (fun _ out => out = .int z.1 :: rest)
        (fun _ => (Ku + 2 * Kr + Kd + 1) * (L + 1)) := by
      refine hK.conseq main dropP
        (fun vs => vs ≠ [])
        (fun vs => vs = .int z.2 :: .int z.1 :: rest)
        (fun vs out => ∃ (v : Val) (r : List Val), vs = v :: r ∧ out = r)
        (fun _ out => out = .int z.1 :: rest)
        (fun vs => Kd * (vsz (vs.headD .nil) + 1))
        (fun _ => (Ku + 2 * Kr + Kd + 1) * (L + 1))
        (hd main) ?_ ?_ ?_
      · intro vs hv
        rw [hv]
        simp
      · intro vs out hv hq
        obtain ⟨v, r, hvs', hout⟩ := hq
        rw [hv] at hvs'
        have h' : r = .int z.1 :: rest := by
          have h2 := hvs'
          simp only [List.cons.injEq] at h2
          exact h2.2.symm
        rw [hout, h']
      · intro vs hv
        rw [hv]
        have h2 : vsz (Val.int z.2) = isz z.2 := Work.ConvR.vsz_int z.2
        rw [show (Val.int z.2 :: Val.int z.1 :: rest).headD .nil = Val.int z.2 from rfl, h2]
        exact stage_le Kd (isz z.2 + 1) L (Ku + 2 * Kr + Kd + 1) hz2 (by omega)
    have hAB : WordR main (HvdH.Cmd.seq unP (rollP 1))
        (fun vs => vs = cfxVal z :: rest)
        (fun _ out => out = .int z.2 :: .int z.1 :: rest)
        (fun _ => (Ku + 2 * Kr + Kd + 1) * (L + 1) + (Ku + 2 * Kr + Kd + 1) * (L + 1)) := by
      refine hK.conseq main (HvdH.Cmd.seq unP (rollP 1)) _ _ _ _ _ _
        (hK.seq main unP (rollP 1)
          (fun vs => vs = cfxVal z :: rest)
          (fun _ out => out = .int z.1 :: .int z.2 :: rest)
          (fun _ => (Ku + 2 * Kr + Kd + 1) * (L + 1))
          (fun vs => vs = .int z.1 :: .int z.2 :: rest)
          (fun _ out => out = .int z.2 :: .int z.1 :: rest)
          (fun _ => (Ku + 2 * Kr + Kd + 1) * (L + 1))
          (fun _ => (Ku + 2 * Kr + Kd + 1) * (L + 1))
          hA hB (fun vs mid hv hq => ⟨by simpa using hq, le_rfl⟩)) ?_ ?_ ?_
      · intro vs hv; exact hv
      · intro vs out hv hq
        obtain ⟨m, hm, hmid⟩ := hq
        exact hmid
      · intro vs _; exact le_rfl
    have hABC : WordR main (HvdH.Cmd.seq (HvdH.Cmd.seq unP (rollP 1)) dropP)
        (fun vs => vs = cfxVal z :: rest)
        (fun _ out => out = .int z.1 :: rest)
        (fun _ => (Ku + 2 * Kr + Kd + 1) * (L + 1) + (Ku + 2 * Kr + Kd + 1) * (L + 1)
          + (Ku + 2 * Kr + Kd + 1) * (L + 1)) := by
      refine hK.conseq main (HvdH.Cmd.seq (HvdH.Cmd.seq unP (rollP 1)) dropP) _ _ _ _ _ _
        (hK.seq main (HvdH.Cmd.seq unP (rollP 1)) dropP
          (fun vs => vs = cfxVal z :: rest)
          (fun _ out => out = .int z.2 :: .int z.1 :: rest)
          (fun _ => (Ku + 2 * Kr + Kd + 1) * (L + 1) + (Ku + 2 * Kr + Kd + 1) * (L + 1))
          (fun vs => vs = .int z.2 :: .int z.1 :: rest)
          (fun _ out => out = .int z.1 :: rest)
          (fun _ => (Ku + 2 * Kr + Kd + 1) * (L + 1))
          (fun _ => (Ku + 2 * Kr + Kd + 1) * (L + 1))
          hAB hC (fun vs mid hv hq => ⟨by simpa using hq, le_rfl⟩)) ?_ ?_ ?_
      · intro vs hv; exact hv
      · intro vs out hv hq
        obtain ⟨m, hm, hmid⟩ := hq
        exact hmid
      · intro vs _; exact le_rfl
    refine hK.conseq main (HvdH.Cmd.seq (HvdH.Cmd.seq unP (rollP 1)) dropP)
      (fun vs => vs = cfxVal z :: rest) (fun vs => vs = cfxVal z :: rest)
      (fun _ out => out = .int z.1 :: rest)
      (fun _ out => ∃ y, out = y :: rest ∧ stepQ (cfxVal z) y ∧ vsz y ≤ L)
      _ (fun _ => (3 * (Ku + 2 * Kr + Kd + 1) + 1) * (L + 1)) hABC ?_ ?_ ?_
    · intro vs hv; exact hv
    · intro vs out hv hq
      refine ⟨.int z.1, hq, ?_⟩
      exact And.intro (Exists.intro z (And.intro rfl rfl)) (by
        rw [Work.ConvR.vsz_int]
        omega)
    · intro vs _
      exact cost_step (Ku + 2 * Kr + Kd + 1) L
  have hmain := hm main (HvdH.Cmd.seq (HvdH.Cmd.seq unP (rollP 1)) dropP) tl
      (fun x => (∃ z : ℤ × ℤ, x = cfxVal z) ∧ vsz x ≤ L) stepQ
      ((3 * (Ku + 2 * Kr + Kd + 1) + 1) * (L + 1)) L
      (fun x hx => hstep x tl hx.1 hx.2)
      (xs.map cfxVal)
      (fun x hx => by
        obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
        exact And.intro (And.intro (Exists.intro z rfl) (hS z hz)) (hS z hz))
  refine hK.conseq main (mapP (HvdH.Cmd.seq (HvdH.Cmd.seq unP (rollP 1)) dropP))
      (fun vs => vs = ofList (xs.map cfxVal) :: tl)
      (fun vs => vs = cvecVal xs :: tl)
      (fun _ out => ∃ ys, out = ofList ys :: tl ∧ List.Forall₂ stepQ (xs.map cfxVal) ys)
      (fun _ out => out = zsVal (xs.map Prod.fst) :: tl)
      _ (fun _ => (3 * (Ku + 2 * Kr + Kd + 1) + 1 + 2 * Km + 1) * (xs.length * (L + 1) + L + 1))
      hmain ?_ ?_ ?_
  · intro vs hv
    rw [hv]
    rfl
  · intro vs out hv hq
    obtain ⟨ys, hout, hf⟩ := hq
    rw [hout]
    exact congrArg (fun v => v :: tl) (ofList_stepQ hf)
  · intro vs _
    rw [List.length_map]
    exact cost_total _ _ _ _

end Work.KronP
