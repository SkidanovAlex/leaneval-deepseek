import Mathlib
import Submission.Work.Resample.buQWdefs
import Submission.Work.Resample.auKit
import Submission.Work.Resample.buQWstepKit
import Submission.Work.Resample.buQWelemKit

/-!
# `Work.Resample.buQWr1Rot`: rotating a vector by `j`

The word reads `[int j, cvecVal v]` and writes `[cvecVal (buRot j.toNat v)]`, where
`buRot k v = v.drop k ++ v.take k` (`buQWdefs.lean`).  Since `cvecVal v = ofList (v.map cfxVal)`,
this is a purely *list-level* transformation: duplicate the pair `(int j, ofList xs)` with two
`pick`s, run `LayoutLib.take` on the first copy and `LayoutLib.drop` on the second, and glue the
two results with `LayoutLib.append`.

The program is the chain
`pick 1 ;;; pick 1 ;;; take ;;; roll 2 ;;; roll 2 ;;; drop ;;; append`,
whose windows are
`[A,B] ↦ [B,A,B] ↦ [A,B,A,B] ↦ [T,A,B] ↦ [B,T,A] ↦ [A,B,T] ↦ [U,T] ↦ [W]`
with `A = int j`, `B = ofList xs`, `T = ofList (xs.take j.toNat)`, `U = ofList (xs.drop j.toNat)`
and `W = ofList (xs.drop j.toNat ++ xs.take j.toNat)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.Resample

open HvdH
open Work.Fx

local infixr:68 " ;;; " => HvdH.Cmd.seq

/-! ## Local helpers -/

/-- A `WordR` whose pre/post are the `∃ rest` forms of a fixed-window transformation is a `Pipe`. -/
theorem buQWr1Rot_ofWordR {main prog : Cmd} {A B : List Val} {c : ℕ}
    (h : WordR main prog (fun vs => ∃ rest, vs = A ++ rest)
      (fun vs out => ∃ rest, vs = A ++ rest ∧ out = B ++ rest) (fun _ => c)) :
    Pipe main prog A B c := by
  intro rest vs hvs s R hR
  obtain ⟨out, s', n, ⟨r, hvs', hout⟩, hev, hn, hstk, hoth⟩ := h vs ⟨rest, hvs⟩ s R hR
  have hr : r = rest := List.append_cancel_left (hvs'.symm.trans hvs)
  exact ⟨out, s', n, by rw [hout, hr], hev, hn, hstk, hoth⟩

/-- `vsz (ofList l) = szl l + l.length + 1`. -/
theorem buQWr1Rot_vsz_ofList (l : List Val) : vsz (ofList l) = szl l + l.length + 1 := by
  induction l with
  | nil => rfl
  | cons x t ih =>
      rw [show ofList (x :: t) = Val.cons x (ofList t) from rfl, Work.Fx.vsz_cons,
        Work.Fx.szl_cons, ih, List.length_cons]
      ring

/-- `vsz (ofList l) ≤ (l.length + 1) * (B + 1)` when every entry of `l` has size `≤ B`. -/
theorem buQWr1Rot_vsz_ofList_le {l : List Val} {B : ℕ} (h : ∀ x ∈ l, vsz x ≤ B) :
    vsz (ofList l) ≤ (l.length + 1) * (B + 1) := by
  have h1 : szl l ≤ l.length * B := szl_le_len_mul h
  have h2 : vsz (ofList l) = szl l + l.length + 1 := buQWr1Rot_vsz_ofList l
  have he : (l.length + 1) * (B + 1) = l.length * B + l.length + B + 1 := by ring
  rw [h2, he]
  omega

/-- `szl (l.drop k) ≤ szl l`. -/
theorem buQWr1Rot_szl_drop_le (l : List Val) (k : ℕ) : szl (l.drop k) ≤ szl l := by
  have h := Work.Fx.szl_append (l.take k) (l.drop k)
  rw [List.take_append_drop] at h
  omega

/-- The pure arithmetic cost bound of the rotation chain. -/
theorem buQWr1Rot_cost (KP Ktk KR Kdo Kap s P I SB ST SU : ℕ)
    (hSB : SB ≤ 2 * ((s + 1) * (P + 1)))
    (hST : ST ≤ 2 * ((s + 1) * (P + 1)))
    (hSU : SU ≤ 2 * ((s + 1) * (P + 1))) :
    KP * 2 * (I + SB + 1)
      + (KP * 2 * (SB + I + 1)
      + (Ktk * (SB + I + 1)
      + (KR * 3 * (ST + I + SB + 1)
      + (KR * 3 * (SB + ST + I + 1)
      + (Kdo * (SB + I + 1) + Kap * (SU + 1))))))
    ≤ (8 * KP + 2 * Ktk + 24 * KR + 2 * Kdo + 2 * Kap) * ((s + 1) * (P + 1) + (I + 1)) := by
  set M : ℕ := (s + 1) * (P + 1) + (I + 1) with hM
  have hM2 : 2 * M = 2 * ((s + 1) * (P + 1)) + 2 * I + 2 := by rw [hM]; ring
  have hM4 : 4 * M = 4 * ((s + 1) * (P + 1)) + 4 * I + 4 := by rw [hM]; ring
  have e1 : I + SB + 1 ≤ 2 * M := by rw [hM2]; omega
  have e2 : SB + I + 1 ≤ 2 * M := by rw [hM2]; omega
  have e4 : ST + I + SB + 1 ≤ 4 * M := by rw [hM4]; omega
  have e5 : SB + ST + I + 1 ≤ 4 * M := by rw [hM4]; omega
  have e7 : SU + 1 ≤ 2 * M := by rw [hM2]; omega
  have t1 : KP * 2 * (I + SB + 1) ≤ 4 * KP * M := by
    calc KP * 2 * (I + SB + 1) ≤ KP * 2 * (2 * M) := Nat.mul_le_mul (le_refl _) e1
      _ = 4 * KP * M := by ring
  have t2 : KP * 2 * (SB + I + 1) ≤ 4 * KP * M := by
    calc KP * 2 * (SB + I + 1) ≤ KP * 2 * (2 * M) := Nat.mul_le_mul (le_refl _) e2
      _ = 4 * KP * M := by ring
  have t3 : Ktk * (SB + I + 1) ≤ 2 * Ktk * M := by
    calc Ktk * (SB + I + 1) ≤ Ktk * (2 * M) := Nat.mul_le_mul (le_refl _) e2
      _ = 2 * Ktk * M := by ring
  have t4 : KR * 3 * (ST + I + SB + 1) ≤ 12 * KR * M := by
    calc KR * 3 * (ST + I + SB + 1) ≤ KR * 3 * (4 * M) := Nat.mul_le_mul (le_refl _) e4
      _ = 12 * KR * M := by ring
  have t5 : KR * 3 * (SB + ST + I + 1) ≤ 12 * KR * M := by
    calc KR * 3 * (SB + ST + I + 1) ≤ KR * 3 * (4 * M) := Nat.mul_le_mul (le_refl _) e5
      _ = 12 * KR * M := by ring
  have t6 : Kdo * (SB + I + 1) ≤ 2 * Kdo * M := by
    calc Kdo * (SB + I + 1) ≤ Kdo * (2 * M) := Nat.mul_le_mul (le_refl _) e2
      _ = 2 * Kdo * M := by ring
  have t7 : Kap * (SU + 1) ≤ 2 * Kap * M := by
    calc Kap * (SU + 1) ≤ Kap * (2 * M) := Nat.mul_le_mul (le_refl _) e7
      _ = 2 * Kap * M := by ring
  have hsum := add_le_add t1 (add_le_add t2 (add_le_add t3 (add_le_add t4 (add_le_add t5
    (add_le_add t6 t7)))))
  have hfin : KP * 2 * (I + SB + 1)
      + (KP * 2 * (SB + I + 1)
      + (Ktk * (SB + I + 1)
      + (KR * 3 * (ST + I + SB + 1)
      + (KR * 3 * (SB + ST + I + 1)
      + (Kdo * (SB + I + 1) + Kap * (SU + 1))))))
      ≤ (8 * KP + 2 * Ktk + 24 * KR + 2 * Kdo + 2 * Kap) * M :=
    le_trans hsum (le_of_eq (by ring))
  rw [hM] at hfin
  exact hfin

/-! ## The rotation word -/

theorem buQWr1Rot (KL : HvdH.KernelLib) (LL : HvdH.LayoutLib) :
    ∃ (q : HvdH.Cmd) (Kc : ℕ),
    ∀ (main : HvdH.Cmd) (s : ℕ) (j : ℤ) (v : List (ℤ × ℤ)) (P : ℕ),
      0 ≤ j → j.toNat < s → v.length = s →
      (∀ z ∈ v, HvdH.isz z.1 ≤ P ∧ HvdH.isz z.2 ≤ P) →
      Work.Resample.Pipe main q [HvdH.Val.int j, HvdH.cvecVal v]
        [HvdH.cvecVal (Work.Resample.buRot j.toNat v)]
        (Kc * ((s + 1) * (P + 1) + (HvdH.isz j + 1))) := by
  obtain ⟨pickP, KP, hpick⟩ := KL.pick
  obtain ⟨rollP, KR, hroll⟩ := KL.roll
  obtain ⟨takeprog, Ktk, htake⟩ := LL.take
  obtain ⟨dropprog, Kdo, hdrop⟩ := LL.drop
  obtain ⟨appprog, Kap, happ⟩ := LL.append
  refine ⟨pickP 1 ;;; pickP 1 ;;; takeprog ;;; rollP 2 ;;; rollP 2 ;;; dropprog ;;; appprog,
    8 * KP + 2 * Ktk + 24 * KR + 2 * Kdo + 2 * Kap, ?_⟩
  intro main s j v P hj0 hjk hlen hP
  set xs : List Val := v.map HvdH.cfxVal with hxsdef
  have hxslen : xs.length = s := by rw [hxsdef, List.length_map, hlen]
  have key : ((j.toNat : ℤ)) = j := Int.toNat_of_nonneg hj0
  -- sizes
  have hBsizes : ∀ x ∈ xs, vsz x ≤ 2 * P + 1 := by
    intro x hx
    rw [hxsdef] at hx
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
    obtain ⟨h1, h2⟩ := hP z hz
    rw [Work.Fx.vsz_cfxVal]
    omega
  have hSB : vsz (ofList xs) ≤ 2 * ((s + 1) * (P + 1)) := by
    calc vsz (ofList xs) ≤ (xs.length + 1) * (2 * P + 1 + 1) := buQWr1Rot_vsz_ofList_le hBsizes
      _ = 2 * ((s + 1) * (P + 1)) := by rw [hxslen]; ring
  have hszlxs : szl xs + s + 1 ≤ 2 * ((s + 1) * (P + 1)) := by
    have h := buQWr1Rot_vsz_ofList xs
    rw [hxslen] at h
    omega
  have hST : vsz (ofList (xs.take j.toNat)) ≤ 2 * ((s + 1) * (P + 1)) := by
    rw [buQWr1Rot_vsz_ofList]
    have h1 : szl (xs.take j.toNat) ≤ szl xs := szl_take_le xs j.toNat
    have h2 : (xs.take j.toNat).length ≤ s := by rw [List.length_take]; omega
    omega
  have hSU : vsz (ofList (xs.drop j.toNat)) ≤ 2 * ((s + 1) * (P + 1)) := by
    rw [buQWr1Rot_vsz_ofList]
    have h1 : szl (xs.drop j.toNat) ≤ szl xs := buQWr1Rot_szl_drop_le xs j.toNat
    have h2 : (xs.drop j.toNat).length ≤ s := by rw [List.length_drop]; omega
    omega
  -- the chain, window by window
  have s1 : Pipe main (pickP 1) [HvdH.Val.int (j.toNat : ℤ), ofList xs]
      [ofList xs, HvdH.Val.int (j.toNat : ℤ), ofList xs]
      (KP * 2 * (isz (j.toNat : ℤ) + vsz (ofList xs) + 1)) := by
    have h := Pipe.pick main hpick (A := [HvdH.Val.int (j.toNat : ℤ), ofList xs]) (k := 1)
      (by simp)
    refine Pipe.le (Pipe.rw h (B' := [ofList xs, HvdH.Val.int (j.toNat : ℤ), ofList xs]) rfl) ?_
    show KP * 2 * (szl ([HvdH.Val.int (j.toNat : ℤ), ofList xs] : List Val) + 1)
      ≤ KP * 2 * (isz (j.toNat : ℤ) + vsz (ofList xs) + 1)
    rw [Work.Fx.szl_cons, Work.Fx.szl_cons, Work.Fx.szl_nil, Work.Fx.vsz_int]
    exact le_of_eq (by ring)
  have s2 : Pipe main (pickP 1) [ofList xs, HvdH.Val.int (j.toNat : ℤ), ofList xs]
      [HvdH.Val.int (j.toNat : ℤ), ofList xs, HvdH.Val.int (j.toNat : ℤ), ofList xs]
      (KP * 2 * (vsz (ofList xs) + isz (j.toNat : ℤ) + 1)) := by
    have h := Pipe.pick main hpick
      (A := [ofList xs, HvdH.Val.int (j.toNat : ℤ), ofList xs]) (k := 1) (by simp)
    refine Pipe.le (Pipe.rw h
      (B' := [HvdH.Val.int (j.toNat : ℤ), ofList xs, HvdH.Val.int (j.toNat : ℤ), ofList xs]) rfl) ?_
    show KP * 2 * (szl ([ofList xs, HvdH.Val.int (j.toNat : ℤ)] : List Val) + 1)
      ≤ KP * 2 * (vsz (ofList xs) + isz (j.toNat : ℤ) + 1)
    rw [Work.Fx.szl_cons, Work.Fx.szl_cons, Work.Fx.szl_nil, Work.Fx.vsz_int]
    exact le_of_eq (by ring)
  have s3 : Pipe main takeprog
      [HvdH.Val.int (j.toNat : ℤ), ofList xs, HvdH.Val.int (j.toNat : ℤ), ofList xs]
      [ofList (xs.take j.toNat), HvdH.Val.int (j.toNat : ℤ), ofList xs]
      (Ktk * (vsz (ofList xs) + isz (j.toNat : ℤ) + 1)) := by
    have h := buQWr1Rot_ofWordR (main := main) (prog := takeprog)
      (A := [HvdH.Val.int (j.toNat : ℤ), ofList xs]) (B := [ofList (xs.take j.toNat)])
      (c := Ktk * (vsz (ofList xs) + isz (j.toNat : ℤ) + 1)) (htake main j.toNat xs)
    simpa only [List.cons_append, List.nil_append] using
      (Pipe.appendTail [HvdH.Val.int (j.toNat : ℤ), ofList xs] h)
  have s4 : Pipe main (rollP 2)
      [ofList (xs.take j.toNat), HvdH.Val.int (j.toNat : ℤ), ofList xs]
      [ofList xs, ofList (xs.take j.toNat), HvdH.Val.int (j.toNat : ℤ)]
      (KR * 3 * (vsz (ofList (xs.take j.toNat)) + isz (j.toNat : ℤ) + vsz (ofList xs) + 1)) := by
    have h := Pipe.roll main hroll
      (A := [ofList (xs.take j.toNat), HvdH.Val.int (j.toNat : ℤ), ofList xs]) (k := 2) (by simp)
    refine Pipe.le (Pipe.rw h
      (B' := [ofList xs, ofList (xs.take j.toNat), HvdH.Val.int (j.toNat : ℤ)]) rfl) ?_
    show KR * 3 * (szl ([ofList (xs.take j.toNat), HvdH.Val.int (j.toNat : ℤ),
          ofList xs] : List Val) + 1)
      ≤ KR * 3 * (vsz (ofList (xs.take j.toNat)) + isz (j.toNat : ℤ) + vsz (ofList xs) + 1)
    rw [Work.Fx.szl_cons, Work.Fx.szl_cons, Work.Fx.szl_cons, Work.Fx.szl_nil, Work.Fx.vsz_int]
    exact le_of_eq (by ring)
  have s5 : Pipe main (rollP 2)
      [ofList xs, ofList (xs.take j.toNat), HvdH.Val.int (j.toNat : ℤ)]
      [HvdH.Val.int (j.toNat : ℤ), ofList xs, ofList (xs.take j.toNat)]
      (KR * 3 * (vsz (ofList xs) + vsz (ofList (xs.take j.toNat)) + isz (j.toNat : ℤ) + 1)) := by
    have h := Pipe.roll main hroll
      (A := [ofList xs, ofList (xs.take j.toNat), HvdH.Val.int (j.toNat : ℤ)]) (k := 2) (by simp)
    refine Pipe.le (Pipe.rw h
      (B' := [HvdH.Val.int (j.toNat : ℤ), ofList xs, ofList (xs.take j.toNat)]) rfl) ?_
    show KR * 3 * (szl ([ofList xs, ofList (xs.take j.toNat),
          HvdH.Val.int (j.toNat : ℤ)] : List Val) + 1)
      ≤ KR * 3 * (vsz (ofList xs) + vsz (ofList (xs.take j.toNat)) + isz (j.toNat : ℤ) + 1)
    rw [Work.Fx.szl_cons, Work.Fx.szl_cons, Work.Fx.szl_cons, Work.Fx.szl_nil, Work.Fx.vsz_int]
    exact le_of_eq (by ring)
  have s6 : Pipe main dropprog
      [HvdH.Val.int (j.toNat : ℤ), ofList xs, ofList (xs.take j.toNat)]
      [ofList (xs.drop j.toNat), ofList (xs.take j.toNat)]
      (Kdo * (vsz (ofList xs) + isz (j.toNat : ℤ) + 1)) := by
    have h := buQWr1Rot_ofWordR (main := main) (prog := dropprog)
      (A := [HvdH.Val.int (j.toNat : ℤ), ofList xs]) (B := [ofList (xs.drop j.toNat)])
      (c := Kdo * (vsz (ofList xs) + isz (j.toNat : ℤ) + 1)) (hdrop main j.toNat xs)
    simpa only [List.cons_append, List.nil_append] using
      (Pipe.appendTail [ofList (xs.take j.toNat)] h)
  have s7 : Pipe main appprog
      [ofList (xs.drop j.toNat), ofList (xs.take j.toNat)]
      [ofList (xs.drop j.toNat ++ xs.take j.toNat)]
      (Kap * (vsz (ofList (xs.drop j.toNat)) + 1)) :=
    buQWr1Rot_ofWordR (main := main) (prog := appprog)
      (A := [ofList (xs.drop j.toNat), ofList (xs.take j.toNat)])
      (B := [ofList (xs.drop j.toNat ++ xs.take j.toNat)])
      (c := Kap * (vsz (ofList (xs.drop j.toNat)) + 1))
      (happ main (xs.drop j.toNat) (xs.take j.toNat))
  have hc := Pipe.comp s1 (Pipe.comp s2 (Pipe.comp s3 (Pipe.comp s4 (Pipe.comp s5
    (Pipe.comp s6 s7)))))
  -- the cost bound
  have hcost : KP * 2 * (isz (j.toNat : ℤ) + vsz (ofList xs) + 1)
      + (KP * 2 * (vsz (ofList xs) + isz (j.toNat : ℤ) + 1)
      + (Ktk * (vsz (ofList xs) + isz (j.toNat : ℤ) + 1)
      + (KR * 3 * (vsz (ofList (xs.take j.toNat)) + isz (j.toNat : ℤ) + vsz (ofList xs) + 1)
      + (KR * 3 * (vsz (ofList xs) + vsz (ofList (xs.take j.toNat)) + isz (j.toNat : ℤ) + 1)
      + (Kdo * (vsz (ofList xs) + isz (j.toNat : ℤ) + 1)
        + Kap * (vsz (ofList (xs.drop j.toNat)) + 1))))))
      ≤ (8 * KP + 2 * Ktk + 24 * KR + 2 * Kdo + 2 * Kap)
        * ((s + 1) * (P + 1) + (isz j + 1)) := by
    rw [key]
    exact buQWr1Rot_cost KP Ktk KR Kdo Kap s P (isz j) (vsz (ofList xs))
      (vsz (ofList (xs.take j.toNat))) (vsz (ofList (xs.drop j.toNat))) hSB hST hSU
  have hmain := Pipe.le hc hcost
  -- convert the windows and the cost
  have hAeq : ([HvdH.Val.int (j.toNat : ℤ), ofList xs] : List HvdH.Val)
      = [HvdH.Val.int j, HvdH.cvecVal v] := by
    rw [key, hxsdef]
    rfl
  have hm : (Work.Resample.buRot j.toNat v).map HvdH.cfxVal = xs.drop j.toNat ++ xs.take j.toNat := by
    rw [Work.Resample.buRot, List.map_append, List.map_drop, List.map_take, ← hxsdef]
  have hBeq : ([ofList (xs.drop j.toNat ++ xs.take j.toNat)] : List HvdH.Val)
      = [HvdH.cvecVal (Work.Resample.buRot j.toNat v)] := by
    rw [← hm]
    rfl
  rw [hAeq, hBeq] at hmain
  exact hmain

end Work.Resample
