import Mathlib
import Submission.Work.MainP.crtLabDefs
import Submission.Work.Kernel.Raw
import Submission.Work.Layout.Base

/-!
# `crtLabEpi`: the epilogue of the CRT labelling word

This file proves `Work.MainP.crtLabEpi`: the last stage of the "label and sort" word of the CRT
reindexing (paper Prop. 5.4, step 2) which turns a list of records `prp v E = cons (int v) (ofList E)`
into the list of their *keys* `v` (i.e. into `ofList (rs.map (fun p => int (pairKey p)))`).

The word is `KernelLib.mapList` applied to the one-record epilogue of `crtLabEpiOne`: to turn the
record `cons (int v) (ofList E)` into `int v`, split the record with `unconsV`, `swap` the key and the
payload and `drop` the payload.  The cost per record is `O(vsz record) = O(L)`, and `mapList` adds a
factor `Y.length`, giving the stated bound.

The `LayoutLib` hypothesis is part of the signature of the requested lemma but is not needed here.
-/

set_option autoImplicit false

namespace Work.MainP

open HvdH

/-- `List.Forall₂ (fun a b => b = f a) xs ys` is exactly `ys = xs.map f`. -/
private theorem forall2MapEq {α β : Type} {f : α → β} {xs : List α} {ys : List β}
    (h : List.Forall₂ (fun a b => b = f a) xs ys) : ys = xs.map f := by
  induction h with
  | nil => rfl
  | cons hb _ ih =>
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨hb, ih⟩

/-- The one-record epilogue of the CRT labelling word: from a value stack whose top is a record
`prp v E`, produce the single integer value `int (pairKey (prp v E)) = int v`, at cost
`O(L + 1)` where `L` bounds the size of the record. -/
private theorem crtLabEpiOne (hK : HvdH.KernelLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (x : HvdH.Val) (L : ℕ) (rest : List HvdH.Val),
      (∃ (v : ℤ) (E : List HvdH.Val), x = Work.MainP.prp v E) →
      HvdH.vsz x ≤ L →
      HvdH.WordR main prog
        (fun vs => vs = x :: rest)
        (fun _ out => ∃ y : HvdH.Val, out = y :: rest ∧ y = HvdH.Val.int (HvdH.pairKey x) ∧
          HvdH.vsz y ≤ L)
        (fun _ => K * (L + 1)) := by
  obtain ⟨pu, Ku, hu⟩ := hK.unconsV
  obtain ⟨psw, Ks, hsw⟩ := hK.swap
  obtain ⟨pd, Kd, hd⟩ := hK.drop
  refine ⟨HvdH.Cmd.seq (HvdH.Cmd.seq pu psw) pd, Ku + Ks + Kd, ?_⟩
  intro main x L rest hx hLx
  obtain ⟨v, E, rfl⟩ := hx
  have hvsz : HvdH.vsz (Work.MainP.prp v E) = HvdH.isz v + HvdH.vsz (HvdH.ofList E) + 1 := by
    simp [Work.MainP.prp, Work.MainP.vsz_cons, Work.MainP.vsz_int]
  have hEL : HvdH.vsz (HvdH.ofList E) + 1 ≤ L := by
    rw [hvsz] at hLx
    omega
  -- `unconsV`: split the record into its key and its payload.
  have hu1 : HvdH.WordR main pu
      (fun vs => vs = Work.MainP.prp v E :: rest)
      (fun _ out => out = HvdH.Val.int v :: HvdH.ofList E :: rest)
      (fun _ => Ku) := by
    refine Work.Kernel.WordR_conseq (hu main) ?_ ?_ ?_
    · intro vs h
      rw [h]
      exact ⟨.int v, HvdH.ofList E, rest, rfl⟩
    · intro vs out hvs hQ
      obtain ⟨a, b, r, hvs', hout⟩ := hQ
      rw [hvs] at hvs'
      simp only [Work.MainP.prp, List.cons.injEq, HvdH.Val.cons.injEq] at hvs'
      obtain ⟨⟨h1, h2⟩, h3⟩ := hvs'
      rw [← h1, ← h2, ← h3] at hout
      exact hout
    · intro vs _
      exact le_rfl
  -- `swap`: put the payload below the key.
  have hs1 : HvdH.WordR main psw
      (fun vs => vs = HvdH.Val.int v :: HvdH.ofList E :: rest)
      (fun _ out => out = HvdH.ofList E :: HvdH.Val.int v :: rest)
      (fun _ => Ks * (L + 1)) := by
    refine Work.Kernel.WordR_conseq (hsw main) ?_ ?_ ?_
    · intro vs h
      rw [h]
      simp
    · intro vs out hvs hQ
      obtain ⟨a, b, r, hvs', hout⟩ := hQ
      rw [hvs] at hvs'
      simp only [List.cons.injEq] at hvs'
      obtain ⟨h1, h2, h3⟩ := hvs'
      rw [← h1, ← h2, ← h3] at hout
      exact hout
    · intro vs hvs
      rw [hvs]
      simp only [List.getD_cons_zero, List.getD_cons_succ, Work.MainP.vsz_int]
      exact Nat.mul_le_mul_left Ks (by omega)
  -- `drop`: discard the payload.
  have hd1 : HvdH.WordR main pd
      (fun vs => vs = HvdH.ofList E :: HvdH.Val.int v :: rest)
      (fun _ out => out = HvdH.Val.int v :: rest)
      (fun _ => Kd * (L + 1)) := by
    refine Work.Kernel.WordR_conseq (hd main) ?_ ?_ ?_
    · intro vs h
      rw [h]
      exact List.cons_ne_nil _ _
    · intro vs out hvs hQ
      obtain ⟨w, r, hvs', hout⟩ := hQ
      rw [hvs] at hvs'
      simp only [List.cons.injEq] at hvs'
      obtain ⟨_, h2⟩ := hvs'
      rw [← h2] at hout
      exact hout
    · intro vs hvs
      rw [hvs]
      simp only [List.headD_cons]
      exact Nat.mul_le_mul_left Kd (by omega)
  -- compose the three stages
  have h12 : HvdH.WordR main (HvdH.Cmd.seq pu psw)
      (fun vs => vs = Work.MainP.prp v E :: rest)
      (fun _ out => out = HvdH.ofList E :: HvdH.Val.int v :: rest)
      (fun _ => Ku + Ks * (L + 1)) := by
    refine Work.Kernel.WordR_conseq
      (Work.Kernel.WordR_seq (B := fun _ => Ks * (L + 1)) hu1 hs1 ?_) ?_ ?_ ?_
    · intro vs mid _ hmid
      exact ⟨hmid, le_rfl⟩
    · intro vs h
      exact h
    · intro vs out _ hQ
      obtain ⟨mid, hmid, hout⟩ := hQ
      first
        | (subst hmid; exact hout)
        | exact hout
    · intro vs _
      first
        | exact le_rfl
        | exact le_of_eq (by ring)
  have h123 : HvdH.WordR main (HvdH.Cmd.seq (HvdH.Cmd.seq pu psw) pd)
      (fun vs => vs = Work.MainP.prp v E :: rest)
      (fun _ out => out = HvdH.Val.int v :: rest)
      (fun _ => Ku + Ks * (L + 1) + Kd * (L + 1)) := by
    refine Work.Kernel.WordR_conseq
      (Work.Kernel.WordR_seq (B := fun _ => Kd * (L + 1)) h12 hd1 ?_) ?_ ?_ ?_
    · intro vs mid _ hmid
      exact ⟨hmid, le_rfl⟩
    · intro vs h
      exact h
    · intro vs out _ hQ
      obtain ⟨mid, hmid, hout⟩ := hQ
      first
        | (subst hmid; exact hout)
        | exact hout
    · intro vs _
      first
        | exact le_rfl
        | exact le_of_eq (by ring)
  -- final shape of the postcondition
  refine Work.Kernel.WordR_conseq h123 ?_ ?_ ?_
  · intro vs h
    exact h
  · intro vs out _ hQ
    refine ⟨.int v, hQ, ?_, ?_⟩
    · simp [Work.MainP.prp, Work.MainP.pairKey_cons]
    · rw [Work.MainP.vsz_int]
      omega
  · intro vs _
    first
      | exact le_rfl
      | (have he : (Ku + Ks + Kd) * (L + 1) =
            Ku + Ks * (L + 1) + Kd * (L + 1) + Ku * L := by ring
         rw [he]
         omega)

/-- **The epilogue of the CRT labelling word**: a list of records
`p = prp v E` is mapped to the list of the keys `int (pairKey p) = int v`. -/
theorem crtLabEpi (hK : HvdH.KernelLib) (hL : HvdH.LayoutLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (Y : List HvdH.Val) (L : ℕ)
      (rest : List HvdH.Val),
    (∀ p ∈ Y, ∃ (v : ℤ) (E : List HvdH.Val), p = Work.MainP.prp v E) →
    (∀ p ∈ Y, HvdH.vsz p ≤ L) →
    HvdH.WordR main prog
      (fun vs => vs = HvdH.ofList Y :: rest)
      (fun vs out => vs = HvdH.ofList Y :: rest ∧
        out = HvdH.ofList (Y.map fun p => HvdH.Val.int (HvdH.pairKey p)) :: rest)
      (fun _ => K * ((Y.length + 1) * (L + 1) + HvdH.vsz (HvdH.ofList Y) + 1)) := by
  obtain ⟨comb, Km, hmap⟩ := hK.mapList
  obtain ⟨prog1, K1, hone⟩ := crtLabEpiOne hK
  refine ⟨comb prog1, K1 + Km, ?_⟩
  intro main Y L rest hY hLY
  refine Work.Kernel.WordR_conseq
    (hmap main prog1 rest
      (fun x => (∃ (v : ℤ) (E : List HvdH.Val), x = Work.MainP.prp v E) ∧ HvdH.vsz x ≤ L)
      (fun x y => y = HvdH.Val.int (HvdH.pairKey x)) (K1 * (L + 1)) L
      ?_ Y ?_) ?_ ?_ ?_
  · intro x hx
    exact hone main x L rest hx.1 hx.2
  · intro x hx
    exact ⟨⟨hY x hx, hLY x hx⟩, hLY x hx⟩
  · intro vs h
    exact h
  · intro vs out hvs hQ
    obtain ⟨ys, hout, hfa⟩ := hQ
    exact ⟨hvs, by rw [hout, forall2MapEq hfa]⟩
  · intro vs _
    have h1 : Y.length * (K1 * (L + 1) + Km * (L + 1)) + Km ≤
        (K1 + Km) * (Y.length * (L + 1)) + (K1 + Km) * (L + 1) := by
      have he : Y.length * (K1 * (L + 1) + Km * (L + 1)) =
          (K1 + Km) * (Y.length * (L + 1)) := by ring
      rw [he]
      have hKm : Km ≤ (K1 + Km) * (L + 1) := by
        calc Km = Km * 1 := (Nat.mul_one Km).symm
          _ ≤ Km * (L + 1) := Nat.mul_le_mul_left Km (Nat.le_add_left 1 L)
          _ ≤ (K1 + Km) * (L + 1) := Nat.mul_le_mul_right (L + 1) (Nat.le_add_left Km K1)
      exact Nat.add_le_add_left hKm _
    calc Y.length * (K1 * (L + 1) + Km * (L + 1)) + Km
        ≤ (K1 + Km) * (Y.length * (L + 1)) + (K1 + Km) * (L + 1) := h1
      _ = (K1 + Km) * ((Y.length + 1) * (L + 1)) := by ring
      _ ≤ (K1 + Km) * ((Y.length + 1) * (L + 1) + HvdH.vsz (HvdH.ofList Y) + 1) :=
          Nat.mul_le_mul_left _ (by omega)

end Work.MainP
