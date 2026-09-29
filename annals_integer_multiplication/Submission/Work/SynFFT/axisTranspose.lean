import Mathlib
import Submission.Work.SynFFT.axisDefs
import Submission.Work.SynFFT.axisKit
import Submission.Work.SynFFT.mrgBlkDefs
import Submission.Work.SynFFT.axisMergeMath
import Submission.Work.SynFFT.axisSlices
import Submission.Work.Resample.chunkWordPB
import Submission.Work.SynFFT.axisLeaf
import Submission.Work.SynFFT.axisMerge
import Submission.Work.SynFFT.axisSizes
import Submission.Work.Kernel.kernelLib
import Submission.Work.SynFFT.axFlatten
import Submission.Work.IntLib.mulSWord

/-!
# The layout-transpose word `Work.SynFFT.HasAxisTranspose` (assembly)

Assembled from `axisChunks` (block splitting), `axisLeaf` (block -> groups of singleton columns),
`axisMerge` (iterated pairwise merge), the pure lemmas `axisMergeMath` / `axisSlices`, and the
`KernelLib` / `LayoutLib.flatten` words.  This file holds the assembly.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.SynFFT

open HvdH

local infixl:68 " ;;; " => HvdH.Cmd.seq

/-- Size of the four values involved in the parameter shuffles. -/
def vol (E : Val) (A t B : ℕ) : ℕ := vsz E + isz (A : ℤ) + isz (t : ℤ) + isz (B : ℤ) + 1

/-- The list after `roll k`: the `k`-th entry moved to the front. -/
def rot (k : ℕ) (l : List Val) : List Val := l.getD k .nil :: l.eraseIdx k

theorem rot_eq (k : ℕ) (l : List Val) : rot k l = l.getD k .nil :: l.eraseIdx k := rfl

theorem rot332 (E : Val) (A t B : ℕ) (rest : List Val) :
    rot 2 (rot 3 (rot 3 (E :: .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: rest)))
      = E :: .int (t : ℤ) :: .int (B : ℤ) :: .int (A : ℤ) :: rest := by
  simp [rot, List.eraseIdx_eq_take_drop_succ]

theorem rot31 (X : Val) (A t B : ℕ) (rest : List Val) :
    rot 1 (rot 3 (X :: .int (t : ℤ) :: .int (B : ℤ) :: .int (A : ℤ) :: rest))
      = X :: .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: rest := by
  simp [rot, List.eraseIdx_eq_take_drop_succ]

/-- Window bound: a sublist of the four shuffle values has weighted length at most `6 * vol`. -/
theorem window_le_vol (v : List Val) (E : Val) (A t B : ℕ) (hlen : v.length ≤ 6)
    (h : ∀ x ∈ v, x ∈ ([E, .int (A : ℤ), .int (t : ℤ), .int (B : ℤ)] : List Val)) :
    (v.map vsz).sum ≤ 6 * vol E A t B := by
  have hbound : ∀ x ∈ v, vsz x ≤ vsz E + isz (A : ℤ) + isz (t : ℤ) + isz (B : ℤ) := by
    intro x hx
    have hx' := h x hx
    rcases List.mem_cons.mp hx' with h1 | h2
    · rw [h1]; omega
    rcases List.mem_cons.mp h2 with h1 | h2
    · rw [h1, MrgKit.vsz_int']; omega
    rcases List.mem_cons.mp h2 with h1 | h2
    · rw [h1, MrgKit.vsz_int']; omega
    rcases List.mem_cons.mp h2 with h1 | h2
    · rw [h1, MrgKit.vsz_int']; omega
    · simp at h2
  have hsum := MrgKit.sum_le_of_forall vsz v (vsz E + isz (A : ℤ) + isz (t : ℤ) + isz (B : ℤ)) hbound
  unfold vol
  nlinarith

/-- `E :: int A :: int t :: int B :: rest ↦ int (t*B) :: E :: int A :: int t :: int B :: rest`:
compute the block size `t*B` (two copies, then the schoolbook product). -/
theorem prelude_mkS {main : Cmd} {pickP : ℕ → Cmd} {mulP : Cmd} {Kp Km D : ℕ}
    (hpick : ∀ k, WordR main (pickP k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs)
      (fun vs => Kp * (k+1) * (((vs.take (k+1)).map vsz).sum + 1)))
    (hmul : BinOp main mulP (fun _ _ => True) (· * ·) (fun a b => Km * isz a * isz b))
    (E : Val) (A t B : ℕ) (rest : List Val)
    (hD : Kp * 3 * (((E :: .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: rest).take 3).map vsz).sum
            + Kp * 3
          + (Kp * 5 * (((.int (t : ℤ) :: E :: .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: rest).take 5).map vsz).sum
            + Kp * 5)
          + Km * isz (B : ℤ) * isz (t : ℤ) ≤ D) :
    WordR main (pickP 2 ;;; pickP 4 ;;; mulP)
      (fun vs => vs = E :: .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: rest)
      (fun _ out => out = .int ((t * B : ℕ) : ℤ) :: E :: .int (A : ℤ) :: .int (t : ℤ) ::
        .int (B : ℤ) :: rest)
      (fun _ => D) := by
  have hlen0 : 2 < (E :: .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: rest).length := by simp
  have hlen1 : 4 < (.int (t : ℤ) :: E :: .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: rest).length :=
    by simp
  have h1 := MrgKit.pickStep hpick 2 (E :: .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: rest)
    hlen0 (Kp * 3 * (((E :: .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: rest).take 3).map vsz).sum
      + Kp * 3) le_rfl
  have h2 := MrgKit.pickStep hpick 4
    (.int (t : ℤ) :: E :: .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: rest) hlen1
    (Kp * 5 * (((.int (t : ℤ) :: E :: .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: rest).take 5).map vsz).sum
      + Kp * 5) le_rfl
  have h3 := MrgKit.mulStep hmul (B : ℤ) (t : ℤ)
    (E :: .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: rest)
    (Km * isz (B : ℤ) * isz (t : ℤ)) le_rfl
  have h12 := MrgKit.WordR_seqC h1 h2
  have h123 := MrgKit.WordR_seqC h12 h3
  refine MrgKit.WordR_weaken h123 ?_ ?_ ?_
  · intro vs hv; rw [hv]
  · intro vs out hv hq
    rw [hq]
    have hmul' : (B : ℤ) * (t : ℤ) = ((t * B : ℕ) : ℤ) := by push_cast; ring
    rw [hmul']
  · intro vs hv; exact hD

/-- `E :: int A :: int t :: int B :: rest ↦ E :: int t :: int B :: int A :: rest`. -/
theorem prelude_reorderFwd {main : Cmd} {rollP : ℕ → Cmd} {Kr D : ℕ}
    (hroll : ∀ k, WordR main (rollP k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs.eraseIdx k)
      (fun vs => Kr * (k+1) * (((vs.take (k+1)).map vsz).sum + 1)))
    (E : Val) (A t B : ℕ) (rest : List Val)
    (hD : Kr * 4 * (((E :: .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: rest).take 4).map vsz).sum + Kr * 4
        + (Kr * 4 * (((.int (B : ℤ) :: E :: .int (A : ℤ) :: .int (t : ℤ) :: rest).take 4).map vsz).sum + Kr * 4)
        + (Kr * 3 * (((.int (t : ℤ) :: .int (B : ℤ) :: E :: .int (A : ℤ) :: rest).take 3).map vsz).sum + Kr * 3)
        ≤ D) :
    WordR main (rollP 3 ;;; rollP 3 ;;; rollP 2)
      (fun vs => vs = E :: .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: rest)
      (fun _ out => out = E :: .int (t : ℤ) :: .int (B : ℤ) :: .int (A : ℤ) :: rest)
      (fun _ => D) := by
  have hlen0 : 3 < (E :: .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: rest).length := by simp
  have hlen1 : 3 < (.int (B : ℤ) :: E :: .int (A : ℤ) :: .int (t : ℤ) :: rest).length := by simp
  have hlen2 : 2 < (.int (t : ℤ) :: .int (B : ℤ) :: E :: .int (A : ℤ) :: rest).length := by simp
  have h1 := MrgKit.rollStep hroll 3 (E :: .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: rest) hlen0
    (Kr * 4 * (((E :: .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: rest).take 4).map vsz).sum + Kr * 4)
    le_rfl
  have h2 := MrgKit.rollStep hroll 3
    (.int (B : ℤ) :: E :: .int (A : ℤ) :: .int (t : ℤ) :: rest) hlen1
    (Kr * 4 * (((.int (B : ℤ) :: E :: .int (A : ℤ) :: .int (t : ℤ) :: rest).take 4).map vsz).sum + Kr * 4)
    le_rfl
  have h3 := MrgKit.rollStep hroll 2
    (.int (t : ℤ) :: .int (B : ℤ) :: E :: .int (A : ℤ) :: rest) hlen2
    (Kr * 3 * (((.int (t : ℤ) :: .int (B : ℤ) :: E :: .int (A : ℤ) :: rest).take 3).map vsz).sum + Kr * 3)
    le_rfl
  have h12 := MrgKit.WordR_seqC h1 h2
  have h123 := MrgKit.WordR_seqC h12 h3
  refine MrgKit.WordR_weaken h123 ?_ ?_ ?_
  · intro vs hv; rw [hv]
  · intro vs out hv hq
    rw [hq]
    exact rot332 E A t B rest
  · intro vs hv; exact hD

/-- `X :: int t :: int B :: int A :: rest ↦ X :: int A :: int t :: int B :: rest`. -/
theorem prelude_reorderBack {main : Cmd} {rollP : ℕ → Cmd} {Kr D : ℕ}
    (hroll : ∀ k, WordR main (rollP k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs.eraseIdx k)
      (fun vs => Kr * (k+1) * (((vs.take (k+1)).map vsz).sum + 1)))
    (X : Val) (A t B : ℕ) (rest : List Val)
    (hD : Kr * 4 * (((X :: .int (t : ℤ) :: .int (B : ℤ) :: .int (A : ℤ) :: rest).take 4).map vsz).sum + Kr * 4
        + (Kr * 2 * (((.int (A : ℤ) :: X :: .int (t : ℤ) :: .int (B : ℤ) :: rest).take 2).map vsz).sum + Kr * 2)
        ≤ D) :
    WordR main (rollP 3 ;;; rollP 1)
      (fun vs => vs = X :: .int (t : ℤ) :: .int (B : ℤ) :: .int (A : ℤ) :: rest)
      (fun _ out => out = X :: .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: rest)
      (fun _ => D) := by
  have hlen0 : 3 < (X :: .int (t : ℤ) :: .int (B : ℤ) :: .int (A : ℤ) :: rest).length := by simp
  have hlen1 : 1 < (.int (A : ℤ) :: X :: .int (t : ℤ) :: .int (B : ℤ) :: rest).length := by simp
  have h1 := MrgKit.rollStep hroll 3 (X :: .int (t : ℤ) :: .int (B : ℤ) :: .int (A : ℤ) :: rest) hlen0
    (Kr * 4 * (((X :: .int (t : ℤ) :: .int (B : ℤ) :: .int (A : ℤ) :: rest).take 4).map vsz).sum + Kr * 4)
    le_rfl
  have h2 := MrgKit.rollStep hroll 1
    (.int (A : ℤ) :: X :: .int (t : ℤ) :: .int (B : ℤ) :: rest) hlen1
    (Kr * 2 * (((.int (A : ℤ) :: X :: .int (t : ℤ) :: .int (B : ℤ) :: rest).take 2).map vsz).sum + Kr * 2)
    le_rfl
  have h12 := MrgKit.WordR_seqC h1 h2
  refine MrgKit.WordR_weaken h12 ?_ ?_ ?_
  · intro vs hv; rw [hv]
  · intro vs out hv hq
    rw [hq]
    exact rot31 X A t B rest
  · intro vs hv; exact hD

/-! ## Empty branch and flatten bookkeeping -/

/-- Flattening is compatible with a `map`: flattening twice is flattening each image once. -/
theorem flatten_flatten_map {α : Type} (l : List α) (f : α → List (List Val)) :
    ((l.map f).flatten).flatten = (l.map (fun x => (f x).flatten)).flatten := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      simp only [List.map_cons, List.flatten_cons, List.flatten_append, ih]

/-- The slices of the empty array are empty. -/
theorem slices_nil (A t B : ℕ) (h : A * t * B = 0) :
    List.flatten (HvdH.slices A t B ([] : List Val)) = [] := by
  rcases Nat.mul_eq_zero.mp h with h1 | h1
  · rcases Nat.mul_eq_zero.mp h1 with h2 | h2
    · subst h2; simp [HvdH.slices]
    · subst h2; simp [HvdH.slices]
  · subst h1; simp [HvdH.slices]

/-- The empty branch of the transpose word: nothing to do but put `nil` back. -/
theorem emptyBranch {main : Cmd} {pushP : Val → Cmd} {Kpv D : ℕ}
    (hpush : ∀ v, WordR main (pushP v) (fun _ => True) (fun vs out => out = v :: vs)
      (fun _ => Kpv * (vsz v + 1)))
    (A t B : ℕ) (h : A * t * B = 0) (rest : List Val) (hD : Kpv * (vsz Val.nil + 1) ≤ D) :
    WordR main (pushP Val.nil) (fun vs => vs = rest)
      (fun _ out => out = HvdH.ofList (List.flatten (HvdH.slices A t B ([] : List Val))) :: rest)
      (fun _ => D) := by
  refine MrgKit.WordR_weaken (MrgKit.pushStep hpush Val.nil rest D hD) ?_ ?_ ?_
  · intro vs hv; rw [hv]
  · intro vs out hv hq
    rw [hq, slices_nil A t B h]
    rfl
  · intro vs hv; exact le_rfl

/-! ## Injectivity of the list encodings -/

theorem ofList_inj : ∀ {l l' : List Val}, ofList l = ofList l' → l = l'
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: t, b :: t', h => by
      have h' : Val.cons a (ofList t) = Val.cons b (ofList t') := h
      injection h' with h1 h2
      rw [h1, ofList_inj h2]

theorem map_ofList_inj : ∀ {l l' : List (List Val)}, l.map ofList = l'.map ofList → l = l'
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: t, b :: t', h => by
      have h' : ofList a :: t.map ofList = ofList b :: t'.map ofList := h
      injection h' with h1 h2
      rw [ofList_inj h1, map_ofList_inj h2]

theorem grpVal_inj {g g' : List (List Val)} (h : grpVal g = grpVal g') : g = g' :=
  map_ofList_inj (ofList_inj h)

theorem stateVal_inj : ∀ {gs gs' : List (List (List Val))}, stateVal gs = stateVal gs' → gs = gs'
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [stateVal, grpVal, ofList] at h
  | _ :: _, [], h => by simp [stateVal, grpVal, ofList] at h
  | a :: t, b :: t', h => by
      have h' : Val.cons (grpVal a) (stateVal t) = Val.cons (grpVal b) (stateVal t') := h
      injection h' with h1 h2
      rw [grpVal_inj h1, stateVal_inj h2]

/-! ## The two block phases (instantiated from the per-block words) -/

/-- `Forall₂` over a `map ofList` determines the result list. -/
theorem forall₂_map_ofList {blks : List (List Val)} {ys : List Val} {f : List Val → Val}
    (h : List.Forall₂ (fun x y => ∃ blk, x = ofList blk ∧ y = f blk)
      (blks.map ofList) ys) : ys = blks.map f := by
  induction blks generalizing ys with
  | nil => cases h with | nil => rfl
  | cons a t ih =>
      cases h with
      | cons hab htail =>
        obtain ⟨bl, hx, hy⟩ := hab
        have h1 : a = bl := ofList_inj hx
        rw [← h1] at hy
        simp only [List.map_cons, hy, ih htail]

/-- `Forall₂` over a `map stateVal` determines the result list. -/
theorem forall₂_map_stateVal {Gss : List (List (List (List Val)))} {ys : List Val}
    (h : List.Forall₂ (fun x y => ∃ Gs, x = stateVal Gs ∧ y = stateVal (mAll Gs))
      (Gss.map stateVal) ys) : ys = Gss.map (fun Gs => stateVal (mAll Gs)) := by
  induction Gss generalizing ys with
  | nil => cases h with | nil => rfl
  | cons a t ih =>
      cases h with
      | cons hab htail =>
        obtain ⟨Gs, hx, hy⟩ := hab
        have h1 : Gs = a := (stateVal_inj hx).symm
        rw [h1] at hy
        simp only [List.map_cons, hy, ih htail]

/-- The leaf phase: apply the leaf word to every block of the array. -/
theorem leafPhase {leafP : Cmd} {Kleaf : ℕ}
    (hleaf : ∀ (main : Cmd) (t B : ℕ) (blk : List Val) (rest : List Val),
      blk.length = t * B → 1 ≤ t → 1 ≤ B →
      WordR main leafP (fun vs => vs = ofList blk :: .int (t : ℤ) :: .int (B : ℤ) :: rest)
        (fun _ out => out = stateVal ((rowsOf t B blk).map exploded) ::
          .int (t : ℤ) :: .int (B : ℤ) :: rest)
        (fun _ => Kleaf * (vsz (ofList blk) + 1) +
          Kleaf * ((blk.length + t + 1) * (isz (B : ℤ) + 1) + 1))) :
    ∃ (comb : Cmd → Cmd) (Kml : ℕ), ∀ (main : Cmd) (blks : List (List Val)) (t B : ℕ)
      (rest : List Val) (c Lmap : ℕ),
      (∀ blk ∈ blks, blk.length = t * B) → 1 ≤ t → 1 ≤ B →
      (∀ blk ∈ blks, vsz (ofList blk) ≤ Lmap) →
      (∀ blk ∈ blks, vsz (stateVal ((rowsOf t B blk).map exploded)) ≤ Lmap) →
      (∀ blk ∈ blks, Kleaf * (vsz (ofList blk) + 1) +
          Kleaf * ((blk.length + t + 1) * (isz (B : ℤ) + 1) + 1) ≤ c) →
      WordR main (comb leafP)
        (fun vs => vs = ofList (blks.map ofList) :: .int (t : ℤ) :: .int (B : ℤ) :: rest)
        (fun _ out => out = ofList (blks.map (fun blk => stateVal ((rowsOf t B blk).map exploded))) ::
          .int (t : ℤ) :: .int (B : ℤ) :: rest)
        (fun _ => blks.length * (c + Kml * (Lmap + 1)) + Kml) := by
  obtain ⟨comb, Kml, hmap⟩ := Work.Kernel.mapList
  refine ⟨comb, Kml, ?_⟩
  intro main blks t B rest c Lmap hlen ht hB hL1 hL2 hc
  have hword : ∀ x, (∃ blk ∈ blks, x = ofList blk ∧ blk.length = t * B) → WordR main leafP
      (fun vs => vs = x :: .int (t : ℤ) :: .int (B : ℤ) :: rest)
      (fun _ out => ∃ y, out = y :: .int (t : ℤ) :: .int (B : ℤ) :: rest ∧
        (∃ blk, x = ofList blk ∧ y = stateVal ((rowsOf t B blk).map exploded)) ∧ vsz y ≤ Lmap)
      (fun _ => c) := by
    intro x hx
    obtain ⟨blk, hblk_mem, rfl, hblk⟩ := hx
    refine MrgKit.WordR_weaken (hleaf main t B blk rest hblk ht hB) ?_ ?_ ?_
    · intro vs hv; rw [hv]
    · intro vs out hv hq
      rw [hq]
      exact ⟨_, rfl, ⟨blk, rfl, rfl⟩, hL2 blk hblk_mem⟩
    · intro vs hv; exact hc blk hblk_mem
  have hxs : ∀ x ∈ blks.map ofList,
      (∃ blk ∈ blks, x = ofList blk ∧ blk.length = t * B) ∧ vsz x ≤ Lmap := by
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨blk, hblk, rfl⟩ := hx
    exact ⟨⟨blk, hblk, rfl, hlen blk hblk⟩, hL1 blk hblk⟩
  have hmain := hmap main leafP (.int (t : ℤ) :: .int (B : ℤ) :: rest)
    (fun x => ∃ blk ∈ blks, x = ofList blk ∧ blk.length = t * B)
    (fun x y => ∃ blk, x = ofList blk ∧ y = stateVal ((rowsOf t B blk).map exploded))
    c Lmap hword (blks.map ofList) hxs
  refine MrgKit.WordR_weaken hmain ?_ ?_ ?_
  · intro vs hv; rw [hv]
  · intro vs out hv hq
    obtain ⟨ys, hout, hforall⟩ := hq
    rw [hout, forall₂_map_ofList hforall]
  · intro vs hv; simp [List.length_map]

/-- The merge phase: apply the merge word to every block of the array. -/
theorem mergePhase {mrgP : Cmd} {Kmrg : ℕ}
    (hmrg : ∀ (main : Cmd) (Gs : List (List (List Val))) (rest : List Val),
      WordR main mrgP (fun vs => vs = stateVal Gs :: rest)
        (fun _ out => out = stateVal (mAll Gs) :: rest)
        (fun _ => Kmrg * (vsz (stateVal Gs) + 1) * (Gs.length.size + 1) + Kmrg)) :
    ∃ (comb : Cmd → Cmd) (Kml : ℕ), ∀ (main : Cmd) (Gss : List (List (List (List Val)))) (t : ℕ)
      (rest : List Val) (c Lmap : ℕ),
      (∀ Gs ∈ Gss, Gs.length = t) →
      (∀ Gs ∈ Gss, vsz (stateVal Gs) ≤ Lmap) →
      (∀ Gs ∈ Gss, vsz (stateVal (mAll Gs)) ≤ Lmap) →
      (∀ Gs ∈ Gss, Kmrg * (vsz (stateVal Gs) + 1) * (t.size + 1) + Kmrg ≤ c) →
      WordR main (comb mrgP)
        (fun vs => vs = ofList (Gss.map stateVal) :: rest)
        (fun _ out => out = ofList (Gss.map (fun Gs => stateVal (mAll Gs))) :: rest)
        (fun _ => Gss.length * (c + Kml * (Lmap + 1)) + Kml) := by
  obtain ⟨comb, Kml, hmap⟩ := Work.Kernel.mapList
  refine ⟨comb, Kml, ?_⟩
  intro main Gss t rest c Lmap hlen hL1 hL2 hc
  have hword : ∀ x, (∃ Gs ∈ Gss, x = stateVal Gs ∧ Gs.length = t) → WordR main mrgP
      (fun vs => vs = x :: rest)
      (fun _ out => ∃ y, out = y :: rest ∧
        (∃ Gs, x = stateVal Gs ∧ y = stateVal (mAll Gs)) ∧ vsz y ≤ Lmap)
      (fun _ => c) := by
    intro x hx
    obtain ⟨Gs, hGs_mem, rfl, hGs⟩ := hx
    refine MrgKit.WordR_weaken (hmrg main Gs rest) ?_ ?_ ?_
    · intro vs hv; rw [hv]
    · intro vs out hv hq
      rw [hq]
      exact ⟨_, rfl, ⟨Gs, rfl, rfl⟩, hL2 Gs hGs_mem⟩
    · intro vs hv
      show Kmrg * (vsz (stateVal Gs) + 1) * (Gs.length.size + 1) + Kmrg ≤ c
      rw [hGs]
      exact hc Gs hGs_mem
  have hxs : ∀ x ∈ Gss.map stateVal,
      (∃ Gs ∈ Gss, x = stateVal Gs ∧ Gs.length = t) ∧ vsz x ≤ Lmap := by
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨Gs, hGs, rfl⟩ := hx
    exact ⟨⟨Gs, hGs, rfl, hlen Gs hGs⟩, hL1 Gs hGs⟩
  have hmain := hmap main mrgP rest (fun x => ∃ Gs ∈ Gss, x = stateVal Gs ∧ Gs.length = t)
    (fun x y => ∃ Gs, x = stateVal Gs ∧ y = stateVal (mAll Gs))
    c Lmap hword (Gss.map stateVal) hxs
  refine MrgKit.WordR_weaken hmain ?_ ?_ ?_
  · intro vs hv; rw [hv]
  · intro vs out hv hq
    obtain ⟨ys, hout, hforall⟩ := hq
    rw [hout, forall₂_map_stateVal hforall]
  · intro vs hv; simp [List.length_map]

/-! ## The two target monomials and their elementary bounds -/

theorem vsz_ofList_le2 {L : ℕ} {xs : List Val} (h : ∀ x ∈ xs, vsz x ≤ L) :
    vsz (ofList xs) ≤ xs.length * (L + 1) + 1 := by
  have h1 : (xs.map vsz).sum ≤ xs.length * L := MrgKit.sum_le_of_forall vsz xs L h
  have h2 : vsz (ofList xs) = xs.length + (xs.map vsz).sum + 1 := MrgKit.vsz_ofList xs
  have h3 : xs.length * (L + 1) = xs.length * L + xs.length := by ring
  omega

def tgtX (A t B L : ℕ) : ℕ := A * t * B * (L + 1) * ((t).size + 1)

def tgtY (A t B : ℕ) : ℕ := A * t * B * ((A * t * B).size + 1)

def tgtV (A t B L : ℕ) : ℕ := A * (t * B * (L + 1) + 3 * (t * B) + t + 3) + 1

theorem le_tgtX_self (A t B L : ℕ) : A * t * B * (L + 1) ≤ tgtX A t B L := by
  rw [tgtX]
  calc A * t * B * (L + 1) = A * t * B * (L + 1) * 1 := by ring
    _ ≤ A * t * B * (L + 1) * (t.size + 1) := Nat.mul_le_mul_left _ (Nat.le_add_left 1 _)

theorem le_tgtY_size (A t B : ℕ) (h : 1 ≤ A * t * B) : (A * t * B).size + 1 ≤ tgtY A t B := by
  rw [tgtY]
  calc (A * t * B).size + 1 = ((A * t * B).size + 1) * 1 := by ring
    _ ≤ ((A * t * B).size + 1) * (A * t * B) := Nat.mul_le_mul_left _ h
    _ = A * t * B * ((A * t * B).size + 1) := by ring

theorem one_le_AtB (A t B : ℕ) (hA : 1 ≤ A) (ht : 1 ≤ t) (hB : 1 ≤ B) : 1 ≤ A * t * B := by
  have h1 : 0 < A := by omega
  have h2 : 0 < t := by omega
  have h3 : 0 < B := by omega
  have h4 : 0 < A * t * B := Nat.mul_pos (Nat.mul_pos h1 h2) h3
  omega

theorem vsz_ofList_le_tgtX (A t B L : ℕ) (es : List Val) (hlen : es.length = A * t * B)
    (hL : ∀ x ∈ es, vsz x ≤ L) :
    vsz (ofList es) ≤ tgtX A t B L + tgtY A t B + 1 := by
  have h1 : vsz (ofList es) ≤ A * t * B * (L + 1) + 1 := by
    have h2 := vsz_ofList_le2 hL
    rw [hlen] at h2
    exact h2
  have h3 := le_tgtX_self A t B L
  omega

/-- Bound for `isz` of a parameter: at most `2*tgtY + 2`. -/
theorem isz_le_tgtY (A t B : ℕ) (hA : 1 ≤ A) (ht : 1 ≤ t) (hB : 1 ≤ B) {m : ℕ}
    (hm : m ≤ A * t * B) : isz (m : ℤ) ≤ 2 * tgtY A t B + 2 := by
  have hN : 1 ≤ A * t * B := one_le_AtB A t B hA ht hB
  have h1 : ((m : ℤ)).natAbs = m := Int.natAbs_natCast m
  have h2 : isz (m : ℤ) = m.size + 2 := by simp only [isz, h1]
  have h3 : m.size ≤ (A * t * B).size := Nat.size_le_size hm
  have h4 := le_tgtY_size A t B hN
  omega

theorem isz_mul_le_tgtY (A t B : ℕ) (hA : 1 ≤ A) (ht : 1 ≤ t) (hB : 1 ≤ B) {m n : ℕ}
    (hm : m ≤ A * t * B) (hn : n ≤ A * t * B) : isz (m : ℤ) * isz (n : ℤ) ≤ 8 * tgtY A t B := by
  have hN : 1 ≤ A * t * B := one_le_AtB A t B hA ht hB
  have h1 : ((m : ℤ)).natAbs = m := Int.natAbs_natCast m
  have h2 : ((n : ℤ)).natAbs = n := Int.natAbs_natCast n
  have h3 : isz (m : ℤ) = m.size + 2 := by simp only [isz, h1]
  have h4 : isz (n : ℤ) = n.size + 2 := by simp only [isz, h2]
  have h5 : m.size ≤ (A * t * B).size := Nat.size_le_size hm
  have h6 : n.size ≤ (A * t * B).size := Nat.size_le_size hn
  have h7 : (A * t * B).size + 2 ≤ 2 * ((A * t * B).size + 1) := by omega
  have h8 : (A * t * B).size + 1 ≤ 2 * (A * t * B) := by
    have h9 : (A * t * B).size ≤ A * t * B := Nat.size_le.mpr (Nat.lt_two_pow_self (n := A * t * B))
    omega
  rw [h3, h4]
  have h10 : (m.size + 2) * (n.size + 2) ≤ ((A * t * B).size + 2) * ((A * t * B).size + 2) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h11 : ((A * t * B).size + 2) * ((A * t * B).size + 2) ≤
      4 * ((A * t * B).size + 1) * ((A * t * B).size + 1) := by
    nlinarith [h7]
  have h12 : ((A * t * B).size + 1) * ((A * t * B).size + 1) ≤
      ((A * t * B).size + 1) * (2 * (A * t * B)) :=
    Nat.mul_le_mul_left _ (by omega)
  have h13 : 4 * (((A * t * B).size + 1) * (2 * (A * t * B))) ≤ 8 * tgtY A t B := by
    rw [tgtY]
    nlinarith
  calc (m.size + 2) * (n.size + 2) ≤ ((A * t * B).size + 2) * ((A * t * B).size + 2) := h10
    _ ≤ 4 * ((A * t * B).size + 1) * ((A * t * B).size + 1) := h11
    _ = 4 * (((A * t * B).size + 1) * ((A * t * B).size + 1)) := by ring
    _ ≤ 4 * (((A * t * B).size + 1) * (2 * (A * t * B))) := by
        exact Nat.mul_le_mul_left 4 h12
    _ ≤ 8 * tgtY A t B := h13

theorem tgtV_le (A t B L : ℕ) (hA : 1 ≤ A) (ht : 1 ≤ t) (hB : 1 ≤ B) :
    tgtV A t B L ≤ 8 * tgtX A t B L + 1 := by
  have hN : 1 ≤ A * t * B := one_le_AtB A t B hA ht hB
  have h1 : A * (t * B * (L + 1)) ≤ tgtX A t B L := by
    have he : A * (t * B * (L + 1)) = A * t * B * (L + 1) := by ring
    rw [he]
    exact le_tgtX_self A t B L
  have h2 : A * (3 * (t * B) + t + 3) ≤ 7 * tgtX A t B L := by
    have htB : t * B ≤ A * t * B := by
      have h : t * B ≤ A * (t * B) := Nat.le_mul_of_pos_left (t * B) (by omega : 0 < A)
      rwa [← mul_assoc] at h
    have ht1 : t ≤ A * t * B := by
      have h : t ≤ t * B := Nat.le_mul_of_pos_right t (by omega : 0 < B)
      exact le_trans h htB
    have hA1 : A ≤ A * t * B := by
      have h : A ≤ A * (t * B) :=
        Nat.le_mul_of_pos_right A (Nat.mul_pos (by omega) (by omega))
      rwa [← mul_assoc] at h
    have heq : A * (3 * (t * B) + t + 3) = 3 * (A * t * B) + A * t + 3 * A := by ring
    have h7 : A * (3 * (t * B) + t + 3) ≤ 7 * (A * t * B) := by
      rw [heq]; nlinarith
    have hNL : A * t * B ≤ A * t * B * (L + 1) := by
      calc A * t * B = A * t * B * 1 := by ring
        _ ≤ A * t * B * (L + 1) := Nat.mul_le_mul_left _ (by omega)
    have h7' : 7 * (A * t * B) ≤ 7 * tgtX A t B L := by
      refine Nat.mul_le_mul_left 7 ?_
      exact le_trans hNL (le_tgtX_self A t B L)
    exact le_trans h7 h7'
  have hdist : A * (t * B * (L + 1) + 3 * (t * B) + t + 3) =
      A * (t * B * (L + 1)) + A * (3 * (t * B) + t + 3) := by ring
  rw [tgtV, hdist]
  omega

/-! ## Cost arithmetic for the assembly

The uniform per-step budget is `bd Cs A t B L = Cs*(tgtX + tgtY + 1)`, i.e. a fixed multiple of the
target cost of `HasAxisTranspose`.  Every step of the main word is charged this budget, and the
arithmetic lemmas below are what each step needs to justify its charge. -/

/-- The uniform per-step budget. -/
def bd (Cs A t B L : ℕ) : ℕ := Cs * (tgtX A t B L + tgtY A t B + 1)

theorem isz_add_one_le {N m : ℕ} (hm : m ≤ N) : isz (m : ℤ) + 1 ≤ N.size + 3 := by
  have h1 : ((m : ℤ)).natAbs = m := Int.natAbs_natCast m
  have h2 : isz (m : ℤ) = m.size + 2 := by simp only [isz, h1]
  have h3 : m.size ≤ N.size := Nat.size_le_size hm
  omega

theorem isz_le_size_add {N m : ℕ} (hm : m ≤ N) : isz (m : ℤ) ≤ N.size + 2 := by
  have h1 : ((m : ℤ)).natAbs = m := Int.natAbs_natCast m
  have h2 : isz (m : ℤ) = m.size + 2 := by simp only [isz, h1]
  have h3 : m.size ≤ N.size := Nat.size_le_size hm
  omega

theorem N_le_tgtX (A t B L : ℕ) : A * t * B ≤ tgtX A t B L := by
  rw [tgtX]
  have h : A * t * B * 1 * 1 ≤ A * t * B * (L + 1) * (t.size + 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  simpa using h

theorem N_le_tgtY (A t B : ℕ) : A * t * B ≤ tgtY A t B := by
  rw [tgtY]
  exact Nat.le_mul_of_pos_right _ (by omega)

theorem size_add3_le {A t B : ℕ} (hN : 1 ≤ A * t * B) :
    (A * t * B).size + 3 ≤ 3 * (tgtY A t B + 1) := by
  have h1 : (A * t * B).size + 1 ≤ tgtY A t B := le_tgtY_size A t B hN
  omega

theorem N_mul_isz_le (A t B : ℕ) {m : ℕ} (hm : m ≤ A * t * B) :
    (A * t * B) * (isz (m : ℤ) + 1) ≤ tgtY A t B + 2 * (A * t * B) := by
  have h1 : isz (m : ℤ) ≤ (A * t * B).size + 2 := isz_le_size_add hm
  rw [tgtY]
  nlinarith

theorem le_N_of_le_tB (A t B : ℕ) (hA : 1 ≤ A) (hB : 1 ≤ B) : t * B ≤ A * t * B := by
  have h : t * B ≤ A * (t * B) := Nat.le_mul_of_pos_left (t * B) (by omega)
  rwa [← mul_assoc] at h

theorem le_N_A (A t B : ℕ) (ht : 1 ≤ t) (hB : 1 ≤ B) : A ≤ A * t * B := by
  have h : A ≤ A * (t * B) := Nat.le_mul_of_pos_right A (Nat.mul_pos (by omega) (by omega))
  rwa [← mul_assoc] at h

theorem le_N_t (A t B : ℕ) (hA : 1 ≤ A) (hB : 1 ≤ B) : t ≤ A * t * B :=
  le_trans (Nat.le_mul_of_pos_right t (by omega)) (le_N_of_le_tB A t B hA hB)

theorem le_N_B (A t B : ℕ) (hA : 1 ≤ A) (ht : 1 ≤ t) (hB : 1 ≤ B) : B ≤ A * t * B :=
  le_trans (Nat.le_mul_of_pos_left B (by omega)) (le_N_of_le_tB A t B hA hB)

theorem vol_le_tgt11 (A t B L : ℕ) (es : List Val) (hlen : es.length = A * t * B)
    (hA : 1 ≤ A) (ht : 1 ≤ t) (hB : 1 ≤ B) (hL : ∀ x ∈ es, vsz x ≤ L) :
    vol (ofList es) A t B ≤ 11 * (tgtX A t B L + tgtY A t B + 1) := by
  have hN1 : 1 ≤ A * t * B := one_le_AtB A t B hA ht hB
  have h1 : isz (A : ℤ) ≤ (A * t * B).size + 2 := isz_le_size_add (le_N_A A t B ht hB)
  have h2 : isz (t : ℤ) ≤ (A * t * B).size + 2 := isz_le_size_add (le_N_t A t B hA hB)
  have h3 : isz (B : ℤ) ≤ (A * t * B).size + 2 := isz_le_size_add (le_N_B A t B hA ht hB)
  have h4 : vsz (ofList es) ≤ tgtX A t B L + tgtY A t B + 1 :=
    vsz_ofList_le_tgtX A t B L es hlen hL
  have h5 : (A * t * B).size + 3 ≤ 3 * (tgtY A t B + 1) := size_add3_le hN1
  unfold vol
  omega

/-- Window bound for the `take 3` prefix of the four shuffle values. -/
theorem w3_le (E : Val) (A t B : ℕ) (rest : List Val) :
    ((((E :: .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: rest).take 3)).map vsz).sum
      ≤ 6 * vol E A t B := by
  refine window_le_vol _ E A t B (by simp) ?_
  intro x hx
  have hx' : x ∈ [E, .int (A : ℤ), .int (t : ℤ)] := by simpa using hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx'
  rcases hx' with h | h | h <;> subst h <;> simp

/-- Window bound for the `take 5` window of the block-size computation. -/
theorem w5_le (E : Val) (A t B : ℕ) (rest : List Val) :
    ((((.int (t : ℤ) :: E :: .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: rest).take 5)).map vsz).sum
      ≤ 6 * vol E A t B := by
  refine window_le_vol _ E A t B (by simp) ?_
  intro x hx
  have hx' : x ∈ [.int (t : ℤ), E, .int (A : ℤ), .int (t : ℤ), .int (B : ℤ)] := by simpa using hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx'
  rcases hx' with h | h | h | h | h <;> subst h <;> simp

/-- Window bound for the `take 4` window of the forward reorder. -/
theorem w4_le (X : Val) (A t B : ℕ) (rest : List Val) :
    ((((X :: .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: rest).take 4)).map vsz).sum
      ≤ 6 * (vsz X + isz (A : ℤ) + isz (t : ℤ) + isz (B : ℤ) + 1) := by
  refine window_le_vol _ X A t B (by simp) ?_
  intro x hx
  have hx' : x ∈ [X, .int (A : ℤ), .int (t : ℤ), .int (B : ℤ)] := by simpa using hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx'
  rcases hx' with h | h | h | h <;> subst h <;> simp

/-- Window bound for a `take 2` window. -/
theorem w2_le (X : Val) (A t B : ℕ) (rest : List Val) :
    ((((X :: .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: rest).take 2)).map vsz).sum
      ≤ 6 * (vsz X + isz (A : ℤ) + isz (t : ℤ) + isz (B : ℤ) + 1) := by
  refine window_le_vol _ X A t B (by simp) ?_
  intro x hx
  have hx' : x ∈ [X, .int (A : ℤ)] := by simpa using hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx'
  rcases hx' with h | h <;> subst h <;> simp

theorem A_Lmap_le (A t B L : ℕ) (ht : 1 ≤ t) (hB : 1 ≤ B) :
    A * (t * B * (L + 1) + 3 * (t * B) + t + 3) ≤ 9 * tgtX A t B L := by
  have ht' : t ≤ t * B := Nat.le_mul_of_pos_right t (by omega)
  have hbig : 3 * (t * B) + t + 3 ≤ 7 * (t * B) := by nlinarith
  rw [show A * (t * B * (L + 1) + 3 * (t * B) + t + 3) =
      A * (t * B * (L + 1)) + A * (3 * (t * B) + t + 3) from by ring]
  have h2 : A * (3 * (t * B) + t + 3) ≤ 7 * (A * t * B) := by
    calc A * (3 * (t * B) + t + 3) ≤ A * (7 * (t * B)) := Nat.mul_le_mul_left A hbig
      _ = 7 * (A * t * B) := by ring
  have h3 : A * (t * B * (L + 1)) ≤ tgtX A t B L := by
    rw [show A * (t * B * (L + 1)) = A * t * B * (L + 1) from by ring]
    exact le_tgtX_self A t B L
  have h4 : A * t * B ≤ tgtX A t B L := N_le_tgtX A t B L
  nlinarith

theorem A_Lmap_add_le (A t B L : ℕ) (ht : 1 ≤ t) (hB : 1 ≤ B) :
    A * (t * B * (L + 1) + 3 * (t * B) + t + 3) + A + 1 ≤
      12 * (tgtX A t B L + tgtY A t B + 1) := by
  have h1 := A_Lmap_le A t B L ht hB
  have h2 : A ≤ tgtX A t B L :=
    le_trans (le_N_A A t B ht hB) (N_le_tgtX A t B L)
  nlinarith

theorem A_lmap_plus2_le (A t B L : ℕ) (ht : 1 ≤ t) (hB : 1 ≤ B) :
    A * (t * B * (L + 1) + 2) ≤ 3 * tgtX A t B L := by
  have ht' : t ≤ t * B := Nat.le_mul_of_pos_right t (by omega)
  have h1 : A * (t * B * (L + 1) + 2) = A * (t * B * (L + 1)) + A * 2 := by ring
  have h2 : A * (t * B * (L + 1)) ≤ tgtX A t B L := by
    rw [show A * (t * B * (L + 1)) = A * t * B * (L + 1) from by ring]
    exact le_tgtX_self A t B L
  have h3 : A * t * B ≤ tgtX A t B L := N_le_tgtX A t B L
  rw [h1]
  nlinarith

theorem A_tB_term_le (A t B L : ℕ) (hA : 1 ≤ A) (ht : 1 ≤ t) (hB : 1 ≤ B) :
    A * ((t * B + t + 1) * (isz (B : ℤ) + 1)) ≤ 10 * (tgtX A t B L + tgtY A t B + 1) := by
  have ht' : t ≤ t * B := Nat.le_mul_of_pos_right t (by omega)
  have h1 : t * B + t + 1 ≤ 3 * (t * B) := by nlinarith
  have h4 : (t * B + t + 1) * (isz (B : ℤ) + 1) ≤ 3 * (t * B) * (isz (B : ℤ) + 1) :=
    Nat.mul_le_mul_right _ h1
  have h5 : A * ((t * B + t + 1) * (isz (B : ℤ) + 1)) ≤
      3 * ((A * t * B) * (isz (B : ℤ) + 1)) := by
    calc A * ((t * B + t + 1) * (isz (B : ℤ) + 1))
        ≤ A * (3 * (t * B) * (isz (B : ℤ) + 1)) := Nat.mul_le_mul_left A h4
      _ = 3 * ((A * t * B) * (isz (B : ℤ) + 1)) := by ring
  have h6 := N_mul_isz_le A t B (le_N_B A t B hA ht hB)
  have h7 : A * t * B ≤ tgtX A t B L := N_le_tgtX A t B L
  nlinarith

theorem A_tB_term_add_le (A t B L : ℕ) (hA : 1 ≤ A) (ht : 1 ≤ t) (hB : 1 ≤ B) :
    A * ((t * B + t + 1) * (isz (B : ℤ) + 1) + 1) ≤ 11 * (tgtX A t B L + tgtY A t B + 1) := by
  have h1 := A_tB_term_le A t B L hA ht hB
  have h2 : A ≤ tgtX A t B L := le_trans (le_N_A A t B ht hB) (N_le_tgtX A t B L)
  have h3 : A * ((t * B + t + 1) * (isz (B : ℤ) + 1) + 1) =
      A * ((t * B + t + 1) * (isz (B : ℤ) + 1)) + A := by ring
  rw [h3]
  nlinarith

theorem chunk_par_le (A t B L : ℕ) (hA : 1 ≤ A) (ht : 1 ≤ t) (hB : 1 ≤ B) :
    (A + 1) * (isz ((t * B : ℕ) : ℤ) + 1) ≤ 7 * (tgtX A t B L + tgtY A t B + 1) := by
  have h1 : isz ((t * B : ℕ) : ℤ) + 1 ≤ (A * t * B).size + 3 :=
    isz_add_one_le (le_N_of_le_tB A t B hA hB)
  have h2 : A + 1 ≤ 2 * (A * t * B) := by
    have h3 : A ≤ A * t * B := le_N_A A t B ht hB
    omega
  have h4 : (A + 1) * (isz ((t * B : ℕ) : ℤ) + 1) ≤
      2 * (A * t * B) * ((A * t * B).size + 3) := Nat.mul_le_mul h2 h1
  have h5 : (A * t * B) * ((A * t * B).size + 3) ≤ tgtY A t B + 2 * (A * t * B) := by
    have h6 : isz (B : ℤ) ≤ (A * t * B).size + 2 := isz_le_size_add (le_N_B A t B hA ht hB)
    rw [tgtY]
    nlinarith
  have h7 : A * t * B ≤ tgtX A t B L := N_le_tgtX A t B L
  nlinarith

/-! ## Working states of the main word -/

def st0 (es : List Val) (A t B : ℕ) (rest : List Val) : List Val :=
  ofList es :: .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: rest

def st1 (es : List Val) (A t B : ℕ) (rest : List Val) : List Val :=
  .int ((t * B : ℕ) : ℤ) :: ofList es :: .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: rest

def st2 (A t B : ℕ) (es : List Val) (rest : List Val) : List Val :=
  .int ((t * B : ℕ) : ℤ) :: ofList ((blocksOf A t B es).map ofList) ::
    .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: rest

def st3 (A t B : ℕ) (es : List Val) (rest : List Val) : List Val :=
  ofList ((blocksOf A t B es).map ofList) ::
    .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: rest

def st4 (A t B : ℕ) (es : List Val) (rest : List Val) : List Val :=
  ofList ((blocksOf A t B es).map ofList) ::
    .int (t : ℤ) :: .int (B : ℤ) :: .int (A : ℤ) :: rest

def st5 (A t B : ℕ) (es : List Val) (rest : List Val) : List Val :=
  ofList ((blocksOf A t B es).map (fun blk => stateVal ((rowsOf t B blk).map exploded))) ::
    .int (t : ℤ) :: .int (B : ℤ) :: .int (A : ℤ) :: rest

def st6 (A t B : ℕ) (es : List Val) (rest : List Val) : List Val :=
  ofList ((blocksOf A t B es).map (fun blk => stateVal (mAll ((rowsOf t B blk).map exploded)))) ::
    .int (t : ℤ) :: .int (B : ℤ) :: .int (A : ℤ) :: rest

def st11 (A t B : ℕ) (es : List Val) (rest : List Val) : List Val :=
  ofList (List.flatten (HvdH.slices A t B es)) ::
    .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: rest

/-! ## Shape of the per-block and per-array size bounds -/

/-- `lmap t B L` bounds the encoded size of one block's group list. -/
def lmap (t B L : ℕ) : ℕ := t * B * (L + 1) + 3 * (t * B) + t + 4

/-- Bound on the per-block cost of the leaf word. -/
def lcost (Kl t B L : ℕ) : ℕ :=
  Kl * (t * B * (L + 1) + 2) + Kl * ((t * B + t + 1) * (isz (B : ℤ) + 1) + 1)

/-- Bound on the per-block cost of the merge word. -/
def mcost (Km t B L : ℕ) : ℕ := Km * (lmap t B L + 1) * (t.size + 1) + Km

theorem lmap_A_le (A t B L : ℕ) (ht : 1 ≤ t) (hB : 1 ≤ B) :
    A * lmap t B L ≤ 9 * (A * t * B * (L + 1)) := by
  rw [lmap]
  have ht' : t ≤ t * B := Nat.le_mul_of_pos_right t (by omega)
  have hbig : 3 * (t * B) + t + 4 ≤ 8 * (t * B) := by nlinarith
  rw [show A * (t * B * (L + 1) + 3 * (t * B) + t + 4) =
      A * (t * B * (L + 1)) + A * (3 * (t * B) + t + 4) from by ring]
  have h2 : A * (3 * (t * B) + t + 4) ≤ 8 * (A * t * B) := by
    calc A * (3 * (t * B) + t + 4) ≤ A * (8 * (t * B)) := Nat.mul_le_mul_left A hbig
      _ = 8 * (A * t * B) := by ring
  have h3 : A * (t * B * (L + 1)) = A * t * B * (L + 1) := by ring
  have h4 : A * t * B ≤ A * t * B * (L + 1) := Nat.le_mul_of_pos_right _ (by omega)
  rw [h3]
  nlinarith

theorem lmap_A1_le (A t B L : ℕ) (ht : 1 ≤ t) (hB : 1 ≤ B) :
    A * (lmap t B L + 1) ≤ 10 * (A * t * B * (L + 1)) := by
  have h1 : A * lmap t B L ≤ 9 * (A * t * B * (L + 1)) := lmap_A_le A t B L ht hB
  have h2 : A ≤ A * t * B := le_N_A A t B ht hB
  have h3 : A * t * B ≤ A * t * B * (L + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have h4 : A * (lmap t B L + 1) = A * lmap t B L + A := by ring
  rw [h4]
  nlinarith

theorem lmap_A_add_le (A t B L : ℕ) (ht : 1 ≤ t) (hB : 1 ≤ B) :
    A * lmap t B L + A + 1 ≤ 12 * (tgtX A t B L + tgtY A t B + 1) := by
  have h1 : A * lmap t B L ≤ 9 * (A * t * B * (L + 1)) := lmap_A_le A t B L ht hB
  have h2 : A * t * B * (L + 1) ≤ tgtX A t B L := le_tgtX_self A t B L
  have h3 : A ≤ tgtX A t B L := le_trans (le_N_A A t B ht hB) (N_le_tgtX A t B L)
  nlinarith

theorem lmap_A1_mul_le (A t B L : ℕ) (ht : 1 ≤ t) (hB : 1 ≤ B) :
    A * (lmap t B L + 1) * (t.size + 1) ≤ 10 * tgtX A t B L := by
  have h1 : A * lmap t B L ≤ 9 * (A * t * B * (L + 1)) := lmap_A_le A t B L ht hB
  have h2 : A ≤ A * t * B := le_N_A A t B ht hB
  have h3 : A * lmap t B L + A ≤ 10 * (A * t * B * (L + 1)) := by nlinarith
  have h4 : (A * (lmap t B L + 1)) = A * lmap t B L + A := by ring
  rw [h4, tgtX]
  nlinarith

theorem arr3_le (A t B L : ℕ) (ht : 1 ≤ t) (hB : 1 ≤ B) :
    2 * (A * lmap t B L) + 1 ≤ 19 * (tgtX A t B L + tgtY A t B + 1) := by
  have h1 : A * lmap t B L ≤ 9 * (A * t * B * (L + 1)) := lmap_A_le A t B L ht hB
  have h2 : A * t * B * (L + 1) ≤ tgtX A t B L := le_tgtX_self A t B L
  nlinarith

/-! ## The individual cost bounds -/

theorem vsz_ofList_singleton (x : Val) : vsz (ofList [x]) = vsz x + 2 := by
  rw [MrgKit.vsz_ofList]
  simp
  omega

theorem sum_ofList_le (l : List (List Val)) :
    (l.map (fun x => vsz (ofList x))).sum ≤ vsz (ofList (l.map ofList)) := by
  rw [MrgKit.vsz_ofList]
  have h2 : ((l.map ofList).map vsz).sum = (l.map (fun x => vsz (ofList x))).sum := by
    rw [List.map_map]; rfl
  rw [List.length_map, h2]
  omega

theorem flatten_map_singleton' {α : Type} (l : List α) (f : α → Val) :
    (l.map (fun x => [f x])).flatten = l.map f := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [ih]

theorem length_le_vsz_ofList (l : List (List Val)) :
    l.length ≤ vsz (ofList (l.map ofList)) := by
  rw [MrgKit.vsz_ofList, List.length_map]
  omega

theorem flatten_sum_le (l : List (List (List Val))) {B : ℕ}
    (h : ∀ xs ∈ l, vsz (ofList (xs.map ofList)) ≤ B) :
    ((l.flatten).map (fun x => vsz (ofList x))).sum ≤ l.length * B := by
  have h1 : ((l.flatten).map (fun x => vsz (ofList x))).sum =
      (l.map (fun xs => (xs.map (fun x => vsz (ofList x))).sum)).sum := by
    rw [List.map_flatten, List.sum_flatten, List.map_map]
    rfl
  rw [h1]
  have h2 : ∀ xs ∈ l, (xs.map (fun x => vsz (ofList x))).sum ≤ B :=
    fun xs hxs => le_trans (sum_ofList_le xs) (h xs hxs)
  exact MrgKit.sum_le_of_forall (fun xs => (xs.map (fun x => vsz (ofList x))).sum) l B h2

theorem flatten_length_le (l : List (List (List Val))) {B : ℕ}
    (h : ∀ xs ∈ l, vsz (ofList (xs.map ofList)) ≤ B) : l.flatten.length ≤ l.length * B := by
  rw [List.length_flatten]
  have h2 : ∀ xs ∈ l, xs.length ≤ B :=
    fun xs hxs => le_trans (length_le_vsz_ofList xs) (h xs hxs)
  exact MrgKit.sum_le_of_forall List.length l B h2

/-- The list of groups after the leaf phase, as a list of per-block value lists. -/
def xss7 (A t B : ℕ) (es : List Val) : List (List Val) :=
  (blocksOf A t B es).map (fun blk => (mAll ((rowsOf t B blk).map exploded)).map grpVal)

/-- The columns of all blocks, as a list of per-block value lists. -/
def xss8 (A t B : ℕ) (es : List Val) : List (List Val) :=
  (blocksOf A t B es).map (fun blk => (cols (rowsOf t B blk)).map ofList)

/-- The columns of all blocks, flattened. -/
def xss9 (A t B : ℕ) (es : List Val) : List (List Val) :=
  ((blocksOf A t B es).map (fun blk => cols (rowsOf t B blk))).flatten

def st10 (A t B : ℕ) (es : List Val) (rest : List Val) : List Val :=
  ofList (List.flatten (HvdH.slices A t B es)) ::
    .int (t : ℤ) :: .int (B : ℤ) :: .int (A : ℤ) :: rest

theorem prelude_cost_le {Cs Kp Km2 A t B L : ℕ} (es : List Val) (rest : List Val)
    (hA : 1 ≤ A) (ht : 1 ≤ t) (hB : 1 ≤ B) (hlen : es.length = A * t * B)
    (hL : ∀ x ∈ es, vsz x ≤ L) (hCs : 1000 * (Kp + Km2 + 1) ≤ Cs) :
    Kp * 3 * ((((ofList es :: .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: rest).take 3)).map vsz).sum
        + Kp * 3
      + (Kp * 5 * ((((.int (t : ℤ) :: ofList es :: .int (A : ℤ) :: .int (t : ℤ) ::
            .int (B : ℤ) :: rest).take 5)).map vsz).sum + Kp * 5)
      + Km2 * isz (B : ℤ) * isz (t : ℤ) ≤ bd Cs A t B L := by
  have hvol := vol_le_tgt11 A t B L es hlen hA ht hB hL
  have w1 := w3_le (ofList es) A t B rest
  have w2 := w5_le (ofList es) A t B rest
  have hi := isz_mul_le_tgtY A t B hA ht hB (le_N_B A t B hA ht hB) (le_N_t A t B hA hB)
  have hk : 600 * Kp ≤ Cs := by omega
  have hm : 10 * Km2 ≤ Cs := by omega
  have hXY : 1 ≤ tgtX A t B L + tgtY A t B + 1 := by omega
  rw [bd]
  nlinarith

theorem chunk_cost_le {Cs Kc A t B L : ℕ} (es : List Val)
    (hA : 1 ≤ A) (ht : 1 ≤ t) (hB : 1 ≤ B) (hlen : es.length = A * t * B)
    (hL : ∀ x ∈ es, vsz x ≤ L) (hCs : 1000 * (Kc + 1) ≤ Cs) :
    Kc * (vsz (ofList es) + 1) + Kc * ((A + 1) * (isz ((t * B : ℕ) : ℤ) + 1) + 1) ≤ bd Cs A t B L := by
  have h1 : vsz (ofList es) + 1 ≤ tgtX A t B L + tgtY A t B + 2 := by
    have h := vsz_ofList_le_tgtX A t B L es hlen hL
    omega
  have h2 := chunk_par_le A t B L hA ht hB
  have hXY : 1 ≤ tgtX A t B L + tgtY A t B + 1 := by omega
  rw [bd]
  nlinarith

theorem kdr_cost_le (Cs Kdr A t B L : ℕ) (hA : 1 ≤ A) (ht : 1 ≤ t) (hB : 1 ≤ B)
    (hCs : 1000 * (Kdr + 1) ≤ Cs) :
    Kdr * (vsz (.int ((t * B : ℕ) : ℤ)) + 1) ≤ bd Cs A t B L := by
  rw [MrgKit.vsz_int']
  have h1 : isz ((t * B : ℕ) : ℤ) + 1 ≤ (A * t * B).size + 3 :=
    isz_add_one_le (le_N_of_le_tB A t B hA hB)
  have h2 : (A * t * B).size + 3 ≤ 3 * (tgtY A t B + 1) := size_add3_le (one_le_AtB A t B hA ht hB)
  have hXY : 1 ≤ tgtX A t B L + tgtY A t B + 1 := by omega
  rw [bd]
  nlinarith

theorem rollFwd_cost_le (Cs Krl A t B L V : ℕ) (hCs : 1000 * (Krl + 1) ≤ Cs)
    (hV : V ≤ 11 * (tgtX A t B L + tgtY A t B + 1)) :
    Krl * 4 * (6 * V) + Krl * 4 + (Krl * 4 * (6 * V) + Krl * 4) + (Krl * 3 * (6 * V) + Krl * 3)
      ≤ bd Cs A t B L := by
  have hXY : 1 ≤ tgtX A t B L + tgtY A t B + 1 := by omega
  rw [bd]
  nlinarith

theorem rollBack_cost_le (Cs Krl A t B L V : ℕ) (hCs : 1000 * (Krl + 1) ≤ Cs)
    (hV : V ≤ 11 * (tgtX A t B L + tgtY A t B + 1)) :
    Krl * 4 * (6 * V) + Krl * 4 + (Krl * 2 * (6 * V) + Krl * 2) ≤ bd Cs A t B L := by
  have hXY : 1 ≤ tgtX A t B L + tgtY A t B + 1 := by omega
  rw [bd]
  nlinarith

theorem vol_of_le (A t B L : ℕ) (hA : 1 ≤ A) (ht : 1 ≤ t) (hB : 1 ≤ B) {E : Val}
    (hE : vsz E ≤ A * (t * B * (L + 1) + 2) + 1) :
    vol E A t B ≤ 11 * (tgtX A t B L + tgtY A t B + 1) := by
  have hN1 : 1 ≤ A * t * B := one_le_AtB A t B hA ht hB
  have h1 : isz (A : ℤ) ≤ (A * t * B).size + 2 := isz_le_size_add (le_N_A A t B ht hB)
  have h2 : isz (t : ℤ) ≤ (A * t * B).size + 2 := isz_le_size_add (le_N_t A t B hA hB)
  have h3 : isz (B : ℤ) ≤ (A * t * B).size + 2 := isz_le_size_add (le_N_B A t B hA ht hB)
  have h5 : (A * t * B).size + 3 ≤ 3 * (tgtY A t B + 1) := size_add3_le hN1
  have h6 : A * (t * B * (L + 1) + 2) ≤ 3 * tgtX A t B L := A_lmap_plus2_le A t B L ht hB
  unfold vol
  omega

theorem leafCost_le (Cs Kl KmlL A t B L : ℕ) (hA : 1 ≤ A) (ht : 1 ≤ t) (hB : 1 ≤ B)
    (hCs : 1000 * (Kl + KmlL + 1) ≤ Cs) :
    A * (lcost Kl t B L + KmlL * (lmap t B L + 1)) + KmlL ≤ bd Cs A t B L := by
  have h1 : A * (Kl * (t * B * (L + 1) + 2)) ≤ Kl * (3 * tgtX A t B L) := by
    have h := A_lmap_plus2_le A t B L ht hB
    nlinarith
  have h2 : A * (Kl * ((t * B + t + 1) * (isz (B : ℤ) + 1) + 1)) ≤
      Kl * (11 * (tgtX A t B L + tgtY A t B + 1)) := by
    have h := A_tB_term_add_le A t B L hA ht hB
    nlinarith
  have h3 : A * (KmlL * (lmap t B L + 1)) ≤ KmlL * (10 * tgtX A t B L) := by
    have h := lmap_A1_le A t B L ht hB
    have h4 : (A * t * B) * (L + 1) ≤ tgtX A t B L := le_tgtX_self A t B L
    nlinarith
  have hXY : 1 ≤ tgtX A t B L + tgtY A t B + 1 := by omega
  rw [lcost, bd]
  nlinarith

theorem mergeCost_le (Cs Km KmlM A t B L : ℕ) (hA : 1 ≤ A) (ht : 1 ≤ t) (hB : 1 ≤ B)
    (hCs : 1000 * (Km + KmlM + 1) ≤ Cs) :
    A * (mcost Km t B L + KmlM * (lmap t B L + 1)) + KmlM ≤ bd Cs A t B L := by
  have h1 : A * (Km * (lmap t B L + 1) * (t.size + 1)) ≤ Km * (10 * tgtX A t B L) := by
    have h := lmap_A1_mul_le A t B L ht hB
    have h' : A * (lmap t B L + 1) * (t.size + 1) ≤ 10 * tgtX A t B L := h
    nlinarith
  have h2 : A * Km ≤ Km * tgtX A t B L := by
    have h := le_N_A A t B ht hB
    have h' := N_le_tgtX A t B L
    nlinarith
  have h3 : A * (KmlM * (lmap t B L + 1)) ≤ KmlM * (10 * tgtX A t B L) := by
    have h := lmap_A1_le A t B L ht hB
    have h4 : (A * t * B) * (L + 1) ≤ tgtX A t B L := le_tgtX_self A t B L
    nlinarith
  have hXY : 1 ≤ tgtX A t B L + tgtY A t B + 1 := by omega
  rw [mcost, bd]
  nlinarith

theorem flatCost_le (Cs Kfl M X Y : ℕ) (hCs : 1000 * (Kfl + 1) ≤ Cs)
    (hXY : 1 ≤ X + Y + 1) (hM : M ≤ 20 * (X + Y + 1)) : Kfl * (M + 1) ≤ Cs * (X + Y + 1) := by
  nlinarith


/-! ## The phase statements (instantiated forms of `leafPhase` / `mergePhase`) -/

/-- The statement of the leaf phase, with the existential witnesses fixed. -/
def LeafPhStmt (main : Cmd) (leafP : Cmd) (combL : Cmd → Cmd) (Kleaf KmlL : ℕ) : Prop :=
  ∀ (blks : List (List Val)) (t B : ℕ) (rest : List Val) (c Lmap : ℕ),
    (∀ blk ∈ blks, blk.length = t * B) → 1 ≤ t → 1 ≤ B →
    (∀ blk ∈ blks, vsz (ofList blk) ≤ Lmap) →
    (∀ blk ∈ blks, vsz (stateVal ((rowsOf t B blk).map exploded)) ≤ Lmap) →
    (∀ blk ∈ blks, Kleaf * (vsz (ofList blk) + 1) +
        Kleaf * ((blk.length + t + 1) * (isz (B : ℤ) + 1) + 1) ≤ c) →
    WordR main (combL leafP)
      (fun vs => vs = ofList (blks.map ofList) :: .int (t : ℤ) :: .int (B : ℤ) :: rest)
      (fun _ out => out = ofList (blks.map (fun blk => stateVal ((rowsOf t B blk).map exploded))) ::
        .int (t : ℤ) :: .int (B : ℤ) :: rest)
      (fun _ => blks.length * (c + KmlL * (Lmap + 1)) + KmlL)

/-- The statement of the merge phase, with the existential witnesses fixed. -/
def MergePhStmt (main : Cmd) (mrgP : Cmd) (combM : Cmd → Cmd) (Kmrg KmlM : ℕ) : Prop :=
  ∀ (Gss : List (List (List (List Val)))) (t : ℕ) (rest : List Val) (c Lmap : ℕ),
    (∀ Gs ∈ Gss, Gs.length = t) →
    (∀ Gs ∈ Gss, vsz (stateVal Gs) ≤ Lmap) →
    (∀ Gs ∈ Gss, vsz (stateVal (mAll Gs)) ≤ Lmap) →
    (∀ Gs ∈ Gss, Kmrg * (vsz (stateVal Gs) + 1) * (t.size + 1) + Kmrg ≤ c) →
    WordR main (combM mrgP)
      (fun vs => vs = ofList (Gss.map stateVal) :: rest)
      (fun _ out => out = ofList (Gss.map (fun Gs => stateVal (mAll Gs))) :: rest)
      (fun _ => Gss.length * (c + KmlM * (Lmap + 1)) + KmlM)

/-! ## Phase 1: the parameter block (steps 1-4) -/

/-- The program of phase 1 (the parameter block). -/
def progParam (mulP chunkP kdrP : Cmd) (pickP rollP : ℕ → Cmd) : Cmd :=
  pickP 2 ;;; pickP 4 ;;; mulP ;;; chunkP ;;; kdrP ;;; (rollP 3 ;;; rollP 3 ;;; rollP 2)

/-- The program of phase 2 (leaf + merge on every block). -/
def progArr (leafP mrgP : Cmd) (combL combM : Cmd → Cmd) : Cmd :=
  combL leafP ;;; combM mrgP

/-- The program of phase 3 (three flattens and the final reorder). -/
def progFlat (flP : Cmd) (rollP : ℕ → Cmd) : Cmd :=
  flP ;;; flP ;;; flP ;;; (rollP 3 ;;; rollP 1)

theorem axisStepParam {main : Cmd} {chunkP mulP kdrP : Cmd} {pickP rollP : ℕ → Cmd}
    {Kc Kpk Krl Kdr Km2 Cs : ℕ}
    (hchunk : ∀ (S : ℕ) (xs : List Val) (rest : List Val), 1 ≤ S → S ∣ xs.length →
      WordR main chunkP (fun vs => vs = .int (S : ℤ) :: ofList xs :: rest)
        (fun _ out => out = .int (S : ℤ) :: ofList ((chunkList S xs).map ofList) :: rest)
        (fun _ => Kc * (vsz (ofList xs) + 1) +
          Kc * ((xs.length / S + 1) * (isz (S : ℤ) + 1) + 1)))
    (hpick : ∀ k, WordR main (pickP k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs)
      (fun vs => Kpk * (k+1) * (((vs.take (k+1)).map vsz).sum + 1)))
    (hroll : ∀ k, WordR main (rollP k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs.eraseIdx k)
      (fun vs => Krl * (k+1) * (((vs.take (k+1)).map vsz).sum + 1)))
    (hkdr : WordR main kdrP (fun vs => vs ≠ [])
      (fun vs out => ∃ v rest, vs = v :: rest ∧ out = rest)
      (fun vs => Kdr * (vsz (vs.headD .nil) + 1)))
    (hmulS : BinOp main mulP (fun _ _ => True) (· * ·) (fun a b => Km2 * isz a * isz b))
    (hCs : 1000 * (Kc + Kpk + Krl + Kdr + Km2 + 1) ≤ Cs)
    (A t B L : ℕ) (es : List Val) (rest : List Val)
    (hlen : es.length = A * t * B) (hL : ∀ x ∈ es, vsz x ≤ L)
    (hA : 1 ≤ A) (ht : 1 ≤ t) (hB : 1 ≤ B)
    (hchunkId : chunkList (t * B) es = blocksOf A t B es)
    (hszArr1 : vsz (ofList ((blocksOf A t B es).map ofList)) ≤ A * (t * B * (L + 1) + 2) + 1) :
    WordR main (progParam mulP chunkP kdrP pickP rollP)
      (fun vs => vs = st0 es A t B rest) (fun _ out => out = st4 A t B es rest)
      (fun _ => 4 * bd Cs A t B L) := by
  have hK1 : 1000 * (Kpk + Km2 + 1) ≤ Cs := by omega
  have h1 : WordR main (pickP 2 ;;; pickP 4 ;;; mulP) (fun vs => vs = st0 es A t B rest)
      (fun _ out => out = st1 es A t B rest) (fun _ => bd Cs A t B L) := by
    have hD := prelude_cost_le es rest hA ht hB hlen hL hK1
    exact MrgKit.WordR_weaken (prelude_mkS hpick hmulS (ofList es) A t B rest hD)
      (fun _ hv => hv) (fun _ _ _ hq => hq) (fun _ _ => le_rfl)
  have h2 : WordR main chunkP (fun vs => vs = st1 es A t B rest)
      (fun _ out => out = st2 A t B es rest) (fun _ => bd Cs A t B L) := by
    have hS1 : 1 ≤ t * B := Nat.mul_pos (by omega) (by omega)
    have hdvd : t * B ∣ es.length := ⟨A, by rw [hlen]; ring⟩
    have hraw := hchunk (t * B) es (.int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: rest) hS1 hdvd
    refine MrgKit.WordR_weaken hraw ?_ ?_ ?_
    · intro vs hv; rw [hv]; rfl
    · intro vs out hv hq
      rw [hq, hchunkId]
      rfl
    · intro vs hv
      have hdiv : es.length / (t * B) = A := by
        refine (Nat.div_eq_iff_eq_mul_right (a := es.length) (b := t * B) (c := A)
          (Nat.mul_pos (by omega) (by omega)) hdvd).mpr ?_
        rw [hlen]
        ring
      rw [hdiv]
      exact chunk_cost_le es hA ht hB hlen hL (by omega)
  have h3 : WordR main kdrP (fun vs => vs = st2 A t B es rest)
      (fun _ out => out = st3 A t B es rest) (fun _ => bd Cs A t B L) := by
    refine MrgKit.WordR_weaken (MrgKit.kdropStep hkdr (st2 A t B es rest) (by simp [st2])
      (bd Cs A t B L) ?_) (fun _ hv => hv) (fun _ _ _ hq => hq) (fun _ _ => le_rfl)
    exact kdr_cost_le Cs Kdr A t B L hA ht hB (by omega : 1000 * (Kdr + 1) ≤ Cs)
  have h4 : WordR main (rollP 3 ;;; rollP 3 ;;; rollP 2) (fun vs => vs = st3 A t B es rest)
      (fun _ out => out = st4 A t B es rest) (fun _ => bd Cs A t B L) := by
    have hV := vol_of_le A t B L hA ht hB hszArr1
    have w1 : ((((ofList ((blocksOf A t B es).map ofList)) :: .int (A : ℤ) :: .int (t : ℤ) ::
        .int (B : ℤ) :: rest).take 4).map vsz).sum
        ≤ 6 * vol (ofList ((blocksOf A t B es).map ofList)) A t B := by
      refine window_le_vol _ _ A t B (by simp) ?_
      intro x hx
      have hx' : x ∈ ([ofList ((blocksOf A t B es).map ofList), .int (A : ℤ), .int (t : ℤ),
          .int (B : ℤ)] : List Val) := by simpa using hx
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx' ⊢
      tauto
    have w2 : (((.int (B : ℤ) :: ofList ((blocksOf A t B es).map ofList) :: .int (A : ℤ) ::
        .int (t : ℤ) :: rest).take 4).map vsz).sum
        ≤ 6 * vol (ofList ((blocksOf A t B es).map ofList)) A t B := by
      refine window_le_vol _ _ A t B (by simp) ?_
      intro x hx
      have hx' : x ∈ ([.int (B : ℤ), ofList ((blocksOf A t B es).map ofList), .int (A : ℤ),
          .int (t : ℤ)] : List Val) := by simpa using hx
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx' ⊢
      tauto
    have w3 : (((.int (t : ℤ) :: .int (B : ℤ) :: ofList ((blocksOf A t B es).map ofList) ::
        .int (A : ℤ) :: rest).take 3).map vsz).sum
        ≤ 6 * vol (ofList ((blocksOf A t B es).map ofList)) A t B := by
      refine window_le_vol _ _ A t B (by simp) ?_
      intro x hx
      have hx' : x ∈ ([.int (t : ℤ), .int (B : ℤ),
          ofList ((blocksOf A t B es).map ofList)] : List Val) := by simpa using hx
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx' ⊢
      tauto
    have hcost := rollFwd_cost_le Cs Krl A t B L
      (vol (ofList ((blocksOf A t B es).map ofList)) A t B) (by omega) hV
    have hD : Krl * 4 * ((((ofList ((blocksOf A t B es).map ofList)) :: .int (A : ℤ) ::
          .int (t : ℤ) :: .int (B : ℤ) :: rest).take 4).map vsz).sum + Krl * 4
        + (Krl * 4 * (((.int (B : ℤ) :: ofList ((blocksOf A t B es).map ofList) :: .int (A : ℤ) ::
            .int (t : ℤ) :: rest).take 4).map vsz).sum + Krl * 4)
        + (Krl * 3 * (((.int (t : ℤ) :: .int (B : ℤ) ::
            ofList ((blocksOf A t B es).map ofList) :: .int (A : ℤ) :: rest).take 3).map vsz).sum
          + Krl * 3)
        ≤ bd Cs A t B L := by
      refine le_trans ?_ hcost
      nlinarith [w1, w2, w3]
    exact MrgKit.WordR_weaken
      (prelude_reorderFwd hroll (ofList ((blocksOf A t B es).map ofList)) A t B rest hD)
      (fun _ hv => hv) (fun _ _ _ hq => hq) (fun _ _ => le_rfl)
  have h12 := MrgKit.WordR_seqC h1 h2
  have h123 := MrgKit.WordR_seqC h12 h3
  have h1234 := MrgKit.WordR_seqC h123 h4
  refine MrgKit.WordR_weaken h1234 (fun _ hv => hv) (fun _ _ _ hq => hq) (fun _ _ => ?_)
  show bd Cs A t B L + bd Cs A t B L + bd Cs A t B L + bd Cs A t B L ≤ 4 * bd Cs A t B L
  omega

theorem vsz_ofList_map_le {α : Type} (l : List α) (f : α → Val) (A B : ℕ) (hlen : l.length ≤ A)
    (h : ∀ x ∈ l, vsz (f x) ≤ B) : vsz (ofList (l.map f)) ≤ A * B + A + 1 := by
  rw [MrgKit.vsz_ofList, List.length_map]
  have h1 := MrgKit.sum_le_of_forall (fun x => vsz (f x)) l B h
  have h2 : ((l.map f).map vsz).sum = (l.map (fun x => vsz (f x))).sum := by
    rw [List.map_map]; rfl
  rw [h2]
  nlinarith

theorem vsz_ofList_flatten_map_le (l : List (List (List Val))) (A B : ℕ) (hlen : l.length ≤ A)
    (h : ∀ xs ∈ l, vsz (ofList (xs.map ofList)) ≤ B) :
    vsz (ofList ((l.flatten).map ofList)) ≤ A * B + A * B + 1 := by
  rw [MrgKit.vsz_ofList, List.length_map]
  have hlen' : (l.flatten).length ≤ A * B :=
    le_trans (flatten_length_le l h) (by nlinarith)
  have hsum : (((l.flatten).map ofList).map vsz).sum ≤ A * B := by
    have h' : ((l.flatten).map (fun x => vsz (ofList x))).sum ≤ l.length * B := flatten_sum_le l h
    have he : ((l.flatten).map ofList).map vsz = (l.flatten).map (fun x => vsz (ofList x)) := by
      rw [List.map_map]; rfl
    rw [he]
    nlinarith
  omega

/-- The head value of the state after the leaf/merge phase: the encoded encoded-columns. -/
def yss8 (A t B : ℕ) (es : List Val) : List Val :=
  (blocksOf A t B es).map (fun blk => grpVal (cols (rowsOf t B blk)))

def P7 (A t B : ℕ) (es : List Val) (rest : List Val) : List Val :=
  ofList (yss8 A t B es) :: .int (t : ℤ) :: .int (B : ℤ) :: .int (A : ℤ) :: rest

def Q8 (A t B : ℕ) (es : List Val) (rest : List Val) : List Val :=
  ofList ((xss9 A t B es).map ofList) :: .int (t : ℤ) :: .int (B : ℤ) :: .int (A : ℤ) :: rest

theorem axisStepArr {main : Cmd} {leafP mrgP : Cmd} {combL combM : Cmd → Cmd}
    {Kl Km KmlL KmlM Cs : ℕ}
    (Hleaf : LeafPhStmt main leafP combL Kl KmlL)
    (Hmrg : MergePhStmt main mrgP combM Km KmlM)
    (hCs : 1000 * (Kl + Km + KmlL + KmlM + 1) ≤ Cs)
    (A t B L : ℕ) (es : List Val) (rest : List Val)
    (hlen : es.length = A * t * B) (hL : ∀ x ∈ es, vsz x ≤ L)
    (hA : 1 ≤ A) (ht : 1 ≤ t) (hB : 1 ≤ B)
    (hblksLen : (blocksOf A t B es).length = A)
    (hblkLen : ∀ blk ∈ blocksOf A t B es, blk.length = t * B)
    (hrowsLen : ∀ (t B : ℕ) (blk : List Val), blk.length = t * B → (rowsOf t B blk).length = t)
    (hszBlkEl : ∀ blk ∈ blocksOf A t B es, ∀ x ∈ blk, vsz x ≤ L)
    (hszBlk : ∀ blk ∈ blocksOf A t B es, vsz (ofList blk) ≤ t * B * (L + 1) + 1)
    (hszLeaf : ∀ blk ∈ blocksOf A t B es,
      vsz (stateVal ((rowsOf t B blk).map exploded)) ≤ t * B * (L + 1) + 3 * (t * B) + t + 2)
    (hszMerged : ∀ (t B L : ℕ) (blk : List Val), 1 ≤ t → blk.length = t * B →
      (∀ x ∈ blk, vsz x ≤ L) →
      vsz (stateVal (mAll ((rowsOf t B blk).map exploded))) ≤ t * B * (L + 1) + 3 * (t * B) + t + 3) :
    WordR main (progArr leafP mrgP combL combM)
      (fun vs => vs = st4 A t B es rest) (fun _ out => out = st6 A t B es rest)
      (fun _ => 2 * bd Cs A t B L) := by
  have h5 : WordR main (combL leafP) (fun vs => vs = st4 A t B es rest)
      (fun _ out => out = st5 A t B es rest) (fun _ => bd Cs A t B L) := by
    have hc : ∀ blk ∈ blocksOf A t B es,
        Kl * (vsz (ofList blk) + 1) + Kl * ((blk.length + t + 1) * (isz (B : ℤ) + 1) + 1)
          ≤ lcost Kl t B L := by
      intro blk hblk
      have h1 := hszBlk blk hblk
      have h2 := hblkLen blk hblk
      rw [h2, lcost]
      nlinarith
    have hL1 : ∀ blk ∈ blocksOf A t B es, vsz (ofList blk) ≤ lmap t B L := by
      intro blk hblk
      have h1 := hszBlk blk hblk
      rw [lmap]; omega
    have hL2 : ∀ blk ∈ blocksOf A t B es,
        vsz (stateVal ((rowsOf t B blk).map exploded)) ≤ lmap t B L := by
      intro blk hblk
      have h1 := hszLeaf blk hblk
      rw [lmap]; omega
    have hraw := Hleaf (blocksOf A t B es) t B (.int (A : ℤ) :: rest) (lcost Kl t B L)
      (lmap t B L) hblkLen ht hB hL1 hL2 hc
    refine MrgKit.WordR_weaken hraw (fun _ hv => hv) (fun _ _ _ hq => hq) (fun _ _ => ?_)
    rw [hblksLen]
    exact leafCost_le Cs Kl KmlL A t B L hA ht hB (by omega)
  have h6 : WordR main (combM mrgP) (fun vs => vs = st5 A t B es rest)
      (fun _ out => out = st6 A t B es rest) (fun _ => bd Cs A t B L) := by
    have hcc : ∀ Gs ∈ (blocksOf A t B es).map (fun blk => (rowsOf t B blk).map exploded),
        Km * (vsz (stateVal Gs) + 1) * (t.size + 1) + Km ≤ mcost Km t B L := by
      intro Gs hGs
      rw [List.mem_map] at hGs
      obtain ⟨blk, hblk, rfl⟩ := hGs
      have h1 := hszLeaf blk hblk
      have h2 : vsz (stateVal ((rowsOf t B blk).map exploded)) + 1 ≤ lmap t B L + 1 := by
        rw [lmap]; omega
      calc Km * (vsz (stateVal ((rowsOf t B blk).map exploded)) + 1) * (t.size + 1) + Km
          ≤ Km * (lmap t B L + 1) * (t.size + 1) + Km :=
            Nat.add_le_add_right (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h2)) _
        _ = mcost Km t B L := by rw [mcost]
    have hG1 : ∀ Gs ∈ (blocksOf A t B es).map (fun blk => (rowsOf t B blk).map exploded),
        Gs.length = t := by
      intro Gs hGs
      rw [List.mem_map] at hGs
      obtain ⟨blk, hblk, rfl⟩ := hGs
      rw [List.length_map]
      exact hrowsLen t B blk (hblkLen blk hblk)
    have hG2 : ∀ Gs ∈ (blocksOf A t B es).map (fun blk => (rowsOf t B blk).map exploded),
        vsz (stateVal Gs) ≤ lmap t B L := by
      intro Gs hGs
      rw [List.mem_map] at hGs
      obtain ⟨blk, hblk, rfl⟩ := hGs
      have h1 := hszLeaf blk hblk
      rw [lmap]; omega
    have hG3 : ∀ Gs ∈ (blocksOf A t B es).map (fun blk => (rowsOf t B blk).map exploded),
        vsz (stateVal (mAll Gs)) ≤ lmap t B L := by
      intro Gs hGs
      rw [List.mem_map] at hGs
      obtain ⟨blk, hblk, rfl⟩ := hGs
      have h1 := hszMerged t B L blk ht (hblkLen blk hblk) (hszBlkEl blk hblk)
      rw [lmap]; omega
    have hraw := Hmrg ((blocksOf A t B es).map (fun blk => (rowsOf t B blk).map exploded)) t
      (.int (t : ℤ) :: .int (B : ℤ) :: .int (A : ℤ) :: rest) (mcost Km t B L) (lmap t B L)
      hG1 hG2 hG3 hcc
    refine MrgKit.WordR_weaken hraw ?_ ?_ ?_
    · intro vs hv
      rw [hv, List.map_map]
      rfl
    · intro vs out hv hq
      rw [hq, List.map_map, st6]
      rfl
    · intro vs hv
      rw [List.length_map, hblksLen]
      exact mergeCost_le Cs Km KmlM A t B L hA ht hB (by omega)
  have h56 := MrgKit.WordR_seqC h5 h6
  refine MrgKit.WordR_weaken h56 (fun _ hv => hv) (fun _ _ _ hq => hq) (fun _ _ => ?_)
  show bd Cs A t B L + bd Cs A t B L ≤ 2 * bd Cs A t B L
  omega

theorem axisStepFlat {main : Cmd} {flP : Cmd} {rollP : ℕ → Cmd} {Kfl Krl Cs : ℕ}
    (hfl : ∀ (xss : List (List Val)), WordR main flP
      (fun vs => ∃ rest, vs = ofList (xss.map ofList) :: rest)
      (fun vs out => ∃ rest, vs = ofList (xss.map ofList) :: rest ∧ out = ofList xss.flatten :: rest)
      (fun _ => Kfl * (vsz (ofList (xss.map ofList)) + 1)))
    (hroll : ∀ k, WordR main (rollP k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs.eraseIdx k)
      (fun vs => Krl * (k+1) * (((vs.take (k+1)).map vsz).sum + 1)))
    (hCs : 1000 * (Kfl + Krl + 1) ≤ Cs)
    (A t B L : ℕ) (es : List Val) (rest : List Val)
    (hlen : es.length = A * t * B) (hL : ∀ x ∈ es, vsz x ≤ L)
    (hA : 1 ≤ A) (ht : 1 ≤ t) (hB : 1 ≤ B)
    (hblksLen : (blocksOf A t B es).length = A)
    (hblkLen : ∀ blk ∈ blocksOf A t B es, blk.length = t * B)
    (hrowsLen : ∀ (t B : ℕ) (blk : List Val), blk.length = t * B → (rowsOf t B blk).length = t)
    (hszBlkEl : ∀ blk ∈ blocksOf A t B es, ∀ x ∈ blk, vsz x ≤ L)
    (hszMerged : ∀ (t B L : ℕ) (blk : List Val), 1 ≤ t → blk.length = t * B →
      (∀ x ∈ blk, vsz x ≤ L) →
      vsz (stateVal (mAll ((rowsOf t B blk).map exploded))) ≤ t * B * (L + 1) + 3 * (t * B) + t + 3)
    (hslicesId : List.flatten (HvdH.slices A t B es) =
      ((blocksOf A t B es).map (fun blk => (cols (rowsOf t B blk)).flatten)).flatten)
    (hszOut : vsz (ofList (List.flatten (HvdH.slices A t B es))) ≤ A * t * B * (L + 1) + 1) :
    WordR main (progFlat flP rollP) (fun vs => vs = st6 A t B es rest)
      (fun _ out => out = st11 A t B es rest) (fun _ => 5 * bd Cs A t B L) := by
  have hP : ∀ blk ∈ blocksOf A t B es, vsz (grpVal (cols (rowsOf t B blk))) ≤ lmap t B L := by
    intro blk hblk
    have hne : rowsOf t B blk ≠ [] := by
      rw [List.ne_nil_iff_length_pos, hrowsLen t B blk (hblkLen blk hblk)]
      omega
    have h1 := hszMerged t B L blk ht (hblkLen blk hblk) (hszBlkEl blk hblk)
    have h2 : mAll ((rowsOf t B blk).map exploded) = [cols (rowsOf t B blk)] :=
      mAll_map_exploded (rowsOf t B blk) hne
    have h3 : vsz (stateVal [cols (rowsOf t B blk)]) ≤ t * B * (L + 1) + 3 * (t * B) + t + 3 := by
      rw [← h2]; exact h1
    have h4 : vsz (grpVal (cols (rowsOf t B blk))) + 2 ≤ t * B * (L + 1) + 3 * (t * B) + t + 3 := by
      rw [← vsz_ofList_singleton (grpVal (cols (rowsOf t B blk)))]
      show vsz (stateVal [cols (rowsOf t B blk)]) ≤ t * B * (L + 1) + 3 * (t * B) + t + 3
      exact h3
    rw [lmap]
    omega
  have hPn : ∀ blk ∈ blocksOf A t B es,
      vsz (stateVal (mAll ((rowsOf t B blk).map exploded))) ≤ lmap t B L := by
    intro blk hblk
    have h1 := hszMerged t B L blk ht (hblkLen blk hblk) (hszBlkEl blk hblk)
    rw [lmap]; omega
  have hxss7 : (blocksOf A t B es).map (fun blk => stateVal (mAll ((rowsOf t B blk).map exploded)))
      = (xss7 A t B es).map ofList := by
    rw [xss7, List.map_map]; rfl
  have hcongr : ∀ blk ∈ blocksOf A t B es,
      (mAll ((rowsOf t B blk).map exploded)).map grpVal = [grpVal (cols (rowsOf t B blk))] := by
    intro blk hblk
    have hne : rowsOf t B blk ≠ [] := by
      rw [List.ne_nil_iff_length_pos, hrowsLen t B blk (hblkLen blk hblk)]
      omega
    rw [mAll_map_exploded (rowsOf t B blk) hne, List.map_cons, List.map_nil]
  have hflatten7 : (xss7 A t B es).flatten = yss8 A t B es := by
    rw [xss7, yss8, List.map_congr_left hcongr]
    exact flatten_map_singleton' (blocksOf A t B es) (fun blk => grpVal (cols (rowsOf t B blk)))
  have hys8 : yss8 A t B es = (xss8 A t B es).map ofList := by
    rw [yss8, xss8, List.map_map]; rfl
  have hflatten8 : (xss8 A t B es).flatten = (xss9 A t B es).map ofList := by
    rw [xss8, xss9, List.map_flatten, List.map_map]; rfl
  have hflatten9 : (xss9 A t B es).flatten = List.flatten (HvdH.slices A t B es) := by
    rw [xss9, flatten_flatten_map]
    exact hslicesId.symm
  have hM7 : vsz (ofList ((xss7 A t B es).map ofList)) ≤ 20 * (tgtX A t B L + tgtY A t B + 1) := by
    have h1 : vsz (ofList ((blocksOf A t B es).map
        (fun blk => stateVal (mAll ((rowsOf t B blk).map exploded))))) ≤ A * lmap t B L + A + 1 :=
      vsz_ofList_map_le (blocksOf A t B es)
        (fun blk => stateVal (mAll ((rowsOf t B blk).map exploded))) A (lmap t B L)
        (le_of_eq hblksLen) hPn
    rw [← hxss7]
    have h2 := lmap_A_add_le A t B L ht hB
    nlinarith
  have hM8 : vsz (ofList ((xss8 A t B es).map ofList)) ≤ 20 * (tgtX A t B L + tgtY A t B + 1) := by
    have h1 : vsz (ofList ((blocksOf A t B es).map
        (fun blk => grpVal (cols (rowsOf t B blk))))) ≤ A * lmap t B L + A + 1 :=
      vsz_ofList_map_le (blocksOf A t B es) (fun blk => grpVal (cols (rowsOf t B blk))) A
        (lmap t B L) (le_of_eq hblksLen) hP
    rw [← hys8, yss8]
    have h2 := lmap_A_add_le A t B L ht hB
    nlinarith
  have hM9 : vsz (ofList ((xss9 A t B es).map ofList)) ≤ 20 * (tgtX A t B L + tgtY A t B + 1) := by
    have hsum : ∀ xs ∈ (blocksOf A t B es).map (fun blk => cols (rowsOf t B blk)),
        vsz (ofList (xs.map ofList)) ≤ lmap t B L := by
      intro xs hxs
      rw [List.mem_map] at hxs
      obtain ⟨blk, hblk, rfl⟩ := hxs
      exact hP blk hblk
    have h1 : vsz (ofList ((((blocksOf A t B es).map (fun blk => cols (rowsOf t B blk))).flatten).map
        ofList)) ≤ A * lmap t B L + A * lmap t B L + 1 :=
      vsz_ofList_flatten_map_le ((blocksOf A t B es).map (fun blk => cols (rowsOf t B blk))) A
        (lmap t B L) (le_of_eq (by rw [List.length_map, hblksLen])) hsum
    rw [xss9]
    have h2 := arr3_le A t B L ht hB
    nlinarith
  have h7 : WordR main flP (fun vs => vs = st6 A t B es rest) (fun _ out => out = P7 A t B es rest)
      (fun _ => bd Cs A t B L) := by
    have hraw := hfl (xss7 A t B es)
    refine MrgKit.WordR_weaken hraw ?_ ?_ ?_
    · intro vs hv
      refine ⟨.int (t : ℤ) :: .int (B : ℤ) :: .int (A : ℤ) :: rest, ?_⟩
      rw [hv, st6, hxss7]
    · intro vs out hv hq
      obtain ⟨r, hv', hout⟩ := hq
      have hr : r = .int (t : ℤ) :: .int (B : ℤ) :: .int (A : ℤ) :: rest := by
        rw [hv, st6, hxss7] at hv'
        exact (List.cons.inj hv'.symm).2
      rw [hout, hr, P7, hflatten7]
    · intro vs hv
      rw [bd]
      exact flatCost_le Cs Kfl (vsz (ofList ((xss7 A t B es).map ofList))) (tgtX A t B L)
        (tgtY A t B) (by omega) (by omega) hM7
  have h8 : WordR main flP (fun vs => vs = P7 A t B es rest) (fun _ out => out = Q8 A t B es rest)
      (fun _ => bd Cs A t B L) := by
    have hraw := hfl (xss8 A t B es)
    refine MrgKit.WordR_weaken hraw ?_ ?_ ?_
    · intro vs hv
      refine ⟨.int (t : ℤ) :: .int (B : ℤ) :: .int (A : ℤ) :: rest, ?_⟩
      rw [hv, P7, hys8]
    · intro vs out hv hq
      obtain ⟨r, hv', hout⟩ := hq
      have hr : r = .int (t : ℤ) :: .int (B : ℤ) :: .int (A : ℤ) :: rest := by
        rw [hv, P7, hys8] at hv'
        exact (List.cons.inj hv'.symm).2
      rw [hout, hr, Q8, hflatten8]
    · intro vs hv
      rw [bd]
      exact flatCost_le Cs Kfl (vsz (ofList ((xss8 A t B es).map ofList))) (tgtX A t B L)
        (tgtY A t B) (by omega) (by omega) hM8
  have h9 : WordR main flP (fun vs => vs = Q8 A t B es rest)
      (fun _ out => out = st10 A t B es rest) (fun _ => bd Cs A t B L) := by
    have hraw := hfl (xss9 A t B es)
    refine MrgKit.WordR_weaken hraw ?_ ?_ ?_
    · intro vs hv
      exact ⟨.int (t : ℤ) :: .int (B : ℤ) :: .int (A : ℤ) :: rest, by rw [hv, Q8]⟩
    · intro vs out hv hq
      obtain ⟨r, hv', hout⟩ := hq
      have hr : r = .int (t : ℤ) :: .int (B : ℤ) :: .int (A : ℤ) :: rest := by
        rw [hv, Q8] at hv'
        exact (List.cons.inj hv'.symm).2
      rw [hout, hr, st10, hflatten9]
    · intro vs hv
      rw [bd]
      exact flatCost_le Cs Kfl (vsz (ofList ((xss9 A t B es).map ofList))) (tgtX A t B L)
        (tgtY A t B) (by omega) (by omega) hM9
  have h10 : WordR main (rollP 3 ;;; rollP 1) (fun vs => vs = st10 A t B es rest)
      (fun _ out => out = st11 A t B es rest) (fun _ => bd Cs A t B L) := by
    have hV : vol (ofList (List.flatten (HvdH.slices A t B es))) A t B
        ≤ 11 * (tgtX A t B L + tgtY A t B + 1) :=
      vol_of_le A t B L hA ht hB (le_trans hszOut (by nlinarith))
    have w1 : ((((ofList (List.flatten (HvdH.slices A t B es))) :: .int (t : ℤ) :: .int (B : ℤ) ::
        .int (A : ℤ) :: rest).take 4).map vsz).sum
        ≤ 6 * vol (ofList (List.flatten (HvdH.slices A t B es))) A t B := by
      refine window_le_vol _ _ A t B (by simp) ?_
      intro x hx
      have hx' : x ∈ ([ofList (List.flatten (HvdH.slices A t B es)), .int (t : ℤ), .int (B : ℤ),
          .int (A : ℤ)] : List Val) := by simpa using hx
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx' ⊢
      tauto
    have w2 : (((.int (A : ℤ) :: ofList (List.flatten (HvdH.slices A t B es)) :: .int (t : ℤ) ::
        .int (B : ℤ) :: rest).take 2).map vsz).sum
        ≤ 6 * vol (ofList (List.flatten (HvdH.slices A t B es))) A t B := by
      refine window_le_vol _ _ A t B (by simp) ?_
      intro x hx
      have hx' : x ∈ ([.int (A : ℤ), ofList (List.flatten (HvdH.slices A t B es))] : List Val) := by
        simpa using hx
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx' ⊢
      tauto
    have hcost := rollBack_cost_le Cs Krl A t B L
      (vol (ofList (List.flatten (HvdH.slices A t B es))) A t B) (by omega) hV
    have hD : Krl * 4 * ((((ofList (List.flatten (HvdH.slices A t B es))) :: .int (t : ℤ) ::
          .int (B : ℤ) :: .int (A : ℤ) :: rest).take 4).map vsz).sum + Krl * 4
        + (Krl * 2 * (((.int (A : ℤ) :: ofList (List.flatten (HvdH.slices A t B es)) ::
            .int (t : ℤ) :: .int (B : ℤ) :: rest).take 2).map vsz).sum + Krl * 2)
        ≤ bd Cs A t B L := by
      refine le_trans ?_ hcost
      nlinarith [w1, w2]
    exact MrgKit.WordR_weaken
      (prelude_reorderBack hroll (ofList (List.flatten (HvdH.slices A t B es))) A t B rest hD)
      (fun _ hv => hv) (fun _ _ _ hq => hq) (fun _ _ => le_rfl)
  have h78 := MrgKit.WordR_seqC h7 h8
  have h789 := MrgKit.WordR_seqC h78 h9
  have h78910 := MrgKit.WordR_seqC h789 h10
  have hcost5 : (((bd Cs A t B L + bd Cs A t B L) + bd Cs A t B L) + bd Cs A t B L)
      ≤ 5 * (bd Cs A t B L) := by omega
  exact MrgKit.WordR_weaken h78910 (fun _ hv => hv) (fun _ _ _ hq => hq) (fun _ _ => hcost5)

theorem tgt_final (Cs A t B L : ℕ) :
    (100 * Cs) * (A * t * B) * (L + 1) * (t.size + 1) +
      (100 * Cs) * (A * t * B) * ((A * t * B).size + 1) + 100 * Cs
      = 100 * bd Cs A t B L := by
  rw [bd, tgtX, tgtY]; ring

/-! ## The main path on a nonempty array -/

theorem mainPath {chunkP leafP mrgP mulP kdrP flP : Cmd} {pickP : ℕ → Cmd} {rollP : ℕ → Cmd}
    {Kc Kl Km Kpk Krl Kdr Kfl Km2 : ℕ}
    (hchunk : ∀ (main : Cmd) (S : ℕ) (xs : List Val) (rest : List Val), 1 ≤ S → S ∣ xs.length →
      WordR main chunkP (fun vs => vs = .int (S : ℤ) :: ofList xs :: rest)
        (fun _ out => out = .int (S : ℤ) :: ofList ((chunkList S xs).map ofList) :: rest)
        (fun _ => Kc * (vsz (ofList xs) + 1) +
          Kc * ((xs.length / S + 1) * (isz (S : ℤ) + 1) + 1)))
    (hleaf : ∀ (main : Cmd) (t B : ℕ) (blk : List Val) (rest : List Val),
      blk.length = t * B → 1 ≤ t → 1 ≤ B →
      WordR main leafP (fun vs => vs = ofList blk :: .int (t : ℤ) :: .int (B : ℤ) :: rest)
        (fun _ out => out = stateVal ((rowsOf t B blk).map exploded) ::
          .int (t : ℤ) :: .int (B : ℤ) :: rest)
        (fun _ => Kl * (vsz (ofList blk) + 1) +
          Kl * ((blk.length + t + 1) * (isz (B : ℤ) + 1) + 1)))
    (hmrg : ∀ (main : Cmd) (Gs : List (List (List Val))) (rest : List Val),
      WordR main mrgP (fun vs => vs = stateVal Gs :: rest)
        (fun _ out => out = stateVal (mAll Gs) :: rest)
        (fun _ => Km * (vsz (stateVal Gs) + 1) * (Gs.length.size + 1) + Km))
    (hpick : ∀ (main : Cmd) (k : ℕ), WordR main (pickP k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs)
      (fun vs => Kpk * (k+1) * (((vs.take (k+1)).map vsz).sum + 1)))
    (hroll : ∀ (main : Cmd) (k : ℕ), WordR main (rollP k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs.eraseIdx k)
      (fun vs => Krl * (k+1) * (((vs.take (k+1)).map vsz).sum + 1)))
    (hkdr : ∀ (main : Cmd), WordR main kdrP (fun vs => vs ≠ [])
      (fun vs out => ∃ v rest, vs = v :: rest ∧ out = rest)
      (fun vs => Kdr * (vsz (vs.headD .nil) + 1)))
    (hmulS : ∀ (main : Cmd), BinOp main mulP (fun _ _ => True) (· * ·) (fun a b => Km2 * isz a * isz b))
    (hfl : ∀ (main : Cmd) (xss : List (List Val)), WordR main flP
      (fun vs => ∃ rest, vs = ofList (xss.map ofList) :: rest)
      (fun vs out => ∃ rest, vs = ofList (xss.map ofList) :: rest ∧ out = ofList xss.flatten :: rest)
      (fun _ => Kfl * (vsz (ofList (xss.map ofList)) + 1)))
    (hblkLen : ∀ (A t B : ℕ) (es : List Val), es.length = A * t * B → 1 ≤ t → 1 ≤ B →
      ∀ blk ∈ blocksOf A t B es, blk.length = t * B)
    (hrowsLen : ∀ (t B : ℕ) (blk : List Val), blk.length = t * B → (rowsOf t B blk).length = t)
    (hchunkId : ∀ (A t B : ℕ) (es : List Val), es.length = A * t * B → 1 ≤ t → 1 ≤ B →
      chunkList (t * B) es = blocksOf A t B es)
    (hslicesId : ∀ (A t B : ℕ) (es : List Val), 1 ≤ A → 1 ≤ t → 1 ≤ B → es.length = A * t * B →
      List.flatten (HvdH.slices A t B es) =
        ((blocksOf A t B es).map (fun blk => (cols (rowsOf t B blk)).flatten)).flatten)
    (hszBlkEl : ∀ (A t B L : ℕ) (es : List Val), es.length = A * t * B → 1 ≤ t → 1 ≤ B →
      (∀ x ∈ es, vsz x ≤ L) → ∀ blk ∈ blocksOf A t B es, ∀ x ∈ blk, vsz x ≤ L)
    (hszBlk : ∀ (A t B L : ℕ) (es : List Val), es.length = A * t * B → 1 ≤ t → 1 ≤ B →
      (∀ x ∈ es, vsz x ≤ L) → ∀ blk ∈ blocksOf A t B es, vsz (ofList blk) ≤ t * B * (L + 1) + 1)
    (hszLeaf : ∀ (A t B L : ℕ) (es : List Val), es.length = A * t * B → 1 ≤ t → 1 ≤ B →
      (∀ x ∈ es, vsz x ≤ L) → ∀ blk ∈ blocksOf A t B es,
        vsz (stateVal ((rowsOf t B blk).map exploded)) ≤ t * B * (L + 1) + 3 * (t * B) + t + 2)
    (hszMerged : ∀ (t B L : ℕ) (blk : List Val), 1 ≤ t → blk.length = t * B →
      (∀ x ∈ blk, vsz x ≤ L) →
      vsz (stateVal (mAll ((rowsOf t B blk).map exploded))) ≤ t * B * (L + 1) + 3 * (t * B) + t + 3)
    (hszArr1 : ∀ (A t B L : ℕ) (es : List Val), es.length = A * t * B → 1 ≤ t → 1 ≤ B →
      (∀ x ∈ es, vsz x ≤ L) → vsz (ofList ((blocksOf A t B es).map ofList)) ≤
        A * (t * B * (L + 1) + 2) + 1)
    (hszArr2 : ∀ (A t B L : ℕ) (es : List Val), es.length = A * t * B → 1 ≤ t → 1 ≤ B →
      (∀ x ∈ es, vsz x ≤ L) → vsz (ofList ((blocksOf A t B es).map
        (fun blk => stateVal ((rowsOf t B blk).map exploded)))) ≤
        A * (t * B * (L + 1) + 3 * (t * B) + t + 3) + 1)
    (hszOut : ∀ (A t B L : ℕ) (es : List Val), es.length = A * t * B → 1 ≤ t → 1 ≤ B →
      (∀ x ∈ es, vsz x ≤ L) →
      vsz (ofList (List.flatten (HvdH.slices A t B es))) ≤ A * t * B * (L + 1) + 1) :
    HasAxisTranspose := by
  obtain ⟨combL, KmlL, hleafPh⟩ := leafPhase hleaf
  obtain ⟨combM, KmlM, hmrgPh⟩ := mergePhase hmrg
  obtain ⟨combI, Kni, hifnil⟩ := Work.Kernel.kernelLib.ifNil
  obtain ⟨pushP, Kpv, hpush⟩ := Work.Kernel.kernelLib.pushVal
  set Cs : ℕ := 1000 * (Kc + Kl + Km + Kpk + Krl + Kdr + Kfl + Km2 + Kni + Kpv + KmlL + KmlM + 1)
    with hCsDef
  refine ⟨combI (pushP Val.nil)
    (progParam mulP chunkP kdrP pickP rollP ;;; progArr leafP mrgP combL combM ;;; progFlat flP rollP),
    100 * Cs, ?_⟩
  intro main A t B es L rest hlen hL
  -- the empty branch
  have hbr1 : ofList es = Val.nil → WordR main (pushP Val.nil)
      (fun vs => vs = .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: rest)
      (fun _ out => out = ofList (List.flatten (HvdH.slices A t B es)) ::
        .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: rest)
      (fun _ => Kpv * (vsz Val.nil + 1)) := by
    intro hnil
    have hes : es = [] := ofList_inj hnil
    subst hes
    have h0 : A * t * B = 0 := hlen.symm
    exact emptyBranch (fun v => hpush main v) A t B h0
      (.int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: rest) le_rfl
  -- the nonempty branch
  have hbr2 : ofList es ≠ Val.nil → WordR main
      (progParam mulP chunkP kdrP pickP rollP ;;; progArr leafP mrgP combL combM ;;; progFlat flP rollP)
      (fun vs => vs = ofList es :: .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: rest)
      (fun _ out => out = ofList (List.flatten (HvdH.slices A t B es)) ::
        .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: rest)
      (fun _ => 11 * bd Cs A t B L) := by
    intro hne
    have hne' : es ≠ [] := by rintro rfl; exact hne rfl
    have hAtB : 1 ≤ A * t * B := by
      have hpos : 0 < es.length := List.length_pos_iff.mpr hne'
      rw [hlen] at hpos; omega
    have hA : 1 ≤ A := by
      rcases Nat.eq_zero_or_pos A with h | h
      · subst h; simp at hAtB
      · exact h
    have ht : 1 ≤ t := by
      rcases Nat.eq_zero_or_pos t with h | h
      · subst h; simp at hAtB
      · exact h
    have hB : 1 ≤ B := by
      rcases Nat.eq_zero_or_pos B with h | h
      · subst h; simp at hAtB
      · exact h
    have hblksLen : (blocksOf A t B es).length = A := by simp [blocksOf]
    have hcs1 : 1000 * (Kc + Kpk + Krl + Kdr + Km2 + 1) ≤ Cs := by
      rw [hCsDef]; omega
    have hcs2 : 1000 * (Kl + Km + KmlL + KmlM + 1) ≤ Cs := by
      rw [hCsDef]; omega
    have hcs3 : 1000 * (Kfl + Krl + 1) ≤ Cs := by
      rw [hCsDef]; omega
    have hT4 : WordR main (progParam mulP chunkP kdrP pickP rollP)
        (fun vs => vs = st0 es A t B rest) (fun _ out => out = st4 A t B es rest)
        (fun _ => 4 * bd Cs A t B L) :=
      axisStepParam (hchunk main) (hpick main) (hroll main) (hkdr main) (hmulS main) hcs1
        A t B L es rest hlen hL hA ht hB (hchunkId A t B es hlen ht hB)
        (hszArr1 A t B L es hlen ht hB hL)
    have hT6 : WordR main (progArr leafP mrgP combL combM)
        (fun vs => vs = st4 A t B es rest) (fun _ out => out = st6 A t B es rest)
        (fun _ => 2 * bd Cs A t B L) :=
      axisStepArr (show LeafPhStmt main leafP combL Kl KmlL from hleafPh main)
        (show MergePhStmt main mrgP combM Km KmlM from hmrgPh main) hcs2
        A t B L es rest hlen hL hA ht hB hblksLen (hblkLen A t B es hlen ht hB) hrowsLen
        (hszBlkEl A t B L es hlen ht hB hL) (hszBlk A t B L es hlen ht hB hL)
        (hszLeaf A t B L es hlen ht hB hL) hszMerged
    have hT11 : WordR main (progFlat flP rollP)
        (fun vs => vs = st6 A t B es rest) (fun _ out => out = st11 A t B es rest)
        (fun _ => 5 * bd Cs A t B L) :=
      axisStepFlat (hfl main) (hroll main) hcs3 A t B L es rest hlen hL hA ht hB hblksLen
        (hblkLen A t B es hlen ht hB) hrowsLen (hszBlkEl A t B L es hlen ht hB hL) hszMerged
        (hslicesId A t B es hA ht hB hlen) (hszOut A t B L es hlen ht hB hL)
    have hPA := MrgKit.WordR_seqC hT4 hT6
    have hPAF := MrgKit.WordR_seqC hPA hT11
    have hcost : 4 * bd Cs A t B L + 2 * bd Cs A t B L + 5 * bd Cs A t B L
        ≤ 11 * bd Cs A t B L := by omega
    exact MrgKit.WordR_weaken hPAF (fun _ hv => hv) (fun _ _ _ hq => hq) (fun _ _ => hcost)
  have hbranch := hifnil main (pushP Val.nil)
    (progParam mulP chunkP kdrP pickP rollP ;;; progArr leafP mrgP combL combM ;;; progFlat flP rollP)
    (ofList es) (.int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: rest)
    (fun out => out = ofList (List.flatten (HvdH.slices A t B es)) ::
      .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: rest)
    (fun out => out = ofList (List.flatten (HvdH.slices A t B es)) ::
      .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: rest)
    (Kpv * (vsz Val.nil + 1)) (11 * bd Cs A t B L) hbr1 hbr2
  refine MrgKit.WordR_weaken hbranch (fun _ hv => hv) (fun vs out hv hq => ?_) (fun _ _ => ?_)
  · by_cases h : ofList es = Val.nil
    · exact hq.1 h
    · exact hq.2 h
  · have hCsK : Kni ≤ Cs := by rw [hCsDef]; omega
    have hCsP : Kpv ≤ Cs := by rw [hCsDef]; omega
    have hbd1 : Cs ≤ bd Cs A t B L := by
      rw [bd]
      exact Nat.le_mul_of_pos_right Cs (by omega)
    have hnil : vsz Val.nil = 1 := by simp [vsz, Val.enc]
    rw [hnil, tgt_final]
    omega

theorem axisTranspose : Work.SynFFT.HasAxisTranspose := by
  obtain ⟨chunkP, Kc, hchunk0⟩ := Work.Resample.chunkWordPB
  have hchunk : ∀ (main : Cmd) (S : ℕ) (xs : List Val) (rest : List Val), 1 ≤ S → S ∣ xs.length →
      WordR main chunkP (fun vs => vs = .int (S : ℤ) :: ofList xs :: rest)
        (fun _ out => out = .int (S : ℤ) :: ofList ((chunkList S xs).map ofList) :: rest)
        (fun _ => Kc * (vsz (ofList xs) + 1) +
          Kc * ((xs.length / S + 1) * (isz (S : ℤ) + 1) + 1)) := by
    intro main S xs rest h1 h2
    simpa only [Work.Resample.PB.blkVal] using hchunk0 main S xs rest h1 h2
  obtain ⟨leafP, Kl, hleaf⟩ := axisLeaf
  obtain ⟨mrgP, Km, hmrg⟩ := axisMerge
  obtain ⟨pickP, Kpk, hpick⟩ := Work.Kernel.kernelLib.pick
  obtain ⟨rollP, Krl, hroll⟩ := Work.Kernel.kernelLib.roll
  obtain ⟨kdrP, Kdr, hkdr⟩ := Work.Kernel.kernelLib.drop
  obtain ⟨mulP, Km2, hmulS⟩ := Work.IntLib.mulSWord
  obtain ⟨flP, Kfl, hfl⟩ := Work.SynFFT.AxFlat.axFlattenWord
  obtain ⟨hSl1, hSl2, hSl3, hSl4, hSl5, hSl6, hSl7⟩ := axisSlices
  obtain ⟨hSz1, hSz2, hSz3, hSz4, hSz5, hSz6, hSz7⟩ := axisSizes
  exact mainPath hchunk hleaf hmrg hpick hroll hkdr hmulS hfl
    hSl2 hSl4 hSl3 hSl7 hSz1 hSz2 hSz3 hSz4 hSz5 hSz6 hSz7

end Work.SynFFT
