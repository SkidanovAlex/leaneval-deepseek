import Mathlib
import Submission.Work.SynFFT.axisKit
import Submission.Work.Kernel.kernelLib
import Submission.Work.SynFFT.mrgBlkDefs

/-!
# The length test of the `axisMerge` loop

`Work.SynFFT.lenTestWord`: from `stateVal Gs :: rest` (a list of groups) push the flag `int 0` if the
list has at most one element and `int 1` if it has at least two, in time `O (vsz (stateVal Gs))`,
leaving `stateVal Gs` itself on top of the stack (below the flag).

The program is built at the `WordR` level from the unconditional kernel library
(`Work.Kernel.kernelLib`): `dup` the list value, `ifNil` the copy (if it is `nil` the list is empty,
so push `int 0`), otherwise `unconsV` it, `drop` the exposed head group and `ifNil` the exposed tail
(if that tail is `nil` the list had exactly one element, so push `int 0`; otherwise `drop` the tail
and push `int 1`).  All branch costs are instance-dependent constants.
-/

set_option autoImplicit false

namespace Work.SynFFT

open HvdH

local infixr:68 " ;;; " => HvdH.Cmd.seq

/-! ### Facts about `stateVal` and `vsz` -/

theorem stateVal_cons (G : List (List Val)) (Gs : List (List (List Val))) :
    stateVal (G :: Gs) = Val.cons (grpVal G) (stateVal Gs) := rfl

theorem stateVal_nil_iff (Gs : List (List (List Val))) : stateVal Gs = Val.nil ↔ Gs = [] := by
  cases Gs with
  | nil => simp [stateVal, ofList]
  | cons G Gs =>
    rw [stateVal_cons]
    constructor
    · intro h; nomatch h
    · intro h; nomatch h

theorem stateVal_ne_nil_iff (Gs : List (List (List Val))) : stateVal Gs ≠ Val.nil ↔ Gs ≠ [] := by
  simp only [ne_eq, stateVal_nil_iff]

theorem vsz_stateVal_cons (G : List (List Val)) (Gs : List (List (List Val))) :
    vsz (stateVal (G :: Gs)) = vsz (grpVal G) + vsz (stateVal Gs) + 1 := by
  rw [stateVal_cons]; exact MrgKit.vsz_cons' (grpVal G) (stateVal Gs)

@[simp] theorem vsz_stateVal_nil : vsz (stateVal ([] : List (List (List Val)))) = 1 := rfl

@[simp] theorem vsz_val_nil : vsz (Val.nil) = 1 := rfl

@[simp] theorem vsz_int_zero : vsz (Val.int 0) = 2 := by
  rw [MrgKit.vsz_int', isz, Int.natAbs_zero, Nat.size_zero]

@[simp] theorem vsz_int_one : vsz (Val.int 1) = 3 := by
  rw [MrgKit.vsz_int', isz, Int.natAbs_one, Nat.size_one]

/-- The postcondition of the length test: the flag `int 0` when `Gs` has at most one element and
`int 1` when it has at least two, the list `stateVal Gs` itself being left on the stack. -/
def lenTestPost (Gs : List (List (List Val))) (rest : List Val) (out : List Val) : Prop :=
  (Gs.length ≤ 1 → out = Val.int 0 :: stateVal Gs :: rest) ∧
  (2 ≤ Gs.length → out = Val.int 1 :: stateVal Gs :: rest)

/-- The `ifNil` combinator of `Work.Kernel.kernelLib`, specialised to a single postcondition `Q`
for both branches. -/
theorem lenTest_ifNil {main : Cmd} {izC : Cmd → Cmd → Cmd} {Ki : ℕ}
    (hiz : ∀ (q₁ q₂ : Cmd) (v : Val) (rest : List Val) (Q₁ Q₂ : List Val → Prop) (c₁ c₂ : ℕ),
      (v = Val.nil → WordR main q₁ (fun vs => vs = rest) (fun _ out => Q₁ out) (fun _ => c₁)) →
      (v ≠ Val.nil → WordR main q₂ (fun vs => vs = v :: rest) (fun _ out => Q₂ out) (fun _ => c₂)) →
      WordR main (izC q₁ q₂) (fun vs => vs = v :: rest)
        (fun _ out => (v = Val.nil → Q₁ out) ∧ (v ≠ Val.nil → Q₂ out)) (fun _ => Ki + max c₁ c₂)) :
    ∀ (q₁ q₂ : Cmd) (v : Val) (rest : List Val) (Q : List Val → Prop) (c₁ c₂ : ℕ),
      (v = Val.nil → WordR main q₁ (fun vs => vs = rest) (fun _ out => Q out) (fun _ => c₁)) →
      (v ≠ Val.nil → WordR main q₂ (fun vs => vs = v :: rest) (fun _ out => Q out) (fun _ => c₂)) →
      WordR main (izC q₁ q₂) (fun vs => vs = v :: rest) (fun _ out => Q out)
        (fun _ => Ki + max c₁ c₂) := by
  intro q₁ q₂ v rest Q c₁ c₂ h₁ h₂
  refine MrgKit.WordR_weaken (hiz q₁ q₂ v rest Q Q c₁ c₂ h₁ h₂) (fun vs h => h) ?_
    (fun vs _ => le_rfl)
  intro vs out _ hq
  by_cases hv : v = Val.nil
  · exact hq.1 hv
  · exact hq.2 hv

/-- Chain a concretised word whose postcondition names the resulting stack with a word whose
postcondition is a general predicate `Q` (the `WordR_seqC` of `MrgKit`, generalised in its second
argument). -/
theorem lenTest_seqC {main : Cmd} {p q : Cmd} {A B : List Val} {Q : List Val → Prop} {c1 c2 : ℕ}
    (h1 : WordR main p (fun vs => vs = A) (fun _ out => out = B) (fun _ => c1))
    (h2 : WordR main q (fun vs => vs = B) (fun _ out => Q out) (fun _ => c2)) :
    WordR main (p ;;; q) (fun vs => vs = A) (fun _ out => Q out) (fun _ => c1 + c2) := by
  refine MrgKit.WordR_weaken (Work.Kernel.WordR_seq h1 h2 ?_) (fun vs h => h) ?_
    (fun vs _ => le_rfl)
  · intro vs mid hvs hQ
    exact ⟨hQ, le_rfl⟩
  · intro vs out _ hq
    obtain ⟨mid, -, hpost⟩ := hq
    exact hpost

-- the length test of the axisMerge loop. From stateVal Gs :: rest (a list of groups) push the flag
-- int 0 if the list has ≤ 1 element and int 1 if it has ≥ 2, in time O(vsz (stateVal Gs)), leaving
-- stateVal Gs itself on top of the stack. Suggested: build it at the WordR level from the
-- unconditional result Work.Kernel.kernelLib (dup, ifNil, unconsV, drop, pushVal, seq, conseq): dup
-- the list value, ifNil (nil = empty list, so push int 0), otherwise unconsV the copy, drop the
-- exposed head group, and ifNil the exposed tail (nil means length 1, so push int 0; else drop the
-- tail and push int 1). All branch costs are instance-dependent constants.
theorem lenTestWord : ∃ (prog : HvdH.Cmd) (K : ℕ),
    ∀ (main : HvdH.Cmd) (Gs : List (List (List HvdH.Val))) (rest : List HvdH.Val),
      HvdH.WordR main prog
        (fun vs => vs = Work.SynFFT.stateVal Gs :: rest)
        (fun _ out => (Gs.length ≤ 1 → out = HvdH.Val.int 0 :: Work.SynFFT.stateVal Gs :: rest) ∧
                      (2 ≤ Gs.length → out = HvdH.Val.int 1 :: Work.SynFFT.stateVal Gs :: rest))
        (fun _ => K * (HvdH.vsz (Work.SynFFT.stateVal Gs) + 1) + K) := by
  obtain ⟨dupP, Kd, hdup⟩ := Work.Kernel.dup
  obtain ⟨izC, Ki, hiz⟩ := Work.Kernel.ifNil
  obtain ⟨uncP, Kuc, hunc⟩ := Work.Kernel.unconsV
  obtain ⟨kdrP, Kdr, hkdr⟩ := Work.Kernel.dropValue
  obtain ⟨pushP, Kpv, hpush⟩ := Work.Kernel.kernelLib_pushVal
  refine ⟨dupP ;;; izC (pushP (Val.int 0))
      (uncP ;;; (kdrP ;;; izC (pushP (Val.int 0)) (kdrP ;;; pushP (Val.int 1)))),
    8 * (Kd + Kdr + Ki + Kuc + Kpv + 1), ?_⟩
  intro main Gs rest
  cases Gs with
  | nil =>
    -- `stateVal [] = nil`: the outer `ifNil` pops it and pushes `int 0`
    have hq₁ : stateVal ([] : List (List (List Val))) = Val.nil →
        WordR main (pushP (Val.int 0)) (fun vs => vs = stateVal [] :: rest)
          (fun _ out => lenTestPost [] rest out) (fun _ => Kpv * (vsz (Val.int 0) + 1)) := by
      intro _
      refine MrgKit.WordR_weaken
        (MrgKit.pushStep (hpush main) (Val.int 0) (stateVal ([] : List (List (List Val))) :: rest) _
          le_rfl) (fun vs h => h) ?_ (fun vs _ => le_rfl)
      intro vs out _ hout
      rw [hout]
      exact ⟨fun _ => rfl, fun h => absurd h (by simp)⟩
    have hq₂ : stateVal ([] : List (List (List Val))) ≠ Val.nil →
        WordR main (uncP ;;; (kdrP ;;; izC (pushP (Val.int 0)) (kdrP ;;; pushP (Val.int 1))))
          (fun vs => vs = stateVal [] :: stateVal [] :: rest)
          (fun _ out => lenTestPost [] rest out) (fun _ => 0) :=
      fun h => absurd ((stateVal_nil_iff ([] : List (List (List Val)))).mpr rfl) h
    have hib : WordR main (izC (pushP (Val.int 0))
          (uncP ;;; (kdrP ;;; izC (pushP (Val.int 0)) (kdrP ;;; pushP (Val.int 1)))))
        (fun vs => vs = stateVal [] :: (stateVal [] :: rest))
        (fun _ out => lenTestPost [] rest out) (fun _ => Ki + max (Kpv * (vsz (Val.int 0) + 1)) 0) :=
      lenTest_ifNil (hiz main) _ _ (stateVal ([] : List (List (List Val)))) (stateVal [] :: rest)
        (lenTestPost [] rest) _ _ hq₁ hq₂
    have hd : WordR main dupP (fun vs => vs = stateVal ([] : List (List (List Val))) :: rest)
        (fun _ out => out = stateVal [] :: stateVal [] :: rest)
        (fun _ => Kd * (vsz (stateVal []) + 1)) :=
      MrgKit.dupStep (hdup main) (stateVal ([] : List (List (List Val)))) rest _ le_rfl
    refine MrgKit.WordR_weaken (lenTest_seqC hd hib) (fun vs h => h) (fun vs out _ h => h) ?_
    intro vs _
    have hmax : max (Kpv * (2 + 1)) 0 = Kpv * (2 + 1) := Nat.max_eq_left (Nat.zero_le _)
    rw [vsz_stateVal_nil, vsz_int_zero, hmax]
    nlinarith
  | cons G Gs' =>
    have hsd : stateVal (G :: Gs') = Val.cons (grpVal G) (stateVal Gs') := stateVal_cons G Gs'
    -- the outer `ifNil` takes the second branch (`stateVal (G :: Gs') ≠ nil` is vacuously
    -- non-`nil`, so the cost of the first branch may be taken to be `0`)
    have hq₁ : stateVal (G :: Gs') = Val.nil →
        WordR main (pushP (Val.int 0)) (fun vs => vs = stateVal (G :: Gs') :: rest)
          (fun _ out => lenTestPost (G :: Gs') rest out) (fun _ => 0) :=
      fun h => absurd h ((stateVal_ne_nil_iff (G :: Gs')).mpr (by simp))
    have hq₂ : stateVal (G :: Gs') ≠ Val.nil →
        WordR main (uncP ;;; (kdrP ;;; izC (pushP (Val.int 0)) (kdrP ;;; pushP (Val.int 1))))
          (fun vs => vs = stateVal (G :: Gs') :: stateVal (G :: Gs') :: rest)
          (fun _ out => lenTestPost (G :: Gs') rest out)
          (fun _ => Kuc + (Kdr * (vsz (grpVal G) + 1) +
            (Ki + max (Kpv * (vsz (Val.int 0) + 1))
              (Kdr * (vsz (stateVal Gs') + 1) + Kpv * (vsz (Val.int 1) + 1))))) := by
      intro _
      simp only [hsd]
      -- expose the head group and its tail with `unconsV`
      have s1 : WordR main uncP
          (fun vs => vs = Val.cons (grpVal G) (stateVal Gs') ::
            (Val.cons (grpVal G) (stateVal Gs') :: rest))
          (fun _ out => out = grpVal G :: stateVal Gs' ::
            (Val.cons (grpVal G) (stateVal Gs') :: rest))
          (fun _ => Kuc) :=
        MrgKit.uncStep (hunc main) (grpVal G) (stateVal Gs')
          (Val.cons (grpVal G) (stateVal Gs') :: rest) _ le_rfl
      -- drop the exposed head group
      have s2 : WordR main kdrP
          (fun vs => vs = grpVal G :: stateVal Gs' ::
            (Val.cons (grpVal G) (stateVal Gs') :: rest))
          (fun _ out => out = stateVal Gs' :: (Val.cons (grpVal G) (stateVal Gs') :: rest))
          (fun _ => Kdr * (vsz (grpVal G) + 1)) := by
        refine MrgKit.WordR_weaken
          (MrgKit.kdropStep (hkdr main)
            (grpVal G :: stateVal Gs' :: (Val.cons (grpVal G) (stateVal Gs') :: rest)) (by simp)
            (Kdr * (vsz (grpVal G) + 1)) (by simp)) (fun vs h => h) ?_ (fun vs _ => le_rfl)
        intro vs out _ hout
        simp [hout]
      -- inner `ifNil` on the exposed tail: `nil` means the list had exactly one element
      have r₁ : stateVal Gs' = Val.nil →
          WordR main (pushP (Val.int 0))
            (fun vs => vs = Val.cons (grpVal G) (stateVal Gs') :: rest)
            (fun _ out => lenTestPost (G :: Gs') rest out) (fun _ => Kpv * (vsz (Val.int 0) + 1)) := by
        intro hnil
        have hGs' : Gs' = [] := (stateVal_nil_iff Gs').mp hnil
        refine MrgKit.WordR_weaken
          (MrgKit.pushStep (hpush main) (Val.int 0)
            (Val.cons (grpVal G) (stateVal Gs') :: rest) _ le_rfl) (fun vs h => h) ?_
          (fun vs _ => le_rfl)
        intro vs out _ hout
        rw [hout]
        refine ⟨fun _ => ?_, fun h => absurd h (by simp [hGs'])⟩
        rw [hsd]
      have r₂ : stateVal Gs' ≠ Val.nil →
          WordR main (kdrP ;;; pushP (Val.int 1))
            (fun vs => vs = stateVal Gs' :: (Val.cons (grpVal G) (stateVal Gs') :: rest))
            (fun _ out => lenTestPost (G :: Gs') rest out)
            (fun _ => Kdr * (vsz (stateVal Gs') + 1) + Kpv * (vsz (Val.int 1) + 1)) := by
        intro hne
        have hne' : Gs' ≠ [] := (stateVal_ne_nil_iff Gs').mp hne
        have hlen : 0 < Gs'.length := List.length_pos_of_ne_nil hne'
        have s2' : WordR main kdrP
            (fun vs => vs = stateVal Gs' :: (Val.cons (grpVal G) (stateVal Gs') :: rest))
            (fun _ out => out = Val.cons (grpVal G) (stateVal Gs') :: rest)
            (fun _ => Kdr * (vsz (stateVal Gs') + 1)) := by
          refine MrgKit.WordR_weaken
            (MrgKit.kdropStep (hkdr main)
              (stateVal Gs' :: (Val.cons (grpVal G) (stateVal Gs') :: rest)) (by simp)
              (Kdr * (vsz (stateVal Gs') + 1)) (by simp)) (fun vs h => h) ?_ (fun vs _ => le_rfl)
          intro vs out _ hout
          simp [hout]
        have s3' : WordR main (pushP (Val.int 1))
            (fun vs => vs = Val.cons (grpVal G) (stateVal Gs') :: rest)
            (fun _ out => lenTestPost (G :: Gs') rest out) (fun _ => Kpv * (vsz (Val.int 1) + 1)) := by
          refine MrgKit.WordR_weaken
            (MrgKit.pushStep (hpush main) (Val.int 1)
              (Val.cons (grpVal G) (stateVal Gs') :: rest) _ le_rfl) (fun vs h => h) ?_
            (fun vs _ => le_rfl)
          intro vs out _ hout
          rw [hout]
          refine ⟨fun h1 => absurd h1 ?_, fun _ => ?_⟩
          · simp only [List.length_cons] at h1; omega
          · rw [← hsd]
        exact lenTest_seqC s2' s3'
      have inner : WordR main (izC (pushP (Val.int 0)) (kdrP ;;; pushP (Val.int 1)))
          (fun vs => vs = stateVal Gs' :: (Val.cons (grpVal G) (stateVal Gs') :: rest))
          (fun _ out => lenTestPost (G :: Gs') rest out)
          (fun _ => Ki + max (Kpv * (vsz (Val.int 0) + 1))
            (Kdr * (vsz (stateVal Gs') + 1) + Kpv * (vsz (Val.int 1) + 1))) :=
        lenTest_ifNil (hiz main) _ _ (stateVal Gs')
          (Val.cons (grpVal G) (stateVal Gs') :: rest) (lenTestPost (G :: Gs') rest) _ _ r₁ r₂
      exact lenTest_seqC s1 (lenTest_seqC s2 inner)
    -- assemble: `dup` then the outer `ifNil`
    have hd : WordR main dupP (fun vs => vs = stateVal (G :: Gs') :: rest)
        (fun _ out => out = stateVal (G :: Gs') :: stateVal (G :: Gs') :: rest)
        (fun _ => Kd * (vsz (stateVal (G :: Gs')) + 1)) :=
      MrgKit.dupStep (hdup main) (stateVal (G :: Gs')) rest _ le_rfl
    have hib : WordR main (izC (pushP (Val.int 0))
          (uncP ;;; (kdrP ;;; izC (pushP (Val.int 0)) (kdrP ;;; pushP (Val.int 1)))))
        (fun vs => vs = stateVal (G :: Gs') :: (stateVal (G :: Gs') :: rest))
        (fun _ out => lenTestPost (G :: Gs') rest out)
        (fun _ => Ki + max 0 (Kuc + (Kdr * (vsz (grpVal G) + 1) +
          (Ki + max (Kpv * (vsz (Val.int 0) + 1))
            (Kdr * (vsz (stateVal Gs') + 1) + Kpv * (vsz (Val.int 1) + 1)))))) :=
      lenTest_ifNil (hiz main) _ _ (stateVal (G :: Gs')) (stateVal (G :: Gs') :: rest)
        (lenTestPost (G :: Gs') rest) 0 _ hq₁ hq₂
    refine MrgKit.WordR_weaken (lenTest_seqC hd hib) (fun vs h => h) (fun vs out _ h => h) ?_
    intro vs _
    rw [vsz_stateVal_cons, vsz_int_zero, vsz_int_one, Nat.max_eq_right (Nat.zero_le _)]
    have hmax : max (Kpv * (2 + 1)) (Kdr * (vsz (stateVal Gs') + 1) + Kpv * (3 + 1)) ≤
        Kpv * (2 + 1) + (Kdr * (vsz (stateVal Gs') + 1) + Kpv * (3 + 1)) := by
      rw [Nat.max_le]
      exact ⟨Nat.le_add_right _ _, Nat.le_add_left _ _⟩
    nlinarith [hmax]

end Work.SynFFT
