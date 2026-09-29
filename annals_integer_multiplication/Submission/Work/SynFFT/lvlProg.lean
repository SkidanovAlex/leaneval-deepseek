import Mathlib
import Submission.Work.SynFFT.lvlKit

/-!
# `Work.SynFFT.lvlProg`: the word for `HasLvlPass`

Building blocks of the program of `Work.SynFFT.hasLvlPass`:

`A :: int m :: int sh :: int sgn :: int r :: int p :: rest`
* `chunksOf m` — the `t/m` blocks of `m` coefficient vectors (values `ofList (cvecs ·)`);
* a `mapList` pass wrapping every block as `cons block (prepVR …)`, where
  `prepVR … = ofList [int p, int r, int sgn, int sh, int m]` carries the five scalar parameters
  into every element of the fold (so that the block word's precondition
  `block :: int m :: int sh :: int sgn :: int r :: int p :: rest` is met);
* a `foldList` over the prepared blocks, accumulating the output blocks on top of an accumulator
  value (`cons`-ing each new block);
* `reverse ; flatten`.

Vocabulary of this file:

* `pM m sh sgn r p` — the five parameters, in order;
* `prepVR m sh sgn r p` — the same five, *reversed*, as one value (un-consing it five times
  recovers `int m, int sh, int sgn, int r, int p`, separated from `nil`);
* `pSz` — a bound on the size of the five parameters;
* `chunkVals m ws` — the value list produced by `chunksOf m` from `cvecs ws`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.SynFFT

open HvdH

local infixr:68 " ;;; " => HvdH.Cmd.seq

/-- The value of one block of coefficient vectors. -/
def bVal (w : List (List (ℤ × ℤ))) : Val := ofList (cvecs w)

/-- The five scalar parameters as a list of values. -/
def pM (m sh : ℕ) (sgn : ℤ) (r p : ℕ) : List Val :=
  [Val.int (m : ℤ), Val.int (sh : ℤ), Val.int sgn, Val.int (r : ℤ), Val.int (p : ℤ)]

/-- The five scalar parameters as one value, *reversed*: un-consing it five times yields
`int m, int sh, int sgn, int r, int p` (followed by a `nil`). -/
def prepVR (m sh : ℕ) (sgn : ℤ) (r p : ℕ) : Val :=
  ofList [Val.int (p : ℤ), Val.int (r : ℤ), Val.int sgn, Val.int (sh : ℤ), Val.int (m : ℤ)]

/-- A bound on `vsz` of the five parameters. -/
def pSz (m sh : ℕ) (sgn : ℤ) (r p : ℕ) : ℕ :=
  isz (m : ℤ) + isz (sh : ℤ) + isz sgn + isz (r : ℤ) + isz (p : ℤ) + 6

/-- The value list produced by `chunksOf m` out of `cvecs ws`. -/
def chunkVals (m : ℕ) (ws : List (List (ℤ × ℤ))) : List Val :=
  (List.range ((cvecs ws).length / m)).map (fun b => ofList (((cvecs ws).drop (b * m)).take m))

theorem pM_unfold (m sh : ℕ) (sgn : ℤ) (r p : ℕ) :
    pM m sh sgn r p
      = .int (m : ℤ) :: .int (sh : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: [] := rfl

theorem prepVR_unfold (m sh : ℕ) (sgn : ℤ) (r p : ℕ) :
    prepVR m sh sgn r p
      = .cons (.int (p : ℤ)) (.cons (.int (r : ℤ)) (.cons (.int sgn)
        (.cons (.int (sh : ℤ)) (.cons (.int (m : ℤ)) .nil)))) := rfl

theorem vsz_prepVR (m sh : ℕ) (sgn : ℤ) (r p : ℕ) :
    vsz (prepVR m sh sgn r p) ≤ pSz m sh sgn r p := by
  rw [prepVR, MrgKit.vsz_ofList]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil, MrgKit.vsz_int']
  rw [pSz]; omega

theorem pSz_eq (m sh : ℕ) (sgn : ℤ) (r p : ℕ) :
    pSz m sh sgn r p
      = isz (m : ℤ) + isz (sh : ℤ) + isz sgn + isz (r : ℤ) + isz (p : ℤ) + 6 := rfl

/-- Size of the value of a list of `m` coefficient vectors in the disc. -/
theorem vsz_ofList_cvecs_le_xlvlProg {m r p : ℕ} {w : List (List (ℤ × ℤ))} (hlen : w.length = m)
    (hind : ∀ x ∈ w, InDiscVec p r x) :
    vsz (ofList (cvecs w)) ≤ 15 * (m + 1) * (r + 1) * (p + 1) := by
  have htake : cws m w 0 = w := by
    simp only [cws, Nat.zero_mul, List.drop_zero]
    rw [← hlen, List.take_length]
  have hlen' : (cws m w 0).length = m := by rw [htake, hlen]
  have hmem : ∀ x ∈ cws m w 0, InDiscVec p r x := by rw [htake]; exact hind
  have h := vsz_blkV_le p r m w 0 hlen' hmem
  rwa [show blkV m w 0 = ofList (cvecs (cws m w 0)) from rfl, htake] at h

/-! ## Small step lemmas -/

theorem pickStepG {main : Cmd} {pickP : ℕ → Cmd} {Kp : ℕ}
    (hpick : ∀ k, WordR main (pickP k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs)
      (fun vs => Kp * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    (k : ℕ) (A : List Val) (hk : k < A.length) (D : ℕ) (hD : Kp * (k + 1) * (((A.take (k + 1)).map vsz).sum + 1) ≤ D) :
    WordR main (pickP k) (fun vs => vs = A) (fun _ out => out = A.getD k .nil :: A) (fun _ => D) :=
  MrgKit.pickStep hpick k A hk D hD

theorem rollStepG {main : Cmd} {rollP : ℕ → Cmd} {Kr : ℕ}
    (hroll : ∀ k, WordR main (rollP k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs.eraseIdx k)
      (fun vs => Kr * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    (k : ℕ) (A : List Val) (hk : k < A.length) (D : ℕ) (hD : Kr * (k + 1) * (((A.take (k + 1)).map vsz).sum + 1) ≤ D) :
    WordR main (rollP k) (fun vs => vs = A) (fun _ out => out = A.getD k .nil :: A.eraseIdx k) (fun _ => D) :=
  MrgKit.rollStep hroll k A hk D hD

theorem swStep {main : Cmd} {swP : Cmd} {Ksw : ℕ}
    (hsw : WordR main swP (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = b :: a :: rest)
      (fun vs => Ksw * (vsz (vs.getD 0 .nil) + vsz (vs.getD 1 .nil) + 1)))
    (a b : Val) (t : List Val) (D : ℕ) (hD : Ksw * (vsz a + vsz b + 1) ≤ D) :
    WordR main swP (fun vs => vs = a :: b :: t) (fun _ out => out = b :: a :: t) (fun _ => D) := by
  refine MrgKit.WordR_conseqC hsw (by simp) ?_ (by simpa using hD)
  intro out hout
  obtain ⟨a', b', r, h1, h2⟩ := hout
  simp only [List.cons.injEq] at h1
  obtain ⟨rfl, rfl, rfl⟩ := h1
  exact h2

theorem drStep {main : Cmd} {drP : Cmd} {Kdr : ℕ}
    (hdr : WordR main drP (fun vs => vs ≠ [])
      (fun vs out => ∃ v rest, vs = v :: rest ∧ out = rest)
      (fun vs => Kdr * (vsz (vs.headD .nil) + 1)))
    (a : Val) (t : List Val) (D : ℕ) (hD : Kdr * (vsz a + 1) ≤ D) :
    WordR main drP (fun vs => vs = a :: t) (fun _ out => out = t) (fun _ => D) := by
  refine MrgKit.WordR_conseqC hdr (by simp) ?_ (by simpa using hD)
  intro out hout
  obtain ⟨v, r, h1, h2⟩ := hout
  simp only [List.cons.injEq] at h1
  obtain ⟨rfl, rfl⟩ := h1
  exact h2

theorem consStep2 {main : Cmd} {consP : Cmd} {Kcv : ℕ}
    (hcons : WordR main consP (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = .cons a b :: rest) (fun _ => Kcv))
    (a b : Val) (t : List Val) (D : ℕ) (hD : Kcv ≤ D) :
    WordR main consP (fun vs => vs = a :: b :: t) (fun _ out => out = .cons a b :: t)
      (fun _ => D) := by
  refine MrgKit.WordR_conseqC hcons (by simp) ?_ hD
  intro out hout
  obtain ⟨a', b', r, h1, h2⟩ := hout
  simp only [List.cons.injEq] at h1
  obtain ⟨rfl, rfl, rfl⟩ := h1
  exact h2

theorem uncStep {main : Cmd} {uncP : Cmd} {Kuc : ℕ}
    (h : WordR main uncP (fun vs => ∃ a b r, vs = .cons a b :: r)
      (fun vs out => ∃ a b r, vs = .cons a b :: r ∧ out = a :: b :: r) (fun _ => Kuc))
    (a b : Val) (t : List Val) (D : ℕ) (hD : Kuc ≤ D) :
    WordR main uncP (fun vs => vs = .cons a b :: t) (fun _ out => out = a :: b :: t)
      (fun _ => D) := by
  refine MrgKit.WordR_conseqC h ⟨a, b, t, rfl⟩ ?_ hD
  intro out hout
  obtain ⟨a', b', r', h1, h2⟩ := hout
  simp only [List.cons.injEq, Val.cons.injEq] at h1
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h1
  exact h2

theorem pushStep2 {main : Cmd} {pushP : Val → Cmd} {Kpv : ℕ}
    (hpush : ∀ v, WordR main (pushP v) (fun _ => True) (fun vs out => out = v :: vs)
      (fun _ => Kpv * (vsz v + 1)))
    (v : Val) (t : List Val) (D : ℕ) (hD : Kpv * (vsz v + 1) ≤ D) :
    WordR main (pushP v) (fun vs => vs = t) (fun _ out => out = v :: t) (fun _ => D) :=
  MrgKit.WordR_conseqC (hpush v) trivial (fun out hout => hout) hD


/-! ## The setup: chunk, copy the parameters, wrap every block -/

/-- The input list of coefficient vectors, as one value. -/
def aV (ws : List (List (ℤ × ℤ))) : Val := ofList (cvecs ws)

/-- The chunk list, as one value. -/
def sqV (m : ℕ) (ws : List (List (ℤ × ℤ))) : Val := ofList (chunkVals m ws)

theorem vsz_nil : vsz (Val.nil) = 1 := rfl

theorem isz_le_pSz_m (m sh : ℕ) (sgn : ℤ) (r p : ℕ) : isz (m : ℤ) ≤ pSz m sh sgn r p := by
  rw [pSz]; omega
theorem isz_le_pSz_sh (m sh : ℕ) (sgn : ℤ) (r p : ℕ) : isz (sh : ℤ) ≤ pSz m sh sgn r p := by
  rw [pSz]; omega
theorem isz_le_pSz_sgn (m sh : ℕ) (sgn : ℤ) (r p : ℕ) : isz sgn ≤ pSz m sh sgn r p := by
  rw [pSz]; omega
theorem isz_le_pSz_r (m sh : ℕ) (sgn : ℤ) (r p : ℕ) : isz (r : ℤ) ≤ pSz m sh sgn r p := by
  rw [pSz]; omega
theorem isz_le_pSz_p (m sh : ℕ) (sgn : ℤ) (r p : ℕ) : isz (p : ℤ) ≤ pSz m sh sgn r p := by
  rw [pSz]; omega

/-- Cost of the setup chain. -/
def lvlSetupCost (Kp Kcs Kpv Ksw Kcv : ℕ) (m sh : ℕ) (sgn : ℤ) (r p : ℕ)
    (ws : List (List (ℤ × ℤ))) : ℕ :=
  Kp * 2 * (vsz (ofList (cvecs ws)) + isz (m : ℤ) + 1)
  + Kcs * (vsz (ofList (cvecs ws)) + ((cvecs ws).length / m + 1) * isz (m : ℤ) + 1)
  + 5 * (Kp * 6 * (vsz (ofList (chunkVals m ws)) + pSz m sh sgn r p + 1))
  + Kpv * 2
  + 5 * (Ksw * (4 * pSz m sh sgn r p + 8) + Kcv)
  + Ksw * (vsz (ofList (chunkVals m ws)) + pSz m sh sgn r p + 1)

theorem lvlSetup {main : Cmd} {pickP : ℕ → Cmd} {csP : Cmd} {pushP : Val → Cmd}
    {swP consP : Cmd} {Kp Kcs Kpv Ksw Kcv : ℕ}
    (hpick : ∀ k, WordR main (pickP k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs)
      (fun vs => Kp * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    (hcs : ∀ (m : ℕ) (xs : List Val), 1 ≤ m → m ∣ xs.length → WordR main csP
      (fun vs => ∃ rest, vs = .int (m : ℤ) :: ofList xs :: rest)
      (fun vs out => ∃ rest, vs = .int (m : ℤ) :: ofList xs :: rest ∧
        out = ofList ((List.range (xs.length / m)).map fun i => ofList ((xs.drop (i * m)).take m)) :: rest)
      (fun _ => Kcs * (vsz (ofList xs) + (xs.length / m + 1) * isz (m : ℤ) + 1)))
    (hpush : ∀ v, WordR main (pushP v) (fun _ => True) (fun vs out => out = v :: vs)
      (fun _ => Kpv * (vsz v + 1)))
    (hsw : WordR main swP (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = b :: a :: rest)
      (fun vs => Ksw * (vsz (vs.getD 0 .nil) + vsz (vs.getD 1 .nil) + 1)))
    (hcons : WordR main consP (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = .cons a b :: rest) (fun _ => Kcv))
    (m sh : ℕ) (sgn : ℤ) (r p : ℕ) (ws : List (List (ℤ × ℤ))) (rest : List Val)
    (hm1 : 1 ≤ m) (hdvd : m ∣ (cvecs ws).length) :
    WordR main (pickP 1 ;;; csP ;;; pickP 5 ;;; pickP 5 ;;; pickP 5 ;;; pickP 5 ;;; pickP 5 ;;;
      pushP .nil ;;; swP ;;; consP ;;; swP ;;; consP ;;; swP ;;; consP ;;; swP ;;; consP ;;; swP ;;; consP ;;;
      swP)
      (fun vs => vs = ofList (cvecs ws) :: pM m sh sgn r p ++ rest)
      (fun _ out => out = ofList (chunkVals m ws) :: prepVR m sh sgn r p :: pM m sh sgn r p ++ rest)
      (fun _ => lvlSetupCost Kp Kcs Kpv Ksw Kcv m sh sgn r p ws) := by
  have hP5len : (pM m sh sgn r p).length = 5 := rfl
  -- ### step 1
  have e1 : WordR main (pickP 1) (fun vs => vs = ofList (cvecs ws) :: pM m sh sgn r p ++ rest)
      (fun _ out => out = .int (m : ℤ) :: ofList (cvecs ws) :: pM m sh sgn r p ++ rest)
      (fun _ => Kp * 2 * (vsz (ofList (cvecs ws)) + isz (m : ℤ) + 1)) := by
    refine pickStepG hpick 1 (ofList (cvecs ws) :: pM m sh sgn r p ++ rest) ?_ _ (le_of_eq ?_)
    · simp only [List.length_cons, List.length_append, hP5len]; omega
    · simp only [List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero,
        List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, List.getD_cons_zero,
        List.length_cons, pM, MrgKit.vsz_int']
      ring
  -- ### step 2
  have e2 : WordR main csP (fun vs => vs = .int (m : ℤ) :: ofList (cvecs ws) :: pM m sh sgn r p ++ rest)
      (fun _ out => out = ofList (chunkVals m ws) :: pM m sh sgn r p ++ rest)
      (fun _ => Kcs * (vsz (ofList (cvecs ws)) + ((cvecs ws).length / m + 1) * isz (m : ℤ) + 1)) := by
    refine MrgKit.WordR_conseqC (hcs m (cvecs ws) hm1 hdvd) ⟨pM m sh sgn r p ++ rest, rfl⟩ ?_
      le_rfl
    intro out hout
    obtain ⟨red, h1, h2⟩ := hout
    have hr : pM m sh sgn r p ++ rest = red := by
      have h : ofList (cvecs ws) :: pM m sh sgn r p ++ rest = ofList (cvecs ws) :: red :=
        (List.cons.inj h1).2
      exact (List.cons.inj h).2
    rw [← hr] at h2
    exact h2
  -- ### steps 3-7: five copies
  have e3 : WordR main (pickP 5) (fun vs => vs = ofList (chunkVals m ws) :: pM m sh sgn r p ++ rest)
      (fun _ out => out = .int (p : ℤ) :: ofList (chunkVals m ws) :: pM m sh sgn r p ++ rest)
      (fun _ => Kp * 6 * (vsz (ofList (chunkVals m ws)) + pSz m sh sgn r p + 1)) := by
    refine pickStepG hpick 5 (ofList (chunkVals m ws) :: pM m sh sgn r p ++ rest) ?_ _ ?_
    · simp only [List.length_cons, List.length_append, hP5len]; omega
    · simp only [List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero,
        List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, List.getD_cons_zero,
        List.getD_cons_succ, pM, pSz, MrgKit.vsz_int']
      exact Nat.mul_le_mul_left _ (by omega)
  have e4 : WordR main (pickP 5)
      (fun vs => vs = .int (p : ℤ) :: ofList (chunkVals m ws) :: pM m sh sgn r p ++ rest)
      (fun _ out => out = .int (r : ℤ) :: .int (p : ℤ) :: ofList (chunkVals m ws)
        :: pM m sh sgn r p ++ rest)
      (fun _ => Kp * 6 * (vsz (ofList (chunkVals m ws)) + pSz m sh sgn r p + 1)) := by
    refine pickStepG hpick 5
      (.int (p : ℤ) :: ofList (chunkVals m ws) :: pM m sh sgn r p ++ rest) ?_ _ ?_
    · simp only [List.length_cons, List.length_append, hP5len]; omega
    · simp only [List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero,
        List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, List.getD_cons_zero,
        List.getD_cons_succ, pM, pSz, MrgKit.vsz_int']
      exact Nat.mul_le_mul_left _ (by omega)
  have e5 : WordR main (pickP 5)
      (fun vs => vs = .int (r : ℤ) :: .int (p : ℤ) :: ofList (chunkVals m ws)
        :: pM m sh sgn r p ++ rest)
      (fun _ out => out = .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: ofList (chunkVals m ws)
        :: pM m sh sgn r p ++ rest)
      (fun _ => Kp * 6 * (vsz (ofList (chunkVals m ws)) + pSz m sh sgn r p + 1)) := by
    refine pickStepG hpick 5
      (.int (r : ℤ) :: .int (p : ℤ) :: ofList (chunkVals m ws) :: pM m sh sgn r p ++ rest) ?_ _ ?_
    · simp only [List.length_cons, List.length_append, hP5len]; omega
    · simp only [List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero,
        List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, List.getD_cons_zero,
        List.getD_cons_succ, pM, pSz, MrgKit.vsz_int']
      exact Nat.mul_le_mul_left _ (by omega)
  have e6 : WordR main (pickP 5)
      (fun vs => vs = .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: ofList (chunkVals m ws)
        :: pM m sh sgn r p ++ rest)
      (fun _ out => out = .int (sh : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ)
        :: ofList (chunkVals m ws) :: pM m sh sgn r p ++ rest)
      (fun _ => Kp * 6 * (vsz (ofList (chunkVals m ws)) + pSz m sh sgn r p + 1)) := by
    refine pickStepG hpick 5
      (.int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: ofList (chunkVals m ws)
        :: pM m sh sgn r p ++ rest) ?_ _ ?_
    · simp only [List.length_cons, List.length_append, hP5len]; omega
    · simp only [List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero,
        List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, List.getD_cons_zero,
        List.getD_cons_succ, pM, pSz, MrgKit.vsz_int']
      exact Nat.mul_le_mul_left _ (by omega)
  have e7 : WordR main (pickP 5)
      (fun vs => vs = .int (sh : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ)
        :: ofList (chunkVals m ws) :: pM m sh sgn r p ++ rest)
      (fun _ out => out = .int (m : ℤ) :: .int (sh : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ)
        :: ofList (chunkVals m ws) :: pM m sh sgn r p ++ rest)
      (fun _ => Kp * 6 * (vsz (ofList (chunkVals m ws)) + pSz m sh sgn r p + 1)) := by
    refine pickStepG hpick 5
      (.int (sh : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: ofList (chunkVals m ws)
        :: pM m sh sgn r p ++ rest) ?_ _ ?_
    · simp only [List.length_cons, List.length_append, hP5len]; omega
    · simp only [List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero,
        List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, List.getD_cons_zero,
        List.getD_cons_succ, pM, pSz, MrgKit.vsz_int']
      exact Nat.mul_le_mul_left _ (by omega)
  -- ### step 8: push nil
  have e8 : WordR main (pushP .nil)
      (fun vs => vs = .int (m : ℤ) :: .int (sh : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ)
        :: ofList (chunkVals m ws) :: pM m sh sgn r p ++ rest)
      (fun _ out => out = .nil :: .int (m : ℤ) :: .int (sh : ℤ) :: .int sgn :: .int (r : ℤ)
        :: .int (p : ℤ) :: ofList (chunkVals m ws) :: pM m sh sgn r p ++ rest)
      (fun _ => Kpv * 2) := by
    refine pushStep2 hpush .nil _ _ ?_
    simp only [vsz_nil]
    exact Nat.mul_le_mul_left _ (by omega)
  -- ### the five swap/cons rounds
  have e9 : WordR main swP
      (fun vs => vs = .nil :: .int (m : ℤ) :: .int (sh : ℤ) :: .int sgn :: .int (r : ℤ)
        :: .int (p : ℤ) :: ofList (chunkVals m ws) :: pM m sh sgn r p ++ rest)
      (fun _ out => out = .int (m : ℤ) :: .nil :: .int (sh : ℤ) :: .int sgn :: .int (r : ℤ)
        :: .int (p : ℤ) :: ofList (chunkVals m ws) :: pM m sh sgn r p ++ rest)
      (fun _ => Ksw * (4 * pSz m sh sgn r p + 8)) := by
    refine swStep hsw .nil (.int (m : ℤ)) _ _ ?_
    simp only [vsz_nil, MrgKit.vsz_int', MrgKit.vsz_cons', pSz]
    exact Nat.mul_le_mul_left _ (by omega)
  have e10 : WordR main consP
      (fun vs => vs = .int (m : ℤ) :: .nil :: .int (sh : ℤ) :: .int sgn :: .int (r : ℤ)
        :: .int (p : ℤ) :: ofList (chunkVals m ws) :: pM m sh sgn r p ++ rest)
      (fun _ out => out = .cons (.int (m : ℤ)) .nil :: .int (sh : ℤ) :: .int sgn :: .int (r : ℤ)
        :: .int (p : ℤ) :: ofList (chunkVals m ws) :: pM m sh sgn r p ++ rest)
      (fun _ => Kcv) := consStep2 hcons _ _ _ _ le_rfl
  have e11 : WordR main swP
      (fun vs => vs = .cons (.int (m : ℤ)) .nil :: .int (sh : ℤ) :: .int sgn :: .int (r : ℤ)
        :: .int (p : ℤ) :: ofList (chunkVals m ws) :: pM m sh sgn r p ++ rest)
      (fun _ out => out = .int (sh : ℤ) :: .cons (.int (m : ℤ)) .nil :: .int sgn :: .int (r : ℤ)
        :: .int (p : ℤ) :: ofList (chunkVals m ws) :: pM m sh sgn r p ++ rest)
      (fun _ => Ksw * (4 * pSz m sh sgn r p + 8)) := by
    refine swStep hsw _ (.int (sh : ℤ)) _ _ ?_
    simp only [vsz_nil, MrgKit.vsz_int', MrgKit.vsz_cons', pSz]
    exact Nat.mul_le_mul_left _ (by omega)
  have e12 : WordR main consP
      (fun vs => vs = .int (sh : ℤ) :: .cons (.int (m : ℤ)) .nil :: .int sgn :: .int (r : ℤ)
        :: .int (p : ℤ) :: ofList (chunkVals m ws) :: pM m sh sgn r p ++ rest)
      (fun _ out => out = .cons (.int (sh : ℤ)) (.cons (.int (m : ℤ)) .nil) :: .int sgn
        :: .int (r : ℤ) :: .int (p : ℤ) :: ofList (chunkVals m ws) :: pM m sh sgn r p ++ rest)
      (fun _ => Kcv) := consStep2 hcons _ _ _ _ le_rfl
  have e13 : WordR main swP
      (fun vs => vs = .cons (.int (sh : ℤ)) (.cons (.int (m : ℤ)) .nil) :: .int sgn :: .int (r : ℤ)
        :: .int (p : ℤ) :: ofList (chunkVals m ws) :: pM m sh sgn r p ++ rest)
      (fun _ out => out = .int sgn :: .cons (.int (sh : ℤ)) (.cons (.int (m : ℤ)) .nil)
        :: .int (r : ℤ) :: .int (p : ℤ) :: ofList (chunkVals m ws) :: pM m sh sgn r p ++ rest)
      (fun _ => Ksw * (4 * pSz m sh sgn r p + 8)) := by
    refine swStep hsw _ (.int sgn) _ _ ?_
    simp only [vsz_nil, MrgKit.vsz_int', MrgKit.vsz_cons', pSz]
    exact Nat.mul_le_mul_left _ (by omega)
  have e14 : WordR main consP
      (fun vs => vs = .int sgn :: .cons (.int (sh : ℤ)) (.cons (.int (m : ℤ)) .nil) :: .int (r : ℤ)
        :: .int (p : ℤ) :: ofList (chunkVals m ws) :: pM m sh sgn r p ++ rest)
      (fun _ out => out = .cons (.int sgn) (.cons (.int (sh : ℤ)) (.cons (.int (m : ℤ)) .nil))
        :: .int (r : ℤ) :: .int (p : ℤ) :: ofList (chunkVals m ws) :: pM m sh sgn r p ++ rest)
      (fun _ => Kcv) := consStep2 hcons _ _ _ _ le_rfl
  have e15 : WordR main swP
      (fun vs => vs = .cons (.int sgn) (.cons (.int (sh : ℤ)) (.cons (.int (m : ℤ)) .nil))
        :: .int (r : ℤ) :: .int (p : ℤ) :: ofList (chunkVals m ws) :: pM m sh sgn r p ++ rest)
      (fun _ out => out = .int (r : ℤ)
        :: .cons (.int sgn) (.cons (.int (sh : ℤ)) (.cons (.int (m : ℤ)) .nil))
        :: .int (p : ℤ) :: ofList (chunkVals m ws) :: pM m sh sgn r p ++ rest)
      (fun _ => Ksw * (4 * pSz m sh sgn r p + 8)) := by
    refine swStep hsw _ (.int (r : ℤ)) _ _ ?_
    simp only [vsz_nil, MrgKit.vsz_int', MrgKit.vsz_cons', pSz]
    exact Nat.mul_le_mul_left _ (by omega)
  have e16 : WordR main consP
      (fun vs => vs = .int (r : ℤ)
        :: .cons (.int sgn) (.cons (.int (sh : ℤ)) (.cons (.int (m : ℤ)) .nil))
        :: .int (p : ℤ) :: ofList (chunkVals m ws) :: pM m sh sgn r p ++ rest)
      (fun _ out => out = .cons (.int (r : ℤ))
          (.cons (.int sgn) (.cons (.int (sh : ℤ)) (.cons (.int (m : ℤ)) .nil)))
        :: .int (p : ℤ) :: ofList (chunkVals m ws) :: pM m sh sgn r p ++ rest)
      (fun _ => Kcv) := consStep2 hcons _ _ _ _ le_rfl
  have e17 : WordR main swP
      (fun vs => vs = .cons (.int (r : ℤ))
          (.cons (.int sgn) (.cons (.int (sh : ℤ)) (.cons (.int (m : ℤ)) .nil)))
        :: .int (p : ℤ) :: ofList (chunkVals m ws) :: pM m sh sgn r p ++ rest)
      (fun _ out => out = .int (p : ℤ)
        :: .cons (.int (r : ℤ))
          (.cons (.int sgn) (.cons (.int (sh : ℤ)) (.cons (.int (m : ℤ)) .nil)))
        :: ofList (chunkVals m ws) :: pM m sh sgn r p ++ rest)
      (fun _ => Ksw * (4 * pSz m sh sgn r p + 8)) := by
    refine swStep hsw _ (.int (p : ℤ)) _ _ ?_
    simp only [vsz_nil, MrgKit.vsz_int', MrgKit.vsz_cons', pSz]
    exact Nat.mul_le_mul_left _ (by omega)
  have e18 : WordR main consP
      (fun vs => vs = .int (p : ℤ)
        :: .cons (.int (r : ℤ))
          (.cons (.int sgn) (.cons (.int (sh : ℤ)) (.cons (.int (m : ℤ)) .nil)))
        :: ofList (chunkVals m ws) :: pM m sh sgn r p ++ rest)
      (fun _ out => out = .cons (.int (p : ℤ))
          (.cons (.int (r : ℤ))
            (.cons (.int sgn) (.cons (.int (sh : ℤ)) (.cons (.int (m : ℤ)) .nil))))
        :: ofList (chunkVals m ws) :: pM m sh sgn r p ++ rest)
      (fun _ => Kcv) := consStep2 hcons _ _ _ _ le_rfl
  have e19 : WordR main swP
      (fun vs => vs = .cons (.int (p : ℤ))
          (.cons (.int (r : ℤ))
            (.cons (.int sgn) (.cons (.int (sh : ℤ)) (.cons (.int (m : ℤ)) .nil))))
        :: ofList (chunkVals m ws) :: pM m sh sgn r p ++ rest)
      (fun _ out => out = ofList (chunkVals m ws) :: .cons (.int (p : ℤ))
          (.cons (.int (r : ℤ))
            (.cons (.int sgn) (.cons (.int (sh : ℤ)) (.cons (.int (m : ℤ)) .nil))))
        :: pM m sh sgn r p ++ rest)
      (fun _ => Ksw * (vsz (ofList (chunkVals m ws)) + pSz m sh sgn r p + 1)) := by
    refine swStep hsw _ _ _ _ ?_
    simp only [vsz_nil, MrgKit.vsz_int', MrgKit.vsz_cons', pSz]
    exact Nat.mul_le_mul_left _ (by omega)
  have g18 := MrgKit.WordR_seqC e18 e19
  have g17 := MrgKit.WordR_seqC e17 g18
  have g16 := MrgKit.WordR_seqC e16 g17
  have g15 := MrgKit.WordR_seqC e15 g16
  have g14 := MrgKit.WordR_seqC e14 g15
  have g13 := MrgKit.WordR_seqC e13 g14
  have g12 := MrgKit.WordR_seqC e12 g13
  have g11 := MrgKit.WordR_seqC e11 g12
  have g10 := MrgKit.WordR_seqC e10 g11
  have g9 := MrgKit.WordR_seqC e9 g10
  have g8 := MrgKit.WordR_seqC e8 g9
  have g7 := MrgKit.WordR_seqC e7 g8
  have g6 := MrgKit.WordR_seqC e6 g7
  have g5 := MrgKit.WordR_seqC e5 g6
  have g4 := MrgKit.WordR_seqC e4 g5
  have g3 := MrgKit.WordR_seqC e3 g4
  have g2 := MrgKit.WordR_seqC e2 g3
  have g1 := MrgKit.WordR_seqC e1 g2
  refine MrgKit.WordR_weaken g1 (fun vs hvs => ?_) (fun vs out _ hQ' => ?_) (fun vs _ => ?_)
  · rw [hvs]
  · exact hQ'
  · simp only [lvlSetupCost]
    ring_nf
    omega


/-- The prefix of the fold body: un-cons the element, extract the five parameters, and bring the
block on top with the parameters below it. -/
def lvlPre (uncP : Cmd) (rollP : ℕ → Cmd) (swP drP : Cmd) : Cmd :=
  uncP ;;; rollP 1 ;;; uncP ;;; rollP 1 ;;; uncP ;;; rollP 1 ;;; uncP ;;; rollP 1 ;;;
    uncP ;;; rollP 1 ;;; uncP ;;; swP ;;; drP ;;; rollP 5

/-- The suffix of the fold body: move the output below the five parameters and `cons` it onto the
accumulator. -/
def lvlSuf (rollP : ℕ → Cmd) (drP consP : Cmd) : Cmd :=
  rollP 5 ;;; rollP 5 ;;; rollP 5 ;;; rollP 5 ;;; rollP 5 ;;;
    drP ;;; drP ;;; drP ;;; drP ;;; drP ;;; consP

/-- General sequencing: a singleton pre with an arbitrary post, followed by a step whose
precondition is the intermediate state. -/
theorem WordR_seq_gen {main : Cmd} {p q : Cmd} {A : List Val} {R : List Val → Prop}
    {S : List Val → Prop} {c1 c2 : ℕ}
    (h1 : WordR main p (fun vs => vs = A) (fun _ out => R out) (fun _ => c1))
    (h2 : ∀ mid, R mid → WordR main q (fun vs => vs = mid) (fun _ out => S out) (fun _ => c2)) :
    WordR main (p ;;; q) (fun vs => vs = A) (fun _ out => S out) (fun _ => c1 + c2) := by
  intro vs hvs s Rgh hstk
  rw [hvs] at hstk
  obtain ⟨mid, s₂, n₁, hR, he₁, hn₁, hstk₁, hoth₁⟩ := h1 A rfl s Rgh hstk
  obtain ⟨out, s₃, n₂, hS, he₂, hn₂, hstk₂, hoth₂⟩ := h2 mid hR mid rfl s₂ Rgh hstk₁
  exact ⟨out, s₃, n₁ + n₂, hS, Eval.seq he₁ he₂, Nat.add_le_add hn₁ hn₂, hstk₂,
    fun k hk => by rw [hoth₂ k hk, hoth₁ k hk]⟩

/-- The `mapList` pass wrapping every chunk as `cons chunk (prepVR …)`. -/
theorem lvlPairMap {main : Cmd} {pickP : ℕ → Cmd} {rollP : ℕ → Cmd} {consP : Cmd}
    {mapP : Cmd → Cmd} {Kp Kr Kcv Kml : ℕ}
    (hpick : ∀ k, WordR main (pickP k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs)
      (fun vs => Kp * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    (hroll : ∀ k, WordR main (rollP k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs.eraseIdx k)
      (fun vs => Kr * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    (hcons : WordR main consP (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = .cons a b :: rest) (fun _ => Kcv))
    (hmap : ∀ (q : Cmd) (rest : List Val) (P : Val → Prop) (Q : Val → Val → Prop) (c L : ℕ),
      (∀ x, P x → WordR main q (fun vs => vs = x :: rest)
        (fun _ out => ∃ y, out = y :: rest ∧ Q x y ∧ vsz y ≤ L) (fun _ => c)) →
      ∀ xs : List Val, (∀ x ∈ xs, P x ∧ vsz x ≤ L) →
      WordR main (mapP q) (fun vs => vs = ofList xs :: rest)
        (fun _ out => ∃ ys, out = ofList ys :: rest ∧ List.Forall₂ Q xs ys)
        (fun _ => xs.length * (c + Kml * (L + 1)) + Kml))
    (m sh : ℕ) (sgn : ℤ) (r p : ℕ) (ws : List (List (ℤ × ℤ))) (rest : List Val) (Lch : ℕ)
    (hLch : ∀ x ∈ chunkVals m ws, vsz x ≤ Lch) :
    WordR main (mapP (pickP 1 ;;; rollP 1 ;;; consP))
      (fun vs => vs = ofList (chunkVals m ws) :: prepVR m sh sgn r p :: pM m sh sgn r p ++ rest)
      (fun _ out => ∃ ys, out = ofList ys :: prepVR m sh sgn r p :: pM m sh sgn r p ++ rest ∧
        List.Forall₂ (fun x y => y = .cons x (prepVR m sh sgn r p)) (chunkVals m ws) ys)
      (fun _ => (chunkVals m ws).length * ((Kp * 2 * (Lch + pSz m sh sgn r p + 1)
          + Kr * 2 * (Lch + pSz m sh sgn r p + 1) + Kcv)
          + Kml * (Lch + pSz m sh sgn r p + 2)) + Kml) := by
  refine MrgKit.WordR_weaken
    (hmap (pickP 1 ;;; rollP 1 ;;; consP) (prepVR m sh sgn r p :: pM m sh sgn r p ++ rest)
      (fun x => vsz x + pSz m sh sgn r p + 1 ≤ Lch + pSz m sh sgn r p + 1)
      (fun x y => y = .cons x (prepVR m sh sgn r p))
      (Kp * 2 * (Lch + pSz m sh sgn r p + 1) + Kr * 2 * (Lch + pSz m sh sgn r p + 1) + Kcv)
      (Lch + pSz m sh sgn r p + 1) ?_ (chunkVals m ws) ?_) ?_ ?_ ?_
  · -- per-element obligation
    intro x hx
    have hx' : vsz x ≤ Lch := by omega
    have hPsz : vsz (prepVR m sh sgn r p) ≤ pSz m sh sgn r p := vsz_prepVR m sh sgn r p
    have f1 : WordR main (pickP 1)
        (fun vs => vs = x :: prepVR m sh sgn r p :: pM m sh sgn r p ++ rest)
        (fun _ out => out = prepVR m sh sgn r p :: x :: prepVR m sh sgn r p :: pM m sh sgn r p ++ rest)
        (fun _ => Kp * 2 * (Lch + pSz m sh sgn r p + 1)) := by
      refine pickStepG hpick 1 (x :: prepVR m sh sgn r p :: pM m sh sgn r p ++ rest) ?_ _ ?_
      · simp only [List.length_cons, List.length_append, pM]; omega
      · simp only [List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero,
          List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, List.getD_cons_zero,
          List.length_cons]
        exact Nat.mul_le_mul_left _ (by omega)
    have f2 : WordR main (rollP 1)
        (fun vs => vs = prepVR m sh sgn r p :: x :: prepVR m sh sgn r p :: pM m sh sgn r p ++ rest)
        (fun _ out => out = x :: prepVR m sh sgn r p :: prepVR m sh sgn r p :: pM m sh sgn r p ++ rest)
        (fun _ => Kr * 2 * (Lch + pSz m sh sgn r p + 1)) := by
      refine rollStepG hroll 1 (prepVR m sh sgn r p :: x :: prepVR m sh sgn r p :: pM m sh sgn r p ++ rest)
        ?_ _ ?_
      · simp only [List.length_cons, List.length_append, pM]; omega
      · simp only [List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero,
          List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, List.getD_cons_zero,
          List.getD_cons_succ]
        exact Nat.mul_le_mul_left _ (by omega)
    have f3 : WordR main consP
        (fun vs => vs = x :: prepVR m sh sgn r p :: prepVR m sh sgn r p :: pM m sh sgn r p ++ rest)
        (fun _ out => out = .cons x (prepVR m sh sgn r p) :: prepVR m sh sgn r p
          :: pM m sh sgn r p ++ rest)
        (fun _ => Kcv) := consStep2 hcons _ _ _ _ le_rfl
    refine MrgKit.WordR_weaken (MrgKit.WordR_seqC f1 (MrgKit.WordR_seqC f2 f3)) ?_ ?_ ?_
    · intro vs hvs
      exact hvs
    · intro vs out hvs hQ
      exact ⟨.cons x (prepVR m sh sgn r p), hQ, rfl, by simp only [MrgKit.vsz_cons']; omega⟩
    · intro vs hvs
      omega
  · -- size hypothesis for the elements
    intro x hx
    exact ⟨by have := hLch x hx; omega, by have := hLch x hx; omega⟩
  · -- the post is already in the required shape
    intro vs hvs
    exact hvs
  · intro vs out hvs hQ
    exact hQ
  · intro vs hvs
    ring_nf
    omega

/-- Cleaning up after the pairing pass: drop the parameter value, push `nil`, swap. -/
theorem lvlCleanup {main : Cmd} {swP drP : Cmd} {pushP : Val → Cmd} {Ksw Kdr Kpv : ℕ}
    (hsw : WordR main swP (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = b :: a :: rest)
      (fun vs => Ksw * (vsz (vs.getD 0 .nil) + vsz (vs.getD 1 .nil) + 1)))
    (hdr : WordR main drP (fun vs => vs ≠ [])
      (fun vs out => ∃ v r, vs = v :: r ∧ out = r) (fun vs => Kdr * (vsz (vs.headD .nil) + 1)))
    (hpush : ∀ v, WordR main (pushP v) (fun _ => True) (fun vs out => out = v :: vs)
      (fun _ => Kpv * (vsz v + 1)))
    (m sh : ℕ) (sgn : ℤ) (r p : ℕ) (rest : List Val) (ys : List Val) :
    WordR main (swP ;;; drP ;;; pushP .nil ;;; swP)
      (fun vs => vs = ofList ys :: prepVR m sh sgn r p :: pM m sh sgn r p ++ rest)
      (fun _ out => out = ofList ys :: .nil :: pM m sh sgn r p ++ rest)
      (fun _ => Ksw * (vsz (ofList ys) + vsz (prepVR m sh sgn r p) + 1)
        + (Kdr * (vsz (prepVR m sh sgn r p) + 1) + (Kpv * 2
        + Ksw * (vsz (ofList ys) + 1 + 1)))) := by
  have f1 : WordR main swP
      (fun vs => vs = ofList ys :: prepVR m sh sgn r p :: pM m sh sgn r p ++ rest)
      (fun _ out => out = prepVR m sh sgn r p :: ofList ys :: pM m sh sgn r p ++ rest)
      (fun _ => Ksw * (vsz (ofList ys) + vsz (prepVR m sh sgn r p) + 1)) :=
    swStep hsw _ _ _ _ le_rfl
  have f2 : WordR main drP
      (fun vs => vs = prepVR m sh sgn r p :: ofList ys :: pM m sh sgn r p ++ rest)
      (fun _ out => out = ofList ys :: pM m sh sgn r p ++ rest)
      (fun _ => Kdr * (vsz (prepVR m sh sgn r p) + 1)) :=
    drStep hdr _ _ _ le_rfl
  have f3 : WordR main (pushP .nil) (fun vs => vs = ofList ys :: pM m sh sgn r p ++ rest)
      (fun _ out => out = .nil :: ofList ys :: pM m sh sgn r p ++ rest) (fun _ => Kpv * 2) := by
    refine pushStep2 hpush .nil _ _ ?_
    simp only [vsz_nil]
    exact Nat.mul_le_mul_left _ (by omega)
  have f4 : WordR main swP (fun vs => vs = .nil :: ofList ys :: pM m sh sgn r p ++ rest)
      (fun _ out => out = ofList ys :: .nil :: pM m sh sgn r p ++ rest)
      (fun _ => Ksw * (vsz (ofList ys) + 1 + 1)) := by
    refine swStep hsw .nil (ofList ys) _ _ ?_
    simp only [vsz_nil]
    exact Nat.mul_le_mul_left _ (by omega)
  exact MrgKit.WordR_seqC f1 (MrgKit.WordR_seqC f2 (MrgKit.WordR_seqC f3 f4))

/-- Cost of one fold iteration. -/
def lvlBodyCost (Kuc Kr Ksw Kdr Kcv Kb m r p L : ℕ) : ℕ :=
  6 * Kuc + (5 * (Kr * 2 * (3 * L + 4)) + (Ksw * (3 * L + 4) + (Kdr * 2
      + Kr * 6 * (3 * L + 4))))
    + ((Kb * m * (r + 1) * (p + 1) + Kb)
      + (5 * (Kr * 6 * (L + 1)) + 5 * (Kdr * (L + 1)) + Kcv))

/-- The suffix of the fold body: after the block word, move the output down past the five
parameters and `cons` it onto the accumulator. -/
theorem lvlBodySuffix {main : Cmd} {rollP : ℕ → Cmd} {drP consP : Cmd} {Kr Kdr Kcv : ℕ}
    (hroll : ∀ k, WordR main (rollP k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs.eraseIdx k)
      (fun vs => Kr * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    (hdr : WordR main drP (fun vs => vs ≠ [])
      (fun vs out => ∃ v r, vs = v :: r ∧ out = r) (fun vs => Kdr * (vsz (vs.headD .nil) + 1)))
    (hcons : WordR main consP (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = .cons a b :: rest) (fun _ => Kcv))
    (m sh : ℕ) (sgn : ℤ) (r p : ℕ) (ws' : List (List (ℤ × ℤ))) (Lacc : Val) (rest : List Val)
    (L : ℕ) (hlen : ws'.length = m) (hind : ∀ w ∈ ws', InDiscVec p r w)
    (hL : pSz m sh sgn r p + 15 * (m + 1) * (r + 1) * (p + 1) + 2 ≤ L) :
    WordR main (lvlSuf rollP drP consP)
      (fun vs => vs = ofList (cvecs ws') :: .int (m : ℤ) :: .int (sh : ℤ) :: .int sgn
        :: .int (r : ℤ) :: .int (p : ℤ) :: Lacc :: pM m sh sgn r p ++ rest)
      (fun _ out => out = .cons (ofList (cvecs ws')) Lacc :: pM m sh sgn r p ++ rest)
      (fun _ => 5 * (Kr * 6 * (L + 1)) + 5 * (Kdr * (L + 1)) + Kcv) := by
  have hYsz : vsz (ofList (cvecs ws')) ≤ 15 * (m + 1) * (r + 1) * (p + 1) :=
    @vsz_ofList_cvecs_le_xlvlProg m r p ws' hlen hind
  have hwin : vsz (ofList (cvecs ws'))
      + (isz (m : ℤ) + isz (sh : ℤ) + isz sgn + isz (r : ℤ) + isz (p : ℤ)) + 1 ≤ L := by
    rw [pSz_eq] at hL
    omega
  have t1 : WordR main (rollP 5)
      (fun vs => vs = ofList (cvecs ws') :: .int (m : ℤ) :: .int (sh : ℤ) :: .int sgn
        :: .int (r : ℤ) :: .int (p : ℤ) :: Lacc :: pM m sh sgn r p ++ rest)
      (fun _ out => out = .int (p : ℤ) :: ofList (cvecs ws') :: .int (m : ℤ) :: .int (sh : ℤ)
        :: .int sgn :: .int (r : ℤ) :: Lacc :: pM m sh sgn r p ++ rest)
      (fun _ => Kr * 6 * (L + 1)) := by
    refine rollStepG hroll 5 _ ?_ _ ?_
    · simp only [List.length_cons, List.length_append, pM]; omega
    · simp only [List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero,
        List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, List.getD_cons_zero,
        List.getD_cons_succ, MrgKit.vsz_int']
      exact Nat.mul_le_mul_left _ (by omega)
  have t2 : WordR main (rollP 5)
      (fun vs => vs = .int (p : ℤ) :: ofList (cvecs ws') :: .int (m : ℤ) :: .int (sh : ℤ)
        :: .int sgn :: .int (r : ℤ) :: Lacc :: pM m sh sgn r p ++ rest)
      (fun _ out => out = .int (r : ℤ) :: .int (p : ℤ) :: ofList (cvecs ws') :: .int (m : ℤ)
        :: .int (sh : ℤ) :: .int sgn :: Lacc :: pM m sh sgn r p ++ rest)
      (fun _ => Kr * 6 * (L + 1)) := by
    refine rollStepG hroll 5 _ ?_ _ ?_
    · simp only [List.length_cons, List.length_append, pM]; omega
    · simp only [List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero,
        List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, List.getD_cons_zero,
        List.getD_cons_succ, MrgKit.vsz_int']
      exact Nat.mul_le_mul_left _ (by omega)
  have t3 : WordR main (rollP 5)
      (fun vs => vs = .int (r : ℤ) :: .int (p : ℤ) :: ofList (cvecs ws') :: .int (m : ℤ)
        :: .int (sh : ℤ) :: .int sgn :: Lacc :: pM m sh sgn r p ++ rest)
      (fun _ out => out = .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: ofList (cvecs ws')
        :: .int (m : ℤ) :: .int (sh : ℤ) :: Lacc :: pM m sh sgn r p ++ rest)
      (fun _ => Kr * 6 * (L + 1)) := by
    refine rollStepG hroll 5 _ ?_ _ ?_
    · simp only [List.length_cons, List.length_append, pM]; omega
    · simp only [List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero,
        List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, List.getD_cons_zero,
        List.getD_cons_succ, MrgKit.vsz_int']
      exact Nat.mul_le_mul_left _ (by omega)
  have t4 : WordR main (rollP 5)
      (fun vs => vs = .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: ofList (cvecs ws')
        :: .int (m : ℤ) :: .int (sh : ℤ) :: Lacc :: pM m sh sgn r p ++ rest)
      (fun _ out => out = .int (sh : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ)
        :: ofList (cvecs ws') :: .int (m : ℤ) :: Lacc :: pM m sh sgn r p ++ rest)
      (fun _ => Kr * 6 * (L + 1)) := by
    refine rollStepG hroll 5 _ ?_ _ ?_
    · simp only [List.length_cons, List.length_append, pM]; omega
    · simp only [List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero,
        List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, List.getD_cons_zero,
        List.getD_cons_succ, MrgKit.vsz_int']
      exact Nat.mul_le_mul_left _ (by omega)
  have t5 : WordR main (rollP 5)
      (fun vs => vs = .int (sh : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ)
        :: ofList (cvecs ws') :: .int (m : ℤ) :: Lacc :: pM m sh sgn r p ++ rest)
      (fun _ out => out = .int (m : ℤ) :: .int (sh : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ)
        :: ofList (cvecs ws') :: Lacc :: pM m sh sgn r p ++ rest)
      (fun _ => Kr * 6 * (L + 1)) := by
    refine rollStepG hroll 5 _ ?_ _ ?_
    · simp only [List.length_cons, List.length_append, pM]; omega
    · simp only [List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero,
        List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, List.getD_cons_zero,
        List.getD_cons_succ, MrgKit.vsz_int']
      exact Nat.mul_le_mul_left _ (by omega)
  have t6 : WordR main drP
      (fun vs => vs = .int (m : ℤ) :: .int (sh : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ)
        :: ofList (cvecs ws') :: Lacc :: pM m sh sgn r p ++ rest)
      (fun _ out => out = .int (sh : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ)
        :: ofList (cvecs ws') :: Lacc :: pM m sh sgn r p ++ rest)
      (fun _ => Kdr * (L + 1)) := by
    refine drStep hdr _ _ _ ?_
    simp only [MrgKit.vsz_int']
    exact Nat.mul_le_mul_left _ (by omega)
  have t7 : WordR main drP
      (fun vs => vs = .int (sh : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ)
        :: ofList (cvecs ws') :: Lacc :: pM m sh sgn r p ++ rest)
      (fun _ out => out = .int sgn :: .int (r : ℤ) :: .int (p : ℤ)
        :: ofList (cvecs ws') :: Lacc :: pM m sh sgn r p ++ rest)
      (fun _ => Kdr * (L + 1)) := by
    refine drStep hdr _ _ _ ?_
    simp only [MrgKit.vsz_int']
    exact Nat.mul_le_mul_left _ (by omega)
  have t8 : WordR main drP
      (fun vs => vs = .int sgn :: .int (r : ℤ) :: .int (p : ℤ)
        :: ofList (cvecs ws') :: Lacc :: pM m sh sgn r p ++ rest)
      (fun _ out => out = .int (r : ℤ) :: .int (p : ℤ)
        :: ofList (cvecs ws') :: Lacc :: pM m sh sgn r p ++ rest)
      (fun _ => Kdr * (L + 1)) := by
    refine drStep hdr _ _ _ ?_
    simp only [MrgKit.vsz_int']
    exact Nat.mul_le_mul_left _ (by omega)
  have t9 : WordR main drP
      (fun vs => vs = .int (r : ℤ) :: .int (p : ℤ)
        :: ofList (cvecs ws') :: Lacc :: pM m sh sgn r p ++ rest)
      (fun _ out => out = .int (p : ℤ)
        :: ofList (cvecs ws') :: Lacc :: pM m sh sgn r p ++ rest)
      (fun _ => Kdr * (L + 1)) := by
    refine drStep hdr _ _ _ ?_
    simp only [MrgKit.vsz_int']
    exact Nat.mul_le_mul_left _ (by omega)
  have t10 : WordR main drP
      (fun vs => vs = .int (p : ℤ)
        :: ofList (cvecs ws') :: Lacc :: pM m sh sgn r p ++ rest)
      (fun _ out => out = ofList (cvecs ws') :: Lacc :: pM m sh sgn r p ++ rest)
      (fun _ => Kdr * (L + 1)) := by
    refine drStep hdr _ _ _ ?_
    simp only [MrgKit.vsz_int']
    exact Nat.mul_le_mul_left _ (by omega)
  have t11 : WordR main consP
      (fun vs => vs = ofList (cvecs ws') :: Lacc :: pM m sh sgn r p ++ rest)
      (fun _ out => out = .cons (ofList (cvecs ws')) Lacc :: pM m sh sgn r p ++ rest)
      (fun _ => Kcv) := consStep2 hcons _ _ _ _ le_rfl
  have chain9 := t11
  have chain8 := MrgKit.WordR_seqC t10 chain9
  have chain7 := MrgKit.WordR_seqC t9 chain8
  have chain6 := MrgKit.WordR_seqC t8 chain7
  have chain5 := MrgKit.WordR_seqC t7 chain6
  have chain4 := MrgKit.WordR_seqC t6 chain5
  have chain3 := MrgKit.WordR_seqC t5 chain4
  have chain2 := MrgKit.WordR_seqC t4 chain3
  have chain1 := MrgKit.WordR_seqC t3 chain2
  have chain0 := MrgKit.WordR_seqC t2 chain1
  have chain := MrgKit.WordR_seqC t1 chain0
  refine MrgKit.WordR_weaken chain (fun vs hvs => hvs) (fun vs out _ hQ => hQ) (fun vs _ => ?_)
  omega

/-- The body of the fold: un-cons the element (a block plus the parameter value), extract the five
parameters, run the block word, put the output on top of the accumulator. -/
theorem lvlBody {main : Cmd} {uncP : Cmd} {rollP : ℕ → Cmd} {drP swP consP blkP : Cmd}
    {Kuc Kr Kdr Ksw Kcv Kb : ℕ}
    (hunc : WordR main uncP (fun vs => ∃ a b r, vs = .cons a b :: r)
      (fun vs out => ∃ a b r, vs = .cons a b :: r ∧ out = a :: b :: r) (fun _ => Kuc))
    (hroll : ∀ k, WordR main (rollP k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs.eraseIdx k)
      (fun vs => Kr * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    (hdr : WordR main drP (fun vs => vs ≠ [])
      (fun vs out => ∃ v r, vs = v :: r ∧ out = r) (fun vs => Kdr * (vsz (vs.headD .nil) + 1)))
    (hsw : WordR main swP (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = b :: a :: rest)
      (fun vs => Ksw * (vsz (vs.getD 0 .nil) + vsz (vs.getD 1 .nil) + 1)))
    (hcons : WordR main consP (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = .cons a b :: rest) (fun _ => Kcv))
    (hblk : ∀ (main : Cmd) (p r m sh : ℕ) (sgn : ℤ) (ws : List (List (ℤ × ℤ))) (u : Arr r) (e : ℝ)
        (rest : List Val),
      2 ≤ m → m * 2 ^ sh = 2 * r → (sgn = 1 ∨ sgn = -1) → 2 * r < 2 ^ p →
      ws.length = m → (∀ w ∈ ws, InDiscVec p r w) → ApproxSL p r m ws u e →
      WordR main blkP (fun vs => vs = ofList (cvecs ws) :: .int (m : ℤ) :: .int (sh : ℤ) :: .int sgn
        :: .int (r : ℤ) :: .int (p : ℤ) :: rest)
        (fun _ out => ∃ ws', out = ofList (cvecs ws') :: .int (m : ℤ) :: .int (sh : ℤ) :: .int sgn
          :: .int (r : ℤ) :: .int (p : ℤ) :: rest ∧ ws'.length = m ∧ (∀ w ∈ ws', InDiscVec p r w) ∧
          ApproxSL p r m ws' (lvlN r m sgn u) (e + 1))
        (fun _ => Kb * m * (r + 1) * (p + 1) + Kb))
    (m sh : ℕ) (sgn : ℤ) (r p : ℕ) (u : Arr r) (e : ℝ) (i : ℕ)
    (wb : List (List (ℤ × ℤ))) (Lacc : Val) (rest : List Val) (L : ℕ)
    (hm2 : 2 ≤ m) (hmr : m * 2 ^ sh = 2 * r) (hsgn : sgn = 1 ∨ sgn = -1) (hp : 2 * r < 2 ^ p)
    (hwb : wb.length = m) (hind : ∀ w ∈ wb, InDiscVec p r w)
    (happ : ApproxSL p r m wb (blkArr r u m i) e)
    (hL : pSz m sh sgn r p + 15 * (m + 1) * (r + 1) * (p + 1) + 2 ≤ L) :
    WordR main (lvlPre uncP rollP swP drP ;;; blkP ;;; lvlSuf rollP drP consP)
      (fun vs => vs = .cons (ofList (cvecs wb)) (prepVR m sh sgn r p) :: Lacc
        :: pM m sh sgn r p ++ rest)
      (fun _ out => ∃ ws' : List (List (ℤ × ℤ)),
        out = .cons (ofList (cvecs ws')) Lacc :: pM m sh sgn r p ++ rest ∧ ws'.length = m ∧
        (∀ w ∈ ws', InDiscVec p r w) ∧ ApproxSL p r m ws' (lvlN r m sgn (blkArr r u m i)) (e + 1))
      (fun _ => lvlBodyCost Kuc Kr Ksw Kdr Kcv Kb m r p L) := by
  have hCH : vsz (ofList (cvecs wb)) ≤ 15 * (m + 1) * (r + 1) * (p + 1) :=
    @vsz_ofList_cvecs_le_xlvlProg m r p wb hwb hind
  have hPszL : pSz m sh sgn r p ≤ L := by omega
  have hPvsz : vsz (prepVR m sh sgn r p)
      ≤ isz (m : ℤ) + isz (sh : ℤ) + isz sgn + isz (r : ℤ) + isz (p : ℤ) + 6 := by
    have h := vsz_prepVR m sh sgn r p
    rwa [pSz_eq] at h
  have hSs : vsz (ofList (cvecs wb))
      + (isz (m : ℤ) + isz (sh : ℤ) + isz sgn + isz (r : ℤ) + isz (p : ℤ)) + 1 ≤ L := by
    rw [pSz_eq] at hL
    omega
  have hT1 : vsz (ofList (cvecs wb)) + vsz (prepVR m sh sgn r p) + 1 ≤ L := by
    rw [pSz_eq] at hL
    omega
  have hP1 : vsz (ofList [.int (m : ℤ)])
      ≤ isz (m : ℤ) + isz (sh : ℤ) + isz sgn + isz (r : ℤ) + isz (p : ℤ) + 6 := by
    simp only [ofList, List.foldr, MrgKit.vsz_cons', MrgKit.vsz_int', vsz_nil]; omega
  have hP2 : vsz (ofList [.int (sh : ℤ), .int (m : ℤ)])
      ≤ isz (m : ℤ) + isz (sh : ℤ) + isz sgn + isz (r : ℤ) + isz (p : ℤ) + 6 := by
    simp only [ofList, List.foldr, MrgKit.vsz_cons', MrgKit.vsz_int', vsz_nil]; omega
  have hP3 : vsz (ofList [.int sgn, .int (sh : ℤ), .int (m : ℤ)])
      ≤ isz (m : ℤ) + isz (sh : ℤ) + isz sgn + isz (r : ℤ) + isz (p : ℤ) + 6 := by
    simp only [ofList, List.foldr, MrgKit.vsz_cons', MrgKit.vsz_int', vsz_nil]; omega
  have hP4 : vsz (ofList [.int (r : ℤ), .int sgn, .int (sh : ℤ), .int (m : ℤ)])
      ≤ pSz m sh sgn r p := by
    simp only [ofList, List.foldr, MrgKit.vsz_cons', MrgKit.vsz_int', vsz_nil, pSz]; omega
  -- ### the prefix
  have t1 : WordR main uncP
      (fun vs => vs = .cons (ofList (cvecs wb)) (prepVR m sh sgn r p) :: Lacc
        :: pM m sh sgn r p ++ rest)
      (fun _ out => out = ofList (cvecs wb) :: prepVR m sh sgn r p :: Lacc
        :: pM m sh sgn r p ++ rest) (fun _ => Kuc) :=
    uncStep hunc _ _ _ _ le_rfl
  have t2 : WordR main (rollP 1)
      (fun vs => vs = ofList (cvecs wb) :: prepVR m sh sgn r p :: Lacc :: pM m sh sgn r p ++ rest)
      (fun _ out => out = prepVR m sh sgn r p :: ofList (cvecs wb) :: Lacc
        :: pM m sh sgn r p ++ rest) (fun _ => Kr * 2 * (3 * L + 4)) := by
    refine rollStepG hroll 1 _ ?_ _ ?_
    · simp only [List.length_cons, List.length_append, pM]; omega
    · simp only [List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero,
        List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, List.getD_cons_zero]
      exact Nat.mul_le_mul_left _ (by omega)
  have t3 : WordR main uncP
      (fun vs => vs = prepVR m sh sgn r p :: ofList (cvecs wb) :: Lacc :: pM m sh sgn r p ++ rest)
      (fun _ out => out = .int (p : ℤ)
        :: ofList [.int (r : ℤ), .int sgn, .int (sh : ℤ), .int (m : ℤ)]
        :: ofList (cvecs wb) :: Lacc :: pM m sh sgn r p ++ rest) (fun _ => Kuc) := by
    exact uncStep hunc (.int (p : ℤ)) _ _ _ le_rfl
  have t4 : WordR main (rollP 1)
      (fun vs => vs = .int (p : ℤ)
        :: ofList [.int (r : ℤ), .int sgn, .int (sh : ℤ), .int (m : ℤ)]
        :: ofList (cvecs wb) :: Lacc :: pM m sh sgn r p ++ rest)
      (fun _ out => out = ofList [.int (r : ℤ), .int sgn, .int (sh : ℤ), .int (m : ℤ)]
        :: .int (p : ℤ) :: ofList (cvecs wb) :: Lacc :: pM m sh sgn r p ++ rest)
      (fun _ => Kr * 2 * (3 * L + 4)) := by
    refine rollStepG hroll 1 _ ?_ _ ?_
    · simp only [List.length_cons, List.length_append, pM]; omega
    · simp only [List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero,
        List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, List.getD_cons_zero,
        List.getD_cons_succ, MrgKit.vsz_int']
      exact Nat.mul_le_mul_left _ (by omega)
  have t5 : WordR main uncP
      (fun vs => vs = ofList [.int (r : ℤ), .int sgn, .int (sh : ℤ), .int (m : ℤ)]
        :: .int (p : ℤ) :: ofList (cvecs wb) :: Lacc :: pM m sh sgn r p ++ rest)
      (fun _ out => out = .int (r : ℤ) :: ofList [.int sgn, .int (sh : ℤ), .int (m : ℤ)]
        :: .int (p : ℤ) :: ofList (cvecs wb) :: Lacc :: pM m sh sgn r p ++ rest)
      (fun _ => Kuc) := by
    exact uncStep hunc (.int (r : ℤ)) _ _ _ le_rfl
  have t6 : WordR main (rollP 1)
      (fun vs => vs = .int (r : ℤ) :: ofList [.int sgn, .int (sh : ℤ), .int (m : ℤ)]
        :: .int (p : ℤ) :: ofList (cvecs wb) :: Lacc :: pM m sh sgn r p ++ rest)
      (fun _ out => out = ofList [.int sgn, .int (sh : ℤ), .int (m : ℤ)]
        :: .int (r : ℤ) :: .int (p : ℤ) :: ofList (cvecs wb) :: Lacc :: pM m sh sgn r p ++ rest)
      (fun _ => Kr * 2 * (3 * L + 4)) := by
    refine rollStepG hroll 1 _ ?_ _ ?_
    · simp only [List.length_cons, List.length_append, pM]; omega
    · simp only [List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero,
        List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, List.getD_cons_zero,
        List.getD_cons_succ, MrgKit.vsz_int']
      exact Nat.mul_le_mul_left _ (by omega)
  have t7 : WordR main uncP
      (fun vs => vs = ofList [.int sgn, .int (sh : ℤ), .int (m : ℤ)]
        :: .int (r : ℤ) :: .int (p : ℤ) :: ofList (cvecs wb) :: Lacc :: pM m sh sgn r p ++ rest)
      (fun _ out => out = .int sgn :: ofList [.int (sh : ℤ), .int (m : ℤ)]
        :: .int (r : ℤ) :: .int (p : ℤ) :: ofList (cvecs wb) :: Lacc :: pM m sh sgn r p ++ rest)
      (fun _ => Kuc) := by
    exact uncStep hunc (.int sgn) _ _ _ le_rfl
  have t8 : WordR main (rollP 1)
      (fun vs => vs = .int sgn :: ofList [.int (sh : ℤ), .int (m : ℤ)]
        :: .int (r : ℤ) :: .int (p : ℤ) :: ofList (cvecs wb) :: Lacc :: pM m sh sgn r p ++ rest)
      (fun _ out => out = ofList [.int (sh : ℤ), .int (m : ℤ)]
        :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: ofList (cvecs wb) :: Lacc
        :: pM m sh sgn r p ++ rest) (fun _ => Kr * 2 * (3 * L + 4)) := by
    refine rollStepG hroll 1 _ ?_ _ ?_
    · simp only [List.length_cons, List.length_append, pM]; omega
    · simp only [List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero,
        List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, List.getD_cons_zero,
        List.getD_cons_succ, MrgKit.vsz_int']
      exact Nat.mul_le_mul_left _ (by omega)
  have t9 : WordR main uncP
      (fun vs => vs = ofList [.int (sh : ℤ), .int (m : ℤ)]
        :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: ofList (cvecs wb) :: Lacc
        :: pM m sh sgn r p ++ rest)
      (fun _ out => out = .int (sh : ℤ) :: ofList [.int (m : ℤ)]
        :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: ofList (cvecs wb) :: Lacc
        :: pM m sh sgn r p ++ rest) (fun _ => Kuc) := by
    exact uncStep hunc (.int (sh : ℤ)) _ _ _ le_rfl
  have t10 : WordR main (rollP 1)
      (fun vs => vs = .int (sh : ℤ) :: ofList [.int (m : ℤ)]
        :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: ofList (cvecs wb) :: Lacc
        :: pM m sh sgn r p ++ rest)
      (fun _ out => out = ofList [.int (m : ℤ)]
        :: .int (sh : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: ofList (cvecs wb) :: Lacc
        :: pM m sh sgn r p ++ rest) (fun _ => Kr * 2 * (3 * L + 4)) := by
    refine rollStepG hroll 1 _ ?_ _ ?_
    · simp only [List.length_cons, List.length_append, pM]; omega
    · simp only [List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero,
        List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, List.getD_cons_zero,
        List.getD_cons_succ, MrgKit.vsz_int']
      exact Nat.mul_le_mul_left _ (by omega)
  have t11 : WordR main uncP
      (fun vs => vs = ofList [.int (m : ℤ)]
        :: .int (sh : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: ofList (cvecs wb) :: Lacc
        :: pM m sh sgn r p ++ rest)
      (fun _ out => out = .int (m : ℤ) :: .nil
        :: .int (sh : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: ofList (cvecs wb) :: Lacc
        :: pM m sh sgn r p ++ rest) (fun _ => Kuc) := by
    exact uncStep hunc (.int (m : ℤ)) .nil _ _ le_rfl
  have t12 : WordR main swP
      (fun vs => vs = .int (m : ℤ) :: .nil
        :: .int (sh : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: ofList (cvecs wb) :: Lacc
        :: pM m sh sgn r p ++ rest)
      (fun _ out => out = .nil :: .int (m : ℤ)
        :: .int (sh : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: ofList (cvecs wb) :: Lacc
        :: pM m sh sgn r p ++ rest) (fun _ => Ksw * (3 * L + 4)) := by
    refine swStep hsw _ _ _ _ ?_
    simp only [vsz_nil, MrgKit.vsz_int']
    exact Nat.mul_le_mul_left _ (by omega)
  have t13 : WordR main drP
      (fun vs => vs = .nil :: .int (m : ℤ)
        :: .int (sh : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: ofList (cvecs wb) :: Lacc
        :: pM m sh sgn r p ++ rest)
      (fun _ out => out = .int (m : ℤ)
        :: .int (sh : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: ofList (cvecs wb) :: Lacc
        :: pM m sh sgn r p ++ rest) (fun _ => Kdr * 2) := by
    refine drStep hdr _ _ _ ?_
    simp only [vsz_nil]
    exact le_of_eq (by ring)
  have t14 : WordR main (rollP 5)
      (fun vs => vs = .int (m : ℤ)
        :: .int (sh : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: ofList (cvecs wb) :: Lacc
        :: pM m sh sgn r p ++ rest)
      (fun _ out => out = ofList (cvecs wb) :: .int (m : ℤ)
        :: .int (sh : ℤ) :: .int sgn :: .int (r : ℤ) :: .int (p : ℤ) :: Lacc
        :: pM m sh sgn r p ++ rest) (fun _ => Kr * 6 * (3 * L + 4)) := by
    refine rollStepG hroll 5 _ ?_ _ ?_
    · simp only [List.length_cons, List.length_append, pM]; omega
    · simp only [List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero,
        List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, List.getD_cons_zero,
        List.getD_cons_succ, MrgKit.vsz_int']
      exact Nat.mul_le_mul_left _ (by omega)
  have c13 := t14
  have c12 := MrgKit.WordR_seqC t13 c13
  have c11 := MrgKit.WordR_seqC t12 c12
  have c10 := MrgKit.WordR_seqC t11 c11
  have c9 := MrgKit.WordR_seqC t10 c10
  have c8 := MrgKit.WordR_seqC t9 c9
  have c7 := MrgKit.WordR_seqC t8 c8
  have c6 := MrgKit.WordR_seqC t7 c7
  have c5 := MrgKit.WordR_seqC t6 c6
  have c4 := MrgKit.WordR_seqC t5 c5
  have c3 := MrgKit.WordR_seqC t4 c4
  have c2 := MrgKit.WordR_seqC t3 c3
  have c1 := MrgKit.WordR_seqC t2 c2
  have pre0 := MrgKit.WordR_seqC t1 c1
  -- ### the block word
  have hb := hblk main p r m sh sgn wb (blkArr r u m i) e (Lacc :: pM m sh sgn r p ++ rest)
    hm2 hmr hsgn hp hwb hind happ
  have pre : WordR main (lvlPre uncP rollP swP drP)
      (fun vs => vs = .cons (ofList (cvecs wb)) (prepVR m sh sgn r p) :: Lacc
        :: pM m sh sgn r p ++ rest)
      (fun _ out => out = ofList (cvecs wb) :: .int (m : ℤ) :: .int (sh : ℤ) :: .int sgn
        :: .int (r : ℤ) :: .int (p : ℤ) :: Lacc :: pM m sh sgn r p ++ rest)
      (fun _ => 6 * Kuc + (5 * (Kr * 2 * (3 * L + 4)) + (Ksw * (3 * L + 4) + (Kdr * 2
        + Kr * 6 * (3 * L + 4))))) := by
    refine MrgKit.WordR_weaken pre0 (fun vs hvs => hvs) (fun vs out _ hQ => hQ) (fun vs _ => ?_)
    omega
  -- ### the suffix
  have suf : ∀ mid, (∃ ws' : List (List (ℤ × ℤ)),
      mid = ofList (cvecs ws') :: .int (m : ℤ) :: .int (sh : ℤ) :: .int sgn :: .int (r : ℤ)
        :: .int (p : ℤ) :: Lacc :: pM m sh sgn r p ++ rest ∧ ws'.length = m ∧
      (∀ w ∈ ws', InDiscVec p r w) ∧
      ApproxSL p r m ws' (lvlN r m sgn (blkArr r u m i)) (e + 1)) →
      WordR main (lvlSuf rollP drP consP)
        (fun vs => vs = mid)
        (fun _ out => ∃ ws' : List (List (ℤ × ℤ)),
          out = .cons (ofList (cvecs ws')) Lacc :: pM m sh sgn r p ++ rest ∧ ws'.length = m ∧
          (∀ w ∈ ws', InDiscVec p r w) ∧
          ApproxSL p r m ws' (lvlN r m sgn (blkArr r u m i)) (e + 1))
        (fun _ => 5 * (Kr * 6 * (L + 1)) + 5 * (Kdr * (L + 1)) + Kcv) := by
    rintro mid ⟨ws', hm, hlen, hind', happ'⟩
    subst hm
    have hL2 : pSz m sh sgn r p + 15 * (m + 1) * (r + 1) * (p + 1) + 2 ≤ L := hL
    have hs := lvlBodySuffix hroll hdr hcons m sh sgn r p ws' Lacc rest L hlen hind' hL2
    refine MrgKit.WordR_weaken hs (fun vs hvs => hvs) (fun vs out _ hQ => ?_) (fun vs _ => le_rfl)
    exact ⟨ws', hQ, hlen, hind', happ'⟩
  -- ### assemble
  have hmid2 : WordR main _ (fun vs => vs = .cons (ofList (cvecs wb)) (prepVR m sh sgn r p) :: Lacc
        :: pM m sh sgn r p ++ rest)
      (fun _ out => ∃ ws' : List (List (ℤ × ℤ)),
        out = ofList (cvecs ws') :: .int (m : ℤ) :: .int (sh : ℤ) :: .int sgn :: .int (r : ℤ)
          :: .int (p : ℤ) :: Lacc :: pM m sh sgn r p ++ rest ∧ ws'.length = m ∧
        (∀ w ∈ ws', InDiscVec p r w) ∧ ApproxSL p r m ws' (blkArr r u m i) e)
      (fun _ => 6 * Kuc + (5 * (Kr * 2 * (3 * L + 4)) + (Ksw * (3 * L + 4) + (Kdr * 2
        + Kr * 6 * (3 * L + 4))))) :=
    MrgKit.WordR_weaken pre (fun vs hvs => hvs)
      (fun vs out _ hQ => ⟨wb, hQ, hwb, hind, happ⟩) (fun vs _ => le_rfl)
  have h2mid : ∀ mid, (∃ ws' : List (List (ℤ × ℤ)),
        mid = ofList (cvecs ws') :: .int (m : ℤ) :: .int (sh : ℤ) :: .int sgn :: .int (r : ℤ)
          :: .int (p : ℤ) :: Lacc :: pM m sh sgn r p ++ rest ∧ ws'.length = m ∧
        (∀ w ∈ ws', InDiscVec p r w) ∧ ApproxSL p r m ws' (blkArr r u m i) e) →
      WordR main blkP (fun vs => vs = mid)
        (fun _ out => ∃ ws' : List (List (ℤ × ℤ)),
          out = ofList (cvecs ws') :: .int (m : ℤ) :: .int (sh : ℤ) :: .int sgn :: .int (r : ℤ)
            :: .int (p : ℤ) :: Lacc :: pM m sh sgn r p ++ rest ∧ ws'.length = m ∧
          (∀ w ∈ ws', InDiscVec p r w) ∧
          ApproxSL p r m ws' (lvlN r m sgn (blkArr r u m i)) (e + 1))
        (fun _ => Kb * m * (r + 1) * (p + 1) + Kb) := by
    rintro mid ⟨ws', hm, hlen, hind', happ'⟩
    subst hm
    exact hblk main p r m sh sgn ws' (blkArr r u m i) e (Lacc :: pM m sh sgn r p ++ rest)
      hm2 hmr hsgn hp hlen hind' happ'
  have hbs : ∀ mid, (∃ ws' : List (List (ℤ × ℤ)),
        mid = ofList (cvecs ws') :: .int (m : ℤ) :: .int (sh : ℤ) :: .int sgn :: .int (r : ℤ)
          :: .int (p : ℤ) :: Lacc :: pM m sh sgn r p ++ rest ∧ ws'.length = m ∧
        (∀ w ∈ ws', InDiscVec p r w) ∧ ApproxSL p r m ws' (blkArr r u m i) e) →
      WordR main (blkP ;;; lvlSuf rollP drP consP)
        (fun vs => vs = mid)
        (fun _ out => ∃ ws' : List (List (ℤ × ℤ)),
          out = .cons (ofList (cvecs ws')) Lacc :: pM m sh sgn r p ++ rest ∧ ws'.length = m ∧
          (∀ w ∈ ws', InDiscVec p r w) ∧
          ApproxSL p r m ws' (lvlN r m sgn (blkArr r u m i)) (e + 1))
        (fun _ => Kb * m * (r + 1) * (p + 1) + Kb
          + (5 * (Kr * 6 * (L + 1)) + 5 * (Kdr * (L + 1)) + Kcv)) := by
    rintro mid hmid'
    exact WordR_seq_gen (h2mid mid hmid') (fun mid' h' => suf mid' h')
  have h1 := WordR_seq_gen hmid2 hbs
  refine MrgKit.WordR_weaken (h := h1) (hP := fun vs hvs => hvs)
    (hQ := fun vs out _ hQ => hQ) (hC := fun vs _ => ?_)
  simp only [lvlBodyCost]
  omega


/-- The fold invariant: the accumulator holds the output blocks produced so far (in reverse
order), the five parameters sit untouched below it, and every completed block satisfies its
target bound. -/
def LvlI (m sh : ℕ) (sgn : ℤ) (r p : ℕ) (u : Arr r) (e : ℝ) (rest : List Val) :
    ℕ → List Val → Prop :=
  fun i acc => ∃ W : List (List (List (ℤ × ℤ))),
    acc = ofList (W.map bVal) :: pM m sh sgn r p ++ rest ∧ W.length = i ∧
    (∀ w ∈ W, w.length = m ∧ (∀ z ∈ w, InDiscVec p r z)) ∧
    (∀ b < i, ApproxSL p r m ((W.reverse).getD b []) (lvlN r m sgn (blkArr r u m b)) (e + 1))

theorem forall₂_getD {α : Type*} {P : α → α → Prop} {l₁ l₂ : List α} (d : α)
    (h : List.Forall₂ P l₁ l₂) : ∀ i < l₂.length, P (l₁.getD i d) (l₂.getD i d) := by
  induction h with
  | nil => intro i hi; simp at hi
  | cons hab _ ih =>
    intro i hi
    cases i with
    | zero => simpa using hab
    | succ i => simpa using ih i (by simpa using hi)

/-- Reading a chunk value. -/
theorem getD_chunkVals (m : ℕ) (ws : List (List (ℤ × ℤ))) {i : ℕ}
    (hi : i < (chunkVals m ws).length) :
    (chunkVals m ws).getD i .nil = ofList (List.take m (List.drop (i * m) (cvecs ws))) := by
  have h : i < (chunkVals m ws).length := hi
  rw [chunkVals] at h ⊢
  rw [List.getD_eq_getElem _ _ h, List.getElem_map, List.getElem_range]

/-- The `mapList`-wrapped block equals the value of the block's coefficient vectors. -/
theorem cvecs_take_drop (m : ℕ) (ws : List (List (ℤ × ℤ))) (i : ℕ) :
    List.take m (List.drop (i * m) (cvecs ws)) = cvecs (cws m ws i) := by
  rw [cws, cvecs_take, cvecs_drop]

/-- One fold iteration: given the element (a block plus the parameter value) and the invariant,
the body produces the next accumulator state. -/
theorem lvlFoldStep {main : Cmd} {uncP : Cmd} {rollP : ℕ → Cmd} {drP swP consP blkP : Cmd}
    {Kuc Kr Kdr Ksw Kcv Kb : ℕ}
    (hunc : WordR main uncP (fun vs => ∃ a b r, vs = .cons a b :: r)
      (fun vs out => ∃ a b r, vs = .cons a b :: r ∧ out = a :: b :: r) (fun _ => Kuc))
    (hroll : ∀ k, WordR main (rollP k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs.eraseIdx k)
      (fun vs => Kr * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    (hdr : WordR main drP (fun vs => vs ≠ [])
      (fun vs out => ∃ v r, vs = v :: r ∧ out = r) (fun vs => Kdr * (vsz (vs.headD .nil) + 1)))
    (hsw : WordR main swP (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = b :: a :: rest)
      (fun vs => Ksw * (vsz (vs.getD 0 .nil) + vsz (vs.getD 1 .nil) + 1)))
    (hcons : WordR main consP (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = .cons a b :: rest) (fun _ => Kcv))
    (hblk : ∀ (main : Cmd) (p r m sh : ℕ) (sgn : ℤ) (ws : List (List (ℤ × ℤ))) (u : Arr r) (e : ℝ)
        (rest : List Val),
      2 ≤ m → m * 2 ^ sh = 2 * r → (sgn = 1 ∨ sgn = -1) → 2 * r < 2 ^ p →
      ws.length = m → (∀ w ∈ ws, InDiscVec p r w) → ApproxSL p r m ws u e →
      WordR main blkP (fun vs => vs = ofList (cvecs ws) :: .int (m : ℤ) :: .int (sh : ℤ) :: .int sgn
        :: .int (r : ℤ) :: .int (p : ℤ) :: rest)
        (fun _ out => ∃ ws', out = ofList (cvecs ws') :: .int (m : ℤ) :: .int (sh : ℤ) :: .int sgn
          :: .int (r : ℤ) :: .int (p : ℤ) :: rest ∧ ws'.length = m ∧ (∀ w ∈ ws', InDiscVec p r w) ∧
          ApproxSL p r m ws' (lvlN r m sgn u) (e + 1))
        (fun _ => Kb * m * (r + 1) * (p + 1) + Kb))
    (m sh : ℕ) (sgn : ℤ) (r p : ℕ) (u : Arr r) (e : ℝ) (t : ℕ)
    (ws : List (List (ℤ × ℤ))) (rest : List Val)
    (hm2 : 2 ≤ m) (hmr : m * 2 ^ sh = 2 * r) (hsgn : sgn = 1 ∨ sgn = -1) (hp : 2 * r < 2 ^ p)
    (hlen : ws.length = t) (hind : ∀ w ∈ ws, InDiscVec p r w)
    (happ : ApproxSL p r t ws u e)
    (L : ℕ) (hL : pSz m sh sgn r p + 15 * (m + 1) * (r + 1) * (p + 1) + 2 ≤ L)
    (ys : List Val)
    (hF : List.Forall₂ (fun x y => y = .cons x (prepVR m sh sgn r p)) (chunkVals m ws) ys)
    (i : ℕ) (hi : i < ys.length) (acc : List Val) (hI : LvlI m sh sgn r p u e rest i acc) :
    WordR main (lvlPre uncP rollP swP drP ;;; blkP ;;; lvlSuf rollP drP consP)
      (fun vs => vs = ys.getD i .nil :: acc)
      (fun _ out => LvlI m sh sgn r p u e rest (i + 1) out)
      (fun _ => lvlBodyCost Kuc Kr Ksw Kdr Kcv Kb m r p L) := by
  obtain ⟨W, hacc, hWlen, hWall, hWb⟩ := hI
  have hcl : (cvecs ws).length = ws.length := by simp only [cvecs, List.length_map]
  have hych : (chunkVals m ws).length = ws.length / m := by
    rw [chunkVals, List.length_map, List.length_range, hcl]
  have hi' : i < (chunkVals m ws).length := by
    have : (chunkVals m ws).length = ys.length := hF.length_eq
    omega
  have hdiv : i < ws.length / m := by rwa [hych] at hi'
  have hQi := forall₂_getD (.nil : Val) hF i hi
  have hQi' : ys.getD i .nil = .cons (ofList (cvecs (cws m ws i))) (prepVR m sh sgn r p) := by
    rw [hQi, getD_chunkVals m ws hi', cvecs_take_drop]
  have hwb : (cws m ws i).length = m := by
    rw [cws, List.length_take, List.length_drop]
    have h1 : (i + 1) * m ≤ ws.length :=
      (Nat.le_div_iff_mul_le (by omega : 0 < m)).mp (Nat.succ_le_of_lt hdiv)
    rw [Nat.succ_mul] at h1
    omega
  have hind' : ∀ w ∈ cws m ws i, InDiscVec p r w := by
    intro w hw
    rw [cws] at hw
    have hw' : w ∈ ws := List.Sublist.subset (List.drop_sublist (i * m) ws)
      (List.Sublist.subset (List.take_sublist m (ws.drop (i * m))) hw)
    exact hind w hw'
  have hle : (i + 1) * m ≤ t := by
    have h1 : (i + 1) * m ≤ ws.length :=
      (Nat.le_div_iff_mul_le (by omega : 0 < m)).mp (Nat.succ_le_of_lt hdiv)
    omega
  have happ' : ApproxSL p r m (cws m ws i) (blkArr r u m i) e :=
    approxSL_block p r t m u ws e i hle happ
  refine MrgKit.WordR_weaken
    (lvlBody hunc hroll hdr hsw hcons hblk m sh sgn r p u e i (cws m ws i)
      (ofList (W.map bVal)) rest L hm2 hmr hsgn hp hwb hind' happ' hL) ?_ ?_ ?_
  · intro vs hvs
    simp only [hvs, hacc, hQi', List.cons_append]
  · intro vs out hvs hQ
    obtain ⟨ws'', hout, hlen'', hind'', happ''⟩ := hQ
    refine ⟨ws'' :: W, ?_, by rw [List.length_cons, hWlen], ?_, ?_⟩
    · rw [hout]
      rfl
    · intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact ⟨hlen'', hind''⟩
      · exact ⟨(hWall w hw).1, (hWall w hw).2⟩
    · intro b hb
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hb) with hlt | heq
      · rw [show (ws'' :: W).reverse = W.reverse ++ [ws''] from List.reverse_cons (a := ws'') (as := W),
          List.getD_append _ _ _ _ (by rw [List.length_reverse, hWlen]; exact hlt)]
        exact hWb b hlt
      · subst heq
        rw [show (ws'' :: W).reverse = W.reverse ++ [ws''] from List.reverse_cons (a := ws'') (as := W),
          List.getD_append_right _ _ _ _ (by rw [List.length_reverse, hWlen]),
          List.length_reverse, hWlen, Nat.sub_self]
        exact happ''
  · intro vs hvs
    exact le_rfl

/-- Flattening a list of coefficient vectors commutes with `cvecs`. -/
theorem cvecs_flatten (W : List (List (List (ℤ × ℤ)))) :
    ((W.map cvecs).flatten) = cvecs (W.flatten) := by
  show (W.map (List.map cvecVal)).flatten = (W.flatten).map cvecVal
  exact (List.map_flatten (L := W) (f := cvecVal)).symm

/-- The teardown: reverse the accumulated blocks and flatten them. -/
theorem lvlTeardown {main : Cmd} {revP fltP : Cmd} {Krev Kflt : ℕ}
    (hrev : ∀ (xs : List Val), WordR main revP
      (fun vs => ∃ rest, vs = ofList xs :: rest)
      (fun vs out => ∃ rest, vs = ofList xs :: rest ∧ out = ofList xs.reverse :: rest)
      (fun _ => Krev * (vsz (ofList xs) + 1)))
    (hflt : ∀ (xss : List (List Val)), WordR main fltP
      (fun vs => ∃ rest, vs = ofList (xss.map ofList) :: rest)
      (fun vs out => ∃ rest, vs = ofList (xss.map ofList) :: rest ∧
        out = ofList xss.flatten :: rest)
      (fun _ => Kflt * (vsz (ofList (xss.map ofList)) + 1)))
    (m sh : ℕ) (sgn : ℤ) (r p : ℕ) (W : List (List (List (ℤ × ℤ)))) (rest : List Val)
    (D : ℕ) (hD : Krev * (vsz (ofList (W.map bVal)) + 1)
      + Kflt * (vsz (ofList ((W.reverse).map cvecs |>.map ofList)) + 1) ≤ D) :
    WordR main (revP ;;; fltP)
      (fun vs => vs = ofList (W.map bVal) :: pM m sh sgn r p ++ rest)
      (fun _ out => out = ofList (cvecs ((W.reverse).flatten)) :: pM m sh sgn r p ++ rest)
      (fun _ => D) := by
  have e1 : WordR main revP (fun vs => vs = ofList (W.map bVal) :: pM m sh sgn r p ++ rest)
      (fun _ out => out = ofList ((W.map bVal).reverse) :: pM m sh sgn r p ++ rest)
      (fun _ => Krev * (vsz (ofList (W.map bVal)) + 1)) :=
    reverseStep hrev _ _ _ le_rfl
  have e2 : WordR main fltP
      (fun vs => vs = ofList ((W.map bVal).reverse) :: pM m sh sgn r p ++ rest)
      (fun _ out => out = ofList (cvecs ((W.reverse).flatten)) :: pM m sh sgn r p ++ rest)
      (fun _ => Kflt * (vsz (ofList ((W.reverse).map cvecs |>.map ofList)) + 1)) := by
    have hval : ofList (((W.reverse).map cvecs).map ofList) = ofList ((W.map bVal).reverse) := by
      rw [List.map_map, List.map_reverse]
      rfl
    have hstep : WordR main fltP
        (fun vs => vs = ofList (((W.reverse).map cvecs).map ofList) :: pM m sh sgn r p ++ rest)
        (fun _ out => out = ofList (((W.reverse).map cvecs).flatten) :: pM m sh sgn r p ++ rest)
        (fun _ => Kflt * (vsz (ofList (((W.reverse).map cvecs).map ofList)) + 1)) :=
      flattenStep hflt ((W.reverse).map cvecs) (pM m sh sgn r p ++ rest) _ le_rfl
    refine MrgKit.WordR_weaken hstep (fun vs hvs => ?_) (fun vs out _ hQ => ?_) (fun vs _ => le_rfl)
    · rw [hvs, hval]
    · rw [hQ, cvecs_flatten]
  refine MrgKit.WordR_weaken (MrgKit.WordR_seqC e1 e2) (fun vs hvs => hvs)
    (fun vs out _ hQ => hQ) (fun vs _ => hD)

end Work.SynFFT
