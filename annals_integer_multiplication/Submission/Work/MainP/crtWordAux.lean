import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.MainP.crtLib
import Submission.Work.MainP.crtTail
import Submission.Work.MainP.crtMath

/-!
# `crtWordAux`: assembly of the CRT reindexing word

Builds the `CrtLib` bundle out of the four library-level propositions (`CrtPieces`), prepends the
argument shuffling `crtPrep`, and runs `if dir = 0 then branch0 else branch1` on the reindexed
argument list. The two branches and the preparation are taken as hypotheses here so that the
assembly can be developed against their statements; `Submission/Work/MainP/crtWord.lean` plugs in
the proved lemmas.
-/

set_option autoImplicit false

namespace Work.MainP

open HvdH

/-- The three word lemmas the assembly consumes, as hypotheses. -/
structure CrtParts (hK : KernelLib) (hI : IntLib) (hL : LayoutLib) : Prop where
  prep : ∀ L : CrtLib, ∃ (prog : Cmd) (C : ℕ),
      ∀ (main : Cmd) (ss : List ℕ) (S : ℕ) (xs : List Val) (dir : ℕ),
        1 ≤ S → dir ≤ 1 → xs.length = S →
        WordR main prog
          (fun vs => ∃ rest, vs = .int (dir : ℤ) :: intList ss :: ofList xs :: rest)
          (fun vs out => ∃ rest, vs = .int (dir : ℤ) :: intList ss :: ofList xs :: rest ∧
            out = .int (dir : ℤ) :: .int (S : ℤ) :: intList ss :: ofList xs :: rest)
          (fun _ => C * CU L ss S xs)
  b0 : ∀ L : CrtLib, ∃ (prog : Cmd) (C : ℕ),
      ∀ (main : Cmd) (ss : List ℕ) (S : ℕ) (xs : List Val) (rest : List Val),
        (∀ s ∈ ss, 1 ≤ s) → S = ss.prod → ss.Pairwise Nat.Coprime → xs.length = S →
        WordR main prog
          (fun vs => vs = .int (S : ℤ) :: intList ss :: ofList xs :: rest)
          (fun _ out => ∃ ys, out = ofList ys :: rest ∧ ys.length = S ∧
            ∀ m < S, ys.getD m .nil = xs.getD (invLab (sigmaList ss) m) .nil)
          (fun _ => C * CU L ss S xs)
  b1 : ∀ L : CrtLib, ∃ (prog : Cmd) (C : ℕ),
      ∀ (main : Cmd) (ss : List ℕ) (S : ℕ) (xs : List Val) (rest : List Val),
        (∀ s ∈ ss, 1 ≤ s) → S = ss.prod → ss.Pairwise Nat.Coprime → xs.length = S →
        WordR main prog
          (fun vs => vs = .int (S : ℤ) :: intList ss :: ofList xs :: rest)
          (fun _ out => ∃ ys, out = ofList ys :: rest ∧ ys.length = S ∧
            ∀ m < S, ys.getD m .nil = xs.getD (invLab (crtQ ss) m) .nil)
          (fun _ => C * CU L ss S xs)

theorem crtWord_aux (hK : KernelLib) (hI : IntLib) (hL : LayoutLib) (hP : CrtPieces)
    (hA : CrtParts hK hI hL) : CrtWordProp := by
  obtain ⟨pJoin, KJoin, hJoin⟩ := hP.join
  obtain ⟨pStrip, KStrip, hStrip⟩ := hP.strip
  obtain ⟨pLab, KLab, hLab⟩ := hP.lab
  obtain ⟨pSort, KSort, hSort⟩ := hL.sortByKey
  obtain ⟨pSwap, KSwap, hSwap⟩ := hK.swap
  obtain ⟨pDup, KDup, hDup⟩ := hK.dup
  obtain ⟨pDrop, KDrop, hDrop⟩ := hK.drop
  obtain ⟨pUnc, KUnc, hUnc⟩ := hK.unconsV
  obtain ⟨pCons, KCons, hCons⟩ := hK.consV
  obtain ⟨pPush, KPush, hPush⟩ := hK.pushVal
  obtain ⟨pRep0, KRep, hRep0⟩ := hL.replicate
  obtain ⟨pEnum, KEnum, hEnum⟩ := hL.enumerate
  obtain ⟨pMap, KMap, hMap⟩ := hK.mapList
  obtain ⟨pRoll, KRoll, hRoll⟩ := hK.roll
  obtain ⟨pLen, KLen, hLen⟩ := hL.length
  obtain ⟨pIfz, KIfz, hIfz⟩ := hK.ifZero
  let L : CrtLib :=
    { hK := hK
      hSorted := hP.sorted
      pLab := pLab, KLab := KLab, hLab := hLab
      pJoin := pJoin, KJoin := KJoin, hJoin := hJoin
      pStrip := pStrip, KStrip := KStrip, hStrip := hStrip
      pSort := pSort, KSort := KSort, hSort := hSort
      pSwap := pSwap, KSwap := KSwap, hSwap := hSwap
      pDup := pDup, KDup := KDup, hDup := hDup
      pDrop := pDrop, KDrop := KDrop, hDrop := hDrop
      pUnc := pUnc, KUnc := KUnc, hUnc := hUnc
      pCons := pCons, KCons := KCons, hCons := hCons
      pPush := pPush, KPush := KPush, hPush := hPush
      pRep := fun _ => pRep0, KRep := KRep, hRep := fun main k v => hRep0 main k v
      pEnum := pEnum, KEnum := KEnum, hEnum := hEnum
      pMap := pMap, KMap := KMap, hMap := hMap
      pRoll := pRoll, KRoll := KRoll, hRoll := hRoll
      pLen := pLen, KLen := KLen, hLen := hLen
      pIfz := pIfz, KIfz := KIfz, hIfz := hIfz }
  obtain ⟨pPrep, Cpre, hPrepW⟩ := hA.prep L
  obtain ⟨pB0, C0, hB0W⟩ := hA.b0 L
  obtain ⟨pB1, C1, hB1W⟩ := hA.b1 L
  refine ⟨.seq pPrep (pIfz pB0 pB1), 100000 * (KF L * (Cpre + C0 + C1 + 4)), ?_⟩
  intro main ss dir xs hpos hcop hxs hdir
  have hpos0 : ∀ s ∈ ss, 0 < s := fun s hs => by have := hpos s hs; omega
  have hS1 : 1 ≤ ss.prod := prod_pos_of_pos hpos
  have hdirz : (dir : ℤ) = 0 ↔ dir = 0 := by omega
  have hdirisz : isz (dir : ℤ) + 1 ≤ 4 := by
    rw [isz_natCast, iszN]
    have : dir.size ≤ 1 := Nat.size_le_size hdir
    omega
  have hKIfz : L.KIfz ≤ KF L := KF_ge L (by simp [kList])
  have hCUsb : CU L ss ss.prod xs = KF L * SB ss ss.prod xs := rfl
  have hSBpos : 1 ≤ SB ss ss.prod xs := one_le_SB ss ss.prod xs
  have hCUge : KF L ≤ CU L ss ss.prod xs := by
    rw [hCUsb]
    calc KF L = KF L * 1 := (Nat.mul_one _).symm
      _ ≤ KF L * SB ss ss.prod xs := Nat.mul_le_mul_left _ hSBpos
  -- the word, for a fixed ambient tail
  have hchain : ∀ rest : List Val, WordR main (.seq pPrep (pIfz pB0 pB1))
      (fun vs => vs = .int (dir : ℤ) :: intList ss :: ofList xs :: rest)
      (fun _ out => ∃ ys, out = ofList ys :: rest ∧ ys.length = ss.prod ∧
        ∀ m < ss.prod, (dir = 0 → ys.getD (crtIdx ss m) .nil = xs.getD m .nil) ∧
          (dir = 1 → ys.getD m .nil = xs.getD (crtIdx ss m) .nil))
      (fun _ => 100000 * (KF L * (Cpre + C0 + C1 + 4))
        * (vsz (ofList xs) + ss.prod * (vsz (intList ss) + 1) + 1) * (ss.prod.size + 1)) := by
    intro rest
    let restT : List Val := .int (ss.prod : ℤ) :: intList ss :: ofList xs :: rest
    have hpR : WordR main pPrep
        (fun vs => vs = .int (dir : ℤ) :: intList ss :: ofList xs :: rest)
        (fun _ out => out = .int (dir : ℤ) :: restT)
        (fun _ => Cpre * CU L ss ss.prod xs) := by
      refine WordR.conseqK (hPrepW main ss ss.prod xs dir hS1 hdir hxs) L.hK ?_ ?_ ?_
      · intro vs hvs; exact ⟨rest, hvs⟩
      · intro vs out hvs hq
        obtain ⟨r', h1, h2⟩ := hq
        rw [hvs] at h1
        have h3 : r' = rest := by simpa using h1.symm
        subst h3
        exact h2
      · intro vs _; exact le_rfl
    have hb0 := hB0W main ss ss.prod xs rest hpos rfl hcop hxs
    have hb1 := hB1W main ss ss.prod xs rest hpos rfl hcop hxs
    have hifz : WordR main (pIfz pB0 pB1) (fun vs => vs = .int (dir : ℤ) :: restT)
        (fun _ out => ((dir : ℤ) = 0 → ∃ ys, out = ofList ys :: rest ∧ ys.length = ss.prod ∧
            ∀ m < ss.prod, ys.getD m .nil = xs.getD (invLab (sigmaList ss) m) .nil) ∧
          ((dir : ℤ) ≠ 0 → ∃ ys, out = ofList ys :: rest ∧ ys.length = ss.prod ∧
            ∀ m < ss.prod, ys.getD m .nil = xs.getD (invLab (crtQ ss) m) .nil))
        (fun _ => L.KIfz * (isz (dir : ℤ) + 1)
          + max (C0 * CU L ss ss.prod xs) (C1 * CU L ss ss.prod xs)) :=
      L.hIfz main pB0 pB1 (dir : ℤ) restT _ _
        (C0 * CU L ss ss.prod xs) (C1 * CU L ss ss.prod xs)
        (fun _ => hb0) (fun _ => hb1)
    refine WordR.conseqK (WordR.seqK hpR hifz L.hK
      (B := fun _ => L.KIfz * (isz (dir : ℤ) + 1)
        + max (C0 * CU L ss ss.prod xs) (C1 * CU L ss ss.prod xs)) ?_) L.hK
      (fun vs hvs => hvs) ?_ ?_
    · intro vs mid hvs hq
      refine ⟨?_, le_rfl⟩
      rw [hq]
    · intro vs out hvs hq
      obtain ⟨_mid, _hmid, hcase⟩ := hq
      by_cases h0 : dir = 0
      · obtain ⟨ys, hout, hlen, hget⟩ := hcase.1 (hdirz.mpr h0)
        refine ⟨ys, hout, hlen, fun m hm => ⟨fun _ => ?_, fun h1 => absurd h1 (by omega)⟩⟩
        rw [hget (crtIdx ss m) (crtIdx_lt hpos0 m),
          invLab_sigmaList hcop hpos0 (crtIdx_lt hpos0 m), crtPinv_crtIdx hcop hpos0 hm]
      · have h0' : (dir : ℤ) ≠ 0 := fun h => h0 (hdirz.mp h)
        obtain ⟨ys, hout, hlen, hget⟩ := hcase.2 h0'
        refine ⟨ys, hout, hlen, fun m hm => ⟨fun h2 => absurd h2 h0, fun _ => ?_⟩⟩
        rw [hget m hm, invLab_crtQ hcop hpos0 hm]
    · intro vs hvs
      have hmax : max (C0 * CU L ss ss.prod xs) (C1 * CU L ss ss.prod xs)
          ≤ (C0 + C1) * CU L ss ss.prod xs := by
        rcases le_total C0 C1 with h | h
        · rw [max_eq_right (Nat.mul_le_mul_right _ h)]
          exact Nat.mul_le_mul_right _ (by omega)
        · rw [max_eq_left (Nat.mul_le_mul_right _ h)]
          exact Nat.mul_le_mul_right _ (by omega)
      have hstep : L.KIfz * (isz (dir : ℤ) + 1) ≤ KF L * 4 := by
        have h3 : isz (dir : ℤ) + 1 ≤ 4 := hdirisz
        calc L.KIfz * (isz (dir : ℤ) + 1) ≤ KF L * (isz (dir : ℤ) + 1) :=
              Nat.mul_le_mul_right _ hKIfz
          _ ≤ KF L * 4 := Nat.mul_le_mul_left _ h3
      have h4 : 4 * KF L ≤ 4 * CU L ss ss.prod xs := Nat.mul_le_mul_left _ hCUge
      have hR : 100000 * (KF L * (Cpre + C0 + C1 + 4))
            * (vsz (ofList xs) + ss.prod * (vsz (intList ss) + 1) + 1) * (ss.prod.size + 1)
          = 100000 * (Cpre + C0 + C1 + 4) * CU L ss ss.prod xs := by
        simp only [CU, SB, PB, QB]
        ring
      rw [hR]
      have hb : Cpre * CU L ss ss.prod xs + (KF L * 4 + (C0 + C1) * CU L ss ss.prod xs)
          ≤ (Cpre + C0 + C1 + 4) * CU L ss ss.prod xs := by
        have h7 : KF L * 4 ≤ 4 * CU L ss ss.prod xs := by
          calc KF L * 4 = 4 * KF L := by ring
            _ ≤ 4 * CU L ss ss.prod xs := h4
        calc Cpre * CU L ss ss.prod xs + (KF L * 4 + (C0 + C1) * CU L ss ss.prod xs)
            ≤ Cpre * CU L ss ss.prod xs
              + (4 * CU L ss ss.prod xs + (C0 + C1) * CU L ss ss.prod xs) := by omega
          _ = (Cpre + C0 + C1 + 4) * CU L ss ss.prod xs := by ring
      have hmain : Cpre * CU L ss ss.prod xs
          + (L.KIfz * (isz (dir : ℤ) + 1) + max (C0 * CU L ss ss.prod xs) (C1 * CU L ss ss.prod xs))
          ≤ Cpre * CU L ss ss.prod xs + (KF L * 4 + (C0 + C1) * CU L ss ss.prod xs) :=
        Nat.add_le_add_left (Nat.add_le_add hstep hmax) _
      have hle : (Cpre + C0 + C1 + 4) ≤ 100000 * (Cpre + C0 + C1 + 4) := by
        calc (Cpre + C0 + C1 + 4) = (Cpre + C0 + C1 + 4) * 1 := (Nat.mul_one _).symm
          _ ≤ (Cpre + C0 + C1 + 4) * 100000 := Nat.mul_le_mul_left _ (by norm_num)
          _ = 100000 * (Cpre + C0 + C1 + 4) := by ring
      exact le_trans hmain (le_trans hb (Nat.mul_le_mul_right _ hle))
  intro vs hvs s R hstk
  obtain ⟨rest, rfl⟩ := hvs
  obtain ⟨out, s', n, hpost, hev, hn, hstk', hfr⟩ := hchain rest _ rfl s R hstk
  refine ⟨out, s', n, ?_, hev, hn, hstk', hfr⟩
  obtain ⟨ys, hout, hlen, hget⟩ := hpost
  exact ⟨rest, ys, rfl, hout, hlen, hget⟩

end Work.MainP
