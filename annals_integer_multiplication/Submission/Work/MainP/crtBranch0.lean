import Mathlib
import Submission.Work.MainP.crtLib
import Submission.Work.MainP.crtTail
import Submission.Work.MainP.crtMath
import Submission.Work.MainP.crtDefs

namespace Work.MainP

open HvdH

/-- The `pLab` phase of branch 0 costs at most two units. -/
theorem labPhase_cost_le (L : CrtLib) {ss : List ℕ} {S : ℕ} {xs : List Val} :
    L.KLab * (S * (vsz (intList ss) + 1) * (S.size + 1) + 1) ≤ 2 * CU L ss S xs := by
  have hKLab : L.KLab ≤ KF L := KF_ge L (by simp [kList])
  have h1 : S * (vsz (intList ss) + 1) ≤ PB ss S xs := by rw [PB]; omega
  have h2 : S * (vsz (intList ss) + 1) * (S.size + 1) ≤ SB ss S xs := by
    rw [SB, QB]
    exact Nat.mul_le_mul_right _ h1
  have h3 : S * (vsz (intList ss) + 1) * (S.size + 1) + 1 ≤ 2 * SB ss S xs := by
    have := one_le_SB ss S xs
    omega
  calc L.KLab * (S * (vsz (intList ss) + 1) * (S.size + 1) + 1)
      ≤ KF L * (S * (vsz (intList ss) + 1) * (S.size + 1) + 1) := Nat.mul_le_mul_right _ hKLab
    _ ≤ KF L * (2 * SB ss S xs) := Nat.mul_le_mul_left _ h3
    _ = 2 * (KF L * SB ss S xs) := by ring
    _ = 2 * CU L ss S xs := by rw [CU]

theorem crtBranch0 (L : Work.MainP.CrtLib) :
    ∃ (prog : HvdH.Cmd) (C : ℕ),
      ∀ (main : HvdH.Cmd) (ss : List ℕ) (S : ℕ) (xs : List HvdH.Val) (rest : List HvdH.Val),
        (∀ s ∈ ss, 1 ≤ s) → S = ss.prod → ss.Pairwise Nat.Coprime → xs.length = S →
        HvdH.WordR main prog
          (fun vs => vs = HvdH.Val.int (S : ℤ) :: HvdH.intList ss :: HvdH.ofList xs :: rest)
          (fun _ out => ∃ ys, out = HvdH.ofList ys :: rest ∧ ys.length = S ∧
            ∀ m < S, ys.getD m HvdH.Val.nil
              = xs.getD (Work.MainP.invLab (Work.MainP.sigmaList ss) m) HvdH.Val.nil)
          (fun _ => C * Work.MainP.CU L ss S xs) := by
  obtain ⟨pTail, hTail⟩ := tailWord L
  refine ⟨.seq L.pLab pTail, 102, ?_⟩
  intro main ss S xs rest hpos hS hcop hxs
  have hpos0 : ∀ s ∈ ss, 0 < s := fun s hs => by have := hpos s hs; omega
  have hlab : (sigmaList ss).length = S := by rw [sigmaList_length, ← hS]
  have hinj : ∀ i < S, ∀ j < S, (sigmaList ss).getD i 0 = (sigmaList ss).getD j 0 → i = j := by
    intro i hi j hj h
    exact sigmaList_inj hcop hpos0 (hS ▸ hi) (hS ▸ hj) h
  have hlt : ∀ i < S, (sigmaList ss).getD i 0 < S := by
    intro i hi
    have h := sigmaList_lt (ss := ss) hpos0 (hS ▸ hi)
    rwa [hS]
  have hLab1 : WordR main L.pLab
      (fun vs => vs = .int (S : ℤ) :: intList ss :: ofList xs :: rest)
      (fun _ out => out = intList (sigmaList ss) :: ofList xs :: rest)
      (fun _ => L.KLab * (S * (vsz (intList ss) + 1) * (S.size + 1) + 1)) := by
    refine WordR.conseqK (L.hLab main ss S hpos hS) L.hK ?_ ?_ ?_
    · intro vs hvs; exact ⟨ofList xs :: rest, hvs⟩
    · intro vs out hvs hq
      obtain ⟨rest', hvs', hout⟩ := hq
      rw [hvs'] at hvs
      have hrest : rest' = ofList xs :: rest := by
        simpa using (List.cons.inj (List.cons.inj hvs).2).2
      rw [hrest] at hout; exact hout
    · intro vs hvs; exact le_rfl
  have hTail1 : WordR main pTail
      (fun vs => vs = intList (sigmaList ss) :: ofList xs :: rest)
      (fun _ out => ∃ ys, out = ofList ys :: rest ∧ ys.length = S ∧
        ∀ m < S, ys.getD m .nil = xs.getD (invLab (sigmaList ss) m) .nil)
      (fun _ => BUD L ss S xs) := by
    refine WordR.conseqK
      (hTail ss (sigmaList ss) S xs rest hpos hS hxs hlab hinj hlt main) L.hK ?_ ?_ ?_
    · intro vs hvs
      rw [hvs, intList_eq_ofList]
    · intro vs out hvs hq; exact hq
    · intro vs hvs; exact le_rfl
  have hAll : WordR main (.seq L.pLab pTail)
      (fun vs => vs = .int (S : ℤ) :: intList ss :: ofList xs :: rest)
      (fun vs out => ∃ mid, mid = intList (sigmaList ss) :: ofList xs :: rest ∧
        (∃ ys, out = ofList ys :: rest ∧ ys.length = S ∧
          ∀ m < S, ys.getD m .nil = xs.getD (invLab (sigmaList ss) m) .nil))
      (fun vs => L.KLab * (S * (vsz (intList ss) + 1) * (S.size + 1) + 1)
        + BUD L ss S xs) :=
    WordR.seqK hLab1 hTail1 L.hK (B := fun _ => BUD L ss S xs)
      (fun vs mid hvs hq => ⟨hq, le_rfl⟩)
  have hLabCost := labPhase_cost_le (L := L) (ss := ss) (S := S) (xs := xs)
  refine WordR.conseqK hAll L.hK (fun vs hvs => hvs) (fun vs out hvs hq => ?_)
    (fun vs hvs => ?_)
  · obtain ⟨mid, hmid, hys⟩ := hq
    subst hmid
    exact hys
  · have hb : BUD L ss S xs = 100 * CU L ss S xs := rfl
    calc L.KLab * (S * (vsz (intList ss) + 1) * (S.size + 1) + 1) + BUD L ss S xs
        ≤ 2 * CU L ss S xs + 100 * CU L ss S xs := Nat.add_le_add hLabCost (le_of_eq hb)
      _ = 102 * CU L ss S xs := by ring

end Work.MainP
