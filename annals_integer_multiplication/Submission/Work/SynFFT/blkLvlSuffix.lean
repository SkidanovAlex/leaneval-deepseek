import Mathlib
import Submission.Work.SynFFT.kit2
import Submission.Work.SynFFT.mrgBlkDefs
import Submission.Work.SynFFT.blkLvlDefs
import Submission.Work.SynFFT.blkLvlSuffixKit
import Submission.Work.SynFFT.fstCompPass
import Submission.Work.SynFFT.sndCompPass
import Submission.Work.SynFFT.takeAppendStep

/-!
# `Work.SynFFT.blkLvlSuffix`: the list-level suffix of one block level pass

The block level pass of the synthetic FFT (`HasBlkLvl`, `Submission/Work/SynFFT/kit2.lean`)
bundles, for every butterfly pair of a block, its two outputs into one `cons` value, and then has
to put the outputs back in the order the next level expects: the `m/2` "sum" outputs followed by
the `m/2` "difference" outputs.  At the list level the bunched list `Z` (`Z[i] = cons low_i
high_i`, `Z.length = m - m/2`) is therefore sent to

`(Z.map vfst).take (m / 2) ++ Z.map vsnd`.

The word is assembled from three pieces, each proved in its own file:

* `fstCompPass` / `sndCompPass` — `ofList xs ↦ ofList (xs.map vfst)` resp. `ofList (xs.map vsnd)`
  for a list of `cons` values of size `≤ Lb` (a `KLib.mapList` with the per-element word
  `unconsV ; swap ; drop` resp. `unconsV ; drop`);
* `takeAppendStep` — `ofList F :: ofList S :: int m ↦ ofList (F.take (m/2) ++ S) :: int m`
  (`pushVal 2 ; roll 3 ; fdiv` to halve `m`, then `LayoutLib.take` and `LayoutLib.append`).

The assembled program is `dup ; sndCompPass ; swap ; fstCompPass ; takeAppendStep`: duplicate `Z`,
replace the copy on top by the list of its second components, swap the two lists, replace the
remaining `Z` by the list of its first components, and finally halve/`take`/`append`.  Every step
costs `O(m (Lb+1) + 1)`, hence so does the whole word.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.SynFFT

open HvdH

local infixl:68 " ;;; " => HvdH.Cmd.seq

/-- The suffix of the block level pass: from the list `Z` of bunched butterfly outputs
(`Z[i] = cons low_i high_i`) it produces `(Z.map vfst).take (m/2) ++ Z.map vsnd`, i.e. the first
`m/2` "sum" outputs followed by all "difference" outputs — the list-level result of one block
level pass. -/
theorem blkLvlSuffix (hk : Work.SynFFT.KLib) (hi : HvdH.IntLib) (hl : HvdH.LayoutLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (m Lb : ℕ) (Z rest : List HvdH.Val),
      2 ≤ m → Z.length = m - m / 2 → (∀ v ∈ Z, HvdH.vsz v ≤ Lb) →
      (∀ v ∈ Z, ∃ a b : HvdH.Val, v = HvdH.Val.cons a b) →
      HvdH.WordR main prog
        (fun vs => vs = HvdH.ofList Z :: HvdH.Val.int (m : ℤ) :: rest)
        (fun vs out => ∃ (Y : List HvdH.Val),
          out = HvdH.ofList Y :: HvdH.Val.int (m : ℤ) :: rest ∧
          Y = (Z.map Work.SynFFT.vfst).take (m / 2) ++ Z.map Work.SynFFT.vsnd)
        (fun _ => K * (m * (Lb + 1) + 1) + K) := by
  obtain ⟨dupP, Kd, hdup⟩ := hk.dup
  obtain ⟨swP, Ksw, hsw⟩ := hk.swap
  obtain ⟨fstP, Kf, hfstP⟩ := fstCompPass hk
  obtain ⟨sndP, Ks, hsndP⟩ := sndCompPass hk
  obtain ⟨taP, Kt, htaP⟩ := takeAppendStep hk hi hl
  refine ⟨((((dupP ;;; sndP) ;;; swP) ;;; fstP) ;;; taP),
    5 * (2 * Kd + 2 * Ks + 3 * Ksw + 2 * Kf + 4 * Kt + 1), ?_⟩
  intro main m Lb Z rest _h2 hZlen hZsz hZcons
  set Kx : ℕ := 2 * Kd + 2 * Ks + 3 * Ksw + 2 * Kf + 4 * Kt + 1 with hKx
  set V : ℕ := m * (Lb + 1) + 1 with hV
  set D : ℕ := Kx * V with hD
  have hV1 : 1 ≤ V := by rw [hV]; omega
  have hZm : Z.length ≤ m := by rw [hZlen]; exact Nat.sub_le m (m / 2)
  have hlenV : Z.length * (Lb + 1) + 1 ≤ V := by
    rw [hV]; exact Nat.add_le_add_right (Nat.mul_le_mul_right (Lb + 1) hZm) 1
  have hszZ : vsz (ofList Z) ≤ V := by
    rw [hV]; exact MrgKit.vsz_ofList_le_of_bound Z Lb m hZsz hZm
  have hszS : vsz (ofList (Z.map vsnd)) ≤ V := by
    rw [hV]
    have h1 := vsz_ofList_map_le_xblkLvlSuffixKit vsnd Z Lb
      (fun x hx => le_trans (vsz_vsnd_le x) (hZsz x hx))
    exact le_trans h1 (Nat.add_le_add_right (Nat.mul_le_mul_right (Lb + 1) hZm) 1)
  have hszF : vsz (ofList (Z.map vfst)) ≤ V := by
    rw [hV]
    have h1 := vsz_ofList_map_le_xblkLvlSuffixKit vfst Z Lb
      (fun x hx => le_trans (vsz_vfst_le x) (hZsz x hx))
    exact le_trans h1 (Nat.add_le_add_right (Nat.mul_le_mul_right (Lb + 1) hZm) 1)
  have hmV : m + 1 ≤ V := by
    rw [hV]
    have hm : m ≤ m * (Lb + 1) := by
      have := Nat.mul_le_mul_left m (show 1 ≤ Lb + 1 by omega)
      simpa using this
    omega
  have hKV : ∀ Kk : ℕ, Kk ≤ Kk * V := by
    intro Kk
    have := Nat.mul_le_mul_left Kk hV1
    simpa using this
  -- step 1: duplicate `Z`
  have e1 : WordR main dupP
      (fun vs => vs = ofList Z :: Val.int (m : ℤ) :: rest)
      (fun _ out => out = ofList Z :: ofList Z :: Val.int (m : ℤ) :: rest)
      (fun _ => D) := by
    have hcost : Kd * (vsz (ofList Z) + 1) ≤ Kx * V := by
      have h1 : vsz (ofList Z) + 1 ≤ 2 * V := by omega
      have h2 : 2 * Kd ≤ Kx := by rw [hKx]; omega
      calc Kd * (vsz (ofList Z) + 1) ≤ Kd * (2 * V) := Nat.mul_le_mul_left Kd h1
        _ = (2 * Kd) * V := by ring
        _ ≤ Kx * V := Nat.mul_le_mul_right V h2
    exact MrgKit.dupStep (hdup main) (ofList Z) (Val.int (m : ℤ) :: rest) D
      (by simpa [hD] using hcost)
  -- step 2: replace the copy on top by its list of second components
  have e2 : WordR main sndP
      (fun vs => vs = ofList Z :: ofList Z :: Val.int (m : ℤ) :: rest)
      (fun _ out => out = ofList (Z.map vsnd) :: ofList Z :: Val.int (m : ℤ) :: rest)
      (fun _ => D) := by
    refine MrgKit.WordR_weaken
      (hsndP main Lb Z (ofList Z :: Val.int (m : ℤ) :: rest) hZcons hZsz)
      (fun _ h => h) (fun _ _ _ h => h) ?_
    intro vs _
    have h2Ks : 2 * Ks ≤ Kx := by rw [hKx]; omega
    have h1 : Ks * (Z.length * (Lb + 1) + 1) ≤ Ks * V := Nat.mul_le_mul_left Ks hlenV
    have h2 : Ks ≤ Ks * V := hKV Ks
    have h3 : Ks * (Z.length * (Lb + 1) + 1) + Ks ≤ (2 * Ks) * V := by
      calc Ks * (Z.length * (Lb + 1) + 1) + Ks ≤ Ks * V + Ks := Nat.add_le_add_right h1 Ks
        _ ≤ Ks * V + Ks * V := Nat.add_le_add_left h2 (Ks * V)
        _ = (2 * Ks) * V := by ring
    have h4 : (2 * Ks) * V ≤ Kx * V := Nat.mul_le_mul_right V h2Ks
    simpa [hD] using le_trans h3 h4
  -- step 3: bring `Z` back on top
  have e3 : WordR main swP
      (fun vs => vs = ofList (Z.map vsnd) :: ofList Z :: Val.int (m : ℤ) :: rest)
      (fun _ out => out = ofList Z :: ofList (Z.map vsnd) :: Val.int (m : ℤ) :: rest)
      (fun _ => D) := by
    have hcost : Ksw * (vsz (ofList (Z.map vsnd)) + vsz (ofList Z) + 1) ≤ Kx * V := by
      have h1 : vsz (ofList (Z.map vsnd)) + vsz (ofList Z) + 1 ≤ 3 * V := by omega
      have h2 : 3 * Ksw ≤ Kx := by rw [hKx]; omega
      calc Ksw * (vsz (ofList (Z.map vsnd)) + vsz (ofList Z) + 1) ≤ Ksw * (3 * V) :=
            Nat.mul_le_mul_left Ksw h1
        _ = (3 * Ksw) * V := by ring
        _ ≤ Kx * V := Nat.mul_le_mul_right V h2
    have hsw' := MrgKit.swapStep (hsw main)
      (ofList (Z.map vsnd) :: ofList Z :: Val.int (m : ℤ) :: rest) (by simp) D
      (by simpa using hcost)
    refine MrgKit.WordR_weaken hsw' (fun _ h => h) ?_ (fun _ _ => le_rfl)
    intro vs out _ hout
    rw [hout]
    simp
  -- step 4: replace the remaining `Z` by its list of first components
  have e4 : WordR main fstP
      (fun vs => vs = ofList Z :: ofList (Z.map vsnd) :: Val.int (m : ℤ) :: rest)
      (fun _ out => out = ofList (Z.map vfst) :: ofList (Z.map vsnd) :: Val.int (m : ℤ) :: rest)
      (fun _ => D) := by
    refine MrgKit.WordR_weaken
      (hfstP main Lb Z (ofList (Z.map vsnd) :: Val.int (m : ℤ) :: rest) hZcons hZsz)
      (fun _ h => h) (fun _ _ _ h => h) ?_
    intro vs _
    have h2Kf : 2 * Kf ≤ Kx := by rw [hKx]; omega
    have h1 : Kf * (Z.length * (Lb + 1) + 1) ≤ Kf * V := Nat.mul_le_mul_left Kf hlenV
    have h2 : Kf ≤ Kf * V := hKV Kf
    have h3 : Kf * (Z.length * (Lb + 1) + 1) + Kf ≤ (2 * Kf) * V := by
      calc Kf * (Z.length * (Lb + 1) + 1) + Kf ≤ Kf * V + Kf := Nat.add_le_add_right h1 Kf
        _ ≤ Kf * V + Kf * V := Nat.add_le_add_left h2 (Kf * V)
        _ = (2 * Kf) * V := by ring
    have h4 : (2 * Kf) * V ≤ Kx * V := Nat.mul_le_mul_right V h2Kf
    simpa [hD] using le_trans h3 h4
  -- step 5: halve `m`, take the first `m/2` of the firsts, append the seconds
  have e5 : WordR main taP
      (fun vs => vs = ofList (Z.map vfst) :: ofList (Z.map vsnd) :: Val.int (m : ℤ) :: rest)
      (fun _ out => out = ofList (((Z.map vfst).take (m / 2)) ++ Z.map vsnd) ::
        Val.int (m : ℤ) :: rest)
      (fun _ => D) := by
    refine MrgKit.WordR_weaken
      (htaP main m (Z.map vfst) (Z.map vsnd) rest) (fun _ h => h) (fun _ _ _ h => h) ?_
    intro vs _
    have hcost : Kt * (vsz (ofList (Z.map vfst)) + vsz (ofList (Z.map vsnd)) + m + 1) + Kt
        ≤ Kx * V := by
      have h1 : vsz (ofList (Z.map vfst)) + vsz (ofList (Z.map vsnd)) + m + 1 ≤ 3 * V :=
        by omega
      have h2 : 4 * Kt ≤ Kx := by rw [hKx]; omega
      calc Kt * (vsz (ofList (Z.map vfst)) + vsz (ofList (Z.map vsnd)) + m + 1) + Kt
          ≤ Kt * (3 * V) + Kt := Nat.add_le_add_right (Nat.mul_le_mul_left Kt h1) Kt
        _ ≤ Kt * (3 * V) + Kt * V := Nat.add_le_add_left (hKV Kt) (Kt * (3 * V))
        _ = (4 * Kt) * V := by ring
        _ ≤ Kx * V := Nat.mul_le_mul_right V h2
    simpa [hD] using hcost
  have c1 := MrgKit.WordR_seqC e1 e2
  have c2 := MrgKit.WordR_seqC c1 e3
  have c3 := MrgKit.WordR_seqC c2 e4
  have c4 := MrgKit.WordR_seqC c3 e5
  refine MrgKit.WordR_weaken c4 (fun _ h => h) ?_ ?_
  · intro vs out _ hout
    exact ⟨((Z.map vfst).take (m / 2)) ++ Z.map vsnd, hout, rfl⟩
  · intro vs _
    have h5 : (((D + D) + D) + D) + D = 5 * Kx * V := by
      simp only [D]; ring
    rw [h5]
    omega

end Work.SynFFT
