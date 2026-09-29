import Mathlib
import Submission.Work.Resample.auCWCntKit
import Submission.Work.Kernel.mapList
import Submission.Work.Kernel.dup
import Submission.Work.Kernel.swap
import Submission.Work.Layout.flattenWord
import Submission.Work.Layout.lengthWord
import Submission.Work.IntLib.encodeNatBridge

/-!
# The counting word of `Work.Resample.auCWExtract`

`cntPass1` (resp. `cntPass2`) counts the `.int 1` (resp. `.int 2`) markers of the record chain
`ofList (qs.map (awRec ·.1 ·.2))`:

* `mapList` replaces every record by its marker sub-value `awSub1 x = ofList (awF1 x)`,
* `flatten` concatenates the resulting list of small lists,
* the length of the concatenation is `awCnt1 qs` (`cntFlatLen1`), and `Layout.lengthWord`
  reads it off.

`auCWCountWord` then computes the three output values `(c₁, c₂, L)` by running the two passes on two
copies of the chain (a `dup`) together with `Layout.lengthWord` for `L`.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.Resample

open HvdH

/-! ## Elementary size facts -/

theorem vsz_ofList_le_cw {l : List HvdH.Val} {b : ℕ} (h : ∀ x ∈ l, HvdH.vsz x ≤ b) :
    HvdH.vsz (HvdH.ofList l) ≤ (b + 1) * l.length + 1 := by
  rw [Work.Layout.vsz_ofList_lw]
  have h1 : (l.map HvdH.vsz).sum ≤ b * l.length := by
    induction l with
    | nil => simp
    | cons x t ih =>
      have hx : HvdH.vsz x ≤ b := h x List.mem_cons_self
      have ht : (t.map HvdH.vsz).sum ≤ b * t.length :=
        ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
      rw [List.map_cons, List.sum_cons, List.length_cons]
      calc HvdH.vsz x + (t.map HvdH.vsz).sum ≤ b + b * t.length := Nat.add_le_add hx ht
        _ = b * (t.length + 1) := by ring
  nlinarith [h1]

theorem awCnt1_le (qs : List (ℤ × ℤ)) : awCnt1 qs ≤ qs.length := by
  unfold awCnt1
  induction qs with
  | nil => simp
  | cons q t ih =>
    rw [List.map_cons, List.sum_cons, List.length_cons]
    have h : (if q.1 = 1 then (1 : ℕ) else 0) ≤ 1 := by split <;> omega
    omega

theorem awCnt2_le (qs : List (ℤ × ℤ)) : awCnt2 qs ≤ qs.length := by
  unfold awCnt2
  induction qs with
  | nil => simp
  | cons q t ih =>
    rw [List.map_cons, List.sum_cons, List.length_cons]
    have h : (if q.2 = 1 then (1 : ℕ) else 0) ≤ 1 := by split <;> omega
    omega

theorem vsz_mem_awF1_awRec {zr zi : ℤ} (hzr : zr = 0 ∨ zr = 1) (hzi : zi = 0 ∨ zi = 1)
    {x : HvdH.Val} (hx : x ∈ awF1 (awRec zr zi)) : HvdH.vsz x ≤ 4 := by
  by_cases h : zr = 1
  · rw [awF1_awRec hzr hzi, if_pos h] at hx
    rw [List.mem_singleton.mp hx]
    decide +kernel
  · rw [awF1_awRec hzr hzi, if_neg h] at hx
    exact absurd hx List.not_mem_nil

theorem vsz_mem_awF2_awRec {zr zi : ℤ} (hzr : zr = 0 ∨ zr = 1) (hzi : zi = 0 ∨ zi = 1)
    {x : HvdH.Val} (hx : x ∈ awF2 (awRec zr zi)) : HvdH.vsz x ≤ 4 := by
  by_cases h : zi = 1
  · rw [awF2_awRec hzr hzi, if_pos h] at hx
    rw [List.mem_singleton.mp hx]
    decide +kernel
  · rw [awF2_awRec hzr hzi, if_neg h] at hx
    exact absurd hx List.not_mem_nil

theorem forall2_awSub1 {xs ys : List HvdH.Val}
    (h : List.Forall₂ (fun x y => y = awSub1 x) xs ys) : ys = xs.map awSub1 := by
  induction h with
  | nil => rfl
  | cons hy _ ih => rw [List.map_cons, hy, ih]

theorem forall2_awSub2 {xs ys : List HvdH.Val}
    (h : List.Forall₂ (fun x y => y = awSub2 x) xs ys) : ys = xs.map awSub2 := by
  induction h with
  | nil => rfl
  | cons hy _ ih => rw [List.map_cons, hy, ih]

/-! ## The single pass -/

theorem cntPass1 (hk : HvdH.KernelLib) (hi : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (qs : List (ℤ × ℤ)) (X : List HvdH.Val),
      (∀ q ∈ qs, q.1 = 0 ∨ q.1 = 1) → (∀ q ∈ qs, q.2 = 0 ∨ q.2 = 1) →
      HvdH.WordR main prog
        (fun vs => vs = HvdH.ofList (qs.map fun q => awRec q.1 q.2) :: X)
        (fun _ out => out = HvdH.Val.int ((qs.map fun q => if q.1 = 1 then (1 : ℤ) else 0).sum) :: X)
        (fun _ => K * (qs.length + 1)) := by
  obtain ⟨bodyP, Kb, hBody⟩ := cntBody1 hk hi
  obtain ⟨mLComb, Km, hML⟩ := Work.Kernel.mapList
  obtain ⟨flatP, Kf, hFlat⟩ := Work.Layout.flattenWord
  obtain ⟨lenP, Kl, hLen⟩ := Work.Layout.lengthWord hi
  obtain ⟨swapP, Ks, hSwap⟩ := Work.Kernel.swap
  obtain ⟨dropP, Kdr, hDrop⟩ := Work.Kernel.dropValue
  refine ⟨HvdH.Cmd.seq (HvdH.Cmd.seq (HvdH.Cmd.seq (HvdH.Cmd.seq (mLComb bodyP) flatP) lenP) swapP) dropP,
    40 * (Kb + Km * 13 + Kf + Kl + Ks + Kdr + 1), ?_⟩
  intro main qs X hq1 hq2
  set R : List HvdH.Val := qs.map (fun q => awRec q.1 q.2) with hR
  set FL : List (List HvdH.Val) := R.map awF1 with hFL
  have hRlen : R.length = qs.length := by rw [hR]; exact List.length_map _
  have hCnt : FL.flatten.length = awCnt1 qs := by rw [hFL, hR]; exact cntFlatLen1 qs hq1 hq2
  have hCntLe : awCnt1 qs ≤ qs.length := awCnt1_le qs
  have hRsz : HvdH.vsz (HvdH.ofList R) + 1 ≤ 13 * (qs.length + 1) := by
    have h := vsz_ofList_le_cw (l := R) (b := 12) (by
      intro x hx
      rw [hR] at hx
      obtain ⟨q, hq, hq'⟩ := List.mem_map.mp hx
      rw [← hq']
      exact vsz_awRec_le (hq1 q hq) (hq2 q hq))
    rw [hRlen] at h
    nlinarith
  have hSubsz : HvdH.vsz (HvdH.ofList (R.map awSub1)) + 1 ≤ 13 * (qs.length + 1) := by
    have h := vsz_ofList_le_cw (l := R.map awSub1) (b := 12) (by
      intro x hx
      obtain ⟨y, hy, hy'⟩ := List.mem_map.mp hx
      rw [← hy']
      rw [hR] at hy
      obtain ⟨q, hq, hq'⟩ := List.mem_map.mp hy
      rw [← hq']
      exact vsz_awSub1_le (hq1 q hq) (hq2 q hq))
    rw [List.length_map, hRlen] at h
    nlinarith
  have hFlatsz : HvdH.vsz (HvdH.ofList FL.flatten) + 1 ≤ 5 * (qs.length + 1) := by
    have h := vsz_ofList_le_cw (l := FL.flatten) (b := 4) (by
      intro x hx
      obtain ⟨l, hl, hxl⟩ := List.mem_flatten.mp hx
      rw [hFL] at hl
      obtain ⟨y, hy, hy'⟩ := List.mem_map.mp hl
      rw [← hy'] at hxl
      rw [hR] at hy
      obtain ⟨q, hq, hq'⟩ := List.mem_map.mp hy
      rw [← hq'] at hxl
      exact vsz_mem_awF1_awRec (hq1 q hq) (hq2 q hq) hxl)
    rw [hCnt] at h
    nlinarith
  have hizCnt : HvdH.vsz (HvdH.Val.int (awCnt1 qs)) ≤ 4 * (qs.length + 1) := by
    have hvz : HvdH.vsz (HvdH.Val.int (awCnt1 qs)) = HvdH.isz (awCnt1 qs) :=
      Work.IntLib.vsz_int (awCnt1 qs)
    rw [hvz, HvdH.isz, Int.natAbs_natCast]
    have h : (awCnt1 qs).size ≤ awCnt1 qs := Nat.size_le.mpr Nat.lt_two_pow_self
    omega
  have hEq0 : ∀ (l : List HvdH.Val),
      HvdH.ofList (l.map awSub1) = HvdH.ofList ((l.map awF1).map HvdH.ofList) := by
    intro l
    rw [List.map_map]
    apply congrArg HvdH.ofList
    apply List.map_congr_left
    intro x _
    rfl
  have hEq : HvdH.ofList (R.map awSub1) = HvdH.ofList (FL.map HvdH.ofList) := by
    rw [hEq0 R, ← hFL]
  -- step 1: map every record to its marker value
  have st1 : HvdH.WordR main (mLComb bodyP)
      (fun vs => vs = HvdH.ofList R :: X)
      (fun _ out => out = HvdH.ofList (FL.map HvdH.ofList) :: X)
      (fun _ => (Kb + 13 * Km + 1) * (qs.length + 1)) := by
    have hbody : ∀ x, (∃ (zr zi : ℤ), (zr = 0 ∨ zr = 1) ∧ (zi = 0 ∨ zi = 1) ∧ x = awRec zr zi) →
        HvdH.WordR main bodyP (fun vs => vs = x :: X)
          (fun _ out => ∃ y, out = y :: X ∧ y = awSub1 x ∧ HvdH.vsz y ≤ 12)
          (fun _ => Kb) := by
      intro x hx
      obtain ⟨zr, zi, hzr, hzi, hxr⟩ := hx
      rw [hxr]
      refine Work.Kernel.WordR_conseq (hBody main zr zi X hzr hzi) ?_ ?_ ?_
      · intro vs hvs; exact hvs
      · intro vs out hvs hpost
        exact ⟨awSub1 (awRec zr zi), hpost, rfl, vsz_awSub1_le hzr hzi⟩
      · intro vs hvs; first | exact le_rfl | nlinarith
    have hmem : ∀ x ∈ R, (∃ (zr zi : ℤ), (zr = 0 ∨ zr = 1) ∧ (zi = 0 ∨ zi = 1) ∧ x = awRec zr zi) ∧
        HvdH.vsz x ≤ 12 := by
      intro x hx
      rw [hR] at hx
      obtain ⟨q, hq, hq'⟩ := List.mem_map.mp hx
      rw [← hq']
      exact ⟨⟨q.1, q.2, hq1 q hq, hq2 q hq, rfl⟩, vsz_awRec_le (hq1 q hq) (hq2 q hq)⟩
    have h := hML main bodyP X
      (fun x => ∃ (zr zi : ℤ), (zr = 0 ∨ zr = 1) ∧ (zi = 0 ∨ zi = 1) ∧ x = awRec zr zi)
      (fun x y => y = awSub1 x) Kb 12 hbody R hmem
    have hconv : HvdH.WordR main (mLComb bodyP) (fun vs => vs = HvdH.ofList R :: X)
        (fun _ out => out = HvdH.ofList (FL.map HvdH.ofList) :: X)
        (fun _ => R.length * (Kb + Km * (12 + 1)) + Km) := by
      refine Work.Kernel.WordR_conseq h ?_ ?_ ?_
      · intro vs hvs; exact hvs
      · intro vs out hvs hpost
        obtain ⟨ys, hout, hfor⟩ := hpost
        rw [hout, forall2_awSub1 hfor, hEq]
      · intro vs hvs; first | exact le_rfl | nlinarith
    refine monoC hconv ?_
    rw [hRlen]
    nlinarith
  -- step 2: flatten
  have st2 : HvdH.WordR main flatP
      (fun vs => vs = HvdH.ofList (FL.map HvdH.ofList) :: X)
      (fun _ out => out = HvdH.ofList FL.flatten :: X)
      (fun _ => 13 * Kf * (qs.length + 1)) := by
    refine winEx (main := main) (p := flatP) (A := [HvdH.ofList (FL.map HvdH.ofList)])
      (B := [HvdH.ofList FL.flatten]) (X := X)
      (c := 13 * Kf * (qs.length + 1)) ?_
    refine monoC (hFlat main FL) ?_
    rw [← hEq]
    nlinarith [hSubsz]
  -- step 3: length of the flattened list
  have st3 : HvdH.WordR main lenP
      (fun vs => vs = HvdH.ofList FL.flatten :: X)
      (fun _ out => out = HvdH.Val.int (awCnt1 qs) :: HvdH.ofList FL.flatten :: X)
      (fun _ => 5 * Kl * (qs.length + 1)) := by
    have hraw : HvdH.WordR main lenP
        (fun vs => vs = HvdH.ofList FL.flatten :: X)
        (fun _ out => out = HvdH.Val.int FL.flatten.length :: HvdH.ofList FL.flatten :: X)
        (fun _ => 5 * Kl * (qs.length + 1)) := by
      refine winEx (main := main) (p := lenP) (A := [HvdH.ofList FL.flatten])
        (B := [HvdH.Val.int FL.flatten.length, HvdH.ofList FL.flatten]) (X := X)
        (c := 5 * Kl * (qs.length + 1)) ?_
      refine monoC (hLen main FL.flatten) ?_
      nlinarith [hFlatsz]
    refine Work.Kernel.WordR_conseq hraw ?_ ?_ ?_
    · intro vs hvs; exact hvs
    · intro vs out hvs hpost
      rw [hpost, hCnt]
    · intro vs hvs; first | exact le_rfl | nlinarith
  -- step 4: swap
  have st4 : HvdH.WordR main swapP
      (fun vs => vs = HvdH.Val.int (awCnt1 qs) :: HvdH.ofList FL.flatten :: X)
      (fun _ out => out = HvdH.ofList FL.flatten :: HvdH.Val.int (awCnt1 qs) :: X)
      (fun _ => 10 * Ks * (qs.length + 1)) := by
    refine swapWin (h := hSwap main) (a := HvdH.Val.int (awCnt1 qs))
      (b := HvdH.ofList FL.flatten) (r := X) (c := 10 * Ks * (qs.length + 1)) ?_
    nlinarith [hizCnt, hFlatsz]
  -- step 5: drop the flattened list
  have st5 : HvdH.WordR main dropP
      (fun vs => vs = HvdH.ofList FL.flatten :: HvdH.Val.int (awCnt1 qs) :: X)
      (fun _ out => out = HvdH.Val.int (awCnt1 qs) :: X)
      (fun _ => 5 * Kdr * (qs.length + 1)) := by
    refine dropWin (h := hDrop main) (a := HvdH.ofList FL.flatten)
      (r := HvdH.Val.int (awCnt1 qs) :: X) (c := 5 * Kdr * (qs.length + 1)) ?_
    nlinarith [hFlatsz]
  have hs1 := seqC st1 st2
  have hs2 := seqC hs1 st3
  have hs3 := seqC hs2 st4
  have hs4 := seqC hs3 st5
  have hfin : HvdH.WordR main
      (HvdH.Cmd.seq (HvdH.Cmd.seq (HvdH.Cmd.seq (HvdH.Cmd.seq (mLComb bodyP) flatP) lenP) swapP) dropP)
      (fun vs => vs = HvdH.ofList R :: X)
      (fun _ out => out = HvdH.Val.int ((qs.map fun q => if q.1 = 1 then (1 : ℤ) else 0).sum) :: X)
      (fun _ => (Kb + 13 * Km + 1) * (qs.length + 1) + (13 * Kf * (qs.length + 1)
        + (5 * Kl * (qs.length + 1) + (10 * Ks * (qs.length + 1) + 5 * Kdr * (qs.length + 1))))) := by
    refine Work.Kernel.WordR_conseq hs4 ?_ ?_ ?_
    · intro vs hvs; exact hvs
    · intro vs out hvs hpost
      rw [hpost, awCnt1_cast]
    · intro vs hvs; first | exact le_rfl | nlinarith
  refine monoC hfin ?_
  refine le_trans (b := (40 * (Kb + Km * 13 + Kf + Kl + Ks + Kdr + 1)) * (qs.length + 1)) ?_ ?_
  · have e1 : (Kb + 13 * Km + 1) * (qs.length + 1) + (13 * Kf * (qs.length + 1)
        + (5 * Kl * (qs.length + 1) + (10 * Ks * (qs.length + 1) + 5 * Kdr * (qs.length + 1))))
        ≤ (40 * (Kb + Km * 13 + Kf + Kl + Ks + Kdr + 1)) * (qs.length + 1) := by
      nlinarith
    exact e1
  · nlinarith

theorem cntPass2 (hk : HvdH.KernelLib) (hi : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (qs : List (ℤ × ℤ)) (X : List HvdH.Val),
      (∀ q ∈ qs, q.1 = 0 ∨ q.1 = 1) → (∀ q ∈ qs, q.2 = 0 ∨ q.2 = 1) →
      HvdH.WordR main prog
        (fun vs => vs = HvdH.ofList (qs.map fun q => awRec q.1 q.2) :: X)
        (fun _ out => out = HvdH.Val.int ((qs.map fun q => if q.2 = 1 then (1 : ℤ) else 0).sum) :: X)
        (fun _ => K * (qs.length + 1)) := by
  obtain ⟨bodyP, Kb, hBody⟩ := cntBody2 hk hi
  obtain ⟨mLComb, Km, hML⟩ := Work.Kernel.mapList
  obtain ⟨flatP, Kf, hFlat⟩ := Work.Layout.flattenWord
  obtain ⟨lenP, Kl, hLen⟩ := Work.Layout.lengthWord hi
  obtain ⟨swapP, Ks, hSwap⟩ := Work.Kernel.swap
  obtain ⟨dropP, Kdr, hDrop⟩ := Work.Kernel.dropValue
  refine ⟨HvdH.Cmd.seq (HvdH.Cmd.seq (HvdH.Cmd.seq (HvdH.Cmd.seq (mLComb bodyP) flatP) lenP) swapP) dropP,
    40 * (Kb + Km * 13 + Kf + Kl + Ks + Kdr + 1), ?_⟩
  intro main qs X hq1 hq2
  set R : List HvdH.Val := qs.map (fun q => awRec q.1 q.2) with hR
  set FL : List (List HvdH.Val) := R.map awF2 with hFL
  have hRlen : R.length = qs.length := by rw [hR]; exact List.length_map _
  have hCnt : FL.flatten.length = awCnt2 qs := by rw [hFL, hR]; exact cntFlatLen2 qs hq1 hq2
  have hCntLe : awCnt2 qs ≤ qs.length := awCnt2_le qs
  have hRsz : HvdH.vsz (HvdH.ofList R) + 1 ≤ 13 * (qs.length + 1) := by
    have h := vsz_ofList_le_cw (l := R) (b := 12) (by
      intro x hx
      rw [hR] at hx
      obtain ⟨q, hq, hq'⟩ := List.mem_map.mp hx
      rw [← hq']
      exact vsz_awRec_le (hq1 q hq) (hq2 q hq))
    rw [hRlen] at h
    nlinarith
  have hSubsz : HvdH.vsz (HvdH.ofList (R.map awSub2)) + 1 ≤ 13 * (qs.length + 1) := by
    have h := vsz_ofList_le_cw (l := R.map awSub2) (b := 12) (by
      intro x hx
      obtain ⟨y, hy, hy'⟩ := List.mem_map.mp hx
      rw [← hy']
      rw [hR] at hy
      obtain ⟨q, hq, hq'⟩ := List.mem_map.mp hy
      rw [← hq']
      exact vsz_awSub2_le (hq1 q hq) (hq2 q hq))
    rw [List.length_map, hRlen] at h
    nlinarith
  have hFlatsz : HvdH.vsz (HvdH.ofList FL.flatten) + 1 ≤ 5 * (qs.length + 1) := by
    have h := vsz_ofList_le_cw (l := FL.flatten) (b := 4) (by
      intro x hx
      obtain ⟨l, hl, hxl⟩ := List.mem_flatten.mp hx
      rw [hFL] at hl
      obtain ⟨y, hy, hy'⟩ := List.mem_map.mp hl
      rw [← hy'] at hxl
      rw [hR] at hy
      obtain ⟨q, hq, hq'⟩ := List.mem_map.mp hy
      rw [← hq'] at hxl
      exact vsz_mem_awF2_awRec (hq1 q hq) (hq2 q hq) hxl)
    rw [hCnt] at h
    nlinarith
  have hizCnt : HvdH.vsz (HvdH.Val.int (awCnt2 qs)) ≤ 4 * (qs.length + 1) := by
    have hvz : HvdH.vsz (HvdH.Val.int (awCnt2 qs)) = HvdH.isz (awCnt2 qs) :=
      Work.IntLib.vsz_int (awCnt2 qs)
    rw [hvz, HvdH.isz, Int.natAbs_natCast]
    have h : (awCnt2 qs).size ≤ awCnt2 qs := Nat.size_le.mpr Nat.lt_two_pow_self
    omega
  have hEq0 : ∀ (l : List HvdH.Val),
      HvdH.ofList (l.map awSub2) = HvdH.ofList ((l.map awF2).map HvdH.ofList) := by
    intro l
    rw [List.map_map]
    apply congrArg HvdH.ofList
    apply List.map_congr_left
    intro x _
    rfl
  have hEq : HvdH.ofList (R.map awSub2) = HvdH.ofList (FL.map HvdH.ofList) := by
    rw [hEq0 R, ← hFL]
  -- step 1: map every record to its marker value
  have st1 : HvdH.WordR main (mLComb bodyP)
      (fun vs => vs = HvdH.ofList R :: X)
      (fun _ out => out = HvdH.ofList (FL.map HvdH.ofList) :: X)
      (fun _ => (Kb + 13 * Km + 1) * (qs.length + 1)) := by
    have hbody : ∀ x, (∃ (zr zi : ℤ), (zr = 0 ∨ zr = 1) ∧ (zi = 0 ∨ zi = 1) ∧ x = awRec zr zi) →
        HvdH.WordR main bodyP (fun vs => vs = x :: X)
          (fun _ out => ∃ y, out = y :: X ∧ y = awSub2 x ∧ HvdH.vsz y ≤ 12)
          (fun _ => Kb) := by
      intro x hx
      obtain ⟨zr, zi, hzr, hzi, hxr⟩ := hx
      rw [hxr]
      refine Work.Kernel.WordR_conseq (hBody main zr zi X hzr hzi) ?_ ?_ ?_
      · intro vs hvs; exact hvs
      · intro vs out hvs hpost
        exact ⟨awSub2 (awRec zr zi), hpost, rfl, vsz_awSub2_le hzr hzi⟩
      · intro vs hvs; first | exact le_rfl | nlinarith
    have hmem : ∀ x ∈ R, (∃ (zr zi : ℤ), (zr = 0 ∨ zr = 1) ∧ (zi = 0 ∨ zi = 1) ∧ x = awRec zr zi) ∧
        HvdH.vsz x ≤ 12 := by
      intro x hx
      rw [hR] at hx
      obtain ⟨q, hq, hq'⟩ := List.mem_map.mp hx
      rw [← hq']
      exact ⟨⟨q.1, q.2, hq1 q hq, hq2 q hq, rfl⟩, vsz_awRec_le (hq1 q hq) (hq2 q hq)⟩
    have h := hML main bodyP X
      (fun x => ∃ (zr zi : ℤ), (zr = 0 ∨ zr = 1) ∧ (zi = 0 ∨ zi = 1) ∧ x = awRec zr zi)
      (fun x y => y = awSub2 x) Kb 12 hbody R hmem
    have hconv : HvdH.WordR main (mLComb bodyP) (fun vs => vs = HvdH.ofList R :: X)
        (fun _ out => out = HvdH.ofList (FL.map HvdH.ofList) :: X)
        (fun _ => R.length * (Kb + Km * (12 + 1)) + Km) := by
      refine Work.Kernel.WordR_conseq h ?_ ?_ ?_
      · intro vs hvs; exact hvs
      · intro vs out hvs hpost
        obtain ⟨ys, hout, hfor⟩ := hpost
        rw [hout, forall2_awSub2 hfor, hEq]
      · intro vs hvs; first | exact le_rfl | nlinarith
    refine monoC hconv ?_
    rw [hRlen]
    nlinarith
  -- step 2: flatten
  have st2 : HvdH.WordR main flatP
      (fun vs => vs = HvdH.ofList (FL.map HvdH.ofList) :: X)
      (fun _ out => out = HvdH.ofList FL.flatten :: X)
      (fun _ => 13 * Kf * (qs.length + 1)) := by
    refine winEx (main := main) (p := flatP) (A := [HvdH.ofList (FL.map HvdH.ofList)])
      (B := [HvdH.ofList FL.flatten]) (X := X)
      (c := 13 * Kf * (qs.length + 1)) ?_
    refine monoC (hFlat main FL) ?_
    rw [← hEq]
    nlinarith [hSubsz]
  -- step 3: length of the flattened list
  have st3 : HvdH.WordR main lenP
      (fun vs => vs = HvdH.ofList FL.flatten :: X)
      (fun _ out => out = HvdH.Val.int (awCnt2 qs) :: HvdH.ofList FL.flatten :: X)
      (fun _ => 5 * Kl * (qs.length + 1)) := by
    have hraw : HvdH.WordR main lenP
        (fun vs => vs = HvdH.ofList FL.flatten :: X)
        (fun _ out => out = HvdH.Val.int FL.flatten.length :: HvdH.ofList FL.flatten :: X)
        (fun _ => 5 * Kl * (qs.length + 1)) := by
      refine winEx (main := main) (p := lenP) (A := [HvdH.ofList FL.flatten])
        (B := [HvdH.Val.int FL.flatten.length, HvdH.ofList FL.flatten]) (X := X)
        (c := 5 * Kl * (qs.length + 1)) ?_
      refine monoC (hLen main FL.flatten) ?_
      nlinarith [hFlatsz]
    refine Work.Kernel.WordR_conseq hraw ?_ ?_ ?_
    · intro vs hvs; exact hvs
    · intro vs out hvs hpost
      rw [hpost, hCnt]
    · intro vs hvs; first | exact le_rfl | nlinarith
  -- step 4: swap
  have st4 : HvdH.WordR main swapP
      (fun vs => vs = HvdH.Val.int (awCnt2 qs) :: HvdH.ofList FL.flatten :: X)
      (fun _ out => out = HvdH.ofList FL.flatten :: HvdH.Val.int (awCnt2 qs) :: X)
      (fun _ => 10 * Ks * (qs.length + 1)) := by
    refine swapWin (h := hSwap main) (a := HvdH.Val.int (awCnt2 qs))
      (b := HvdH.ofList FL.flatten) (r := X) (c := 10 * Ks * (qs.length + 1)) ?_
    nlinarith [hizCnt, hFlatsz]
  -- step 5: drop the flattened list
  have st5 : HvdH.WordR main dropP
      (fun vs => vs = HvdH.ofList FL.flatten :: HvdH.Val.int (awCnt2 qs) :: X)
      (fun _ out => out = HvdH.Val.int (awCnt2 qs) :: X)
      (fun _ => 5 * Kdr * (qs.length + 1)) := by
    refine dropWin (h := hDrop main) (a := HvdH.ofList FL.flatten)
      (r := HvdH.Val.int (awCnt2 qs) :: X) (c := 5 * Kdr * (qs.length + 1)) ?_
    nlinarith [hFlatsz]
  have hs1 := seqC st1 st2
  have hs2 := seqC hs1 st3
  have hs3 := seqC hs2 st4
  have hs4 := seqC hs3 st5
  have hfin : HvdH.WordR main
      (HvdH.Cmd.seq (HvdH.Cmd.seq (HvdH.Cmd.seq (HvdH.Cmd.seq (mLComb bodyP) flatP) lenP) swapP) dropP)
      (fun vs => vs = HvdH.ofList R :: X)
      (fun _ out => out = HvdH.Val.int ((qs.map fun q => if q.2 = 1 then (1 : ℤ) else 0).sum) :: X)
      (fun _ => (Kb + 13 * Km + 1) * (qs.length + 1) + (13 * Kf * (qs.length + 1)
        + (5 * Kl * (qs.length + 1) + (10 * Ks * (qs.length + 1) + 5 * Kdr * (qs.length + 1))))) := by
    refine Work.Kernel.WordR_conseq hs4 ?_ ?_ ?_
    · intro vs hvs; exact hvs
    · intro vs out hvs hpost
      rw [hpost, awCnt2_cast]
    · intro vs hvs; first | exact le_rfl | nlinarith
  refine monoC hfin ?_
  refine le_trans (b := (40 * (Kb + Km * 13 + Kf + Kl + Ks + Kdr + 1)) * (qs.length + 1)) ?_ ?_
  · have e1 : (Kb + 13 * Km + 1) * (qs.length + 1) + (13 * Kf * (qs.length + 1)
        + (5 * Kl * (qs.length + 1) + (10 * Ks * (qs.length + 1) + 5 * Kdr * (qs.length + 1))))
        ≤ (40 * (Kb + Km * 13 + Kf + Kl + Ks + Kdr + 1)) * (qs.length + 1) := by
      nlinarith
    exact e1
  · nlinarith



/-! ## The three output values -/

theorem auCWCountWord (hk : HvdH.KernelLib) (hi : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (qs : List (ℤ × ℤ)) (T : List HvdH.Val),
      (∀ q ∈ qs, q.1 = 0 ∨ q.1 = 1) → (∀ q ∈ qs, q.2 = 0 ∨ q.2 = 1) →
      HvdH.WordR main prog
        (fun vs => vs = HvdH.ofList (qs.map fun q => awRec q.1 q.2) :: T)
        (fun _ out => out = HvdH.Val.int ((qs.map fun q => if q.1 = 1 then (1 : ℤ) else 0).sum)
          :: HvdH.Val.int ((qs.map fun q => if q.2 = 1 then (1 : ℤ) else 0).sum)
          :: HvdH.Val.int ((qs.length : ℕ) : ℤ) :: T)
        (fun _ => K * (qs.length + 1)) := by
  obtain ⟨pass1P, K1, hPass1⟩ := cntPass1 hk hi
  obtain ⟨pass2P, K2, hPass2⟩ := cntPass2 hk hi
  obtain ⟨lenP, Kl, hLen⟩ := Work.Layout.lengthWord hi
  obtain ⟨swapP, Ks, hSwap⟩ := Work.Kernel.swap
  obtain ⟨dupP, Kd, hDup⟩ := hk.dup
  refine ⟨HvdH.Cmd.seq (HvdH.Cmd.seq (HvdH.Cmd.seq (HvdH.Cmd.seq (HvdH.Cmd.seq lenP swapP) dupP)
    pass2P) swapP) pass1P, 100 * (K1 + K2 + Kl + Ks + Kd + 1), ?_⟩
  intro main qs T hq1 hq2
  set R : List HvdH.Val := qs.map (fun q => awRec q.1 q.2) with hR
  have hRlen : R.length = qs.length := by rw [hR]; exact List.length_map _
  have hRsz : HvdH.vsz (HvdH.ofList R) + 1 ≤ 13 * (qs.length + 1) := by
    have h := vsz_ofList_le_cw (l := R) (b := 12) (by
      intro x hx
      rw [hR] at hx
      obtain ⟨q, hq, hq'⟩ := List.mem_map.mp hx
      rw [← hq']
      exact vsz_awRec_le (hq1 q hq) (hq2 q hq))
    rw [hRlen] at h
    nlinarith
  have hLsz : HvdH.vsz (HvdH.Val.int ((qs.length : ℕ) : ℤ)) ≤ 4 * (qs.length + 1) := by
    have hvz : HvdH.vsz (HvdH.Val.int ((qs.length : ℕ) : ℤ)) = HvdH.isz ((qs.length : ℕ) : ℤ) :=
      Work.IntLib.vsz_int ((qs.length : ℕ) : ℤ)
    rw [hvz, HvdH.isz, Int.natAbs_natCast]
    have h : (qs.length).size ≤ qs.length := Nat.size_le.mpr Nat.lt_two_pow_self
    omega
  have hC2sz : HvdH.vsz (HvdH.Val.int ((qs.map fun q => if q.2 = 1 then (1 : ℤ) else 0).sum))
      ≤ 4 * (qs.length + 1) := by
    have hvz : HvdH.vsz (HvdH.Val.int ((qs.map fun q => if q.2 = 1 then (1 : ℤ) else 0).sum))
        = HvdH.isz ((qs.map fun q => if q.2 = 1 then (1 : ℤ) else 0).sum) :=
      Work.IntLib.vsz_int _
    have h0 : 0 ≤ ((qs.map fun q => if q.2 = 1 then (1 : ℤ) else 0).sum) := by
      rw [← awCnt2_cast]; positivity
    have hle : ((qs.map fun q => if q.2 = 1 then (1 : ℤ) else 0).sum) ≤ (qs.length : ℤ) := by
      rw [← awCnt2_cast]
      exact_mod_cast awCnt2_le qs
    have hnat : ((qs.map fun q => if q.2 = 1 then (1 : ℤ) else 0).sum).natAbs ≤ qs.length := by
      have h1 : ((((qs.map fun q => if q.2 = 1 then (1 : ℤ) else 0).sum).natAbs : ℕ) : ℤ)
          = ((qs.map fun q => if q.2 = 1 then (1 : ℤ) else 0).sum) := Int.natAbs_of_nonneg h0
      have h2 : ((((qs.map fun q => if q.2 = 1 then (1 : ℤ) else 0).sum).natAbs : ℕ) : ℤ)
          ≤ (qs.length : ℤ) := by rw [h1]; exact hle
      exact_mod_cast h2
    rw [hvz, HvdH.isz]
    have h2 : ((((qs.map fun q => if q.2 = 1 then (1 : ℤ) else 0).sum).natAbs).size) ≤ qs.length :=
      le_trans (Nat.size_le_size hnat) (Nat.size_le.mpr Nat.lt_two_pow_self)
    omega
  have st1 : HvdH.WordR main lenP (fun vs => vs = HvdH.ofList R :: T)
      (fun _ out => out = HvdH.Val.int ((qs.length : ℕ) : ℤ) :: HvdH.ofList R :: T)
      (fun _ => 13 * Kl * (qs.length + 1)) := by
    have hraw : HvdH.WordR main lenP (fun vs => vs = HvdH.ofList R :: T)
        (fun _ out => out = HvdH.Val.int R.length :: HvdH.ofList R :: T)
        (fun _ => 13 * Kl * (qs.length + 1)) := by
      refine winEx (main := main) (p := lenP) (A := [HvdH.ofList R])
        (B := [HvdH.Val.int R.length, HvdH.ofList R]) (X := T) (c := 13 * Kl * (qs.length + 1)) ?_
      refine monoC (hLen main R) ?_
      nlinarith [hRsz]
    refine Work.Kernel.WordR_conseq hraw ?_ ?_ ?_
    · intro vs hvs; exact hvs
    · intro vs out hvs hpost; rw [hpost, hRlen]
    · intro vs hvs; first | exact le_rfl | nlinarith
  have st2 : HvdH.WordR main swapP
      (fun vs => vs = HvdH.Val.int ((qs.length : ℕ) : ℤ) :: HvdH.ofList R :: T)
      (fun _ out => out = HvdH.ofList R :: HvdH.Val.int ((qs.length : ℕ) : ℤ) :: T)
      (fun _ => 40 * Ks * (qs.length + 1)) := by
    refine swapWin (h := hSwap main) (a := HvdH.Val.int ((qs.length : ℕ) : ℤ))
      (b := HvdH.ofList R) (r := T) (c := 40 * Ks * (qs.length + 1)) ?_
    nlinarith [hLsz, hRsz]
  have st3 : HvdH.WordR main dupP
      (fun vs => vs = HvdH.ofList R :: HvdH.Val.int ((qs.length : ℕ) : ℤ) :: T)
      (fun _ out => out = HvdH.ofList R :: HvdH.ofList R :: HvdH.Val.int ((qs.length : ℕ) : ℤ) :: T)
      (fun _ => 13 * Kd * (qs.length + 1)) := by
    refine dupWin (h := hDup main) (a := HvdH.ofList R)
      (r := HvdH.Val.int ((qs.length : ℕ) : ℤ) :: T) (c := 13 * Kd * (qs.length + 1)) ?_
    nlinarith [hRsz]
  have st4 : HvdH.WordR main pass2P
      (fun vs => vs = HvdH.ofList R :: HvdH.ofList R :: HvdH.Val.int ((qs.length : ℕ) : ℤ) :: T)
      (fun _ out => out = HvdH.Val.int ((qs.map fun q => if q.2 = 1 then (1 : ℤ) else 0).sum)
        :: HvdH.ofList R :: HvdH.Val.int ((qs.length : ℕ) : ℤ) :: T)
      (fun _ => K2 * (qs.length + 1)) := by
    have h := hPass2 main qs (HvdH.ofList R :: HvdH.Val.int ((qs.length : ℕ) : ℤ) :: T) hq1 hq2
    rw [← hR] at h
    exact h
  have st5 : HvdH.WordR main swapP
      (fun vs => vs = HvdH.Val.int ((qs.map fun q => if q.2 = 1 then (1 : ℤ) else 0).sum)
        :: HvdH.ofList R :: HvdH.Val.int ((qs.length : ℕ) : ℤ) :: T)
      (fun _ out => out = HvdH.ofList R
        :: HvdH.Val.int ((qs.map fun q => if q.2 = 1 then (1 : ℤ) else 0).sum)
        :: HvdH.Val.int ((qs.length : ℕ) : ℤ) :: T)
      (fun _ => 40 * Ks * (qs.length + 1)) := by
    refine swapWin (h := hSwap main) (a := HvdH.Val.int ((qs.map fun q => if q.2 = 1 then (1 : ℤ) else 0).sum))
      (b := HvdH.ofList R) (r := HvdH.Val.int ((qs.length : ℕ) : ℤ) :: T) (c := 40 * Ks * (qs.length + 1)) ?_
    nlinarith [hC2sz, hRsz]
  have st6 : HvdH.WordR main pass1P
      (fun vs => vs = HvdH.ofList R
        :: HvdH.Val.int ((qs.map fun q => if q.2 = 1 then (1 : ℤ) else 0).sum)
        :: HvdH.Val.int ((qs.length : ℕ) : ℤ) :: T)
      (fun _ out => out = HvdH.Val.int ((qs.map fun q => if q.1 = 1 then (1 : ℤ) else 0).sum)
        :: HvdH.Val.int ((qs.map fun q => if q.2 = 1 then (1 : ℤ) else 0).sum)
        :: HvdH.Val.int ((qs.length : ℕ) : ℤ) :: T)
      (fun _ => K1 * (qs.length + 1)) := by
    have h := hPass1 main qs (HvdH.Val.int ((qs.map fun q => if q.2 = 1 then (1 : ℤ) else 0).sum)
      :: HvdH.Val.int ((qs.length : ℕ) : ℤ) :: T) hq1 hq2
    rw [← hR] at h
    exact h
  have hs1 := seqC st1 st2
  have hs2 := seqC hs1 st3
  have hs3 := seqC hs2 st4
  have hs4 := seqC hs3 st5
  have hs5 := seqC hs4 st6
  refine monoC hs5 ?_
  nlinarith

end Work.Resample
