import Mathlib
import Submission.Work.Layout.AA.Defs
import Submission.Work.Layout.AA.clearAbove_ev
import Submission.Work.Layout.reverseWord
import Submission.Work.Resample.PB.Defs
import Submission.Work.Resample.PB.Kit
import Submission.Work.SynFFT.axisKit
import Submission.Work.Kernel.kernelLib
import Submission.Work.Resample.PBChunk.chunksOfWordPB
import Submission.Work.Resample.chunkCostAbs

/-!
# `Work.Resample.chunkWordPB`: a chunking word in the `Resample`/`PB` dialect

`chunkWordPB` cuts the value `ofList xs` below an integer `int S` into consecutive chunks of length
`S` (`1 ≤ S`, `S ∣ xs.length`), i.e. it produces `PB.blkVal (SynFFT.chunkList S xs)`, and restores
the integer `int S` on top of stack 0.  Its cost is linear in the size of the input plus
`O(isz S)` per chunk.

## Construction

* `Work.Resample.PBChunk.chunksOfWordPB` is the `ChunksOfWord` interface: a word turning
  `int m :: ofList xs :: rest` into `ofList (map ofList chunks) :: rest`, consuming the integer.
  It is the Layout chunk word, re-proved in the private namespace
  `Work.Resample.PBChunk` (see the headers of the modules in
  `Submission/Work/Resample/PBChunk/`; the relocation is needed because the original
  `Submission.Work.Layout.chunksOfDefs` cannot be imported together with
  `Submission.Work.Layout.AA.Defs`: both declare `Work.Layout.rF`).
* To keep `int S` on top of the result, the chunk word is preceded by `dup` (duplicating `int S`)
  and two `roll`s, so that it is invoked on `int S :: ofList xs :: int S :: rest` — the spare copy
  sits *below* the input list and is therefore returned under the chunk list — and followed by one
  more `roll 1` bringing the integer back to the top.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

namespace Work.Resample

open HvdH

theorem chunkWordPB : ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (S : ℕ)
    (xs : List HvdH.Val) (rest : List HvdH.Val),
    1 ≤ S → S ∣ xs.length →
    HvdH.WordR main prog
      (fun vs => vs = HvdH.Val.int (S : ℤ) :: HvdH.ofList xs :: rest)
      (fun _ out => out = HvdH.Val.int (S : ℤ) ::
        Work.Resample.PB.blkVal (Work.SynFFT.chunkList S xs) :: rest)
      (fun _ => K * (HvdH.vsz (HvdH.ofList xs) + 1) +
        K * ((xs.length / S + 1) * (HvdH.isz (S : ℤ) + 1) + 1)) := by
  obtain ⟨chP, Kc, hch⟩ := (Work.Resample.PBChunk.chunksOfWordPB : Work.Resample.ChunksOfWord)
  obtain ⟨dupP, Kd, hdup⟩ := Work.Kernel.kernelLib.dup
  obtain ⟨rollP, Kr, hroll⟩ := Work.Kernel.kernelLib.roll
  refine ⟨Work.Layout.seqs [dupP, rollP 2, rollP 1, chP, rollP 1],
    1000 * (Kc + Kd + Kr) + 1000, ?_⟩
  intro main S xs rest hS hdvd vs hvs s R hR
  subst hvs
  -- ### step 1: duplicate `int S`
  obtain ⟨o1, s1, n1, hp1, he1, hn1, hs1, hf1⟩ :=
    hdup main (HvdH.Val.int (S : ℤ) :: HvdH.ofList xs :: rest) (by simp) s R hR
  obtain ⟨v1, r1, hv1, ho1⟩ := hp1
  obtain ⟨hva, hvb⟩ := List.cons.inj hv1
  obtain rfl : v1 = HvdH.Val.int (S : ℤ) := hva.symm
  obtain rfl : r1 = HvdH.ofList xs :: rest := hvb.symm
  -- ### step 2: `roll 2`
  obtain ⟨o2, s2, n2, ho2, he2, hn2, hs2, hf2⟩ :=
    hroll main 2 o1 (by rw [ho1]; simp) s1 R hs1
  have ho2' : o2 = HvdH.ofList xs :: HvdH.Val.int (S : ℤ) :: HvdH.Val.int (S : ℤ) :: rest := by
    rw [ho2, ho1]
    simp only [List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero,
      List.eraseIdx_cons_succ]
  -- ### step 3: `roll 1`
  obtain ⟨o3, s3, n3, ho3, he3, hn3, hs3, hf3⟩ :=
    hroll main 1 o2 (by rw [ho2']; simp) s2 R hs2
  have ho3' : o3 = HvdH.Val.int (S : ℤ) :: HvdH.ofList xs :: HvdH.Val.int (S : ℤ) :: rest := by
    rw [ho3, ho2']
    simp only [List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero,
      List.eraseIdx_cons_succ]
  -- ### step 4: the chunk word (consuming the first copy of `int S`)
  obtain ⟨o4, s4, n4, hp4, he4, hn4, hs4, hf4⟩ :=
    hch main S xs hS hdvd o3 (by rw [ho3']; exact ⟨HvdH.Val.int (S : ℤ) :: rest, rfl⟩) s3 R hs3
  obtain ⟨r4, hv4, ho4⟩ := hp4
  have hr4 : r4 = HvdH.Val.int (S : ℤ) :: rest := by
    rw [ho3'] at hv4
    simpa using hv4.symm
  have ho4' : o4 = HvdH.ofList ((List.range (xs.length / S)).map
      fun i => HvdH.ofList ((xs.drop (i * S)).take S)) :: HvdH.Val.int (S : ℤ) :: rest := by
    rw [ho4, hr4]
  -- ### step 5: `roll 1` (bring the integer back to the top)
  obtain ⟨o5, s5, n5, ho5, he5, hn5, hs5, hf5⟩ :=
    hroll main 1 o4 (by rw [ho4']; simp) s4 R hs4
  have ho5' : o5 = HvdH.Val.int (S : ℤ) :: HvdH.ofList ((List.range (xs.length / S)).map
      fun i => HvdH.ofList ((xs.drop (i * S)).take S)) :: rest := by
    rw [ho5, ho4']
    simp only [List.getD_cons_zero, List.getD_cons_succ, List.eraseIdx_cons_zero,
      List.eraseIdx_cons_succ]
  -- ### the chunk list is `blkVal (chunkList S xs)`
  have hblk : Work.Resample.PB.blkVal (Work.SynFFT.chunkList S xs)
      = HvdH.ofList ((List.range (xs.length / S)).map
          fun i => HvdH.ofList ((xs.drop (i * S)).take S)) := by
    simp only [Work.Resample.PB.blkVal, Work.SynFFT.chunkList, List.map_map]
    rfl
  -- ### the five step bounds
  have hvsz_int : HvdH.vsz (HvdH.Val.int (S : ℤ)) = HvdH.isz (S : ℤ) := Work.IntLib.vsz_int _
  have hb1 : n1 ≤ Kd * (HvdH.isz (S : ℤ) + 1) := by
    simpa only [List.headD_cons, hvsz_int] using hn1
  have hb2 : n2 ≤ Kr * 3 * (2 * HvdH.isz (S : ℤ) + HvdH.vsz (HvdH.ofList xs) + 1) := by
    have h : (List.map HvdH.vsz (List.take (2 + 1) o1)).sum + 1
        = 2 * HvdH.isz (S : ℤ) + HvdH.vsz (HvdH.ofList xs) + 1 := by
      rw [ho1]
      show (List.map HvdH.vsz [HvdH.Val.int (S : ℤ), HvdH.Val.int (S : ℤ),
        HvdH.ofList xs]).sum + 1 = 2 * HvdH.isz (S : ℤ) + HvdH.vsz (HvdH.ofList xs) + 1
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hvsz_int,
        Nat.add_zero]
      ring
    calc n2 ≤ Kr * (2 + 1) * ((List.map HvdH.vsz (List.take (2 + 1) o1)).sum + 1) := hn2
      _ = Kr * 3 * (2 * HvdH.isz (S : ℤ) + HvdH.vsz (HvdH.ofList xs) + 1) := by rw [h]
  have hb3 : n3 ≤ Kr * 2 * (HvdH.vsz (HvdH.ofList xs) + HvdH.isz (S : ℤ) + 1) := by
    have h : (List.map HvdH.vsz (List.take (1 + 1) o2)).sum + 1
        = HvdH.vsz (HvdH.ofList xs) + HvdH.isz (S : ℤ) + 1 := by
      rw [ho2']
      show (List.map HvdH.vsz [HvdH.ofList xs, HvdH.Val.int (S : ℤ)]).sum + 1
        = HvdH.vsz (HvdH.ofList xs) + HvdH.isz (S : ℤ) + 1
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hvsz_int,
        Nat.add_zero]
    calc n3 ≤ Kr * (1 + 1) * ((List.map HvdH.vsz (List.take (1 + 1) o2)).sum + 1) := hn3
      _ = Kr * 2 * (HvdH.vsz (HvdH.ofList xs) + HvdH.isz (S : ℤ) + 1) := by rw [h]
  have hb4 : n4 ≤ Kc * (HvdH.vsz (HvdH.ofList xs) + (xs.length / S + 1) * HvdH.isz (S : ℤ) + 1) := by
    simpa only [] using hn4
  have hb5 : n5 ≤ Kr * 2 * (HvdH.vsz (HvdH.ofList xs) + 2 * (xs.length / S) + HvdH.isz (S : ℤ) + 1) := by
    have hvs : HvdH.vsz (HvdH.ofList ((List.range (xs.length / S)).map
        fun i => HvdH.ofList ((xs.drop (i * S)).take S)))
        = HvdH.vsz (HvdH.ofList xs) + 2 * (xs.length / S) := by
      have hmap : (List.map (fun i => HvdH.ofList ((xs.drop (i * S)).take S))
            (List.range (xs.length / S)))
          = List.map HvdH.ofList (List.map (fun i => (xs.drop (i * S)).take S)
              (List.range (xs.length / S))) := by
        exact (List.map_map (g := HvdH.ofList) (f := fun i => (xs.drop (i * S)).take S)
          (l := List.range (xs.length / S))).symm
      rw [hmap]
      exact Work.Resample.PBChunk.vsz_chunks xs S hS hdvd
    have h : (List.map HvdH.vsz (List.take (1 + 1) o4)).sum + 1
        = HvdH.vsz (HvdH.ofList xs) + 2 * (xs.length / S) + HvdH.isz (S : ℤ) + 1 := by
      rw [ho4']
      show (List.map HvdH.vsz [HvdH.ofList ((List.range (xs.length / S)).map
        fun i => HvdH.ofList ((xs.drop (i * S)).take S)), HvdH.Val.int (S : ℤ)]).sum + 1
        = HvdH.vsz (HvdH.ofList xs) + 2 * (xs.length / S) + HvdH.isz (S : ℤ) + 1
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hvsz_int,
        Nat.add_zero]
      rw [hvs]
    calc n5 ≤ Kr * (1 + 1) * ((List.map HvdH.vsz (List.take (1 + 1) o4)).sum + 1) := hn5
      _ = Kr * 2 * (HvdH.vsz (HvdH.ofList xs) + 2 * (xs.length / S) + HvdH.isz (S : ℤ) + 1) := by
        rw [h]
  -- ### the composed evaluation
  have H1 : Work.Layout.Ev main dupP s s1 (Kd * (HvdH.isz (S:ℤ) + 1)) := ⟨n1, he1, hb1⟩
  have H2 : Work.Layout.Ev main (rollP 2) s1 s2
      (Kr * 3 * (2 * HvdH.isz (S:ℤ) + HvdH.vsz (HvdH.ofList xs) + 1)) := ⟨n2, he2, hb2⟩
  have H3 : Work.Layout.Ev main (rollP 1) s2 s3
      (Kr * 2 * (HvdH.vsz (HvdH.ofList xs) + HvdH.isz (S:ℤ) + 1)) := ⟨n3, he3, hb3⟩
  have H4 : Work.Layout.Ev main chP s3 s4
      (Kc * (HvdH.vsz (HvdH.ofList xs) + (xs.length / S + 1) * HvdH.isz (S:ℤ) + 1)) :=
    ⟨n4, he4, hb4⟩
  have H5 : Work.Layout.Ev main (rollP 1) s4 s5
      (Kr * 2 * (HvdH.vsz (HvdH.ofList xs) + 2 * (xs.length / S) + HvdH.isz (S:ℤ) + 1)) :=
    ⟨n5, he5, hb5⟩
  have h45 : Work.Layout.Ev main (Work.Layout.seqs [chP, rollP 1]) s3 s5
      (Kc * (HvdH.vsz (HvdH.ofList xs) + (xs.length / S + 1) * HvdH.isz (S:ℤ) + 1)
       + Kr * 2 * (HvdH.vsz (HvdH.ofList xs) + 2 * (xs.length / S) + HvdH.isz (S:ℤ) + 1)) :=
    Work.Layout.Ev.seqs_cons H4 H5
  have h345 : Work.Layout.Ev main (Work.Layout.seqs [rollP 1, chP, rollP 1]) s2 s5
      (Kr * 2 * (HvdH.vsz (HvdH.ofList xs) + HvdH.isz (S:ℤ) + 1)
       + (Kc * (HvdH.vsz (HvdH.ofList xs) + (xs.length / S + 1) * HvdH.isz (S:ℤ) + 1)
       + Kr * 2 * (HvdH.vsz (HvdH.ofList xs) + 2 * (xs.length / S) + HvdH.isz (S:ℤ) + 1))) :=
    Work.Layout.Ev.seqs_cons H3 h45
  have h2345 : Work.Layout.Ev main (Work.Layout.seqs [rollP 2, rollP 1, chP, rollP 1]) s1 s5
      (Kr * 3 * (2 * HvdH.isz (S:ℤ) + HvdH.vsz (HvdH.ofList xs) + 1)
       + (Kr * 2 * (HvdH.vsz (HvdH.ofList xs) + HvdH.isz (S:ℤ) + 1)
       + (Kc * (HvdH.vsz (HvdH.ofList xs) + (xs.length / S + 1) * HvdH.isz (S:ℤ) + 1)
       + Kr * 2 * (HvdH.vsz (HvdH.ofList xs) + 2 * (xs.length / S) + HvdH.isz (S:ℤ) + 1)))) :=
    Work.Layout.Ev.seqs_cons H2 h345
  have hAll : Work.Layout.Ev main (Work.Layout.seqs [dupP, rollP 2, rollP 1, chP, rollP 1]) s s5
      (Kd * (HvdH.isz (S:ℤ) + 1)
       + (Kr * 3 * (2 * HvdH.isz (S:ℤ) + HvdH.vsz (HvdH.ofList xs) + 1)
       + (Kr * 2 * (HvdH.vsz (HvdH.ofList xs) + HvdH.isz (S:ℤ) + 1)
       + (Kc * (HvdH.vsz (HvdH.ofList xs) + (xs.length / S + 1) * HvdH.isz (S:ℤ) + 1)
       + Kr * 2 * (HvdH.vsz (HvdH.ofList xs) + 2 * (xs.length / S) + HvdH.isz (S:ℤ) + 1))))) :=
    Work.Layout.Ev.seqs_cons H1 h2345
  obtain ⟨n, hev, hcost⟩ := hAll
  clear hn1 hn2 hn3 hn4 hn5
  refine ⟨o5, s5, n, ?_, hev, ?_, ?_, ?_⟩
  · rw [ho5', hblk]
  · -- cost: absorb the five step bounds
    show n ≤ (1000 * (Kc + Kd + Kr) + 1000) * (HvdH.vsz (HvdH.ofList xs) + 1) +
        (1000 * (Kc + Kd + Kr) + 1000) * ((xs.length / S + 1) * (HvdH.isz (S:ℤ) + 1) + 1)
    have hq : xs.length / S ≤ HvdH.vsz (HvdH.ofList xs) :=
      le_trans (Nat.div_le_self _ _) (Work.Resample.PBChunk.length_le_vsz_ofList xs)
    have hcost' : n ≤ Kd * (HvdH.isz (S:ℤ) + 1) + Kr * 3 * (2 * HvdH.isz (S:ℤ)
        + HvdH.vsz (HvdH.ofList xs) + 1) + Kr * 2 * (HvdH.vsz (HvdH.ofList xs)
        + HvdH.isz (S:ℤ) + 1) + Kc * (HvdH.vsz (HvdH.ofList xs)
        + (xs.length / S + 1) * HvdH.isz (S:ℤ) + 1) + Kr * 2 * (HvdH.vsz (HvdH.ofList xs)
        + 2 * (xs.length / S) + HvdH.isz (S:ℤ) + 1) := by
      omega
    have habs := Work.Resample.chunkCostAbs Kc Kd Kr (HvdH.vsz (HvdH.ofList xs))
      (HvdH.isz (S : ℤ)) (xs.length / S) hq
    rw [Nat.mul_add (1000 * (Kc + Kd + Kr) + 1000) (HvdH.vsz (HvdH.ofList xs) + 1)
      ((xs.length / S + 1) * (HvdH.isz (S : ℤ) + 1) + 1)] at habs
    exact le_trans hcost' habs
  · exact hs5
  · intro k hk
    exact (hf5 k hk).trans ((hf4 k hk).trans ((hf3 k hk).trans ((hf2 k hk).trans (hf1 k hk))))

end Work.Resample
