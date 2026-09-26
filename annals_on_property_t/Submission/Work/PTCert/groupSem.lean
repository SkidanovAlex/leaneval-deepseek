import Submission.Work.PTCert.groupSemAux

/-! Guidance from the project lead (the requester):

Context: `Submission/Work/PTCert/Glue2.lean` (concrete objects and the semantic Props of the data) and
`Glue3.lean` (math steps), `KernelShared.lean`/`KernelCert.lean` (the Bool check functions), the data
modules `Data/*.lean` (namespace `Submission.PTCert.D`) and the kernel theorems `Checks/*.lean`
(namespace `Submission.PTCert.C`, each `theorem xxx : <check> = true := by decide +kernel`, ALREADY BUILT).
Design notes: `NOTES_LEAD_glue.md` at the workspace root.
Checks (rows r = 1..17): `C.mem_ok{r}_{j}` (memGroupsOK cmT eM labT{r} stabT{r} grepT{r} gl{r}_{j} gsz{r}_{j} g0),
`C.gsz_ok{r}`, `C.sizes_ok{r}` (Σ sizes = 4641 ∧ length = ngL[r]), `C.grep_ok{r}`, `C.clos_ok{r}_{j}`,
plus `C.memidx_ok{r}_{j}` and `C.stablen_ok{r}` (module `Checks.X`).

The proof is factored as follows.  `Submission/Work/PTCert/groupSemAux.lean` contains the generic
machinery (`allL_iff_eAux`, `eqL_iff_eAux`, `strictInc → Nodup`, soundness of the checks `memGroupsOK`,
`memIdxOK`, `closOK`, `grepOK`, the chunk predicate `GroupChunk`, the cumulative-offset concatenation
`GroupsAt_cumul`, and the one-row reduction `genericGroups`).  Here each of the seventeen rows is
reduced to `genericGroups` using its own kernel checks, and the results are assembled.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace Work.PTCert

open Submission.PTCert Submission.PTCert.G Submission.PTCert.D Submission.PTCert.C
open Work.PTCert.GSAux
open scoped BigOperators

theorem row1 :
    (∀ z ∈ eAll, labE 1 z < ngE 1 ∧ ∃ i < (stabL 1).length,
        actC cmT (stabTab 1 i) (grepE 1 (labE 1 z)) = z) ∧
    (∀ g < ngE 1, grepE 1 g ∈ eAll ∧ labE 1 (grepE 1 g) = g) ∧
    (∀ i < (stabL 1).length, ∀ g < ngE 1,
        labE 1 (actC cmT (stabTab 1 i) (grepE 1 g)) = g) ∧
    (∀ g < ngE 1, (eAll.filter (fun z => labE 1 z = g)).length = sizeE 1 g) ∧
    (sizesL.getD 1 []).length = ngE 1 := by
  have hs_ok : sumL sizes1 = 4641 ∧ sizes1.length = ngE 1 := by
    have h := sizes_ok1
    rw [Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    rw [Nat.beq_eq] at h1
    rw [decide_eq_true_eq, Nat.beq_eq] at h2
    exact ⟨h1, h2⟩
  have hszlen : sizes1.length = ngE 1 := hs_ok.2
  have hm0 : gl1_0.map List.length = gsz1_0 := (memGroupsOK_sound mem_ok1_0).1
  have hm1 : gl1_1.map List.length = gsz1_1 := (memGroupsOK_sound mem_ok1_1).1
  have hm2 : gl1_2.map List.length = gsz1_2 := (memGroupsOK_sound mem_ok1_2).1
  have hm3 : gl1_3.map List.length = gsz1_3 := (memGroupsOK_sound mem_ok1_3).1
  have hm4 : gl1_4.map List.length = gsz1_4 := (memGroupsOK_sound mem_ok1_4).1
  have hm5 : gl1_5.map List.length = gsz1_5 := (memGroupsOK_sound mem_ok1_5).1
  have hm6 : gl1_6.map List.length = gsz1_6 := (memGroupsOK_sound mem_ok1_6).1
  have hL0 : (gl1_0).length = 88 := by decide
  have hL1 : (gl1_1).length = 94 := by decide
  have hL2 : (gl1_2).length = 46 := by decide
  have hL3 : (gl1_3).length = 63 := by decide
  have hL4 : (gl1_4).length = 58 := by decide
  have hL5 : (gl1_5).length = 30 := by decide
  have hgsz : sizes1 = [gsz1_0, gsz1_1, gsz1_2, gsz1_3, gsz1_4, gsz1_5, gsz1_6].flatten := by
    rw [eqL_eq.mp gsz_ok1]
    rfl
  have hG : GroupsAt cmT eM labT1 stabT1 grepT1 [gl1_0, gl1_1, gl1_2, gl1_3, gl1_4, gl1_5, gl1_6].flatten 0 := by
    refine GroupsAt_cumul _ 0 ?_
    intro j hj
    have hj' : j < 7 := by simpa using hj
    interval_cases j
    · exact (memGroupsOK_sound mem_ok1_0).2
    · have ho : (cumul (0:ℕ) [gl1_0, gl1_1, gl1_2, gl1_3, gl1_4, gl1_5, gl1_6]).getD 1 0 = 88 := by
        show (0 + (gl1_0).length) = 88
        rw [hL0]
      rw [ho]; exact (memGroupsOK_sound mem_ok1_1).2
    · have ho : (cumul (0:ℕ) [gl1_0, gl1_1, gl1_2, gl1_3, gl1_4, gl1_5, gl1_6]).getD 2 0 = 182 := by
        show ((0 + (gl1_0).length) + (gl1_1).length) = 182
        rw [hL0, hL1]
      rw [ho]; exact (memGroupsOK_sound mem_ok1_2).2
    · have ho : (cumul (0:ℕ) [gl1_0, gl1_1, gl1_2, gl1_3, gl1_4, gl1_5, gl1_6]).getD 3 0 = 228 := by
        show (((0 + (gl1_0).length) + (gl1_1).length) + (gl1_2).length) = 228
        rw [hL0, hL1, hL2]
      rw [ho]; exact (memGroupsOK_sound mem_ok1_3).2
    · have ho : (cumul (0:ℕ) [gl1_0, gl1_1, gl1_2, gl1_3, gl1_4, gl1_5, gl1_6]).getD 4 0 = 291 := by
        show ((((0 + (gl1_0).length) + (gl1_1).length) + (gl1_2).length) + (gl1_3).length) = 291
        rw [hL0, hL1, hL2, hL3]
      rw [ho]; exact (memGroupsOK_sound mem_ok1_4).2
    · have ho : (cumul (0:ℕ) [gl1_0, gl1_1, gl1_2, gl1_3, gl1_4, gl1_5, gl1_6]).getD 5 0 = 349 := by
        show (((((0 + (gl1_0).length) + (gl1_1).length) + (gl1_2).length) + (gl1_3).length) + (gl1_4).length) = 349
        rw [hL0, hL1, hL2, hL3, hL4]
      rw [ho]; exact (memGroupsOK_sound mem_ok1_5).2
    · have ho : (cumul (0:ℕ) [gl1_0, gl1_1, gl1_2, gl1_3, gl1_4, gl1_5, gl1_6]).getD 6 0 = 379 := by
        show ((((((0 + (gl1_0).length) + (gl1_1).length) + (gl1_2).length) + (gl1_3).length) + (gl1_4).length) + (gl1_5).length) = 379
        rw [hL0, hL1, hL2, hL3, hL4, hL5]
      rw [ho]; exact (memGroupsOK_sound mem_ok1_6).2
  have hmap : ([gl1_0, gl1_1, gl1_2, gl1_3, gl1_4, gl1_5, gl1_6].map (fun l => l.map List.length)) = [gsz1_0, gsz1_1, gsz1_2, gsz1_3, gsz1_4, gsz1_5, gsz1_6] := by
    simp only [List.map_cons, List.map_nil, hm0, hm1, hm2, hm3, hm4, hm5, hm6]
  have hGsz : ([gl1_0, gl1_1, gl1_2, gl1_3, gl1_4, gl1_5, gl1_6].flatten).map List.length = sizes1 := by
    rw [hgsz, List.map_flatten, hmap]
  have hGlen : ([gl1_0, gl1_1, gl1_2, gl1_3, gl1_4, gl1_5, gl1_6].flatten).length = ngE 1 := by
    rw [show ([gl1_0, gl1_1, gl1_2, gl1_3, gl1_4, gl1_5, gl1_6].flatten).length = (([gl1_0, gl1_1, gl1_2, gl1_3, gl1_4, gl1_5, gl1_6].flatten).map List.length).length from
      (List.length_map List.length).symm, hGsz]
    exact hszlen
  have hsum : (([gl1_0, gl1_1, gl1_2, gl1_3, gl1_4, gl1_5, gl1_6].flatten).flatten).length = 4641 := by
    rw [List.length_flatten, hGsz, ← sumL_eq_sum]; exact hs_ok.1
  have hrep : ∀ g < ngE 1, cG grepT1 g ∈ eAll ∧ lG labT1 (cG grepT1 g) = g := by
    intro g hg
    have h := grepOK_sound grep_ok1 g hg
    exact ⟨Work.PTCert.NSemAux.mem_eAll_of_em_ne_zero h.1 h.2.1, h.2.2⟩
  have hStabLen : (stabL 1).length = 48 := by
    have h := stablen_ok1
    rw [Nat.beq_eq] at h
    exact h
  have hstab : ∀ s < (stabL 1).length, ∀ k < 81, lk (stabT1.get s) k < 81 := by
    intro s hs k hk
    obtain ⟨pc, sc, hpc, htab⟩ := tabsOK_sound stabtab_ok1 s hs
    rw [htab k hk]
    exact Work.PTCert.codeFactsAux.actLBound pc sc hpc k hk
  have hssrange : [[0,1,2,3,4], [5,6,7,8,9], [10,11,12,13,14], [15,16,17,18,19], [20,21,22,23,24], [25,26,27,28,29], [30,31,32,33,34], [35,36,37,38,39], [40,41,42,43,44], [45,46,47]].flatten = List.range 48 := by decide
  have hclos : ∀ s < (stabL 1).length, ∀ g < ngE 1,
      lG labT1 (actC cmT (stabT1.get s) (cG grepT1 g)) = g := by
    intro s hs g hg
    have hs' : s ∈ [[0,1,2,3,4], [5,6,7,8,9], [10,11,12,13,14], [15,16,17,18,19], [20,21,22,23,24], [25,26,27,28,29], [30,31,32,33,34], [35,36,37,38,39], [40,41,42,43,44], [45,46,47]].flatten := by
      rw [hssrange, List.mem_range]; rwa [hStabLen] at hs
    exact closOK_flatten_spec (chunks := [[0,1,2,3,4], [5,6,7,8,9], [10,11,12,13,14], [15,16,17,18,19], [20,21,22,23,24], [25,26,27,28,29], [30,31,32,33,34], [35,36,37,38,39], [40,41,42,43,44], [45,46,47]]) (gs := List.range (ngE 1))
      (fun j hj => by
        have hj' : j < 10 := by simpa using hj
        interval_cases j
        · exact clos_ok1_0
        · exact clos_ok1_1
        · exact clos_ok1_2
        · exact clos_ok1_3
        · exact clos_ok1_4
        · exact clos_ok1_5
        · exact clos_ok1_6
        · exact clos_ok1_7
        · exact clos_ok1_8
        · exact clos_ok1_9
        )
      g (List.mem_range.mpr hg) s hs'
  have hidx : ∀ i < ([gl1_0, gl1_1, gl1_2, gl1_3, gl1_4, gl1_5, gl1_6].flatten).length, ∀ v ∈ ([gl1_0, gl1_1, gl1_2, gl1_3, gl1_4, gl1_5, gl1_6].flatten).getD i [],
      v % 4096 < (stabL 1).length := by
    intro i hi v hv
    have hmem : ([gl1_0, gl1_1, gl1_2, gl1_3, gl1_4, gl1_5, gl1_6].flatten).getD i [] ∈ ([gl1_0, gl1_1, gl1_2, gl1_3, gl1_4, gl1_5, gl1_6].flatten) := getD_mem hi
    have h := memIdxOK_flatten_spec (chunks := [gl1_0, gl1_1, gl1_2, gl1_3, gl1_4, gl1_5, gl1_6]) (ns := 48)
      (fun j hj => by
        have hj' : j < 7 := by simpa using hj
        interval_cases j
        · exact memidx_ok1_0
        · exact memidx_ok1_1
        · exact memidx_ok1_2
        · exact memidx_ok1_3
        · exact memidx_ok1_4
        · exact memidx_ok1_5
        · exact memidx_ok1_6
        ) _ hmem v hv
    rwa [hStabLen]
  exact genericGroups labT1 stabT1 grepT1 (stabL1) (sizes1) ([gl1_0, gl1_1, gl1_2, gl1_3, gl1_4, gl1_5, gl1_6].flatten) (ngE 1)
    hG hGsz hGlen hszlen hsum hrep hstab hclos hidx

theorem row2 :
    (∀ z ∈ eAll, labE 2 z < ngE 2 ∧ ∃ i < (stabL 2).length,
        actC cmT (stabTab 2 i) (grepE 2 (labE 2 z)) = z) ∧
    (∀ g < ngE 2, grepE 2 g ∈ eAll ∧ labE 2 (grepE 2 g) = g) ∧
    (∀ i < (stabL 2).length, ∀ g < ngE 2,
        labE 2 (actC cmT (stabTab 2 i) (grepE 2 g)) = g) ∧
    (∀ g < ngE 2, (eAll.filter (fun z => labE 2 z = g)).length = sizeE 2 g) ∧
    (sizesL.getD 2 []).length = ngE 2 := by
  have hs_ok : sumL sizes2 = 4641 ∧ sizes2.length = ngE 2 := by
    have h := sizes_ok2
    rw [Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    rw [Nat.beq_eq] at h1
    rw [decide_eq_true_eq, Nat.beq_eq] at h2
    exact ⟨h1, h2⟩
  have hszlen : sizes2.length = ngE 2 := hs_ok.2
  have hm0 : gl2_0.map List.length = gsz2_0 := (memGroupsOK_sound mem_ok2_0).1
  have hm1 : gl2_1.map List.length = gsz2_1 := (memGroupsOK_sound mem_ok2_1).1
  have hm2 : gl2_2.map List.length = gsz2_2 := (memGroupsOK_sound mem_ok2_2).1
  have hm3 : gl2_3.map List.length = gsz2_3 := (memGroupsOK_sound mem_ok2_3).1
  have hm4 : gl2_4.map List.length = gsz2_4 := (memGroupsOK_sound mem_ok2_4).1
  have hm5 : gl2_5.map List.length = gsz2_5 := (memGroupsOK_sound mem_ok2_5).1
  have hm6 : gl2_6.map List.length = gsz2_6 := (memGroupsOK_sound mem_ok2_6).1
  have hL0 : (gl2_0).length = 88 := by decide
  have hL1 : (gl2_1).length = 94 := by decide
  have hL2 : (gl2_2).length = 46 := by decide
  have hL3 : (gl2_3).length = 63 := by decide
  have hL4 : (gl2_4).length = 58 := by decide
  have hL5 : (gl2_5).length = 30 := by decide
  have hgsz : sizes2 = [gsz2_0, gsz2_1, gsz2_2, gsz2_3, gsz2_4, gsz2_5, gsz2_6].flatten := by
    rw [eqL_eq.mp gsz_ok2]
    rfl
  have hG : GroupsAt cmT eM labT2 stabT2 grepT2 [gl2_0, gl2_1, gl2_2, gl2_3, gl2_4, gl2_5, gl2_6].flatten 0 := by
    refine GroupsAt_cumul _ 0 ?_
    intro j hj
    have hj' : j < 7 := by simpa using hj
    interval_cases j
    · exact (memGroupsOK_sound mem_ok2_0).2
    · have ho : (cumul (0:ℕ) [gl2_0, gl2_1, gl2_2, gl2_3, gl2_4, gl2_5, gl2_6]).getD 1 0 = 88 := by
        show (0 + (gl2_0).length) = 88
        rw [hL0]
      rw [ho]; exact (memGroupsOK_sound mem_ok2_1).2
    · have ho : (cumul (0:ℕ) [gl2_0, gl2_1, gl2_2, gl2_3, gl2_4, gl2_5, gl2_6]).getD 2 0 = 182 := by
        show ((0 + (gl2_0).length) + (gl2_1).length) = 182
        rw [hL0, hL1]
      rw [ho]; exact (memGroupsOK_sound mem_ok2_2).2
    · have ho : (cumul (0:ℕ) [gl2_0, gl2_1, gl2_2, gl2_3, gl2_4, gl2_5, gl2_6]).getD 3 0 = 228 := by
        show (((0 + (gl2_0).length) + (gl2_1).length) + (gl2_2).length) = 228
        rw [hL0, hL1, hL2]
      rw [ho]; exact (memGroupsOK_sound mem_ok2_3).2
    · have ho : (cumul (0:ℕ) [gl2_0, gl2_1, gl2_2, gl2_3, gl2_4, gl2_5, gl2_6]).getD 4 0 = 291 := by
        show ((((0 + (gl2_0).length) + (gl2_1).length) + (gl2_2).length) + (gl2_3).length) = 291
        rw [hL0, hL1, hL2, hL3]
      rw [ho]; exact (memGroupsOK_sound mem_ok2_4).2
    · have ho : (cumul (0:ℕ) [gl2_0, gl2_1, gl2_2, gl2_3, gl2_4, gl2_5, gl2_6]).getD 5 0 = 349 := by
        show (((((0 + (gl2_0).length) + (gl2_1).length) + (gl2_2).length) + (gl2_3).length) + (gl2_4).length) = 349
        rw [hL0, hL1, hL2, hL3, hL4]
      rw [ho]; exact (memGroupsOK_sound mem_ok2_5).2
    · have ho : (cumul (0:ℕ) [gl2_0, gl2_1, gl2_2, gl2_3, gl2_4, gl2_5, gl2_6]).getD 6 0 = 379 := by
        show ((((((0 + (gl2_0).length) + (gl2_1).length) + (gl2_2).length) + (gl2_3).length) + (gl2_4).length) + (gl2_5).length) = 379
        rw [hL0, hL1, hL2, hL3, hL4, hL5]
      rw [ho]; exact (memGroupsOK_sound mem_ok2_6).2
  have hmap : ([gl2_0, gl2_1, gl2_2, gl2_3, gl2_4, gl2_5, gl2_6].map (fun l => l.map List.length)) = [gsz2_0, gsz2_1, gsz2_2, gsz2_3, gsz2_4, gsz2_5, gsz2_6] := by
    simp only [List.map_cons, List.map_nil, hm0, hm1, hm2, hm3, hm4, hm5, hm6]
  have hGsz : ([gl2_0, gl2_1, gl2_2, gl2_3, gl2_4, gl2_5, gl2_6].flatten).map List.length = sizes2 := by
    rw [hgsz, List.map_flatten, hmap]
  have hGlen : ([gl2_0, gl2_1, gl2_2, gl2_3, gl2_4, gl2_5, gl2_6].flatten).length = ngE 2 := by
    rw [show ([gl2_0, gl2_1, gl2_2, gl2_3, gl2_4, gl2_5, gl2_6].flatten).length = (([gl2_0, gl2_1, gl2_2, gl2_3, gl2_4, gl2_5, gl2_6].flatten).map List.length).length from
      (List.length_map List.length).symm, hGsz]
    exact hszlen
  have hsum : (([gl2_0, gl2_1, gl2_2, gl2_3, gl2_4, gl2_5, gl2_6].flatten).flatten).length = 4641 := by
    rw [List.length_flatten, hGsz, ← sumL_eq_sum]; exact hs_ok.1
  have hrep : ∀ g < ngE 2, cG grepT2 g ∈ eAll ∧ lG labT2 (cG grepT2 g) = g := by
    intro g hg
    have h := grepOK_sound grep_ok2 g hg
    exact ⟨Work.PTCert.NSemAux.mem_eAll_of_em_ne_zero h.1 h.2.1, h.2.2⟩
  have hStabLen : (stabL 2).length = 48 := by
    have h := stablen_ok2
    rw [Nat.beq_eq] at h
    exact h
  have hstab : ∀ s < (stabL 2).length, ∀ k < 81, lk (stabT2.get s) k < 81 := by
    intro s hs k hk
    obtain ⟨pc, sc, hpc, htab⟩ := tabsOK_sound stabtab_ok2 s hs
    rw [htab k hk]
    exact Work.PTCert.codeFactsAux.actLBound pc sc hpc k hk
  have hssrange : [[0,1,2,3,4], [5,6,7,8,9], [10,11,12,13,14], [15,16,17,18,19], [20,21,22,23,24], [25,26,27,28,29], [30,31,32,33,34], [35,36,37,38,39], [40,41,42,43,44], [45,46,47]].flatten = List.range 48 := by decide
  have hclos : ∀ s < (stabL 2).length, ∀ g < ngE 2,
      lG labT2 (actC cmT (stabT2.get s) (cG grepT2 g)) = g := by
    intro s hs g hg
    have hs' : s ∈ [[0,1,2,3,4], [5,6,7,8,9], [10,11,12,13,14], [15,16,17,18,19], [20,21,22,23,24], [25,26,27,28,29], [30,31,32,33,34], [35,36,37,38,39], [40,41,42,43,44], [45,46,47]].flatten := by
      rw [hssrange, List.mem_range]; rwa [hStabLen] at hs
    exact closOK_flatten_spec (chunks := [[0,1,2,3,4], [5,6,7,8,9], [10,11,12,13,14], [15,16,17,18,19], [20,21,22,23,24], [25,26,27,28,29], [30,31,32,33,34], [35,36,37,38,39], [40,41,42,43,44], [45,46,47]]) (gs := List.range (ngE 2))
      (fun j hj => by
        have hj' : j < 10 := by simpa using hj
        interval_cases j
        · exact clos_ok2_0
        · exact clos_ok2_1
        · exact clos_ok2_2
        · exact clos_ok2_3
        · exact clos_ok2_4
        · exact clos_ok2_5
        · exact clos_ok2_6
        · exact clos_ok2_7
        · exact clos_ok2_8
        · exact clos_ok2_9
        )
      g (List.mem_range.mpr hg) s hs'
  have hidx : ∀ i < ([gl2_0, gl2_1, gl2_2, gl2_3, gl2_4, gl2_5, gl2_6].flatten).length, ∀ v ∈ ([gl2_0, gl2_1, gl2_2, gl2_3, gl2_4, gl2_5, gl2_6].flatten).getD i [],
      v % 4096 < (stabL 2).length := by
    intro i hi v hv
    have hmem : ([gl2_0, gl2_1, gl2_2, gl2_3, gl2_4, gl2_5, gl2_6].flatten).getD i [] ∈ ([gl2_0, gl2_1, gl2_2, gl2_3, gl2_4, gl2_5, gl2_6].flatten) := getD_mem hi
    have h := memIdxOK_flatten_spec (chunks := [gl2_0, gl2_1, gl2_2, gl2_3, gl2_4, gl2_5, gl2_6]) (ns := 48)
      (fun j hj => by
        have hj' : j < 7 := by simpa using hj
        interval_cases j
        · exact memidx_ok2_0
        · exact memidx_ok2_1
        · exact memidx_ok2_2
        · exact memidx_ok2_3
        · exact memidx_ok2_4
        · exact memidx_ok2_5
        · exact memidx_ok2_6
        ) _ hmem v hv
    rwa [hStabLen]
  exact genericGroups labT2 stabT2 grepT2 (stabL2) (sizes2) ([gl2_0, gl2_1, gl2_2, gl2_3, gl2_4, gl2_5, gl2_6].flatten) (ngE 2)
    hG hGsz hGlen hszlen hsum hrep hstab hclos hidx

theorem row3 :
    (∀ z ∈ eAll, labE 3 z < ngE 3 ∧ ∃ i < (stabL 3).length,
        actC cmT (stabTab 3 i) (grepE 3 (labE 3 z)) = z) ∧
    (∀ g < ngE 3, grepE 3 g ∈ eAll ∧ labE 3 (grepE 3 g) = g) ∧
    (∀ i < (stabL 3).length, ∀ g < ngE 3,
        labE 3 (actC cmT (stabTab 3 i) (grepE 3 g)) = g) ∧
    (∀ g < ngE 3, (eAll.filter (fun z => labE 3 z = g)).length = sizeE 3 g) ∧
    (sizesL.getD 3 []).length = ngE 3 := by
  have hs_ok : sumL sizes3 = 4641 ∧ sizes3.length = ngE 3 := by
    have h := sizes_ok3
    rw [Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    rw [Nat.beq_eq] at h1
    rw [decide_eq_true_eq, Nat.beq_eq] at h2
    exact ⟨h1, h2⟩
  have hszlen : sizes3.length = ngE 3 := hs_ok.2
  have hm0 : gl3_0.map List.length = gsz3_0 := (memGroupsOK_sound mem_ok3_0).1
  have hm1 : gl3_1.map List.length = gsz3_1 := (memGroupsOK_sound mem_ok3_1).1
  have hm2 : gl3_2.map List.length = gsz3_2 := (memGroupsOK_sound mem_ok3_2).1
  have hm3 : gl3_3.map List.length = gsz3_3 := (memGroupsOK_sound mem_ok3_3).1
  have hm4 : gl3_4.map List.length = gsz3_4 := (memGroupsOK_sound mem_ok3_4).1
  have hm5 : gl3_5.map List.length = gsz3_5 := (memGroupsOK_sound mem_ok3_5).1
  have hm6 : gl3_6.map List.length = gsz3_6 := (memGroupsOK_sound mem_ok3_6).1
  have hL0 : (gl3_0).length = 52 := by decide
  have hL1 : (gl3_1).length = 51 := by decide
  have hL2 : (gl3_2).length = 23 := by decide
  have hL3 : (gl3_3).length = 32 := by decide
  have hL4 : (gl3_4).length = 28 := by decide
  have hL5 : (gl3_5).length = 18 := by decide
  have hgsz : sizes3 = [gsz3_0, gsz3_1, gsz3_2, gsz3_3, gsz3_4, gsz3_5, gsz3_6].flatten := by
    rw [eqL_eq.mp gsz_ok3]
    rfl
  have hG : GroupsAt cmT eM labT3 stabT3 grepT3 [gl3_0, gl3_1, gl3_2, gl3_3, gl3_4, gl3_5, gl3_6].flatten 0 := by
    refine GroupsAt_cumul _ 0 ?_
    intro j hj
    have hj' : j < 7 := by simpa using hj
    interval_cases j
    · exact (memGroupsOK_sound mem_ok3_0).2
    · have ho : (cumul (0:ℕ) [gl3_0, gl3_1, gl3_2, gl3_3, gl3_4, gl3_5, gl3_6]).getD 1 0 = 52 := by
        show (0 + (gl3_0).length) = 52
        rw [hL0]
      rw [ho]; exact (memGroupsOK_sound mem_ok3_1).2
    · have ho : (cumul (0:ℕ) [gl3_0, gl3_1, gl3_2, gl3_3, gl3_4, gl3_5, gl3_6]).getD 2 0 = 103 := by
        show ((0 + (gl3_0).length) + (gl3_1).length) = 103
        rw [hL0, hL1]
      rw [ho]; exact (memGroupsOK_sound mem_ok3_2).2
    · have ho : (cumul (0:ℕ) [gl3_0, gl3_1, gl3_2, gl3_3, gl3_4, gl3_5, gl3_6]).getD 3 0 = 126 := by
        show (((0 + (gl3_0).length) + (gl3_1).length) + (gl3_2).length) = 126
        rw [hL0, hL1, hL2]
      rw [ho]; exact (memGroupsOK_sound mem_ok3_3).2
    · have ho : (cumul (0:ℕ) [gl3_0, gl3_1, gl3_2, gl3_3, gl3_4, gl3_5, gl3_6]).getD 4 0 = 158 := by
        show ((((0 + (gl3_0).length) + (gl3_1).length) + (gl3_2).length) + (gl3_3).length) = 158
        rw [hL0, hL1, hL2, hL3]
      rw [ho]; exact (memGroupsOK_sound mem_ok3_4).2
    · have ho : (cumul (0:ℕ) [gl3_0, gl3_1, gl3_2, gl3_3, gl3_4, gl3_5, gl3_6]).getD 5 0 = 186 := by
        show (((((0 + (gl3_0).length) + (gl3_1).length) + (gl3_2).length) + (gl3_3).length) + (gl3_4).length) = 186
        rw [hL0, hL1, hL2, hL3, hL4]
      rw [ho]; exact (memGroupsOK_sound mem_ok3_5).2
    · have ho : (cumul (0:ℕ) [gl3_0, gl3_1, gl3_2, gl3_3, gl3_4, gl3_5, gl3_6]).getD 6 0 = 204 := by
        show ((((((0 + (gl3_0).length) + (gl3_1).length) + (gl3_2).length) + (gl3_3).length) + (gl3_4).length) + (gl3_5).length) = 204
        rw [hL0, hL1, hL2, hL3, hL4, hL5]
      rw [ho]; exact (memGroupsOK_sound mem_ok3_6).2
  have hmap : ([gl3_0, gl3_1, gl3_2, gl3_3, gl3_4, gl3_5, gl3_6].map (fun l => l.map List.length)) = [gsz3_0, gsz3_1, gsz3_2, gsz3_3, gsz3_4, gsz3_5, gsz3_6] := by
    simp only [List.map_cons, List.map_nil, hm0, hm1, hm2, hm3, hm4, hm5, hm6]
  have hGsz : ([gl3_0, gl3_1, gl3_2, gl3_3, gl3_4, gl3_5, gl3_6].flatten).map List.length = sizes3 := by
    rw [hgsz, List.map_flatten, hmap]
  have hGlen : ([gl3_0, gl3_1, gl3_2, gl3_3, gl3_4, gl3_5, gl3_6].flatten).length = ngE 3 := by
    rw [show ([gl3_0, gl3_1, gl3_2, gl3_3, gl3_4, gl3_5, gl3_6].flatten).length = (([gl3_0, gl3_1, gl3_2, gl3_3, gl3_4, gl3_5, gl3_6].flatten).map List.length).length from
      (List.length_map List.length).symm, hGsz]
    exact hszlen
  have hsum : (([gl3_0, gl3_1, gl3_2, gl3_3, gl3_4, gl3_5, gl3_6].flatten).flatten).length = 4641 := by
    rw [List.length_flatten, hGsz, ← sumL_eq_sum]; exact hs_ok.1
  have hrep : ∀ g < ngE 3, cG grepT3 g ∈ eAll ∧ lG labT3 (cG grepT3 g) = g := by
    intro g hg
    have h := grepOK_sound grep_ok3 g hg
    exact ⟨Work.PTCert.NSemAux.mem_eAll_of_em_ne_zero h.1 h.2.1, h.2.2⟩
  have hStabLen : (stabL 3).length = 96 := by
    have h := stablen_ok3
    rw [Nat.beq_eq] at h
    exact h
  have hstab : ∀ s < (stabL 3).length, ∀ k < 81, lk (stabT3.get s) k < 81 := by
    intro s hs k hk
    obtain ⟨pc, sc, hpc, htab⟩ := tabsOK_sound stabtab_ok3 s hs
    rw [htab k hk]
    exact Work.PTCert.codeFactsAux.actLBound pc sc hpc k hk
  have hssrange : [[0,1,2,3,4,5,6,7,8], [9,10,11,12,13,14,15,16,17], [18,19,20,21,22,23,24,25,26], [27,28,29,30,31,32,33,34,35], [36,37,38,39,40,41,42,43,44], [45,46,47,48,49,50,51,52,53], [54,55,56,57,58,59,60,61,62], [63,64,65,66,67,68,69,70,71], [72,73,74,75,76,77,78,79,80], [81,82,83,84,85,86,87,88,89], [90,91,92,93,94,95]].flatten = List.range 96 := by decide
  have hclos : ∀ s < (stabL 3).length, ∀ g < ngE 3,
      lG labT3 (actC cmT (stabT3.get s) (cG grepT3 g)) = g := by
    intro s hs g hg
    have hs' : s ∈ [[0,1,2,3,4,5,6,7,8], [9,10,11,12,13,14,15,16,17], [18,19,20,21,22,23,24,25,26], [27,28,29,30,31,32,33,34,35], [36,37,38,39,40,41,42,43,44], [45,46,47,48,49,50,51,52,53], [54,55,56,57,58,59,60,61,62], [63,64,65,66,67,68,69,70,71], [72,73,74,75,76,77,78,79,80], [81,82,83,84,85,86,87,88,89], [90,91,92,93,94,95]].flatten := by
      rw [hssrange, List.mem_range]; rwa [hStabLen] at hs
    exact closOK_flatten_spec (chunks := [[0,1,2,3,4,5,6,7,8], [9,10,11,12,13,14,15,16,17], [18,19,20,21,22,23,24,25,26], [27,28,29,30,31,32,33,34,35], [36,37,38,39,40,41,42,43,44], [45,46,47,48,49,50,51,52,53], [54,55,56,57,58,59,60,61,62], [63,64,65,66,67,68,69,70,71], [72,73,74,75,76,77,78,79,80], [81,82,83,84,85,86,87,88,89], [90,91,92,93,94,95]]) (gs := List.range (ngE 3))
      (fun j hj => by
        have hj' : j < 11 := by simpa using hj
        interval_cases j
        · exact clos_ok3_0
        · exact clos_ok3_1
        · exact clos_ok3_2
        · exact clos_ok3_3
        · exact clos_ok3_4
        · exact clos_ok3_5
        · exact clos_ok3_6
        · exact clos_ok3_7
        · exact clos_ok3_8
        · exact clos_ok3_9
        · exact clos_ok3_10
        )
      g (List.mem_range.mpr hg) s hs'
  have hidx : ∀ i < ([gl3_0, gl3_1, gl3_2, gl3_3, gl3_4, gl3_5, gl3_6].flatten).length, ∀ v ∈ ([gl3_0, gl3_1, gl3_2, gl3_3, gl3_4, gl3_5, gl3_6].flatten).getD i [],
      v % 4096 < (stabL 3).length := by
    intro i hi v hv
    have hmem : ([gl3_0, gl3_1, gl3_2, gl3_3, gl3_4, gl3_5, gl3_6].flatten).getD i [] ∈ ([gl3_0, gl3_1, gl3_2, gl3_3, gl3_4, gl3_5, gl3_6].flatten) := getD_mem hi
    have h := memIdxOK_flatten_spec (chunks := [gl3_0, gl3_1, gl3_2, gl3_3, gl3_4, gl3_5, gl3_6]) (ns := 96)
      (fun j hj => by
        have hj' : j < 7 := by simpa using hj
        interval_cases j
        · exact memidx_ok3_0
        · exact memidx_ok3_1
        · exact memidx_ok3_2
        · exact memidx_ok3_3
        · exact memidx_ok3_4
        · exact memidx_ok3_5
        · exact memidx_ok3_6
        ) _ hmem v hv
    rwa [hStabLen]
  exact genericGroups labT3 stabT3 grepT3 (stabL3) (sizes3) ([gl3_0, gl3_1, gl3_2, gl3_3, gl3_4, gl3_5, gl3_6].flatten) (ngE 3)
    hG hGsz hGlen hszlen hsum hrep hstab hclos hidx

theorem row4 :
    (∀ z ∈ eAll, labE 4 z < ngE 4 ∧ ∃ i < (stabL 4).length,
        actC cmT (stabTab 4 i) (grepE 4 (labE 4 z)) = z) ∧
    (∀ g < ngE 4, grepE 4 g ∈ eAll ∧ labE 4 (grepE 4 g) = g) ∧
    (∀ i < (stabL 4).length, ∀ g < ngE 4,
        labE 4 (actC cmT (stabTab 4 i) (grepE 4 g)) = g) ∧
    (∀ g < ngE 4, (eAll.filter (fun z => labE 4 z = g)).length = sizeE 4 g) ∧
    (sizesL.getD 4 []).length = ngE 4 := by
  have hs_ok : sumL sizes4 = 4641 ∧ sizes4.length = ngE 4 := by
    have h := sizes_ok4
    rw [Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    rw [Nat.beq_eq] at h1
    rw [decide_eq_true_eq, Nat.beq_eq] at h2
    exact ⟨h1, h2⟩
  have hszlen : sizes4.length = ngE 4 := hs_ok.2
  have hm0 : gl4_0.map List.length = gsz4_0 := (memGroupsOK_sound mem_ok4_0).1
  have hm1 : gl4_1.map List.length = gsz4_1 := (memGroupsOK_sound mem_ok4_1).1
  have hm2 : gl4_2.map List.length = gsz4_2 := (memGroupsOK_sound mem_ok4_2).1
  have hm3 : gl4_3.map List.length = gsz4_3 := (memGroupsOK_sound mem_ok4_3).1
  have hm4 : gl4_4.map List.length = gsz4_4 := (memGroupsOK_sound mem_ok4_4).1
  have hm5 : gl4_5.map List.length = gsz4_5 := (memGroupsOK_sound mem_ok4_5).1
  have hm6 : gl4_6.map List.length = gsz4_6 := (memGroupsOK_sound mem_ok4_6).1
  have hL0 : (gl4_0).length = 59 := by decide
  have hL1 : (gl4_1).length = 61 := by decide
  have hL2 : (gl4_2).length = 28 := by decide
  have hL3 : (gl4_3).length = 35 := by decide
  have hL4 : (gl4_4).length = 33 := by decide
  have hL5 : (gl4_5).length = 21 := by decide
  have hgsz : sizes4 = [gsz4_0, gsz4_1, gsz4_2, gsz4_3, gsz4_4, gsz4_5, gsz4_6].flatten := by
    rw [eqL_eq.mp gsz_ok4]
    rfl
  have hG : GroupsAt cmT eM labT4 stabT4 grepT4 [gl4_0, gl4_1, gl4_2, gl4_3, gl4_4, gl4_5, gl4_6].flatten 0 := by
    refine GroupsAt_cumul _ 0 ?_
    intro j hj
    have hj' : j < 7 := by simpa using hj
    interval_cases j
    · exact (memGroupsOK_sound mem_ok4_0).2
    · have ho : (cumul (0:ℕ) [gl4_0, gl4_1, gl4_2, gl4_3, gl4_4, gl4_5, gl4_6]).getD 1 0 = 59 := by
        show (0 + (gl4_0).length) = 59
        rw [hL0]
      rw [ho]; exact (memGroupsOK_sound mem_ok4_1).2
    · have ho : (cumul (0:ℕ) [gl4_0, gl4_1, gl4_2, gl4_3, gl4_4, gl4_5, gl4_6]).getD 2 0 = 120 := by
        show ((0 + (gl4_0).length) + (gl4_1).length) = 120
        rw [hL0, hL1]
      rw [ho]; exact (memGroupsOK_sound mem_ok4_2).2
    · have ho : (cumul (0:ℕ) [gl4_0, gl4_1, gl4_2, gl4_3, gl4_4, gl4_5, gl4_6]).getD 3 0 = 148 := by
        show (((0 + (gl4_0).length) + (gl4_1).length) + (gl4_2).length) = 148
        rw [hL0, hL1, hL2]
      rw [ho]; exact (memGroupsOK_sound mem_ok4_3).2
    · have ho : (cumul (0:ℕ) [gl4_0, gl4_1, gl4_2, gl4_3, gl4_4, gl4_5, gl4_6]).getD 4 0 = 183 := by
        show ((((0 + (gl4_0).length) + (gl4_1).length) + (gl4_2).length) + (gl4_3).length) = 183
        rw [hL0, hL1, hL2, hL3]
      rw [ho]; exact (memGroupsOK_sound mem_ok4_4).2
    · have ho : (cumul (0:ℕ) [gl4_0, gl4_1, gl4_2, gl4_3, gl4_4, gl4_5, gl4_6]).getD 5 0 = 216 := by
        show (((((0 + (gl4_0).length) + (gl4_1).length) + (gl4_2).length) + (gl4_3).length) + (gl4_4).length) = 216
        rw [hL0, hL1, hL2, hL3, hL4]
      rw [ho]; exact (memGroupsOK_sound mem_ok4_5).2
    · have ho : (cumul (0:ℕ) [gl4_0, gl4_1, gl4_2, gl4_3, gl4_4, gl4_5, gl4_6]).getD 6 0 = 237 := by
        show ((((((0 + (gl4_0).length) + (gl4_1).length) + (gl4_2).length) + (gl4_3).length) + (gl4_4).length) + (gl4_5).length) = 237
        rw [hL0, hL1, hL2, hL3, hL4, hL5]
      rw [ho]; exact (memGroupsOK_sound mem_ok4_6).2
  have hmap : ([gl4_0, gl4_1, gl4_2, gl4_3, gl4_4, gl4_5, gl4_6].map (fun l => l.map List.length)) = [gsz4_0, gsz4_1, gsz4_2, gsz4_3, gsz4_4, gsz4_5, gsz4_6] := by
    simp only [List.map_cons, List.map_nil, hm0, hm1, hm2, hm3, hm4, hm5, hm6]
  have hGsz : ([gl4_0, gl4_1, gl4_2, gl4_3, gl4_4, gl4_5, gl4_6].flatten).map List.length = sizes4 := by
    rw [hgsz, List.map_flatten, hmap]
  have hGlen : ([gl4_0, gl4_1, gl4_2, gl4_3, gl4_4, gl4_5, gl4_6].flatten).length = ngE 4 := by
    rw [show ([gl4_0, gl4_1, gl4_2, gl4_3, gl4_4, gl4_5, gl4_6].flatten).length = (([gl4_0, gl4_1, gl4_2, gl4_3, gl4_4, gl4_5, gl4_6].flatten).map List.length).length from
      (List.length_map List.length).symm, hGsz]
    exact hszlen
  have hsum : (([gl4_0, gl4_1, gl4_2, gl4_3, gl4_4, gl4_5, gl4_6].flatten).flatten).length = 4641 := by
    rw [List.length_flatten, hGsz, ← sumL_eq_sum]; exact hs_ok.1
  have hrep : ∀ g < ngE 4, cG grepT4 g ∈ eAll ∧ lG labT4 (cG grepT4 g) = g := by
    intro g hg
    have h := grepOK_sound grep_ok4 g hg
    exact ⟨Work.PTCert.NSemAux.mem_eAll_of_em_ne_zero h.1 h.2.1, h.2.2⟩
  have hStabLen : (stabL 4).length = 96 := by
    have h := stablen_ok4
    rw [Nat.beq_eq] at h
    exact h
  have hstab : ∀ s < (stabL 4).length, ∀ k < 81, lk (stabT4.get s) k < 81 := by
    intro s hs k hk
    obtain ⟨pc, sc, hpc, htab⟩ := tabsOK_sound stabtab_ok4 s hs
    rw [htab k hk]
    exact Work.PTCert.codeFactsAux.actLBound pc sc hpc k hk
  have hssrange : [[0,1,2,3,4,5,6,7], [8,9,10,11,12,13,14,15], [16,17,18,19,20,21,22,23], [24,25,26,27,28,29,30,31], [32,33,34,35,36,37,38,39], [40,41,42,43,44,45,46,47], [48,49,50,51,52,53,54,55], [56,57,58,59,60,61,62,63], [64,65,66,67,68,69,70,71], [72,73,74,75,76,77,78,79], [80,81,82,83,84,85,86,87], [88,89,90,91,92,93,94,95]].flatten = List.range 96 := by decide
  have hclos : ∀ s < (stabL 4).length, ∀ g < ngE 4,
      lG labT4 (actC cmT (stabT4.get s) (cG grepT4 g)) = g := by
    intro s hs g hg
    have hs' : s ∈ [[0,1,2,3,4,5,6,7], [8,9,10,11,12,13,14,15], [16,17,18,19,20,21,22,23], [24,25,26,27,28,29,30,31], [32,33,34,35,36,37,38,39], [40,41,42,43,44,45,46,47], [48,49,50,51,52,53,54,55], [56,57,58,59,60,61,62,63], [64,65,66,67,68,69,70,71], [72,73,74,75,76,77,78,79], [80,81,82,83,84,85,86,87], [88,89,90,91,92,93,94,95]].flatten := by
      rw [hssrange, List.mem_range]; rwa [hStabLen] at hs
    exact closOK_flatten_spec (chunks := [[0,1,2,3,4,5,6,7], [8,9,10,11,12,13,14,15], [16,17,18,19,20,21,22,23], [24,25,26,27,28,29,30,31], [32,33,34,35,36,37,38,39], [40,41,42,43,44,45,46,47], [48,49,50,51,52,53,54,55], [56,57,58,59,60,61,62,63], [64,65,66,67,68,69,70,71], [72,73,74,75,76,77,78,79], [80,81,82,83,84,85,86,87], [88,89,90,91,92,93,94,95]]) (gs := List.range (ngE 4))
      (fun j hj => by
        have hj' : j < 12 := by simpa using hj
        interval_cases j
        · exact clos_ok4_0
        · exact clos_ok4_1
        · exact clos_ok4_2
        · exact clos_ok4_3
        · exact clos_ok4_4
        · exact clos_ok4_5
        · exact clos_ok4_6
        · exact clos_ok4_7
        · exact clos_ok4_8
        · exact clos_ok4_9
        · exact clos_ok4_10
        · exact clos_ok4_11
        )
      g (List.mem_range.mpr hg) s hs'
  have hidx : ∀ i < ([gl4_0, gl4_1, gl4_2, gl4_3, gl4_4, gl4_5, gl4_6].flatten).length, ∀ v ∈ ([gl4_0, gl4_1, gl4_2, gl4_3, gl4_4, gl4_5, gl4_6].flatten).getD i [],
      v % 4096 < (stabL 4).length := by
    intro i hi v hv
    have hmem : ([gl4_0, gl4_1, gl4_2, gl4_3, gl4_4, gl4_5, gl4_6].flatten).getD i [] ∈ ([gl4_0, gl4_1, gl4_2, gl4_3, gl4_4, gl4_5, gl4_6].flatten) := getD_mem hi
    have h := memIdxOK_flatten_spec (chunks := [gl4_0, gl4_1, gl4_2, gl4_3, gl4_4, gl4_5, gl4_6]) (ns := 96)
      (fun j hj => by
        have hj' : j < 7 := by simpa using hj
        interval_cases j
        · exact memidx_ok4_0
        · exact memidx_ok4_1
        · exact memidx_ok4_2
        · exact memidx_ok4_3
        · exact memidx_ok4_4
        · exact memidx_ok4_5
        · exact memidx_ok4_6
        ) _ hmem v hv
    rwa [hStabLen]
  exact genericGroups labT4 stabT4 grepT4 (stabL4) (sizes4) ([gl4_0, gl4_1, gl4_2, gl4_3, gl4_4, gl4_5, gl4_6].flatten) (ngE 4)
    hG hGsz hGlen hszlen hsum hrep hstab hclos hidx

theorem row5 :
    (∀ z ∈ eAll, labE 5 z < ngE 5 ∧ ∃ i < (stabL 5).length,
        actC cmT (stabTab 5 i) (grepE 5 (labE 5 z)) = z) ∧
    (∀ g < ngE 5, grepE 5 g ∈ eAll ∧ labE 5 (grepE 5 g) = g) ∧
    (∀ i < (stabL 5).length, ∀ g < ngE 5,
        labE 5 (actC cmT (stabTab 5 i) (grepE 5 g)) = g) ∧
    (∀ g < ngE 5, (eAll.filter (fun z => labE 5 z = g)).length = sizeE 5 g) ∧
    (sizesL.getD 5 []).length = ngE 5 := by
  have hs_ok : sumL sizes5 = 4641 ∧ sizes5.length = ngE 5 := by
    have h := sizes_ok5
    rw [Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    rw [Nat.beq_eq] at h1
    rw [decide_eq_true_eq, Nat.beq_eq] at h2
    exact ⟨h1, h2⟩
  have hszlen : sizes5.length = ngE 5 := hs_ok.2
  have hm0 : gl5_0.map List.length = gsz5_0 := (memGroupsOK_sound mem_ok5_0).1
  have hm1 : gl5_1.map List.length = gsz5_1 := (memGroupsOK_sound mem_ok5_1).1
  have hm2 : gl5_2.map List.length = gsz5_2 := (memGroupsOK_sound mem_ok5_2).1
  have hm3 : gl5_3.map List.length = gsz5_3 := (memGroupsOK_sound mem_ok5_3).1
  have hm4 : gl5_4.map List.length = gsz5_4 := (memGroupsOK_sound mem_ok5_4).1
  have hm5 : gl5_5.map List.length = gsz5_5 := (memGroupsOK_sound mem_ok5_5).1
  have hm6 : gl5_6.map List.length = gsz5_6 := (memGroupsOK_sound mem_ok5_6).1
  have hL0 : (gl5_0).length = 233 := by decide
  have hL1 : (gl5_1).length = 255 := by decide
  have hL2 : (gl5_2).length = 187 := by decide
  have hL3 : (gl5_3).length = 219 := by decide
  have hL4 : (gl5_4).length = 208 := by decide
  have hL5 : (gl5_5).length = 126 := by decide
  have hgsz : sizes5 = [gsz5_0, gsz5_1, gsz5_2, gsz5_3, gsz5_4, gsz5_5, gsz5_6].flatten := by
    rw [eqL_eq.mp gsz_ok5]
    rfl
  have hG : GroupsAt cmT eM labT5 stabT5 grepT5 [gl5_0, gl5_1, gl5_2, gl5_3, gl5_4, gl5_5, gl5_6].flatten 0 := by
    refine GroupsAt_cumul _ 0 ?_
    intro j hj
    have hj' : j < 7 := by simpa using hj
    interval_cases j
    · exact (memGroupsOK_sound mem_ok5_0).2
    · have ho : (cumul (0:ℕ) [gl5_0, gl5_1, gl5_2, gl5_3, gl5_4, gl5_5, gl5_6]).getD 1 0 = 233 := by
        show (0 + (gl5_0).length) = 233
        rw [hL0]
      rw [ho]; exact (memGroupsOK_sound mem_ok5_1).2
    · have ho : (cumul (0:ℕ) [gl5_0, gl5_1, gl5_2, gl5_3, gl5_4, gl5_5, gl5_6]).getD 2 0 = 488 := by
        show ((0 + (gl5_0).length) + (gl5_1).length) = 488
        rw [hL0, hL1]
      rw [ho]; exact (memGroupsOK_sound mem_ok5_2).2
    · have ho : (cumul (0:ℕ) [gl5_0, gl5_1, gl5_2, gl5_3, gl5_4, gl5_5, gl5_6]).getD 3 0 = 675 := by
        show (((0 + (gl5_0).length) + (gl5_1).length) + (gl5_2).length) = 675
        rw [hL0, hL1, hL2]
      rw [ho]; exact (memGroupsOK_sound mem_ok5_3).2
    · have ho : (cumul (0:ℕ) [gl5_0, gl5_1, gl5_2, gl5_3, gl5_4, gl5_5, gl5_6]).getD 4 0 = 894 := by
        show ((((0 + (gl5_0).length) + (gl5_1).length) + (gl5_2).length) + (gl5_3).length) = 894
        rw [hL0, hL1, hL2, hL3]
      rw [ho]; exact (memGroupsOK_sound mem_ok5_4).2
    · have ho : (cumul (0:ℕ) [gl5_0, gl5_1, gl5_2, gl5_3, gl5_4, gl5_5, gl5_6]).getD 5 0 = 1102 := by
        show (((((0 + (gl5_0).length) + (gl5_1).length) + (gl5_2).length) + (gl5_3).length) + (gl5_4).length) = 1102
        rw [hL0, hL1, hL2, hL3, hL4]
      rw [ho]; exact (memGroupsOK_sound mem_ok5_5).2
    · have ho : (cumul (0:ℕ) [gl5_0, gl5_1, gl5_2, gl5_3, gl5_4, gl5_5, gl5_6]).getD 6 0 = 1228 := by
        show ((((((0 + (gl5_0).length) + (gl5_1).length) + (gl5_2).length) + (gl5_3).length) + (gl5_4).length) + (gl5_5).length) = 1228
        rw [hL0, hL1, hL2, hL3, hL4, hL5]
      rw [ho]; exact (memGroupsOK_sound mem_ok5_6).2
  have hmap : ([gl5_0, gl5_1, gl5_2, gl5_3, gl5_4, gl5_5, gl5_6].map (fun l => l.map List.length)) = [gsz5_0, gsz5_1, gsz5_2, gsz5_3, gsz5_4, gsz5_5, gsz5_6] := by
    simp only [List.map_cons, List.map_nil, hm0, hm1, hm2, hm3, hm4, hm5, hm6]
  have hGsz : ([gl5_0, gl5_1, gl5_2, gl5_3, gl5_4, gl5_5, gl5_6].flatten).map List.length = sizes5 := by
    rw [hgsz, List.map_flatten, hmap]
  have hGlen : ([gl5_0, gl5_1, gl5_2, gl5_3, gl5_4, gl5_5, gl5_6].flatten).length = ngE 5 := by
    rw [show ([gl5_0, gl5_1, gl5_2, gl5_3, gl5_4, gl5_5, gl5_6].flatten).length = (([gl5_0, gl5_1, gl5_2, gl5_3, gl5_4, gl5_5, gl5_6].flatten).map List.length).length from
      (List.length_map List.length).symm, hGsz]
    exact hszlen
  have hsum : (([gl5_0, gl5_1, gl5_2, gl5_3, gl5_4, gl5_5, gl5_6].flatten).flatten).length = 4641 := by
    rw [List.length_flatten, hGsz, ← sumL_eq_sum]; exact hs_ok.1
  have hrep : ∀ g < ngE 5, cG grepT5 g ∈ eAll ∧ lG labT5 (cG grepT5 g) = g := by
    intro g hg
    have h := grepOK_sound grep_ok5 g hg
    exact ⟨Work.PTCert.NSemAux.mem_eAll_of_em_ne_zero h.1 h.2.1, h.2.2⟩
  have hStabLen : (stabL 5).length = 8 := by
    have h := stablen_ok5
    rw [Nat.beq_eq] at h
    exact h
  have hstab : ∀ s < (stabL 5).length, ∀ k < 81, lk (stabT5.get s) k < 81 := by
    intro s hs k hk
    obtain ⟨pc, sc, hpc, htab⟩ := tabsOK_sound stabtab_ok5 s hs
    rw [htab k hk]
    exact Work.PTCert.codeFactsAux.actLBound pc sc hpc k hk
  have hssrange : [[0], [1], [2], [3], [4], [5], [6], [7]].flatten = List.range 8 := by decide
  have hclos : ∀ s < (stabL 5).length, ∀ g < ngE 5,
      lG labT5 (actC cmT (stabT5.get s) (cG grepT5 g)) = g := by
    intro s hs g hg
    have hs' : s ∈ [[0], [1], [2], [3], [4], [5], [6], [7]].flatten := by
      rw [hssrange, List.mem_range]; rwa [hStabLen] at hs
    exact closOK_flatten_spec (chunks := [[0], [1], [2], [3], [4], [5], [6], [7]]) (gs := List.range (ngE 5))
      (fun j hj => by
        have hj' : j < 8 := by simpa using hj
        interval_cases j
        · exact clos_ok5_0
        · exact clos_ok5_1
        · exact clos_ok5_2
        · exact clos_ok5_3
        · exact clos_ok5_4
        · exact clos_ok5_5
        · exact clos_ok5_6
        · exact clos_ok5_7
        )
      g (List.mem_range.mpr hg) s hs'
  have hidx : ∀ i < ([gl5_0, gl5_1, gl5_2, gl5_3, gl5_4, gl5_5, gl5_6].flatten).length, ∀ v ∈ ([gl5_0, gl5_1, gl5_2, gl5_3, gl5_4, gl5_5, gl5_6].flatten).getD i [],
      v % 4096 < (stabL 5).length := by
    intro i hi v hv
    have hmem : ([gl5_0, gl5_1, gl5_2, gl5_3, gl5_4, gl5_5, gl5_6].flatten).getD i [] ∈ ([gl5_0, gl5_1, gl5_2, gl5_3, gl5_4, gl5_5, gl5_6].flatten) := getD_mem hi
    have h := memIdxOK_flatten_spec (chunks := [gl5_0, gl5_1, gl5_2, gl5_3, gl5_4, gl5_5, gl5_6]) (ns := 8)
      (fun j hj => by
        have hj' : j < 7 := by simpa using hj
        interval_cases j
        · exact memidx_ok5_0
        · exact memidx_ok5_1
        · exact memidx_ok5_2
        · exact memidx_ok5_3
        · exact memidx_ok5_4
        · exact memidx_ok5_5
        · exact memidx_ok5_6
        ) _ hmem v hv
    rwa [hStabLen]
  exact genericGroups labT5 stabT5 grepT5 (stabL5) (sizes5) ([gl5_0, gl5_1, gl5_2, gl5_3, gl5_4, gl5_5, gl5_6].flatten) (ngE 5)
    hG hGsz hGlen hszlen hsum hrep hstab hclos hidx

theorem row6 :
    (∀ z ∈ eAll, labE 6 z < ngE 6 ∧ ∃ i < (stabL 6).length,
        actC cmT (stabTab 6 i) (grepE 6 (labE 6 z)) = z) ∧
    (∀ g < ngE 6, grepE 6 g ∈ eAll ∧ labE 6 (grepE 6 g) = g) ∧
    (∀ i < (stabL 6).length, ∀ g < ngE 6,
        labE 6 (actC cmT (stabTab 6 i) (grepE 6 g)) = g) ∧
    (∀ g < ngE 6, (eAll.filter (fun z => labE 6 z = g)).length = sizeE 6 g) ∧
    (sizesL.getD 6 []).length = ngE 6 := by
  have hs_ok : sumL sizes6 = 4641 ∧ sizes6.length = ngE 6 := by
    have h := sizes_ok6
    rw [Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    rw [Nat.beq_eq] at h1
    rw [decide_eq_true_eq, Nat.beq_eq] at h2
    exact ⟨h1, h2⟩
  have hszlen : sizes6.length = ngE 6 := hs_ok.2
  have hm0 : gl6_0.map List.length = gsz6_0 := (memGroupsOK_sound mem_ok6_0).1
  have hm1 : gl6_1.map List.length = gsz6_1 := (memGroupsOK_sound mem_ok6_1).1
  have hm2 : gl6_2.map List.length = gsz6_2 := (memGroupsOK_sound mem_ok6_2).1
  have hm3 : gl6_3.map List.length = gsz6_3 := (memGroupsOK_sound mem_ok6_3).1
  have hm4 : gl6_4.map List.length = gsz6_4 := (memGroupsOK_sound mem_ok6_4).1
  have hm5 : gl6_5.map List.length = gsz6_5 := (memGroupsOK_sound mem_ok6_5).1
  have hm6 : gl6_6.map List.length = gsz6_6 := (memGroupsOK_sound mem_ok6_6).1
  have hL0 : (gl6_0).length = 120 := by decide
  have hL1 : (gl6_1).length = 133 := by decide
  have hL2 : (gl6_2).length = 93 := by decide
  have hL3 : (gl6_3).length = 110 := by decide
  have hL4 : (gl6_4).length = 104 := by decide
  have hL5 : (gl6_5).length = 68 := by decide
  have hgsz : sizes6 = [gsz6_0, gsz6_1, gsz6_2, gsz6_3, gsz6_4, gsz6_5, gsz6_6].flatten := by
    rw [eqL_eq.mp gsz_ok6]
    rfl
  have hG : GroupsAt cmT eM labT6 stabT6 grepT6 [gl6_0, gl6_1, gl6_2, gl6_3, gl6_4, gl6_5, gl6_6].flatten 0 := by
    refine GroupsAt_cumul _ 0 ?_
    intro j hj
    have hj' : j < 7 := by simpa using hj
    interval_cases j
    · exact (memGroupsOK_sound mem_ok6_0).2
    · have ho : (cumul (0:ℕ) [gl6_0, gl6_1, gl6_2, gl6_3, gl6_4, gl6_5, gl6_6]).getD 1 0 = 120 := by
        show (0 + (gl6_0).length) = 120
        rw [hL0]
      rw [ho]; exact (memGroupsOK_sound mem_ok6_1).2
    · have ho : (cumul (0:ℕ) [gl6_0, gl6_1, gl6_2, gl6_3, gl6_4, gl6_5, gl6_6]).getD 2 0 = 253 := by
        show ((0 + (gl6_0).length) + (gl6_1).length) = 253
        rw [hL0, hL1]
      rw [ho]; exact (memGroupsOK_sound mem_ok6_2).2
    · have ho : (cumul (0:ℕ) [gl6_0, gl6_1, gl6_2, gl6_3, gl6_4, gl6_5, gl6_6]).getD 3 0 = 346 := by
        show (((0 + (gl6_0).length) + (gl6_1).length) + (gl6_2).length) = 346
        rw [hL0, hL1, hL2]
      rw [ho]; exact (memGroupsOK_sound mem_ok6_3).2
    · have ho : (cumul (0:ℕ) [gl6_0, gl6_1, gl6_2, gl6_3, gl6_4, gl6_5, gl6_6]).getD 4 0 = 456 := by
        show ((((0 + (gl6_0).length) + (gl6_1).length) + (gl6_2).length) + (gl6_3).length) = 456
        rw [hL0, hL1, hL2, hL3]
      rw [ho]; exact (memGroupsOK_sound mem_ok6_4).2
    · have ho : (cumul (0:ℕ) [gl6_0, gl6_1, gl6_2, gl6_3, gl6_4, gl6_5, gl6_6]).getD 5 0 = 560 := by
        show (((((0 + (gl6_0).length) + (gl6_1).length) + (gl6_2).length) + (gl6_3).length) + (gl6_4).length) = 560
        rw [hL0, hL1, hL2, hL3, hL4]
      rw [ho]; exact (memGroupsOK_sound mem_ok6_5).2
    · have ho : (cumul (0:ℕ) [gl6_0, gl6_1, gl6_2, gl6_3, gl6_4, gl6_5, gl6_6]).getD 6 0 = 628 := by
        show ((((((0 + (gl6_0).length) + (gl6_1).length) + (gl6_2).length) + (gl6_3).length) + (gl6_4).length) + (gl6_5).length) = 628
        rw [hL0, hL1, hL2, hL3, hL4, hL5]
      rw [ho]; exact (memGroupsOK_sound mem_ok6_6).2
  have hmap : ([gl6_0, gl6_1, gl6_2, gl6_3, gl6_4, gl6_5, gl6_6].map (fun l => l.map List.length)) = [gsz6_0, gsz6_1, gsz6_2, gsz6_3, gsz6_4, gsz6_5, gsz6_6] := by
    simp only [List.map_cons, List.map_nil, hm0, hm1, hm2, hm3, hm4, hm5, hm6]
  have hGsz : ([gl6_0, gl6_1, gl6_2, gl6_3, gl6_4, gl6_5, gl6_6].flatten).map List.length = sizes6 := by
    rw [hgsz, List.map_flatten, hmap]
  have hGlen : ([gl6_0, gl6_1, gl6_2, gl6_3, gl6_4, gl6_5, gl6_6].flatten).length = ngE 6 := by
    rw [show ([gl6_0, gl6_1, gl6_2, gl6_3, gl6_4, gl6_5, gl6_6].flatten).length = (([gl6_0, gl6_1, gl6_2, gl6_3, gl6_4, gl6_5, gl6_6].flatten).map List.length).length from
      (List.length_map List.length).symm, hGsz]
    exact hszlen
  have hsum : (([gl6_0, gl6_1, gl6_2, gl6_3, gl6_4, gl6_5, gl6_6].flatten).flatten).length = 4641 := by
    rw [List.length_flatten, hGsz, ← sumL_eq_sum]; exact hs_ok.1
  have hrep : ∀ g < ngE 6, cG grepT6 g ∈ eAll ∧ lG labT6 (cG grepT6 g) = g := by
    intro g hg
    have h := grepOK_sound grep_ok6 g hg
    exact ⟨Work.PTCert.NSemAux.mem_eAll_of_em_ne_zero h.1 h.2.1, h.2.2⟩
  have hStabLen : (stabL 6).length = 16 := by
    have h := stablen_ok6
    rw [Nat.beq_eq] at h
    exact h
  have hstab : ∀ s < (stabL 6).length, ∀ k < 81, lk (stabT6.get s) k < 81 := by
    intro s hs k hk
    obtain ⟨pc, sc, hpc, htab⟩ := tabsOK_sound stabtab_ok6 s hs
    rw [htab k hk]
    exact Work.PTCert.codeFactsAux.actLBound pc sc hpc k hk
  have hssrange : [[0,1], [2,3], [4,5], [6,7], [8,9], [10,11], [12,13], [14,15]].flatten = List.range 16 := by decide
  have hclos : ∀ s < (stabL 6).length, ∀ g < ngE 6,
      lG labT6 (actC cmT (stabT6.get s) (cG grepT6 g)) = g := by
    intro s hs g hg
    have hs' : s ∈ [[0,1], [2,3], [4,5], [6,7], [8,9], [10,11], [12,13], [14,15]].flatten := by
      rw [hssrange, List.mem_range]; rwa [hStabLen] at hs
    exact closOK_flatten_spec (chunks := [[0,1], [2,3], [4,5], [6,7], [8,9], [10,11], [12,13], [14,15]]) (gs := List.range (ngE 6))
      (fun j hj => by
        have hj' : j < 8 := by simpa using hj
        interval_cases j
        · exact clos_ok6_0
        · exact clos_ok6_1
        · exact clos_ok6_2
        · exact clos_ok6_3
        · exact clos_ok6_4
        · exact clos_ok6_5
        · exact clos_ok6_6
        · exact clos_ok6_7
        )
      g (List.mem_range.mpr hg) s hs'
  have hidx : ∀ i < ([gl6_0, gl6_1, gl6_2, gl6_3, gl6_4, gl6_5, gl6_6].flatten).length, ∀ v ∈ ([gl6_0, gl6_1, gl6_2, gl6_3, gl6_4, gl6_5, gl6_6].flatten).getD i [],
      v % 4096 < (stabL 6).length := by
    intro i hi v hv
    have hmem : ([gl6_0, gl6_1, gl6_2, gl6_3, gl6_4, gl6_5, gl6_6].flatten).getD i [] ∈ ([gl6_0, gl6_1, gl6_2, gl6_3, gl6_4, gl6_5, gl6_6].flatten) := getD_mem hi
    have h := memIdxOK_flatten_spec (chunks := [gl6_0, gl6_1, gl6_2, gl6_3, gl6_4, gl6_5, gl6_6]) (ns := 16)
      (fun j hj => by
        have hj' : j < 7 := by simpa using hj
        interval_cases j
        · exact memidx_ok6_0
        · exact memidx_ok6_1
        · exact memidx_ok6_2
        · exact memidx_ok6_3
        · exact memidx_ok6_4
        · exact memidx_ok6_5
        · exact memidx_ok6_6
        ) _ hmem v hv
    rwa [hStabLen]
  exact genericGroups labT6 stabT6 grepT6 (stabL6) (sizes6) ([gl6_0, gl6_1, gl6_2, gl6_3, gl6_4, gl6_5, gl6_6].flatten) (ngE 6)
    hG hGsz hGlen hszlen hsum hrep hstab hclos hidx

theorem row7 :
    (∀ z ∈ eAll, labE 7 z < ngE 7 ∧ ∃ i < (stabL 7).length,
        actC cmT (stabTab 7 i) (grepE 7 (labE 7 z)) = z) ∧
    (∀ g < ngE 7, grepE 7 g ∈ eAll ∧ labE 7 (grepE 7 g) = g) ∧
    (∀ i < (stabL 7).length, ∀ g < ngE 7,
        labE 7 (actC cmT (stabTab 7 i) (grepE 7 g)) = g) ∧
    (∀ g < ngE 7, (eAll.filter (fun z => labE 7 z = g)).length = sizeE 7 g) ∧
    (sizesL.getD 7 []).length = ngE 7 := by
  have hs_ok : sumL sizes7 = 4641 ∧ sizes7.length = ngE 7 := by
    have h := sizes_ok7
    rw [Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    rw [Nat.beq_eq] at h1
    rw [decide_eq_true_eq, Nat.beq_eq] at h2
    exact ⟨h1, h2⟩
  have hszlen : sizes7.length = ngE 7 := hs_ok.2
  have hm0 : gl7_0.map List.length = gsz7_0 := (memGroupsOK_sound mem_ok7_0).1
  have hm1 : gl7_1.map List.length = gsz7_1 := (memGroupsOK_sound mem_ok7_1).1
  have hm2 : gl7_2.map List.length = gsz7_2 := (memGroupsOK_sound mem_ok7_2).1
  have hm3 : gl7_3.map List.length = gsz7_3 := (memGroupsOK_sound mem_ok7_3).1
  have hm4 : gl7_4.map List.length = gsz7_4 := (memGroupsOK_sound mem_ok7_4).1
  have hm5 : gl7_5.map List.length = gsz7_5 := (memGroupsOK_sound mem_ok7_5).1
  have hm6 : gl7_6.map List.length = gsz7_6 := (memGroupsOK_sound mem_ok7_6).1
  have hL0 : (gl7_0).length = 88 := by decide
  have hL1 : (gl7_1).length = 94 := by decide
  have hL2 : (gl7_2).length = 46 := by decide
  have hL3 : (gl7_3).length = 63 := by decide
  have hL4 : (gl7_4).length = 58 := by decide
  have hL5 : (gl7_5).length = 30 := by decide
  have hgsz : sizes7 = [gsz7_0, gsz7_1, gsz7_2, gsz7_3, gsz7_4, gsz7_5, gsz7_6].flatten := by
    rw [eqL_eq.mp gsz_ok7]
    rfl
  have hG : GroupsAt cmT eM labT7 stabT7 grepT7 [gl7_0, gl7_1, gl7_2, gl7_3, gl7_4, gl7_5, gl7_6].flatten 0 := by
    refine GroupsAt_cumul _ 0 ?_
    intro j hj
    have hj' : j < 7 := by simpa using hj
    interval_cases j
    · exact (memGroupsOK_sound mem_ok7_0).2
    · have ho : (cumul (0:ℕ) [gl7_0, gl7_1, gl7_2, gl7_3, gl7_4, gl7_5, gl7_6]).getD 1 0 = 88 := by
        show (0 + (gl7_0).length) = 88
        rw [hL0]
      rw [ho]; exact (memGroupsOK_sound mem_ok7_1).2
    · have ho : (cumul (0:ℕ) [gl7_0, gl7_1, gl7_2, gl7_3, gl7_4, gl7_5, gl7_6]).getD 2 0 = 182 := by
        show ((0 + (gl7_0).length) + (gl7_1).length) = 182
        rw [hL0, hL1]
      rw [ho]; exact (memGroupsOK_sound mem_ok7_2).2
    · have ho : (cumul (0:ℕ) [gl7_0, gl7_1, gl7_2, gl7_3, gl7_4, gl7_5, gl7_6]).getD 3 0 = 228 := by
        show (((0 + (gl7_0).length) + (gl7_1).length) + (gl7_2).length) = 228
        rw [hL0, hL1, hL2]
      rw [ho]; exact (memGroupsOK_sound mem_ok7_3).2
    · have ho : (cumul (0:ℕ) [gl7_0, gl7_1, gl7_2, gl7_3, gl7_4, gl7_5, gl7_6]).getD 4 0 = 291 := by
        show ((((0 + (gl7_0).length) + (gl7_1).length) + (gl7_2).length) + (gl7_3).length) = 291
        rw [hL0, hL1, hL2, hL3]
      rw [ho]; exact (memGroupsOK_sound mem_ok7_4).2
    · have ho : (cumul (0:ℕ) [gl7_0, gl7_1, gl7_2, gl7_3, gl7_4, gl7_5, gl7_6]).getD 5 0 = 349 := by
        show (((((0 + (gl7_0).length) + (gl7_1).length) + (gl7_2).length) + (gl7_3).length) + (gl7_4).length) = 349
        rw [hL0, hL1, hL2, hL3, hL4]
      rw [ho]; exact (memGroupsOK_sound mem_ok7_5).2
    · have ho : (cumul (0:ℕ) [gl7_0, gl7_1, gl7_2, gl7_3, gl7_4, gl7_5, gl7_6]).getD 6 0 = 379 := by
        show ((((((0 + (gl7_0).length) + (gl7_1).length) + (gl7_2).length) + (gl7_3).length) + (gl7_4).length) + (gl7_5).length) = 379
        rw [hL0, hL1, hL2, hL3, hL4, hL5]
      rw [ho]; exact (memGroupsOK_sound mem_ok7_6).2
  have hmap : ([gl7_0, gl7_1, gl7_2, gl7_3, gl7_4, gl7_5, gl7_6].map (fun l => l.map List.length)) = [gsz7_0, gsz7_1, gsz7_2, gsz7_3, gsz7_4, gsz7_5, gsz7_6] := by
    simp only [List.map_cons, List.map_nil, hm0, hm1, hm2, hm3, hm4, hm5, hm6]
  have hGsz : ([gl7_0, gl7_1, gl7_2, gl7_3, gl7_4, gl7_5, gl7_6].flatten).map List.length = sizes7 := by
    rw [hgsz, List.map_flatten, hmap]
  have hGlen : ([gl7_0, gl7_1, gl7_2, gl7_3, gl7_4, gl7_5, gl7_6].flatten).length = ngE 7 := by
    rw [show ([gl7_0, gl7_1, gl7_2, gl7_3, gl7_4, gl7_5, gl7_6].flatten).length = (([gl7_0, gl7_1, gl7_2, gl7_3, gl7_4, gl7_5, gl7_6].flatten).map List.length).length from
      (List.length_map List.length).symm, hGsz]
    exact hszlen
  have hsum : (([gl7_0, gl7_1, gl7_2, gl7_3, gl7_4, gl7_5, gl7_6].flatten).flatten).length = 4641 := by
    rw [List.length_flatten, hGsz, ← sumL_eq_sum]; exact hs_ok.1
  have hrep : ∀ g < ngE 7, cG grepT7 g ∈ eAll ∧ lG labT7 (cG grepT7 g) = g := by
    intro g hg
    have h := grepOK_sound grep_ok7 g hg
    exact ⟨Work.PTCert.NSemAux.mem_eAll_of_em_ne_zero h.1 h.2.1, h.2.2⟩
  have hStabLen : (stabL 7).length = 48 := by
    have h := stablen_ok7
    rw [Nat.beq_eq] at h
    exact h
  have hstab : ∀ s < (stabL 7).length, ∀ k < 81, lk (stabT7.get s) k < 81 := by
    intro s hs k hk
    obtain ⟨pc, sc, hpc, htab⟩ := tabsOK_sound stabtab_ok7 s hs
    rw [htab k hk]
    exact Work.PTCert.codeFactsAux.actLBound pc sc hpc k hk
  have hssrange : [[0,1,2,3,4], [5,6,7,8,9], [10,11,12,13,14], [15,16,17,18,19], [20,21,22,23,24], [25,26,27,28,29], [30,31,32,33,34], [35,36,37,38,39], [40,41,42,43,44], [45,46,47]].flatten = List.range 48 := by decide
  have hclos : ∀ s < (stabL 7).length, ∀ g < ngE 7,
      lG labT7 (actC cmT (stabT7.get s) (cG grepT7 g)) = g := by
    intro s hs g hg
    have hs' : s ∈ [[0,1,2,3,4], [5,6,7,8,9], [10,11,12,13,14], [15,16,17,18,19], [20,21,22,23,24], [25,26,27,28,29], [30,31,32,33,34], [35,36,37,38,39], [40,41,42,43,44], [45,46,47]].flatten := by
      rw [hssrange, List.mem_range]; rwa [hStabLen] at hs
    exact closOK_flatten_spec (chunks := [[0,1,2,3,4], [5,6,7,8,9], [10,11,12,13,14], [15,16,17,18,19], [20,21,22,23,24], [25,26,27,28,29], [30,31,32,33,34], [35,36,37,38,39], [40,41,42,43,44], [45,46,47]]) (gs := List.range (ngE 7))
      (fun j hj => by
        have hj' : j < 10 := by simpa using hj
        interval_cases j
        · exact clos_ok7_0
        · exact clos_ok7_1
        · exact clos_ok7_2
        · exact clos_ok7_3
        · exact clos_ok7_4
        · exact clos_ok7_5
        · exact clos_ok7_6
        · exact clos_ok7_7
        · exact clos_ok7_8
        · exact clos_ok7_9
        )
      g (List.mem_range.mpr hg) s hs'
  have hidx : ∀ i < ([gl7_0, gl7_1, gl7_2, gl7_3, gl7_4, gl7_5, gl7_6].flatten).length, ∀ v ∈ ([gl7_0, gl7_1, gl7_2, gl7_3, gl7_4, gl7_5, gl7_6].flatten).getD i [],
      v % 4096 < (stabL 7).length := by
    intro i hi v hv
    have hmem : ([gl7_0, gl7_1, gl7_2, gl7_3, gl7_4, gl7_5, gl7_6].flatten).getD i [] ∈ ([gl7_0, gl7_1, gl7_2, gl7_3, gl7_4, gl7_5, gl7_6].flatten) := getD_mem hi
    have h := memIdxOK_flatten_spec (chunks := [gl7_0, gl7_1, gl7_2, gl7_3, gl7_4, gl7_5, gl7_6]) (ns := 48)
      (fun j hj => by
        have hj' : j < 7 := by simpa using hj
        interval_cases j
        · exact memidx_ok7_0
        · exact memidx_ok7_1
        · exact memidx_ok7_2
        · exact memidx_ok7_3
        · exact memidx_ok7_4
        · exact memidx_ok7_5
        · exact memidx_ok7_6
        ) _ hmem v hv
    rwa [hStabLen]
  exact genericGroups labT7 stabT7 grepT7 (stabL7) (sizes7) ([gl7_0, gl7_1, gl7_2, gl7_3, gl7_4, gl7_5, gl7_6].flatten) (ngE 7)
    hG hGsz hGlen hszlen hsum hrep hstab hclos hidx

theorem row8 :
    (∀ z ∈ eAll, labE 8 z < ngE 8 ∧ ∃ i < (stabL 8).length,
        actC cmT (stabTab 8 i) (grepE 8 (labE 8 z)) = z) ∧
    (∀ g < ngE 8, grepE 8 g ∈ eAll ∧ labE 8 (grepE 8 g) = g) ∧
    (∀ i < (stabL 8).length, ∀ g < ngE 8,
        labE 8 (actC cmT (stabTab 8 i) (grepE 8 g)) = g) ∧
    (∀ g < ngE 8, (eAll.filter (fun z => labE 8 z = g)).length = sizeE 8 g) ∧
    (sizesL.getD 8 []).length = ngE 8 := by
  have hs_ok : sumL sizes8 = 4641 ∧ sizes8.length = ngE 8 := by
    have h := sizes_ok8
    rw [Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    rw [Nat.beq_eq] at h1
    rw [decide_eq_true_eq, Nat.beq_eq] at h2
    exact ⟨h1, h2⟩
  have hszlen : sizes8.length = ngE 8 := hs_ok.2
  have hm0 : gl8_0.map List.length = gsz8_0 := (memGroupsOK_sound mem_ok8_0).1
  have hm1 : gl8_1.map List.length = gsz8_1 := (memGroupsOK_sound mem_ok8_1).1
  have hm2 : gl8_2.map List.length = gsz8_2 := (memGroupsOK_sound mem_ok8_2).1
  have hm3 : gl8_3.map List.length = gsz8_3 := (memGroupsOK_sound mem_ok8_3).1
  have hm4 : gl8_4.map List.length = gsz8_4 := (memGroupsOK_sound mem_ok8_4).1
  have hm5 : gl8_5.map List.length = gsz8_5 := (memGroupsOK_sound mem_ok8_5).1
  have hm6 : gl8_6.map List.length = gsz8_6 := (memGroupsOK_sound mem_ok8_6).1
  have hL0 : (gl8_0).length = 88 := by decide
  have hL1 : (gl8_1).length = 94 := by decide
  have hL2 : (gl8_2).length = 46 := by decide
  have hL3 : (gl8_3).length = 63 := by decide
  have hL4 : (gl8_4).length = 58 := by decide
  have hL5 : (gl8_5).length = 30 := by decide
  have hgsz : sizes8 = [gsz8_0, gsz8_1, gsz8_2, gsz8_3, gsz8_4, gsz8_5, gsz8_6].flatten := by
    rw [eqL_eq.mp gsz_ok8]
    rfl
  have hG : GroupsAt cmT eM labT8 stabT8 grepT8 [gl8_0, gl8_1, gl8_2, gl8_3, gl8_4, gl8_5, gl8_6].flatten 0 := by
    refine GroupsAt_cumul _ 0 ?_
    intro j hj
    have hj' : j < 7 := by simpa using hj
    interval_cases j
    · exact (memGroupsOK_sound mem_ok8_0).2
    · have ho : (cumul (0:ℕ) [gl8_0, gl8_1, gl8_2, gl8_3, gl8_4, gl8_5, gl8_6]).getD 1 0 = 88 := by
        show (0 + (gl8_0).length) = 88
        rw [hL0]
      rw [ho]; exact (memGroupsOK_sound mem_ok8_1).2
    · have ho : (cumul (0:ℕ) [gl8_0, gl8_1, gl8_2, gl8_3, gl8_4, gl8_5, gl8_6]).getD 2 0 = 182 := by
        show ((0 + (gl8_0).length) + (gl8_1).length) = 182
        rw [hL0, hL1]
      rw [ho]; exact (memGroupsOK_sound mem_ok8_2).2
    · have ho : (cumul (0:ℕ) [gl8_0, gl8_1, gl8_2, gl8_3, gl8_4, gl8_5, gl8_6]).getD 3 0 = 228 := by
        show (((0 + (gl8_0).length) + (gl8_1).length) + (gl8_2).length) = 228
        rw [hL0, hL1, hL2]
      rw [ho]; exact (memGroupsOK_sound mem_ok8_3).2
    · have ho : (cumul (0:ℕ) [gl8_0, gl8_1, gl8_2, gl8_3, gl8_4, gl8_5, gl8_6]).getD 4 0 = 291 := by
        show ((((0 + (gl8_0).length) + (gl8_1).length) + (gl8_2).length) + (gl8_3).length) = 291
        rw [hL0, hL1, hL2, hL3]
      rw [ho]; exact (memGroupsOK_sound mem_ok8_4).2
    · have ho : (cumul (0:ℕ) [gl8_0, gl8_1, gl8_2, gl8_3, gl8_4, gl8_5, gl8_6]).getD 5 0 = 349 := by
        show (((((0 + (gl8_0).length) + (gl8_1).length) + (gl8_2).length) + (gl8_3).length) + (gl8_4).length) = 349
        rw [hL0, hL1, hL2, hL3, hL4]
      rw [ho]; exact (memGroupsOK_sound mem_ok8_5).2
    · have ho : (cumul (0:ℕ) [gl8_0, gl8_1, gl8_2, gl8_3, gl8_4, gl8_5, gl8_6]).getD 6 0 = 379 := by
        show ((((((0 + (gl8_0).length) + (gl8_1).length) + (gl8_2).length) + (gl8_3).length) + (gl8_4).length) + (gl8_5).length) = 379
        rw [hL0, hL1, hL2, hL3, hL4, hL5]
      rw [ho]; exact (memGroupsOK_sound mem_ok8_6).2
  have hmap : ([gl8_0, gl8_1, gl8_2, gl8_3, gl8_4, gl8_5, gl8_6].map (fun l => l.map List.length)) = [gsz8_0, gsz8_1, gsz8_2, gsz8_3, gsz8_4, gsz8_5, gsz8_6] := by
    simp only [List.map_cons, List.map_nil, hm0, hm1, hm2, hm3, hm4, hm5, hm6]
  have hGsz : ([gl8_0, gl8_1, gl8_2, gl8_3, gl8_4, gl8_5, gl8_6].flatten).map List.length = sizes8 := by
    rw [hgsz, List.map_flatten, hmap]
  have hGlen : ([gl8_0, gl8_1, gl8_2, gl8_3, gl8_4, gl8_5, gl8_6].flatten).length = ngE 8 := by
    rw [show ([gl8_0, gl8_1, gl8_2, gl8_3, gl8_4, gl8_5, gl8_6].flatten).length = (([gl8_0, gl8_1, gl8_2, gl8_3, gl8_4, gl8_5, gl8_6].flatten).map List.length).length from
      (List.length_map List.length).symm, hGsz]
    exact hszlen
  have hsum : (([gl8_0, gl8_1, gl8_2, gl8_3, gl8_4, gl8_5, gl8_6].flatten).flatten).length = 4641 := by
    rw [List.length_flatten, hGsz, ← sumL_eq_sum]; exact hs_ok.1
  have hrep : ∀ g < ngE 8, cG grepT8 g ∈ eAll ∧ lG labT8 (cG grepT8 g) = g := by
    intro g hg
    have h := grepOK_sound grep_ok8 g hg
    exact ⟨Work.PTCert.NSemAux.mem_eAll_of_em_ne_zero h.1 h.2.1, h.2.2⟩
  have hStabLen : (stabL 8).length = 48 := by
    have h := stablen_ok8
    rw [Nat.beq_eq] at h
    exact h
  have hstab : ∀ s < (stabL 8).length, ∀ k < 81, lk (stabT8.get s) k < 81 := by
    intro s hs k hk
    obtain ⟨pc, sc, hpc, htab⟩ := tabsOK_sound stabtab_ok8 s hs
    rw [htab k hk]
    exact Work.PTCert.codeFactsAux.actLBound pc sc hpc k hk
  have hssrange : [[0,1,2,3,4], [5,6,7,8,9], [10,11,12,13,14], [15,16,17,18,19], [20,21,22,23,24], [25,26,27,28,29], [30,31,32,33,34], [35,36,37,38,39], [40,41,42,43,44], [45,46,47]].flatten = List.range 48 := by decide
  have hclos : ∀ s < (stabL 8).length, ∀ g < ngE 8,
      lG labT8 (actC cmT (stabT8.get s) (cG grepT8 g)) = g := by
    intro s hs g hg
    have hs' : s ∈ [[0,1,2,3,4], [5,6,7,8,9], [10,11,12,13,14], [15,16,17,18,19], [20,21,22,23,24], [25,26,27,28,29], [30,31,32,33,34], [35,36,37,38,39], [40,41,42,43,44], [45,46,47]].flatten := by
      rw [hssrange, List.mem_range]; rwa [hStabLen] at hs
    exact closOK_flatten_spec (chunks := [[0,1,2,3,4], [5,6,7,8,9], [10,11,12,13,14], [15,16,17,18,19], [20,21,22,23,24], [25,26,27,28,29], [30,31,32,33,34], [35,36,37,38,39], [40,41,42,43,44], [45,46,47]]) (gs := List.range (ngE 8))
      (fun j hj => by
        have hj' : j < 10 := by simpa using hj
        interval_cases j
        · exact clos_ok8_0
        · exact clos_ok8_1
        · exact clos_ok8_2
        · exact clos_ok8_3
        · exact clos_ok8_4
        · exact clos_ok8_5
        · exact clos_ok8_6
        · exact clos_ok8_7
        · exact clos_ok8_8
        · exact clos_ok8_9
        )
      g (List.mem_range.mpr hg) s hs'
  have hidx : ∀ i < ([gl8_0, gl8_1, gl8_2, gl8_3, gl8_4, gl8_5, gl8_6].flatten).length, ∀ v ∈ ([gl8_0, gl8_1, gl8_2, gl8_3, gl8_4, gl8_5, gl8_6].flatten).getD i [],
      v % 4096 < (stabL 8).length := by
    intro i hi v hv
    have hmem : ([gl8_0, gl8_1, gl8_2, gl8_3, gl8_4, gl8_5, gl8_6].flatten).getD i [] ∈ ([gl8_0, gl8_1, gl8_2, gl8_3, gl8_4, gl8_5, gl8_6].flatten) := getD_mem hi
    have h := memIdxOK_flatten_spec (chunks := [gl8_0, gl8_1, gl8_2, gl8_3, gl8_4, gl8_5, gl8_6]) (ns := 48)
      (fun j hj => by
        have hj' : j < 7 := by simpa using hj
        interval_cases j
        · exact memidx_ok8_0
        · exact memidx_ok8_1
        · exact memidx_ok8_2
        · exact memidx_ok8_3
        · exact memidx_ok8_4
        · exact memidx_ok8_5
        · exact memidx_ok8_6
        ) _ hmem v hv
    rwa [hStabLen]
  exact genericGroups labT8 stabT8 grepT8 (stabL8) (sizes8) ([gl8_0, gl8_1, gl8_2, gl8_3, gl8_4, gl8_5, gl8_6].flatten) (ngE 8)
    hG hGsz hGlen hszlen hsum hrep hstab hclos hidx

theorem row9 :
    (∀ z ∈ eAll, labE 9 z < ngE 9 ∧ ∃ i < (stabL 9).length,
        actC cmT (stabTab 9 i) (grepE 9 (labE 9 z)) = z) ∧
    (∀ g < ngE 9, grepE 9 g ∈ eAll ∧ labE 9 (grepE 9 g) = g) ∧
    (∀ i < (stabL 9).length, ∀ g < ngE 9,
        labE 9 (actC cmT (stabTab 9 i) (grepE 9 g)) = g) ∧
    (∀ g < ngE 9, (eAll.filter (fun z => labE 9 z = g)).length = sizeE 9 g) ∧
    (sizesL.getD 9 []).length = ngE 9 := by
  have hs_ok : sumL sizes9 = 4641 ∧ sizes9.length = ngE 9 := by
    have h := sizes_ok9
    rw [Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    rw [Nat.beq_eq] at h1
    rw [decide_eq_true_eq, Nat.beq_eq] at h2
    exact ⟨h1, h2⟩
  have hszlen : sizes9.length = ngE 9 := hs_ok.2
  have hm0 : gl9_0.map List.length = gsz9_0 := (memGroupsOK_sound mem_ok9_0).1
  have hm1 : gl9_1.map List.length = gsz9_1 := (memGroupsOK_sound mem_ok9_1).1
  have hm2 : gl9_2.map List.length = gsz9_2 := (memGroupsOK_sound mem_ok9_2).1
  have hm3 : gl9_3.map List.length = gsz9_3 := (memGroupsOK_sound mem_ok9_3).1
  have hm4 : gl9_4.map List.length = gsz9_4 := (memGroupsOK_sound mem_ok9_4).1
  have hm5 : gl9_5.map List.length = gsz9_5 := (memGroupsOK_sound mem_ok9_5).1
  have hm6 : gl9_6.map List.length = gsz9_6 := (memGroupsOK_sound mem_ok9_6).1
  have hL0 : (gl9_0).length = 88 := by decide
  have hL1 : (gl9_1).length = 94 := by decide
  have hL2 : (gl9_2).length = 46 := by decide
  have hL3 : (gl9_3).length = 63 := by decide
  have hL4 : (gl9_4).length = 58 := by decide
  have hL5 : (gl9_5).length = 30 := by decide
  have hgsz : sizes9 = [gsz9_0, gsz9_1, gsz9_2, gsz9_3, gsz9_4, gsz9_5, gsz9_6].flatten := by
    rw [eqL_eq.mp gsz_ok9]
    rfl
  have hG : GroupsAt cmT eM labT9 stabT9 grepT9 [gl9_0, gl9_1, gl9_2, gl9_3, gl9_4, gl9_5, gl9_6].flatten 0 := by
    refine GroupsAt_cumul _ 0 ?_
    intro j hj
    have hj' : j < 7 := by simpa using hj
    interval_cases j
    · exact (memGroupsOK_sound mem_ok9_0).2
    · have ho : (cumul (0:ℕ) [gl9_0, gl9_1, gl9_2, gl9_3, gl9_4, gl9_5, gl9_6]).getD 1 0 = 88 := by
        show (0 + (gl9_0).length) = 88
        rw [hL0]
      rw [ho]; exact (memGroupsOK_sound mem_ok9_1).2
    · have ho : (cumul (0:ℕ) [gl9_0, gl9_1, gl9_2, gl9_3, gl9_4, gl9_5, gl9_6]).getD 2 0 = 182 := by
        show ((0 + (gl9_0).length) + (gl9_1).length) = 182
        rw [hL0, hL1]
      rw [ho]; exact (memGroupsOK_sound mem_ok9_2).2
    · have ho : (cumul (0:ℕ) [gl9_0, gl9_1, gl9_2, gl9_3, gl9_4, gl9_5, gl9_6]).getD 3 0 = 228 := by
        show (((0 + (gl9_0).length) + (gl9_1).length) + (gl9_2).length) = 228
        rw [hL0, hL1, hL2]
      rw [ho]; exact (memGroupsOK_sound mem_ok9_3).2
    · have ho : (cumul (0:ℕ) [gl9_0, gl9_1, gl9_2, gl9_3, gl9_4, gl9_5, gl9_6]).getD 4 0 = 291 := by
        show ((((0 + (gl9_0).length) + (gl9_1).length) + (gl9_2).length) + (gl9_3).length) = 291
        rw [hL0, hL1, hL2, hL3]
      rw [ho]; exact (memGroupsOK_sound mem_ok9_4).2
    · have ho : (cumul (0:ℕ) [gl9_0, gl9_1, gl9_2, gl9_3, gl9_4, gl9_5, gl9_6]).getD 5 0 = 349 := by
        show (((((0 + (gl9_0).length) + (gl9_1).length) + (gl9_2).length) + (gl9_3).length) + (gl9_4).length) = 349
        rw [hL0, hL1, hL2, hL3, hL4]
      rw [ho]; exact (memGroupsOK_sound mem_ok9_5).2
    · have ho : (cumul (0:ℕ) [gl9_0, gl9_1, gl9_2, gl9_3, gl9_4, gl9_5, gl9_6]).getD 6 0 = 379 := by
        show ((((((0 + (gl9_0).length) + (gl9_1).length) + (gl9_2).length) + (gl9_3).length) + (gl9_4).length) + (gl9_5).length) = 379
        rw [hL0, hL1, hL2, hL3, hL4, hL5]
      rw [ho]; exact (memGroupsOK_sound mem_ok9_6).2
  have hmap : ([gl9_0, gl9_1, gl9_2, gl9_3, gl9_4, gl9_5, gl9_6].map (fun l => l.map List.length)) = [gsz9_0, gsz9_1, gsz9_2, gsz9_3, gsz9_4, gsz9_5, gsz9_6] := by
    simp only [List.map_cons, List.map_nil, hm0, hm1, hm2, hm3, hm4, hm5, hm6]
  have hGsz : ([gl9_0, gl9_1, gl9_2, gl9_3, gl9_4, gl9_5, gl9_6].flatten).map List.length = sizes9 := by
    rw [hgsz, List.map_flatten, hmap]
  have hGlen : ([gl9_0, gl9_1, gl9_2, gl9_3, gl9_4, gl9_5, gl9_6].flatten).length = ngE 9 := by
    rw [show ([gl9_0, gl9_1, gl9_2, gl9_3, gl9_4, gl9_5, gl9_6].flatten).length = (([gl9_0, gl9_1, gl9_2, gl9_3, gl9_4, gl9_5, gl9_6].flatten).map List.length).length from
      (List.length_map List.length).symm, hGsz]
    exact hszlen
  have hsum : (([gl9_0, gl9_1, gl9_2, gl9_3, gl9_4, gl9_5, gl9_6].flatten).flatten).length = 4641 := by
    rw [List.length_flatten, hGsz, ← sumL_eq_sum]; exact hs_ok.1
  have hrep : ∀ g < ngE 9, cG grepT9 g ∈ eAll ∧ lG labT9 (cG grepT9 g) = g := by
    intro g hg
    have h := grepOK_sound grep_ok9 g hg
    exact ⟨Work.PTCert.NSemAux.mem_eAll_of_em_ne_zero h.1 h.2.1, h.2.2⟩
  have hStabLen : (stabL 9).length = 48 := by
    have h := stablen_ok9
    rw [Nat.beq_eq] at h
    exact h
  have hstab : ∀ s < (stabL 9).length, ∀ k < 81, lk (stabT9.get s) k < 81 := by
    intro s hs k hk
    obtain ⟨pc, sc, hpc, htab⟩ := tabsOK_sound stabtab_ok9 s hs
    rw [htab k hk]
    exact Work.PTCert.codeFactsAux.actLBound pc sc hpc k hk
  have hssrange : [[0,1,2,3,4], [5,6,7,8,9], [10,11,12,13,14], [15,16,17,18,19], [20,21,22,23,24], [25,26,27,28,29], [30,31,32,33,34], [35,36,37,38,39], [40,41,42,43,44], [45,46,47]].flatten = List.range 48 := by decide
  have hclos : ∀ s < (stabL 9).length, ∀ g < ngE 9,
      lG labT9 (actC cmT (stabT9.get s) (cG grepT9 g)) = g := by
    intro s hs g hg
    have hs' : s ∈ [[0,1,2,3,4], [5,6,7,8,9], [10,11,12,13,14], [15,16,17,18,19], [20,21,22,23,24], [25,26,27,28,29], [30,31,32,33,34], [35,36,37,38,39], [40,41,42,43,44], [45,46,47]].flatten := by
      rw [hssrange, List.mem_range]; rwa [hStabLen] at hs
    exact closOK_flatten_spec (chunks := [[0,1,2,3,4], [5,6,7,8,9], [10,11,12,13,14], [15,16,17,18,19], [20,21,22,23,24], [25,26,27,28,29], [30,31,32,33,34], [35,36,37,38,39], [40,41,42,43,44], [45,46,47]]) (gs := List.range (ngE 9))
      (fun j hj => by
        have hj' : j < 10 := by simpa using hj
        interval_cases j
        · exact clos_ok9_0
        · exact clos_ok9_1
        · exact clos_ok9_2
        · exact clos_ok9_3
        · exact clos_ok9_4
        · exact clos_ok9_5
        · exact clos_ok9_6
        · exact clos_ok9_7
        · exact clos_ok9_8
        · exact clos_ok9_9
        )
      g (List.mem_range.mpr hg) s hs'
  have hidx : ∀ i < ([gl9_0, gl9_1, gl9_2, gl9_3, gl9_4, gl9_5, gl9_6].flatten).length, ∀ v ∈ ([gl9_0, gl9_1, gl9_2, gl9_3, gl9_4, gl9_5, gl9_6].flatten).getD i [],
      v % 4096 < (stabL 9).length := by
    intro i hi v hv
    have hmem : ([gl9_0, gl9_1, gl9_2, gl9_3, gl9_4, gl9_5, gl9_6].flatten).getD i [] ∈ ([gl9_0, gl9_1, gl9_2, gl9_3, gl9_4, gl9_5, gl9_6].flatten) := getD_mem hi
    have h := memIdxOK_flatten_spec (chunks := [gl9_0, gl9_1, gl9_2, gl9_3, gl9_4, gl9_5, gl9_6]) (ns := 48)
      (fun j hj => by
        have hj' : j < 7 := by simpa using hj
        interval_cases j
        · exact memidx_ok9_0
        · exact memidx_ok9_1
        · exact memidx_ok9_2
        · exact memidx_ok9_3
        · exact memidx_ok9_4
        · exact memidx_ok9_5
        · exact memidx_ok9_6
        ) _ hmem v hv
    rwa [hStabLen]
  exact genericGroups labT9 stabT9 grepT9 (stabL9) (sizes9) ([gl9_0, gl9_1, gl9_2, gl9_3, gl9_4, gl9_5, gl9_6].flatten) (ngE 9)
    hG hGsz hGlen hszlen hsum hrep hstab hclos hidx

theorem row10 :
    (∀ z ∈ eAll, labE 10 z < ngE 10 ∧ ∃ i < (stabL 10).length,
        actC cmT (stabTab 10 i) (grepE 10 (labE 10 z)) = z) ∧
    (∀ g < ngE 10, grepE 10 g ∈ eAll ∧ labE 10 (grepE 10 g) = g) ∧
    (∀ i < (stabL 10).length, ∀ g < ngE 10,
        labE 10 (actC cmT (stabTab 10 i) (grepE 10 g)) = g) ∧
    (∀ g < ngE 10, (eAll.filter (fun z => labE 10 z = g)).length = sizeE 10 g) ∧
    (sizesL.getD 10 []).length = ngE 10 := by
  have hs_ok : sumL sizes10 = 4641 ∧ sizes10.length = ngE 10 := by
    have h := sizes_ok10
    rw [Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    rw [Nat.beq_eq] at h1
    rw [decide_eq_true_eq, Nat.beq_eq] at h2
    exact ⟨h1, h2⟩
  have hszlen : sizes10.length = ngE 10 := hs_ok.2
  have hm0 : gl10_0.map List.length = gsz10_0 := (memGroupsOK_sound mem_ok10_0).1
  have hm1 : gl10_1.map List.length = gsz10_1 := (memGroupsOK_sound mem_ok10_1).1
  have hm2 : gl10_2.map List.length = gsz10_2 := (memGroupsOK_sound mem_ok10_2).1
  have hm3 : gl10_3.map List.length = gsz10_3 := (memGroupsOK_sound mem_ok10_3).1
  have hm4 : gl10_4.map List.length = gsz10_4 := (memGroupsOK_sound mem_ok10_4).1
  have hm5 : gl10_5.map List.length = gsz10_5 := (memGroupsOK_sound mem_ok10_5).1
  have hm6 : gl10_6.map List.length = gsz10_6 := (memGroupsOK_sound mem_ok10_6).1
  have hL0 : (gl10_0).length = 88 := by decide
  have hL1 : (gl10_1).length = 94 := by decide
  have hL2 : (gl10_2).length = 46 := by decide
  have hL3 : (gl10_3).length = 63 := by decide
  have hL4 : (gl10_4).length = 58 := by decide
  have hL5 : (gl10_5).length = 30 := by decide
  have hgsz : sizes10 = [gsz10_0, gsz10_1, gsz10_2, gsz10_3, gsz10_4, gsz10_5, gsz10_6].flatten := by
    rw [eqL_eq.mp gsz_ok10]
    rfl
  have hG : GroupsAt cmT eM labT10 stabT10 grepT10 [gl10_0, gl10_1, gl10_2, gl10_3, gl10_4, gl10_5, gl10_6].flatten 0 := by
    refine GroupsAt_cumul _ 0 ?_
    intro j hj
    have hj' : j < 7 := by simpa using hj
    interval_cases j
    · exact (memGroupsOK_sound mem_ok10_0).2
    · have ho : (cumul (0:ℕ) [gl10_0, gl10_1, gl10_2, gl10_3, gl10_4, gl10_5, gl10_6]).getD 1 0 = 88 := by
        show (0 + (gl10_0).length) = 88
        rw [hL0]
      rw [ho]; exact (memGroupsOK_sound mem_ok10_1).2
    · have ho : (cumul (0:ℕ) [gl10_0, gl10_1, gl10_2, gl10_3, gl10_4, gl10_5, gl10_6]).getD 2 0 = 182 := by
        show ((0 + (gl10_0).length) + (gl10_1).length) = 182
        rw [hL0, hL1]
      rw [ho]; exact (memGroupsOK_sound mem_ok10_2).2
    · have ho : (cumul (0:ℕ) [gl10_0, gl10_1, gl10_2, gl10_3, gl10_4, gl10_5, gl10_6]).getD 3 0 = 228 := by
        show (((0 + (gl10_0).length) + (gl10_1).length) + (gl10_2).length) = 228
        rw [hL0, hL1, hL2]
      rw [ho]; exact (memGroupsOK_sound mem_ok10_3).2
    · have ho : (cumul (0:ℕ) [gl10_0, gl10_1, gl10_2, gl10_3, gl10_4, gl10_5, gl10_6]).getD 4 0 = 291 := by
        show ((((0 + (gl10_0).length) + (gl10_1).length) + (gl10_2).length) + (gl10_3).length) = 291
        rw [hL0, hL1, hL2, hL3]
      rw [ho]; exact (memGroupsOK_sound mem_ok10_4).2
    · have ho : (cumul (0:ℕ) [gl10_0, gl10_1, gl10_2, gl10_3, gl10_4, gl10_5, gl10_6]).getD 5 0 = 349 := by
        show (((((0 + (gl10_0).length) + (gl10_1).length) + (gl10_2).length) + (gl10_3).length) + (gl10_4).length) = 349
        rw [hL0, hL1, hL2, hL3, hL4]
      rw [ho]; exact (memGroupsOK_sound mem_ok10_5).2
    · have ho : (cumul (0:ℕ) [gl10_0, gl10_1, gl10_2, gl10_3, gl10_4, gl10_5, gl10_6]).getD 6 0 = 379 := by
        show ((((((0 + (gl10_0).length) + (gl10_1).length) + (gl10_2).length) + (gl10_3).length) + (gl10_4).length) + (gl10_5).length) = 379
        rw [hL0, hL1, hL2, hL3, hL4, hL5]
      rw [ho]; exact (memGroupsOK_sound mem_ok10_6).2
  have hmap : ([gl10_0, gl10_1, gl10_2, gl10_3, gl10_4, gl10_5, gl10_6].map (fun l => l.map List.length)) = [gsz10_0, gsz10_1, gsz10_2, gsz10_3, gsz10_4, gsz10_5, gsz10_6] := by
    simp only [List.map_cons, List.map_nil, hm0, hm1, hm2, hm3, hm4, hm5, hm6]
  have hGsz : ([gl10_0, gl10_1, gl10_2, gl10_3, gl10_4, gl10_5, gl10_6].flatten).map List.length = sizes10 := by
    rw [hgsz, List.map_flatten, hmap]
  have hGlen : ([gl10_0, gl10_1, gl10_2, gl10_3, gl10_4, gl10_5, gl10_6].flatten).length = ngE 10 := by
    rw [show ([gl10_0, gl10_1, gl10_2, gl10_3, gl10_4, gl10_5, gl10_6].flatten).length = (([gl10_0, gl10_1, gl10_2, gl10_3, gl10_4, gl10_5, gl10_6].flatten).map List.length).length from
      (List.length_map List.length).symm, hGsz]
    exact hszlen
  have hsum : (([gl10_0, gl10_1, gl10_2, gl10_3, gl10_4, gl10_5, gl10_6].flatten).flatten).length = 4641 := by
    rw [List.length_flatten, hGsz, ← sumL_eq_sum]; exact hs_ok.1
  have hrep : ∀ g < ngE 10, cG grepT10 g ∈ eAll ∧ lG labT10 (cG grepT10 g) = g := by
    intro g hg
    have h := grepOK_sound grep_ok10 g hg
    exact ⟨Work.PTCert.NSemAux.mem_eAll_of_em_ne_zero h.1 h.2.1, h.2.2⟩
  have hStabLen : (stabL 10).length = 48 := by
    have h := stablen_ok10
    rw [Nat.beq_eq] at h
    exact h
  have hstab : ∀ s < (stabL 10).length, ∀ k < 81, lk (stabT10.get s) k < 81 := by
    intro s hs k hk
    obtain ⟨pc, sc, hpc, htab⟩ := tabsOK_sound stabtab_ok10 s hs
    rw [htab k hk]
    exact Work.PTCert.codeFactsAux.actLBound pc sc hpc k hk
  have hssrange : [[0,1,2,3,4], [5,6,7,8,9], [10,11,12,13,14], [15,16,17,18,19], [20,21,22,23,24], [25,26,27,28,29], [30,31,32,33,34], [35,36,37,38,39], [40,41,42,43,44], [45,46,47]].flatten = List.range 48 := by decide
  have hclos : ∀ s < (stabL 10).length, ∀ g < ngE 10,
      lG labT10 (actC cmT (stabT10.get s) (cG grepT10 g)) = g := by
    intro s hs g hg
    have hs' : s ∈ [[0,1,2,3,4], [5,6,7,8,9], [10,11,12,13,14], [15,16,17,18,19], [20,21,22,23,24], [25,26,27,28,29], [30,31,32,33,34], [35,36,37,38,39], [40,41,42,43,44], [45,46,47]].flatten := by
      rw [hssrange, List.mem_range]; rwa [hStabLen] at hs
    exact closOK_flatten_spec (chunks := [[0,1,2,3,4], [5,6,7,8,9], [10,11,12,13,14], [15,16,17,18,19], [20,21,22,23,24], [25,26,27,28,29], [30,31,32,33,34], [35,36,37,38,39], [40,41,42,43,44], [45,46,47]]) (gs := List.range (ngE 10))
      (fun j hj => by
        have hj' : j < 10 := by simpa using hj
        interval_cases j
        · exact clos_ok10_0
        · exact clos_ok10_1
        · exact clos_ok10_2
        · exact clos_ok10_3
        · exact clos_ok10_4
        · exact clos_ok10_5
        · exact clos_ok10_6
        · exact clos_ok10_7
        · exact clos_ok10_8
        · exact clos_ok10_9
        )
      g (List.mem_range.mpr hg) s hs'
  have hidx : ∀ i < ([gl10_0, gl10_1, gl10_2, gl10_3, gl10_4, gl10_5, gl10_6].flatten).length, ∀ v ∈ ([gl10_0, gl10_1, gl10_2, gl10_3, gl10_4, gl10_5, gl10_6].flatten).getD i [],
      v % 4096 < (stabL 10).length := by
    intro i hi v hv
    have hmem : ([gl10_0, gl10_1, gl10_2, gl10_3, gl10_4, gl10_5, gl10_6].flatten).getD i [] ∈ ([gl10_0, gl10_1, gl10_2, gl10_3, gl10_4, gl10_5, gl10_6].flatten) := getD_mem hi
    have h := memIdxOK_flatten_spec (chunks := [gl10_0, gl10_1, gl10_2, gl10_3, gl10_4, gl10_5, gl10_6]) (ns := 48)
      (fun j hj => by
        have hj' : j < 7 := by simpa using hj
        interval_cases j
        · exact memidx_ok10_0
        · exact memidx_ok10_1
        · exact memidx_ok10_2
        · exact memidx_ok10_3
        · exact memidx_ok10_4
        · exact memidx_ok10_5
        · exact memidx_ok10_6
        ) _ hmem v hv
    rwa [hStabLen]
  exact genericGroups labT10 stabT10 grepT10 (stabL10) (sizes10) ([gl10_0, gl10_1, gl10_2, gl10_3, gl10_4, gl10_5, gl10_6].flatten) (ngE 10)
    hG hGsz hGlen hszlen hsum hrep hstab hclos hidx

theorem row11 :
    (∀ z ∈ eAll, labE 11 z < ngE 11 ∧ ∃ i < (stabL 11).length,
        actC cmT (stabTab 11 i) (grepE 11 (labE 11 z)) = z) ∧
    (∀ g < ngE 11, grepE 11 g ∈ eAll ∧ labE 11 (grepE 11 g) = g) ∧
    (∀ i < (stabL 11).length, ∀ g < ngE 11,
        labE 11 (actC cmT (stabTab 11 i) (grepE 11 g)) = g) ∧
    (∀ g < ngE 11, (eAll.filter (fun z => labE 11 z = g)).length = sizeE 11 g) ∧
    (sizesL.getD 11 []).length = ngE 11 := by
  have hs_ok : sumL sizes11 = 4641 ∧ sizes11.length = ngE 11 := by
    have h := sizes_ok11
    rw [Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    rw [Nat.beq_eq] at h1
    rw [decide_eq_true_eq, Nat.beq_eq] at h2
    exact ⟨h1, h2⟩
  have hszlen : sizes11.length = ngE 11 := hs_ok.2
  have hm0 : gl11_0.map List.length = gsz11_0 := (memGroupsOK_sound mem_ok11_0).1
  have hm1 : gl11_1.map List.length = gsz11_1 := (memGroupsOK_sound mem_ok11_1).1
  have hm2 : gl11_2.map List.length = gsz11_2 := (memGroupsOK_sound mem_ok11_2).1
  have hm3 : gl11_3.map List.length = gsz11_3 := (memGroupsOK_sound mem_ok11_3).1
  have hm4 : gl11_4.map List.length = gsz11_4 := (memGroupsOK_sound mem_ok11_4).1
  have hm5 : gl11_5.map List.length = gsz11_5 := (memGroupsOK_sound mem_ok11_5).1
  have hm6 : gl11_6.map List.length = gsz11_6 := (memGroupsOK_sound mem_ok11_6).1
  have hL0 : (gl11_0).length = 233 := by decide
  have hL1 : (gl11_1).length = 255 := by decide
  have hL2 : (gl11_2).length = 187 := by decide
  have hL3 : (gl11_3).length = 219 := by decide
  have hL4 : (gl11_4).length = 208 := by decide
  have hL5 : (gl11_5).length = 126 := by decide
  have hgsz : sizes11 = [gsz11_0, gsz11_1, gsz11_2, gsz11_3, gsz11_4, gsz11_5, gsz11_6].flatten := by
    rw [eqL_eq.mp gsz_ok11]
    rfl
  have hG : GroupsAt cmT eM labT11 stabT11 grepT11 [gl11_0, gl11_1, gl11_2, gl11_3, gl11_4, gl11_5, gl11_6].flatten 0 := by
    refine GroupsAt_cumul _ 0 ?_
    intro j hj
    have hj' : j < 7 := by simpa using hj
    interval_cases j
    · exact (memGroupsOK_sound mem_ok11_0).2
    · have ho : (cumul (0:ℕ) [gl11_0, gl11_1, gl11_2, gl11_3, gl11_4, gl11_5, gl11_6]).getD 1 0 = 233 := by
        show (0 + (gl11_0).length) = 233
        rw [hL0]
      rw [ho]; exact (memGroupsOK_sound mem_ok11_1).2
    · have ho : (cumul (0:ℕ) [gl11_0, gl11_1, gl11_2, gl11_3, gl11_4, gl11_5, gl11_6]).getD 2 0 = 488 := by
        show ((0 + (gl11_0).length) + (gl11_1).length) = 488
        rw [hL0, hL1]
      rw [ho]; exact (memGroupsOK_sound mem_ok11_2).2
    · have ho : (cumul (0:ℕ) [gl11_0, gl11_1, gl11_2, gl11_3, gl11_4, gl11_5, gl11_6]).getD 3 0 = 675 := by
        show (((0 + (gl11_0).length) + (gl11_1).length) + (gl11_2).length) = 675
        rw [hL0, hL1, hL2]
      rw [ho]; exact (memGroupsOK_sound mem_ok11_3).2
    · have ho : (cumul (0:ℕ) [gl11_0, gl11_1, gl11_2, gl11_3, gl11_4, gl11_5, gl11_6]).getD 4 0 = 894 := by
        show ((((0 + (gl11_0).length) + (gl11_1).length) + (gl11_2).length) + (gl11_3).length) = 894
        rw [hL0, hL1, hL2, hL3]
      rw [ho]; exact (memGroupsOK_sound mem_ok11_4).2
    · have ho : (cumul (0:ℕ) [gl11_0, gl11_1, gl11_2, gl11_3, gl11_4, gl11_5, gl11_6]).getD 5 0 = 1102 := by
        show (((((0 + (gl11_0).length) + (gl11_1).length) + (gl11_2).length) + (gl11_3).length) + (gl11_4).length) = 1102
        rw [hL0, hL1, hL2, hL3, hL4]
      rw [ho]; exact (memGroupsOK_sound mem_ok11_5).2
    · have ho : (cumul (0:ℕ) [gl11_0, gl11_1, gl11_2, gl11_3, gl11_4, gl11_5, gl11_6]).getD 6 0 = 1228 := by
        show ((((((0 + (gl11_0).length) + (gl11_1).length) + (gl11_2).length) + (gl11_3).length) + (gl11_4).length) + (gl11_5).length) = 1228
        rw [hL0, hL1, hL2, hL3, hL4, hL5]
      rw [ho]; exact (memGroupsOK_sound mem_ok11_6).2
  have hmap : ([gl11_0, gl11_1, gl11_2, gl11_3, gl11_4, gl11_5, gl11_6].map (fun l => l.map List.length)) = [gsz11_0, gsz11_1, gsz11_2, gsz11_3, gsz11_4, gsz11_5, gsz11_6] := by
    simp only [List.map_cons, List.map_nil, hm0, hm1, hm2, hm3, hm4, hm5, hm6]
  have hGsz : ([gl11_0, gl11_1, gl11_2, gl11_3, gl11_4, gl11_5, gl11_6].flatten).map List.length = sizes11 := by
    rw [hgsz, List.map_flatten, hmap]
  have hGlen : ([gl11_0, gl11_1, gl11_2, gl11_3, gl11_4, gl11_5, gl11_6].flatten).length = ngE 11 := by
    rw [show ([gl11_0, gl11_1, gl11_2, gl11_3, gl11_4, gl11_5, gl11_6].flatten).length = (([gl11_0, gl11_1, gl11_2, gl11_3, gl11_4, gl11_5, gl11_6].flatten).map List.length).length from
      (List.length_map List.length).symm, hGsz]
    exact hszlen
  have hsum : (([gl11_0, gl11_1, gl11_2, gl11_3, gl11_4, gl11_5, gl11_6].flatten).flatten).length = 4641 := by
    rw [List.length_flatten, hGsz, ← sumL_eq_sum]; exact hs_ok.1
  have hrep : ∀ g < ngE 11, cG grepT11 g ∈ eAll ∧ lG labT11 (cG grepT11 g) = g := by
    intro g hg
    have h := grepOK_sound grep_ok11 g hg
    exact ⟨Work.PTCert.NSemAux.mem_eAll_of_em_ne_zero h.1 h.2.1, h.2.2⟩
  have hStabLen : (stabL 11).length = 8 := by
    have h := stablen_ok11
    rw [Nat.beq_eq] at h
    exact h
  have hstab : ∀ s < (stabL 11).length, ∀ k < 81, lk (stabT11.get s) k < 81 := by
    intro s hs k hk
    obtain ⟨pc, sc, hpc, htab⟩ := tabsOK_sound stabtab_ok11 s hs
    rw [htab k hk]
    exact Work.PTCert.codeFactsAux.actLBound pc sc hpc k hk
  have hssrange : [[0], [1], [2], [3], [4], [5], [6], [7]].flatten = List.range 8 := by decide
  have hclos : ∀ s < (stabL 11).length, ∀ g < ngE 11,
      lG labT11 (actC cmT (stabT11.get s) (cG grepT11 g)) = g := by
    intro s hs g hg
    have hs' : s ∈ [[0], [1], [2], [3], [4], [5], [6], [7]].flatten := by
      rw [hssrange, List.mem_range]; rwa [hStabLen] at hs
    exact closOK_flatten_spec (chunks := [[0], [1], [2], [3], [4], [5], [6], [7]]) (gs := List.range (ngE 11))
      (fun j hj => by
        have hj' : j < 8 := by simpa using hj
        interval_cases j
        · exact clos_ok11_0
        · exact clos_ok11_1
        · exact clos_ok11_2
        · exact clos_ok11_3
        · exact clos_ok11_4
        · exact clos_ok11_5
        · exact clos_ok11_6
        · exact clos_ok11_7
        )
      g (List.mem_range.mpr hg) s hs'
  have hidx : ∀ i < ([gl11_0, gl11_1, gl11_2, gl11_3, gl11_4, gl11_5, gl11_6].flatten).length, ∀ v ∈ ([gl11_0, gl11_1, gl11_2, gl11_3, gl11_4, gl11_5, gl11_6].flatten).getD i [],
      v % 4096 < (stabL 11).length := by
    intro i hi v hv
    have hmem : ([gl11_0, gl11_1, gl11_2, gl11_3, gl11_4, gl11_5, gl11_6].flatten).getD i [] ∈ ([gl11_0, gl11_1, gl11_2, gl11_3, gl11_4, gl11_5, gl11_6].flatten) := getD_mem hi
    have h := memIdxOK_flatten_spec (chunks := [gl11_0, gl11_1, gl11_2, gl11_3, gl11_4, gl11_5, gl11_6]) (ns := 8)
      (fun j hj => by
        have hj' : j < 7 := by simpa using hj
        interval_cases j
        · exact memidx_ok11_0
        · exact memidx_ok11_1
        · exact memidx_ok11_2
        · exact memidx_ok11_3
        · exact memidx_ok11_4
        · exact memidx_ok11_5
        · exact memidx_ok11_6
        ) _ hmem v hv
    rwa [hStabLen]
  exact genericGroups labT11 stabT11 grepT11 (stabL11) (sizes11) ([gl11_0, gl11_1, gl11_2, gl11_3, gl11_4, gl11_5, gl11_6].flatten) (ngE 11)
    hG hGsz hGlen hszlen hsum hrep hstab hclos hidx

theorem row12 :
    (∀ z ∈ eAll, labE 12 z < ngE 12 ∧ ∃ i < (stabL 12).length,
        actC cmT (stabTab 12 i) (grepE 12 (labE 12 z)) = z) ∧
    (∀ g < ngE 12, grepE 12 g ∈ eAll ∧ labE 12 (grepE 12 g) = g) ∧
    (∀ i < (stabL 12).length, ∀ g < ngE 12,
        labE 12 (actC cmT (stabTab 12 i) (grepE 12 g)) = g) ∧
    (∀ g < ngE 12, (eAll.filter (fun z => labE 12 z = g)).length = sizeE 12 g) ∧
    (sizesL.getD 12 []).length = ngE 12 := by
  have hs_ok : sumL sizes12 = 4641 ∧ sizes12.length = ngE 12 := by
    have h := sizes_ok12
    rw [Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    rw [Nat.beq_eq] at h1
    rw [decide_eq_true_eq, Nat.beq_eq] at h2
    exact ⟨h1, h2⟩
  have hszlen : sizes12.length = ngE 12 := hs_ok.2
  have hm0 : gl12_0.map List.length = gsz12_0 := (memGroupsOK_sound mem_ok12_0).1
  have hm1 : gl12_1.map List.length = gsz12_1 := (memGroupsOK_sound mem_ok12_1).1
  have hm2 : gl12_2.map List.length = gsz12_2 := (memGroupsOK_sound mem_ok12_2).1
  have hm3 : gl12_3.map List.length = gsz12_3 := (memGroupsOK_sound mem_ok12_3).1
  have hm4 : gl12_4.map List.length = gsz12_4 := (memGroupsOK_sound mem_ok12_4).1
  have hm5 : gl12_5.map List.length = gsz12_5 := (memGroupsOK_sound mem_ok12_5).1
  have hm6 : gl12_6.map List.length = gsz12_6 := (memGroupsOK_sound mem_ok12_6).1
  have hL0 : (gl12_0).length = 233 := by decide
  have hL1 : (gl12_1).length = 255 := by decide
  have hL2 : (gl12_2).length = 187 := by decide
  have hL3 : (gl12_3).length = 219 := by decide
  have hL4 : (gl12_4).length = 208 := by decide
  have hL5 : (gl12_5).length = 126 := by decide
  have hgsz : sizes12 = [gsz12_0, gsz12_1, gsz12_2, gsz12_3, gsz12_4, gsz12_5, gsz12_6].flatten := by
    rw [eqL_eq.mp gsz_ok12]
    rfl
  have hG : GroupsAt cmT eM labT12 stabT12 grepT12 [gl12_0, gl12_1, gl12_2, gl12_3, gl12_4, gl12_5, gl12_6].flatten 0 := by
    refine GroupsAt_cumul _ 0 ?_
    intro j hj
    have hj' : j < 7 := by simpa using hj
    interval_cases j
    · exact (memGroupsOK_sound mem_ok12_0).2
    · have ho : (cumul (0:ℕ) [gl12_0, gl12_1, gl12_2, gl12_3, gl12_4, gl12_5, gl12_6]).getD 1 0 = 233 := by
        show (0 + (gl12_0).length) = 233
        rw [hL0]
      rw [ho]; exact (memGroupsOK_sound mem_ok12_1).2
    · have ho : (cumul (0:ℕ) [gl12_0, gl12_1, gl12_2, gl12_3, gl12_4, gl12_5, gl12_6]).getD 2 0 = 488 := by
        show ((0 + (gl12_0).length) + (gl12_1).length) = 488
        rw [hL0, hL1]
      rw [ho]; exact (memGroupsOK_sound mem_ok12_2).2
    · have ho : (cumul (0:ℕ) [gl12_0, gl12_1, gl12_2, gl12_3, gl12_4, gl12_5, gl12_6]).getD 3 0 = 675 := by
        show (((0 + (gl12_0).length) + (gl12_1).length) + (gl12_2).length) = 675
        rw [hL0, hL1, hL2]
      rw [ho]; exact (memGroupsOK_sound mem_ok12_3).2
    · have ho : (cumul (0:ℕ) [gl12_0, gl12_1, gl12_2, gl12_3, gl12_4, gl12_5, gl12_6]).getD 4 0 = 894 := by
        show ((((0 + (gl12_0).length) + (gl12_1).length) + (gl12_2).length) + (gl12_3).length) = 894
        rw [hL0, hL1, hL2, hL3]
      rw [ho]; exact (memGroupsOK_sound mem_ok12_4).2
    · have ho : (cumul (0:ℕ) [gl12_0, gl12_1, gl12_2, gl12_3, gl12_4, gl12_5, gl12_6]).getD 5 0 = 1102 := by
        show (((((0 + (gl12_0).length) + (gl12_1).length) + (gl12_2).length) + (gl12_3).length) + (gl12_4).length) = 1102
        rw [hL0, hL1, hL2, hL3, hL4]
      rw [ho]; exact (memGroupsOK_sound mem_ok12_5).2
    · have ho : (cumul (0:ℕ) [gl12_0, gl12_1, gl12_2, gl12_3, gl12_4, gl12_5, gl12_6]).getD 6 0 = 1228 := by
        show ((((((0 + (gl12_0).length) + (gl12_1).length) + (gl12_2).length) + (gl12_3).length) + (gl12_4).length) + (gl12_5).length) = 1228
        rw [hL0, hL1, hL2, hL3, hL4, hL5]
      rw [ho]; exact (memGroupsOK_sound mem_ok12_6).2
  have hmap : ([gl12_0, gl12_1, gl12_2, gl12_3, gl12_4, gl12_5, gl12_6].map (fun l => l.map List.length)) = [gsz12_0, gsz12_1, gsz12_2, gsz12_3, gsz12_4, gsz12_5, gsz12_6] := by
    simp only [List.map_cons, List.map_nil, hm0, hm1, hm2, hm3, hm4, hm5, hm6]
  have hGsz : ([gl12_0, gl12_1, gl12_2, gl12_3, gl12_4, gl12_5, gl12_6].flatten).map List.length = sizes12 := by
    rw [hgsz, List.map_flatten, hmap]
  have hGlen : ([gl12_0, gl12_1, gl12_2, gl12_3, gl12_4, gl12_5, gl12_6].flatten).length = ngE 12 := by
    rw [show ([gl12_0, gl12_1, gl12_2, gl12_3, gl12_4, gl12_5, gl12_6].flatten).length = (([gl12_0, gl12_1, gl12_2, gl12_3, gl12_4, gl12_5, gl12_6].flatten).map List.length).length from
      (List.length_map List.length).symm, hGsz]
    exact hszlen
  have hsum : (([gl12_0, gl12_1, gl12_2, gl12_3, gl12_4, gl12_5, gl12_6].flatten).flatten).length = 4641 := by
    rw [List.length_flatten, hGsz, ← sumL_eq_sum]; exact hs_ok.1
  have hrep : ∀ g < ngE 12, cG grepT12 g ∈ eAll ∧ lG labT12 (cG grepT12 g) = g := by
    intro g hg
    have h := grepOK_sound grep_ok12 g hg
    exact ⟨Work.PTCert.NSemAux.mem_eAll_of_em_ne_zero h.1 h.2.1, h.2.2⟩
  have hStabLen : (stabL 12).length = 8 := by
    have h := stablen_ok12
    rw [Nat.beq_eq] at h
    exact h
  have hstab : ∀ s < (stabL 12).length, ∀ k < 81, lk (stabT12.get s) k < 81 := by
    intro s hs k hk
    obtain ⟨pc, sc, hpc, htab⟩ := tabsOK_sound stabtab_ok12 s hs
    rw [htab k hk]
    exact Work.PTCert.codeFactsAux.actLBound pc sc hpc k hk
  have hssrange : [[0], [1], [2], [3], [4], [5], [6], [7]].flatten = List.range 8 := by decide
  have hclos : ∀ s < (stabL 12).length, ∀ g < ngE 12,
      lG labT12 (actC cmT (stabT12.get s) (cG grepT12 g)) = g := by
    intro s hs g hg
    have hs' : s ∈ [[0], [1], [2], [3], [4], [5], [6], [7]].flatten := by
      rw [hssrange, List.mem_range]; rwa [hStabLen] at hs
    exact closOK_flatten_spec (chunks := [[0], [1], [2], [3], [4], [5], [6], [7]]) (gs := List.range (ngE 12))
      (fun j hj => by
        have hj' : j < 8 := by simpa using hj
        interval_cases j
        · exact clos_ok12_0
        · exact clos_ok12_1
        · exact clos_ok12_2
        · exact clos_ok12_3
        · exact clos_ok12_4
        · exact clos_ok12_5
        · exact clos_ok12_6
        · exact clos_ok12_7
        )
      g (List.mem_range.mpr hg) s hs'
  have hidx : ∀ i < ([gl12_0, gl12_1, gl12_2, gl12_3, gl12_4, gl12_5, gl12_6].flatten).length, ∀ v ∈ ([gl12_0, gl12_1, gl12_2, gl12_3, gl12_4, gl12_5, gl12_6].flatten).getD i [],
      v % 4096 < (stabL 12).length := by
    intro i hi v hv
    have hmem : ([gl12_0, gl12_1, gl12_2, gl12_3, gl12_4, gl12_5, gl12_6].flatten).getD i [] ∈ ([gl12_0, gl12_1, gl12_2, gl12_3, gl12_4, gl12_5, gl12_6].flatten) := getD_mem hi
    have h := memIdxOK_flatten_spec (chunks := [gl12_0, gl12_1, gl12_2, gl12_3, gl12_4, gl12_5, gl12_6]) (ns := 8)
      (fun j hj => by
        have hj' : j < 7 := by simpa using hj
        interval_cases j
        · exact memidx_ok12_0
        · exact memidx_ok12_1
        · exact memidx_ok12_2
        · exact memidx_ok12_3
        · exact memidx_ok12_4
        · exact memidx_ok12_5
        · exact memidx_ok12_6
        ) _ hmem v hv
    rwa [hStabLen]
  exact genericGroups labT12 stabT12 grepT12 (stabL12) (sizes12) ([gl12_0, gl12_1, gl12_2, gl12_3, gl12_4, gl12_5, gl12_6].flatten) (ngE 12)
    hG hGsz hGlen hszlen hsum hrep hstab hclos hidx

theorem row13 :
    (∀ z ∈ eAll, labE 13 z < ngE 13 ∧ ∃ i < (stabL 13).length,
        actC cmT (stabTab 13 i) (grepE 13 (labE 13 z)) = z) ∧
    (∀ g < ngE 13, grepE 13 g ∈ eAll ∧ labE 13 (grepE 13 g) = g) ∧
    (∀ i < (stabL 13).length, ∀ g < ngE 13,
        labE 13 (actC cmT (stabTab 13 i) (grepE 13 g)) = g) ∧
    (∀ g < ngE 13, (eAll.filter (fun z => labE 13 z = g)).length = sizeE 13 g) ∧
    (sizesL.getD 13 []).length = ngE 13 := by
  have hs_ok : sumL sizes13 = 4641 ∧ sizes13.length = ngE 13 := by
    have h := sizes_ok13
    rw [Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    rw [Nat.beq_eq] at h1
    rw [decide_eq_true_eq, Nat.beq_eq] at h2
    exact ⟨h1, h2⟩
  have hszlen : sizes13.length = ngE 13 := hs_ok.2
  have hm0 : gl13_0.map List.length = gsz13_0 := (memGroupsOK_sound mem_ok13_0).1
  have hm1 : gl13_1.map List.length = gsz13_1 := (memGroupsOK_sound mem_ok13_1).1
  have hm2 : gl13_2.map List.length = gsz13_2 := (memGroupsOK_sound mem_ok13_2).1
  have hm3 : gl13_3.map List.length = gsz13_3 := (memGroupsOK_sound mem_ok13_3).1
  have hm4 : gl13_4.map List.length = gsz13_4 := (memGroupsOK_sound mem_ok13_4).1
  have hm5 : gl13_5.map List.length = gsz13_5 := (memGroupsOK_sound mem_ok13_5).1
  have hm6 : gl13_6.map List.length = gsz13_6 := (memGroupsOK_sound mem_ok13_6).1
  have hL0 : (gl13_0).length = 233 := by decide
  have hL1 : (gl13_1).length = 255 := by decide
  have hL2 : (gl13_2).length = 187 := by decide
  have hL3 : (gl13_3).length = 219 := by decide
  have hL4 : (gl13_4).length = 208 := by decide
  have hL5 : (gl13_5).length = 126 := by decide
  have hgsz : sizes13 = [gsz13_0, gsz13_1, gsz13_2, gsz13_3, gsz13_4, gsz13_5, gsz13_6].flatten := by
    rw [eqL_eq.mp gsz_ok13]
    rfl
  have hG : GroupsAt cmT eM labT13 stabT13 grepT13 [gl13_0, gl13_1, gl13_2, gl13_3, gl13_4, gl13_5, gl13_6].flatten 0 := by
    refine GroupsAt_cumul _ 0 ?_
    intro j hj
    have hj' : j < 7 := by simpa using hj
    interval_cases j
    · exact (memGroupsOK_sound mem_ok13_0).2
    · have ho : (cumul (0:ℕ) [gl13_0, gl13_1, gl13_2, gl13_3, gl13_4, gl13_5, gl13_6]).getD 1 0 = 233 := by
        show (0 + (gl13_0).length) = 233
        rw [hL0]
      rw [ho]; exact (memGroupsOK_sound mem_ok13_1).2
    · have ho : (cumul (0:ℕ) [gl13_0, gl13_1, gl13_2, gl13_3, gl13_4, gl13_5, gl13_6]).getD 2 0 = 488 := by
        show ((0 + (gl13_0).length) + (gl13_1).length) = 488
        rw [hL0, hL1]
      rw [ho]; exact (memGroupsOK_sound mem_ok13_2).2
    · have ho : (cumul (0:ℕ) [gl13_0, gl13_1, gl13_2, gl13_3, gl13_4, gl13_5, gl13_6]).getD 3 0 = 675 := by
        show (((0 + (gl13_0).length) + (gl13_1).length) + (gl13_2).length) = 675
        rw [hL0, hL1, hL2]
      rw [ho]; exact (memGroupsOK_sound mem_ok13_3).2
    · have ho : (cumul (0:ℕ) [gl13_0, gl13_1, gl13_2, gl13_3, gl13_4, gl13_5, gl13_6]).getD 4 0 = 894 := by
        show ((((0 + (gl13_0).length) + (gl13_1).length) + (gl13_2).length) + (gl13_3).length) = 894
        rw [hL0, hL1, hL2, hL3]
      rw [ho]; exact (memGroupsOK_sound mem_ok13_4).2
    · have ho : (cumul (0:ℕ) [gl13_0, gl13_1, gl13_2, gl13_3, gl13_4, gl13_5, gl13_6]).getD 5 0 = 1102 := by
        show (((((0 + (gl13_0).length) + (gl13_1).length) + (gl13_2).length) + (gl13_3).length) + (gl13_4).length) = 1102
        rw [hL0, hL1, hL2, hL3, hL4]
      rw [ho]; exact (memGroupsOK_sound mem_ok13_5).2
    · have ho : (cumul (0:ℕ) [gl13_0, gl13_1, gl13_2, gl13_3, gl13_4, gl13_5, gl13_6]).getD 6 0 = 1228 := by
        show ((((((0 + (gl13_0).length) + (gl13_1).length) + (gl13_2).length) + (gl13_3).length) + (gl13_4).length) + (gl13_5).length) = 1228
        rw [hL0, hL1, hL2, hL3, hL4, hL5]
      rw [ho]; exact (memGroupsOK_sound mem_ok13_6).2
  have hmap : ([gl13_0, gl13_1, gl13_2, gl13_3, gl13_4, gl13_5, gl13_6].map (fun l => l.map List.length)) = [gsz13_0, gsz13_1, gsz13_2, gsz13_3, gsz13_4, gsz13_5, gsz13_6] := by
    simp only [List.map_cons, List.map_nil, hm0, hm1, hm2, hm3, hm4, hm5, hm6]
  have hGsz : ([gl13_0, gl13_1, gl13_2, gl13_3, gl13_4, gl13_5, gl13_6].flatten).map List.length = sizes13 := by
    rw [hgsz, List.map_flatten, hmap]
  have hGlen : ([gl13_0, gl13_1, gl13_2, gl13_3, gl13_4, gl13_5, gl13_6].flatten).length = ngE 13 := by
    rw [show ([gl13_0, gl13_1, gl13_2, gl13_3, gl13_4, gl13_5, gl13_6].flatten).length = (([gl13_0, gl13_1, gl13_2, gl13_3, gl13_4, gl13_5, gl13_6].flatten).map List.length).length from
      (List.length_map List.length).symm, hGsz]
    exact hszlen
  have hsum : (([gl13_0, gl13_1, gl13_2, gl13_3, gl13_4, gl13_5, gl13_6].flatten).flatten).length = 4641 := by
    rw [List.length_flatten, hGsz, ← sumL_eq_sum]; exact hs_ok.1
  have hrep : ∀ g < ngE 13, cG grepT13 g ∈ eAll ∧ lG labT13 (cG grepT13 g) = g := by
    intro g hg
    have h := grepOK_sound grep_ok13 g hg
    exact ⟨Work.PTCert.NSemAux.mem_eAll_of_em_ne_zero h.1 h.2.1, h.2.2⟩
  have hStabLen : (stabL 13).length = 8 := by
    have h := stablen_ok13
    rw [Nat.beq_eq] at h
    exact h
  have hstab : ∀ s < (stabL 13).length, ∀ k < 81, lk (stabT13.get s) k < 81 := by
    intro s hs k hk
    obtain ⟨pc, sc, hpc, htab⟩ := tabsOK_sound stabtab_ok13 s hs
    rw [htab k hk]
    exact Work.PTCert.codeFactsAux.actLBound pc sc hpc k hk
  have hssrange : [[0], [1], [2], [3], [4], [5], [6], [7]].flatten = List.range 8 := by decide
  have hclos : ∀ s < (stabL 13).length, ∀ g < ngE 13,
      lG labT13 (actC cmT (stabT13.get s) (cG grepT13 g)) = g := by
    intro s hs g hg
    have hs' : s ∈ [[0], [1], [2], [3], [4], [5], [6], [7]].flatten := by
      rw [hssrange, List.mem_range]; rwa [hStabLen] at hs
    exact closOK_flatten_spec (chunks := [[0], [1], [2], [3], [4], [5], [6], [7]]) (gs := List.range (ngE 13))
      (fun j hj => by
        have hj' : j < 8 := by simpa using hj
        interval_cases j
        · exact clos_ok13_0
        · exact clos_ok13_1
        · exact clos_ok13_2
        · exact clos_ok13_3
        · exact clos_ok13_4
        · exact clos_ok13_5
        · exact clos_ok13_6
        · exact clos_ok13_7
        )
      g (List.mem_range.mpr hg) s hs'
  have hidx : ∀ i < ([gl13_0, gl13_1, gl13_2, gl13_3, gl13_4, gl13_5, gl13_6].flatten).length, ∀ v ∈ ([gl13_0, gl13_1, gl13_2, gl13_3, gl13_4, gl13_5, gl13_6].flatten).getD i [],
      v % 4096 < (stabL 13).length := by
    intro i hi v hv
    have hmem : ([gl13_0, gl13_1, gl13_2, gl13_3, gl13_4, gl13_5, gl13_6].flatten).getD i [] ∈ ([gl13_0, gl13_1, gl13_2, gl13_3, gl13_4, gl13_5, gl13_6].flatten) := getD_mem hi
    have h := memIdxOK_flatten_spec (chunks := [gl13_0, gl13_1, gl13_2, gl13_3, gl13_4, gl13_5, gl13_6]) (ns := 8)
      (fun j hj => by
        have hj' : j < 7 := by simpa using hj
        interval_cases j
        · exact memidx_ok13_0
        · exact memidx_ok13_1
        · exact memidx_ok13_2
        · exact memidx_ok13_3
        · exact memidx_ok13_4
        · exact memidx_ok13_5
        · exact memidx_ok13_6
        ) _ hmem v hv
    rwa [hStabLen]
  exact genericGroups labT13 stabT13 grepT13 (stabL13) (sizes13) ([gl13_0, gl13_1, gl13_2, gl13_3, gl13_4, gl13_5, gl13_6].flatten) (ngE 13)
    hG hGsz hGlen hszlen hsum hrep hstab hclos hidx

theorem row14 :
    (∀ z ∈ eAll, labE 14 z < ngE 14 ∧ ∃ i < (stabL 14).length,
        actC cmT (stabTab 14 i) (grepE 14 (labE 14 z)) = z) ∧
    (∀ g < ngE 14, grepE 14 g ∈ eAll ∧ labE 14 (grepE 14 g) = g) ∧
    (∀ i < (stabL 14).length, ∀ g < ngE 14,
        labE 14 (actC cmT (stabTab 14 i) (grepE 14 g)) = g) ∧
    (∀ g < ngE 14, (eAll.filter (fun z => labE 14 z = g)).length = sizeE 14 g) ∧
    (sizesL.getD 14 []).length = ngE 14 := by
  have hs_ok : sumL sizes14 = 4641 ∧ sizes14.length = ngE 14 := by
    have h := sizes_ok14
    rw [Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    rw [Nat.beq_eq] at h1
    rw [decide_eq_true_eq, Nat.beq_eq] at h2
    exact ⟨h1, h2⟩
  have hszlen : sizes14.length = ngE 14 := hs_ok.2
  have hm0 : gl14_0.map List.length = gsz14_0 := (memGroupsOK_sound mem_ok14_0).1
  have hm1 : gl14_1.map List.length = gsz14_1 := (memGroupsOK_sound mem_ok14_1).1
  have hm2 : gl14_2.map List.length = gsz14_2 := (memGroupsOK_sound mem_ok14_2).1
  have hm3 : gl14_3.map List.length = gsz14_3 := (memGroupsOK_sound mem_ok14_3).1
  have hm4 : gl14_4.map List.length = gsz14_4 := (memGroupsOK_sound mem_ok14_4).1
  have hm5 : gl14_5.map List.length = gsz14_5 := (memGroupsOK_sound mem_ok14_5).1
  have hm6 : gl14_6.map List.length = gsz14_6 := (memGroupsOK_sound mem_ok14_6).1
  have hL0 : (gl14_0).length = 233 := by decide
  have hL1 : (gl14_1).length = 255 := by decide
  have hL2 : (gl14_2).length = 187 := by decide
  have hL3 : (gl14_3).length = 219 := by decide
  have hL4 : (gl14_4).length = 208 := by decide
  have hL5 : (gl14_5).length = 126 := by decide
  have hgsz : sizes14 = [gsz14_0, gsz14_1, gsz14_2, gsz14_3, gsz14_4, gsz14_5, gsz14_6].flatten := by
    rw [eqL_eq.mp gsz_ok14]
    rfl
  have hG : GroupsAt cmT eM labT14 stabT14 grepT14 [gl14_0, gl14_1, gl14_2, gl14_3, gl14_4, gl14_5, gl14_6].flatten 0 := by
    refine GroupsAt_cumul _ 0 ?_
    intro j hj
    have hj' : j < 7 := by simpa using hj
    interval_cases j
    · exact (memGroupsOK_sound mem_ok14_0).2
    · have ho : (cumul (0:ℕ) [gl14_0, gl14_1, gl14_2, gl14_3, gl14_4, gl14_5, gl14_6]).getD 1 0 = 233 := by
        show (0 + (gl14_0).length) = 233
        rw [hL0]
      rw [ho]; exact (memGroupsOK_sound mem_ok14_1).2
    · have ho : (cumul (0:ℕ) [gl14_0, gl14_1, gl14_2, gl14_3, gl14_4, gl14_5, gl14_6]).getD 2 0 = 488 := by
        show ((0 + (gl14_0).length) + (gl14_1).length) = 488
        rw [hL0, hL1]
      rw [ho]; exact (memGroupsOK_sound mem_ok14_2).2
    · have ho : (cumul (0:ℕ) [gl14_0, gl14_1, gl14_2, gl14_3, gl14_4, gl14_5, gl14_6]).getD 3 0 = 675 := by
        show (((0 + (gl14_0).length) + (gl14_1).length) + (gl14_2).length) = 675
        rw [hL0, hL1, hL2]
      rw [ho]; exact (memGroupsOK_sound mem_ok14_3).2
    · have ho : (cumul (0:ℕ) [gl14_0, gl14_1, gl14_2, gl14_3, gl14_4, gl14_5, gl14_6]).getD 4 0 = 894 := by
        show ((((0 + (gl14_0).length) + (gl14_1).length) + (gl14_2).length) + (gl14_3).length) = 894
        rw [hL0, hL1, hL2, hL3]
      rw [ho]; exact (memGroupsOK_sound mem_ok14_4).2
    · have ho : (cumul (0:ℕ) [gl14_0, gl14_1, gl14_2, gl14_3, gl14_4, gl14_5, gl14_6]).getD 5 0 = 1102 := by
        show (((((0 + (gl14_0).length) + (gl14_1).length) + (gl14_2).length) + (gl14_3).length) + (gl14_4).length) = 1102
        rw [hL0, hL1, hL2, hL3, hL4]
      rw [ho]; exact (memGroupsOK_sound mem_ok14_5).2
    · have ho : (cumul (0:ℕ) [gl14_0, gl14_1, gl14_2, gl14_3, gl14_4, gl14_5, gl14_6]).getD 6 0 = 1228 := by
        show ((((((0 + (gl14_0).length) + (gl14_1).length) + (gl14_2).length) + (gl14_3).length) + (gl14_4).length) + (gl14_5).length) = 1228
        rw [hL0, hL1, hL2, hL3, hL4, hL5]
      rw [ho]; exact (memGroupsOK_sound mem_ok14_6).2
  have hmap : ([gl14_0, gl14_1, gl14_2, gl14_3, gl14_4, gl14_5, gl14_6].map (fun l => l.map List.length)) = [gsz14_0, gsz14_1, gsz14_2, gsz14_3, gsz14_4, gsz14_5, gsz14_6] := by
    simp only [List.map_cons, List.map_nil, hm0, hm1, hm2, hm3, hm4, hm5, hm6]
  have hGsz : ([gl14_0, gl14_1, gl14_2, gl14_3, gl14_4, gl14_5, gl14_6].flatten).map List.length = sizes14 := by
    rw [hgsz, List.map_flatten, hmap]
  have hGlen : ([gl14_0, gl14_1, gl14_2, gl14_3, gl14_4, gl14_5, gl14_6].flatten).length = ngE 14 := by
    rw [show ([gl14_0, gl14_1, gl14_2, gl14_3, gl14_4, gl14_5, gl14_6].flatten).length = (([gl14_0, gl14_1, gl14_2, gl14_3, gl14_4, gl14_5, gl14_6].flatten).map List.length).length from
      (List.length_map List.length).symm, hGsz]
    exact hszlen
  have hsum : (([gl14_0, gl14_1, gl14_2, gl14_3, gl14_4, gl14_5, gl14_6].flatten).flatten).length = 4641 := by
    rw [List.length_flatten, hGsz, ← sumL_eq_sum]; exact hs_ok.1
  have hrep : ∀ g < ngE 14, cG grepT14 g ∈ eAll ∧ lG labT14 (cG grepT14 g) = g := by
    intro g hg
    have h := grepOK_sound grep_ok14 g hg
    exact ⟨Work.PTCert.NSemAux.mem_eAll_of_em_ne_zero h.1 h.2.1, h.2.2⟩
  have hStabLen : (stabL 14).length = 8 := by
    have h := stablen_ok14
    rw [Nat.beq_eq] at h
    exact h
  have hstab : ∀ s < (stabL 14).length, ∀ k < 81, lk (stabT14.get s) k < 81 := by
    intro s hs k hk
    obtain ⟨pc, sc, hpc, htab⟩ := tabsOK_sound stabtab_ok14 s hs
    rw [htab k hk]
    exact Work.PTCert.codeFactsAux.actLBound pc sc hpc k hk
  have hssrange : [[0], [1], [2], [3], [4], [5], [6], [7]].flatten = List.range 8 := by decide
  have hclos : ∀ s < (stabL 14).length, ∀ g < ngE 14,
      lG labT14 (actC cmT (stabT14.get s) (cG grepT14 g)) = g := by
    intro s hs g hg
    have hs' : s ∈ [[0], [1], [2], [3], [4], [5], [6], [7]].flatten := by
      rw [hssrange, List.mem_range]; rwa [hStabLen] at hs
    exact closOK_flatten_spec (chunks := [[0], [1], [2], [3], [4], [5], [6], [7]]) (gs := List.range (ngE 14))
      (fun j hj => by
        have hj' : j < 8 := by simpa using hj
        interval_cases j
        · exact clos_ok14_0
        · exact clos_ok14_1
        · exact clos_ok14_2
        · exact clos_ok14_3
        · exact clos_ok14_4
        · exact clos_ok14_5
        · exact clos_ok14_6
        · exact clos_ok14_7
        )
      g (List.mem_range.mpr hg) s hs'
  have hidx : ∀ i < ([gl14_0, gl14_1, gl14_2, gl14_3, gl14_4, gl14_5, gl14_6].flatten).length, ∀ v ∈ ([gl14_0, gl14_1, gl14_2, gl14_3, gl14_4, gl14_5, gl14_6].flatten).getD i [],
      v % 4096 < (stabL 14).length := by
    intro i hi v hv
    have hmem : ([gl14_0, gl14_1, gl14_2, gl14_3, gl14_4, gl14_5, gl14_6].flatten).getD i [] ∈ ([gl14_0, gl14_1, gl14_2, gl14_3, gl14_4, gl14_5, gl14_6].flatten) := getD_mem hi
    have h := memIdxOK_flatten_spec (chunks := [gl14_0, gl14_1, gl14_2, gl14_3, gl14_4, gl14_5, gl14_6]) (ns := 8)
      (fun j hj => by
        have hj' : j < 7 := by simpa using hj
        interval_cases j
        · exact memidx_ok14_0
        · exact memidx_ok14_1
        · exact memidx_ok14_2
        · exact memidx_ok14_3
        · exact memidx_ok14_4
        · exact memidx_ok14_5
        · exact memidx_ok14_6
        ) _ hmem v hv
    rwa [hStabLen]
  exact genericGroups labT14 stabT14 grepT14 (stabL14) (sizes14) ([gl14_0, gl14_1, gl14_2, gl14_3, gl14_4, gl14_5, gl14_6].flatten) (ngE 14)
    hG hGsz hGlen hszlen hsum hrep hstab hclos hidx

theorem row15 :
    (∀ z ∈ eAll, labE 15 z < ngE 15 ∧ ∃ i < (stabL 15).length,
        actC cmT (stabTab 15 i) (grepE 15 (labE 15 z)) = z) ∧
    (∀ g < ngE 15, grepE 15 g ∈ eAll ∧ labE 15 (grepE 15 g) = g) ∧
    (∀ i < (stabL 15).length, ∀ g < ngE 15,
        labE 15 (actC cmT (stabTab 15 i) (grepE 15 g)) = g) ∧
    (∀ g < ngE 15, (eAll.filter (fun z => labE 15 z = g)).length = sizeE 15 g) ∧
    (sizesL.getD 15 []).length = ngE 15 := by
  have hs_ok : sumL sizes15 = 4641 ∧ sizes15.length = ngE 15 := by
    have h := sizes_ok15
    rw [Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    rw [Nat.beq_eq] at h1
    rw [decide_eq_true_eq, Nat.beq_eq] at h2
    exact ⟨h1, h2⟩
  have hszlen : sizes15.length = ngE 15 := hs_ok.2
  have hm0 : gl15_0.map List.length = gsz15_0 := (memGroupsOK_sound mem_ok15_0).1
  have hm1 : gl15_1.map List.length = gsz15_1 := (memGroupsOK_sound mem_ok15_1).1
  have hm2 : gl15_2.map List.length = gsz15_2 := (memGroupsOK_sound mem_ok15_2).1
  have hm3 : gl15_3.map List.length = gsz15_3 := (memGroupsOK_sound mem_ok15_3).1
  have hm4 : gl15_4.map List.length = gsz15_4 := (memGroupsOK_sound mem_ok15_4).1
  have hm5 : gl15_5.map List.length = gsz15_5 := (memGroupsOK_sound mem_ok15_5).1
  have hm6 : gl15_6.map List.length = gsz15_6 := (memGroupsOK_sound mem_ok15_6).1
  have hL0 : (gl15_0).length = 128 := by decide
  have hL1 : (gl15_1).length = 140 := by decide
  have hL2 : (gl15_2).length = 99 := by decide
  have hL3 : (gl15_3).length = 113 := by decide
  have hL4 : (gl15_4).length = 111 := by decide
  have hL5 : (gl15_5).length = 66 := by decide
  have hgsz : sizes15 = [gsz15_0, gsz15_1, gsz15_2, gsz15_3, gsz15_4, gsz15_5, gsz15_6].flatten := by
    rw [eqL_eq.mp gsz_ok15]
    rfl
  have hG : GroupsAt cmT eM labT15 stabT15 grepT15 [gl15_0, gl15_1, gl15_2, gl15_3, gl15_4, gl15_5, gl15_6].flatten 0 := by
    refine GroupsAt_cumul _ 0 ?_
    intro j hj
    have hj' : j < 7 := by simpa using hj
    interval_cases j
    · exact (memGroupsOK_sound mem_ok15_0).2
    · have ho : (cumul (0:ℕ) [gl15_0, gl15_1, gl15_2, gl15_3, gl15_4, gl15_5, gl15_6]).getD 1 0 = 128 := by
        show (0 + (gl15_0).length) = 128
        rw [hL0]
      rw [ho]; exact (memGroupsOK_sound mem_ok15_1).2
    · have ho : (cumul (0:ℕ) [gl15_0, gl15_1, gl15_2, gl15_3, gl15_4, gl15_5, gl15_6]).getD 2 0 = 268 := by
        show ((0 + (gl15_0).length) + (gl15_1).length) = 268
        rw [hL0, hL1]
      rw [ho]; exact (memGroupsOK_sound mem_ok15_2).2
    · have ho : (cumul (0:ℕ) [gl15_0, gl15_1, gl15_2, gl15_3, gl15_4, gl15_5, gl15_6]).getD 3 0 = 367 := by
        show (((0 + (gl15_0).length) + (gl15_1).length) + (gl15_2).length) = 367
        rw [hL0, hL1, hL2]
      rw [ho]; exact (memGroupsOK_sound mem_ok15_3).2
    · have ho : (cumul (0:ℕ) [gl15_0, gl15_1, gl15_2, gl15_3, gl15_4, gl15_5, gl15_6]).getD 4 0 = 480 := by
        show ((((0 + (gl15_0).length) + (gl15_1).length) + (gl15_2).length) + (gl15_3).length) = 480
        rw [hL0, hL1, hL2, hL3]
      rw [ho]; exact (memGroupsOK_sound mem_ok15_4).2
    · have ho : (cumul (0:ℕ) [gl15_0, gl15_1, gl15_2, gl15_3, gl15_4, gl15_5, gl15_6]).getD 5 0 = 591 := by
        show (((((0 + (gl15_0).length) + (gl15_1).length) + (gl15_2).length) + (gl15_3).length) + (gl15_4).length) = 591
        rw [hL0, hL1, hL2, hL3, hL4]
      rw [ho]; exact (memGroupsOK_sound mem_ok15_5).2
    · have ho : (cumul (0:ℕ) [gl15_0, gl15_1, gl15_2, gl15_3, gl15_4, gl15_5, gl15_6]).getD 6 0 = 657 := by
        show ((((((0 + (gl15_0).length) + (gl15_1).length) + (gl15_2).length) + (gl15_3).length) + (gl15_4).length) + (gl15_5).length) = 657
        rw [hL0, hL1, hL2, hL3, hL4, hL5]
      rw [ho]; exact (memGroupsOK_sound mem_ok15_6).2
  have hmap : ([gl15_0, gl15_1, gl15_2, gl15_3, gl15_4, gl15_5, gl15_6].map (fun l => l.map List.length)) = [gsz15_0, gsz15_1, gsz15_2, gsz15_3, gsz15_4, gsz15_5, gsz15_6] := by
    simp only [List.map_cons, List.map_nil, hm0, hm1, hm2, hm3, hm4, hm5, hm6]
  have hGsz : ([gl15_0, gl15_1, gl15_2, gl15_3, gl15_4, gl15_5, gl15_6].flatten).map List.length = sizes15 := by
    rw [hgsz, List.map_flatten, hmap]
  have hGlen : ([gl15_0, gl15_1, gl15_2, gl15_3, gl15_4, gl15_5, gl15_6].flatten).length = ngE 15 := by
    rw [show ([gl15_0, gl15_1, gl15_2, gl15_3, gl15_4, gl15_5, gl15_6].flatten).length = (([gl15_0, gl15_1, gl15_2, gl15_3, gl15_4, gl15_5, gl15_6].flatten).map List.length).length from
      (List.length_map List.length).symm, hGsz]
    exact hszlen
  have hsum : (([gl15_0, gl15_1, gl15_2, gl15_3, gl15_4, gl15_5, gl15_6].flatten).flatten).length = 4641 := by
    rw [List.length_flatten, hGsz, ← sumL_eq_sum]; exact hs_ok.1
  have hrep : ∀ g < ngE 15, cG grepT15 g ∈ eAll ∧ lG labT15 (cG grepT15 g) = g := by
    intro g hg
    have h := grepOK_sound grep_ok15 g hg
    exact ⟨Work.PTCert.NSemAux.mem_eAll_of_em_ne_zero h.1 h.2.1, h.2.2⟩
  have hStabLen : (stabL 15).length = 16 := by
    have h := stablen_ok15
    rw [Nat.beq_eq] at h
    exact h
  have hstab : ∀ s < (stabL 15).length, ∀ k < 81, lk (stabT15.get s) k < 81 := by
    intro s hs k hk
    obtain ⟨pc, sc, hpc, htab⟩ := tabsOK_sound stabtab_ok15 s hs
    rw [htab k hk]
    exact Work.PTCert.codeFactsAux.actLBound pc sc hpc k hk
  have hssrange : [[0,1], [2,3], [4,5], [6,7], [8,9], [10,11], [12,13], [14,15]].flatten = List.range 16 := by decide
  have hclos : ∀ s < (stabL 15).length, ∀ g < ngE 15,
      lG labT15 (actC cmT (stabT15.get s) (cG grepT15 g)) = g := by
    intro s hs g hg
    have hs' : s ∈ [[0,1], [2,3], [4,5], [6,7], [8,9], [10,11], [12,13], [14,15]].flatten := by
      rw [hssrange, List.mem_range]; rwa [hStabLen] at hs
    exact closOK_flatten_spec (chunks := [[0,1], [2,3], [4,5], [6,7], [8,9], [10,11], [12,13], [14,15]]) (gs := List.range (ngE 15))
      (fun j hj => by
        have hj' : j < 8 := by simpa using hj
        interval_cases j
        · exact clos_ok15_0
        · exact clos_ok15_1
        · exact clos_ok15_2
        · exact clos_ok15_3
        · exact clos_ok15_4
        · exact clos_ok15_5
        · exact clos_ok15_6
        · exact clos_ok15_7
        )
      g (List.mem_range.mpr hg) s hs'
  have hidx : ∀ i < ([gl15_0, gl15_1, gl15_2, gl15_3, gl15_4, gl15_5, gl15_6].flatten).length, ∀ v ∈ ([gl15_0, gl15_1, gl15_2, gl15_3, gl15_4, gl15_5, gl15_6].flatten).getD i [],
      v % 4096 < (stabL 15).length := by
    intro i hi v hv
    have hmem : ([gl15_0, gl15_1, gl15_2, gl15_3, gl15_4, gl15_5, gl15_6].flatten).getD i [] ∈ ([gl15_0, gl15_1, gl15_2, gl15_3, gl15_4, gl15_5, gl15_6].flatten) := getD_mem hi
    have h := memIdxOK_flatten_spec (chunks := [gl15_0, gl15_1, gl15_2, gl15_3, gl15_4, gl15_5, gl15_6]) (ns := 16)
      (fun j hj => by
        have hj' : j < 7 := by simpa using hj
        interval_cases j
        · exact memidx_ok15_0
        · exact memidx_ok15_1
        · exact memidx_ok15_2
        · exact memidx_ok15_3
        · exact memidx_ok15_4
        · exact memidx_ok15_5
        · exact memidx_ok15_6
        ) _ hmem v hv
    rwa [hStabLen]
  exact genericGroups labT15 stabT15 grepT15 (stabL15) (sizes15) ([gl15_0, gl15_1, gl15_2, gl15_3, gl15_4, gl15_5, gl15_6].flatten) (ngE 15)
    hG hGsz hGlen hszlen hsum hrep hstab hclos hidx

theorem row16 :
    (∀ z ∈ eAll, labE 16 z < ngE 16 ∧ ∃ i < (stabL 16).length,
        actC cmT (stabTab 16 i) (grepE 16 (labE 16 z)) = z) ∧
    (∀ g < ngE 16, grepE 16 g ∈ eAll ∧ labE 16 (grepE 16 g) = g) ∧
    (∀ i < (stabL 16).length, ∀ g < ngE 16,
        labE 16 (actC cmT (stabTab 16 i) (grepE 16 g)) = g) ∧
    (∀ g < ngE 16, (eAll.filter (fun z => labE 16 z = g)).length = sizeE 16 g) ∧
    (sizesL.getD 16 []).length = ngE 16 := by
  have hs_ok : sumL sizes16 = 4641 ∧ sizes16.length = ngE 16 := by
    have h := sizes_ok16
    rw [Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    rw [Nat.beq_eq] at h1
    rw [decide_eq_true_eq, Nat.beq_eq] at h2
    exact ⟨h1, h2⟩
  have hszlen : sizes16.length = ngE 16 := hs_ok.2
  have hm0 : gl16_0.map List.length = gsz16_0 := (memGroupsOK_sound mem_ok16_0).1
  have hm1 : gl16_1.map List.length = gsz16_1 := (memGroupsOK_sound mem_ok16_1).1
  have hm2 : gl16_2.map List.length = gsz16_2 := (memGroupsOK_sound mem_ok16_2).1
  have hm3 : gl16_3.map List.length = gsz16_3 := (memGroupsOK_sound mem_ok16_3).1
  have hm4 : gl16_4.map List.length = gsz16_4 := (memGroupsOK_sound mem_ok16_4).1
  have hm5 : gl16_5.map List.length = gsz16_5 := (memGroupsOK_sound mem_ok16_5).1
  have hm6 : gl16_6.map List.length = gsz16_6 := (memGroupsOK_sound mem_ok16_6).1
  have hL0 : (gl16_0).length = 120 := by decide
  have hL1 : (gl16_1).length = 132 := by decide
  have hL2 : (gl16_2).length = 94 := by decide
  have hL3 : (gl16_3).length = 110 := by decide
  have hL4 : (gl16_4).length = 104 := by decide
  have hL5 : (gl16_5).length = 67 := by decide
  have hgsz : sizes16 = [gsz16_0, gsz16_1, gsz16_2, gsz16_3, gsz16_4, gsz16_5, gsz16_6].flatten := by
    rw [eqL_eq.mp gsz_ok16]
    rfl
  have hG : GroupsAt cmT eM labT16 stabT16 grepT16 [gl16_0, gl16_1, gl16_2, gl16_3, gl16_4, gl16_5, gl16_6].flatten 0 := by
    refine GroupsAt_cumul _ 0 ?_
    intro j hj
    have hj' : j < 7 := by simpa using hj
    interval_cases j
    · exact (memGroupsOK_sound mem_ok16_0).2
    · have ho : (cumul (0:ℕ) [gl16_0, gl16_1, gl16_2, gl16_3, gl16_4, gl16_5, gl16_6]).getD 1 0 = 120 := by
        show (0 + (gl16_0).length) = 120
        rw [hL0]
      rw [ho]; exact (memGroupsOK_sound mem_ok16_1).2
    · have ho : (cumul (0:ℕ) [gl16_0, gl16_1, gl16_2, gl16_3, gl16_4, gl16_5, gl16_6]).getD 2 0 = 252 := by
        show ((0 + (gl16_0).length) + (gl16_1).length) = 252
        rw [hL0, hL1]
      rw [ho]; exact (memGroupsOK_sound mem_ok16_2).2
    · have ho : (cumul (0:ℕ) [gl16_0, gl16_1, gl16_2, gl16_3, gl16_4, gl16_5, gl16_6]).getD 3 0 = 346 := by
        show (((0 + (gl16_0).length) + (gl16_1).length) + (gl16_2).length) = 346
        rw [hL0, hL1, hL2]
      rw [ho]; exact (memGroupsOK_sound mem_ok16_3).2
    · have ho : (cumul (0:ℕ) [gl16_0, gl16_1, gl16_2, gl16_3, gl16_4, gl16_5, gl16_6]).getD 4 0 = 456 := by
        show ((((0 + (gl16_0).length) + (gl16_1).length) + (gl16_2).length) + (gl16_3).length) = 456
        rw [hL0, hL1, hL2, hL3]
      rw [ho]; exact (memGroupsOK_sound mem_ok16_4).2
    · have ho : (cumul (0:ℕ) [gl16_0, gl16_1, gl16_2, gl16_3, gl16_4, gl16_5, gl16_6]).getD 5 0 = 560 := by
        show (((((0 + (gl16_0).length) + (gl16_1).length) + (gl16_2).length) + (gl16_3).length) + (gl16_4).length) = 560
        rw [hL0, hL1, hL2, hL3, hL4]
      rw [ho]; exact (memGroupsOK_sound mem_ok16_5).2
    · have ho : (cumul (0:ℕ) [gl16_0, gl16_1, gl16_2, gl16_3, gl16_4, gl16_5, gl16_6]).getD 6 0 = 627 := by
        show ((((((0 + (gl16_0).length) + (gl16_1).length) + (gl16_2).length) + (gl16_3).length) + (gl16_4).length) + (gl16_5).length) = 627
        rw [hL0, hL1, hL2, hL3, hL4, hL5]
      rw [ho]; exact (memGroupsOK_sound mem_ok16_6).2
  have hmap : ([gl16_0, gl16_1, gl16_2, gl16_3, gl16_4, gl16_5, gl16_6].map (fun l => l.map List.length)) = [gsz16_0, gsz16_1, gsz16_2, gsz16_3, gsz16_4, gsz16_5, gsz16_6] := by
    simp only [List.map_cons, List.map_nil, hm0, hm1, hm2, hm3, hm4, hm5, hm6]
  have hGsz : ([gl16_0, gl16_1, gl16_2, gl16_3, gl16_4, gl16_5, gl16_6].flatten).map List.length = sizes16 := by
    rw [hgsz, List.map_flatten, hmap]
  have hGlen : ([gl16_0, gl16_1, gl16_2, gl16_3, gl16_4, gl16_5, gl16_6].flatten).length = ngE 16 := by
    rw [show ([gl16_0, gl16_1, gl16_2, gl16_3, gl16_4, gl16_5, gl16_6].flatten).length = (([gl16_0, gl16_1, gl16_2, gl16_3, gl16_4, gl16_5, gl16_6].flatten).map List.length).length from
      (List.length_map List.length).symm, hGsz]
    exact hszlen
  have hsum : (([gl16_0, gl16_1, gl16_2, gl16_3, gl16_4, gl16_5, gl16_6].flatten).flatten).length = 4641 := by
    rw [List.length_flatten, hGsz, ← sumL_eq_sum]; exact hs_ok.1
  have hrep : ∀ g < ngE 16, cG grepT16 g ∈ eAll ∧ lG labT16 (cG grepT16 g) = g := by
    intro g hg
    have h := grepOK_sound grep_ok16 g hg
    exact ⟨Work.PTCert.NSemAux.mem_eAll_of_em_ne_zero h.1 h.2.1, h.2.2⟩
  have hStabLen : (stabL 16).length = 16 := by
    have h := stablen_ok16
    rw [Nat.beq_eq] at h
    exact h
  have hstab : ∀ s < (stabL 16).length, ∀ k < 81, lk (stabT16.get s) k < 81 := by
    intro s hs k hk
    obtain ⟨pc, sc, hpc, htab⟩ := tabsOK_sound stabtab_ok16 s hs
    rw [htab k hk]
    exact Work.PTCert.codeFactsAux.actLBound pc sc hpc k hk
  have hssrange : [[0,1], [2,3], [4,5], [6,7], [8,9], [10,11], [12,13], [14,15]].flatten = List.range 16 := by decide
  have hclos : ∀ s < (stabL 16).length, ∀ g < ngE 16,
      lG labT16 (actC cmT (stabT16.get s) (cG grepT16 g)) = g := by
    intro s hs g hg
    have hs' : s ∈ [[0,1], [2,3], [4,5], [6,7], [8,9], [10,11], [12,13], [14,15]].flatten := by
      rw [hssrange, List.mem_range]; rwa [hStabLen] at hs
    exact closOK_flatten_spec (chunks := [[0,1], [2,3], [4,5], [6,7], [8,9], [10,11], [12,13], [14,15]]) (gs := List.range (ngE 16))
      (fun j hj => by
        have hj' : j < 8 := by simpa using hj
        interval_cases j
        · exact clos_ok16_0
        · exact clos_ok16_1
        · exact clos_ok16_2
        · exact clos_ok16_3
        · exact clos_ok16_4
        · exact clos_ok16_5
        · exact clos_ok16_6
        · exact clos_ok16_7
        )
      g (List.mem_range.mpr hg) s hs'
  have hidx : ∀ i < ([gl16_0, gl16_1, gl16_2, gl16_3, gl16_4, gl16_5, gl16_6].flatten).length, ∀ v ∈ ([gl16_0, gl16_1, gl16_2, gl16_3, gl16_4, gl16_5, gl16_6].flatten).getD i [],
      v % 4096 < (stabL 16).length := by
    intro i hi v hv
    have hmem : ([gl16_0, gl16_1, gl16_2, gl16_3, gl16_4, gl16_5, gl16_6].flatten).getD i [] ∈ ([gl16_0, gl16_1, gl16_2, gl16_3, gl16_4, gl16_5, gl16_6].flatten) := getD_mem hi
    have h := memIdxOK_flatten_spec (chunks := [gl16_0, gl16_1, gl16_2, gl16_3, gl16_4, gl16_5, gl16_6]) (ns := 16)
      (fun j hj => by
        have hj' : j < 7 := by simpa using hj
        interval_cases j
        · exact memidx_ok16_0
        · exact memidx_ok16_1
        · exact memidx_ok16_2
        · exact memidx_ok16_3
        · exact memidx_ok16_4
        · exact memidx_ok16_5
        · exact memidx_ok16_6
        ) _ hmem v hv
    rwa [hStabLen]
  exact genericGroups labT16 stabT16 grepT16 (stabL16) (sizes16) ([gl16_0, gl16_1, gl16_2, gl16_3, gl16_4, gl16_5, gl16_6].flatten) (ngE 16)
    hG hGsz hGlen hszlen hsum hrep hstab hclos hidx

theorem row17 :
    (∀ z ∈ eAll, labE 17 z < ngE 17 ∧ ∃ i < (stabL 17).length,
        actC cmT (stabTab 17 i) (grepE 17 (labE 17 z)) = z) ∧
    (∀ g < ngE 17, grepE 17 g ∈ eAll ∧ labE 17 (grepE 17 g) = g) ∧
    (∀ i < (stabL 17).length, ∀ g < ngE 17,
        labE 17 (actC cmT (stabTab 17 i) (grepE 17 g)) = g) ∧
    (∀ g < ngE 17, (eAll.filter (fun z => labE 17 z = g)).length = sizeE 17 g) ∧
    (sizesL.getD 17 []).length = ngE 17 := by
  have hs_ok : sumL sizes17 = 4641 ∧ sizes17.length = ngE 17 := by
    have h := sizes_ok17
    rw [Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    rw [Nat.beq_eq] at h1
    rw [decide_eq_true_eq, Nat.beq_eq] at h2
    exact ⟨h1, h2⟩
  have hszlen : sizes17.length = ngE 17 := hs_ok.2
  have hm0 : gl17_0.map List.length = gsz17_0 := (memGroupsOK_sound mem_ok17_0).1
  have hm1 : gl17_1.map List.length = gsz17_1 := (memGroupsOK_sound mem_ok17_1).1
  have hm2 : gl17_2.map List.length = gsz17_2 := (memGroupsOK_sound mem_ok17_2).1
  have hm3 : gl17_3.map List.length = gsz17_3 := (memGroupsOK_sound mem_ok17_3).1
  have hm4 : gl17_4.map List.length = gsz17_4 := (memGroupsOK_sound mem_ok17_4).1
  have hm5 : gl17_5.map List.length = gsz17_5 := (memGroupsOK_sound mem_ok17_5).1
  have hm6 : gl17_6.map List.length = gsz17_6 := (memGroupsOK_sound mem_ok17_6).1
  have hL0 : (gl17_0).length = 256 := by decide
  have hL1 : (gl17_1).length = 254 := by decide
  have hL2 : (gl17_2).length = 247 := by decide
  have hL3 : (gl17_3).length = 247 := by decide
  have hL4 : (gl17_4).length = 249 := by decide
  have hL5 : (gl17_5).length = 201 := by decide
  have hgsz : sizes17 = [gsz17_0, gsz17_1, gsz17_2, gsz17_3, gsz17_4, gsz17_5, gsz17_6].flatten := by
    rw [eqL_eq.mp gsz_ok17]
    rfl
  have hG : GroupsAt cmT eM labT17 stabT17 grepT17 [gl17_0, gl17_1, gl17_2, gl17_3, gl17_4, gl17_5, gl17_6].flatten 0 := by
    refine GroupsAt_cumul _ 0 ?_
    intro j hj
    have hj' : j < 7 := by simpa using hj
    interval_cases j
    · exact (memGroupsOK_sound mem_ok17_0).2
    · have ho : (cumul (0:ℕ) [gl17_0, gl17_1, gl17_2, gl17_3, gl17_4, gl17_5, gl17_6]).getD 1 0 = 256 := by
        show (0 + (gl17_0).length) = 256
        rw [hL0]
      rw [ho]; exact (memGroupsOK_sound mem_ok17_1).2
    · have ho : (cumul (0:ℕ) [gl17_0, gl17_1, gl17_2, gl17_3, gl17_4, gl17_5, gl17_6]).getD 2 0 = 510 := by
        show ((0 + (gl17_0).length) + (gl17_1).length) = 510
        rw [hL0, hL1]
      rw [ho]; exact (memGroupsOK_sound mem_ok17_2).2
    · have ho : (cumul (0:ℕ) [gl17_0, gl17_1, gl17_2, gl17_3, gl17_4, gl17_5, gl17_6]).getD 3 0 = 757 := by
        show (((0 + (gl17_0).length) + (gl17_1).length) + (gl17_2).length) = 757
        rw [hL0, hL1, hL2]
      rw [ho]; exact (memGroupsOK_sound mem_ok17_3).2
    · have ho : (cumul (0:ℕ) [gl17_0, gl17_1, gl17_2, gl17_3, gl17_4, gl17_5, gl17_6]).getD 4 0 = 1004 := by
        show ((((0 + (gl17_0).length) + (gl17_1).length) + (gl17_2).length) + (gl17_3).length) = 1004
        rw [hL0, hL1, hL2, hL3]
      rw [ho]; exact (memGroupsOK_sound mem_ok17_4).2
    · have ho : (cumul (0:ℕ) [gl17_0, gl17_1, gl17_2, gl17_3, gl17_4, gl17_5, gl17_6]).getD 5 0 = 1253 := by
        show (((((0 + (gl17_0).length) + (gl17_1).length) + (gl17_2).length) + (gl17_3).length) + (gl17_4).length) = 1253
        rw [hL0, hL1, hL2, hL3, hL4]
      rw [ho]; exact (memGroupsOK_sound mem_ok17_5).2
    · have ho : (cumul (0:ℕ) [gl17_0, gl17_1, gl17_2, gl17_3, gl17_4, gl17_5, gl17_6]).getD 6 0 = 1454 := by
        show ((((((0 + (gl17_0).length) + (gl17_1).length) + (gl17_2).length) + (gl17_3).length) + (gl17_4).length) + (gl17_5).length) = 1454
        rw [hL0, hL1, hL2, hL3, hL4, hL5]
      rw [ho]; exact (memGroupsOK_sound mem_ok17_6).2
  have hmap : ([gl17_0, gl17_1, gl17_2, gl17_3, gl17_4, gl17_5, gl17_6].map (fun l => l.map List.length)) = [gsz17_0, gsz17_1, gsz17_2, gsz17_3, gsz17_4, gsz17_5, gsz17_6] := by
    simp only [List.map_cons, List.map_nil, hm0, hm1, hm2, hm3, hm4, hm5, hm6]
  have hGsz : ([gl17_0, gl17_1, gl17_2, gl17_3, gl17_4, gl17_5, gl17_6].flatten).map List.length = sizes17 := by
    rw [hgsz, List.map_flatten, hmap]
  have hGlen : ([gl17_0, gl17_1, gl17_2, gl17_3, gl17_4, gl17_5, gl17_6].flatten).length = ngE 17 := by
    rw [show ([gl17_0, gl17_1, gl17_2, gl17_3, gl17_4, gl17_5, gl17_6].flatten).length = (([gl17_0, gl17_1, gl17_2, gl17_3, gl17_4, gl17_5, gl17_6].flatten).map List.length).length from
      (List.length_map List.length).symm, hGsz]
    exact hszlen
  have hsum : (([gl17_0, gl17_1, gl17_2, gl17_3, gl17_4, gl17_5, gl17_6].flatten).flatten).length = 4641 := by
    rw [List.length_flatten, hGsz, ← sumL_eq_sum]; exact hs_ok.1
  have hrep : ∀ g < ngE 17, cG grepT17 g ∈ eAll ∧ lG labT17 (cG grepT17 g) = g := by
    intro g hg
    have h := grepOK_sound grep_ok17 g hg
    exact ⟨Work.PTCert.NSemAux.mem_eAll_of_em_ne_zero h.1 h.2.1, h.2.2⟩
  have hStabLen : (stabL 17).length = 4 := by
    have h := stablen_ok17
    rw [Nat.beq_eq] at h
    exact h
  have hstab : ∀ s < (stabL 17).length, ∀ k < 81, lk (stabT17.get s) k < 81 := by
    intro s hs k hk
    obtain ⟨pc, sc, hpc, htab⟩ := tabsOK_sound stabtab_ok17 s hs
    rw [htab k hk]
    exact Work.PTCert.codeFactsAux.actLBound pc sc hpc k hk
  have hssrange : [[0], [1], [2], [3]].flatten = List.range 4 := by decide
  have hclos : ∀ s < (stabL 17).length, ∀ g < ngE 17,
      lG labT17 (actC cmT (stabT17.get s) (cG grepT17 g)) = g := by
    intro s hs g hg
    have hs' : s ∈ [[0], [1], [2], [3]].flatten := by
      rw [hssrange, List.mem_range]; rwa [hStabLen] at hs
    exact closOK_flatten_spec (chunks := [[0], [1], [2], [3]]) (gs := List.range (ngE 17))
      (fun j hj => by
        have hj' : j < 4 := by simpa using hj
        interval_cases j
        · exact clos_ok17_0
        · exact clos_ok17_1
        · exact clos_ok17_2
        · exact clos_ok17_3
        )
      g (List.mem_range.mpr hg) s hs'
  have hidx : ∀ i < ([gl17_0, gl17_1, gl17_2, gl17_3, gl17_4, gl17_5, gl17_6].flatten).length, ∀ v ∈ ([gl17_0, gl17_1, gl17_2, gl17_3, gl17_4, gl17_5, gl17_6].flatten).getD i [],
      v % 4096 < (stabL 17).length := by
    intro i hi v hv
    have hmem : ([gl17_0, gl17_1, gl17_2, gl17_3, gl17_4, gl17_5, gl17_6].flatten).getD i [] ∈ ([gl17_0, gl17_1, gl17_2, gl17_3, gl17_4, gl17_5, gl17_6].flatten) := getD_mem hi
    have h := memIdxOK_flatten_spec (chunks := [gl17_0, gl17_1, gl17_2, gl17_3, gl17_4, gl17_5, gl17_6]) (ns := 4)
      (fun j hj => by
        have hj' : j < 7 := by simpa using hj
        interval_cases j
        · exact memidx_ok17_0
        · exact memidx_ok17_1
        · exact memidx_ok17_2
        · exact memidx_ok17_3
        · exact memidx_ok17_4
        · exact memidx_ok17_5
        · exact memidx_ok17_6
        ) _ hmem v hv
    rwa [hStabLen]
  exact genericGroups labT17 stabT17 grepT17 (stabL17) (sizes17) ([gl17_0, gl17_1, gl17_2, gl17_3, gl17_4, gl17_5, gl17_6].flatten) (ngE 17)
    hG hGsz hGlen hszlen hsum hrep hstab hclos hidx

theorem groupSem : GroupSem := by
  refine ⟨?_, ?_, ?_⟩
  · rfl
  · intro g hg; rfl
  · intro r hr18 hr1
    interval_cases r
    · exact row1
    · exact row2
    · exact row3
    · exact row4
    · exact row5
    · exact row6
    · exact row7
    · exact row8
    · exact row9
    · exact row10
    · exact row11
    · exact row12
    · exact row13
    · exact row14
    · exact row15
    · exact row16
    · exact row17

end Work.PTCert
