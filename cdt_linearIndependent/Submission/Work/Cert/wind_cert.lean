import Mathlib
import Submission.Work.Cert.Spec
import Submission.Work.Cert.WindFinal
import Submission.Work.Cert.warcsOK_next
import Submission.Work.Cert.warcsOK_append
import Submission.Work.Cert.warcOK_facts

/-!
# `WindCertFacts` from the winding chunks

The lead-built certificate consists of the 46 chunks `arcsW000 … arcsW045` of `WChunks`, each
checking (`okW### : warcsOK … = true`) that its arcs form a `warcOK` chain from their own start to
the chunk end.  `WindFinal` supplies the linkage of the chunk ends (`wlink_ok`), the starting point
`(S,0)` (`wfirst_ok`), the ordering of the grid indices (`wj_ok`) and the label winding check
(`wlabels_ok`).

Here we glue the 46 chunk chains into a single chain `warcsOK S 0 allArcs`, extract the per-arc data
and package it as `WindCertFacts`.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Work.Cert

open Submission.CDTPlan
open Work.Cert.WChunks

/-! ## The 46 chunks glued into one chain -/

/-- the 46 winding chunks, in order. -/
def chunkList : List (List WArc) := [arcsW000, arcsW001, arcsW002, arcsW003, arcsW004, arcsW005, arcsW006, arcsW007, arcsW008, arcsW009, arcsW010, arcsW011, arcsW012, arcsW013, arcsW014, arcsW015, arcsW016, arcsW017, arcsW018, arcsW019, arcsW020, arcsW021, arcsW022, arcsW023, arcsW024, arcsW025, arcsW026, arcsW027, arcsW028, arcsW029, arcsW030, arcsW031, arcsW032, arcsW033, arcsW034, arcsW035, arcsW036, arcsW037, arcsW038, arcsW039, arcsW040, arcsW041, arcsW042, arcsW043, arcsW044, arcsW045]

/-- all winding arcs, in order. -/
def allArcs : List WArc := chunkList.foldr (· ++ ·) []

/-- the concatenation of the chunks `c … 45`. -/
def suf (c : ℕ) : List WArc := (chunkList.drop c).foldr (· ++ ·) []

theorem allArcs_unfold : allArcs = arcsW000 ++ suf 1 := rfl

/-- the two fold expressions for `allArcs` agree (associativity of `++`). -/
lemma foldl_append_eq (L : List (List WArc)) (init : List WArc) :
    L.foldl (· ++ ·) init = init ++ List.foldr (· ++ ·) [] L := by
  induction L generalizing init with
  | nil => exact (List.append_nil init).symm
  | cons a t ih =>
    rw [List.foldl_cons, ih (init ++ a), List.foldr_cons]
    exact List.append_assoc init a _

theorem warcsAll_eq_foldl : WFinal.warcsAll = chunkList.foldl (· ++ ·) [] := rfl

theorem allArcs_eq : allArcs = WFinal.warcsAll := by
  rw [warcsAll_eq_foldl, foldl_append_eq chunkList [], List.nil_append]
  rfl

theorem warcsAll_length : WFinal.warcsAll.length = 4096 := by
  have h := congrArg List.length WFinal.wj_ok
  simpa using h

theorem allArcs_length : allArcs.length = 4096 := by
  rw [allArcs_eq, warcsAll_length]

/-! ## The chunk junctions -/

/-- chunk 000 ends at the first grid point of the next chunk. -/
theorem hpt000 : (endW000.1, endW000.2) =
    ((suf 1).head?.map (fun a : WArc => (a.Ex, a.Ey))).getD (0, 0) := by decide
theorem hj000 : (arcsW000.getLast?.map (fun a : WArc => a.j)).getD 0 + 1 =
    ((suf 1).head?.map (fun a : WArc => a.j)).getD 0 := by decide

/-- chunk 001 ends at the first grid point of the next chunk. -/
theorem hpt001 : (endW001.1, endW001.2) =
    ((suf 2).head?.map (fun a : WArc => (a.Ex, a.Ey))).getD (0, 0) := by decide
theorem hj001 : (arcsW001.getLast?.map (fun a : WArc => a.j)).getD 0 + 1 =
    ((suf 2).head?.map (fun a : WArc => a.j)).getD 0 := by decide

/-- chunk 002 ends at the first grid point of the next chunk. -/
theorem hpt002 : (endW002.1, endW002.2) =
    ((suf 3).head?.map (fun a : WArc => (a.Ex, a.Ey))).getD (0, 0) := by decide
theorem hj002 : (arcsW002.getLast?.map (fun a : WArc => a.j)).getD 0 + 1 =
    ((suf 3).head?.map (fun a : WArc => a.j)).getD 0 := by decide

/-- chunk 003 ends at the first grid point of the next chunk. -/
theorem hpt003 : (endW003.1, endW003.2) =
    ((suf 4).head?.map (fun a : WArc => (a.Ex, a.Ey))).getD (0, 0) := by decide
theorem hj003 : (arcsW003.getLast?.map (fun a : WArc => a.j)).getD 0 + 1 =
    ((suf 4).head?.map (fun a : WArc => a.j)).getD 0 := by decide

/-- chunk 004 ends at the first grid point of the next chunk. -/
theorem hpt004 : (endW004.1, endW004.2) =
    ((suf 5).head?.map (fun a : WArc => (a.Ex, a.Ey))).getD (0, 0) := by decide
theorem hj004 : (arcsW004.getLast?.map (fun a : WArc => a.j)).getD 0 + 1 =
    ((suf 5).head?.map (fun a : WArc => a.j)).getD 0 := by decide

/-- chunk 005 ends at the first grid point of the next chunk. -/
theorem hpt005 : (endW005.1, endW005.2) =
    ((suf 6).head?.map (fun a : WArc => (a.Ex, a.Ey))).getD (0, 0) := by decide
theorem hj005 : (arcsW005.getLast?.map (fun a : WArc => a.j)).getD 0 + 1 =
    ((suf 6).head?.map (fun a : WArc => a.j)).getD 0 := by decide

/-- chunk 006 ends at the first grid point of the next chunk. -/
theorem hpt006 : (endW006.1, endW006.2) =
    ((suf 7).head?.map (fun a : WArc => (a.Ex, a.Ey))).getD (0, 0) := by decide
theorem hj006 : (arcsW006.getLast?.map (fun a : WArc => a.j)).getD 0 + 1 =
    ((suf 7).head?.map (fun a : WArc => a.j)).getD 0 := by decide

/-- chunk 007 ends at the first grid point of the next chunk. -/
theorem hpt007 : (endW007.1, endW007.2) =
    ((suf 8).head?.map (fun a : WArc => (a.Ex, a.Ey))).getD (0, 0) := by decide
theorem hj007 : (arcsW007.getLast?.map (fun a : WArc => a.j)).getD 0 + 1 =
    ((suf 8).head?.map (fun a : WArc => a.j)).getD 0 := by decide

/-- chunk 008 ends at the first grid point of the next chunk. -/
theorem hpt008 : (endW008.1, endW008.2) =
    ((suf 9).head?.map (fun a : WArc => (a.Ex, a.Ey))).getD (0, 0) := by decide
theorem hj008 : (arcsW008.getLast?.map (fun a : WArc => a.j)).getD 0 + 1 =
    ((suf 9).head?.map (fun a : WArc => a.j)).getD 0 := by decide

/-- chunk 009 ends at the first grid point of the next chunk. -/
theorem hpt009 : (endW009.1, endW009.2) =
    ((suf 10).head?.map (fun a : WArc => (a.Ex, a.Ey))).getD (0, 0) := by decide
theorem hj009 : (arcsW009.getLast?.map (fun a : WArc => a.j)).getD 0 + 1 =
    ((suf 10).head?.map (fun a : WArc => a.j)).getD 0 := by decide

/-- chunk 010 ends at the first grid point of the next chunk. -/
theorem hpt010 : (endW010.1, endW010.2) =
    ((suf 11).head?.map (fun a : WArc => (a.Ex, a.Ey))).getD (0, 0) := by decide
theorem hj010 : (arcsW010.getLast?.map (fun a : WArc => a.j)).getD 0 + 1 =
    ((suf 11).head?.map (fun a : WArc => a.j)).getD 0 := by decide

/-- chunk 011 ends at the first grid point of the next chunk. -/
theorem hpt011 : (endW011.1, endW011.2) =
    ((suf 12).head?.map (fun a : WArc => (a.Ex, a.Ey))).getD (0, 0) := by decide
theorem hj011 : (arcsW011.getLast?.map (fun a : WArc => a.j)).getD 0 + 1 =
    ((suf 12).head?.map (fun a : WArc => a.j)).getD 0 := by decide

/-- chunk 012 ends at the first grid point of the next chunk. -/
theorem hpt012 : (endW012.1, endW012.2) =
    ((suf 13).head?.map (fun a : WArc => (a.Ex, a.Ey))).getD (0, 0) := by decide
theorem hj012 : (arcsW012.getLast?.map (fun a : WArc => a.j)).getD 0 + 1 =
    ((suf 13).head?.map (fun a : WArc => a.j)).getD 0 := by decide

/-- chunk 013 ends at the first grid point of the next chunk. -/
theorem hpt013 : (endW013.1, endW013.2) =
    ((suf 14).head?.map (fun a : WArc => (a.Ex, a.Ey))).getD (0, 0) := by decide
theorem hj013 : (arcsW013.getLast?.map (fun a : WArc => a.j)).getD 0 + 1 =
    ((suf 14).head?.map (fun a : WArc => a.j)).getD 0 := by decide

/-- chunk 014 ends at the first grid point of the next chunk. -/
theorem hpt014 : (endW014.1, endW014.2) =
    ((suf 15).head?.map (fun a : WArc => (a.Ex, a.Ey))).getD (0, 0) := by decide
theorem hj014 : (arcsW014.getLast?.map (fun a : WArc => a.j)).getD 0 + 1 =
    ((suf 15).head?.map (fun a : WArc => a.j)).getD 0 := by decide

/-- chunk 015 ends at the first grid point of the next chunk. -/
theorem hpt015 : (endW015.1, endW015.2) =
    ((suf 16).head?.map (fun a : WArc => (a.Ex, a.Ey))).getD (0, 0) := by decide
theorem hj015 : (arcsW015.getLast?.map (fun a : WArc => a.j)).getD 0 + 1 =
    ((suf 16).head?.map (fun a : WArc => a.j)).getD 0 := by decide

/-- chunk 016 ends at the first grid point of the next chunk. -/
theorem hpt016 : (endW016.1, endW016.2) =
    ((suf 17).head?.map (fun a : WArc => (a.Ex, a.Ey))).getD (0, 0) := by decide
theorem hj016 : (arcsW016.getLast?.map (fun a : WArc => a.j)).getD 0 + 1 =
    ((suf 17).head?.map (fun a : WArc => a.j)).getD 0 := by decide

/-- chunk 017 ends at the first grid point of the next chunk. -/
theorem hpt017 : (endW017.1, endW017.2) =
    ((suf 18).head?.map (fun a : WArc => (a.Ex, a.Ey))).getD (0, 0) := by decide
theorem hj017 : (arcsW017.getLast?.map (fun a : WArc => a.j)).getD 0 + 1 =
    ((suf 18).head?.map (fun a : WArc => a.j)).getD 0 := by decide

/-- chunk 018 ends at the first grid point of the next chunk. -/
theorem hpt018 : (endW018.1, endW018.2) =
    ((suf 19).head?.map (fun a : WArc => (a.Ex, a.Ey))).getD (0, 0) := by decide
theorem hj018 : (arcsW018.getLast?.map (fun a : WArc => a.j)).getD 0 + 1 =
    ((suf 19).head?.map (fun a : WArc => a.j)).getD 0 := by decide

/-- chunk 019 ends at the first grid point of the next chunk. -/
theorem hpt019 : (endW019.1, endW019.2) =
    ((suf 20).head?.map (fun a : WArc => (a.Ex, a.Ey))).getD (0, 0) := by decide
theorem hj019 : (arcsW019.getLast?.map (fun a : WArc => a.j)).getD 0 + 1 =
    ((suf 20).head?.map (fun a : WArc => a.j)).getD 0 := by decide

/-- chunk 020 ends at the first grid point of the next chunk. -/
theorem hpt020 : (endW020.1, endW020.2) =
    ((suf 21).head?.map (fun a : WArc => (a.Ex, a.Ey))).getD (0, 0) := by decide
theorem hj020 : (arcsW020.getLast?.map (fun a : WArc => a.j)).getD 0 + 1 =
    ((suf 21).head?.map (fun a : WArc => a.j)).getD 0 := by decide

/-- chunk 021 ends at the first grid point of the next chunk. -/
theorem hpt021 : (endW021.1, endW021.2) =
    ((suf 22).head?.map (fun a : WArc => (a.Ex, a.Ey))).getD (0, 0) := by decide
theorem hj021 : (arcsW021.getLast?.map (fun a : WArc => a.j)).getD 0 + 1 =
    ((suf 22).head?.map (fun a : WArc => a.j)).getD 0 := by decide

/-- chunk 022 ends at the first grid point of the next chunk. -/
theorem hpt022 : (endW022.1, endW022.2) =
    ((suf 23).head?.map (fun a : WArc => (a.Ex, a.Ey))).getD (0, 0) := by decide
theorem hj022 : (arcsW022.getLast?.map (fun a : WArc => a.j)).getD 0 + 1 =
    ((suf 23).head?.map (fun a : WArc => a.j)).getD 0 := by decide

/-- chunk 023 ends at the first grid point of the next chunk. -/
theorem hpt023 : (endW023.1, endW023.2) =
    ((suf 24).head?.map (fun a : WArc => (a.Ex, a.Ey))).getD (0, 0) := by decide
theorem hj023 : (arcsW023.getLast?.map (fun a : WArc => a.j)).getD 0 + 1 =
    ((suf 24).head?.map (fun a : WArc => a.j)).getD 0 := by decide

/-- chunk 024 ends at the first grid point of the next chunk. -/
theorem hpt024 : (endW024.1, endW024.2) =
    ((suf 25).head?.map (fun a : WArc => (a.Ex, a.Ey))).getD (0, 0) := by decide
theorem hj024 : (arcsW024.getLast?.map (fun a : WArc => a.j)).getD 0 + 1 =
    ((suf 25).head?.map (fun a : WArc => a.j)).getD 0 := by decide

/-- chunk 025 ends at the first grid point of the next chunk. -/
theorem hpt025 : (endW025.1, endW025.2) =
    ((suf 26).head?.map (fun a : WArc => (a.Ex, a.Ey))).getD (0, 0) := by decide
theorem hj025 : (arcsW025.getLast?.map (fun a : WArc => a.j)).getD 0 + 1 =
    ((suf 26).head?.map (fun a : WArc => a.j)).getD 0 := by decide

/-- chunk 026 ends at the first grid point of the next chunk. -/
theorem hpt026 : (endW026.1, endW026.2) =
    ((suf 27).head?.map (fun a : WArc => (a.Ex, a.Ey))).getD (0, 0) := by decide
theorem hj026 : (arcsW026.getLast?.map (fun a : WArc => a.j)).getD 0 + 1 =
    ((suf 27).head?.map (fun a : WArc => a.j)).getD 0 := by decide

/-- chunk 027 ends at the first grid point of the next chunk. -/
theorem hpt027 : (endW027.1, endW027.2) =
    ((suf 28).head?.map (fun a : WArc => (a.Ex, a.Ey))).getD (0, 0) := by decide
theorem hj027 : (arcsW027.getLast?.map (fun a : WArc => a.j)).getD 0 + 1 =
    ((suf 28).head?.map (fun a : WArc => a.j)).getD 0 := by decide

/-- chunk 028 ends at the first grid point of the next chunk. -/
theorem hpt028 : (endW028.1, endW028.2) =
    ((suf 29).head?.map (fun a : WArc => (a.Ex, a.Ey))).getD (0, 0) := by decide
theorem hj028 : (arcsW028.getLast?.map (fun a : WArc => a.j)).getD 0 + 1 =
    ((suf 29).head?.map (fun a : WArc => a.j)).getD 0 := by decide

/-- chunk 029 ends at the first grid point of the next chunk. -/
theorem hpt029 : (endW029.1, endW029.2) =
    ((suf 30).head?.map (fun a : WArc => (a.Ex, a.Ey))).getD (0, 0) := by decide
theorem hj029 : (arcsW029.getLast?.map (fun a : WArc => a.j)).getD 0 + 1 =
    ((suf 30).head?.map (fun a : WArc => a.j)).getD 0 := by decide

/-- chunk 030 ends at the first grid point of the next chunk. -/
theorem hpt030 : (endW030.1, endW030.2) =
    ((suf 31).head?.map (fun a : WArc => (a.Ex, a.Ey))).getD (0, 0) := by decide
theorem hj030 : (arcsW030.getLast?.map (fun a : WArc => a.j)).getD 0 + 1 =
    ((suf 31).head?.map (fun a : WArc => a.j)).getD 0 := by decide

/-- chunk 031 ends at the first grid point of the next chunk. -/
theorem hpt031 : (endW031.1, endW031.2) =
    ((suf 32).head?.map (fun a : WArc => (a.Ex, a.Ey))).getD (0, 0) := by decide
theorem hj031 : (arcsW031.getLast?.map (fun a : WArc => a.j)).getD 0 + 1 =
    ((suf 32).head?.map (fun a : WArc => a.j)).getD 0 := by decide

/-- chunk 032 ends at the first grid point of the next chunk. -/
theorem hpt032 : (endW032.1, endW032.2) =
    ((suf 33).head?.map (fun a : WArc => (a.Ex, a.Ey))).getD (0, 0) := by decide
theorem hj032 : (arcsW032.getLast?.map (fun a : WArc => a.j)).getD 0 + 1 =
    ((suf 33).head?.map (fun a : WArc => a.j)).getD 0 := by decide

/-- chunk 033 ends at the first grid point of the next chunk. -/
theorem hpt033 : (endW033.1, endW033.2) =
    ((suf 34).head?.map (fun a : WArc => (a.Ex, a.Ey))).getD (0, 0) := by decide
theorem hj033 : (arcsW033.getLast?.map (fun a : WArc => a.j)).getD 0 + 1 =
    ((suf 34).head?.map (fun a : WArc => a.j)).getD 0 := by decide

/-- chunk 034 ends at the first grid point of the next chunk. -/
theorem hpt034 : (endW034.1, endW034.2) =
    ((suf 35).head?.map (fun a : WArc => (a.Ex, a.Ey))).getD (0, 0) := by decide
theorem hj034 : (arcsW034.getLast?.map (fun a : WArc => a.j)).getD 0 + 1 =
    ((suf 35).head?.map (fun a : WArc => a.j)).getD 0 := by decide

/-- chunk 035 ends at the first grid point of the next chunk. -/
theorem hpt035 : (endW035.1, endW035.2) =
    ((suf 36).head?.map (fun a : WArc => (a.Ex, a.Ey))).getD (0, 0) := by decide
theorem hj035 : (arcsW035.getLast?.map (fun a : WArc => a.j)).getD 0 + 1 =
    ((suf 36).head?.map (fun a : WArc => a.j)).getD 0 := by decide

/-- chunk 036 ends at the first grid point of the next chunk. -/
theorem hpt036 : (endW036.1, endW036.2) =
    ((suf 37).head?.map (fun a : WArc => (a.Ex, a.Ey))).getD (0, 0) := by decide
theorem hj036 : (arcsW036.getLast?.map (fun a : WArc => a.j)).getD 0 + 1 =
    ((suf 37).head?.map (fun a : WArc => a.j)).getD 0 := by decide

/-- chunk 037 ends at the first grid point of the next chunk. -/
theorem hpt037 : (endW037.1, endW037.2) =
    ((suf 38).head?.map (fun a : WArc => (a.Ex, a.Ey))).getD (0, 0) := by decide
theorem hj037 : (arcsW037.getLast?.map (fun a : WArc => a.j)).getD 0 + 1 =
    ((suf 38).head?.map (fun a : WArc => a.j)).getD 0 := by decide

/-- chunk 038 ends at the first grid point of the next chunk. -/
theorem hpt038 : (endW038.1, endW038.2) =
    ((suf 39).head?.map (fun a : WArc => (a.Ex, a.Ey))).getD (0, 0) := by decide
theorem hj038 : (arcsW038.getLast?.map (fun a : WArc => a.j)).getD 0 + 1 =
    ((suf 39).head?.map (fun a : WArc => a.j)).getD 0 := by decide

/-- chunk 039 ends at the first grid point of the next chunk. -/
theorem hpt039 : (endW039.1, endW039.2) =
    ((suf 40).head?.map (fun a : WArc => (a.Ex, a.Ey))).getD (0, 0) := by decide
theorem hj039 : (arcsW039.getLast?.map (fun a : WArc => a.j)).getD 0 + 1 =
    ((suf 40).head?.map (fun a : WArc => a.j)).getD 0 := by decide

/-- chunk 040 ends at the first grid point of the next chunk. -/
theorem hpt040 : (endW040.1, endW040.2) =
    ((suf 41).head?.map (fun a : WArc => (a.Ex, a.Ey))).getD (0, 0) := by decide
theorem hj040 : (arcsW040.getLast?.map (fun a : WArc => a.j)).getD 0 + 1 =
    ((suf 41).head?.map (fun a : WArc => a.j)).getD 0 := by decide

/-- chunk 041 ends at the first grid point of the next chunk. -/
theorem hpt041 : (endW041.1, endW041.2) =
    ((suf 42).head?.map (fun a : WArc => (a.Ex, a.Ey))).getD (0, 0) := by decide
theorem hj041 : (arcsW041.getLast?.map (fun a : WArc => a.j)).getD 0 + 1 =
    ((suf 42).head?.map (fun a : WArc => a.j)).getD 0 := by decide

/-- chunk 042 ends at the first grid point of the next chunk. -/
theorem hpt042 : (endW042.1, endW042.2) =
    ((suf 43).head?.map (fun a : WArc => (a.Ex, a.Ey))).getD (0, 0) := by decide
theorem hj042 : (arcsW042.getLast?.map (fun a : WArc => a.j)).getD 0 + 1 =
    ((suf 43).head?.map (fun a : WArc => a.j)).getD 0 := by decide

/-- chunk 043 ends at the first grid point of the next chunk. -/
theorem hpt043 : (endW043.1, endW043.2) =
    ((suf 44).head?.map (fun a : WArc => (a.Ex, a.Ey))).getD (0, 0) := by decide
theorem hj043 : (arcsW043.getLast?.map (fun a : WArc => a.j)).getD 0 + 1 =
    ((suf 44).head?.map (fun a : WArc => a.j)).getD 0 := by decide

/-- chunk 044 ends at the first grid point of the next chunk. -/
theorem hpt044 : (endW044.1, endW044.2) =
    ((suf 45).head?.map (fun a : WArc => (a.Ex, a.Ey))).getD (0, 0) := by decide
theorem hj044 : (arcsW044.getLast?.map (fun a : WArc => a.j)).getD 0 + 1 =
    ((suf 45).head?.map (fun a : WArc => a.j)).getD 0 := by decide

/-! ## Gluing -/

theorem suf_last : suf 45 = arcsW045 := List.append_nil _

theorem allArcs_warcsOK : warcsOK S 0 allArcs = true := by
  have h045 : warcsOK S 0 (suf 45) = true := by
    have h : (S, 0) = (endW045.1, endW045.2) := by decide
    rw [suf_last, show S = endW045.1 from (congrArg Prod.fst h).symm,
        show (0 : ℤ) = endW045.2 from (congrArg Prod.snd h).symm]
    exact okW045
  have h044 : warcsOK S 0 (suf 44) = true := by
    have hp := hpt044
    have hne : suf 45 ≠ [] := by
      intro h
      rw [h] at hp
      simp at hp
      exact (by decide : (endW044.1, endW044.2) ≠ (0, 0)) hp
    exact warcsOK_append arcsW044 (suf 45) endW044.1 endW044.2 S 0
      okW044 h045 hne hpt044 hj044
  have h043 : warcsOK S 0 (suf 43) = true := by
    have hp := hpt043
    have hne : suf 44 ≠ [] := by
      intro h
      rw [h] at hp
      simp at hp
      exact (by decide : (endW043.1, endW043.2) ≠ (0, 0)) hp
    exact warcsOK_append arcsW043 (suf 44) endW043.1 endW043.2 S 0
      okW043 h044 hne hpt043 hj043
  have h042 : warcsOK S 0 (suf 42) = true := by
    have hp := hpt042
    have hne : suf 43 ≠ [] := by
      intro h
      rw [h] at hp
      simp at hp
      exact (by decide : (endW042.1, endW042.2) ≠ (0, 0)) hp
    exact warcsOK_append arcsW042 (suf 43) endW042.1 endW042.2 S 0
      okW042 h043 hne hpt042 hj042
  have h041 : warcsOK S 0 (suf 41) = true := by
    have hp := hpt041
    have hne : suf 42 ≠ [] := by
      intro h
      rw [h] at hp
      simp at hp
      exact (by decide : (endW041.1, endW041.2) ≠ (0, 0)) hp
    exact warcsOK_append arcsW041 (suf 42) endW041.1 endW041.2 S 0
      okW041 h042 hne hpt041 hj041
  have h040 : warcsOK S 0 (suf 40) = true := by
    have hp := hpt040
    have hne : suf 41 ≠ [] := by
      intro h
      rw [h] at hp
      simp at hp
      exact (by decide : (endW040.1, endW040.2) ≠ (0, 0)) hp
    exact warcsOK_append arcsW040 (suf 41) endW040.1 endW040.2 S 0
      okW040 h041 hne hpt040 hj040
  have h039 : warcsOK S 0 (suf 39) = true := by
    have hp := hpt039
    have hne : suf 40 ≠ [] := by
      intro h
      rw [h] at hp
      simp at hp
      exact (by decide : (endW039.1, endW039.2) ≠ (0, 0)) hp
    exact warcsOK_append arcsW039 (suf 40) endW039.1 endW039.2 S 0
      okW039 h040 hne hpt039 hj039
  have h038 : warcsOK S 0 (suf 38) = true := by
    have hp := hpt038
    have hne : suf 39 ≠ [] := by
      intro h
      rw [h] at hp
      simp at hp
      exact (by decide : (endW038.1, endW038.2) ≠ (0, 0)) hp
    exact warcsOK_append arcsW038 (suf 39) endW038.1 endW038.2 S 0
      okW038 h039 hne hpt038 hj038
  have h037 : warcsOK S 0 (suf 37) = true := by
    have hp := hpt037
    have hne : suf 38 ≠ [] := by
      intro h
      rw [h] at hp
      simp at hp
      exact (by decide : (endW037.1, endW037.2) ≠ (0, 0)) hp
    exact warcsOK_append arcsW037 (suf 38) endW037.1 endW037.2 S 0
      okW037 h038 hne hpt037 hj037
  have h036 : warcsOK S 0 (suf 36) = true := by
    have hp := hpt036
    have hne : suf 37 ≠ [] := by
      intro h
      rw [h] at hp
      simp at hp
      exact (by decide : (endW036.1, endW036.2) ≠ (0, 0)) hp
    exact warcsOK_append arcsW036 (suf 37) endW036.1 endW036.2 S 0
      okW036 h037 hne hpt036 hj036
  have h035 : warcsOK S 0 (suf 35) = true := by
    have hp := hpt035
    have hne : suf 36 ≠ [] := by
      intro h
      rw [h] at hp
      simp at hp
      exact (by decide : (endW035.1, endW035.2) ≠ (0, 0)) hp
    exact warcsOK_append arcsW035 (suf 36) endW035.1 endW035.2 S 0
      okW035 h036 hne hpt035 hj035
  have h034 : warcsOK S 0 (suf 34) = true := by
    have hp := hpt034
    have hne : suf 35 ≠ [] := by
      intro h
      rw [h] at hp
      simp at hp
      exact (by decide : (endW034.1, endW034.2) ≠ (0, 0)) hp
    exact warcsOK_append arcsW034 (suf 35) endW034.1 endW034.2 S 0
      okW034 h035 hne hpt034 hj034
  have h033 : warcsOK S 0 (suf 33) = true := by
    have hp := hpt033
    have hne : suf 34 ≠ [] := by
      intro h
      rw [h] at hp
      simp at hp
      exact (by decide : (endW033.1, endW033.2) ≠ (0, 0)) hp
    exact warcsOK_append arcsW033 (suf 34) endW033.1 endW033.2 S 0
      okW033 h034 hne hpt033 hj033
  have h032 : warcsOK S 0 (suf 32) = true := by
    have hp := hpt032
    have hne : suf 33 ≠ [] := by
      intro h
      rw [h] at hp
      simp at hp
      exact (by decide : (endW032.1, endW032.2) ≠ (0, 0)) hp
    exact warcsOK_append arcsW032 (suf 33) endW032.1 endW032.2 S 0
      okW032 h033 hne hpt032 hj032
  have h031 : warcsOK S 0 (suf 31) = true := by
    have hp := hpt031
    have hne : suf 32 ≠ [] := by
      intro h
      rw [h] at hp
      simp at hp
      exact (by decide : (endW031.1, endW031.2) ≠ (0, 0)) hp
    exact warcsOK_append arcsW031 (suf 32) endW031.1 endW031.2 S 0
      okW031 h032 hne hpt031 hj031
  have h030 : warcsOK S 0 (suf 30) = true := by
    have hp := hpt030
    have hne : suf 31 ≠ [] := by
      intro h
      rw [h] at hp
      simp at hp
      exact (by decide : (endW030.1, endW030.2) ≠ (0, 0)) hp
    exact warcsOK_append arcsW030 (suf 31) endW030.1 endW030.2 S 0
      okW030 h031 hne hpt030 hj030
  have h029 : warcsOK S 0 (suf 29) = true := by
    have hp := hpt029
    have hne : suf 30 ≠ [] := by
      intro h
      rw [h] at hp
      simp at hp
      exact (by decide : (endW029.1, endW029.2) ≠ (0, 0)) hp
    exact warcsOK_append arcsW029 (suf 30) endW029.1 endW029.2 S 0
      okW029 h030 hne hpt029 hj029
  have h028 : warcsOK S 0 (suf 28) = true := by
    have hp := hpt028
    have hne : suf 29 ≠ [] := by
      intro h
      rw [h] at hp
      simp at hp
      exact (by decide : (endW028.1, endW028.2) ≠ (0, 0)) hp
    exact warcsOK_append arcsW028 (suf 29) endW028.1 endW028.2 S 0
      okW028 h029 hne hpt028 hj028
  have h027 : warcsOK S 0 (suf 27) = true := by
    have hp := hpt027
    have hne : suf 28 ≠ [] := by
      intro h
      rw [h] at hp
      simp at hp
      exact (by decide : (endW027.1, endW027.2) ≠ (0, 0)) hp
    exact warcsOK_append arcsW027 (suf 28) endW027.1 endW027.2 S 0
      okW027 h028 hne hpt027 hj027
  have h026 : warcsOK S 0 (suf 26) = true := by
    have hp := hpt026
    have hne : suf 27 ≠ [] := by
      intro h
      rw [h] at hp
      simp at hp
      exact (by decide : (endW026.1, endW026.2) ≠ (0, 0)) hp
    exact warcsOK_append arcsW026 (suf 27) endW026.1 endW026.2 S 0
      okW026 h027 hne hpt026 hj026
  have h025 : warcsOK S 0 (suf 25) = true := by
    have hp := hpt025
    have hne : suf 26 ≠ [] := by
      intro h
      rw [h] at hp
      simp at hp
      exact (by decide : (endW025.1, endW025.2) ≠ (0, 0)) hp
    exact warcsOK_append arcsW025 (suf 26) endW025.1 endW025.2 S 0
      okW025 h026 hne hpt025 hj025
  have h024 : warcsOK S 0 (suf 24) = true := by
    have hp := hpt024
    have hne : suf 25 ≠ [] := by
      intro h
      rw [h] at hp
      simp at hp
      exact (by decide : (endW024.1, endW024.2) ≠ (0, 0)) hp
    exact warcsOK_append arcsW024 (suf 25) endW024.1 endW024.2 S 0
      okW024 h025 hne hpt024 hj024
  have h023 : warcsOK S 0 (suf 23) = true := by
    have hp := hpt023
    have hne : suf 24 ≠ [] := by
      intro h
      rw [h] at hp
      simp at hp
      exact (by decide : (endW023.1, endW023.2) ≠ (0, 0)) hp
    exact warcsOK_append arcsW023 (suf 24) endW023.1 endW023.2 S 0
      okW023 h024 hne hpt023 hj023
  have h022 : warcsOK S 0 (suf 22) = true := by
    have hp := hpt022
    have hne : suf 23 ≠ [] := by
      intro h
      rw [h] at hp
      simp at hp
      exact (by decide : (endW022.1, endW022.2) ≠ (0, 0)) hp
    exact warcsOK_append arcsW022 (suf 23) endW022.1 endW022.2 S 0
      okW022 h023 hne hpt022 hj022
  have h021 : warcsOK S 0 (suf 21) = true := by
    have hp := hpt021
    have hne : suf 22 ≠ [] := by
      intro h
      rw [h] at hp
      simp at hp
      exact (by decide : (endW021.1, endW021.2) ≠ (0, 0)) hp
    exact warcsOK_append arcsW021 (suf 22) endW021.1 endW021.2 S 0
      okW021 h022 hne hpt021 hj021
  have h020 : warcsOK S 0 (suf 20) = true := by
    have hp := hpt020
    have hne : suf 21 ≠ [] := by
      intro h
      rw [h] at hp
      simp at hp
      exact (by decide : (endW020.1, endW020.2) ≠ (0, 0)) hp
    exact warcsOK_append arcsW020 (suf 21) endW020.1 endW020.2 S 0
      okW020 h021 hne hpt020 hj020
  have h019 : warcsOK S 0 (suf 19) = true := by
    have hp := hpt019
    have hne : suf 20 ≠ [] := by
      intro h
      rw [h] at hp
      simp at hp
      exact (by decide : (endW019.1, endW019.2) ≠ (0, 0)) hp
    exact warcsOK_append arcsW019 (suf 20) endW019.1 endW019.2 S 0
      okW019 h020 hne hpt019 hj019
  have h018 : warcsOK S 0 (suf 18) = true := by
    have hp := hpt018
    have hne : suf 19 ≠ [] := by
      intro h
      rw [h] at hp
      simp at hp
      exact (by decide : (endW018.1, endW018.2) ≠ (0, 0)) hp
    exact warcsOK_append arcsW018 (suf 19) endW018.1 endW018.2 S 0
      okW018 h019 hne hpt018 hj018
  have h017 : warcsOK S 0 (suf 17) = true := by
    have hp := hpt017
    have hne : suf 18 ≠ [] := by
      intro h
      rw [h] at hp
      simp at hp
      exact (by decide : (endW017.1, endW017.2) ≠ (0, 0)) hp
    exact warcsOK_append arcsW017 (suf 18) endW017.1 endW017.2 S 0
      okW017 h018 hne hpt017 hj017
  have h016 : warcsOK S 0 (suf 16) = true := by
    have hp := hpt016
    have hne : suf 17 ≠ [] := by
      intro h
      rw [h] at hp
      simp at hp
      exact (by decide : (endW016.1, endW016.2) ≠ (0, 0)) hp
    exact warcsOK_append arcsW016 (suf 17) endW016.1 endW016.2 S 0
      okW016 h017 hne hpt016 hj016
  have h015 : warcsOK S 0 (suf 15) = true := by
    have hp := hpt015
    have hne : suf 16 ≠ [] := by
      intro h
      rw [h] at hp
      simp at hp
      exact (by decide : (endW015.1, endW015.2) ≠ (0, 0)) hp
    exact warcsOK_append arcsW015 (suf 16) endW015.1 endW015.2 S 0
      okW015 h016 hne hpt015 hj015
  have h014 : warcsOK S 0 (suf 14) = true := by
    have hp := hpt014
    have hne : suf 15 ≠ [] := by
      intro h
      rw [h] at hp
      simp at hp
      exact (by decide : (endW014.1, endW014.2) ≠ (0, 0)) hp
    exact warcsOK_append arcsW014 (suf 15) endW014.1 endW014.2 S 0
      okW014 h015 hne hpt014 hj014
  have h013 : warcsOK S 0 (suf 13) = true := by
    have hp := hpt013
    have hne : suf 14 ≠ [] := by
      intro h
      rw [h] at hp
      simp at hp
      exact (by decide : (endW013.1, endW013.2) ≠ (0, 0)) hp
    exact warcsOK_append arcsW013 (suf 14) endW013.1 endW013.2 S 0
      okW013 h014 hne hpt013 hj013
  have h012 : warcsOK S 0 (suf 12) = true := by
    have hp := hpt012
    have hne : suf 13 ≠ [] := by
      intro h
      rw [h] at hp
      simp at hp
      exact (by decide : (endW012.1, endW012.2) ≠ (0, 0)) hp
    exact warcsOK_append arcsW012 (suf 13) endW012.1 endW012.2 S 0
      okW012 h013 hne hpt012 hj012
  have h011 : warcsOK S 0 (suf 11) = true := by
    have hp := hpt011
    have hne : suf 12 ≠ [] := by
      intro h
      rw [h] at hp
      simp at hp
      exact (by decide : (endW011.1, endW011.2) ≠ (0, 0)) hp
    exact warcsOK_append arcsW011 (suf 12) endW011.1 endW011.2 S 0
      okW011 h012 hne hpt011 hj011
  have h010 : warcsOK S 0 (suf 10) = true := by
    have hp := hpt010
    have hne : suf 11 ≠ [] := by
      intro h
      rw [h] at hp
      simp at hp
      exact (by decide : (endW010.1, endW010.2) ≠ (0, 0)) hp
    exact warcsOK_append arcsW010 (suf 11) endW010.1 endW010.2 S 0
      okW010 h011 hne hpt010 hj010
  have h009 : warcsOK S 0 (suf 9) = true := by
    have hp := hpt009
    have hne : suf 10 ≠ [] := by
      intro h
      rw [h] at hp
      simp at hp
      exact (by decide : (endW009.1, endW009.2) ≠ (0, 0)) hp
    exact warcsOK_append arcsW009 (suf 10) endW009.1 endW009.2 S 0
      okW009 h010 hne hpt009 hj009
  have h008 : warcsOK S 0 (suf 8) = true := by
    have hp := hpt008
    have hne : suf 9 ≠ [] := by
      intro h
      rw [h] at hp
      simp at hp
      exact (by decide : (endW008.1, endW008.2) ≠ (0, 0)) hp
    exact warcsOK_append arcsW008 (suf 9) endW008.1 endW008.2 S 0
      okW008 h009 hne hpt008 hj008
  have h007 : warcsOK S 0 (suf 7) = true := by
    have hp := hpt007
    have hne : suf 8 ≠ [] := by
      intro h
      rw [h] at hp
      simp at hp
      exact (by decide : (endW007.1, endW007.2) ≠ (0, 0)) hp
    exact warcsOK_append arcsW007 (suf 8) endW007.1 endW007.2 S 0
      okW007 h008 hne hpt007 hj007
  have h006 : warcsOK S 0 (suf 6) = true := by
    have hp := hpt006
    have hne : suf 7 ≠ [] := by
      intro h
      rw [h] at hp
      simp at hp
      exact (by decide : (endW006.1, endW006.2) ≠ (0, 0)) hp
    exact warcsOK_append arcsW006 (suf 7) endW006.1 endW006.2 S 0
      okW006 h007 hne hpt006 hj006
  have h005 : warcsOK S 0 (suf 5) = true := by
    have hp := hpt005
    have hne : suf 6 ≠ [] := by
      intro h
      rw [h] at hp
      simp at hp
      exact (by decide : (endW005.1, endW005.2) ≠ (0, 0)) hp
    exact warcsOK_append arcsW005 (suf 6) endW005.1 endW005.2 S 0
      okW005 h006 hne hpt005 hj005
  have h004 : warcsOK S 0 (suf 4) = true := by
    have hp := hpt004
    have hne : suf 5 ≠ [] := by
      intro h
      rw [h] at hp
      simp at hp
      exact (by decide : (endW004.1, endW004.2) ≠ (0, 0)) hp
    exact warcsOK_append arcsW004 (suf 5) endW004.1 endW004.2 S 0
      okW004 h005 hne hpt004 hj004
  have h003 : warcsOK S 0 (suf 3) = true := by
    have hp := hpt003
    have hne : suf 4 ≠ [] := by
      intro h
      rw [h] at hp
      simp at hp
      exact (by decide : (endW003.1, endW003.2) ≠ (0, 0)) hp
    exact warcsOK_append arcsW003 (suf 4) endW003.1 endW003.2 S 0
      okW003 h004 hne hpt003 hj003
  have h002 : warcsOK S 0 (suf 2) = true := by
    have hp := hpt002
    have hne : suf 3 ≠ [] := by
      intro h
      rw [h] at hp
      simp at hp
      exact (by decide : (endW002.1, endW002.2) ≠ (0, 0)) hp
    exact warcsOK_append arcsW002 (suf 3) endW002.1 endW002.2 S 0
      okW002 h003 hne hpt002 hj002
  have h001 : warcsOK S 0 (suf 1) = true := by
    have hp := hpt001
    have hne : suf 2 ≠ [] := by
      intro h
      rw [h] at hp
      simp at hp
      exact (by decide : (endW001.1, endW001.2) ≠ (0, 0)) hp
    exact warcsOK_append arcsW001 (suf 2) endW001.1 endW001.2 S 0
      okW001 h002 hne hpt001 hj001
  have h000 : warcsOK S 0 (suf 0) = true := by
    have hp := hpt000
    have hne : suf 1 ≠ [] := by
      intro h
      rw [h] at hp
      simp at hp
      exact (by decide : (endW000.1, endW000.2) ≠ (0, 0)) hp
    exact warcsOK_append arcsW000 (suf 1) endW000.1 endW000.2 S 0
      okW000 h001 hne hpt000 hj000
  exact h000

/-! ## The certificate data as total functions -/

/-- `j`-th label of the winding certificate (junk `0` off the range `j < 4096`). -/
def windLab (j : ℕ) : ℕ := (allArcs[j]?.map (fun a : WArc => a.lab)).getD 0

/-- `j`-th grid point of the winding certificate (junk `(S,0)` at `j = 4096`). -/
def windE (j : ℕ) : ℤ × ℤ := (allArcs[j]?.map (fun a : WArc => (a.Ex, a.Ey))).getD (S, 0)

/-- the leaves of the `j`-th winding arc. -/
def windLS (j : ℕ) : List (Leaf × ℤ) := (allArcs[j]?.map (fun a : WArc => a.leaves)).getD []

theorem windLab_get (j : ℕ) (hj : j < allArcs.length) : windLab j = (allArcs[j]'hj).lab := by
  rw [windLab, List.getElem?_eq_getElem hj, Option.map_some, Option.getD_some]

theorem windE_get (j : ℕ) (hj : j < allArcs.length) :
    windE j = ((allArcs[j]'hj).Ex, (allArcs[j]'hj).Ey) := by
  rw [windE, List.getElem?_eq_getElem hj, Option.map_some, Option.getD_some]

theorem windLS_get (j : ℕ) (hj : j < allArcs.length) : windLS j = (allArcs[j]'hj).leaves := by
  rw [windLS, List.getElem?_eq_getElem hj, Option.map_some, Option.getD_some]

/-- the grid point at `0` is `(S,0)` (the circle starts there). -/
theorem windE_zero : windE 0 = (S, 0) := by decide

/-- the grid point after the last arc is `(S,0)` again. -/
theorem windE_4096 : windE 4096 = (S, 0) := by
  rw [windE, List.getElem?_eq_none (by rw [allArcs_length])]
  rfl

theorem windLab_allArcs_range : (List.range 4096).map windLab = allArcs.map (fun a : WArc => a.lab) := by
  apply List.ext_getElem?'
  intro n hn
  have hn4 : n < allArcs.length := by simpa [allArcs_length] using hn
  have h4 : n < 4096 := by rw [← allArcs_length]; exact hn4
  rw [List.getElem?_map, List.getElem?_map, List.getElem?_range h4]
  simp only [windLab, List.getElem?_eq_getElem hn4, Option.map_some, Option.getD_some]

theorem windLab_range : (List.range 4096).map windLab = WFinal.warcsAll.map (fun a : WArc => a.lab) := by
  rw [windLab_allArcs_range, allArcs_eq]

/-! ## The certificate -/

theorem wind_cert : WindCertFacts := by
  refine ⟨windLab, windE, windLS, windE_zero, windE_4096, ?_, ?_⟩
  · intro j hj
    have hj' : j < allArcs.length := by rw [allArcs_length]; exact hj
    have hOK : warcOK (allArcs[j]'hj') (windE (j + 1)).1 (windE (j + 1)).2 = true := by
      by_cases hlast : j + 1 < allArcs.length
      · have hnext := warcsOK_next allArcs S 0 allArcs_warcsOK j hj'
        rw [dif_pos hlast, dif_pos hlast] at hnext
        rw [windE_get (j + 1) hlast]
        exact hnext
      · have hlast' : j + 1 = allArcs.length := by omega
        have hnext := warcsOK_next allArcs S 0 allArcs_warcsOK j hj'
        rw [dif_neg hlast, dif_neg hlast] at hnext
        have hE : windE (j + 1) = (S, 0) := by rw [hlast']; exact windE_4096
        rw [hE]
        exact hnext
    obtain ⟨⟨l, rest, hleaves, hAx, hAy⟩, hchain, _hchainOK, hgrid, hwind⟩ :=
      warcOK_facts (allArcs[j]'hj') (windE (j + 1)).1 (windE (j + 1)).2 hOK
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [windLS_get j hj', windE_get j hj', hleaves]
      simp [hAx, hAy]
    · rw [windLS_get j hj']
      exact hchain
    · rw [windE_get j hj']
      exact hgrid
    · rw [windLS_get j hj', windLab_get j hj']
      exact List.all_eq_true.mpr hwind
  · rw [windLab_range]
    exact WFinal.wlabels_ok

end Work.Cert
