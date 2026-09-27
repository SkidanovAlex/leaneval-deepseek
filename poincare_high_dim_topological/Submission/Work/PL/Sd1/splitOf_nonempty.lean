import Mathlib
import Submission.Work.PL.Sd1.Defs
import Submission.Work.PL.Shell.Basic
import Submission.Work.PL.Shell.flagEnum_mem
import Submission.Work.PL.Shell.ascIdx_mem
import Submission.Work.PL.Shell.bary_inj
import Submission.Work.PL.Shell.exists_ascent

namespace Work.PL.Sd1

open Finset

/-- `List.Perm` preserves `toFinset`. -/
private theorem perm_toFinset {N : ℕ} {l l' : List (PL.E N)} (h : l.Perm l') :
    l.toFinset = l'.toFinset := by
  ext x
  rw [List.mem_toFinset, List.mem_toFinset]
  exact h.mem_iff

/-- **Combinatorial core.**  Every flag `l` of `vs` either has an ascent position or its
last vertex lies in `T`.

Indeed, if the last vertex `w` of `l` is not in `T`, pick `u ∈ T`.  Since `l` enumerates
`Δ ⊇ T`, `u` occurs in `l`, say at position `j`; the last position is `l.length - 1` and
holds `w`, so `j < l.length - 1` because `u ≠ w`.  Now the sequence `i ↦ rk (l i)` is
strictly smaller at `j` than at `l.length - 1` (by the hypothesis `hT`), so by
`exists_ascent` it admits a strict increase at some consecutive pair inside that interval,
i.e. `l` has an ascent. -/
private theorem ascIdx_nonempty_or_getLast_mem {N : ℕ} {Δ T : Finset (PL.E N)}
    {vs : List (PL.E N)} {rk : PL.E N → ℕ} (hvs : vs.toFinset = Δ)
    (hT₁ : T.Nonempty) (hT₂ : T ⊂ Δ)
    (hT : ∀ u ∈ T, ∀ w ∈ Δ, w ∉ T → rk u < rk w)
    {l : List (PL.E N)} (hl : l ∈ Work.PL.Shell.flagEnum vs) :
    (Work.PL.Shell.ascIdx rk l).Nonempty ∨ (∃ v, l.getLast? = some v ∧ v ∈ T) := by
  have hlperm : l.Perm vs := Work.PL.Shell.flagEnum_mem.mp hl
  have hlΔ : l.toFinset = Δ := by rw [perm_toFinset hlperm, hvs]
  by_cases hlast : ∃ v, l.getLast? = some v ∧ v ∈ T
  · exact Or.inr hlast
  · refine Or.inl ?_
    have hlne : l ≠ [] := by
      rintro rfl
      obtain ⟨u, huT⟩ := hT₁
      have hmem : u ∈ ([] : List (PL.E N)).toFinset := by
        rw [hlΔ]
        exact hT₂.1 huT
      simpa using hmem
    have hdpos : 0 < l.length := List.length_pos_iff.mpr hlne
    set w : PL.E N := l.getLast hlne with hwdef
    have hlastw : l.getLast? = some w := by
      rw [hwdef, List.getLast?_eq_some_getLast hlne]
    have hwT : w ∉ T := fun hwT => hlast ⟨w, hlastw, hwT⟩
    have hwmem : w ∈ l := List.getLast_mem hlne
    have hwΔ : w ∈ Δ := by
      rw [← hlΔ]
      exact List.mem_toFinset.mpr hwmem
    obtain ⟨u, huT⟩ := hT₁
    have huΔ : u ∈ Δ := hT₂.1 huT
    have hul : u ∈ l := by
      rw [← List.mem_toFinset, hlΔ]
      exact huΔ
    obtain ⟨j, hj, hju⟩ := List.mem_iff_getElem.mp hul
    have huw : u ≠ w := fun h => hwT (h ▸ huT)
    have hlt : rk u < rk w := hT u huT w hwΔ hwT
    have hld : l.length - 1 < l.length := by omega
    have hwget : l[l.length - 1]'hld = w := by
      rw [← List.getLast_eq_getElem hlne]
    have hjlast : j < l.length - 1 := by
      have hjne : j ≠ l.length - 1 := by
        intro hje
        refine huw (Option.some.inj ?_)
        have h1 : l[j]? = some u := by rw [List.getElem?_eq_getElem hj, hju]
        have h2 : l[l.length - 1]? = some w := by
          rw [List.getElem?_eq_getElem hld, hwget]
        rw [← h1, ← h2, hje]
      omega
    -- the sequence of ranks along the positions of `l`
    have hincr : rk (l.getD j 0) < rk (l.getD (l.length - 1) 0) := by
      rw [List.getD_eq_getElem l 0 hj, List.getD_eq_getElem l 0 hld, hju, hwget]
      exact hlt
    obtain ⟨s, -, hsi, hasc⟩ :=
      Work.PL.Shell.exists_ascent (a := fun n => rk (l.getD n 0)) hjlast hincr
    have hs : s < l.length := by omega
    have hs1 : s + 1 < l.length := by omega
    refine ⟨s, Work.PL.Shell.ascIdx_mem.mpr ⟨hs1, ?_⟩⟩
    have hasc' : rk (l.getD s 0) < rk (l.getD (s + 1) 0) := hasc
    rw [List.getD_eq_getElem l 0 hs, List.getD_eq_getElem l 0 hs1] at hasc'
    exact hasc'

theorem splitOf_nonempty {N : ℕ} {Δ T : Finset (PL.E N)}
    (hΔ : AffineIndependent ℝ ((↑) : Δ → PL.E N))
    {vs : List (PL.E N)} {rk : PL.E N → ℕ} (hvs : vs.toFinset = Δ) (hvs' : vs.Nodup)
    (hrk : (vs.map rk).Pairwise (· < ·)) (hT₁ : T.Nonempty) (hT₂ : T ⊂ Δ)
    (hT : ∀ u ∈ T, ∀ w ∈ Δ, w ∉ T → rk u < rk w)
    {l : List (PL.E N)} (hl : l ∈ Work.PL.Shell.flagEnum vs) :
    (Work.PL.Shell.splitOf Δ T rk l).Nonempty := by
  have hkey := ascIdx_nonempty_or_getLast_mem hvs hT₁ hT₂ hT hl
  rw [Work.PL.Shell.splitOf]
  by_cases hlast : ∃ v, l.getLast? = some v ∧ v ∈ T
  · rw [if_pos hlast]
    exact Finset.insert_nonempty _ _
  · rw [if_neg hlast]
    rcases hkey with hne | hcon
    · exact Finset.Nonempty.image hne _
    · exact absurd hcon hlast

end Work.PL.Sd1
