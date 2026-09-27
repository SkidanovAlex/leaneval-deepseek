import Mathlib
import Submission.Work.PL.Defs
import Submission.Work.PL.Shell.Basic
import Submission.Work.PL.Sd1.Red
import Submission.Work.PL.Sd1.shell1_of_cover
import Submission.Work.PL.Shell.sd_iter_prelim
import Submission.Work.PL.Shell.sd_iter_cover
import Submission.Work.PL.Shell.preUnion_eq_iUnion_take
import Submission.Work.PL.Shell.flatMap_take_decomp

/-!
# Shelling the `r`-fold barycentric subdivision of a simplex

`Work.PL.Shell.sd_iter_shelling_strong`: the `r`-fold barycentric subdivision of an affinely
independent simplex `Δ` admits a shelling (`shellOrd r Δ τ₁`, attaching sets
`shellSplit r Δ τ₁ i`) with respect to the floor `B = ⋃_{w ∈ τ₁} simp (Δ \ {w})`.

The proof is an induction over `r` on the invariant `ShellOK Δ B (sdIter r Δ τ₁)`: the induction
step subdivides every simplex of the level-`r` list, with its own attaching set as the new
splitting, using the one-step shelling spec `sd1Data_spec_here` for each block (derived from the
general `r = 1` statement `Work.PL.Sd1.Shell1` via `Work.PL.Sd1.sd1Data_spec_of_shell1`) and the
prefix-union bookkeeping of `Submission.Work.PL.Shell.sd_iter_prelim`.
-/

namespace Work.PL.Shell

open Set Metric Finset
open scoped BigOperators

noncomputable section

variable {N : ℕ}

/-! ### The one-step shelling spec in the `sd1Data` form -/

/-- The one-step shelling spec, derived from the general `Shell1` statement via
`Work.PL.Sd1.sd1Data_spec_of_shell1`. -/
theorem sd1Data_spec_here {N : ℕ} (σ T : Finset (PL.E N))
    (hσ : AffineIndependent ℝ ((↑) : σ → PL.E N))
    (h₁ : T.Nonempty) (h₂ : T ⊂ σ) :
    let B : Set (PL.E N) := ⋃ w ∈ T, PL.simp (σ.erase w)
    (∀ i (hi : i < (sd1Data σ T).length),
      let s := (sd1Data σ T).get ⟨i, hi⟩
      s.2.Nonempty ∧ s.2 ⊂ s.1 ∧
      PL.simp s.1 ∩ (B ∪ ⋃ j ∈ Finset.range i, PL.simp ((sd1Data σ T).getD j (∅, ∅)).1)
        = ⋃ w ∈ s.2, PL.simp (s.1.erase w)) ∧
    (sd1Data σ T).Nodup ∧
    (⋃ p ∈ (sd1Data σ T).toFinset, PL.simp p.1) = PL.simp σ := by
  have H : Work.PL.Sd1.Sd1DataConcl σ T :=
    Work.PL.Sd1.sd1Data_spec_of_shell1 σ T hσ h₁ h₂
      (Work.PL.Sd1.shell1_of_general σ T hσ h₁ h₂
        (fun hΔ vs rk hvs hvs' hrk hT₁ hT₂ hT =>
          Work.PL.Sd1.shell1_of_cover hΔ vs rk hvs hvs' hrk hT₁ hT₂ hT
            (sd_iter_covering_flagEnum hΔ vs hvs hvs')))
  rw [Work.PL.Sd1.Sd1DataConcl] at H
  exact H

/-- The data of a shelling order of `sd^r Δ`: the list of pairs (simplex, attaching set). -/
def ShellOK (Δ : Finset (PL.E N)) (B : Set (PL.E N))
    (L : List (Finset (PL.E N) × Finset (PL.E N))) : Prop :=
  (L.map Prod.fst).Nodup ∧
  (∀ i (hi : i < L.length),
    (L.get ⟨i, hi⟩).1.card = Δ.card ∧
    AffineIndependent ℝ ((↑) : (L.get ⟨i, hi⟩).1 → PL.E N) ∧
    PL.simp (L.get ⟨i, hi⟩).1 ⊆ PL.simp Δ ∧
    (L.get ⟨i, hi⟩).2.Nonempty ∧
    (L.get ⟨i, hi⟩).2 ⊂ (L.get ⟨i, hi⟩).1 ∧
    PL.simp (L.get ⟨i, hi⟩).1 ∩ (B ∪ preUnion (L.map Prod.fst) i) =
      ⋃ w ∈ (L.get ⟨i, hi⟩).2, PL.simp ((L.get ⟨i, hi⟩).1.erase w)) ∧
  (⋃ p ∈ L.toFinset, PL.simp p.1) = PL.simp Δ

/-- Base case: the trivial shelling of `Δ` itself. -/
theorem shellOK_zero (Δ τ₁ : Finset (PL.E N)) {B : Set (PL.E N)}
    (hΔ : AffineIndependent ℝ ((↑) : Δ → PL.E N))
    (hB : B = ⋃ w ∈ τ₁, PL.simp (Δ.erase w)) (h₁ : τ₁.Nonempty) (h₂ : τ₁ ⊂ Δ) :
    ShellOK Δ B [(Δ, τ₁)] := by
  have hBsub : (⋃ w ∈ τ₁, PL.simp (Δ.erase w)) ⊆ PL.simp Δ := by
    intro x hx
    obtain ⟨w, -, hxw⟩ := Set.mem_iUnion₂.mp hx
    exact convexHull_mono (fun y hy => Finset.mem_of_mem_erase hy) hxw
  refine ⟨by simp, ?_, by simp⟩
  intro i hi
  have hi0 : i = 0 := by simp at hi; omega
  subst hi0
  have hg : ([(Δ, τ₁)].get ⟨0, hi⟩) = (Δ, τ₁) := List.get_cons_zero
  rw [hg]
  refine ⟨rfl, hΔ, subset_rfl, h₁, h₂, ?_⟩
  rw [show preUnion ([(Δ, τ₁)].map Prod.fst) 0 = ∅ by simp [preUnion],
    Set.union_empty, hB]
  exact Set.inter_eq_right.mpr hBsub

/-- One step of the iteration: subdividing every simplex of the level-`r` list. -/
theorem shellOK_flatMap (Δ : Finset (PL.E N)) (B : Set (PL.E N))
    (L : List (Finset (PL.E N) × Finset (PL.E N))) (hL : ShellOK Δ B L) :
    ShellOK Δ B (L.flatMap fun p => sd1Data p.1 p.2) := by
  obtain ⟨hnd, hprop, hcov⟩ := hL
  have hmap : (L.flatMap fun p => sd1Data p.1 p.2).map Prod.fst
      = L.flatMap fun p => (sd1Data p.1 p.2).map Prod.fst := List.map_flatMap
  -- per-index data
  have hdata : ∀ m (hm : m < (L.flatMap fun p => sd1Data p.1 p.2).length),
      ((L.flatMap fun p => sd1Data p.1 p.2).get ⟨m, hm⟩).1.card = Δ.card ∧
      AffineIndependent ℝ
        ((↑) : ((L.flatMap fun p => sd1Data p.1 p.2).get ⟨m, hm⟩).1 → PL.E N) ∧
      PL.simp ((L.flatMap fun p => sd1Data p.1 p.2).get ⟨m, hm⟩).1 ⊆ PL.simp Δ ∧
      ((L.flatMap fun p => sd1Data p.1 p.2).get ⟨m, hm⟩).2.Nonempty ∧
      ((L.flatMap fun p => sd1Data p.1 p.2).get ⟨m, hm⟩).2
        ⊂ ((L.flatMap fun p => sd1Data p.1 p.2).get ⟨m, hm⟩).1 ∧
      PL.simp ((L.flatMap fun p => sd1Data p.1 p.2).get ⟨m, hm⟩).1
          ∩ (B ∪ preUnion ((L.flatMap fun p => sd1Data p.1 p.2).map Prod.fst) m)
        = ⋃ w ∈ ((L.flatMap fun p => sd1Data p.1 p.2).get ⟨m, hm⟩).2,
            PL.simp (((L.flatMap fun p => sd1Data p.1 p.2).get ⟨m, hm⟩).1.erase w) := by
    intro m hm
    obtain ⟨k, hk, j, hj, hdec, hget, htake⟩ :=
      flatMap_take_decomp L (fun p => sd1Data p.1 p.2) hm
    obtain ⟨hcardσ, hAIσ, hsubσ, hneT, hssubT, htraceT⟩ := hprop k hk
    obtain ⟨hspeci, -, hcovd⟩ := sd1Data_spec_here (L.get ⟨k, hk⟩).1 (L.get ⟨k, hk⟩).2
      hAIσ hneT hssubT
    obtain ⟨hcard', hAI', hsub'⟩ :=
      sd_iter_sd1Data_elem_spec (T := (L.get ⟨k, hk⟩).2) (σ := (L.get ⟨k, hk⟩).1) hAIσ j hj
    obtain ⟨hne', hssub', htrace'⟩ := hspeci j hj
    -- length bookkeeping between the pair list and the vertex-set list
    have hlen : ((L.take k).flatMap fun p => (sd1Data p.1 p.2).map Prod.fst).length
        = ((L.take k).flatMap fun p => sd1Data p.1 p.2).length := by
      rw [List.length_flatMap, List.length_flatMap]
      congr 1
      exact List.map_congr_left fun p _ => List.length_map Prod.fst
    have hlen' : ((L.take k).flatMap fun p => (sd1Data p.1 p.2).map Prod.fst).length + j = m := by
      rw [hlen, hdec]
    -- the prefix union splits into the earlier blocks and the current one
    have hA : preUnion ((sd1Data (L.get ⟨k, hk⟩).1 (L.get ⟨k, hk⟩).2).map Prod.fst) j
        = ⋃ j' ∈ Finset.range j, PL.simp ((sd1Data (L.get ⟨k, hk⟩).1
            (L.get ⟨k, hk⟩).2).getD j' (∅, ∅)).1 := by
      rw [preUnion]
      refine iUnion₂_congr fun j' hj' => ?_
      rw [getD_map_fst _ _ (by rw [Finset.mem_range] at hj'; omega)]
    have hpf := preUnion_flatMap L (fun p => (sd1Data p.1 p.2).map Prod.fst) Prod.fst
      (fun p hp => by
        obtain ⟨i, hi, hpi⟩ := List.getElem_of_mem hp
        rw [← hpi]
        obtain ⟨-, hAIi, -, hnei, hssubi, -⟩ := hprop i hi
        obtain ⟨-, -, hcovi⟩ := sd1Data_spec_here (L.get ⟨i, hi⟩).1 (L.get ⟨i, hi⟩).2
          hAIi hnei hssubi
        rw [iUnion_toFinset_map]
        exact hcovi)
      k hk j (by rw [List.length_map]; exact le_of_lt hj)
    have hpre' : preUnion ((L.flatMap fun p => sd1Data p.1 p.2).map Prod.fst) m
        = preUnion (L.map Prod.fst) k
          ∪ ⋃ j' ∈ Finset.range j, PL.simp ((sd1Data (L.get ⟨k, hk⟩).1
              (L.get ⟨k, hk⟩).2).getD j' (∅, ∅)).1 := by
      rw [hmap, ← hlen', hpf, hA]
    rw [hget, hpre']
    refine ⟨?_, ?_, ?_, hne', hssub', ?_⟩
    · rw [hcard']; exact hcardσ
    · exact hAI'
    · exact hsub'.trans hsubσ
    · rw [← htrace', ← htraceT]
      ext x
      simp only [Set.mem_inter_iff, Set.mem_union]
      constructor
      · rintro ⟨hxs, hB | (hP | hA)⟩
        · exact ⟨hxs, Or.inl ⟨hsub' hxs, Or.inl hB⟩⟩
        · exact ⟨hxs, Or.inl ⟨hsub' hxs, Or.inr hP⟩⟩
        · exact ⟨hxs, Or.inr hA⟩
      · rintro ⟨hxs, (⟨_, hB | hP⟩ | hA)⟩
        · exact ⟨hxs, Or.inl hB⟩
        · exact ⟨hxs, Or.inr (Or.inl hP)⟩
        · exact ⟨hxs, Or.inr (Or.inr hA)⟩
  -- the covering
  have hcov' : (⋃ p ∈ (L.flatMap fun p => sd1Data p.1 p.2).toFinset, PL.simp p.1) = PL.simp Δ := by
    rw [← iUnion_toFinset_map, hmap, iUnion_toFinset_flatMap, ← hcov]
    refine iUnion₂_congr fun p hp => ?_
    obtain ⟨i, hi, hpi⟩ := List.getElem_of_mem (List.mem_toFinset.mp hp)
    rw [← hpi]
    obtain ⟨-, hAIi, -, hnei, hssubi, -⟩ := hprop i hi
    obtain ⟨-, -, hcovi⟩ := sd1Data_spec_here (L.get ⟨i, hi⟩).1 (L.get ⟨i, hi⟩).2
      hAIi hnei hssubi
    rw [iUnion_toFinset_map]
    exact hcovi
  -- the `Nodup`
  have hnd' : ((L.flatMap fun p => sd1Data p.1 p.2).map Prod.fst).Nodup := by
    refine Work.PL.Sd1.nodup_map_fst_of_shelling (B := B) (fun m hm => (hdata m hm).2.1) ?_ ?_
    · intro m hm
      obtain ⟨-, -, -, hne, hssub, -⟩ := hdata m hm
      exact ⟨hne, (Finset.ssubset_iff_subset_ne.mp hssub).1⟩
    · intro m hm
      obtain ⟨-, -, -, -, -, htr⟩ := hdata m hm
      exact htr
  exact ⟨hnd', hdata, hcov'⟩


/-- **The `r`-fold shelling of the barycentric subdivision of a simplex.** -/
theorem sd_iter_shelling_strong {N : ℕ} (r : ℕ) (Δ : Finset (PL.E N))
    (hΔ : AffineIndependent ℝ ((↑) : Δ → PL.E N))
    (τ₁ : Finset (PL.E N)) (h₁ : τ₁.Nonempty) (h₂ : τ₁ ⊂ Δ) :
    let B : Set (PL.E N) := ⋃ w ∈ τ₁, PL.simp (Δ.erase w)
    (Work.PL.Shell.shellOrd r Δ τ₁).Nodup ∧
    (∀ i (hi : i < (Work.PL.Shell.shellOrd r Δ τ₁).length),
        ((Work.PL.Shell.shellOrd r Δ τ₁).get ⟨i, hi⟩).card = Δ.card ∧
        PL.simp ((Work.PL.Shell.shellOrd r Δ τ₁).get ⟨i, hi⟩) ⊆ PL.simp Δ ∧
        (Work.PL.Shell.shellSplit r Δ τ₁ i).Nonempty ∧
        (Work.PL.Shell.shellSplit r Δ τ₁ i) ⊂ (Work.PL.Shell.shellOrd r Δ τ₁).get ⟨i, hi⟩ ∧
        PL.simp ((Work.PL.Shell.shellOrd r Δ τ₁).get ⟨i, hi⟩) ∩
            (B ∪ Work.PL.Shell.preUnion (Work.PL.Shell.shellOrd r Δ τ₁) i)
          = ⋃ w ∈ Work.PL.Shell.shellSplit r Δ τ₁ i,
              PL.simp (((Work.PL.Shell.shellOrd r Δ τ₁).get ⟨i, hi⟩).erase w)) ∧
    (⋃ τ ∈ (Work.PL.Shell.shellOrd r Δ τ₁).toFinset, PL.simp τ) = PL.simp Δ := by
  let B : Set (PL.E N) := ⋃ w ∈ τ₁, PL.simp (Δ.erase w)
  have hmain : ShellOK Δ B (sdIter r Δ τ₁) := by
    induction r with
    | zero => exact shellOK_zero Δ τ₁ hΔ rfl h₁ h₂
    | succ n ih => exact shellOK_flatMap Δ B (sdIter n Δ τ₁) ih
  obtain ⟨hnd, hprop, hcov⟩ := hmain
  refine ⟨?_, ?_, ?_⟩
  · simpa [shellOrd] using hnd
  · intro i hi
    have hi' : i < (sdIter r Δ τ₁).length := by simpa [shellOrd] using hi
    obtain ⟨hcard, -, hsub, hne, hssub, htr⟩ := hprop i hi'
    have hg : (shellOrd r Δ τ₁).get ⟨i, hi⟩ = ((sdIter r Δ τ₁).get ⟨i, hi'⟩).1 := by
      simp only [shellOrd]
      exact List.getElem_map (f := Prod.fst) (l := sdIter r Δ τ₁) (i := i) (h := hi)
    rw [hg]
    simp only [shellSplit, shellOrd, List.getD_eq_getElem (sdIter r Δ τ₁) (∅, ∅) hi']
    exact ⟨hcard, hsub, hne, hssub, htr⟩
  · rw [shellOrd, iUnion_toFinset_map]
    exact hcov



end

end Work.PL.Shell
