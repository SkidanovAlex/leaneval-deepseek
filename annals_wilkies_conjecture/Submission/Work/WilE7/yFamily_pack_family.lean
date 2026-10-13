/-
  Area E7 / `CoreLT_succ`: **the `Y`-family aggregation step** (packing a *family of lists* of
  candidate sets into one list, with the base projections preserved and the bounds aggregated).

  `yFamily_pack` handles a single candidate per index; the assembly of the `(n+1,K+1)` step needs to
  pack *lists* of candidates that come from the producers — the `π_n`-fibre-cut pieces of the ambient
  family (`CoreStep.piFamily`), the `hE5`-strata and frontier strata of the `π_{n+1}`-cut pieces
  (`coreLT_succ.frontierFamily`), the refined cut (`coreLT_succ.refinedCutFamily`), the `±1` slices
  (`coreLT_succ.semiPf_coord_levelSet`), `Σ`/`Σlow`, and the transported outer `Y`.  Each of those
  candidates lives in its own fibre dimension `m i`; each carries a format bound `F'` (a function of
  the outer `F`) and a degree bound `Q.eval D` (a polynomial in the outer degree bound `D`), and the
  number of candidates for each `i` is bounded by `N` (which the caller turns into a polynomial in
  `D` and `k`).

  This file collects them into one list `Yl : List (SemiPf (n + M))` such that

  * `Yl.length ≤ ι * N` (the length aggregation the cardinality bookkeeping consumes),
  * every member has `fmt ≤ F' + M` and `deg ≤ Q.eval D` (uniform in the candidate),
  * **every candidate is represented**: for every `i` and every `Y ∈ Cs i` there is a member `Y'` of
    `Yl` with `Y'.deg ≤ Y.deg` and — crucially for the vertical row — the *same* base projection
    `projFirst n M '' Y'.set = projFirst n (m i) '' Y.set`.

  The last clause is what `NOTES_S54` §11 identifies as the operative one: the base cells of the
  inner `CoreLT n K` call are compatible with the projections of the members of `Yl`, so the specific
  pieces that cut at the switch points of the vertical row (in particular the frontier strata) must be
  *members* of the packed list, not merely covered by its union.
-/
import Mathlib
import Submission.Work.WilE7.Defs
import Submission.Work.WilE7.pad_proj
import Submission.Work.WilE7.pad_deg
import Submission.Work.WilE7.yFamily_pack

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7

open WilkiesDesign WilkiesDesign.E

/-- Length bound for `List.flatMap` with a uniform bound on the fibres. -/
theorem length_flatMap_le {α β : Type*} (l : List α) (f : α → List β) (B : ℕ)
    (h : ∀ a ∈ l, (f a).length ≤ B) : (l.flatMap f).length ≤ l.length * B := by
  induction l with
  | nil => simp
  | cons a t ih =>
      rw [List.flatMap_cons, List.length_append, List.length_cons]
      have ha : (f a).length ≤ B := h a (by simp)
      have ht : (t.flatMap f).length ≤ t.length * B := ih (fun b hb => h b (by simp [hb]))
      calc (f a).length + (t.flatMap f).length ≤ B + t.length * B := Nat.add_le_add ha ht
        _ = (t.length + 1) * B := by ring

/-- **Aggregated packaging.**  A family of lists of candidate sets, with a common format bound `F'`, a
common degree bound `Q.eval D` and a uniform cardinality bound `N`, is packed into a single list in a
common fibre dimension `n + M`, preserving every candidate's base projection and its degree bound. -/
theorem yFamily_pack_family {n : ℕ} {ι : ℕ}
    (m : Fin ι → ℕ) (M : ℕ) (hm : ∀ i, m i ≤ M)
    (Cs : (i : Fin ι) → List (WilkiesDesign.E.SemiPf (n + m i)))
    (F' : ℕ) (hfmt : ∀ i, ∀ Y ∈ Cs i, Y.fmt ≤ F')
    (D : ℕ) (Q : Polynomial ℕ) (hdeg : ∀ i, ∀ Y ∈ Cs i, Y.deg ≤ Q.eval D)
    (N : ℕ) (hlen : ∀ i, (Cs i).length ≤ N) :
    ∃ Yl : List (WilkiesDesign.E.SemiPf (n + M)),
      Yl.length ≤ ι * N ∧
      (∀ Y ∈ Yl, Y.fmt ≤ F' + M ∧ Y.deg ≤ Q.eval D) ∧
      (∀ (i : Fin ι) (Y : WilkiesDesign.E.SemiPf (n + m i)), Y ∈ Cs i →
        ∃ Y' ∈ Yl, Y'.deg ≤ Y.deg ∧
          WilkiesDesign.E.projFirst n M '' Y'.set =
            WilkiesDesign.E.projFirst n (m i) '' Y.set) := by
  refine ⟨(List.finRange ι).flatMap (fun i =>
      (Cs i).map (fun Y => Work.WilE7.SemiPf.pad (Nat.add_le_add_left (hm i) n) Y)), ?_, ?_, ?_⟩
  · have h := length_flatMap_le (List.finRange ι)
      (fun i => (Cs i).map (fun Y => Work.WilE7.SemiPf.pad (Nat.add_le_add_left (hm i) n) Y))
      N (fun i _ => by simpa using hlen i)
    rwa [List.length_finRange] at h
  · intro Y hY
    rw [List.mem_flatMap] at hY
    obtain ⟨i, -, hYi⟩ := hY
    rw [List.mem_map] at hYi
    obtain ⟨Y0, hY0, rfl⟩ := hYi
    refine ⟨?_, ?_⟩
    · have h := hfmt i Y0 hY0
      simp only [SemiPf.fmt, Work.WilE7.SemiPf.pad] at h ⊢
      omega
    · exact le_trans (semipf_deg_pad_le _ Y0) (hdeg i Y0 hY0)
  · intro i Y hY
    refine ⟨Work.WilE7.SemiPf.pad (Nat.add_le_add_left (hm i) n) Y, ?_, semipf_deg_pad_le _ Y,
      pad_proj (hm i) Y⟩
    exact List.mem_flatMap.mpr ⟨i, List.mem_finRange i, List.mem_map.mpr ⟨Y, hY, rfl⟩⟩

end Work.WilE7
