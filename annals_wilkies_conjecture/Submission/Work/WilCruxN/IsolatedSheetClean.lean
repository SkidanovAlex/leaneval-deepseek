import Mathlib
import Submission.Work.WilCrux.Defs
import Submission.Work.WilCrux.SheetDefs
import Submission.Work.Wilkies.Defs
import Submission.Work.Wilkies.CG.Spec
import Submission.Work.WilG1.Cell.generic_continuity
import Submission.Work.WilG1.Cell.exists_mem_of_cylDecomp
import Submission.Work.WilG1.Cell.thin_closure
import Submission.Work.WilG1.Cell.thin_union
import Submission.Work.WilCrux.SheetAux
import Submission.Work.WilCrux.level_separation
import Submission.Work.WilCrux.sep_or_lex
import Submission.Work.WilCrux.sheet_graph_mem
import Submission.Work.WilCrux.exists_max_word
import Submission.Work.WilCrux.isCell_level_data
import Submission.Work.WilCrux.isOpen_of_isCell_interior_nonempty
import Submission.Work.WilCrux.graph_representation
import Submission.Work.WilCruxN.Defs
import Submission.Work.WilCruxN.OpenBaseCell

/-
  `Work.WilCruxN.IsolatedSheetClean` — node N1 of `WilCrux/DESIGN.md`, clean re-proof.

  The proof is assembled out of the team's shared pieces (all of them `sorry`-free and
  axiom-clean, checked with `#print axioms`):

  * `Work.WilCruxN.OpenBaseCell` — the open cell `C₀` of the projected decomposition meeting
    `O` (the sharp-o-minimal replacement of the Baire argument, via
    `Work.WilG1.Cell.exists_thick_cell` and `Work.WilCrux.isOpen_of_isCell_interior_nonempty`);
  * `Work.WilCrux.exists_max_word` — the `Z`-cell over `C₀` meeting `W × U` of lexicographically
    maximal type word;
  * `Work.WilCrux.isolation` (`SheetAux`, via `Work.WilCrux.sep_or_lex` and
    `Work.WilCrux.level_separation`) — a point of the maximal cell over `W × U` is isolated
    inside `Z`: any other `Z`-cell close to it would either be separated from `κ`, or be a cell
    over the same base whose type word is lexicographically larger, contradicting maximality;
  * `Work.WilCrux.graph_representation` — the maximal cell is the graph of a continuous map over
    its band projection `T`;
  * `Work.WilCrux.mem_T_iff`, `Work.WilCrux.phi_eq_graph` (`SheetAux`) and
    `Work.WilCrux.sheet_graph_mem` — the coordinate graphs of `φ` are `Ω`-definable, with the
    degree bound a polynomial in `D` obtained from the decomposition bound `cP`.
-/

namespace Work.WilCruxN

open Classical
open WilkiesDesign

/-- **N1, clean re-proof.**  `Work.WilCrux.IsolatedSheet` (`Submission/Work/WilCrux/IsolatedSheet.lean`, currently a `sorry` stub) re-stated at a fresh path so that it can be proved `sorry`-free and axiom-clean.  The statement is the node N1 of `sources/wilkiesG4/wilkies_g4c_crux_map.md` (see also `Submission/Work/WilCrux/DESIGN.md`): if `Z` is `Ω`-definable and every parameter of the nonempty open `O ⊆ W` carries a point of `Z` over the open `U`, then `Z` contains an *isolated* continuous graph sheet over an open base.

Proof plan (from the map and DESIGN.md): `S.SharpCD` for the single set `Z` gives a cylindrical decomposition `C` of `ℝ^{m+N}` compatible with `Z`; Baire on the cover of the open `O` by the projections of the `Z`-cells gives an open base cell `C₀` meeting `O`; among the `Z`-cells over `C₀` meeting `W × U` choose one with lexicographically maximal *type word* (`b` at a level whose cell is a band, `g` if a graph, compared from level `m+1` up with `b > g`).  *Isolation*: no other `Z`-cell `κ'` has a point of `κ ∩ (W×U)` in its closure, because its word would be `>`.  A cell over an open base with `n₁` bands and `n₂` graphs is the graph of a continuous map over the projection onto the band coordinates, and `V := T ∩ {w ∈ W, y ∈ U}` is open nonempty; `graphOf (φ · j)` is `Ω`-definable.  The cell/word machinery is already partly developed in `Submission/Work/WilCrux/SheetDefs.lean` (`sheetPtM`, `word`, `LexLt`, `bandIdx`, `graphIdx`, `slot`, `wordEquiv`, `sheetPt_wordEquiv_band/graph`) and in `Submission/Work/WilG1/Cell/*` (`exists_thick_cell`, `gc_isCell_of_mem_cylDecomp`, `gc_exists_mem_of_cylDecomp`, `continuousOn_of_isCell_subset_graphOf`, `thin_closure`).  **The result must be `sorry`-free and axiom-clean; do NOT use any declaration whose `#print axioms` mentions `sorryAx` (check, since many sibling files are stubs).**  You may delegate sub-pieces to your own fleet. -/
theorem IsolatedSheetClean (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) {m N F D : ℕ}
    (Z : Set (Fin (m + N) → ℝ)) (hZ : Z ∈ S.Ω F D (m + N))
    (W : Set (Fin m → ℝ)) (hW : IsOpen W) (U : Set (Fin N → ℝ)) (hU : IsOpen U)
    (O : Set (Fin m → ℝ)) (hO : IsOpen O) (hOne : O.Nonempty) (hOW : O ⊆ W)
    (hfib : ∀ w ∈ O, ∃ y ∈ U, Fin.append w y ∈ Z) :
    ∃ (n1 n2 : ℕ) (e : Fin N ≃ Fin (n1 + n2)) (V : Set (Fin (m + n1) → ℝ))
      (φ : (Fin (m + n1) → ℝ) → (Fin n2 → ℝ)) (F' : ℕ) (b' : Polynomial ℕ),
      IsOpen V ∧ V.Nonempty ∧ ContinuousOn φ V ∧
      (∀ j : Fin n2, WilkiesDesign.graphOf (fun v => φ v j)
        ∈ S.Ω F' (b'.eval D) (m + n1 + 1)) ∧
      (∀ v ∈ V, Work.WilCrux.sheetPt e v (φ v) ∈ Z ∧
        (fun i : Fin m => v (Fin.castAdd n1 i)) ∈ W ∧
        (fun j : Fin N => (Fin.append (fun k : Fin n1 => v (Fin.natAdd m k)) (φ v)) (e j)) ∈ U) ∧
      (∀ v ∈ V, ∃ ε > 0, ∀ z ∈ Z, dist z (Work.WilCrux.sheetPt e v (φ v)) < ε →
        ∃ v' ∈ V, z = Work.WilCrux.sheetPt e v' (φ v')) := by
  classical
  -- 1. a sharp cylindrical decomposition compatible with `Z`
  obtain ⟨a, bMv, cP, hsharp⟩ := hcd F (m + N)
  obtain ⟨C, hdec, hsep1, -, hmem⟩ := hsharp D 1 (fun _ : Fin 1 => Z) (fun _ => hZ)
  have hsep : ∀ κ ∈ C, κ ⊆ Z ∨ Disjoint κ Z := fun κ hκ => hsep1 0 κ hκ
  -- 2. the fibre condition in the form used by the Baire step
  have hfib' : ∀ w ∈ O, ∃ p ∈ Z, (fun i : Fin m => p (Fin.castAdd N i)) = w := by
    intro w hw
    obtain ⟨y, hyU, hyZ⟩ := hfib w hw
    exact ⟨Fin.append w y, hyZ, by funext i; rw [Fin.append_left]⟩
  -- 3. an open cell of the projected decomposition meeting `O`
  obtain ⟨C₀, hC₀mem, hC₀open, hC₀inter⟩ := OpenBaseCell hdec hsep hO hOne hfib'
  -- 4. the `Z`-cells over `C₀` meeting the box `W × U`
  set K : Finset (Set (Fin (m + N) → ℝ)) :=
    C.filter (fun κ => κ ⊆ Z ∧ Work.WilCrux.projOver m N κ = C₀ ∧
      (κ ∩ Work.WilCrux.box m N W U).Nonempty) with hK
  have hKne : K.Nonempty := by
    obtain ⟨w₀, hw₀C₀, hw₀O⟩ := hC₀inter
    obtain ⟨y₀, hy₀U, hy₀Z⟩ := hfib w₀ hw₀O
    set p : Fin (m + N) → ℝ := Fin.append w₀ y₀ with hpdef
    have hpproj : (fun i : Fin m => p (Fin.castAdd N i)) = w₀ := by
      funext i; rw [hpdef, Fin.append_left]
    have hpfib : (fun j : Fin N => p (Fin.natAdd m j)) = y₀ := by
      funext j; rw [hpdef, Fin.append_right]
    obtain ⟨κ, hκC, hpκ⟩ := Work.WilCrux.cylDecomp_cover hdec p
    have hκZ : κ ⊆ Z := by
      rcases hsep κ hκC with h | hd
      · exact h
      · exact absurd hy₀Z (Set.disjoint_left.mp hd hpκ)
    have hproj : Work.WilCrux.projOver m N κ = C₀ := by
      have h1 : (fun i : Fin m => p (Fin.castAdd N i)) ∈ Work.WilCrux.projOver m N κ :=
        Work.WilCrux.mem_projOver hpκ
      rw [hpproj] at h1
      exact Work.WilCrux.eq_of_mem_projDecomp hdec
        (Work.WilCrux.projOver_mem_projDecomp hκC) hC₀mem h1 hw₀C₀
    have hbox : (κ ∩ Work.WilCrux.box m N W U).Nonempty :=
      ⟨p, hpκ, by rw [hpproj]; exact hOW hw₀O, by rw [hpfib]; exact hy₀U⟩
    exact ⟨κ, by rw [hK, Finset.mem_filter]; exact ⟨hκC, hκZ, hproj, hbox⟩⟩
  -- 5. the `Z`-cell of lexicographically maximal type word
  obtain ⟨κ, hκK, hκmax⟩ := Work.WilCrux.exists_max_word (N := N) (m := m) hKne
  rw [hK, Finset.mem_filter] at hκK
  obtain ⟨hκC, hκZ, hκproj, hκbox⟩ := hκK
  have hmax : ∀ κ' ∈ C, κ' ⊆ Z → Work.WilCrux.projOver m N κ' = C₀ →
      (κ' ∩ Work.WilCrux.box m N W U).Nonempty →
      ¬ Work.WilCrux.LexLt (Work.WilCrux.word m N κ) (Work.WilCrux.word m N κ') := by
    intro κ' hκ'C hκ'Z hκ'proj hκ'box
    exact hκmax κ' (by rw [hK, Finset.mem_filter]; exact ⟨hκ'C, hκ'Z, hκ'proj, hκ'box⟩)
  -- 6. the maximal cell is a graph over its band coordinates
  obtain ⟨T, φ, hTopen, hTne, hφcont, hφ0, hTproj, hTmem, hTsurj⟩ :=
    Work.WilCrux.graph_representation m N C₀ κ hC₀open
      (Work.WilCrux.IsCellOver.of_mem N hdec hκC hκproj)
  -- 7. the two descriptions of `T` and of `φ` needed for definability
  have hTiff := Work.WilCrux.mem_T_iff hTmem hTsurj
  have hφT := Work.WilCrux.phi_eq_graph hTmem hTsurj
  -- 8. the coordinate graphs of `φ` are `Ω`-definable
  obtain ⟨F'', b'', hb''⟩ := Work.WilCrux.sheet_graph_mem S (hmem κ hκC) T φ hTiff hφT
    (fun v hv j => congrFun (hφ0 v hv) j)
  -- 9. the sheet base: `v ∈ T` with parameters in `W` and fibre in `U`
  let V : Set (Fin (m + Work.WilCrux.nBand N (Work.WilCrux.word m N κ)) → ℝ) :=
    {v | v ∈ T ∧
      (fun i : Fin m => v (Fin.castAdd (Work.WilCrux.nBand N (Work.WilCrux.word m N κ)) i)) ∈ W ∧
      (fun j : Fin N => (Fin.append (fun k : Fin (Work.WilCrux.nBand N (Work.WilCrux.word m N κ)) =>
        v (Fin.natAdd m k)) (φ v)) ((Work.WilCrux.wordEquiv (Work.WilCrux.word m N κ)) j)) ∈ U}
  have hsheetfun : ∀ v : Fin (m + Work.WilCrux.nBand N (Work.WilCrux.word m N κ)) → ℝ,
      (fun j : Fin N => (Fin.append (fun k : Fin (Work.WilCrux.nBand N (Work.WilCrux.word m N κ)) =>
        v (Fin.natAdd m k)) (φ v)) ((Work.WilCrux.wordEquiv (Work.WilCrux.word m N κ)) j))
        = fun j : Fin N => Work.WilCrux.sheetPtM (Work.WilCrux.wordEquiv (Work.WilCrux.word m N κ))
            v (φ v) (Fin.natAdd m j) := by
    intro v; funext j; rw [Work.WilCrux.sheetPtM_natAdd]
  refine ⟨Work.WilCrux.nBand N (Work.WilCrux.word m N κ),
    Work.WilCrux.nGraph N (Work.WilCrux.word m N κ),
    Work.WilCrux.wordEquiv (Work.WilCrux.word m N κ), V, φ, F'', b''.comp cP,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `V` is open
    have hcont : ContinuousOn
        (fun v : Fin (m + Work.WilCrux.nBand N (Work.WilCrux.word m N κ)) → ℝ =>
          Work.WilCrux.sheetPtM (Work.WilCrux.wordEquiv (Work.WilCrux.word m N κ)) v (φ v)) T :=
      (Work.WilCrux.continuous_sheetPtM
        (Work.WilCrux.wordEquiv (Work.WilCrux.word m N κ))).comp_continuousOn
        (continuousOn_id.prodMk hφcont)
    have hfibcont : ContinuousOn
        (fun v : Fin (m + Work.WilCrux.nBand N (Work.WilCrux.word m N κ)) → ℝ =>
          fun j : Fin N =>
            Work.WilCrux.sheetPtM (Work.WilCrux.wordEquiv (Work.WilCrux.word m N κ)) v (φ v)
              (Fin.natAdd m j)) T :=
      (continuous_pi fun j => continuous_apply (Fin.natAdd m j)).comp_continuousOn hcont
    have hW' : IsOpen {v : Fin (m + Work.WilCrux.nBand N (Work.WilCrux.word m N κ)) → ℝ |
        (fun i : Fin m =>
          v (Fin.castAdd (Work.WilCrux.nBand N (Work.WilCrux.word m N κ)) i)) ∈ W} :=
      hW.preimage (continuous_pi fun i => continuous_apply (Fin.castAdd _ i))
    have hU' : IsOpen (T ∩ {v : Fin (m + Work.WilCrux.nBand N (Work.WilCrux.word m N κ)) → ℝ |
        (fun j : Fin N =>
          Work.WilCrux.sheetPtM (Work.WilCrux.wordEquiv (Work.WilCrux.word m N κ)) v (φ v)
            (Fin.natAdd m j)) ∈ U}) :=
      hfibcont.isOpen_inter_preimage hTopen hU
    have hV_eq : V = T ∩ ({v : Fin (m + Work.WilCrux.nBand N (Work.WilCrux.word m N κ)) → ℝ |
          (fun i : Fin m =>
            v (Fin.castAdd (Work.WilCrux.nBand N (Work.WilCrux.word m N κ)) i)) ∈ W} ∩
        (T ∩ {v : Fin (m + Work.WilCrux.nBand N (Work.WilCrux.word m N κ)) → ℝ |
          (fun j : Fin N =>
            Work.WilCrux.sheetPtM (Work.WilCrux.wordEquiv (Work.WilCrux.word m N κ)) v (φ v)
              (Fin.natAdd m j)) ∈ U})) := by
      ext v
      simp only [V, Set.mem_setOf_eq, Set.mem_inter_iff, hsheetfun v]
      tauto
    rw [hV_eq]
    exact hTopen.inter (hW'.inter hU')
  · -- `V` is nonempty (the box point of `κ` provides a base point)
    obtain ⟨p₀, hp₀κ, hp₀box⟩ := hκbox
    obtain ⟨v₀, hv₀T, hv₀eq⟩ := hTsurj p₀ hp₀κ
    have h1 : (fun i : Fin m =>
        v₀ (Fin.castAdd (Work.WilCrux.nBand N (Work.WilCrux.word m N κ)) i))
        = fun i : Fin m => p₀ (Fin.castAdd N i) := by
      funext i; rw [hv₀eq, Work.WilCrux.sheetPtM_castAdd]
    have h2 : (fun j : Fin N => p₀ (Fin.natAdd m j))
        = fun j : Fin N =>
            Work.WilCrux.sheetPtM (Work.WilCrux.wordEquiv (Work.WilCrux.word m N κ))
              v₀ (φ v₀) (Fin.natAdd m j) := by
      funext j; rw [hv₀eq]
    exact ⟨v₀, hv₀T, by rw [h1]; exact hp₀box.1, by rw [hsheetfun v₀, ← h2]; exact hp₀box.2⟩
  · -- continuity of `φ`
    exact hφcont.mono fun v hv => hv.1
  · -- definability of the coordinate graphs of `φ`
    intro j
    simpa [Polynomial.eval_comp] using hb'' j
  · -- the sheet points lie in `Z` and over `W × U`
    intro v hv
    obtain ⟨hvT, hvmW, hvfU⟩ := hv
    have hpκ : Work.WilCrux.sheetPtM (Work.WilCrux.wordEquiv (Work.WilCrux.word m N κ)) v (φ v)
        ∈ κ := hTmem v hvT
    exact ⟨hκZ hpκ, hvmW, hvfU⟩
  · -- isolation of each sheet point inside `Z`
    intro v hv
    obtain ⟨hvT, hvmW, hvfU⟩ := hv
    have hpκ : Work.WilCrux.sheetPtM (Work.WilCrux.wordEquiv (Work.WilCrux.word m N κ)) v (φ v)
        ∈ κ := hTmem v hvT
    have hproj_eq : (fun i : Fin m =>
          Work.WilCrux.sheetPtM (Work.WilCrux.wordEquiv (Work.WilCrux.word m N κ)) v (φ v)
            (Fin.castAdd N i))
        = fun i : Fin m =>
            v (Fin.castAdd (Work.WilCrux.nBand N (Work.WilCrux.word m N κ)) i) := by
      funext i; rw [Work.WilCrux.sheetPtM_castAdd]
    have hvfU' : (fun j : Fin N =>
        Work.WilCrux.sheetPtM (Work.WilCrux.wordEquiv (Work.WilCrux.word m N κ)) v (φ v)
          (Fin.natAdd m j)) ∈ U := by
      rw [← hsheetfun v]; exact hvfU
    have hpbox : Work.WilCrux.sheetPtM (Work.WilCrux.wordEquiv (Work.WilCrux.word m N κ)) v (φ v)
        ∈ Work.WilCrux.box m N W U := ⟨by rw [hproj_eq]; exact hvmW, hvfU'⟩
    obtain ⟨ε₀, hε₀, hisol⟩ :=
      Work.WilCrux.isolation hdec hC₀open hW hU hsep hκC hκZ hκproj hmax hpκ hpbox
    obtain ⟨ε₁, hε₁, hbox₁⟩ := Metric.isOpen_iff.mp (Work.WilCrux.isOpen_box hW hU) _ hpbox
    refine ⟨min ε₀ ε₁, lt_min hε₀ hε₁, fun z hzZ hz => ?_⟩
    have hz₀ : dist z (Work.WilCrux.sheetPtM (Work.WilCrux.wordEquiv (Work.WilCrux.word m N κ))
        v (φ v)) < ε₀ := lt_of_lt_of_le hz (min_le_left _ _)
    have hz₁ : dist z (Work.WilCrux.sheetPtM (Work.WilCrux.wordEquiv (Work.WilCrux.word m N κ))
        v (φ v)) < ε₁ := lt_of_lt_of_le hz (min_le_right _ _)
    have hzκ : z ∈ κ := hisol z hzZ hz₀
    have hzbox : z ∈ Work.WilCrux.box m N W U := hbox₁ (Metric.mem_ball.mpr hz₁)
    obtain ⟨v', hv'T, hv'eq⟩ := hTsurj z hzκ
    have h1 : (fun i : Fin m =>
        v' (Fin.castAdd (Work.WilCrux.nBand N (Work.WilCrux.word m N κ)) i))
        = fun i : Fin m => z (Fin.castAdd N i) := by
      funext i; rw [hv'eq, Work.WilCrux.sheetPtM_castAdd]
    have h2 : (fun j : Fin N => z (Fin.natAdd m j))
        = fun j : Fin N =>
            Work.WilCrux.sheetPtM (Work.WilCrux.wordEquiv (Work.WilCrux.word m N κ))
              v' (φ v') (Fin.natAdd m j) := by
      funext j; rw [hv'eq]
    exact ⟨v', ⟨hv'T, by rw [h1]; exact hzbox.1, by rw [hsheetfun v', ← h2]; exact hzbox.2⟩, hv'eq⟩

end Work.WilCruxN
