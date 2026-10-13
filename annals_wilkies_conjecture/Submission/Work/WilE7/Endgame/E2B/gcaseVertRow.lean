import Mathlib
import Submission.Work.WilE7.Endgame.E2B.GSheets
import Submission.Work.WilE7.Endgame.E2B.pieceL_vert_of_pkg
import Submission.Work.WilE7.Endgame.attain_dichotomy_of_pairAvoid
import Submission.Work.WilE7.Endgame.isOpen_projTopSet_inter_cyl_of_pairAvoid
import Submission.Work.WilE7.Endgame.cell_compat_of_levelGraphs
import Submission.Work.WilE7.Endgame.havoid_of_sigma_cross
import Submission.Work.WilE7.Endgame.projRank_ge_of_avoid
import Submission.Work.WilE7.CoreStep.cells_compat_levels

/-!
  Area E7 / E2B, the **vertical row of the `G`-branch**: the cells of the level decomposition
  `cfs b TT` are compatible with the `(n+1)`-projection of a *vertical* piece `T ∈ P.Pv`.

  The proof is the `gcase_vertical_cell` route of `NOTES_S52`/`Assembly.lean`, with the three
  geometric nodes instantiated at the data of the package `P`:

  * **G2** (`isOpen_projTopSet_inter_cyl_of_pairAvoid`): `projTopSet T` is open in `cyl b`.  The
    pair family `Wl` stratifying `absPairSet2 (G.S t₀) T` is the clause `.2.2.2.2.2.2` of
    `P.specSig` at the active candidate `G.S t₀` of dimension `K` and the vertical piece `T`; its
    low-base-rank avoidance is `GHyp` through the `Σ`-coverage clause.
  * **G1** (`attain_dichotomy_of_pairAvoid`): for every sheet level of every active candidate, the
    level is attained on all of `b` or on none of it.  Here the pair family `Vl` is the clause
    `.2.2.2.2.2.1` of `P.specSig`, again with the avoidance coming from `GHyp`.
  * **G3** (`cell_compat_of_levelGraphs`): the clopen argument on each cell, with the level family
    of the *sheets* `G.sc t j`; the compatibility hypothesis `hcompat` of that lemma is where the
    trichotomy `hTcov` is used: every sheet level is one of the levels of `TT` (or the constant
    `±1`, which are the two extreme levels), so each cell of `cfs b TT` is either a graph of a sheet
    level or disjoint from all of them.

  The `himm`/`hvert` facts about `T` are `E2B.pieceL_vert_of_pkg`; `hdim` (the dimension of the
  candidate `G.S t₀`) together with `T ∈ P.Pv` (dimension `K+1`) gives `hdimR`.
-/

namespace Work.WilE7.Endgame.E2B

set_option autoImplicit false
noncomputable section
open Classical

open WilkiesDesign WilkiesDesign.E
open Work.WilE7.MainDesign
open Work.WilE7.CoreLTSuccPlan
open Work.WilE7.CoreStep (pPair pDim absPtUp absPtInv absReindex absLevelPairSet absPairSet
  pairPtUp projTop projTopSet projTopLin absPtLin AttainAt vertCoord)
open Work.CoreStep (frontierSet pairSubBaseFst pairFrontierBaseFst pairBase)

theorem gcaseVertRow {n K F : ℕ} (c : E2Const n K F) {Fq : ℕ} {Qq : Polynomial ℕ}
    (c2 : E2Const2 c Fq Qq) {D k l m m' : ℕ} {X : Fin k → WilkiesDesign.E.SemiPf ((n + 1) + m)}
    {Y : Fin l → WilkiesDesign.E.SemiPf (n + m')} (P : E2Pkg c c2 D k l m m' X Y)
    {b : Set (Fin n → ℝ)} (hG : GHyp c c2 P b) (hpre : IsPreconnected b)
    (G : GSheets c c2 P b)
    (T : WilkiesDesign.E.Stratum 0 (n + (m + 1))) (hT : T ∈ P.Pv)
    (Kc : ℕ) (TT : Fin Kc → (Fin n → ℝ) → ℝ)
    (hTTmono : ∀ x ∈ b, StrictMono fun i : Fin Kc => TT i x)
    (hTTbnd : ∀ x ∈ b, ∀ i : Fin Kc, |TT i x| < 1)
    (hTcov : ∀ t j, (∃ i : Fin Kc, ∀ x ∈ b, TT i x = (G.sc t j x) (Fin.last m)) ∨
      (∀ x ∈ b, (G.sc t j x) (Fin.last m) = 1) ∨
      (∀ x ∈ b, (G.sc t j x) (Fin.last m) = -1))
    (hC' : WilkiesDesign.E.IsCylDecompOn (n + 1) (Work.WilE7.cyl b) (Work.WilE7.cfs b TT))
    (t₀ : Fin G.r) (ht₀ : 0 < G.kc t₀) (hdim : n + (m + 1) - (G.S t₀).j = K)
    (hbound : (closure (Work.WilE7.CoreStep.projTopSet T) \ Work.WilE7.CoreStep.projTopSet T) ∩
        Work.WilE7.cyl b ⊆
      ⋃ t : Fin G.r, ⋃ j : Fin (G.kc t),
        Work.WilE7.gr b (fun x => (G.sc t j x) (Fin.last m))) :
    ∀ κ ∈ Work.WilE7.cfs b TT,
      κ ⊆ Work.WilE7.CoreStep.projTopSet T ∨ Disjoint κ (Work.WilE7.CoreStep.projTopSet T) := by
  classical
  -- ## The vertical piece `T`: membership in the piece list, `Good`, `himm` and `hvert`.
  obtain ⟨hTmem, hTdim⟩ := P.specPv T hT
  have hTgood : T.Good := (P.specPL T hTmem).1
  obtain ⟨himm, hvert⟩ := pieceL_vert_of_pkg c c2 P hT
  -- ## The two `Σ`-clauses of the package at the pair `(candidate, vertical piece)`.
  have hSigLevVP := P.specSig.2.2.2.2.2.1
  have hSigPairVP := P.specSig.2.2.2.2.2.2
  -- ## G2 — openness of `projTopSet T` in `cyl b`.
  obtain ⟨Wl, hWl, hWcov, hWlow'⟩ := hSigPairVP (G.S t₀) (G.hScand t₀) T hT
  have hWgood : ∀ W ∈ Wl, W.Good := fun W hW => (hWl W hW).1
  have hWsub : ∀ W ∈ Wl, W.X.set ⊆ (absPairSet2 (G.S t₀) T).set := fun W hW => (hWl W hW).2
  have hWlow : ∀ W ∈ Wl, ∀ w ∈ W.X.set,
      pairBaseRank W w < n + (m + 1) - (G.S t₀).j → pairBase n m w ∉ b := by
    intro W hW w hw hlt hwb
    obtain ⟨Z, hZ, hZmem⟩ := Set.mem_iUnion₂.mp (hWlow' W hW w hw hlt)
    exact (Set.disjoint_left.mp (hG.1 Z hZ)) hwb hZmem
  have hdimR : n + (m + 1) - (G.S t₀).j + 1 = n + (m + 1) - T.j := by omega
  have hAopen := isOpen_projTopSet_inter_cyl_of_pairAvoid T (G.S t₀) hTgood (G.hSgood t₀) himm
    hvert (G.hSrank t₀) hdimR b ht₀ (G.sc t₀) (G.hcont t₀)
    (fun j x hx => (Work.CoreStep.mem_absSet_iff (G.S t₀) _).mp (G.hsub t₀ j x hx))
    Wl hWgood hWsub hWcov hWlow
  -- ## G1 — the per-level attainment dichotomy for every sheet level.
  have hgraph : ∀ (t : Fin G.r) (j : Fin (G.kc t)),
      Work.WilE7.gr b (fun x => (G.sc t j x) (Fin.last m)) ⊆
          Work.WilE7.CoreStep.projTopSet T ∨
      Disjoint (Work.WilE7.gr b (fun x => (G.sc t j x) (Fin.last m)))
        (Work.WilE7.CoreStep.projTopSet T) := by
    intro t j
    obtain ⟨Vl, hVl, hVcov, hVlow', hVtop'⟩ := hSigLevVP (G.S t) (G.hScand t) T hT
    have hVgood : ∀ V ∈ Vl, V.Good := fun V hV => (hVl V hV).1
    have hVsub : ∀ V ∈ Vl, V.X.set ⊆ (absLevelPairSet (G.S t) T).set := fun V hV => (hVl V hV).2
    have hlow : ∀ V ∈ Vl, pPair n m - V.j < n + (m + 1) - (G.S t).j →
        Disjoint (pairSubBaseFst n m V) b := by
      intro V hV hlt
      rw [Set.disjoint_left]
      intro x hxV hxb
      obtain ⟨Z, hZ, hZmem⟩ := Set.mem_iUnion₂.mp (hVlow' V hV hlt hxV)
      exact (Set.disjoint_left.mp (hG.1 Z hZ)) hxb hZmem
    have htop : ∀ V ∈ Vl, pPair n m - V.j = n + (m + 1) - (G.S t).j →
        Disjoint (pairFrontierBaseFst n m V) b := by
      intro V hV heq
      rw [Set.disjoint_left]
      intro x hxV hxb
      obtain ⟨Z, hZ, hZmem⟩ := Set.mem_iUnion₂.mp (hVtop' V hV heq hxV)
      exact (Set.disjoint_left.mp (hG.1 Z hZ)) hxb hZmem
    rcases attain_dichotomy_of_pairAvoid (G.S t) T (G.hSgood t) hTgood himm b hpre
      (G.sc t) (G.hcont t)
      (fun j x hx => (Work.CoreStep.mem_absSet_iff (G.S t) _).mp (G.hsub t j x hx))
      Vl hVgood hVsub hVcov hlow htop j with h | h
    · exact Or.inl (Work.WilE7.CoreStep.gr_subset_or_disjoint_of_attain T b _ h)
    · exact Or.inr (Work.WilE7.CoreStep.gr_disjoint_of_not_attain T b _ h)
  -- ## G3 — the sheet-level compatibility of the cells of `cfs b TT`.
  have hcompat : ∀ κ ∈ Work.WilE7.cfs b TT, ∀ t : Fin G.r,
      κ ⊆ (⋃ j : Fin (G.kc t), Work.WilE7.gr b (fun x => (G.sc t j x) (Fin.last m))) ∨
      Disjoint κ (⋃ j : Fin (G.kc t),
        Work.WilE7.gr b (fun x => (G.sc t j x) (Fin.last m))) := by
    intro κ hκ t
    -- every sheet level is one of the levels of the family `TT` (`hTcov`: the `±1` cases are the
    -- two extreme levels).
    have hidx : ∀ j : Fin (G.kc t), ∃ i : Fin (Kc + 2),
        ∀ x ∈ b, Work.WilE7.lvl TT x i = (G.sc t j x) (Fin.last m) := by
      intro j
      rcases hTcov t j with ⟨i, hi⟩ | h1 | h1
      · exact ⟨Fin.succ (Fin.castSucc i), fun x hx => by
          rw [Work.WilE7.lvl_succ]; exact hi x hx⟩
      · exact ⟨Fin.last (Kc + 1), fun x hx => by
          rw [Work.WilE7.lvl_last]; exact (h1 x hx).symm⟩
      · exact ⟨0, fun x hx => by
          rw [Work.WilE7.lvl_zero]; exact (h1 x hx).symm⟩
    choose ii hii using hidx
    have hgr : ∀ j : Fin (G.kc t), Work.WilE7.gr b (fun x => (G.sc t j x) (Fin.last m)) =
        Work.WilE7.gr b (fun x => Work.WilE7.lvl TT x (ii j)) := by
      intro j
      ext z
      simp only [Work.WilE7.gr, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, by rw [h2]; exact (hii j (Fin.init z) h1).symm⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, by rw [h2]; exact hii j (Fin.init z) h1⟩
    have hunion : (⋃ j : Fin (G.kc t), Work.WilE7.gr b (fun x => (G.sc t j x) (Fin.last m))) =
        ⋃ j : Fin (G.kc t), Work.WilE7.gr b (fun x => Work.WilE7.lvl TT x (ii j)) :=
      Set.iUnion_congr fun j => hgr j
    rw [hunion]
    rw [Work.WilE7.mem_cfs] at hκ
    rcases hκ with ⟨i₀, rfl⟩ | ⟨i₀, rfl⟩
    · -- a graph cell: contained in a sheet level graph, or disjoint from all of them
      by_cases hsome : ∃ j : Fin (G.kc t), ii j = i₀
      · obtain ⟨j, hj⟩ := hsome
        left
        intro z hz
        exact Set.mem_iUnion.mpr ⟨j, by rw [hj]; exact hz⟩
      · right
        rw [Set.disjoint_iUnion_right]
        intro j
        rw [Set.disjoint_left]
        intro z hz hz'
        simp only [Work.WilE7.gr, Set.mem_ofPred_eq] at hz hz'
        obtain ⟨hz1, hz2⟩ := hz
        obtain ⟨hz1', hz2'⟩ := hz'
        have hsm := Work.WilE7.strictMono_lvl (hTTmono (Fin.init z) hz1)
          (fun i => hTTbnd (Fin.init z) hz1 i)
        exact hsome ⟨j, (hsm.injective (by rw [← hz2, ← hz2'])).symm⟩
    · -- a band cell: disjoint from every level graph, hence from every sheet level graph
      right
      rw [Set.disjoint_iUnion_right]
      intro j
      refine (Work.WilE7.CoreStep.bd_disjoint_iUnion_gr TT hTTmono hTTbnd i₀).mono_right ?_
      intro z hz
      exact Set.mem_iUnion.mpr
        ⟨ii j, ⟨hz, Work.WilE7.CoreStep.gr_subset_cyl TT hTTbnd (ii j) hz⟩⟩
  -- ## the three inputs of `cell_compat_of_levelGraphs`
  have hf : ∀ (t : Fin G.r) (j : Fin (G.kc t)),
      ContinuousOn (fun x => (G.sc t j x) (Fin.last m)) b :=
    fun t j => (continuous_apply (Fin.last m)).comp_continuousOn (G.hcont t j)
  exact cell_compat_of_levelGraphs hC' G.kc (fun t j x => (G.sc t j x) (Fin.last m)) hf hcompat
    (Work.WilE7.CoreStep.projTopSet T) hAopen hgraph hbound

end

end Work.WilE7.Endgame.E2B
