import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.IntervalCases
import Submission.Work.FTS.StrongEps.E4R3.Nblock6.ChapterOfS2
import Submission.Work.FTS.StrongEps.E4R3.Nblock6.Route
import Submission.Work.FTS.StrongEps.E4R3.Nblock6.Stmts
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux.N_b4
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux.SmHm
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux.ZTrunc
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux.ztrunc_classC
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux.ztrunc_pkgs
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux.N_ztrunc_agree
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.epsWP_semitame_proof
import Submission.Work.FTS.StrongPersist.H6Row6.nsum_split6
import Submission.Work.FTS.GalFields.RHS.HkSum
import Submission.Work.FTS.EllipticEst.HkSq_congr_open
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.L6Ctx_JfamP_proof

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Nblock6.Assembly` — the per-`α` `S2` from the four groups of the `N`-block

This module carries the *assembly* of the semi-tame estimate `S2`
(`Work.FTS.StrongEps.E4R3.S2Stmt`, the type of `EpsWPSemitame.epsWP_semitame`) out of

* the four per-`α` level-six bounds of the groups of the twenty pieces
  `ClassCRHS.NBlk` (`Nblock6.N_b6_gg/hkMem6/star/rad/five`), carried here as explicit
  hypotheses, and
* the four *already proved* level-four/size blocks of `epsWBlk`
  (`RawE6Aux.bdata_blkLin`, `RawE6Aux.bdata_blkMu`, `Apriori4Proofs.blkN0_BData_blocks`,
  `RawE6Aux.bdata_blkNstar`, level-six membership and level-four bound `blocks.N_aux.N_b4`),

combined with `RawE6Aux.semitame_of_bdata` and the identity `epsWP = epsWBlk` on the projected
slice.  The final file `E4R3/sixthChapterBF_leaf.lean` applies the result (once the four group
lemmas are proved) to `sixthChapterBF_of_S2`.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Nblock6

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- **The level-six bound of the whole `N`-block from the four groups.** -/
theorem N_b6_perAlpha_of_groups
    (hgg : ∀ C₀ Ce Cs : ℝ, ∀ α ∈ Set.Ioc (0 : ℝ) 1, ∃ K : ℝ, 0 < K ∧
      ∀ (Φs w Φg : ℝ → ℝ → ℝ),
      Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
      (∀ z θ : ℝ, ¬ (0 < z ∧ θ ∈ Set.Ioo 0 (Real.pi / 2)) → w z θ = 0) →
      Work.FTS.VocabO.EllPkgGo α Ce w Φg → Work.FTS.ClassC.EllPkgK α 6 Ce w Φg →
      Work.FTS.StrongPersist.StarPkg6 α Cs Φs →
      (Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 0)
          ≤ K * (1 + Work.Spaces.HkSq α 7 w) + K * (1 + Work.Spaces.HkSq α 6 w) ^ 2) ∧
      (Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 4)
          ≤ K * (1 + Work.Spaces.HkSq α 7 w) + K * (1 + Work.Spaces.HkSq α 6 w) ^ 2) ∧
      (Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 8)
          ≤ K * (1 + Work.Spaces.HkSq α 7 w) + K * (1 + Work.Spaces.HkSq α 6 w) ^ 2))
    (hstar : ∀ C₀ Ce Cs : ℝ, ∀ α ∈ Set.Ioc (0 : ℝ) 1, ∃ K : ℝ, 0 < K ∧
      ∀ (Φs w Φg : ℝ → ℝ → ℝ),
      Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
      (∀ z θ : ℝ, ¬ (0 < z ∧ θ ∈ Set.Ioo 0 (Real.pi / 2)) → w z θ = 0) →
      Work.FTS.VocabO.EllPkgGo α Ce w Φg → Work.FTS.ClassC.EllPkgK α 6 Ce w Φg →
      Work.FTS.StrongPersist.StarPkg6 α Cs Φs →
      (∀ k ∈ ({1, 2, 3, 5, 6, 7, 9, 10, 11} : Finset ℕ),
        Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k)
          ≤ K * (1 + Work.Spaces.HkSq α 7 w) + K * (1 + Work.Spaces.HkSq α 6 w) ^ 2))
    (hrad : ∀ C₀ Ce Cs : ℝ, ∀ α ∈ Set.Ioc (0 : ℝ) 1, ∃ K : ℝ, 0 < K ∧
      ∀ (Φs w Φg : ℝ → ℝ → ℝ),
      Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
      (∀ z θ : ℝ, ¬ (0 < z ∧ θ ∈ Set.Ioo 0 (Real.pi / 2)) → w z θ = 0) →
      Work.FTS.VocabO.EllPkgGo α Ce w Φg → Work.FTS.ClassC.EllPkgK α 6 Ce w Φg →
      Work.FTS.StrongPersist.StarPkg6 α Cs Φs →
      (∀ k ∈ ({12, 13, 14, 15} : Finset ℕ),
        Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k)
          ≤ K * (1 + Work.Spaces.HkSq α 7 w) + K * (1 + Work.Spaces.HkSq α 6 w) ^ 2))
    (hfive : ∀ C₀ Ce Cs : ℝ, ∀ α ∈ Set.Ioc (0 : ℝ) 1, ∃ K : ℝ, 0 < K ∧
      ∀ (Φs w Φg : ℝ → ℝ → ℝ),
      Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
      (∀ z θ : ℝ, ¬ (0 < z ∧ θ ∈ Set.Ioo 0 (Real.pi / 2)) → w z θ = 0) →
      Work.FTS.VocabO.EllPkgGo α Ce w Φg → Work.FTS.ClassC.EllPkgK α 6 Ce w Φg →
      Work.FTS.StrongPersist.StarPkg6 α Cs Φs →
      (∀ k ∈ ({16, 17, 18, 19} : Finset ℕ),
        Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k)
          ≤ K * (1 + Work.Spaces.HkSq α 7 w) + K * (1 + Work.Spaces.HkSq α 6 w) ^ 2))
    (hmem : ∀ C₀ Ce Cs : ℝ, ∀ α ∈ Set.Ioc (0 : ℝ) 1,
      ∀ (Φs w Φg : ℝ → ℝ → ℝ),
      Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
      (∀ z θ : ℝ, ¬ (0 < z ∧ θ ∈ Set.Ioo 0 (Real.pi / 2)) → w z θ = 0) →
      Work.FTS.VocabO.EllPkgGo α Ce w Φg → Work.FTS.ClassC.EllPkgK α 6 Ce w Φg →
      Work.FTS.StrongPersist.StarPkg6 α Cs Φs →
      ∀ k ∈ Finset.range 20,
        Work.Spaces.HkMem α 6 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k)) :
    ∀ C₀ Ce Cs : ℝ, ∀ α ∈ Set.Ioc (0 : ℝ) 1, ∃ K : ℝ, 0 < K ∧
    ∀ (Φs w Φg : ℝ → ℝ → ℝ),
    Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
    (∀ z θ : ℝ, ¬ (0 < z ∧ θ ∈ Set.Ioo 0 (Real.pi / 2)) → w z θ = 0) →
    Work.FTS.VocabO.EllPkgGo α Ce w Φg → Work.FTS.ClassC.EllPkgK α 6 Ce w Φg →
    Work.FTS.StrongPersist.StarPkg6 α Cs Φs →
    Work.Spaces.HkSq α 6 (Work.Construction.N α (Work.Construction.Ftot α w)
        (fun z θ => Φs z θ + Φg z θ))
      ≤ K * (1 + Work.Spaces.HkSq α 7 w) + K * (1 + Work.Spaces.HkSq α 6 w) ^ 2 := by
  intro C₀ Ce Cs α hαmem
  obtain ⟨Kg, hKg, hg⟩ := hgg C₀ Ce Cs α hαmem
  obtain ⟨Ks, hKs, hs⟩ := hstar C₀ Ce Cs α hαmem
  obtain ⟨Kr, hKr, hr⟩ := hrad C₀ Ce Cs α hαmem
  obtain ⟨Kf, hKf, hf⟩ := hfive C₀ Ce Cs α hαmem
  have hα0 : 0 < α := hαmem.1
  set K : ℝ := max (max Kg Ks) (max Kr Kf) + 1 with hKdef
  refine ⟨(2 : ℝ) ^ 20 * (20 * K), by positivity, ?_⟩
  intro Φs w Φg hw hXw hz hell hK hstar6
  have hg' := hg Φs w Φg hw hXw hz hell hK hstar6
  have hs' := hs Φs w Φg hw hXw hz hell hK hstar6
  have hr' := hr Φs w Φg hw hXw hz hell hK hstar6
  have hf' := hf Φs w Φg hw hXw hz hell hK hstar6
  have hKgK : Kg ≤ K := by
    rw [hKdef]
    linarith [le_max_left (max Kg Ks) (max Kr Kf), le_max_left Kg Ks]
  have hKsK : Ks ≤ K := by
    rw [hKdef]
    linarith [le_max_left (max Kg Ks) (max Kr Kf), le_max_right Kg Ks]
  have hKrK : Kr ≤ K := by
    rw [hKdef]
    linarith [le_max_right (max Kg Ks) (max Kr Kf), le_max_left Kr Kf]
  have hKfK : Kf ≤ K := by
    rw [hKdef]
    linarith [le_max_right (max Kg Ks) (max Kr Kf), le_max_right Kr Kf]
  -- the per-piece bounds with the single constant `K`
  have hA7 : (0 : ℝ) ≤ 1 + Work.Spaces.HkSq α 7 w := by
    have := Work.Spaces.HkSq_nonneg α 7 w
    linarith
  have hA6 : (0 : ℝ) ≤ (1 + Work.Spaces.HkSq α 6 w) ^ 2 := sq_nonneg _
  have mono : ∀ (k : ℕ) {K' : ℝ}, K' ≤ K →
      (Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k)
          ≤ K' * (1 + Work.Spaces.HkSq α 7 w) + K' * (1 + Work.Spaces.HkSq α 6 w) ^ 2) →
      Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k)
          ≤ K * (1 + Work.Spaces.HkSq α 7 w) + K * (1 + Work.Spaces.HkSq α 6 w) ^ 2 := by
    intro k K' hK' h
    exact le_trans h (add_le_add (mul_le_mul_of_nonneg_right hK' hA7)
      (mul_le_mul_of_nonneg_right hK' hA6))
  have hpiece : ∀ k ∈ Finset.range 20,
      Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k)
        ≤ K * (1 + Work.Spaces.HkSq α 7 w) + K * (1 + Work.Spaces.HkSq α 6 w) ^ 2 := by
    intro k hk
    have hk20 : k < 20 := Finset.mem_range.mp hk
    interval_cases k
    · exact mono 0 hKgK (hg'.1)
    · exact mono 1 hKsK (hs' 1 (by decide))
    · exact mono 2 hKsK (hs' 2 (by decide))
    · exact mono 3 hKsK (hs' 3 (by decide))
    · exact mono 4 hKgK (hg'.2.1)
    · exact mono 5 hKsK (hs' 5 (by decide))
    · exact mono 6 hKsK (hs' 6 (by decide))
    · exact mono 7 hKsK (hs' 7 (by decide))
    · exact mono 8 hKgK (hg'.2.2)
    · exact mono 9 hKsK (hs' 9 (by decide))
    · exact mono 10 hKsK (hs' 10 (by decide))
    · exact mono 11 hKsK (hs' 11 (by decide))
    · exact mono 12 hKrK (hr' 12 (by decide))
    · exact mono 13 hKrK (hr' 13 (by decide))
    · exact mono 14 hKrK (hr' 14 (by decide))
    · exact mono 15 hKrK (hr' 15 (by decide))
    · exact mono 16 hKfK (hf' 16 (by decide))
    · exact mono 17 hKfK (hf' 17 (by decide))
    · exact mono 18 hKfK (hf' 18 (by decide))
    · exact mono 19 hKfK (hf' 19 (by decide))
  -- the twenty-piece splitting identity and the subadditivity
  obtain ⟨C1, hC1, hs1⟩ := Work.FTS.StrongEps.ClassCRHS.StarAtomsScaled
  obtain ⟨C2, hC2, hs2⟩ := Work.FTS.StrongEps.ClassCRHS.StarAtomsFK
  obtain ⟨Kbig, hKbig, hdata⟩ :=
    Work.FTS.StrongEps.ClassCRHS.nb_data hαmem hC1 hC2 (hs1 α hαmem) (hs2 α hαmem)
  obtain ⟨hsmAll, -, hid⟩ := hdata hw hXw (le_refl (Work.Spaces.HkNorm α 6 w)) hell
    hstar6.toStarPkgo2
  have hmAll := hmem C₀ Ce Cs α hαmem Φs w Φg hw hXw hz hell hK hstar6
  have hcongr : Work.Spaces.HkSq α 6 (Work.Construction.N α (Work.Construction.Ftot α w)
        (fun z θ => Φs z θ + Φg z θ))
      = Work.Spaces.HkSq α 6 (fun z θ => ∑ k ∈ Finset.range 20,
          Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k z θ) :=
    Work.FTS.EllipticEst.HkSq_congr_open α 6
      (fun z θ hz' hθ hθ2 => hid z θ ⟨hz', hθ, hθ2⟩)
  have hsub := Work.FTS.GalFields.RHS.HkSq_finset_sum_le α 6 hα0 (Finset.range 20)
    (f := fun k => Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k) hsmAll hmAll
  rw [hcongr]
  refine le_trans hsub ?_
  have hsum2 : (∑ k ∈ Finset.range 20,
      Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k))
      ≤ 20 * (K * (1 + Work.Spaces.HkSq α 7 w) + K * (1 + Work.Spaces.HkSq α 6 w) ^ 2) := by
    refine le_trans (Finset.sum_le_sum hpiece) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    norm_num
  calc (2 : ℝ) ^ 20 * ∑ k ∈ Finset.range 20,
        Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k)
      ≤ (2 : ℝ) ^ 20 * (20 * (K * (1 + Work.Spaces.HkSq α 7 w)
          + K * (1 + Work.Spaces.HkSq α 6 w) ^ 2)) :=
        mul_le_mul_of_nonneg_left hsum2 (by positivity)
    _ = ((2 : ℝ) ^ 20 * (20 * K)) * (1 + Work.Spaces.HkSq α 7 w)
        + ((2 : ℝ) ^ 20 * (20 * K)) * (1 + Work.Spaces.HkSq α 6 w) ^ 2 := by ring

/-- **The `BData` of the `N`-block, per `α`, from the four groups.** -/
theorem N_BData_perAlpha_of_groups
    (hgg : ∀ C₀ Ce Cs : ℝ, ∀ α ∈ Set.Ioc (0 : ℝ) 1, ∃ K : ℝ, 0 < K ∧
      ∀ (Φs w Φg : ℝ → ℝ → ℝ),
      Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
      (∀ z θ : ℝ, ¬ (0 < z ∧ θ ∈ Set.Ioo 0 (Real.pi / 2)) → w z θ = 0) →
      Work.FTS.VocabO.EllPkgGo α Ce w Φg → Work.FTS.ClassC.EllPkgK α 6 Ce w Φg →
      Work.FTS.StrongPersist.StarPkg6 α Cs Φs →
      (Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 0)
          ≤ K * (1 + Work.Spaces.HkSq α 7 w) + K * (1 + Work.Spaces.HkSq α 6 w) ^ 2) ∧
      (Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 4)
          ≤ K * (1 + Work.Spaces.HkSq α 7 w) + K * (1 + Work.Spaces.HkSq α 6 w) ^ 2) ∧
      (Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 8)
          ≤ K * (1 + Work.Spaces.HkSq α 7 w) + K * (1 + Work.Spaces.HkSq α 6 w) ^ 2))
    (hstar : ∀ C₀ Ce Cs : ℝ, ∀ α ∈ Set.Ioc (0 : ℝ) 1, ∃ K : ℝ, 0 < K ∧
      ∀ (Φs w Φg : ℝ → ℝ → ℝ),
      Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
      (∀ z θ : ℝ, ¬ (0 < z ∧ θ ∈ Set.Ioo 0 (Real.pi / 2)) → w z θ = 0) →
      Work.FTS.VocabO.EllPkgGo α Ce w Φg → Work.FTS.ClassC.EllPkgK α 6 Ce w Φg →
      Work.FTS.StrongPersist.StarPkg6 α Cs Φs →
      (∀ k ∈ ({1, 2, 3, 5, 6, 7, 9, 10, 11} : Finset ℕ),
        Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k)
          ≤ K * (1 + Work.Spaces.HkSq α 7 w) + K * (1 + Work.Spaces.HkSq α 6 w) ^ 2))
    (hrad : ∀ C₀ Ce Cs : ℝ, ∀ α ∈ Set.Ioc (0 : ℝ) 1, ∃ K : ℝ, 0 < K ∧
      ∀ (Φs w Φg : ℝ → ℝ → ℝ),
      Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
      (∀ z θ : ℝ, ¬ (0 < z ∧ θ ∈ Set.Ioo 0 (Real.pi / 2)) → w z θ = 0) →
      Work.FTS.VocabO.EllPkgGo α Ce w Φg → Work.FTS.ClassC.EllPkgK α 6 Ce w Φg →
      Work.FTS.StrongPersist.StarPkg6 α Cs Φs →
      (∀ k ∈ ({12, 13, 14, 15} : Finset ℕ),
        Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k)
          ≤ K * (1 + Work.Spaces.HkSq α 7 w) + K * (1 + Work.Spaces.HkSq α 6 w) ^ 2))
    (hfive : ∀ C₀ Ce Cs : ℝ, ∀ α ∈ Set.Ioc (0 : ℝ) 1, ∃ K : ℝ, 0 < K ∧
      ∀ (Φs w Φg : ℝ → ℝ → ℝ),
      Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
      (∀ z θ : ℝ, ¬ (0 < z ∧ θ ∈ Set.Ioo 0 (Real.pi / 2)) → w z θ = 0) →
      Work.FTS.VocabO.EllPkgGo α Ce w Φg → Work.FTS.ClassC.EllPkgK α 6 Ce w Φg →
      Work.FTS.StrongPersist.StarPkg6 α Cs Φs →
      (∀ k ∈ ({16, 17, 18, 19} : Finset ℕ),
        Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k)
          ≤ K * (1 + Work.Spaces.HkSq α 7 w) + K * (1 + Work.Spaces.HkSq α 6 w) ^ 2))
    (hmem : ∀ C₀ Ce Cs : ℝ, ∀ α ∈ Set.Ioc (0 : ℝ) 1,
      ∀ (Φs w Φg : ℝ → ℝ → ℝ),
      Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
      (∀ z θ : ℝ, ¬ (0 < z ∧ θ ∈ Set.Ioo 0 (Real.pi / 2)) → w z θ = 0) →
      Work.FTS.VocabO.EllPkgGo α Ce w Φg → Work.FTS.ClassC.EllPkgK α 6 Ce w Φg →
      Work.FTS.StrongPersist.StarPkg6 α Cs Φs →
      ∀ k ∈ Finset.range 20,
        Work.Spaces.HkMem α 6 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k)) :
    ∀ C₀ Ce Cs : ℝ, ∀ α ∈ Set.Ioc (0 : ℝ) 1, ∃ K : ℝ, 0 < K ∧
    ∀ (Φs w Φg : ℝ → ℝ → ℝ),
    Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
    (∀ z θ : ℝ, ¬ (0 < z ∧ θ ∈ Set.Ioo 0 (Real.pi / 2)) → w z θ = 0) →
    Work.FTS.VocabO.EllPkgGo α Ce w Φg → Work.FTS.ClassC.EllPkgK α 6 Ce w Φg →
    Work.FTS.StrongPersist.StarPkg6 α Cs Φs →
    Work.FTS.StrongEps.E4R3.Apriori4Proofs.BData α w K
      (Work.FTS.StrongEps.E4R3.Apriori4Proofs.blkN α Φs w Φg) := by
  intro C₀ Ce Cs α hαmem
  obtain ⟨K6, hK6, h6⟩ :=
    N_b6_perAlpha_of_groups hgg hstar hrad hfive hmem C₀ Ce Cs α hαmem
  obtain ⟨K4, hK4, h4⟩ := Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux.N_b4 C₀ Ce Cs
  have hα0 : 0 < α := hαmem.1
  have hα1 : α ≤ 1 := hαmem.2
  have h4' := h4 α hαmem
  refine ⟨max K6 K4 + 1, by positivity, ?_⟩
  intro Φs w Φg hw hXw hz hell hK hstar6
  -- the weak vanishing form, for the truncation toolkit
  have hzweak : ∀ z θ : ℝ, 0 < z → θ ∉ Set.Ioo 0 (Real.pi / 2) → w z θ = 0 :=
    fun z θ hz' hθ => hz z θ (fun hh => hθ hh.2)
  -- the truncated datum
  have hcls' : Work.FTS.ClassC.ClassC α
      (Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux.ztrunc w) :=
    Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux.ztrunc_classC hw hzweak
  have hXn' : Work.FTS.Nonlin.Xn α
      (Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux.ztrunc w) ≤ C₀ * α ^ 2 := by
    rw [Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux.Xn_ztrunc]
    exact hXw
  have hz' : ∀ z θ : ℝ, ¬ (0 < z ∧ θ ∈ Set.Ioo 0 (Real.pi / 2)) →
      Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux.ztrunc w z θ = 0 :=
    Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux.ztrunc_strong_zero hw hzweak
  obtain ⟨hgo', hK'⟩ :=
    Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux.ztrunc_pkgs hw hell hK
  have hNae : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Construction.N α (Work.Construction.Ftot α
          (Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux.ztrunc w))
          (fun z θ => Φs z θ + Φg z θ) z θ
        = Work.Construction.N α (Work.Construction.Ftot α w)
          (fun z θ => Φs z θ + Φg z θ) z θ :=
    fun z θ hzθ => Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux.N_ztrunc_agree z θ hzθ
  have hsqN : ∀ k : ℕ, Work.Spaces.HkSq α k
        (Work.Construction.N α (Work.Construction.Ftot α
          (Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux.ztrunc w))
          (fun z θ => Φs z θ + Φg z θ))
      = Work.Spaces.HkSq α k (Work.Construction.N α (Work.Construction.Ftot α w)
          (fun z θ => Φs z θ + Φg z θ)) :=
    fun k => Work.FTS.EllipticEst.HkSq_congr_open α k
      (fun z θ hz' hθ hθ2 => hNae z θ ⟨hz', hθ, hθ2⟩)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux.smoothOpen_blkN hα0 hα1 hw hell hstar6
  · exact Work.FTS.StrongPersist.H6Pair6Aux.HkMem_congr_Qd hNae
      (Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux.hkMem_blkN hα0 hα1 hcls' hz' hgo' hK'
        hstar6)
  · have h := h4' Φs (Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux.ztrunc w) Φg
      hcls' hXn' hz' hgo' hK' hstar6
    rw [Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux.HkSq_ztrunc] at h
    rw [hsqN 4] at h
    refine le_trans h ?_
    refine mul_le_mul_of_nonneg_right ?_ (by
      have := Work.Spaces.HkSq_nonneg α 5 w
      linarith)
    linarith [le_max_right K6 K4]
  · have h := h6 Φs (Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux.ztrunc w) Φg
      hcls' hXn' hz' hgo' hK' hstar6
    simp only [Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux.HkSq_ztrunc] at h
    rw [hsqN 6] at h
    have hle : K6 ≤ max K6 K4 + 1 := by linarith [le_max_left K6 K4]
    have h5 : (0 : ℝ) ≤ 1 + Work.Spaces.HkSq α 7 w := by
      have := Work.Spaces.HkSq_nonneg α 7 w
      linarith
    have h6'' : (0 : ℝ) ≤ (1 + Work.Spaces.HkSq α 6 w) ^ 2 := sq_nonneg _
    calc Work.Spaces.HkSq α 6 (Work.Construction.N α (Work.Construction.Ftot α w)
            (fun z θ => Φs z θ + Φg z θ))
        ≤ K6 * (1 + Work.Spaces.HkSq α 7 w) + K6 * (1 + Work.Spaces.HkSq α 6 w) ^ 2 := h
      _ ≤ (max K6 K4 + 1) * (1 + Work.Spaces.HkSq α 7 w)
            + (max K6 K4 + 1) * (1 + Work.Spaces.HkSq α 6 w) ^ 2 :=
          add_le_add (mul_le_mul_of_nonneg_right hle h5) (mul_le_mul_of_nonneg_right hle h6'')

/-- **`S2` from the four groups of the `N`-block.** -/
theorem S2_of_groups
    (hgg : ∀ C₀ Ce Cs : ℝ, ∀ α ∈ Set.Ioc (0 : ℝ) 1, ∃ K : ℝ, 0 < K ∧
      ∀ (Φs w Φg : ℝ → ℝ → ℝ),
      Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
      (∀ z θ : ℝ, ¬ (0 < z ∧ θ ∈ Set.Ioo 0 (Real.pi / 2)) → w z θ = 0) →
      Work.FTS.VocabO.EllPkgGo α Ce w Φg → Work.FTS.ClassC.EllPkgK α 6 Ce w Φg →
      Work.FTS.StrongPersist.StarPkg6 α Cs Φs →
      (Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 0)
          ≤ K * (1 + Work.Spaces.HkSq α 7 w) + K * (1 + Work.Spaces.HkSq α 6 w) ^ 2) ∧
      (Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 4)
          ≤ K * (1 + Work.Spaces.HkSq α 7 w) + K * (1 + Work.Spaces.HkSq α 6 w) ^ 2) ∧
      (Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 8)
          ≤ K * (1 + Work.Spaces.HkSq α 7 w) + K * (1 + Work.Spaces.HkSq α 6 w) ^ 2))
    (hstar : ∀ C₀ Ce Cs : ℝ, ∀ α ∈ Set.Ioc (0 : ℝ) 1, ∃ K : ℝ, 0 < K ∧
      ∀ (Φs w Φg : ℝ → ℝ → ℝ),
      Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
      (∀ z θ : ℝ, ¬ (0 < z ∧ θ ∈ Set.Ioo 0 (Real.pi / 2)) → w z θ = 0) →
      Work.FTS.VocabO.EllPkgGo α Ce w Φg → Work.FTS.ClassC.EllPkgK α 6 Ce w Φg →
      Work.FTS.StrongPersist.StarPkg6 α Cs Φs →
      (∀ k ∈ ({1, 2, 3, 5, 6, 7, 9, 10, 11} : Finset ℕ),
        Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k)
          ≤ K * (1 + Work.Spaces.HkSq α 7 w) + K * (1 + Work.Spaces.HkSq α 6 w) ^ 2))
    (hrad : ∀ C₀ Ce Cs : ℝ, ∀ α ∈ Set.Ioc (0 : ℝ) 1, ∃ K : ℝ, 0 < K ∧
      ∀ (Φs w Φg : ℝ → ℝ → ℝ),
      Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
      (∀ z θ : ℝ, ¬ (0 < z ∧ θ ∈ Set.Ioo 0 (Real.pi / 2)) → w z θ = 0) →
      Work.FTS.VocabO.EllPkgGo α Ce w Φg → Work.FTS.ClassC.EllPkgK α 6 Ce w Φg →
      Work.FTS.StrongPersist.StarPkg6 α Cs Φs →
      (∀ k ∈ ({12, 13, 14, 15} : Finset ℕ),
        Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k)
          ≤ K * (1 + Work.Spaces.HkSq α 7 w) + K * (1 + Work.Spaces.HkSq α 6 w) ^ 2))
    (hfive : ∀ C₀ Ce Cs : ℝ, ∀ α ∈ Set.Ioc (0 : ℝ) 1, ∃ K : ℝ, 0 < K ∧
      ∀ (Φs w Φg : ℝ → ℝ → ℝ),
      Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
      (∀ z θ : ℝ, ¬ (0 < z ∧ θ ∈ Set.Ioo 0 (Real.pi / 2)) → w z θ = 0) →
      Work.FTS.VocabO.EllPkgGo α Ce w Φg → Work.FTS.ClassC.EllPkgK α 6 Ce w Φg →
      Work.FTS.StrongPersist.StarPkg6 α Cs Φs →
      (∀ k ∈ ({16, 17, 18, 19} : Finset ℕ),
        Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k)
          ≤ K * (1 + Work.Spaces.HkSq α 7 w) + K * (1 + Work.Spaces.HkSq α 6 w) ^ 2))
    (hmem : ∀ C₀ Ce Cs : ℝ, ∀ α ∈ Set.Ioc (0 : ℝ) 1,
      ∀ (Φs w Φg : ℝ → ℝ → ℝ),
      Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
      (∀ z θ : ℝ, ¬ (0 < z ∧ θ ∈ Set.Ioo 0 (Real.pi / 2)) → w z θ = 0) →
      Work.FTS.VocabO.EllPkgGo α Ce w Φg → Work.FTS.ClassC.EllPkgK α 6 Ce w Φg →
      Work.FTS.StrongPersist.StarPkg6 α Cs Φs →
      ∀ k ∈ Finset.range 20,
        Work.Spaces.HkMem α 6 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k)) :
    S2Stmt := by
  have hN := N_BData_perAlpha_of_groups hgg hstar hrad hfive hmem
  intro C₀ Ce Cs
  obtain ⟨aL, haL, hLall⟩ := Work.FTS.StrongEps.E4R3.RawE6Aux.bdata_blkLin C₀
  obtain ⟨a0, ha0, h0all⟩ := Work.FTS.StrongEps.E4R3.Apriori4Proofs.blkN0_BData_blocks C₀
  refine ⟨min (min aL a0) 1, lt_min (lt_min haL ha0) one_pos, ?_⟩
  intro α hα
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := le_trans hα.2 (min_le_right _ _)
  have hαL : α ∈ Set.Ioc 0 aL :=
    ⟨hα0, le_trans hα.2 (le_trans (min_le_left _ _) (min_le_left _ _))⟩
  have hα0' : α ∈ Set.Ioc 0 a0 :=
    ⟨hα0, le_trans hα.2 (le_trans (min_le_left _ _) (min_le_right _ _))⟩
  obtain ⟨KL, hKL, hL⟩ := hLall α hαL
  obtain ⟨K0, hK0, h0⟩ := h0all α hα0'
  obtain ⟨KM, hKM, hM⟩ :=
    Work.FTS.StrongEps.E4R3.RawE6Aux.bdata_blkMu C₀ α ⟨hα0, hα1⟩
  obtain ⟨KS, hKS, hS⟩ :=
    Work.FTS.StrongEps.E4R3.RawE6Aux.bdata_blkNstar C₀ α ⟨hα0, hα1⟩
  obtain ⟨KN, hKN, hN'⟩ := hN C₀ Ce Cs α ⟨hα0, hα1⟩
  refine ⟨Real.sqrt (16 * (KL + KM + K0 + KN + KS + 1)) + 1, by positivity, ?_⟩
  intro ρ Φs E hρ hEll hstar6 hml ε hε g τ hcls hXw
  set w : Fn := slice (Work.FTS.StrongEps.JfamP ρ ε g) τ with hw
  have hzero : ∀ z θ : ℝ, ¬ (0 < z ∧ θ ∈ Set.Ioo 0 (Real.pi / 2)) → w z θ = 0 := by
    intro z θ hzq
    rw [hw]
    exact Work.FTS.StrongEps.E4R3.Apriori4Proofs.Pz_Jeps_eq_zero_of_not_mem_quadrant
      (ρ := ρ) (ε := ε) (h := slice g τ) hzq
  have hml' := hml w hcls hXw
  have hμ : |Work.FTS.StrongEps.E4R3.Apriori4Proofs.muBlk α Φs w (E w)| ≤ 1 / 2 := by
    have h := hml'.1
    rwa [Work.FTS.StrongEps.E4R3.Apriori4Proofs.muDyn_const_eq α Φs E w] at h
  have hlam : |Work.Construction.lamfun
      (Work.FTS.StrongEps.E4R3.Apriori4Proofs.muBlk α Φs w (E w))| ≤ 1 := by
    have h := hml'.2
    rwa [Work.FTS.StrongEps.E4R3.Apriori4Proofs.lamDyn_const_eq α Φs E w] at h
  have key := Work.FTS.StrongEps.E4R3.RawE6Aux.semitame_of_bdata
    (C₀ := C₀) (Ce := Ce) (Cs := Cs) (α := α) ⟨hα0, hα1⟩ hKL hKM hK0 hKN hKS
    hL hM h0
    (fun {Φs w Φg} hcls' hXw' hz' hell' hK' hstar' =>
      hN' Φs w Φg hcls' hXw' hz' hell' hK' hstar')
    hS hcls hXw hμ hlam hμ hzero (hEll w hcls).1 (hEll w hcls).2 hstar6
  have hwp : Work.FTS.StrongEps.epsWP α ρ ε Φs E g τ
      = Work.FTS.StrongEps.E4R3.Apriori4Proofs.epsWBlk α Φs w (E w)
          (Work.FTS.StrongEps.E4R3.Apriori4Proofs.muBlk α Φs w (E w))
          (Work.Construction.lamfun
            (Work.FTS.StrongEps.E4R3.Apriori4Proofs.muBlk α Φs w (E w))) := by
    rw [hw]
    exact Work.FTS.StrongEps.E4R3.Apriori4Proofs.epsWP_eq_epsWBlk α ρ ε Φs E g τ
  rw [hwp]
  exact key

/-- **`S2` from the four groups** (`S2_of_groups` with the abbreviation types). -/
theorem S2_of_groups' (hgg : GGStmt) (hstar : StarStmt) (hrad : RadStmt) (hfive : FiveStmt)
    (hmem : MemStmt) : S2Stmt :=
  S2_of_groups hgg hstar hrad hfive hmem

/-- **The `gg`-group from `NBlk 0` and the two pieces `NBlk 4, 8`.** -/
theorem GGStmt_of_p0_p48 (h0 : P0Stmt) (h48 : P48Stmt) : GGStmt := by
  intro C₀ Ce Cs α hα
  obtain ⟨K0, hK0, h0'⟩ := h0 C₀ Ce Cs α hα
  obtain ⟨K48, hK48, h48'⟩ := h48 C₀ Ce Cs α hα
  refine ⟨max K0 K48 + 1, by positivity, ?_⟩
  intro Φs w Φg hcls hXw hz hell hK hstar
  obtain ⟨h4, h8⟩ := h48' Φs w Φg hcls hXw hz hell hK hstar
  have h0'' := h0' Φs w Φg hcls hXw hz hell hK hstar
  have hA7 : (0 : ℝ) ≤ 1 + Work.Spaces.HkSq α 7 w := by
    have := Work.Spaces.HkSq_nonneg α 7 w
    linarith
  have hA6 : (0 : ℝ) ≤ (1 + Work.Spaces.HkSq α 6 w) ^ 2 := sq_nonneg _
  have hle0 : K0 ≤ max K0 K48 + 1 := by linarith [le_max_left K0 K48]
  have hle4 : K48 ≤ max K0 K48 + 1 := by linarith [le_max_right K0 K48]
  refine ⟨?_, ?_, ?_⟩
  · exact le_trans h0'' (add_le_add (mul_le_mul_of_nonneg_right hle0 hA7)
      (mul_le_mul_of_nonneg_right hle0 hA6))
  · exact le_trans h4 (add_le_add (mul_le_mul_of_nonneg_right hle4 hA7)
      (mul_le_mul_of_nonneg_right hle4 hA6))
  · exact le_trans h8 (add_le_add (mul_le_mul_of_nonneg_right hle4 hA7)
      (mul_le_mul_of_nonneg_right hle4 hA6))

end Work.FTS.StrongEps.E4R3.Nblock6
