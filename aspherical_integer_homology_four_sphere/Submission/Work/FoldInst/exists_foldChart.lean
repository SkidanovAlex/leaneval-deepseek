/-
# Existence of the fold chart of a fold class of `M̄`

For each of the 98 fold classes `i` of `M̄` (codimension `c = foldCodim i`) the blueprint glues the
`2^c` Voronoi pieces `Dvor i r` of the two copies of the truncated 24-cell into a single chart of
`M̄`.  This file proves the existence of that chart:

    ∃ Φ : OpenPartialHomeomorph M̄ E4,
      Φ.source = ⋃ r, mk '' Dvor i r ∧
      ∀ r x, x ∈ Dvor i r → Φ (mk x) = foldTheta i r x.2.1

The chart is built with the generic gluing lemma `Work.FoldInst.fold_chart_of_glued`
(`Submission.Work.FoldInst.fold_chart_of_glued`), applied to `Y = M̄` with the reindexed pieces

    U ρ = mk '' Dvor i (signVecNeg ρ)     (`ρ : Sign c = Fin c → Bool`)

and the glued chart function `foldPhi i : M̄ → E4`.  The reindexing is forced by the orthant
convention of `Work.Fold`: the image of the piece `Dvor i r` lies in the orthant of index
`signVecNeg r` (`fold_theta_orthant`), and `Work.Fold.reflVec` is `+1` on `true`.  The hypotheses
of the gluing lemma are:

* `hopen` / `hcont` — the union of the pieces is open (`fold_source_open_dvor`) and `foldPhi i` is
  continuous on it (`foldPhi_continuousOn`);
* `horth` — `fold_theta_orthant`, via `Dvor i r ⊆ Clift i r` (`hcross_Dvor_subset_Clift`);
* `hinj` — the cross lemma `foldPsi_hcross` for the glued value `foldPsi i`, transported through
  `foldPhi_mk`;
* `himage` — the fold lemma: the image of a piece is the `reflVec`-reflection of the image of the
  root piece (`foldPsi_image_reflVec`, from `foldTheta_flip` and `actX_image_Dvor`);
* `htarget_open` — the image of the root piece is relatively open in the positive orthant
  (`htarget_open`);
* the local inverse `inv ρ` — the Klein-coordinate inverse `foldInv` of the chart
  (`foldInv_foldTheta`, `continuousOn_foldInv`), lifted into the copy `foldCr i (signVecNeg ρ)` of
  `Q̄` by `piecePt`.

The value of the chart on a piece is then read off from the gluing lemma (`hval`) and the two
identifications `foldPhi_mk` and `foldPsi_eq`.
-/
import Mathlib
import Submission.Work.FoldInst.FoldInvDefs
import Submission.Work.FoldInst.foldInv_foldTheta
import Submission.Work.FoldInst.continuousOn_foldInv
import Submission.Work.FoldInst.foldPsi_image_reflVec
import Submission.Work.FoldInst.fold_chart_of_glued
import Submission.Work.FoldInst.fold_source_open_dvor
import Submission.Work.FoldInst.foldPsi_continuousOn
import Submission.Work.FoldInst.foldPsi_hagree
import Submission.Work.FoldInst.foldPsi_hcross
import Submission.Work.FoldInst.htarget_open
import Submission.Work.FoldInst.foldPhi_continuousOn
import Submission.Work.FoldInst.foldPhi_mk
import Submission.Work.FoldInst.foldPsi_eq

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

namespace Work.FoldInst

open Set

/-! ### elementary facts -/

theorem signVecNeg_involutive {c : ℕ} (r : Fin c → Bool) :
    Work.Fold.signVecNeg (Work.Fold.signVecNeg r) = r := by
  funext t
  simp [Work.Fold.signVecNeg]

theorem signVecNeg_oneSign {c : ℕ} :
    Work.Fold.signVecNeg (Work.Fold.oneSign c) = (fun _ => false) := by
  funext t
  simp [Work.Fold.signVecNeg, Work.Fold.oneSign]

/-! ### the canonical lift -/

theorem foldInv_mem_Qbar (i : Fin 98) (r : Fin (foldCodim i) → Bool) {z : E4}
    (hz : z ∈ foldPsi i '' Dvor i r) : foldInv i r z ∈ Qbar := by
  obtain ⟨x, hx, hxz⟩ := exists_witness_of_mem i r hz
  rw [← hxz, foldInv_foldTheta i r (Dvor_subset_ball i r hx)]
  exact x.2.2

theorem piecePt_mem_Dvor (i : Fin 98) (r : Fin (foldCodim i) → Bool) {z : E4}
    (hz : z ∈ foldPsi i '' Dvor i r) : piecePt i r z ∈ Dvor i r := by
  obtain ⟨x, hx, hxz⟩ := exists_witness_of_mem i r hz
  have hQ := foldInv_mem_Qbar i r hz
  have hV : foldInv i r z ∈ VoronoiOpen i r := by
    rw [← hxz, foldInv_foldTheta i r (Dvor_subset_ball i r hx)]
    exact hx.2
  rw [piecePt, dite_eq_left hQ, mem_Dvor]
  exact ⟨rfl, hV⟩

theorem foldTheta_foldInv_of_mem (i : Fin 98) (r : Fin (foldCodim i) → Bool) {z : E4}
    (hz : z ∈ foldPsi i '' Dvor i r) : foldTheta i r (foldInv i r z) = z := by
  obtain ⟨x, hx, hxz⟩ := exists_witness_of_mem i r hz
  rw [← hxz, foldInv_foldTheta i r (Dvor_subset_ball i r hx)]

theorem continuousOn_mkPiece (i : Fin 98) (r : Fin (foldCodim i) → Bool) :
    ContinuousOn (fun z => mk (piecePt i r z)) (foldPsi i '' Dvor i r) := by
  have hT : foldPsi i '' Dvor i r ⊆ foldTheta i r '' HypModel.ball :=
    fun z hz => mem_image_ball_of_mem i r hz
  have hInv : ContinuousOn (foldInv i r) (foldPsi i '' Dvor i r) :=
    (continuousOn_foldInv i r).mono hT
  rw [continuousOn_iff_continuous_domRestrict]
  have hQ : ∀ z : ↥(foldPsi i '' Dvor i r), foldInv i r z.1 ∈ Qbar :=
    fun z => foldInv_mem_Qbar i r z.2
  have h1 : Continuous (fun z : ↥(foldPsi i '' Dvor i r) => foldInv i r z.1) :=
    continuousOn_iff_continuous_domRestrict.mp hInv
  have h2 : Continuous (fun z : ↥(foldPsi i '' Dvor i r) =>
      (⟨foldInv i r z.1, hQ z⟩ : Qbar)) := Continuous.subtype_mk h1 hQ
  have h3 : Continuous (fun z : ↥(foldPsi i '' Dvor i r) =>
      ((foldCr i r, (⟨foldInv i r z.1, hQ z⟩ : Qbar)) : ZMod 2 × Qbar)) :=
    continuous_const.prodMk h2
  have h4 : Continuous (fun z : ↥(foldPsi i '' Dvor i r) =>
      mk ((foldCr i r, (⟨foldInv i r z.1, hQ z⟩ : Qbar)) : Xbar)) :=
    continuous_quotient_mk'.comp h3
  refine h4.congr fun z => ?_
  exact (mk_piecePt_eq (hQ z)).symm



/-! ### the assembly -/

theorem exists_foldChart (i : Fin 98) :
    ∃ Φ : OpenPartialHomeomorph Mbar E4,
      Φ.source = ⋃ r : Fin (foldCodim i) → Bool, mk '' Dvor i r ∧
      (∀ (r : Fin (foldCodim i) → Bool) (x : Xbar), x ∈ Dvor i r → Φ (mk x) = foldTheta i r x.2.1) := by
  classical
  have hc4 : foldCodim i ≤ 4 := le_trans (foldCodim_le i) (by norm_num)
  let U : Work.Fold.Sign (foldCodim i) → Set Mbar :=
    fun ρ => mk '' Dvor i (Work.Fold.signVecNeg ρ)
  have hUeq : (⋃ ρ, U ρ) = (⋃ r : Fin (foldCodim i) → Bool, mk '' Dvor i r) := by
    apply le_antisymm
    · refine iUnion_subset fun ρ => ?_
      exact subset_iUnion (fun r => mk '' Dvor i r) (Work.Fold.signVecNeg ρ)
    · refine iUnion_subset fun r => ?_
      have h : mk '' Dvor i r = U (Work.Fold.signVecNeg r) := by
        show mk '' Dvor i r = mk '' Dvor i (Work.Fold.signVecNeg (Work.Fold.signVecNeg r))
        rw [signVecNeg_involutive]
      rw [h]
      exact subset_iUnion U (Work.Fold.signVecNeg r)
  have himg_eq : ∀ r : Fin (foldCodim i) → Bool,
      foldPhi i '' (mk '' Dvor i r) = foldPsi i '' Dvor i r := by
    intro r
    rw [← Set.image_comp]
    exact Set.image_congr fun x hx => foldPhi_mk i (Set.mem_iUnion.mpr ⟨r, hx⟩)
  have htarget_eq : foldPhi i '' U (Work.Fold.oneSign (foldCodim i))
      = foldPsi i '' Dvor i (fun _ => false) := by
    show foldPhi i '' (mk '' Dvor i (Work.Fold.signVecNeg (Work.Fold.oneSign (foldCodim i)))) = _
    rw [signVecNeg_oneSign]
    exact himg_eq _
  have hopen : IsOpen (⋃ ρ, U ρ) := hUeq ▸ (fold_source_open_dvor i).1
  have hcont : ContinuousOn (foldPhi i) (⋃ ρ, U ρ) := by
    rw [hUeq]
    exact foldPhi_continuousOn i
  have horth : ∀ ρ ⦃p : Mbar⦄, p ∈ U ρ → foldPhi i p ∈ Work.Fold.orthant ρ := by
    intro ρ p hp
    obtain ⟨x, hx, rfl⟩ := hp
    rw [foldPhi_mk i (Set.mem_iUnion.mpr ⟨Work.Fold.signVecNeg ρ, hx⟩), foldPsi_eq i hx]
    have h := fold_theta_orthant i (Work.Fold.signVecNeg ρ) x
      (hcross_Dvor_subset_Clift i (Work.Fold.signVecNeg ρ) hx)
    rwa [signVecNeg_involutive] at h
  have hinj : Set.InjOn (foldPhi i) (⋃ ρ, U ρ) := by
    intro p hp q hq hpq
    obtain ⟨r, hp'⟩ := Set.mem_iUnion.mp hp
    obtain ⟨s, hq'⟩ := Set.mem_iUnion.mp hq
    obtain ⟨x, hx, rfl⟩ := hp'
    obtain ⟨x', hx', rfl⟩ := hq'
    have h1 : foldPsi i x = foldPsi i x' := by
      rw [← foldPhi_mk i (Set.mem_iUnion.mpr ⟨Work.Fold.signVecNeg r, hx⟩),
        ← foldPhi_mk i (Set.mem_iUnion.mpr ⟨Work.Fold.signVecNeg s, hx'⟩)]
      exact hpq
    exact Quotient.sound (foldPsi_hcross i (Set.mem_iUnion.mpr ⟨Work.Fold.signVecNeg r, hx⟩)
      (Set.mem_iUnion.mpr ⟨Work.Fold.signVecNeg s, hx'⟩) h1)
  have himage : ∀ ρ, foldPhi i '' U ρ
      = Work.Fold.reflVec ρ '' (foldPhi i '' U (Work.Fold.oneSign (foldCodim i))) := by
    intro ρ
    have h1 : foldPhi i '' U ρ = foldPsi i '' Dvor i (Work.Fold.signVecNeg ρ) :=
      himg_eq (Work.Fold.signVecNeg ρ)
    rw [h1, htarget_eq, foldPsi_image_reflVec i (Work.Fold.signVecNeg ρ),
      signVecNeg_involutive]
  have htarget : Work.Fold.IsRelOpen (Work.Fold.posOrthant (foldCodim i))
      (foldPhi i '' U (Work.Fold.oneSign (foldCodim i))) := by
    rw [htarget_eq]
    exact htarget_open i
  let inv : Work.Fold.Sign (foldCodim i) → E4 → Mbar :=
    fun ρ z => mk (piecePt i (Work.Fold.signVecNeg ρ) z)
  have inv_mem : ∀ ρ ⦃x : E4⦄, x ∈ foldPhi i '' U ρ → inv ρ x ∈ U ρ := by
    intro ρ x hx
    have hz : x ∈ foldPsi i '' Dvor i (Work.Fold.signVecNeg ρ) := by
      rw [← himg_eq (Work.Fold.signVecNeg ρ)]
      exact hx
    exact ⟨piecePt i (Work.Fold.signVecNeg ρ) x,
      piecePt_mem_Dvor i (Work.Fold.signVecNeg ρ) hz, rfl⟩
  have inv_apply : ∀ ρ ⦃x : E4⦄, x ∈ foldPhi i '' U ρ → foldPhi i (inv ρ x) = x := by
    intro ρ x hx
    have hz : x ∈ foldPsi i '' Dvor i (Work.Fold.signVecNeg ρ) := by
      rw [← himg_eq (Work.Fold.signVecNeg ρ)]
      exact hx
    show foldPhi i (mk (piecePt i (Work.Fold.signVecNeg ρ) x)) = x
    rw [foldPhi_mk i (Set.mem_iUnion.mpr ⟨Work.Fold.signVecNeg ρ,
        piecePt_mem_Dvor i (Work.Fold.signVecNeg ρ) hz⟩),
      foldPsi_eq i (piecePt_mem_Dvor i (Work.Fold.signVecNeg ρ) hz),
      piecePt_snd (foldInv_mem_Qbar i (Work.Fold.signVecNeg ρ) hz)]
    exact foldTheta_foldInv_of_mem i (Work.Fold.signVecNeg ρ) hz
  have inv_cont : ∀ ρ, ContinuousOn (inv ρ) (foldPhi i '' U ρ) := by
    intro ρ
    have h1 : foldPhi i '' U ρ = foldPsi i '' Dvor i (Work.Fold.signVecNeg ρ) :=
      himg_eq (Work.Fold.signVecNeg ρ)
    rw [h1]
    exact continuousOn_mkPiece i (Work.Fold.signVecNeg ρ)
  obtain ⟨Φ, hsrc, -, hval⟩ := fold_chart_of_glued (Y := Mbar) hc4 U (foldPhi i) hopen hcont
    horth hinj himage htarget inv inv_mem inv_apply inv_cont
  refine ⟨Φ, ?_, ?_⟩
  · rw [hsrc, hUeq]
  · intro r x hx
    have hmem : mk x ∈ U (Work.Fold.signVecNeg r) :=
      ⟨x, by rwa [signVecNeg_involutive], rfl⟩
    have hsrcmem : mk x ∈ ⋃ ρ, U ρ := Set.mem_iUnion.mpr ⟨Work.Fold.signVecNeg r, hmem⟩
    calc Φ (mk x) = foldPhi i (mk x) := hval (mk x) (by rw [hsrc]; exact hsrcmem)
      _ = foldPsi i x := foldPhi_mk i (Set.mem_iUnion.mpr ⟨r, hx⟩)
      _ = foldTheta i r x.2.1 := foldPsi_eq i hx

end Work.FoldInst
