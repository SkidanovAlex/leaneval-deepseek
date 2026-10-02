import Mathlib
import Submission.Work.ThomBordism.LeadChapter.Defs
import Submission.Work.ThomBordism.boundarySign_boundaryChartAt_univ
import Submission.Work.ThomBordism.LeadChapter.bdryAux
import Submission.Work.ThomBordism.LeadChapter.psiPhiNeZero
import Submission.Work.ThomBordism.LeadChapter.psiPhiBdryDisj
import Submission.Work.ThomBordism.LeadChapter.psiPhiEqOfEq
import Submission.Work.ThomBordism.LeadChapter.psiPhiCont
import Submission.Work.ThomBordism.LeadChapter.psiBump
import Submission.Work.ThomBordism.LeadChapter.bdryTransferNC

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-! Guidance from the project lead (the requester):

# S2 `Work.ThomBordism.chapter_bdryTransfer` — T1 for an arbitrary half-space chart
File: `Submission/Work/ThomBordism/LeadChapter/S2_bdryTransfer.lean`.

**Statement.** ∃ c = ±1 (after `n hn`) such that for every manifold with boundary `W`, every open partial
homeomorphism `ψ : W ⇀ EuclideanHalfSpace (n+1)` with `q ∈ ∂W ↔ (ψ q).1 0 = 0` on `ψ.source`, boundary
point `y ∈ ψ.source`, closed coordinate half-ball `{dist z (ψ y) ≤ r} ⊆ ψ.target`, interior point
`x₀ ∈ ψ.source` with `dist (ψ x₀) (ψ y) < r`, interior part `κ` (`κ q = (ψ q).1` on `κ.source ⊆ ψ.source`),
boundary part `g` (`g q = tail n (ψ q).1` on `g.source`), and relative class `w` whose local class at
`x₀` is `chartTr κ x₀ (eucFam (n+1))`: `locClass (hPairδ w) ⟨y,hy⟩ = c • chartTr g ⟨y,hy⟩ (eucFam n)`.

**Proof sketch.** Replay the proof of T1 (`boundarySign_boundaryChartAt_univ`) with `ψ` in place of
`chartAt y`: the collapse `bcuPhi` (built from `ψ`, a bump `χ` supported in `ψ.source`, scale `τ`) maps
`(W,∂W)` to the standard half-ball model; `c` is the model constant of `bsu_modelEquation` (take the
same `c` as T1). Where T1 uses `chart_coord_zero_of_mem_boundary` / `chartAt_boundary_coord_zero`, use
`hbd`. Where it uses `icChart`/`boundaryChartAt`, use `κ`/`g` and the relations `hκ`/`hg`.
Alternative: excise to `ψ.source`, transport by `ψ` to an open subset of the half-space, and compare with
T1 applied to the half-space model with its identity chart (needs naturality of `hPairδ`/`locClass`).
T1 itself is the special case ψ = chartAt y (checked in `_lead_design/sanity.lean`).

**Proved lemmas.** `boundarySign_boundaryChartAt_univ` and its local helpers `bcuVa*`, `bcuPhi*`
(`Submission.Work.ThomBordism.boundarySign_boundaryChartAt_univ`), `bsu_modelEquation`
(`…/bsu_modelEquation`), `boundarySign_chartLocal` (`…/boundarySign_chartLocal`),
`boundarySign_transfer_bdry`, `continuous_bcuPhi_and_mem`, `exists_bcu_bump`,
`relHmapOf_injective_of_chartTr_generator`, `PosAtlas.chartTr_eq_of_affine_transition`,
`Work.Orient.exists_halfBallGood_piece`, `locClass_hPairDelta_eq_of_localClass_eq`
(`…/locClass_hPairDelta_eq_of_localClass_eq`), `chartTr_relHmapOf` (`…/chartTr_relHmapOf`).

**Traps.**
- No `respectTransparency false` in the new file (T1's file has it; do not copy the option).
- Keep `(W := TopCat.of ↥((𝓡∂ (n+1)).boundary W))` explicit on the boundary `chartTr`.
- `c` must be ONE constant, outside `∀ W`; do not let it depend on ψ or y.
- No `CompactSpace W` hypothesis is available (deliberately dropped); if T1's argument used
  compactness, use compactness of the closed half-ball `ψ.symm '' B` instead.
-/

namespace Work.ThomBordism.LeadChapter

set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

open scoped Manifold ContDiff Topology in
open CategoryTheory Work.PTGeometric in
theorem chapter_bdryTransfer (n : ℕ) (hn : 1 ≤ n) :
    ∃ c : ℤ, (c = 1 ∨ c = -1) ∧
      ∀ (W : TopCat) [T2Space W]
        [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
        [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) ((⊤ : ENat) : WithTop ENat) W]
        (ψ : OpenPartialHomeomorph W (EuclideanHalfSpace (n + 1)))
        (hbd : ∀ q ∈ ψ.source,
          q ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W ↔ (ψ q).1 0 = 0)
        {y : W} (hy : y ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
        (hyψ : y ∈ ψ.source)
        {r : ℝ} (hr : 0 < r)
        (hball : ∀ z : EuclideanHalfSpace (n + 1), dist z.1 (ψ y).1 ≤ r → z ∈ ψ.target)
        {x₀ : W} (hx₀ψ : x₀ ∈ ψ.source) (hx₀r : dist (ψ x₀).1 (ψ y).1 < r)
        (hx₀int : x₀ ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
        (κ : OpenPartialHomeomorph W (EuclideanSpace ℝ (Fin (n + 1))))
        (hx₀κ : x₀ ∈ κ.source)
        (hκ : ∀ q ∈ κ.source, q ∈ ψ.source ∧ κ q = (ψ q).1)
        (g : OpenPartialHomeomorph ↥((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
          (EuclideanSpace ℝ (Fin n)))
        (hyg : (⟨y, hy⟩ : ↥((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)) ∈ g.source)
        (hg : ∀ q ∈ g.source, (q : W) ∈ ψ.source ∧ g q = Work.PTGeometric.tail n (ψ q).1)
        (w : (Work.Cohomology.relChains W
          ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)).homology (n + 1))
        (hw : (HomologicalComplex.homologyMap
              (Work.Orient.relPunct W ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
                x₀ hx₀int) (n + 1)).hom w
            = Work.PTGeometric.HOF.chartTr κ x₀ hx₀κ
                (Work.PTGeometric.HOF.eucFam (n + 1) (by omega) (κ x₀))),
      Work.Orient.locClass
        (TopCat.of ↥((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)) n
        ((Work.Cohomology.hPairδ W
          ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) n).hom w) ⟨y, hy⟩
      = c • Work.PTGeometric.HOF.chartTr (W := TopCat.of
            ↥((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W))
          g ⟨y, hy⟩ hyg (Work.PTGeometric.HOF.eucFam n hn (g ⟨y, hy⟩)) := by
  classical
  obtain ⟨c, hc, hmodel⟩ := bsu_modelEquation n hn
  refine ⟨c, hc, ?_⟩
  intro W _t2W _chW _ismW ψ hbd y hy hyψ r hr hball x₀ hx₀ψ hx₀r hx₀int κ hx₀κ hκ g hyg hg w hw
  haveI : IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 W := inferInstance
  let B : Set W := (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W
  have hyB : y ∈ B := hy
  -- ===================== the model =====================
  obtain ⟨csM, imM, hbM, _hcolM, hcptM⟩ := stdHalfBallCharted n
  letI : ChartedSpace (EuclideanHalfSpace (n + 1)) ↥(stdHalfBall (n + 1)) := csM
  haveI : IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) ∞ ↥(stdHalfBall (n + 1)) := imM
  haveI : IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 ↥(stdHalfBall (n + 1)) :=
    inferInstance
  haveI : CompactSpace ↥(stdHalfBall (n + 1)) := hcptM
  let W' : TopCat := TopCat.of ↥(stdHalfBall (n + 1))
  let B' : Set W' := stdHalfBallBdry (n + 1)
  let y' : W' := ⟨(0 : EuclideanSpace ℝ (Fin (n + 1))), zero_mem_stdHalfBall (n + 1)⟩
  have hB'eq : (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W' = B' := hbM
  have hy'B' : y' ∈ B' := by
    show (⟨(0 : EuclideanSpace ℝ (Fin (n + 1))), zero_mem_stdHalfBall (n + 1)⟩ : W') ∈
      Work.ThomBordism.stdHalfBallBdry (n + 1)
    rw [Work.ThomBordism.stdHalfBallBdry]
    exact Or.inl (by simp)
  obtain ⟨r', hr'pos, hgood'M, U, hUopen, hy'U, hUsub⟩ :=
    Work.Orient.exists_halfBallGood_piece (n + 1) W' y'
  obtain ⟨ε, hεpos, hballU⟩ := Metric.isOpen_iff.mp hUopen y' hy'U
  -- ===================== the point data =====================
  set c₀ : EuclideanSpace ℝ (Fin (n + 1)) := (ψ y).1 with hc₀def
  have hc₀0 : c₀ 0 = 0 := by
    rw [hc₀def]
    exact (hbd y hyψ).mp hy
  set c₁ : EuclideanSpace ℝ (Fin (n + 1)) := (ψ x₀).1 with hc₁def
  have hpsiChx₀ : psiCh ψ x₀ = c₁ := by rw [psiCh, ← hc₁def]
  have hpsiChy : psiCh ψ y = c₀ := by rw [psiCh, ← hc₀def]
  have hNlt : ‖c₁ - c₀‖ < r := by
    have h := hx₀r
    rw [dist_eq_norm] at h
    exact h
  obtain ⟨ρ, hNρ, hρr⟩ : ∃ ρ : ℝ, ‖c₁ - c₀‖ < ρ ∧ ρ < r :=
    ⟨(‖c₁ - c₀‖ + r) / 2, by linarith, by linarith⟩
  have hρpos : 0 < ρ := lt_of_le_of_lt (norm_nonneg _) hNρ
  obtain ⟨τ, hτpos, hτsmall⟩ : ∃ τ : ℝ, 0 < τ ∧ τ * ‖c₁ - c₀‖ < min (min ε 1) (1 / 2) := by
    rcases eq_or_lt_of_le (norm_nonneg (c₁ - c₀)) with h0 | h0
    · exact ⟨1, one_pos, by rw [← h0, mul_zero]; positivity⟩
    · refine ⟨min (min ε 1) (1 / 2) / (‖c₁ - c₀‖ + 1), by positivity, ?_⟩
      have hden : 0 < ‖c₁ - c₀‖ + 1 := by positivity
      have hm : 0 < min (min ε 1) (1 / 2) := lt_min (lt_min hεpos one_pos) (by norm_num)
      have hfrac : ‖c₁ - c₀‖ / (‖c₁ - c₀‖ + 1) < 1 := by
        rw [div_lt_one hden]; linarith [norm_nonneg (c₁ - c₀)]
      calc min (min ε 1) (1 / 2) / (‖c₁ - c₀‖ + 1) * ‖c₁ - c₀‖
          = min (min ε 1) (1 / 2) * (‖c₁ - c₀‖ / (‖c₁ - c₀‖ + 1)) := by ring
        _ < min (min ε 1) (1 / 2) * 1 := mul_lt_mul_of_pos_left hfrac hm
        _ = min (min ε 1) (1 / 2) := mul_one _
  have hτne : τ ≠ 0 := ne_of_gt hτpos
  have hc₁0 : 0 < c₁ 0 := by
    rw [hc₁def]
    exact psiCh_coord_pos_of_not_bdry ψ hbd hx₀ψ hx₀int
  have hVnorm : ‖psiVa ψ y τ x₀‖ = τ * ‖c₁ - c₀‖ := by
    show ‖τ • (psiCh ψ x₀ - psiCh ψ y)‖ = τ * ‖c₁ - c₀‖
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hτpos, hpsiChx₀, hpsiChy]
  have hVpos : 0 < (psiVa ψ y τ x₀) 0 := by
    rw [psiVa_coord, psiCh_coord_eq_zero_of_bdry ψ hbd hyψ hy, sub_zero, hpsiChx₀]
    exact mul_pos hτpos hc₁0
  have hVne : psiVa ψ y τ x₀ ≠ 0 := by
    intro h0
    have h1 : ‖psiVa ψ y τ x₀‖ = 0 := by rw [h0, norm_zero]
    rw [hVnorm] at h1
    have h2 : ‖c₁ - c₀‖ = 0 := by nlinarith [hτpos]
    have h3 : c₁ = c₀ := sub_eq_zero.mp (norm_eq_zero.mp h2)
    rw [h3, hc₀0] at hc₁0
    exact absurd hc₁0 (lt_irrefl 0)
  have hVle : ‖psiVa ψ y τ x₀‖ ≤ 1 / 2 := by
    rw [hVnorm]
    exact le_of_lt (lt_of_lt_of_le hτsmall (min_le_right _ _))
  have hVlt1 : ‖psiVa ψ y τ x₀‖ < 1 := by
    rw [hVnorm]
    exact lt_of_lt_of_le hτsmall (le_trans (min_le_left _ _) (min_le_right _ _))
  have hVltε : ‖psiVa ψ y τ x₀‖ < ε := by
    rw [hVnorm]
    exact lt_of_lt_of_le hτsmall (le_trans (min_le_left _ _) (min_le_left _ _))
  -- ===================== the bump =====================
  obtain ⟨χ, hχcont, hχ01, hχ1, hχ0⟩ := psiBump n W ψ hyψ hρpos hρr hball
  set Sr : Set W := ψ.symm '' {v : EuclideanHalfSpace (n + 1) | dist v.1 (ψ y).1 ≤ r}
    with hSrdef
  set Sp : Set W := ψ.symm '' {v : EuclideanHalfSpace (n + 1) | dist v.1 (ψ y).1 ≤ ρ}
    with hSpdef
  have hχSp : ∀ z, z ∈ Sp → χ z = 1 := by
    intro z hz; rw [hSpdef] at hz; exact hχ1 z hz
  have hχSr : ∀ z, z ∉ Sr → χ z = 0 := by
    intro z hz; rw [hSrdef] at hz; exact hχ0 z hz
  have hSpSr : Sp ⊆ Sr := by
    rintro z ⟨v, hv, rfl⟩
    exact ⟨v, le_trans hv (le_of_lt hρr), rfl⟩
  have hKsub : Sr ⊆ ψ.source := by
    rintro z ⟨v, hv, rfl⟩
    exact ψ.map_target (hball v hv)
  have hKcpt : IsCompact Sr := by
    rw [hSrdef]
    refine IsCompact.image_of_continuousOn ?_ (ψ.continuousOn_symm.mono ?_)
    · exact isCompact_halfSpace_closedBall n (ψ y).1 r
    · intro v hv
      exact hball v hv
  have hySp : y ∈ Sp := by
    rw [hSpdef]
    exact ⟨ψ y, by simp [le_of_lt hρpos], ψ.left_inv hyψ⟩
  have hχout : ∀ z, z ∉ ψ.source → χ z = 0 :=
    fun z hz => hχ0 z (fun hzS => hz (hKsub hzS))
  have hvan : ∀ z ∈ ψ.source, psiVa ψ y τ z = 0 → χ z = 1 := by
    intro z hz h0
    have hzy : z = y := (psiVa_eq_zero_iff ψ hτne hyψ hz).mp h0
    rw [hzy]
    exact hχSp y hySp
  obtain ⟨hΦcont, hΦmem⟩ := psiPhiCont n W ψ hbd hyψ hy τ hτpos χ Sr hχcont hχ01 hKcpt
    hKsub hχSr hvan
    (fun t₀ v₀ h1 h2 h3 => bcu_profile2_continuousAt n t₀ v₀ h1 h2 h3)
  -- ===================== the collapse =====================
  let Φ : W ⟶ W' := TopCat.ofHom ⟨fun z => (⟨psiPhi ψ y τ χ z, hΦmem z⟩ : W'),
    hΦcont.subtype_mk hΦmem⟩
  have hΦapply : ∀ z : W, ((Φ z : W') : EuclideanSpace ℝ (Fin (n + 1))) = psiPhi ψ y τ χ z :=
    fun z => rfl
  have hΦy : Φ y = y' := by
    show (⟨psiPhi ψ y τ χ y, hΦmem y⟩ : W') = y'
    exact Subtype.ext (psiPhi_self ψ y τ χ (hχSp y hySp))
  have hΦbdry : ∀ z : ↥B, Φ z.1 ∈ B' := by
    intro z
    change ((Φ z.1 : W') : EuclideanSpace ℝ (Fin (n + 1))) 0 = 0 ∨
      ‖((Φ z.1 : W') : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1
    by_cases hzsrc : z.1 ∈ ψ.source
    · exact psiPhiBdryDisj n W ψ hbd hyψ hy hzsrc z.2 hτpos hχ01 hχout (hχSp y hySp)
    · right
      rw [hΦapply, psiPhi_eq_northPole ψ y τ χ z.1 (hχout z.1 hzsrc)]
      exact BCU.bcu_northPole_norm n
  have hΦbcont : Continuous fun z : ↥B =>
      (⟨⟨psiPhi ψ y τ χ z.1, hΦmem z.1⟩, hΦbdry z⟩ : ↥B') :=
    Continuous.subtype_mk ((hΦcont.subtype_mk hΦmem).comp continuous_subtype_val) hΦbdry
  let Φb : TopCat.of ↥B ⟶ TopCat.of ↥B' :=
    TopCat.ofHom ⟨fun z => (⟨⟨psiPhi ψ y τ χ z.1, hΦmem z.1⟩, hΦbdry z⟩ : ↥B'), hΦbcont⟩
  have hΦb_apply : ∀ z : ↥B, ((Φb z : ↥B') : W') = Φ z.1 := fun z => rfl
  have hpairb : ∀ z : ↥B, z ∉ ({⟨y, hyB⟩} : Set ↥B) →
      Φb z ∉ ({Φb ⟨y, hyB⟩} : Set ↥B') := by
    intro z hz hcon
    simp only [Set.mem_singleton_iff] at hz hcon
    refine hz (Subtype.ext ?_)
    have h1 : Φ z.1 = y' := by
      rw [← hΦb_apply z, hcon, hΦb_apply (⟨y, hyB⟩ : ↥B), hΦy]
    have h2 : psiPhi ψ y τ χ z.1 = 0 := by
      have h3 := congrArg (fun u : W' => ((u : W') : EuclideanSpace ℝ (Fin (n + 1)))) h1
      rw [hΦapply] at h3
      rw [show ((y' : W') : EuclideanSpace ℝ (Fin (n + 1))) = 0 from rfl] at h3
      exact h3
    exact absurd h2 (psiPhiNeZero n W ψ hbd hyψ hy hτpos hχ01 hχout
      (fun hzy => hz (Subtype.ext hzy)))
  have hΦbinj : ∀ z : ↥B, z ≠ ⟨y, hyB⟩ → Φb z ≠ Φb ⟨y, hyB⟩ := by
    intro z hz hcon
    exact hpairb z (by simpa using hz) (by simpa using hcon)
  -- ===================== the fibre at `x₀` =====================
  have hx₀Sp : x₀ ∈ Sp := by
    rw [hSpdef]
    refine ⟨ψ x₀, ?_, ψ.left_inv hx₀ψ⟩
    change dist (psiCh ψ x₀) (psiCh ψ y) ≤ ρ
    rw [dist_eq_norm, hpsiChx₀, hpsiChy]
    exact le_of_lt hNρ
  have hSray : ∀ z ∈ ψ.source,
      (∃ m : ℝ, 0 ≤ m ∧ m ≤ 1 ∧ psiVa ψ y τ z = m • psiVa ψ y τ x₀) → z ∈ Sp := by
    intro z hz hray
    obtain ⟨m, hm0, hm1, hm⟩ := hray
    rw [hSpdef]
    refine ⟨ψ z, ?_, ψ.left_inv hz⟩
    change dist (psiCh ψ z) (psiCh ψ y) ≤ ρ
    have h2 : psiCh ψ z - psiCh ψ y = m • (c₁ - c₀) := by
      have h3 : τ • (psiCh ψ z - psiCh ψ y) = τ • (m • (c₁ - c₀)) := by
        have h4 := hm
        rw [psiVa_apply, psiVa_apply, hpsiChx₀, hpsiChy] at h4
        rw [h4, smul_comm]
      exact smul_right_injective _ hτne h3
    have h5 : psiCh ψ z = psiCh ψ y + m • (c₁ - c₀) := sub_eq_iff_eq_add'.mp h2
    rw [dist_eq_norm, h5, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hm0]
    calc m * ‖c₁ - c₀‖ ≤ 1 * ‖c₁ - c₀‖ := mul_le_mul_of_nonneg_right hm1 (norm_nonneg _)
      _ = ‖c₁ - c₀‖ := one_mul _
      _ ≤ ρ := le_of_lt hNρ
  have hVeq : ∀ z ∈ ψ.source, psiVa ψ y τ z = psiVa ψ y τ x₀ → z = x₀ :=
    fun z hz h => psiVa_injOn ψ hτne hz hx₀ψ h
  have hΦx₀val₀ : psiPhi ψ y τ χ x₀ = psiVa ψ y τ x₀ := by
    rw [psiPhi_apply, hχSp x₀ hx₀Sp, (bcu_profile2_properties n).2.2.1]
    exact BCU.bcu_clampBall_eq_self _ (le_of_lt hVlt1)
  have hΦinj : ∀ z : W, Φ z = Φ x₀ → z = x₀ := by
    intro z hz
    have h2 : psiPhi ψ y τ χ z = psiVa ψ y τ x₀ := by
      have h3 := congrArg (fun u : W' => ((u : W') : EuclideanSpace ℝ (Fin (n + 1)))) hz
      rw [hΦapply, hΦapply, hΦx₀val₀] at h3
      exact h3
    exact psiPhiEqOfEq n W ψ hbd hyψ hy hτpos hVpos hVeq hχ01 hχout Sp hχSp hySp hSray
      hVne hVle h2
  have hΦx₀val : ((Φ x₀ : W') : EuclideanSpace ℝ (Fin (n + 1))) = psiVa ψ y τ x₀ := by
    rw [hΦapply]
    exact hΦx₀val₀
  have hx₀int' : Φ x₀ ∉ B' := by
    rw [← Work.ThomBordism.mem_stdHalfBallInterior_iff (n + 1) (Φ x₀)]
    exact ⟨by rw [hΦx₀val]; exact hVpos, by rw [hΦx₀val]; exact hVlt1⟩
  have hx₀srcE : Φ x₀ ∈ (stdIntChart (n + 1)).source :=
    ⟨by rw [hΦx₀val]; exact hVpos, by rw [hΦx₀val]; exact hVlt1⟩
  have hx₀'U : Φ x₀ ∈ U := by
    apply hballU
    rw [Metric.mem_ball, Subtype.dist_eq, hΦx₀val,
      show ((y' : W') : EuclideanSpace ℝ (Fin (n + 1))) = 0 from rfl, dist_zero_right]
    exact hVltε
  have hyeq : ((Φb ⟨y, hyB⟩ : ↥B') : W') = y' := by rw [hΦb_apply, hΦy]
  have hgood'' : Work.Orient.halfBallGood (n + 1) W' (((Φb ⟨y, hyB⟩ : ↥B') : W')) r' := by
    rw [hyeq]; exact hgood'M
  have hx₀'' : Φ x₀ ∈ Work.Orient.halfBallPiece (n + 1) W' (((Φb ⟨y, hyB⟩ : ↥B') : W')) r' := by
    rw [hyeq]; exact hUsub hx₀'U
  have hpairx : ∀ z : W, z ∉ ({x₀} : Set W) → Φ z ∉ ({Φ x₀} : Set W') := by
    intro z hz hcon
    refine hz ?_
    simp only [Set.mem_singleton_iff] at hcon ⊢
    exact hΦinj z hcon
  -- ===================== the interior chart =====================
  have hf₁ : ContinuousOn (fun z : W => (ψ z).1) ψ.source :=
    continuous_subtype_val.comp_continuousOn ψ.continuousOn
  have hf₂ : ContinuousOn (fun z : W => psiVa ψ y τ z) ψ.source := by
    show ContinuousOn (fun z : W => τ • (psiCh ψ z - psiCh ψ y)) ψ.source
    exact (hf₁.sub continuousOn_const).const_smul τ
  have hf₃ : ContinuousOn (fun z : W => ((ψ z).1) 0) ψ.source :=
    (continuous_coord (n + 1)).comp_continuousOn hf₁
  set V₀ : Set W := ψ.source ∩ (fun z : W => (ψ z).1) ⁻¹' Metric.ball ((ψ y).1) ρ with hV₀def
  set U₁ : Set W := ψ.source ∩ (fun z : W => psiVa ψ y τ z) ⁻¹'
    Metric.ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 with hU₁def
  set U₂ : Set W := ψ.source ∩ (fun z : W => ((ψ z).1) 0) ⁻¹' Set.Ioi (0 : ℝ) with hU₂def
  set U₀ : Set W := V₀ ∩ U₁ ∩ U₂ ∩ κ.source with hU₀def
  have hV₀open : IsOpen V₀ := by
    rw [hV₀def]
    exact hf₁.isOpen_inter_preimage ψ.open_source Metric.isOpen_ball
  have hU₁open : IsOpen U₁ := by
    rw [hU₁def]
    exact hf₂.isOpen_inter_preimage ψ.open_source Metric.isOpen_ball
  have hU₂open : IsOpen U₂ := by
    rw [hU₂def]
    exact hf₃.isOpen_inter_preimage ψ.open_source isOpen_Ioi
  have hU₀open : IsOpen U₀ := by
    rw [hU₀def]
    exact ((hV₀open.inter hU₁open).inter hU₂open).inter κ.open_source
  have hU₀parts : ∀ z, z ∈ U₀ → z ∈ V₀ ∧ z ∈ U₁ ∧ z ∈ U₂ ∧ z ∈ κ.source := by
    intro z hz
    rw [hU₀def] at hz
    exact ⟨hz.1.1.1, hz.1.1.2, hz.1.2, hz.2⟩
  have hU₀src : ∀ z, z ∈ U₀ → z ∈ ψ.source := by
    intro z hz
    have h1 : z ∈ V₀ := (hU₀parts z hz).1
    rw [hV₀def] at h1
    exact h1.1
  have hU₀norm : ∀ z, z ∈ U₀ → ‖psiVa ψ y τ z‖ < 1 := by
    intro z hz
    have h1 : z ∈ U₁ := (hU₀parts z hz).2.1
    rw [hU₁def] at h1
    have h2 : psiVa ψ y τ z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 := h1.2
    rw [Metric.mem_ball, dist_zero_right] at h2
    exact h2
  have hU₀pos : ∀ z, z ∈ U₀ → 0 < ((ψ z).1) 0 := by
    intro z hz
    have h1 : z ∈ U₂ := (hU₀parts z hz).2.2.1
    rw [hU₂def] at h1
    exact h1.2
  have hU₀κ : ∀ z, z ∈ U₀ → z ∈ κ.source := fun z hz => (hU₀parts z hz).2.2.2
  have hV₀Sp : ∀ z, z ∈ V₀ → z ∈ Sp := by
    intro z hz
    rw [hV₀def] at hz
    rw [hSpdef]
    exact ⟨ψ z, le_of_lt (Metric.mem_ball.mp hz.2), ψ.left_inv hz.1⟩
  have hx₀U₀ : x₀ ∈ U₀ := by
    rw [hU₀def]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, hx₀κ⟩
    · rw [hV₀def]
      refine ⟨hx₀ψ, ?_⟩
      change dist (psiCh ψ x₀) (psiCh ψ y) < ρ
      rw [dist_eq_norm, hpsiChx₀, hpsiChy]
      exact hNρ
    · rw [hU₁def]
      refine ⟨hx₀ψ, ?_⟩
      change dist (psiVa ψ y τ x₀) 0 < 1
      rw [dist_zero_right]
      exact hVlt1
    · rw [hU₂def]
      refine ⟨hx₀ψ, ?_⟩
      change 0 < psiCh ψ x₀ 0
      rw [hpsiChx₀]
      exact hc₁0
  have hΦeq_U₀ : ∀ z, z ∈ U₀ → psiPhi ψ y τ χ z = psiVa ψ y τ z := by
    intro z hz
    have hχz : χ z = 1 := hχSp z (hV₀Sp z (hU₀parts z hz).1)
    have hnz : ‖psiVa ψ y τ z‖ < 1 := hU₀norm z hz
    rw [psiPhi_apply, hχz, (bcu_profile2_properties n).2.2.1]
    exact BCU.bcu_clampBall_eq_self _ (le_of_lt hnz)
  set e : OpenPartialHomeomorph W (EuclideanSpace ℝ (Fin (n + 1))) :=
    (κ.transHomeomorph (affHomeo (n + 1) ((ψ y).1) τ hτne)).restr U₀ with hedef
  have he_src : e.source = κ.source ∩ U₀ := by
    rw [hedef, OpenPartialHomeomorph.restr_source, OpenPartialHomeomorph.transHomeomorph_source,
      hU₀open.interior_eq]
  have hx₀e : x₀ ∈ e.source := by rw [he_src]; exact ⟨hx₀κ, hx₀U₀⟩
  have he_val : ∀ z ∈ e.source, e z = (affHomeo (n + 1) ((ψ y).1) τ hτne) (κ z) := by
    intro z hz
    rw [hedef, OpenPartialHomeomorph.restr_apply, OpenPartialHomeomorph.transHomeomorph_apply,
      Function.comp_apply]
  have hA : Function.Bijective (τ⁻¹ • (1 : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n + 1)))) := by
    constructor
    · intro u v huv
      have huv' : τ⁻¹ • u = τ⁻¹ • v := by
        simpa only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply] using huv
      exact smul_right_injective _ (inv_ne_zero hτne) huv'
    · intro v
      exact ⟨τ • v, by simp [smul_smul, mul_inv_cancel₀ hτne, inv_mul_cancel₀ hτne]⟩
  have hdet : 0 < LinearMap.det ((τ⁻¹ • (1 : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n + 1)))).toLinearMap) := by
    rw [ContinuousLinearMap.toLinearMap_smul, ContinuousLinearMap.toLinearMap_one,
      LinearMap.det_smul]
    have hone : LinearMap.det (1 : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ]
        EuclideanSpace ℝ (Fin (n + 1))) = 1 := by
      rw [show (1 : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
        = LinearMap.id from rfl, LinearMap.det_id]
    rw [hone, mul_one, finrank_euclideanSpace, Fintype.card_fin]
    exact pow_pos (inv_pos.mpr hτpos) _
  have htrans_e : ∀ z ∈ e.target, κ (e.symm z) = (τ⁻¹ • (1 : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n + 1)))) z + (ψ y).1 := by
    intro z hz
    have h1 : e (e.symm z) = z := e.right_inv hz
    have h2 : e (e.symm z) = (affHomeo (n + 1) ((ψ y).1) τ hτne) (κ (e.symm z)) :=
      he_val _ (e.map_target hz)
    have h3 : (affHomeo (n + 1) ((ψ y).1) τ hτne) (κ (e.symm z)) = z := by rw [← h2, h1]
    have h4 : κ (e.symm z) = (affHomeo (n + 1) ((ψ y).1) τ hτne).symm z :=
      (affHomeo (n + 1) ((ψ y).1) τ hτne).injective
        (by rw [Homeomorph.apply_symm_apply]; exact h3)
    rw [h4, affHomeo_symm_apply]
    rfl
  have hchartTr_e : Work.PTGeometric.HOF.chartTr e x₀ hx₀e
      (Work.PTGeometric.HOF.eucFam (n + 1) (by omega) (e x₀))
      = Work.PTGeometric.HOF.chartTr κ x₀ hx₀κ
        (Work.PTGeometric.HOF.eucFam (n + 1) (by omega) (κ x₀)) :=
    Work.ThomBordism.PosAtlas.chartTr_eq_of_affine_transition (n := n + 1) (by omega) e κ
      (τ⁻¹ • (1 : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1))))
      hA ((ψ y).1) htrans_e hdet x₀ hx₀e hx₀κ
  have hΦs : ∀ z, z ∈ e.source → (⟨psiPhi ψ y τ χ z, hΦmem z⟩ : W') ∈
      (stdIntChart (n + 1)).source := by
    intro z hz
    have hzU : z ∈ U₀ := (by rw [he_src] at hz; exact hz.2)
    have hΦz : psiPhi ψ y τ χ z = psiVa ψ y τ z := hΦeq_U₀ z hzU
    refine ⟨?_, ?_⟩
    · show (0 : ℝ) < ((⟨psiPhi ψ y τ χ z, hΦmem z⟩ : W') :
        EuclideanSpace ℝ (Fin (n + 1))) 0
      rw [show ((⟨psiPhi ψ y τ χ z, hΦmem z⟩ : W') :
        EuclideanSpace ℝ (Fin (n + 1))) = psiPhi ψ y τ χ z from rfl, hΦz, psiVa_coord,
        psiCh_coord_eq_zero_of_bdry ψ hbd hyψ hy, sub_zero]
      exact mul_pos hτpos (hU₀pos z hzU)
    · show ‖((⟨psiPhi ψ y τ χ z, hΦmem z⟩ : W') : EuclideanSpace ℝ (Fin (n + 1)))‖ < 1
      rw [show ((⟨psiPhi ψ y τ χ z, hΦmem z⟩ : W') :
        EuclideanSpace ℝ (Fin (n + 1))) = psiPhi ψ y τ χ z from rfl, hΦz]
      exact hU₀norm z hzU
  have hΦe : ∀ z, z ∈ e.source → (stdIntChart (n + 1))
      (⟨psiPhi ψ y τ χ z, hΦmem z⟩ : W') = e z := by
    intro z hz
    have hzU : z ∈ U₀ := (by rw [he_src] at hz; exact hz.2)
    have hzκ : z ∈ κ.source := (by rw [he_src] at hz; exact hz.1)
    rw [show (stdIntChart (n + 1)) (⟨psiPhi ψ y τ χ z, hΦmem z⟩ : W') =
      psiPhi ψ y τ χ z from rfl, hΦeq_U₀ z hzU, he_val z hz, (hκ z hzκ).2]
    rfl
  have hInt0 : Work.PTGeometric.HOF.RelHmapOf (n + 1) Φ ({x₀} : Set W) ({Φ x₀} : Set W')
      (fun z hz hzx => hz (hΦinj z (by simpa using hzx)))
      (Work.PTGeometric.HOF.chartTr e x₀ hx₀e
        (Work.PTGeometric.HOF.eucFam (n + 1) (by omega) (e x₀)))
      = Work.PTGeometric.HOF.chartTr (W := W') (stdIntChart (n + 1)) (Φ x₀) hx₀srcE
        (Work.PTGeometric.HOF.eucFam (n + 1) (by omega) ((stdIntChart (n + 1)) (Φ x₀))) :=
    chartTr_relHmapOf (N := n + 1) (W := W) (W' := W') (by omega) e (stdIntChart (n + 1))
      Φ.hom x₀ hx₀e hΦs hΦe (fun z hz h => hz (hΦinj z (by simpa using h)))
  have hInt : Work.PTGeometric.HOF.RelHmapOf (n + 1) Φ ({x₀} : Set W) ({Φ x₀} : Set W')
      (fun z hz hzx => hz (hΦinj z (by simpa using hzx)))
      (Work.PTGeometric.HOF.chartTr κ x₀ hx₀κ
        (Work.PTGeometric.HOF.eucFam (n + 1) (by omega) (κ x₀)))
      = Work.PTGeometric.HOF.chartTr (W := W') (stdIntChart (n + 1)) (Φ x₀) hx₀srcE
        (Work.PTGeometric.HOF.eucFam (n + 1) (by omega) ((stdIntChart (n + 1)) (Φ x₀))) := by
    rw [← hchartTr_e]
    exact hInt0

  -- ===================== the boundary chart =====================
  set Wb : Set ↥B := Subtype.val ⁻¹' (V₀ ∩ U₁) ∩ g.source with hWbdef
  have hVUopen : IsOpen (V₀ ∩ U₁) := hV₀open.inter hU₁open
  have hWbopen : IsOpen Wb := by
    rw [hWbdef]
    exact (hVUopen.preimage continuous_subtype_val).inter g.open_source
  have hyVU : y ∈ V₀ ∩ U₁ := by
    refine ⟨?_, ?_⟩
    · rw [hV₀def]
      refine ⟨hyψ, ?_⟩
      change dist (psiCh ψ y) (psiCh ψ y) < ρ
      rw [dist_self]
      exact hρpos
    · rw [hU₁def]
      refine ⟨hyψ, ?_⟩
      change dist (psiVa ψ y τ y) 0 < 1
      rw [dist_zero_right, psiVa_self ψ y τ, norm_zero]
      norm_num
  have hyWb : (⟨y, hyB⟩ : ↥B) ∈ Wb := by
    rw [hWbdef]
    exact ⟨hyVU, hyg⟩
  set gS : OpenPartialHomeomorph ↥B (EuclideanSpace ℝ (Fin n)) :=
    (g.transHomeomorph (affHomeo n (g ⟨y, hyB⟩) τ hτne)).restr Wb with hgSdef
  have hgS_src : gS.source = g.source ∩ Wb := by
    rw [hgSdef, OpenPartialHomeomorph.restr_source, OpenPartialHomeomorph.transHomeomorph_source,
      hWbopen.interior_eq]
  have hygS : (⟨y, hyB⟩ : ↥B) ∈ gS.source := by rw [hgS_src]; exact ⟨hyg, hyWb⟩
  have hgS_val : ∀ z : ↥B, gS z = τ • (g z - g ⟨y, hyB⟩) := by
    intro z
    rw [hgSdef, OpenPartialHomeomorph.restr_apply, OpenPartialHomeomorph.transHomeomorph_apply,
      Function.comp_apply, affHomeo_apply]
  have hVUsrc : ∀ z, z ∈ V₀ ∩ U₁ → z ∈ ψ.source ∧ ‖psiVa ψ y τ z‖ < 1 ∧ χ z = 1 := by
    intro z hz
    have hχ : χ z = 1 := hχSp z (hV₀Sp z hz.1)
    have hzU : z ∈ U₁ := hz.2
    rw [hU₁def] at hzU
    have hn : ‖psiVa ψ y τ z‖ < 1 := by
      have h2 : psiVa ψ y τ z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 := hzU.2
      rwa [Metric.mem_ball, dist_zero_right] at h2
    exact ⟨hzU.1, hn, hχ⟩
  have hΦs' : ∀ z, z ∈ gS.source → Φb z ∈ (stdFlatChart n).source := by
    intro z hz
    rw [hgS_src] at hz
    obtain ⟨hzsrc, hnz, hχz⟩ := hVUsrc z.1 hz.2.1
    have hΦz : psiPhi ψ y τ χ z.1 = psiVa ψ y τ z.1 := by
      rw [psiPhi_apply, hχz, (bcu_profile2_properties n).2.2.1]
      exact BCU.bcu_clampBall_eq_self _ (le_of_lt hnz)
    have hcoe : ((Φb z : ↥B').1.1 : EuclideanSpace ℝ (Fin (n + 1))) = psiPhi ψ y τ χ z.1 :=
      congrArg (fun u : W' => ((u : W') : EuclideanSpace ℝ (Fin (n + 1)))) (hΦb_apply z)
    refine ⟨?_, ?_⟩
    · show (((Φb z : ↥B').1.1 : EuclideanSpace ℝ (Fin (n + 1)))) 0 = 0
      rw [hcoe, hΦz]
      exact psiVa_coord_eq_zero_of_boundary ψ hbd hyψ hy hzsrc z.2
    · show ‖((Φb z : ↥B').1.1 : EuclideanSpace ℝ (Fin (n + 1)))‖ < 1
      rw [hcoe, hΦz]
      exact hnz
  have hΦ' : ∀ z, z ∈ gS.source → (stdFlatChart n) (Φb z) = gS z := by
    intro z hz
    rw [hgS_src] at hz
    obtain ⟨hzsrc, hnz, hχz⟩ := hVUsrc z.1 hz.2.1
    have hΦz : psiPhi ψ y τ χ z.1 = psiVa ψ y τ z.1 := by
      rw [psiPhi_apply, hχz, (bcu_profile2_properties n).2.2.1]
      exact BCU.bcu_clampBall_eq_self _ (le_of_lt hnz)
    have hcoe : ((Φb z : ↥B').1.1 : EuclideanSpace ℝ (Fin (n + 1))) = psiPhi ψ y τ χ z.1 :=
      congrArg (fun u : W' => ((u : W') : EuclideanSpace ℝ (Fin (n + 1)))) (hΦb_apply z)
    have hgz : g z = Work.PTGeometric.tailCLM n ((ψ z.1).1) := (hg z hz.1).2
    have hgy : g ⟨y, hyB⟩ = Work.PTGeometric.tailCLM n ((ψ y).1) :=
      (hg ⟨y, hyB⟩ hyg).2
    calc (stdFlatChart n) (Φb z)
        = Work.PTGeometric.tailCLM n
            ((Φb z : ↥B').1.1 : EuclideanSpace ℝ (Fin (n + 1))) := rfl
      _ = Work.PTGeometric.tailCLM n (psiVa ψ y τ z.1) := by rw [hcoe, hΦz]
      _ = τ • (g z - g ⟨y, hyB⟩) := by
            rw [psiVa_apply, map_smul, map_sub, ← hgz, ← hgy]
      _ = gS z := (hgS_val z).symm
  have hA' : Function.Bijective (τ⁻¹ • (1 : EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n))) := by
    constructor
    · intro u v huv
      have huv' : τ⁻¹ • u = τ⁻¹ • v := by
        simpa only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply] using huv
      exact smul_right_injective _ (inv_ne_zero hτne) huv'
    · intro v
      exact ⟨τ • v, by simp [smul_smul, mul_inv_cancel₀ hτne, inv_mul_cancel₀ hτne]⟩
  have hdet' : 0 < LinearMap.det ((τ⁻¹ • (1 : EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n))).toLinearMap) := by
    rw [ContinuousLinearMap.toLinearMap_smul, ContinuousLinearMap.toLinearMap_one,
      LinearMap.det_smul]
    have hone : LinearMap.det (1 : EuclideanSpace ℝ (Fin n) →ₗ[ℝ]
        EuclideanSpace ℝ (Fin n)) = 1 := by
      rw [show (1 : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
        = LinearMap.id from rfl, LinearMap.det_id]
    rw [hone, mul_one, finrank_euclideanSpace, Fintype.card_fin]
    exact pow_pos (inv_pos.mpr hτpos) _
  have htrans_g : ∀ z ∈ gS.target, g (gS.symm z) = (τ⁻¹ • (1 : EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n))) z + g ⟨y, hyB⟩ := by
    intro z hz
    have h1 : gS (gS.symm z) = z := gS.right_inv hz
    have h2 : gS (gS.symm z) = (affHomeo n (g ⟨y, hyB⟩) τ hτne) (g (gS.symm z)) := by
      rw [hgS_val, affHomeo_apply]
    have h3 : (affHomeo n (g ⟨y, hyB⟩) τ hτne) (g (gS.symm z)) = z := by rw [← h2, h1]
    have h4 : g (gS.symm z) = (affHomeo n (g ⟨y, hyB⟩) τ hτne).symm z :=
      (affHomeo n (g ⟨y, hyB⟩) τ hτne).injective (by rw [Homeomorph.apply_symm_apply]; exact h3)
    rw [h4, affHomeo_symm_apply]
    rfl
  have hb1 : Work.PTGeometric.HOF.chartTr (W := TopCat.of ↥B) gS ⟨y, hyB⟩ hygS
      (Work.PTGeometric.HOF.eucFam n hn (gS ⟨y, hyB⟩))
      = Work.PTGeometric.HOF.chartTr (W := TopCat.of ↥B) g ⟨y, hyB⟩ hyg
        (Work.PTGeometric.HOF.eucFam n hn (g ⟨y, hyB⟩)) :=
    Work.ThomBordism.PosAtlas.chartTr_eq_of_affine_transition (n := n) (W := TopCat.of ↥B) hn
      gS g (τ⁻¹ • (1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) hA' (g ⟨y, hyB⟩)
      htrans_g hdet' ⟨y, hyB⟩ hygS hyg
  have hyeb' : Φb ⟨y, hyB⟩ ∈ (stdFlatChart n).source := hΦs' ⟨y, hyB⟩ hygS
  have hChartB : Work.PTGeometric.HOF.RelHmapOf n Φb ({⟨y, hyB⟩} : Set ↥B)
      ({Φb ⟨y, hyB⟩} : Set ↥B') hpairb
      (Work.PTGeometric.HOF.chartTr (W := TopCat.of ↥B) g ⟨y, hyB⟩ hyg
        (Work.PTGeometric.HOF.eucFam n hn (g ⟨y, hyB⟩)))
      = Work.PTGeometric.HOF.chartTr (W := TopCat.of ↥B') (stdFlatChart n) (Φb ⟨y, hyB⟩) hyeb'
          (Work.PTGeometric.HOF.eucFam n hn ((stdFlatChart n) (Φb ⟨y, hyB⟩))) := by
    rw [← hb1]
    exact chartTr_relHmapOf (N := n) (W := TopCat.of ↥B) (W' := TopCat.of ↥B') hn gS
      (stdFlatChart n) Φb.hom ⟨y, hyB⟩ hygS hΦs' hΦ' hΦbinj
  -- ===================== the model equation =====================
  have hw_compat : Work.Cohomology.subtypeIncl W B ≫ Φ
      = Φb ≫ Work.Cohomology.subtypeIncl W' B' := by
    apply TopCat.ext
    intro z
    exact (hΦb_apply z).symm
  let wtilde : (Work.Cohomology.relChains W' B').homology (n + 1) :=
    (HomologicalComplex.homologyMap
      (Work.Cohomology.relChainsMapOf W W' B B' Φ Φb hw_compat) (n + 1)).hom w
  have hγ : Work.PTGeometric.HOF.RelHmapOf (n + 1) Φ ({x₀} : Set W) ({Φ x₀} : Set W')
      (fun z hz hzx => hz (hΦinj z (by simpa using hzx)))
      ((HomologicalComplex.homologyMap (Work.Orient.relPunct W B x₀ hx₀int) (n + 1)).hom w)
      = (HomologicalComplex.homologyMap
          (Work.Orient.relPunct W' B' (Φ x₀) hx₀int') (n + 1)).hom wtilde := by
    have hsq := relChainsMapOf_relPunct_aux B B' Φ Φb hw_compat hx₀int hx₀int'
      (fun z hz hzx => hz (hΦinj z (by simpa using hzx)))
    have h2 : (HomologicalComplex.homologyMap
          (Work.Orient.relPunct W' B' (Φ x₀) hx₀int') (n + 1)).hom wtilde
        = (HomologicalComplex.homologyMap
            ((Work.Cohomology.relChainsMapOf W W' B B' Φ Φb hw_compat)
              ≫ (Work.Orient.relPunct W' B' (Φ x₀) hx₀int')) (n + 1)).hom w := by
      rw [← ModuleCat.comp_apply, ← HomologicalComplex.homologyMap_comp]
    rw [h2, hsq, HomologicalComplex.homologyMap_comp, ModuleCat.comp_apply]
    exact LinearMap.congr_fun (Work.PTGeometric.HOF.RelHmapOf_eq (n := n + 1) Φ ({x₀} : Set W)
      ({Φ x₀} : Set W') (fun z hz hzx => hz (hΦinj z (by simpa using hzx))))
      ((HomologicalComplex.homologyMap (Work.Orient.relPunct W B x₀ hx₀int) (n + 1)).hom w)
  have hpin : (HomologicalComplex.homologyMap
        (Work.Orient.relPunct W' B' (Φ x₀) hx₀int') (n + 1)).hom wtilde
      = Work.PTGeometric.HOF.chartTr (W := W') (stdIntChart (n + 1)) (Φ x₀) hx₀srcE
          (Work.PTGeometric.HOF.eucFam (n + 1) (by omega) ((stdIntChart (n + 1)) (Φ x₀))) := by
    rw [← hγ, hw]
    exact hInt
  have hEq' : Work.Orient.locClass (TopCat.of ↥B') n
      ((Work.Cohomology.hPairδ W' B' n).hom wtilde) (Φb ⟨y, hyB⟩)
      = c • Work.PTGeometric.HOF.chartTr (W := TopCat.of ↥B') (stdFlatChart n) (Φb ⟨y, hyB⟩)
          hyeb' (Work.PTGeometric.HOF.eucFam n hn ((stdFlatChart n) (Φb ⟨y, hyB⟩))) :=
    hmodel csM (inferInstance : IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1
        ↥(stdHalfBall (n + 1))) hbM ((Φb ⟨y, hyB⟩ : ↥B') : W') ((Φb ⟨y, hyB⟩ : ↥B').2) hyeb'
      (Φ x₀) hx₀srcE hx₀int' hr'pos hgood'' hx₀'' wtilde hpin
  have hinjb : Function.Injective (Work.PTGeometric.HOF.RelHmapOf n Φb ({⟨y, hyB⟩} : Set ↥B)
      ({Φb ⟨y, hyB⟩} : Set ↥B') hpairb) :=
    Work.ThomBordism.relHmapOf_injective_of_chartTr_generator (n := n) hn Φb g hyg
      (stdFlatChart n) hyeb' hpairb hChartB
  exact bdryTransferNC (n := n) (hn := hn) (c := c) (W := W) (B := B) (y := y) (hy := hyB)
    (eb := g) (hyeb := hyg) (hx₀int := hx₀int) (w := w) (W' := W') (B' := B') (hB' := hB'eq)
    (Φ := Φ) (Φb := Φb) (hΦb := hΦb_apply) (hpairb := hpairb) (hΦinj := hΦinj)
    (eb' := stdFlatChart n) (hyeb' := hyeb') (r' := r') (hr' := hr'pos) (hgood' := hgood'')
    (hx₀' := hx₀'') (hx₀int' := hx₀int') (w' := wtilde) (hγ := hγ) (hChartB := hChartB)
    (hEq' := hEq') (hinjb := hinjb)

end Work.ThomBordism.LeadChapter
