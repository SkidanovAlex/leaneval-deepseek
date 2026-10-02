import Mathlib
import Submission.Work.ThomBordism.CofAtlas.sign_lvlTransition
import Submission.Work.ThomBordism.LeadChapter.Defs
import Submission.Work.ThomBordism.orientationFamily_valued_of_coframing
import Submission.Work.ThomBordism.CofAtlas.fderiv_transAux_int
import Submission.Work.ThomBordism.CofAtlas.Omega_eq_fderiv
import Submission.Work.ThomBordism.CofAtlas.range_mfderiv_v_eq_range_e
import Submission.Work.ThomBordism.CofAtlas.range_chartIota_eq_ker_Omega
import Submission.Work.ThomBordism.CofAtlas.Delta_comp_DeltaInv
import Submission.Work.ThomBordism.CofAtlas.det_section_prod
import Submission.Work.ThomBordism.blockDetDefs
import Submission.Work.ThomBordism.blockDet
import Submission.Work.ThomBordism.sgnBlockFactor
import Submission.Work.ThomBordism.PosAtlas.chartTrChangeSigned_gen
import Submission.Work.PTGeometric.HOFChart
import Submission.Work.PTGeometric.Lvl.Chart

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-! Guidance from the project lead (the requester):

# S1 `Work.ThomBordism.chapter_K1det` — (K1) in determinant form, any chart
File: `Submission/Work/ThomBordism/LeadChapter/S1_K1det.lean` (defs: `LeadChapter/Defs.lean`).

**Statement.** ∃ ε = ±1 (after `k n`, before everything else) such that for every coframed level set
`D : CofAtlas.Cof k n M`, interior point `x` of `W`, chart `κ` of `W` at `x`, `A` = derivative at `κ x`
of `u ↦ extChartAt (x:M) (κ.symm u)`, `Lv` = derivative of `D.v ∘ (extChartAt (x:M)).symm` at
`extChartAt x x`, coframing index `j` with `x ∈ U j`, and `N` with `blockDet k A N ≠ 0`:
`flipSign x • chartTr (icChart x) = (ε · sgnZ(blockDet A N) · sgnZ(det(ℓ j ∘ Lv ∘ N))) • chartTr κ`.

**Proof sketch** (expected ε = 1).
1. `Lv ∘ A = 0`: `D.v ∘ κ.symm ≡ 0` on `κ.target`; chain rule through `extChartAt x`.
2. The Lvl chart `icChart 8 _ x` is, near `x`, `chartBeta x (domExt x · - chartZ x) + chartEps • e₀`;
   its derivative in ambient coordinates at `x` is `β ∘ Δ` (`Δ = CofAtlas.Cof.Delta x x`).
   So `icChart ∘ κ.symm` has derivative `β Δ A` at `κ x`; with `hdet` it is bijective.
3. `PosAtlas.chartTrChangeSigned_gen` (e := κ, f := icChart x): `chartTr κ = sgn det(βΔA) • chartTr icChart`.
4. Block determinant: `σ ∘ phiD ∘ Δ ∘ [A|N] ∘ σ⁻¹` is conjugate to `phiD Δ [A|N] = [[βΔA, *],[0, ℓ_jx Lv N]]`
   because `Omega x x ∘ Δ = ℓ_jx ∘ Lv` (`Cx x x = Δ⁻¹`). Hence
   `sgn·tau·sgn(blockDet) = sgn det(βΔA) · sgn det(ℓ_jx Lv N)`, i.e. `flipSign = …`.
5. `j ↔ jx x`: `hpos` (`0 < det(ℓ j ∘ e (jx x) x)`) and `range (Lv ∘ N) ⊆ range P x = range e` give equal signs.

**Proved lemmas.** `Work.ThomBordism.PosAtlas.chartTrChangeSigned_gen` (`…/PosAtlas/chartTrChangeSigned_gen`),
`CofAtlas.Cof.{Delta,Cx,Omega,phiD,sgn,tau,flipSign}` (`…/CofAtlas/Signs`),
`Work.CofAtlas.phiDSplitBlocks` (`Submission.Work.CofAtlas.phiDSplitBlocks`),
`Work.CofAtlas.sgnPackaging` (`Submission.Work.CofAtlas.sgnPackaging`),
`range_chartIota_eq_ker_Omega` (`…/CofAtlas/range_chartIota_eq_ker_Omega`),
`hasFDerivAt_icN_icL`, `icN_coe`, `icL_coe` (`…/orientationFamily_valued_of_coframing`),
`chartBeta_iota`, `chartFun_invFun` (`Submission.Work.PTGeometric.Lvl.Chart`),
`icChart_coe`, `icChart_coe_symm` (`Submission.Work.PTGeometric.exists_halfOrientationFamily_of_det_pos`),
`packingK1` (`…/packingK1`, for the sign bookkeeping pattern `sgz`, `signDetCxEqTau`).

**Traps.**
- No `set_option backward.isDefEq.respectTransparency false` (whnf loops).
- Keep explicit `(W := TopCat.of D.S.Pre) (N := 9)` on every `chartTr`; build intermediate chart
  transfers with `set`/`let` inside the proof.
- Do not move ε inside the `∀`; do not specialise κ to the Lvl chart (the statement is for ANY κ).
- `x` is interior: `x ∉ ∂W` ⇒ `(x:M) ∈ interior M`; at interior points `fderivWithin (range I) = fderiv`.
-/

namespace Work.ThomBordism.LeadChapter

open scoped Manifold ContDiff Topology
open CategoryTheory Work.PTGeometric Filter

variable {k n : ℕ} {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (CofAtlas.NN k)) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace (CofAtlas.NN k)) ((⊤ : ENat) : WithTop ENat) M]

/-- **(K1), step 1**: the derivative `Lv` of the level function and the derivative `A` of the
chart `κ` into the ambient chart satisfy `Lv ∘ A = 0` (the chart lands in the level set). -/
theorem Lv_comp_A_eq_zero (D : CofAtlas.Cof k n M) (x : D.S.Pre)
    (κ : OpenPartialHomeomorph D.S.Pre CofAtlas.E9) (hκ : x ∈ κ.source)
    (A : CofAtlas.E9 →L[ℝ] CofAtlas.ModN k)
    (hA : HasFDerivAt (fun u : CofAtlas.E9 =>
        extChartAt (modelWithCornersEuclideanHalfSpace (CofAtlas.NN k)) (x : M)
          ((κ.symm u : D.S.Pre) : M)) A (κ x))
    (Lv : CofAtlas.ModN k →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hLv : HasFDerivAt (fun u : CofAtlas.ModN k =>
        D.v ((extChartAt (modelWithCornersEuclideanHalfSpace (CofAtlas.NN k))
          (x : M)).symm u)) Lv
        (extChartAt (modelWithCornersEuclideanHalfSpace (CofAtlas.NN k)) (x : M) (x : M))) :
    Lv.comp A = 0 := by
  let I := modelWithCornersEuclideanHalfSpace (CofAtlas.NN k)
  have hκx : (κ.symm (κ x) : D.S.Pre) = x := κ.left_inv hκ
  have hval : extChartAt I (x : M) (x : M)
      = ((fun u : CofAtlas.E9 => extChartAt I (x : M) ((κ.symm u : D.S.Pre) : M)) (κ x)) := by
    simp only [hκx]
  have hLv' : HasFDerivAt (fun u : CofAtlas.ModN k => D.v ((extChartAt I (x : M)).symm u)) Lv
      (((fun u : CofAtlas.E9 => extChartAt I (x : M) ((κ.symm u : D.S.Pre) : M)) (κ x))) :=
    hval ▸ hLv
  have hcomp := (hLv'.comp (κ x) hA)
  have hmem : {u : CofAtlas.E9 | (((κ.symm u : D.S.Pre)) : M)
      ∈ (extChartAt I (x : M)).source} ∈ 𝓝 (κ x) := by
    have hcont : ContinuousAt (fun u : CofAtlas.E9 => (((κ.symm u : D.S.Pre)) : M)) (κ x) :=
      continuous_subtype_val.continuousAt.comp (κ.continuousAt_symm (κ.map_source hκ))
    refine Filter.mem_of_superset
      (hcont.preimage_mem_nhds ((chartAt (EuclideanHalfSpace (CofAtlas.NN k)) (x : M)).open_source.mem_nhds ?_)) ?_
    · rw [hκx]
      exact mem_chart_source (EuclideanHalfSpace (CofAtlas.NN k)) (x : M)
    · intro u hu
      rwa [extChartAt_source]
  have hev : (fun u : CofAtlas.E9 => D.v (((κ.symm u : D.S.Pre)) : M))
      =ᶠ[𝓝 (κ x)]
      (fun u : CofAtlas.E9 => D.v ((extChartAt I (x : M)).symm
        (extChartAt I (x : M) (((κ.symm u : D.S.Pre)) : M)))) := by
    filter_upwards [hmem] with u hu
    rw [PartialEquiv.left_inv _ hu]
  have hcomp2 : HasFDerivAt (fun u : CofAtlas.E9 => D.v (((κ.symm u : D.S.Pre)) : M))
      (Lv.comp A) (κ x) := hcomp.congr_of_eventuallyEq hev
  have hzero : (fun u : CofAtlas.E9 => D.v (((κ.symm u : D.S.Pre)) : M)) = fun _ => 0 := by
    funext u
    have h : (((κ.symm u : D.S.Pre)) : M) ∈ D.W := (κ.symm u : D.S.Pre).2
    rw [D.hW] at h
    exact h
  rw [hzero] at hcomp2
  exact hcomp2.unique (hasFDerivAt_const (0 : EuclideanSpace ℝ (Fin n)) (κ x))

/-- **(K1), step 2**: the `mfderiv` of the level function is the ordinary derivative `Lv` read in the
ambient chart at the (interior) point `x`. -/
theorem mfderiv_v_eq (D : CofAtlas.Cof k n M) (x : D.S.Pre)
    (hint : (x : M) ∈ (modelWithCornersEuclideanHalfSpace (CofAtlas.NN k)).interior M)
    (Lv : CofAtlas.ModN k →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hLv : HasFDerivAt (fun u : CofAtlas.ModN k =>
        D.v ((extChartAt (modelWithCornersEuclideanHalfSpace (CofAtlas.NN k))
          (x : M)).symm u)) Lv
        (extChartAt (modelWithCornersEuclideanHalfSpace (CofAtlas.NN k)) (x : M) (x : M))) :
    mfderiv (modelWithCornersEuclideanHalfSpace (CofAtlas.NN k))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) D.v (x : M) = Lv := by
  have hn : (((⊤ : ENat) : WithTop ENat) : ℕ∞ω) ≠ 0 := by simp
  have hmd : MDifferentiableAt (modelWithCornersEuclideanHalfSpace (CofAtlas.NN k))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) D.v (x : M) :=
    (D.hvsm (x : M)).mdifferentiableAt hn
  rw [hmd.mfderiv]
  have hwr : writtenInExtChartAt (modelWithCornersEuclideanHalfSpace (CofAtlas.NN k))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (x : M) D.v
      = fun u => D.v ((extChartAt (modelWithCornersEuclideanHalfSpace (CofAtlas.NN k))
          (x : M)).symm u) := by
    funext y
    simp only [writtenInExtChartAt]
    rfl
  rw [hwr]
  have hp : (extChartAt (modelWithCornersEuclideanHalfSpace (CofAtlas.NN k)) (x : M)) (x : M)
      ∈ interior (Set.range (modelWithCornersEuclideanHalfSpace (CofAtlas.NN k))) :=
    Work.ThomBordism.CofAtlas.tcD_mem_interior_range
      (modelWithCornersEuclideanHalfSpace (CofAtlas.NN k)) hn
      (IsManifold.chart_mem_maximalAtlas (x : M))
      (mem_chart_source (EuclideanHalfSpace (CofAtlas.NN k)) (x : M)) hint
  rw [fderivWithin_of_mem_nhds
    (Filter.mem_of_superset (isOpen_interior.mem_nhds hp) interior_subset)]
  exact hLv.fderiv

/-- **(K1), step 3**: `DeltaInv` is also a *left* inverse of `Delta` (both are endomorphisms of the
finite-dimensional space `ℝ^{9+k}`, and `Delta ∘ DeltaInv = 1`). -/
theorem DeltaInv_comp_Delta (D : CofAtlas.Cof k n M) (x : D.S.Pre)
    (hint : (x : M) ∈ (modelWithCornersEuclideanHalfSpace (CofAtlas.NN k)).interior M) :
    (D.DeltaInv x (x : M)).comp (D.Delta x (x : M)) = 1 := by
  have hAB := Work.ThomBordism.CofAtlas.Delta_comp_DeltaInv D x (D.mem_chartSource_self x)
    (D.mem_ambSrc_self x) hint
  have hsurj : Function.Surjective ((D.Delta x (x : M)).toLinearMap) := by
    intro w
    exact ⟨D.DeltaInv x (x : M) w, by
      have h := congrArg (fun f : CofAtlas.ModN k →L[ℝ] CofAtlas.ModN k => f w) hAB
      simpa using h⟩
  have hinj : Function.Injective ((D.Delta x (x : M)).toLinearMap) :=
    (LinearMap.injective_iff_surjective (f := (D.Delta x (x : M)).toLinearMap)).mpr hsurj
  apply ContinuousLinearMap.ext
  intro v
  have h2 : (D.Delta x (x : M)).toLinearMap
      ((D.DeltaInv x (x : M)).toLinearMap ((D.Delta x (x : M)).toLinearMap v))
      = (D.Delta x (x : M)).toLinearMap v := by
    have h := congrArg (fun f : CofAtlas.ModN k →L[ℝ] CofAtlas.ModN k =>
      f ((D.Delta x (x : M)) v)) hAB
    simpa using h
  exact hinj h2

/-- **(K1), step 4**: the coframing of the level set in normal-form coordinates, composed with the
chart change `Delta`, is the coframing `ℓ (jx x)` read on the derivative `Lv` of the level function
in ambient coordinates: the second block of `phiD x x ∘ Delta x x`. -/
theorem Omega_comp_Delta_eq (D : CofAtlas.Cof k n M) (x : D.S.Pre)
    (hint : (x : M) ∈ (modelWithCornersEuclideanHalfSpace (CofAtlas.NN k)).interior M)
    (Lv : CofAtlas.ModN k →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hLv : HasFDerivAt (fun u : CofAtlas.ModN k =>
        D.v ((extChartAt (modelWithCornersEuclideanHalfSpace (CofAtlas.NN k))
          (x : M)).symm u)) Lv
        (extChartAt (modelWithCornersEuclideanHalfSpace (CofAtlas.NN k)) (x : M) (x : M))) :
    (D.Omega x (x : M)).comp (D.Delta x (x : M)) = (D.ℓ (D.jx x)).comp Lv := by
  have hmf := mfderiv_v_eq D x hint Lv hLv
  have hinv := DeltaInv_comp_Delta D x hint
  apply ContinuousLinearMap.ext
  intro v
  have h1 : D.DeltaInv x (x : M) (D.Delta x (x : M) v) = v := by
    have h := congrArg (fun f : CofAtlas.ModN k →L[ℝ] CofAtlas.ModN k => f v) hinv
    simpa using h
  show D.Omega x (x : M) (D.Delta x (x : M) v) = (D.ℓ (D.jx x)) (Lv v)
  rw [show D.Omega x (x : M) (D.Delta x (x : M) v)
      = (D.ℓ (D.jx x)) (mfderiv (modelWithCornersEuclideanHalfSpace (CofAtlas.NN k))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) D.v (x : M)
          (D.DeltaInv x (x : M) (D.Delta x (x : M) v))) from rfl]
  rw [h1, hmf]
  rfl


/-- **(K1), step 5**: the block-determinant identity.

For the frame `[A | N]` of `ℝ^{9+k}` (level directions `A`, normal directions `N`) at an interior
centre `x` of the coframed level set, the determinants of the three chart maps (ambient
`sigma ∘ phiD`, the chart change `Delta`, and the frame) multiply to the determinants of the two
blocks `beta ∘ Delta ∘ A` (the "Lvl chart derivative") and `ℓ (jx x) ∘ Lv ∘ N` (the coframing of
the normal directions). -/
theorem blockDet_delta_identity (D : CofAtlas.Cof k n M) (x : D.S.Pre)
    (hint : (x : M) ∈ (modelWithCornersEuclideanHalfSpace (CofAtlas.NN k)).interior M)
    (A : CofAtlas.E9 →L[ℝ] CofAtlas.ModN k)
    (N : EuclideanSpace ℝ (Fin k) →L[ℝ] CofAtlas.ModN k)
    (Lv : CofAtlas.ModN k →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hLv : HasFDerivAt (fun u : CofAtlas.ModN k =>
        D.v ((extChartAt (modelWithCornersEuclideanHalfSpace (CofAtlas.NN k))
          (x : M)).symm u)) Lv
        (extChartAt (modelWithCornersEuclideanHalfSpace (CofAtlas.NN k)) (x : M) (x : M)))
    (hLA : (Lv.comp A) = 0) :
    LinearMap.det ((CofAtlas.sigma k).toLinearMap.comp (D.phiD x (x : M)).toLinearMap)
        * LinearMap.det (D.Delta x (x : M)).toLinearMap
        * blockDet k A N
      = LinearMap.det (((D.S.chartBeta x).toLinearMap).comp
          (((D.Delta x (x : M)).toLinearMap).comp A.toLinearMap))
        * LinearMap.det (((D.ℓ (D.jx x)).comp (Lv.comp N)) :
            EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k)) := by
  have hOD := Omega_comp_Delta_eq D x hint Lv hLv
  set Y : (CofAtlas.E9 × EuclideanSpace ℝ (Fin k)) →ₗ[ℝ]
      (CofAtlas.E9 × EuclideanSpace ℝ (Fin k)) :=
    ((D.phiD x (x : M)).toLinearMap).comp
      (((D.Delta x (x : M)).toLinearMap).comp ((A.coprod N).toLinearMap)) with hYdef
  set f : CofAtlas.E9 →ₗ[ℝ] CofAtlas.E9 :=
    ((D.S.chartBeta x).toLinearMap).comp (((D.Delta x (x : M)).toLinearMap).comp A.toLinearMap)
    with hfdef
  set kk : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] CofAtlas.E9 :=
    ((D.S.chartBeta x).toLinearMap).comp (((D.Delta x (x : M)).toLinearMap).comp N.toLinearMap)
    with hkkdef
  set g : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k) :=
    ((D.ℓ (D.jx x)).toLinearMap).comp ((Lv.toLinearMap).comp N.toLinearMap) with hgdef
  -- (i) the block structure of `phiD ∘ Delta ∘ [A | N]`
  have hYblocks : Y
      = (f.comp (LinearMap.fst ℝ CofAtlas.E9 (EuclideanSpace ℝ (Fin k)))
          + kk.comp (LinearMap.snd ℝ CofAtlas.E9 (EuclideanSpace ℝ (Fin k)))).prod
        (g.comp (LinearMap.snd ℝ CofAtlas.E9 (EuclideanSpace ℝ (Fin k)))) := by
    rw [hYdef]
    apply LinearMap.ext
    intro z
    obtain ⟨u, c⟩ := z
    refine Prod.ext ?_ ?_
    · show (D.S.chartBeta x) (D.Delta x (x : M) ((A.coprod N) (u, c))) = f u + kk c
      rw [ContinuousLinearMap.coprod_apply, map_add, map_add]
      rfl
    · show D.Omega x (x : M) (D.Delta x (x : M) ((A.coprod N) (u, c))) = g c
      rw [ContinuousLinearMap.coprod_apply]
      have hOD' := congrArg (fun (F : CofAtlas.ModN k →L[ℝ] EuclideanSpace ℝ (Fin k)) =>
        F (A u + N c)) hOD
      simp only [ContinuousLinearMap.comp_apply] at hOD'
      rw [hOD']
      have hLA' := congrArg (fun (F : CofAtlas.E9 →L[ℝ] EuclideanSpace ℝ (Fin n)) => F u) hLA
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply] at hLA'
      rw [map_add, hLA', zero_add]
      rfl
  -- (ii) the determinant bookkeeping
  have hassoc : ((CofAtlas.sigma k).toLinearMap.comp (D.phiD x (x : M)).toLinearMap).comp
        ((D.Delta x (x : M)).toLinearMap.comp
          (((A.coprod N).toLinearMap).comp ((CofAtlas.sigma k).symm).toLinearMap))
      = ((CofAtlas.sigma k).toLinearMap).comp (Y.comp ((CofAtlas.sigma k).symm).toLinearMap) := by
    rw [hYdef]
    simp only [LinearMap.comp_assoc]
  have hcomp1 : LinearMap.det ((CofAtlas.sigma k).toLinearMap.comp (D.phiD x (x : M)).toLinearMap)
        * LinearMap.det (D.Delta x (x : M)).toLinearMap
        * LinearMap.det (((A.coprod N).toLinearMap).comp ((CofAtlas.sigma k).symm).toLinearMap)
      = LinearMap.det (((CofAtlas.sigma k).toLinearMap.comp (D.phiD x (x : M)).toLinearMap).comp
          ((D.Delta x (x : M)).toLinearMap.comp
            (((A.coprod N).toLinearMap).comp ((CofAtlas.sigma k).symm).toLinearMap))) := by
    rw [LinearMap.det_comp, LinearMap.det_comp]
    ring
  have hconj : LinearMap.det (((CofAtlas.sigma k).toLinearMap).comp
        (Y.comp ((CofAtlas.sigma k).symm).toLinearMap)) = LinearMap.det Y := by
    rw [← LinearMap.comp_assoc]
    exact LinearMap.det_conj Y (CofAtlas.sigma k)
  have hYdet : LinearMap.det Y = LinearMap.det f * LinearMap.det g := by
    rw [hYblocks, Work.ThomBordism.CofAtlas.det_prod_block]
  rw [show blockDet k A N
      = LinearMap.det (((A.coprod N).toLinearMap).comp
          ((CofAtlas.sigma k).symm).toLinearMap) from rfl]
  rw [hcomp1, hassoc, hconj, hYdet, hfdef, hgdef]
  simp only [ContinuousLinearMap.toLinearMap_comp, LinearMap.comp_assoc]

/-! ## `ℤ`-valued sign bookkeeping -/

theorem sgnZ_ne_one_or_neg_one (r : ℝ) : sgnZ r = 1 ∨ sgnZ r = -1 := by
  unfold sgnZ; split <;> simp

theorem sgnZ_sq (r : ℝ) : sgnZ r * sgnZ r = 1 := by
  rcases sgnZ_ne_one_or_neg_one r with h | h <;> rw [h] <;> norm_num

theorem sgnZ_mul (r s : ℝ) (hr : r ≠ 0) (hs : s ≠ 0) :
    sgnZ (r * s) = sgnZ r * sgnZ s := by
  have hr' : 0 < r ∨ r < 0 := lt_or_gt_of_ne (Ne.symm hr)
  have hs' : 0 < s ∨ s < 0 := lt_or_gt_of_ne (Ne.symm hs)
  unfold sgnZ
  rcases hr' with hr' | hr' <;> rcases hs' with hs' | hs'
  · rw [if_pos hr', if_pos hs', if_pos (mul_pos hr' hs')]; norm_num
  · rw [if_pos hr', if_neg (not_lt.mpr (le_of_lt hs')),
      if_neg (not_lt.mpr (le_of_lt (mul_neg_of_pos_of_neg hr' hs')))]; norm_num
  · rw [if_neg (not_lt.mpr (le_of_lt hr')), if_pos hs',
      if_neg (not_lt.mpr (le_of_lt (mul_neg_of_neg_of_pos hr' hs')))]; norm_num
  · rw [if_neg (not_lt.mpr (le_of_lt hr')), if_neg (not_lt.mpr (le_of_lt hs')),
      if_pos (mul_pos_of_neg_of_neg hr' hs')]; norm_num

theorem sgnZ_eq_sign (r : ℝ) (hr : r ≠ 0) :
    sgnZ r = (if SignType.sign r = 1 then (1 : ℤ) else -1) := by
  have hr' : 0 < r ∨ r < 0 := lt_or_gt_of_ne (Ne.symm hr)
  unfold sgnZ
  rcases hr' with hr' | hr'
  · rw [if_pos hr', if_pos (sign_pos hr')]
  · have hsign : SignType.sign r = -1 := sign_neg hr'
    rw [if_neg (not_lt.mpr (le_of_lt hr')), if_neg (by rw [hsign]; decide)]

theorem ite_mul_sign (s t : SignType) (hs : s ≠ 0) (ht : t ≠ 0) :
    (if s * t = 1 then (1 : ℤ) else -1)
      = (if s = 1 then (1 : ℤ) else -1) * (if t = 1 then (1 : ℤ) else -1) := by
  have hs' : s = 1 ∨ s = -1 := by
    rcases SignType.trichotomy s with h | h | h
    · exact Or.inr h
    · exact absurd h hs
    · exact Or.inl h
  have ht' : t = 1 ∨ t = -1 := by
    rcases SignType.trichotomy t with h | h | h
    · exact Or.inr h
    · exact absurd h ht
    · exact Or.inl h
  rcases hs' with rfl | rfl <;> rcases ht' with rfl | rfl <;> decide

theorem int_pm_one {a : ℤ} (h : a * a = 1) : a = 1 ∨ a = -1 := by
  have h2 : (a - 1) * (a + 1) = 0 := by nlinarith [h]
  rcases mul_eq_zero.mp h2 with h' | h'
  · left; omega
  · right; omega

theorem int_sign_arith {x y z u v : ℤ} (h : x * y * z = u * v)
    (hx : x * x = 1) (hy : y * y = 1) (hz : z * z = 1) (hu : u * u = 1)
    (hv : v * v = 1) :
    (x * y) * u = z * v := by
  rcases int_pm_one hx with rfl | rfl <;> rcases int_pm_one hy with rfl | rfl <;>
    rcases int_pm_one hz with rfl | rfl <;> rcases int_pm_one hu with rfl | rfl <;>
    rcases int_pm_one hv with rfl | rfl <;> omega

/-! ## The range of the derivative of the level function -/

theorem range_Lv_eq (D : CofAtlas.Cof k n M) (x : D.S.Pre)
    (hint : (x : M) ∈ (modelWithCornersEuclideanHalfSpace (CofAtlas.NN k)).interior M)
    (Lv : CofAtlas.ModN k →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hLv : HasFDerivAt (fun u : CofAtlas.ModN k =>
        D.v ((extChartAt (modelWithCornersEuclideanHalfSpace (CofAtlas.NN k))
          (x : M)).symm u)) Lv
        (extChartAt (modelWithCornersEuclideanHalfSpace (CofAtlas.NN k)) (x : M) (x : M))) :
    LinearMap.range Lv.toLinearMap
      = LinearMap.range (D.e (D.jx x) (x : M)).toLinearMap := by
  rw [← mfderiv_v_eq D x hint Lv hLv]
  exact Work.ThomBordism.CofAtlas.range_mfderiv_v_eq_range_e D x (D.mem_src_self x)

/-! ## Invertibility from a non-zero determinant -/

theorem bijective_of_det_ne_zero {n : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (h : LinearMap.det A.toLinearMap ≠ 0) : Function.Bijective A := by
  have hker : A.toLinearMap.ker = ⊥ := by
    by_contra hk
    exact h ((LinearMap.det_eq_zero_iff_ker_ne_bot).mpr hk)
  have hinj : Function.Injective A := LinearMap.ker_eq_bot.mp hker
  exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩


/-- **(K1), step 6**: the integer sign identity.

With the block-determinant identity (`blockDet_delta_identity`) and the vanishing of the three
determinants involved (`sgn_det_ne_zero`, `tau_det_ne_zero`, `hdet`), the `±1` correction
`flipSign x` of the `Lvl` chart times the chart-transfer sign `sgnZ (det (beta ∘ Delta ∘ A))`
equals the product of the two block signs. -/
theorem sign_identity (D : CofAtlas.Cof k n M) (x : D.S.Pre)
    (hint : (x : M) ∈ (modelWithCornersEuclideanHalfSpace (CofAtlas.NN k)).interior M)
    (A : CofAtlas.E9 →L[ℝ] CofAtlas.ModN k)
    (N : EuclideanSpace ℝ (Fin k) →L[ℝ] CofAtlas.ModN k)
    (Lv : CofAtlas.ModN k →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hLv : HasFDerivAt (fun u : CofAtlas.ModN k =>
        D.v ((extChartAt (modelWithCornersEuclideanHalfSpace (CofAtlas.NN k))
          (x : M)).symm u)) Lv
        (extChartAt (modelWithCornersEuclideanHalfSpace (CofAtlas.NN k)) (x : M) (x : M)))
    (hLA : (Lv.comp A) = 0)
    (hdet : blockDet k A N ≠ 0)
    (j : Fin D.m)
    (hcof : sgnZ (LinearMap.det (((D.ℓ j).comp (Lv.comp N)) :
            EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k)))
        = sgnZ (LinearMap.det (((D.ℓ (D.jx x)).comp (Lv.comp N)) :
            EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k)))) :
    (if D.flipSign x = 1 then (1 : ℤ) else -1)
        * sgnZ (LinearMap.det (((D.S.chartBeta x).toLinearMap).comp
            (((D.Delta x (x : M)).toLinearMap).comp A.toLinearMap)))
      = sgnZ (blockDet k A N)
        * sgnZ (LinearMap.det (((D.ℓ j).comp (Lv.comp N)) :
            EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k))) := by
  have hblk := blockDet_delta_identity D x hint A N Lv hLv hLA
  set A1 : ℝ := LinearMap.det ((CofAtlas.sigma k).toLinearMap.comp
    (D.phiD x (x : M)).toLinearMap) with hA1def
  set A2 : ℝ := LinearMap.det (D.Delta x (x : M)).toLinearMap with hA2def
  set B1 : ℝ := LinearMap.det (((D.S.chartBeta x).toLinearMap).comp
    (((D.Delta x (x : M)).toLinearMap).comp A.toLinearMap)) with hB1def
  set B2 : ℝ := LinearMap.det (((D.ℓ (D.jx x)).comp (Lv.comp N)) :
    EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k)) with hB2def
  have hblk' : A1 * A2 * blockDet k A N = B1 * B2 := hblk
  have hA1nz : A1 ≠ 0 := Work.ThomBordism.CofAtlas.sgn_det_ne_zero D x (D.mem_src_self x) hint
  have hA2nz : A2 ≠ 0 := Work.ThomBordism.CofAtlas.tau_det_ne_zero D x (D.mem_src_self x) hint
  have hRHS : B1 * B2 ≠ 0 := by
    rw [← hblk']
    exact mul_ne_zero (mul_ne_zero hA1nz hA2nz) hdet
  have hB1nz : B1 ≠ 0 := (mul_ne_zero_iff.mp hRHS).1
  have hB2nz : B2 ≠ 0 := (mul_ne_zero_iff.mp hRHS).2
  have hsign : sgnZ A1 * sgnZ A2 * sgnZ (blockDet k A N) = sgnZ B1 * sgnZ B2 := by
    rw [← sgnZ_mul A1 A2 hA1nz hA2nz, ← sgnZ_mul (A1 * A2) (blockDet k A N)
      (mul_ne_zero hA1nz hA2nz) hdet, ← sgnZ_mul B1 B2 hB1nz hB2nz, hblk']
  have harith : (sgnZ A1 * sgnZ A2) * sgnZ B1 = sgnZ (blockDet k A N) * sgnZ B2 :=
    int_sign_arith hsign (sgnZ_sq A1) (sgnZ_sq A2) (sgnZ_sq (blockDet k A N))
      (sgnZ_sq B1) (sgnZ_sq B2)
  have hsgn : D.sgn x (x : M) ≠ 0 := by
    change SignType.sign A1 ≠ 0
    exact sign_ne_zero.mpr hA1nz
  have htau : D.tau x (x : M) ≠ 0 := by
    change SignType.sign A2 ≠ 0
    exact sign_ne_zero.mpr hA2nz
  have h1 : (if D.sgn x (x : M) = 1 then (1 : ℤ) else -1) = sgnZ A1 := by
    show (if SignType.sign A1 = 1 then (1 : ℤ) else -1) = sgnZ A1
    rw [sgnZ_eq_sign A1 hA1nz]
  have h2 : (if D.tau x (x : M) = 1 then (1 : ℤ) else -1) = sgnZ A2 := by
    show (if SignType.sign A2 = 1 then (1 : ℤ) else -1) = sgnZ A2
    rw [sgnZ_eq_sign A2 hA2nz]
  have hF : (if D.flipSign x = 1 then (1 : ℤ) else -1) = sgnZ A1 * sgnZ A2 := by
    calc (if D.flipSign x = 1 then (1 : ℤ) else -1)
        = (if D.sgn x (x : M) * D.tau x (x : M) = 1 then (1 : ℤ) else -1) := rfl
      _ = (if D.sgn x (x : M) = 1 then (1 : ℤ) else -1)
            * (if D.tau x (x : M) = 1 then (1 : ℤ) else -1) := ite_mul_sign _ _ hsgn htau
      _ = sgnZ A1 * sgnZ A2 := by rw [h1, h2]
  rw [hF, show B1 = LinearMap.det (((D.S.chartBeta x).toLinearMap).comp
      (((D.Delta x (x : M)).toLinearMap).comp A.toLinearMap)) from rfl, hcof]
  exact harith


end Work.ThomBordism.LeadChapter
