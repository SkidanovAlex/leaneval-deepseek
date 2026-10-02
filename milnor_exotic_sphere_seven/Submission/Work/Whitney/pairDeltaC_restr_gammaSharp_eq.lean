import Mathlib
import Submission.Work.Whitney.TCMDefs
import Submission.Work.Whitney.CupDefs
import Submission.Work.Whitney.Mn_one_eq_pairDelta
import Submission.Work.Whitney.Cutoff
import Submission.Work.Thom.naturalModelClass_punct
import Submission.Work.Thom.pairDeltaNatural
import Submission.Work.Cohomology.twoComponentCokernel
import Submission.Work.Thom.Orientation.ReflSections
import Submission.Work.Whitney.RankTwo.AlphaAux

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false

/-!
# The transgression of the restricted clever lift

For the model pair `X = tcmX Y n 1 = Y × (ℝⁿ × ℝ)` with the closed set `C = tcmC Y n 1` (the
points whose last fibre coordinate does not vanish), the `0`-cochain `Work.Whitney.gammaSharp Y n`
(the indicator of "last coordinate `≥ 0`") restricts to a `0`-cocycle on `C` — it is the indicator
of the clopen set "last coordinate `> 0`" there — and its transgression is the pullback of the
rank-one model class:

  `(pairδC C 0).hom [gammaSharp|_C] = (tcmPr2)^* (Mpun 1 Y)`.

The proof mirrors the identification of the transgression input of `Mpun 1` in
`Submission/Work/Whitney/RankTwo/AlphaAux.lean`:

* the **strict** sign cochain `gsign` (the indicator of "last coordinate `> 0`", equal to
  `RankTwo.bt0` pulled back along `tcmPr2`) differs from `gammaSharp` by the indicator `ζ` of the
  zero locus `{lastCoord = 0}`, which vanishes on `C`; hence `gammaSharp` and `gsign` restrict to
  the same cochain on `C`, and `d(gammaSharp) - d(gsign) = d ζ` restricts to `0` as well;
* `d(gsign) = (tcmPr2)^*(RankTwo.t1)` with `RankTwo.t1 = d(RankTwo.bt0)`, and `RankTwo.t1` kills
  every simplex lying in the punctured part `Punct Y 1` (`RankTwo.t1_mem_relKern_punct`), so
  `d(gammaSharp)` restricts to `0` on `C` — this is the cocycle `hγ`;
* the transgression of `gsign` is computed with `pairδC_class_of_lift` (i.e. `pdmc_pairδ_lift`),
  and compared with `(tcmPr2)^* Mpun 1 Y` through the relative naturality
  `homologyMap_relComplexMap_relClassOf` and the identification `RankTwo.t1_class_punct`.
-/

namespace Work.Whitney

open Work.Thom
open Work.Cohomology
open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Simplicial

noncomputable section

/-! ## Coordinates of `tcmSumLin` -/

/-- In the coordinate identification `tcmSumLin p q : ℝ^p × ℝ^q ≅ ℝ^{p+q}` the second factor is
read in the last `q` coordinates (along `Fin.natAdd`). -/
lemma tcmSumLin_symm_apply_snd' (p q : ℕ) (u : EuclideanSpace ℝ (Fin (p + q))) (i : Fin q) :
    ((tcmSumLin p q).symm u).2 i = u (Fin.natAdd p i) := by
  simp only [tcmSumLin, ContinuousLinearEquiv.symm_symm, EuclideanSpace.finAddEquivProd,
    EuclideanSpace.sumEquivProd, ContinuousLinearEquiv.trans_apply,
    PiLp.sumPiLpEquivProdLpPiLp_apply_ofLp, LinearIsometryEquiv.piLpCongrLeft_apply,
    Equiv.piCongrLeft'_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    WithLp.prodContinuousLinearEquiv_apply]
  rfl

lemma natAdd_zero_eq_last (p : ℕ) : Fin.natAdd p (0 : Fin 1) = Fin.last p := by
  ext; simp [Fin.natAdd, Fin.last]

/-- **The last coordinate of `tcmX Y p 1` is its second fibre coordinate.** -/
lemma lastCoord_eq (Y : Type) [TopologicalSpace Y] (p : ℕ) (x : tcmX Y p 1) :
    lastCoord Y p x = (x.2.2).ofLp 0 := by
  simp only [lastCoord]
  have h := tcmSumLin_symm_apply_snd' p 1 (tcmSumLin p 1 x.2) (0 : Fin 1)
  rw [ContinuousLinearEquiv.symm_apply_apply] at h
  rw [h, natAdd_zero_eq_last]

/-- On `tcmC` the last coordinate does not vanish. -/
lemma lastCoord_ne_zero_of_mem_tcmC (Y : Type) [TopologicalSpace Y] (n : ℕ)
    {x : tcmX Y n 1} (hx : x ∈ tcmC Y n 1) : lastCoord Y n x ≠ 0 := by
  rw [lastCoord_eq]
  exact fun h => hx ((RankTwo.ofLp_zero_iff _).mp h)

/-- The `.ofLp 0`-coordinate of `tcmPr2` applied to a point of `tcmC` is the last coordinate. -/
lemma tcmPr2_ofLp_zero_of_mem (Y : Type) [TopologicalSpace Y] (n : ℕ)
    (x : ↥(tcmC Y n 1)) :
    (((tcmPr2 Y n 1 x.1).2).ofLp 0) = lastCoord Y n x.1 := by
  rw [lastCoord_eq]
  rfl

/-! ## The strict sign cochain `gsign` of the last coordinate -/

/-- The point underlying a `0`-simplex of `tcmX Y n 1`. -/
noncomputable def tcmPt (Y : Type) [TopologicalSpace Y] (n : ℕ)
    (σ : (ssB (tcmX Y n 1)) _⦋0⦌) : tcmX Y n 1 :=
  (TopCat.toSSetObjEquivOld (TopCat.of (tcmX Y n 1))
    (Opposite.op (SimplexCategory.mk 0))) σ default

/-- The point underlying a `0`-simplex of `tcmC Y n 1`. -/
noncomputable def tcmCPt (Y : Type) [TopologicalSpace Y] (n : ℕ)
    (τ : (ssB ↥(tcmC Y n 1)) _⦋0⦌) : ↥(tcmC Y n 1) :=
  (TopCat.toSSetObjEquivOld (TopCat.of ↥(tcmC Y n 1))
    (Opposite.op (SimplexCategory.mk 0))) τ default

/-- **The strict sign of the last coordinate of `tcmX Y n 1`**: `1` where it is `> 0`, `0`
elsewhere.  Unlike `gammaSharp` it vanishes at the zero locus, which is what makes its
transgression the pullback of `RankTwo.t1`. -/
noncomputable def gsign (Y : Type) [TopologicalSpace Y] (n : ℕ) :
    Cochain ℤ (ssB (tcmX Y n 1)) 0 :=
  RankTwo.cochainOf (ssB (tcmX Y n 1)) 0
    (fun σ => RankTwo.posOf (lastCoord Y n (tcmPt Y n σ)))

theorem genEval_gsign (Y : Type) [TopologicalSpace Y] (n : ℕ)
    (σ : (ssB (tcmX Y n 1)) _⦋0⦌) :
    genEval ℤ (ssB (tcmX Y n 1)) (gsign Y n) σ
      = RankTwo.posOf (lastCoord Y n (tcmPt Y n σ)) :=
  RankTwo.genEval_cochainOf _ _ _ _

/-- The point of `tcmX Y n 1` underlying the pushforward of a `0`-simplex of `tcmC`. -/
theorem tcmPt_map_subtypeIncl (Y : Type) [TopologicalSpace Y] (n : ℕ)
    (τ : (ssB ↥(tcmC Y n 1)) _⦋0⦌) :
    tcmPt Y n ((TopCat.toSSet.map (subtypeIncl (TopCat.of (tcmX Y n 1)) (tcmC Y n 1))).app
        (Opposite.op (SimplexCategory.mk 0)) τ)
      = (subtypeIncl (TopCat.of (tcmX Y n 1)) (tcmC Y n 1)) (tcmCPt Y n τ) :=
  RankTwo.toSSetObjEquiv_map_apply' (TopCat.of ↥(tcmC Y n 1)) (TopCat.of (tcmX Y n 1))
    (subtypeIncl (TopCat.of (tcmX Y n 1)) (tcmC Y n 1)) (Opposite.op (SimplexCategory.mk 0))
    τ default

/-- **`gsign` is the pullback of the sign cochain of the line bundle.** -/
theorem pullback_tcmPr2_bt0 (Y : Type) [TopologicalSpace Y] (n : ℕ) :
    ((dualChainMap ℤ (TopCat.of (tcmX Y n 1)) (TopCat.of (RankTwo.Y1 Y))
      (TopCat.ofHom (tcmPr2 Y n 1))).f 0) (RankTwo.bt0 Y) = gsign Y n := by
  apply genEval_ext
  intro σ
  have h1 := RankTwo.genEval_dualChainMap (X := TopCat.of (tcmX Y n 1))
    (Y := TopCat.of (RankTwo.Y1 Y)) (f := TopCat.ofHom (tcmPr2 Y n 1)) (n := 0)
    (α := RankTwo.bt0 Y) (σ := σ)
  have h2 : genEval ℤ (RankTwo.ssY1 Y) (RankTwo.bt0 Y)
      ((TopCat.toSSet.map (TopCat.ofHom (tcmPr2 Y n 1))).app
        (Opposite.op (SimplexCategory.mk 0)) σ)
      = RankTwo.signFib Y (tcmPr2 Y n 1 (tcmPt Y n σ)) := by
    refine (RankTwo.genEval_bt0 Y _).trans ?_
    exact congrArg (RankTwo.signFib Y)
      (RankTwo.toSSetObjEquiv_map_apply' (TopCat.of (tcmX Y n 1)) (TopCat.of (RankTwo.Y1 Y))
        (TopCat.ofHom (tcmPr2 Y n 1)) (Opposite.op (SimplexCategory.mk 0)) σ default)
  have h3 : RankTwo.signFib Y (tcmPr2 Y n 1 (tcmPt Y n σ))
      = RankTwo.posOf (lastCoord Y n (tcmPt Y n σ)) := by
    rw [show RankTwo.signFib Y (tcmPr2 Y n 1 (tcmPt Y n σ))
        = RankTwo.posOf (((tcmPr2 Y n 1 (tcmPt Y n σ)).2).ofLp 0) from rfl]
    rw [show (tcmPr2 Y n 1 (tcmPt Y n σ)).2 = (tcmPt Y n σ).2.2 from rfl, lastCoord_eq]
  exact h1.trans (h2.trans (h3.trans (genEval_gsign Y n σ).symm))

/-- **The differential of `gsign` is the pullback of `RankTwo.t1`.** -/
theorem cochainDiff_gsign (Y : Type) [TopologicalSpace Y] (n : ℕ) :
    cochainDiff ℤ (ssB (tcmX Y n 1)) (gsign Y n)
      = ((dualChainMap ℤ (TopCat.of (tcmX Y n 1)) (TopCat.of (RankTwo.Y1 Y))
          (TopCat.ofHom (tcmPr2 Y n 1))).f 1) (RankTwo.t1 Y) := by
  have h1 : ((dualChainMap ℤ (TopCat.of (tcmX Y n 1)) (TopCat.of (RankTwo.Y1 Y))
      (TopCat.ofHom (tcmPr2 Y n 1))).f 1) (RankTwo.t1 Y)
      = ((dualChainMap ℤ (TopCat.of (tcmX Y n 1)) (TopCat.of (RankTwo.Y1 Y))
        (TopCat.ofHom (tcmPr2 Y n 1))).f 1) (cochainDiff ℤ (RankTwo.ssY1 Y) (RankTwo.bt0 Y)) :=
    rfl
  have h2 : cochainDiff ℤ (ssB (tcmX Y n 1)) (gsign Y n)
      = cochainDiff ℤ (ssB (tcmX Y n 1))
          (((dualChainMap ℤ (TopCat.of (tcmX Y n 1)) (TopCat.of (RankTwo.Y1 Y))
            (TopCat.ofHom (tcmPr2 Y n 1))).f 0) (RankTwo.bt0 Y)) :=
    congrArg (fun z => cochainDiff ℤ (ssB (tcmX Y n 1)) z) (pullback_tcmPr2_bt0 Y n).symm
  exact h2.trans ((RankTwo.cochainDiff_dualChainMap (f := tcmPr2 Y n 1) (n := 0)
    (α := RankTwo.bt0 Y)).symm.trans h1.symm)

/-- The `genEval` of the zero cochain is zero. -/
theorem genEval_zero_cochain (X : SSet) (n : ℕ) (σ : X _⦋n⦌) :
    genEval ℤ X (0 : Cochain ℤ X n) σ = 0 := by
  simp only [genEval, LinearMap.zero_apply]

/-- The pullback of `RankTwo.t1` to `tcmC` vanishes (the projection lands in the punctured
part, on which `RankTwo.t1` is zero). -/
theorem restr_pullback_t1_eq_zero (Y : Type) [TopologicalSpace Y] (n : ℕ) :
    ((restr ℤ (TopCat.of (tcmX Y n 1)) (tcmC Y n 1)).f 1)
      (((dualChainMap ℤ (TopCat.of (tcmX Y n 1)) (TopCat.of (RankTwo.Y1 Y))
        (TopCat.ofHom (tcmPr2 Y n 1))).f 1) (RankTwo.t1 Y)) = 0 := by
  apply genEval_ext
  intro τ
  have hA : genEval ℤ (ssB ↥(tcmC Y n 1))
      (((restr ℤ (TopCat.of (tcmX Y n 1)) (tcmC Y n 1)).f 1)
        (((dualChainMap ℤ (TopCat.of (tcmX Y n 1)) (TopCat.of (RankTwo.Y1 Y))
          (TopCat.ofHom (tcmPr2 Y n 1))).f 1) (RankTwo.t1 Y))) τ
      = genEval ℤ (RankTwo.ssY1 Y) (RankTwo.t1 Y)
          ((TopCat.toSSet.map (TopCat.ofHom (tcmPr2 Y n 1))).app
            (Opposite.op (SimplexCategory.mk 1))
            ((TopCat.toSSet.map (subtypeIncl (TopCat.of (tcmX Y n 1)) (tcmC Y n 1))).app
              (Opposite.op (SimplexCategory.mk 1)) τ)) :=
    (RankTwo.genEval_dualChainMap (X := TopCat.of ↥(tcmC Y n 1))
      (Y := TopCat.of (tcmX Y n 1))
      (f := subtypeIncl (TopCat.of (tcmX Y n 1)) (tcmC Y n 1)) (n := 1)
      (α := ((dualChainMap ℤ (TopCat.of (tcmX Y n 1)) (TopCat.of (RankTwo.Y1 Y))
        (TopCat.ofHom (tcmPr2 Y n 1))).f 1) (RankTwo.t1 Y)) (σ := τ)).trans
    (RankTwo.genEval_dualChainMap (X := TopCat.of (tcmX Y n 1))
      (Y := TopCat.of (RankTwo.Y1 Y)) (f := TopCat.ofHom (tcmPr2 Y n 1)) (n := 1)
      (α := RankTwo.t1 Y)
      (σ := (TopCat.toSSet.map (subtypeIncl (TopCat.of (tcmX Y n 1)) (tcmC Y n 1))).app
        (Opposite.op (SimplexCategory.mk 1)) τ))
  refine hA.trans ?_
  refine (RankTwo.genEval_t1_eq_zero Y _ ?_).trans (genEval_zero_cochain _ 1 τ).symm
  intro q
  have hq1 := RankTwo.toSSetObjEquiv_map_apply' (TopCat.of (tcmX Y n 1))
    (TopCat.of (RankTwo.Y1 Y)) (TopCat.ofHom (tcmPr2 Y n 1))
    (Opposite.op (SimplexCategory.mk 1))
    ((TopCat.toSSet.map (subtypeIncl (TopCat.of (tcmX Y n 1)) (tcmC Y n 1))).app
      (Opposite.op (SimplexCategory.mk 1)) τ) q
  have hq2 := RankTwo.toSSetObjEquiv_map_apply' (TopCat.of ↥(tcmC Y n 1))
    (TopCat.of (tcmX Y n 1)) (subtypeIncl (TopCat.of (tcmX Y n 1)) (tcmC Y n 1))
    (Opposite.op (SimplexCategory.mk 1)) τ q
  rw [hq1, hq2]
  set x : ↥(tcmC Y n 1) :=
    ((TopCat.toSSetObjEquivOld (TopCat.of ↥(tcmC Y n 1))
      (Opposite.op (SimplexCategory.mk 1))) τ) q
  show (((tcmPr2 Y n 1 x.1).2).ofLp 0) ≠ 0
  rw [tcmPr2_ofLp_zero_of_mem Y n x]
  exact lastCoord_ne_zero_of_mem_tcmC Y n x.2

/-! ## `gammaSharp` and `gsign` agree on `tcmC` -/

/-- The `if 0 ≤ a then 1 else 0`-cochain agrees with `posOf` away from `0`. -/
lemma if_nonneg_eq_posOf {a : ℝ} (ha : a ≠ 0) :
    (if 0 ≤ a then (1 : ℤ) else 0) = RankTwo.posOf a := by
  rcases lt_or_gt_of_ne (Ne.symm ha) with h | h
  · rw [if_pos (le_of_lt h), RankTwo.posOf_pos h]
  · rw [if_neg (not_le.mpr h), RankTwo.posOf_nonpos (not_lt.mpr (le_of_lt h))]

/-- **`gammaSharp` and `gsign` restrict to the same cochain on `tcmC`** (on `tcmC` the last
coordinate does not vanish, so `≥ 0` and `> 0` agree). -/
theorem restr_gammaSharp_eq_restr_gsign (Y : Type) [TopologicalSpace Y] (n : ℕ) :
    ((restr ℤ (TopCat.of (tcmX Y n 1)) (tcmC Y n 1)).f 0) (gammaSharp Y n)
      = ((restr ℤ (TopCat.of (tcmX Y n 1)) (tcmC Y n 1)).f 0) (gsign Y n) := by
  apply genEval_ext
  intro τ
  have hA : genEval ℤ (ssB ↥(tcmC Y n 1))
      (((restr ℤ (TopCat.of (tcmX Y n 1)) (tcmC Y n 1)).f 0) (gammaSharp Y n)) τ
      = (if 0 ≤ lastCoord Y n ((subtypeIncl (TopCat.of (tcmX Y n 1))
          (tcmC Y n 1)) (tcmCPt Y n τ)) then 1 else 0) := by
    refine (RankTwo.genEval_dualChainMap (X := TopCat.of ↥(tcmC Y n 1))
      (Y := TopCat.of (tcmX Y n 1))
      (f := subtypeIncl (TopCat.of (tcmX Y n 1)) (tcmC Y n 1)) (n := 0)
      (α := gammaSharp Y n) (σ := τ)).trans ?_
    refine (genEval_gammaSharp Y n _).trans ?_
    exact congrArg (fun z => if 0 ≤ lastCoord Y n z then (1 : ℤ) else 0)
      (tcmPt_map_subtypeIncl Y n τ)
  have hB : genEval ℤ (ssB ↥(tcmC Y n 1))
      (((restr ℤ (TopCat.of (tcmX Y n 1)) (tcmC Y n 1)).f 0) (gsign Y n)) τ
      = RankTwo.posOf (lastCoord Y n ((subtypeIncl (TopCat.of (tcmX Y n 1))
          (tcmC Y n 1)) (tcmCPt Y n τ))) := by
    refine (RankTwo.genEval_dualChainMap (X := TopCat.of ↥(tcmC Y n 1))
      (Y := TopCat.of (tcmX Y n 1))
      (f := subtypeIncl (TopCat.of (tcmX Y n 1)) (tcmC Y n 1)) (n := 0)
      (α := gsign Y n) (σ := τ)).trans ?_
    refine (genEval_gsign Y n _).trans ?_
    exact congrArg (fun z => RankTwo.posOf (lastCoord Y n z)) (tcmPt_map_subtypeIncl Y n τ)
  exact hA.trans ((if_nonneg_eq_posOf (lastCoord_ne_zero_of_mem_tcmC Y n (tcmCPt Y n τ).2)).trans
    hB.symm)

/-! ## The cocycle `hγ` -/

/-- **The restriction of `gammaSharp` to `tcmC` is a `0`-cocycle.** -/
theorem cochainDiff_restr_gammaSharp (Y : Type) [TopologicalSpace Y] (n : ℕ) :
    cochainDiff ℤ (ssB ↥(tcmC Y n 1))
      (((restr ℤ (TopCat.of (tcmX Y n 1)) (tcmC Y n 1)).f 0) (gammaSharp Y n)) = 0 := by
  refine (RankTwo.cochainDiff_restr (X := TopCat.of (tcmX Y n 1)) (tcmC Y n 1) (n := 0)
    (gammaSharp Y n)).trans ?_
  have hζ : ((restr ℤ (TopCat.of (tcmX Y n 1)) (tcmC Y n 1)).f 0)
      (gammaSharp Y n - gsign Y n) = 0 := by
    rw [map_sub]
    exact sub_eq_zero.mpr (restr_gammaSharp_eq_restr_gsign Y n)
  have hd : cochainDiff ℤ (ssB (tcmX Y n 1)) (gammaSharp Y n)
      = cochainDiff ℤ (ssB (tcmX Y n 1)) (gsign Y n)
        + cochainDiff ℤ (ssB (tcmX Y n 1)) (gammaSharp Y n - gsign Y n) := by
    refine (congrArg (fun z => cochainDiff ℤ (ssB (tcmX Y n 1)) z)
      (by abel : gammaSharp Y n = gsign Y n + (gammaSharp Y n - gsign Y n))).trans ?_
    exact (cochainDiffLM ℤ (ssB (tcmX Y n 1)) 0).map_add (gsign Y n)
      (gammaSharp Y n - gsign Y n)
  have hζcob : ((restr ℤ (TopCat.of (tcmX Y n 1)) (tcmC Y n 1)).f 1)
      (cochainDiff ℤ (ssB (tcmX Y n 1)) (gammaSharp Y n - gsign Y n)) = 0 := by
    refine (RankTwo.cochainDiff_restr (X := TopCat.of (tcmX Y n 1)) (tcmC Y n 1) (n := 0)
      (gammaSharp Y n - gsign Y n)).symm.trans ?_
    rw [hζ]
    exact RankTwo.cochainDiff_zero (ssB ↥(tcmC Y n 1)) 0
  rw [hd, map_add, cochainDiff_gsign Y n, restr_pullback_t1_eq_zero Y n, hζcob, add_zero]

/-! ## The main theorem -/

theorem pairDeltaC_restr_gammaSharp_eq (Y : Type) [TopologicalSpace Y] (n : ℕ) :
    ∃ (hγ : Work.Cohomology.cochainDiff ℤ (Work.Whitney.ssB ↥(Work.Whitney.tcmC Y n 1))
        (((Work.Cohomology.restr ℤ (TopCat.of (Work.Whitney.tcmX Y n 1))
          (Work.Whitney.tcmC Y n 1)).f 0) (Work.Whitney.gammaSharp Y n)) = 0),
      (Work.Thom.pairδC (Work.Whitney.tcmC Y n 1) 0).hom
          (Work.Cohomology.cohomologyClassOf ℤ (Work.Whitney.ssB ↥(Work.Whitney.tcmC Y n 1))
            (((Work.Cohomology.restr ℤ (TopCat.of (Work.Whitney.tcmX Y n 1))
              (Work.Whitney.tcmC Y n 1)).f 0) (Work.Whitney.gammaSharp Y n)) hγ)
        = (Work.Thom.relCohMap (Work.Whitney.tcmPr2 Y n 1) (Work.Whitney.tcmC Y n 1)
            (Work.Thom.Punct Y 1) (fun x hx => hx) ℤ 1).hom (Work.Thom.Mpun 1 Y) := by
  have href := restr_gammaSharp_eq_restr_gsign Y n
  have hγ0 := cochainDiff_restr_gammaSharp Y n
  have hgs : cochainDiff ℤ (ssB ↥(tcmC Y n 1))
      (((restr ℤ (TopCat.of (tcmX Y n 1)) (tcmC Y n 1)).f 0) (gsign Y n)) = 0 := href ▸ hγ0
  refine ⟨hγ0, ?_⟩
  obtain ⟨hmemg, hcocg, hδg⟩ :=
    pairδC_class_of_lift (tcmC Y n 1)
      (((restr ℤ (TopCat.of (tcmX Y n 1)) (tcmC Y n 1)).f 0) (gsign Y n)) hgs
      (gsign Y n) rfl
  have hcls : cohomologyClassOf ℤ (ssB ↥(tcmC Y n 1))
      (((restr ℤ (TopCat.of (tcmX Y n 1)) (tcmC Y n 1)).f 0) (gammaSharp Y n)) hγ0
      = cohomologyClassOf ℤ (ssB ↥(tcmC Y n 1))
        (((restr ℤ (TopCat.of (tcmX Y n 1)) (tcmC Y n 1)).f 0) (gsign Y n)) hgs :=
    cohomologyClassOf_congr ℤ (ssB ↥(tcmC Y n 1)) href hγ0 hgs
  have hrel : (relMapLM ℤ (tcmC Y n 1) (Punct Y 1) (TopCat.ofHom (tcmPr2 Y n 1))
        (fun x hx => hx) 1) (RankTwo.t1punt Y)
      = ⟨((singularCochainComplex ℤ (TopCat.of (tcmX Y n 1))).d 0 1).hom (gsign Y n), hmemg⟩ := by
    apply Subtype.ext
    refine (relMapLM_coe (R := ℤ) (X₁ := TopCat.of (tcmX Y n 1)) (X₂ := TopCat.of (RankTwo.Y1 Y))
      (tcmC Y n 1) (Punct Y 1) (TopCat.ofHom (tcmPr2 Y n 1))
      (fun x hx => hx) 1 (RankTwo.t1punt Y)).trans ?_
    exact (cochainDiff_gsign Y n).symm.trans
      (singularCochain_d_apply ℤ (TopCat.of (tcmX Y n 1)) (gsign Y n)).symm
  have hR : (relCohMap (tcmPr2 Y n 1) (tcmC Y n 1) (Punct Y 1) (fun x hx => hx) ℤ 1).hom
        (Mpun 1 Y)
      = relClassOf ℤ (TopCat.of (tcmX Y n 1)) (tcmC Y n 1)
          ⟨((singularCochainComplex ℤ (TopCat.of (tcmX Y n 1))).d 0 1).hom (gsign Y n), hmemg⟩
          hcocg := by
    refine (congrArg (fun z => (relCohMap (tcmPr2 Y n 1) (tcmC Y n 1) (Punct Y 1)
      (fun x hx => hx) ℤ 1).hom z) (RankTwo.t1_class_punct Y).symm).trans ?_
    refine (homologyMap_relComplexMap_relClassOf (R := ℤ)
      (X₁ := TopCat.of (tcmX Y n 1)) (X₂ := TopCat.of (RankTwo.Y1 Y))
      (A₁ := tcmC Y n 1) (A₂ := Punct Y 1)
      (f := TopCat.ofHom (tcmPr2 Y n 1)) (h := fun x hx => hx) (n := 1)
      (a := RankTwo.t1punt Y) (ha := RankTwo.relDiffLM_t1punt Y)).trans ?_
    refine relClassOf_congr ℤ (TopCat.of (tcmX Y n 1)) (tcmC Y n 1) _ hcocg hrel
  rw [hcls, hδg, hR]

end

end Work.Whitney
