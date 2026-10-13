import Mathlib
import Submission.Work.DSG2.Segre.Basic
import Submission.Work.DSG2.Segre.projChart_relation
import Submission.Work.DSG2.Segre.chartElemAll_surjective
import Submission.Work.DSG2.Segre.Triangle
import Submission.Work.DSG4c.ChartPushout.chartToPoly_surjective
import Submission.Work.DSG2.Segre.cc_base
import Submission.Work.DSG2.Segre.cc_charts
import Submission.Work.DSG2.Segre.cc_trans

/-!
# The two Segre charts agree on the intersection of two product charts

This file assembles the proof of `Work.DSG2.Segre.charts_compat`: for two product charts
`V k`, `V k'` of `P^a_A ×_{Spec A} P^b_A`, the Segre chart maps `sigma k`, `sigma k'` agree on
`V k ∩ V k'` (the pullback of the two open inclusions).

The strategy is to factor both composites through the intersection chart
`Spec (Away (PGr A N) (z_m · z_{m'}))` of `P^N` (`m = toIdx k`, `m' = toIdx k'`), and to compare
the two resulting maps by the ring maps they induce on global sections; `Away x` is a
localization of the `m`-chart `Away (X m)`, and the two chart rings of `P^N` are compared on the
generators `z_p/z_m`, where the chart transition identities of `P^a` and `P^b`
(`cc_alpha_mul`, `cc_beta_mul`) give the compatibility.
-/

namespace Work.DSG2.Segre

universe u

open CategoryTheory AlgebraicGeometry Limits MvPolynomial
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra


section Main

variable (A : Type u) [CommRing A] (a b : ℕ) (k k' : Fin (a+1) × Fin (b+1))

/-! ## The intersection chart of `P^N` -/

/-- The ring of the intersection chart `D₊(z_m z_{m'})` of `P^N`. -/
noncomputable abbrev ccX2Ring :=
  HomogeneousLocalization.Away (DSMap.PGr A (segreN a b)) (ccX2 A a b k k')

/-- The structure map `A →+* Γ(D₊(z_m z_{m'}), ⊤)` of the intersection chart. -/
noncomputable abbrev ccX2map : A →+* ccX2Ring A a b k k' :=
  (HomogeneousLocalization.fromZeroRingHom (DSMap.PGr A (segreN a b))
    (Submonoid.powers (ccX2 A a b k k'))).comp (algebraMap A (DSMap.PGr A (segreN a b) 0))

/-- The intersection chart of `P^N` is a chart of `P^N` over `Spec A`. -/
lemma ccSpec_map_ccX2map : Spec.map (CommRingCat.ofHom (ccX2map A a b k k')) =
    ccIntι A a b k k' ≫ DSMap.PSpace.toSpec A (segreN a b) := by
  show Spec.map (CommRingCat.ofHom ((HomogeneousLocalization.fromZeroRingHom (DSMap.PGr A (segreN a b))
      (Submonoid.powers (ccX2 A a b k k'))).comp (algebraMap A (DSMap.PGr A (segreN a b) 0)))) =
    ccIntι A a b k k' ≫ DSMap.PSpace.toSpec A (segreN a b)
  rw [CommRingCat.ofHom_comp, Spec.map_comp,
    ← Proj.awayι_toSpecZero (𝒜 := DSMap.PGr A (segreN a b)) (f := ccX2 A a b k k') (m := 2)
      (f_deg := ccX2_mem A a b k k') (hm := by norm_num),
    Category.assoc]
  rfl

/-- The constants of the intersection chart are the constants of the `m`-chart. -/
lemma ccAM_chartMap (c : A) :
    ccAM A a b k k' (Work.DSG4c.chartMap A (segreN a b) (toIdx a b k) c) =
      ccX2map A a b k k' c := by
  rw [Work.DSG4c.chartMap]
  exact HomogeneousLocalization.awayMap_fromZeroRingHom ..

/-! ## The coordinate functions of the two product charts -/

/-- The `x`-coordinate `x_p/x_{k.1}` of the `k`-chart of `P^a`, as a function on `ccP`. -/
noncomputable abbrev ccxiL (p : Fin (a+1)) : Γ(ccP A a b k k', ⊤) :=
  (cc_rr (ccP A a b k k') (chartRingA A a k.1) (ccAlphaL A a b k k'))
    (Work.DSG4c.ChartPushout.chartElemAll A a k.1 p)

/-- The `y`-coordinate `y_q/y_{k.2}` of the `k`-chart of `P^b`, as a function on `ccP`. -/
noncomputable abbrev ccetaL (q : Fin (b+1)) : Γ(ccP A a b k k', ⊤) :=
  (cc_rr (ccP A a b k k') (chartRingB A b k.2) (ccBetaL A a b k k'))
    (Work.DSG4c.ChartPushout.chartElemAll A b k.2 q)

/-- The `x`-coordinate `x_p/x_{k'.1}` of the `k'`-chart of `P^a`, as a function on `ccP`. -/
noncomputable abbrev ccxiR (p : Fin (a+1)) : Γ(ccP A a b k k', ⊤) :=
  (cc_rr (ccP A a b k k') (chartRingA A a k'.1) (ccAlphaR A a b k k'))
    (Work.DSG4c.ChartPushout.chartElemAll A a k'.1 p)

/-- The `y`-coordinate `y_q/y_{k'.2}` of the `k'`-chart of `P^b`, as a function on `ccP`. -/
noncomputable abbrev ccetaR (q : Fin (b+1)) : Γ(ccP A a b k k', ⊤) :=
  (cc_rr (ccP A a b k k') (chartRingB A b k'.2) (ccBetaR A a b k k'))
    (Work.DSG4c.ChartPushout.chartElemAll A b k'.2 q)

lemma ccxiR_self : ccxiR A a b k k' k'.1 = 1 := by
  rw [ccxiR, Work.DSG4c.ChartPushout.chartElemAll_self, map_one]

lemma ccetaR_self : ccetaR A a b k k' k'.2 = 1 := by
  rw [ccetaR, Work.DSG4c.ChartPushout.chartElemAll_self, map_one]

/-- The chart transition identity of `P^a` on `ccP`. -/
lemma ccxiL_ccxiR_eq (p : Fin (a+1)) :
    ccxiL A a b k k' p * ccxiR A a b k k' k.1 = ccxiR A a b k k' p :=
  cc_alpha_mul A a b k k' p

/-- The chart transition identity of `P^b` on `ccP`. -/
lemma ccetaL_ccetaR_eq (q : Fin (b+1)) :
    ccetaL A a b k k' q * ccetaR A a b k k' k.2 = ccetaR A a b k k' q :=
  cc_beta_mul A a b k k' q

lemma ccxiL_mul_ccxiR : ccxiL A a b k k' k'.1 * ccxiR A a b k k' k.1 = 1 := by
  rw [ccxiL_ccxiR_eq A a b k k' k'.1, ccxiR_self A a b k k']

lemma ccetaL_mul_ccetaR : ccetaL A a b k k' k'.2 * ccetaR A a b k k' k.2 = 1 := by
  rw [ccetaL_ccetaR_eq A a b k k' k'.2, ccetaR_self A a b k k']

/-- Solving the transition identity for the `k`-coordinate. -/
lemma ccxiL_eq (p : Fin (a+1)) :
    ccxiL A a b k k' p = ccxiR A a b k k' p * ccxiL A a b k k' k'.1 := by
  have h := ccxiL_ccxiR_eq A a b k k' p
  rw [← h, mul_assoc, mul_comm (ccxiR A a b k k' k.1) (ccxiL A a b k k' k'.1),
    ccxiL_mul_ccxiR A a b k k', mul_one]

/-- Solving the transition identity for the `k`-coordinate, `P^b` version. -/
lemma ccetaL_eq (q : Fin (b+1)) :
    ccetaL A a b k k' q = ccetaR A a b k k' q * ccetaL A a b k k' k'.2 := by
  have h := ccetaL_ccetaR_eq A a b k k' q
  rw [← h, mul_assoc, mul_comm (ccetaR A a b k k' k.2) (ccetaL A a b k k' k'.2),
    ccetaL_mul_ccetaR A a b k k', mul_one]

/-! ## The two chart maps of the Segre embedding -/

/-- The value of the `k`-chart Segre map `ccPhi` on the chart coordinate `z_p/z_m`. -/
noncomputable abbrev ccPhiEval (p : Fin (segreN a b + 1)) : Γ(ccP A a b k k', ⊤) :=
  (cc_rr (ccP A a b k k') (Work.DSG4c.awayChart A (segreN a b) (toIdx a b k))
    (ccPhi A a b k k')) (Work.DSG4c.ChartPushout.chartElemAll A (segreN a b) (toIdx a b k) p)

/-- The value of the `k'`-chart Segre map `ccPsi` on the chart coordinate. -/
noncomputable abbrev ccPsiEval (p : Fin (segreN a b + 1)) : Γ(ccP A a b k k', ⊤) :=
  (cc_rr (ccP A a b k k') (Work.DSG4c.awayChart A (segreN a b) (toIdx a b k'))
    (ccPsi A a b k k')) (Work.DSG4c.ChartPushout.chartElemAll A (segreN a b) (toIdx a b k') p)

/-- `ccPhi` followed by the `k`-chart inclusion is `ccSigmaF`. -/
lemma ccPhi_toSpec : ccPhi A a b k k' ≫ Spec.map (CommRingCat.ofHom
      (Work.DSG4c.chartMap A (segreN a b) (toIdx a b k))) =
    ccSigmaF A a b k k' ≫ DSMap.PSpace.toSpec A (segreN a b) := by
  have h1 : ccPhi A a b k k' ≫ Spec.map (CommRingCat.ofHom
        (Work.DSG4c.chartMap A (segreN a b) (toIdx a b k))) =
      (ccPhi A a b k k' ≫ Work.DSG4c.chartι A (segreN a b) (toIdx a b k)) ≫
        DSMap.PSpace.toSpec A (segreN a b) := by
    rw [← Work.DSG4c.chartι_comp_toSpec A (segreN a b) (toIdx a b k), ← Category.assoc]
  rw [h1, ccPhi_fac A a b k k']

/-- The two composites of `ccSigmaF` and `ccSigmaG` with the structure map agree. -/
lemma ccSigma_toSpec : ccSigmaF A a b k k' ≫ DSMap.PSpace.toSpec A (segreN a b) =
    ccSigmaG A a b k k' ≫ DSMap.PSpace.toSpec A (segreN a b) := by
  have hSF : ccSigmaF A a b k k' ≫ DSMap.PSpace.toSpec A (segreN a b) =
      (pullback.fst (V A a b k).ι (V A a b k').ι ≫ (V A a b k).ι) ≫
        (pullback.fst (DSMap.PSpace.toSpec A a) (DSMap.PSpace.toSpec A b) ≫
          DSMap.PSpace.toSpec A a) := by
    simp only [ccSigmaF, Category.assoc, sigma_toSpec A a b k]
  have hSG : ccSigmaG A a b k k' ≫ DSMap.PSpace.toSpec A (segreN a b) =
      (pullback.snd (V A a b k).ι (V A a b k').ι ≫ (V A a b k').ι) ≫
        (pullback.fst (DSMap.PSpace.toSpec A a) (DSMap.PSpace.toSpec A b) ≫
          DSMap.PSpace.toSpec A a) := by
    simp only [ccSigmaG, Category.assoc, sigma_toSpec A a b k']
  rw [hSF, hSG, pullback.condition]

/-- The reduction of `ccPhi` to the product chart: `cc_rr ccPhi` factors through `segreChart`. -/
lemma ccPhi_rr : cc_rr (ccP A a b k k') (Work.DSG4c.awayChart A (segreN a b) (toIdx a b k))
      (ccPhi A a b k k') =
    (cc_rr (ccP A a b k k') (chartRing A a b k) (ccThetaL A a b k k')).comp
      (segreChart A a b k) := by
  have h : ccThetaL A a b k k' ≫ Spec.map (CommRingCat.ofHom (segreChart A a b k)) =
      ccPhi A a b k k' := by
    simp only [ccPhi, ccThetaL, Category.assoc]
  rw [← h]
  exact cc_rr_comp_specMap (h := ccThetaL A a b k k') (φ := segreChart A a b k)

/-- The reduction of `ccPsi` to the product chart. -/
lemma ccPsi_rr : cc_rr (ccP A a b k k') (Work.DSG4c.awayChart A (segreN a b) (toIdx a b k'))
      (ccPsi A a b k k') =
    (cc_rr (ccP A a b k k') (chartRing A a b k') (ccThetaR A a b k k')).comp
      (segreChart A a b k') := by
  have h : ccThetaR A a b k k' ≫ Spec.map (CommRingCat.ofHom (segreChart A a b k')) =
      ccPsi A a b k k' := by
    simp only [ccPsi, ccThetaR, Category.assoc]
  rw [← h]
  exact cc_rr_comp_specMap (h := ccThetaR A a b k k') (φ := segreChart A a b k')

/-- On a chart coordinate, `ccPhi` is the product of the `x`- and `y`-coordinates. -/
lemma ccPhiEval_eq (p : Fin (segreN a b + 1)) :
    ccPhiEval A a b k k' p =
      ccxiL A a b k k' ((toIdx a b).symm p).1 * ccetaL A a b k k' ((toIdx a b).symm p).2 := by
  have h := RingHom.congr_fun (ccPhi_rr A a b k k')
    (Work.DSG4c.ChartPushout.chartElemAll A (segreN a b) (toIdx a b k) p)
  simp only [RingHom.comp_apply] at h
  rw [cc_segreChart_chartElemAll A a b k p] at h
  rw [ccThetaL_comp A a b k k'] at h
  exact h

/-- On a chart coordinate, `ccPsi` is the product of the `x`- and `y`-coordinates. -/
lemma ccPsiEval_eq (p : Fin (segreN a b + 1)) :
    ccPsiEval A a b k k' p =
      ccxiR A a b k k' ((toIdx a b).symm p).1 * ccetaR A a b k k' ((toIdx a b).symm p).2 := by
  have h := RingHom.congr_fun (ccPsi_rr A a b k k')
    (Work.DSG4c.ChartPushout.chartElemAll A (segreN a b) (toIdx a b k') p)
  simp only [RingHom.comp_apply] at h
  rw [cc_segreChart_chartElemAll A a b k' p] at h
  rw [ccThetaR_comp A a b k k'] at h
  exact h

/-- The `m'`-coordinate of `ccPsi` is `1`. -/
lemma ccPsiEval_self : ccPsiEval A a b k k' (toIdx a b k') = 1 := by
  rw [ccPsiEval, Work.DSG4c.ChartPushout.chartElemAll_self, map_one]

/-- The compatibility relation between the two chart maps, in the `m`-chart. -/
lemma ccPhiPsi_mul (p : Fin (segreN a b + 1)) :
    ccPhiEval A a b k k' p * ccPsiEval A a b k k' (toIdx a b k) = ccPsiEval A a b k k' p := by
  rw [ccPhiEval_eq A a b k k' p, ccPsiEval_eq A a b k k' (toIdx a b k), ccPsiEval_eq A a b k k' p]
  simp only [Equiv.symm_apply_apply]
  calc (ccxiL A a b k k' ((toIdx a b).symm p).1 * ccetaL A a b k k' ((toIdx a b).symm p).2) *
        (ccxiR A a b k k' k.1 * ccetaR A a b k k' k.2)
      = (ccxiL A a b k k' ((toIdx a b).symm p).1 * ccxiR A a b k k' k.1) *
        (ccetaL A a b k k' ((toIdx a b).symm p).2 * ccetaR A a b k k' k.2) := by ring
    _ = ccxiR A a b k k' ((toIdx a b).symm p).1 *
        ccetaR A a b k k' ((toIdx a b).symm p).2 := by
        rw [ccxiL_ccxiR_eq A a b k k' ((toIdx a b).symm p).1,
          ccetaL_ccetaR_eq A a b k k' ((toIdx a b).symm p).2]

/-- The compatibility relation between the two chart maps, in the `m'`-chart. -/
lemma ccPhiPsi_mul' (p : Fin (segreN a b + 1)) :
    ccPsiEval A a b k k' p * ccPhiEval A a b k k' (toIdx a b k') = ccPhiEval A a b k k' p := by
  rw [ccPsiEval_eq A a b k k' p, ccPhiEval_eq A a b k k' (toIdx a b k'), ccPhiEval_eq A a b k k' p]
  simp only [Equiv.symm_apply_apply]
  calc (ccxiR A a b k k' ((toIdx a b).symm p).1 * ccetaR A a b k k' ((toIdx a b).symm p).2) *
        (ccxiL A a b k k' k'.1 * ccetaL A a b k k' k'.2)
      = (ccxiR A a b k k' ((toIdx a b).symm p).1 * ccxiL A a b k k' k'.1) *
        (ccetaR A a b k k' ((toIdx a b).symm p).2 * ccetaL A a b k k' k'.2) := by ring
    _ = ccxiL A a b k k' ((toIdx a b).symm p).1 *
        ccetaL A a b k k' ((toIdx a b).symm p).2 := by
        rw [← ccxiL_eq A a b k k' ((toIdx a b).symm p).1,
          ← ccetaL_eq A a b k k' ((toIdx a b).symm p).2]

/-! ## The comparison of the two lifts -/

/-- **The main compatibility computation.**  Two maps `f`, `g` into the intersection chart of
`P^N` which restrict to the `k`- and `k'`-chart Segre maps and are morphisms over `Spec A` agree:
their induced maps on global sections are both determined by their restriction to the `m`-chart,
where they agree by the chart transition identities of `P^a` and `P^b`. -/
lemma ccPhiPsi_crux
    (f g : ccP A a b k k' ⟶ Spec (CommRingCat.of (ccX2Ring A a b k k')))
    (hfPhi : f ≫ Spec.map (CommRingCat.ofHom (ccAM A a b k k')) = ccPhi A a b k k')
    (hgPsi : g ≫ Spec.map (CommRingCat.ofHom (ccAM' A a b k k')) = ccPsi A a b k k')
    (hf : f ≫ Spec.map (CommRingCat.ofHom (ccX2map A a b k k')) =
      ccSigmaF A a b k k' ≫ DSMap.PSpace.toSpec A (segreN a b))
    (hg : g ≫ Spec.map (CommRingCat.ofHom (ccX2map A a b k k')) =
      ccSigmaG A a b k k' ≫ DSMap.PSpace.toSpec A (segreN a b))
    (hFG : ccSigmaF A a b k k' ≫ DSMap.PSpace.toSpec A (segreN a b) =
      ccSigmaG A a b k k' ≫ DSMap.PSpace.toSpec A (segreN a b)) :
    cc_rr (ccP A a b k k') (ccX2Ring A a b k k') f =
      cc_rr (ccP A a b k k') (ccX2Ring A a b k k') g := by
  letI : Algebra A (ccX2Ring A a b k k') := (ccX2map A a b k k').toAlgebra
  letI : Algebra (Work.DSG4c.awayChart A (segreN a b) (toIdx a b k)) (ccX2Ring A a b k k') :=
    (ccAM A a b k k').toAlgebra
  -- the two charts of `P^N` seen from `ccP`
  have hj : (cc_rr (ccP A a b k k') (ccX2Ring A a b k k') f).comp (ccAM A a b k k') =
      cc_rr (ccP A a b k k') (Work.DSG4c.awayChart A (segreN a b) (toIdx a b k))
        (ccPhi A a b k k') := by
    have h := cc_rr_comp_specMap (Y := ccP A a b k k') (h := f) (φ := ccAM A a b k k')
    rw [hfPhi] at h
    exact h.symm
  have hg' : (cc_rr (ccP A a b k k') (ccX2Ring A a b k k') g).comp (ccAM' A a b k k') =
      cc_rr (ccP A a b k k') (Work.DSG4c.awayChart A (segreN a b) (toIdx a b k'))
        (ccPsi A a b k k') := by
    have h := cc_rr_comp_specMap (Y := ccP A a b k k') (h := g) (φ := ccAM' A a b k k')
    rw [hgPsi] at h
    exact h.symm
  -- the two charts are charts over `Spec A`
  have hfx : (cc_rr (ccP A a b k k') (ccX2Ring A a b k k') f).comp (ccX2map A a b k k') =
      cc_rr (ccP A a b k k') A
        (ccSigmaF A a b k k' ≫ DSMap.PSpace.toSpec A (segreN a b)) := by
    have h := cc_rr_comp_specMap (Y := ccP A a b k k') (h := f) (φ := ccX2map A a b k k')
    rw [hf] at h
    exact h.symm
  have hgx : (cc_rr (ccP A a b k k') (ccX2Ring A a b k k') g).comp (ccX2map A a b k k') =
      cc_rr (ccP A a b k k') A
        (ccSigmaG A a b k k' ≫ DSMap.PSpace.toSpec A (segreN a b)) := by
    have h := cc_rr_comp_specMap (Y := ccP A a b k k') (h := g) (φ := ccX2map A a b k k')
    rw [hg] at h
    exact h.symm
  have hPhi_x : (cc_rr (ccP A a b k k') (Work.DSG4c.awayChart A (segreN a b) (toIdx a b k))
        (ccPhi A a b k k')).comp (Work.DSG4c.chartMap A (segreN a b) (toIdx a b k)) =
      cc_rr (ccP A a b k k') A
        (ccSigmaF A a b k k' ≫ DSMap.PSpace.toSpec A (segreN a b)) := by
    have h := cc_rr_comp_specMap (Y := ccP A a b k k') (h := ccPhi A a b k k')
      (φ := Work.DSG4c.chartMap A (segreN a b) (toIdx a b k))
    rw [ccPhi_toSpec A a b k k'] at h
    exact h.symm
  -- the constants agree
  have hconst : (cc_rr (ccP A a b k k') (ccX2Ring A a b k k') f).comp (ccX2map A a b k k') =
      (cc_rr (ccP A a b k k') (ccX2Ring A a b k k') g).comp (ccX2map A a b k k') := by
    rw [hfx, hgx, hFG]
  -- the `m'`-chart of `P^N` seen through `g`
  have hPsi_app : ∀ (y : Work.DSG4c.awayChart A (segreN a b) (toIdx a b k')),
      (cc_rr (ccP A a b k k') (ccX2Ring A a b k k') g) (ccAM' A a b k k' y) =
        (cc_rr (ccP A a b k k') (Work.DSG4c.awayChart A (segreN a b) (toIdx a b k'))
          (ccPsi A a b k k')) y := by
    intro y
    rw [← RingHom.comp_apply, hg']
  -- the product of the two transition elements is `1`
  have hprod : (ccAM A a b k k'
        (Work.DSG4c.ChartPushout.chartElemAll A (segreN a b) (toIdx a b k) (toIdx a b k'))) *
      (ccAM' A a b k k'
        (Work.DSG4c.ChartPushout.chartElemAll A (segreN a b) (toIdx a b k') (toIdx a b k))) = 1 := by
    have hrel := projChart_relation A (segreN a b) (toIdx a b k) (toIdx a b k') (toIdx a b k)
    rw [Work.DSG4c.ChartPushout.chartElemAll_self, map_one] at hrel
    exact (mul_comm _ _).trans hrel.symm
  -- `g` on the transition element of the `m`-chart
  have hg_v : (cc_rr (ccP A a b k k') (ccX2Ring A a b k k') g)
      (ccAM A a b k k'
        (Work.DSG4c.ChartPushout.chartElemAll A (segreN a b) (toIdx a b k) (toIdx a b k'))) *
      ccPsiEval A a b k k' (toIdx a b k) = 1 := by
    rw [ccPsiEval, ← hPsi_app, ← map_mul, hprod, map_one]
  -- `ccPhi` on the transition element
  have hphi_v : ccPhiEval A a b k k' (toIdx a b k') * ccPsiEval A a b k k' (toIdx a b k) = 1 := by
    rw [ccPhiPsi_mul A a b k k' (toIdx a b k'), ccPsiEval_self A a b k k']
  have hunit : (cc_rr (ccP A a b k k') (ccX2Ring A a b k k') g)
      (ccAM A a b k k'
        (Work.DSG4c.ChartPushout.chartElemAll A (segreN a b) (toIdx a b k) (toIdx a b k'))) =
      ccPhiEval A a b k k' (toIdx a b k') := by
    calc (cc_rr (ccP A a b k k') (ccX2Ring A a b k k') g)
          (ccAM A a b k k'
            (Work.DSG4c.ChartPushout.chartElemAll A (segreN a b) (toIdx a b k) (toIdx a b k')))
        = (cc_rr (ccP A a b k k') (ccX2Ring A a b k k') g)
            (ccAM A a b k k'
              (Work.DSG4c.ChartPushout.chartElemAll A (segreN a b) (toIdx a b k)
                (toIdx a b k'))) * 1 := (mul_one _).symm
      _ = (cc_rr (ccP A a b k k') (ccX2Ring A a b k k') g)
            (ccAM A a b k k'
              (Work.DSG4c.ChartPushout.chartElemAll A (segreN a b) (toIdx a b k)
                (toIdx a b k'))) *
          (ccPhiEval A a b k k' (toIdx a b k') * ccPsiEval A a b k k' (toIdx a b k)) := by
            rw [hphi_v]
      _ = ((cc_rr (ccP A a b k k') (ccX2Ring A a b k k') g)
            (ccAM A a b k k'
              (Work.DSG4c.ChartPushout.chartElemAll A (segreN a b) (toIdx a b k)
                (toIdx a b k'))) * ccPsiEval A a b k k' (toIdx a b k)) *
          ccPhiEval A a b k k' (toIdx a b k') := by ring
      _ = 1 * ccPhiEval A a b k k' (toIdx a b k') := by rw [hg_v]
      _ = ccPhiEval A a b k k' (toIdx a b k') := one_mul _
  -- `g` on the generators of the `m`-chart
  have hgen_val (p : Fin (segreN a b + 1)) :
      (cc_rr (ccP A a b k k') (ccX2Ring A a b k k') g)
        (ccAM A a b k k'
          (Work.DSG4c.ChartPushout.chartElemAll A (segreN a b) (toIdx a b k) p)) =
        ccPhiEval A a b k k' p := by
    have hrel := projChart_relation A (segreN a b) (toIdx a b k) (toIdx a b k') p
    rw [hrel, map_mul, hPsi_app, hunit, ccPhiPsi_mul' A a b k k' p]
  -- the two composites with the surjection `A[X] → Away m`
  have hsurj := chartElemAll_surjective A (segreN a b) (toIdx a b k)
  have hgen : ((cc_rr (ccP A a b k k') (ccX2Ring A a b k k') g).comp (ccAM A a b k k')).comp
        (MvPolynomial.aeval (R := A)
          (fun q : Fin (segreN a b + 1) =>
            Work.DSG4c.ChartPushout.chartElemAll A (segreN a b) (toIdx a b k) q)).toRingHom =
      (cc_rr (ccP A a b k k') (Work.DSG4c.awayChart A (segreN a b) (toIdx a b k))
        (ccPhi A a b k k')).comp
        (MvPolynomial.aeval (R := A)
          (fun q : Fin (segreN a b + 1) =>
            Work.DSG4c.ChartPushout.chartElemAll A (segreN a b) (toIdx a b k) q)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply]
      rw [show (MvPolynomial.aeval (R := A)
            (fun q : Fin (segreN a b + 1) =>
              Work.DSG4c.ChartPushout.chartElemAll A (segreN a b) (toIdx a b k) q)).toRingHom
            (MvPolynomial.C c) =
          algebraMap A (Work.DSG4c.awayChart A (segreN a b) (toIdx a b k)) c
        from MvPolynomial.aeval_C _ c]
      rw [awayChart_algebraMap A (segreN a b) (toIdx a b k), ccAM_chartMap A a b k k' c]
      show ((cc_rr (ccP A a b k k') (ccX2Ring A a b k k') g).comp (ccX2map A a b k k')) c =
        ((cc_rr (ccP A a b k k') (Work.DSG4c.awayChart A (segreN a b) (toIdx a b k))
          (ccPhi A a b k k')).comp
            (Work.DSG4c.chartMap A (segreN a b) (toIdx a b k))) c
      rw [← hconst, hfx, hPhi_x]
    · intro q
      simp only [RingHom.comp_apply]
      rw [show (MvPolynomial.aeval (R := A)
            (fun q : Fin (segreN a b + 1) =>
              Work.DSG4c.ChartPushout.chartElemAll A (segreN a b) (toIdx a b k) q)).toRingHom
            (MvPolynomial.X q) =
          Work.DSG4c.ChartPushout.chartElemAll A (segreN a b) (toIdx a b k) q
        from MvPolynomial.aeval_X _ q]
      exact hgen_val q
  -- `g` restricts to `ccPhi` on the `m`-chart
  have hgPhi : (cc_rr (ccP A a b k k') (ccX2Ring A a b k k') g).comp (ccAM A a b k k') =
      cc_rr (ccP A a b k k') (Work.DSG4c.awayChart A (segreN a b) (toIdx a b k))
        (ccPhi A a b k k') := by
    refine RingHom.ext fun y => ?_
    obtain ⟨p, hp⟩ := hsurj y
    rw [← hp]
    exact RingHom.congr_fun hgen p
  -- the localization comparison
  have hloc : IsLocalization (Submonoid.powers
      (Work.DSG4c.ChartPushout.chartElemAll A (segreN a b) (toIdx a b k) (toIdx a b k')))
      (ccX2Ring A a b k k') := by
    have hbase := HomogeneousLocalization.Away.isLocalization_mul (𝒜 := DSMap.PGr A (segreN a b))
      (d := 1) (e := 1) (hf := Work.DSG4c.X_mem A (segreN a b) (toIdx a b k))
      (hg := Work.DSG4c.X_mem A (segreN a b) (toIdx a b k')) (hx := rfl) (hd := one_ne_zero)
    rw [cc_isLocalizationElem_chartElemAll A (segreN a b) (toIdx a b k) (toIdx a b k')] at hbase
    exact hbase
  haveI := hloc
  have hkey : (cc_rr (ccP A a b k k') (ccX2Ring A a b k k') f).comp
        (algebraMap (Work.DSG4c.awayChart A (segreN a b) (toIdx a b k)) (ccX2Ring A a b k k')) =
      (cc_rr (ccP A a b k k') (ccX2Ring A a b k k') g).comp
        (algebraMap (Work.DSG4c.awayChart A (segreN a b) (toIdx a b k)) (ccX2Ring A a b k k')) := by
    show (cc_rr (ccP A a b k k') (ccX2Ring A a b k k') f).comp (ccAM A a b k k') =
      (cc_rr (ccP A a b k k') (ccX2Ring A a b k k') g).comp (ccAM A a b k k')
    rw [hj, hgPhi]
  exact IsLocalization.ringHom_ext (Submonoid.powers
    (Work.DSG4c.ChartPushout.chartElemAll A (segreN a b) (toIdx a b k) (toIdx a b k'))) hkey

/-! ## The chart compatibility -/

/-- The two chart-wise Segre maps agree on the intersection of the charts. -/
theorem ccSigmaF_eq_ccSigmaG : ccSigmaF A a b k k' = ccSigmaG A a b k k' := by
  have hF := cc_range_F A a b k k'
  have hG := cc_range_G A a b k k'
  set lF : ccP A a b k k' ⟶ Spec (CommRingCat.of (ccX2Ring A a b k k')) :=
    IsOpenImmersion.lift (ccIntι A a b k k') (ccSigmaF A a b k k') hF with hlFdef
  set lG : ccP A a b k k' ⟶ Spec (CommRingCat.of (ccX2Ring A a b k k')) :=
    IsOpenImmersion.lift (ccIntι A a b k k') (ccSigmaG A a b k k') hG with hlGdef
  have hlF : lF ≫ ccIntι A a b k k' = ccSigmaF A a b k k' := by
    rw [hlFdef]
    exact IsOpenImmersion.lift_fac _ _ _
  have hlG : lG ≫ ccIntι A a b k k' = ccSigmaG A a b k k' := by
    rw [hlGdef]
    exact IsOpenImmersion.lift_fac _ _ _
  haveI : Mono (Work.DSG4c.chartι A (segreN a b) (toIdx a b k)) := IsOpenImmersion.mono _
  haveI : Mono (Work.DSG4c.chartι A (segreN a b) (toIdx a b k')) := IsOpenImmersion.mono _
  have hFphi : lF ≫ Spec.map (CommRingCat.ofHom (ccAM A a b k k')) = ccPhi A a b k k' := by
    apply (cancel_mono (Work.DSG4c.chartι A (segreN a b) (toIdx a b k))).mp
    have h1 : (lF ≫ Spec.map (CommRingCat.ofHom (ccAM A a b k k'))) ≫
        Work.DSG4c.chartι A (segreN a b) (toIdx a b k) = lF ≫ ccIntι A a b k k' := by
      rw [Category.assoc, ← ccIntι_fac A a b k k']
    rw [h1, hlF, ccPhi_fac A a b k k']
  have hGpsi : lG ≫ Spec.map (CommRingCat.ofHom (ccAM' A a b k k')) = ccPsi A a b k k' := by
    apply (cancel_mono (Work.DSG4c.chartι A (segreN a b) (toIdx a b k'))).mp
    have h1 : (lG ≫ Spec.map (CommRingCat.ofHom (ccAM' A a b k k'))) ≫
        Work.DSG4c.chartι A (segreN a b) (toIdx a b k') = lG ≫ ccIntι A a b k k' := by
      rw [Category.assoc, ← ccIntι_fac' A a b k k']
    rw [h1, hlG, ccPsi_fac A a b k k']
  have hFtoSpec : lF ≫ Spec.map (CommRingCat.ofHom (ccX2map A a b k k')) =
      ccSigmaF A a b k k' ≫ DSMap.PSpace.toSpec A (segreN a b) := by
    rw [ccSpec_map_ccX2map A a b k k', ← Category.assoc, hlF]
  have hGtoSpec : lG ≫ Spec.map (CommRingCat.ofHom (ccX2map A a b k k')) =
      ccSigmaG A a b k k' ≫ DSMap.PSpace.toSpec A (segreN a b) := by
    rw [ccSpec_map_ccX2map A a b k k', ← Category.assoc, hlG]
  have hlFG : lF = lG := cc_rr_ext
    (ccPhiPsi_crux A a b k k' lF lG hFphi hGpsi hFtoSpec hGtoSpec (ccSigma_toSpec A a b k k'))
  calc ccSigmaF A a b k k' = lF ≫ ccIntι A a b k k' := hlF.symm
    _ = lG ≫ ccIntι A a b k k' := by rw [hlFG]
    _ = ccSigmaG A a b k k' := hlG

end Main

end Work.DSG2.Segre
