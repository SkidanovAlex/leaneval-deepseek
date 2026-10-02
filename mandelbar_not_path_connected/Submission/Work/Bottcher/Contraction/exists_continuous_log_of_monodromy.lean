import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.Bottcher.Contraction.LiftCoreDefs
import Submission.Work.Bottcher.Contraction.NormFactorRoots
import Submission.Work.Bottcher.Contraction.isPreconnected_escapeSet
import Submission.Work.Bottcher.Contraction.bottcher_comm_Tantibar_of_analytic
import Submission.Work.Bottcher.LogLift.Defs
import Submission.Work.Bottcher.LogLift.liftChange_concatC
import Submission.Work.Bottcher.LogLift.liftChange_revC
import Submission.Work.Bottcher.LogLift.exists_tendsto_zero_log_of_continuous_log

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# A continuous logarithm of the normalised Böttcher factor from trivial monodromy

`Work.Bottcher.Contraction.exists_continuous_log_of_monodromy`: if every loop `γ` in the
escape set of the tricorn at a Mandelbar parameter has trivial monodromy (the lift change of
the normalised factor `normFactorPath c γ` through `Complex.exp` vanishes), then the
normalised Böttcher factor `pMap c z / z^4` admits a *continuous* logarithm
`L : ℂ → ℂ` on the escape set which is flat at infinity (`L → 0` as `z → ∞`).

The proof is the covering-space lifting criterion.  On the escape set `U = {G_c > 0}`
(open, preconnected, hence path connected) the monodromy hypothesis says that the
endpoint of the lift of `normFactor` along a path depends only on the endpoint of the path;
`IsLocalHomeomorph.existsUnique_continuousMap_lifts` then produces a global lift
`F : C(U, ℂ)`, and `L := F` extended by `0` off `U` is a continuous logarithm.  Flatness at
infinity is obtained by subtracting the constant (`2πiℤ`-valued) discrepancy between `L`
and the principal logarithm `Complex.log ∘ normFactor` on the far region.

The two path-manipulation lemmas `liftChange_concatC` / `liftChange_revC` (in
`Submission.Work.Bottcher.LogLift`) and the normalisation lemma
`exists_tendsto_zero_log_of_continuous_log` are proved separately.
-/

open Filter Function
open scoped Topology ComplexConjugate

namespace Work.Bottcher.Contraction

noncomputable section

open Work.Bottcher.LogLift

theorem liftChange_eq_sub_of_lift {δ : C(unitInterval, ℂ)} (hδ : ∀ t, δ t ≠ 0)
    {Γ : C(unitInterval, ℂ)} (hΓ : ∀ t, Complex.exp (Γ t) = δ t) (e : ℂ) (hΓe : Γ 0 = e) :
    liftChange δ hδ = Γ 1 - e := by
  have he : Complex.exp e = δ 0 := by rw [← hΓe, hΓ 0]
  have hlift : liftOf δ hδ e he = Γ := by
    rw [liftOf]
    exact ((Complex.isCoveringMap_exp.eq_liftPath_iff' (Subtype.ext he.symm)).mpr
      ⟨by funext t; apply Subtype.ext; exact hΓ t, hΓe⟩).symm
  rw [liftChange_eq_liftOf δ hδ e he, hlift]

theorem exists_continuous_log_of_monodromy (c : ℂ) (hc : c ∈ LeanEval.ComplexAnalysis.Mandelbar)
    (hmono : ∀ (γ : C(unitInterval, ℂ)) (hloop : γ 1 = γ 0)
      (hγ : ∀ t, 0 < Work.Bottcher.green c (γ t)) (hγne : ∀ t, γ t ≠ 0)
      (h : ∀ t, Work.Bottcher.Contraction.normFactorPath c γ hγne t ≠ 0),
      Work.Bottcher.Contraction.liftChange (Work.Bottcher.Contraction.normFactorPath c γ hγne) h = 0) :
    ∃ L : ℂ → ℂ, ContinuousOn L (Work.Bottcher.EscapeSet c) ∧
      (∀ z : ℂ, 0 < Work.Bottcher.green c z →
        Complex.exp (L z) = Work.Bottcher.pMap c z / z ^ 4) ∧
      Filter.Tendsto L (Filter.cocompact ℂ) (nhds (0 : ℂ)) := by
  classical
  have h0green : Work.Bottcher.green c 0 = 0 := green_zero_of_mem_mandelbar c hc
  have hne0 : ∀ z : ℂ, 0 < Work.Bottcher.green c z → z ≠ 0 := by
    intro z hz hz0; rw [hz0, h0green] at hz; exact lt_irrefl 0 hz
  have hnorm_ne : ∀ z : ℂ, 0 < Work.Bottcher.green c z → Work.Bottcher.normFactor c z ≠ 0 :=
    fun z hz => normFactor_ne_zero_of_mem_mandelbar c hc hz
  set z₁ : ℂ := ((Work.Bottcher.escapeRadius c + 1 : ℝ) : ℂ) with hz₁def
  have hz₁far : Work.Bottcher.escapeRadius c < ‖z₁‖ := by
    rw [hz₁def, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith [Work.Bottcher.Core.escapeRadius_pos c])]
    linarith [Work.Bottcher.Core.escapeRadius_pos c]
  have hz₁mem : 0 < Work.Bottcher.green c z₁ :=
    green_pos_of_escapeRadius_le c (le_of_lt hz₁far)
  let U : Set ℂ := Work.Bottcher.EscapeSet c
  have hUo : IsOpen U := isOpen_escapeSet c
  have hUc : IsPreconnected U := isPreconnected_escapeSet c
  haveI : PreconnectedSpace ↥U := isPreconnected_iff_preconnectedSpace.mp hUc
  haveI : LocallyPathConnectedSpace ↥U := hUo.locallyPathConnectedSpace
  haveI : ConnectedSpace ↥U := ConnectedSpace.mk ⟨⟨z₁, hz₁mem⟩⟩
  haveI : PathConnectedSpace ↥U := PathConnectedSpace.of_locallyPathConnectedSpace
  let a₀ : ↥U := ⟨z₁, hz₁mem⟩
  let e₀ : ℂ := Complex.log (Work.Bottcher.normFactor c z₁)
  have he₀ : Complex.exp e₀ = Work.Bottcher.normFactor c z₁ :=
    Complex.exp_log (hnorm_ne z₁ hz₁mem)
  have hcontNF : ContinuousOn (Work.Bottcher.normFactor c) U := by
    have h : Work.Bottcher.normFactor c = fun z : ℂ => Work.Bottcher.pMap c z / z ^ 4 := rfl
    rw [h]
    refine ContinuousOn.div (continuous_pMap c).continuousOn ?_ ?_
    · fun_prop
    · intro z hz; exact pow_ne_zero 4 (hne0 z hz)
  let fmap : C(↥U, {z : ℂ // z ≠ 0}) :=
    ⟨fun a => ⟨Work.Bottcher.normFactor c a.1, hnorm_ne a.1 a.2⟩,
      (continuousOn_iff_continuous_domRestrict.mp hcontNF).subtype_mk (fun a => hnorm_ne a.1 a.2)⟩
  have he : (fun z : ℂ => (⟨Complex.exp z, Complex.exp_ne_zero z⟩ : {z : ℂ // z ≠ 0})) e₀
      = fmap a₀ := by
    apply Subtype.ext; exact he₀
  have hex : ∀ (γ : C(unitInterval, ↥U)), γ 0 = a₀ →
      ∃ Γ : C(unitInterval, ℂ), Γ 0 = e₀ ∧
        (fun z : ℂ => (⟨Complex.exp z, Complex.exp_ne_zero z⟩ : {z : ℂ // z ≠ 0})) ∘ Γ =
          ⇑(fmap.comp γ) := by
    intro γ hγ0
    have hpt : (fmap.comp γ) 0
        = (fun z : ℂ => (⟨Complex.exp z, Complex.exp_ne_zero z⟩ : {z : ℂ // z ≠ 0})) e₀ := by
      rw [ContinuousMap.comp_apply, hγ0]; exact he.symm
    obtain ⟨Γ, hΓlifts, hΓ0⟩ := Complex.isCoveringMap_exp.exists_path_lifts (fmap.comp γ) e₀ hpt
    exact ⟨Γ, hΓ0, hΓlifts⟩
  have huniq : ∀ (γ γ' : C(unitInterval, ↥U)) (Γ Γ' : C(unitInterval, ℂ)),
      γ 0 = a₀ → γ' 0 = a₀ → Γ 0 = e₀ → Γ' 0 = e₀ →
      (fun z : ℂ => (⟨Complex.exp z, Complex.exp_ne_zero z⟩ : {z : ℂ // z ≠ 0})) ∘ Γ = ⇑(fmap.comp γ) →
      (fun z : ℂ => (⟨Complex.exp z, Complex.exp_ne_zero z⟩ : {z : ℂ // z ≠ 0})) ∘ Γ' = ⇑(fmap.comp γ') →
      γ 1 = γ' 1 → Γ 1 = Γ' 1 := by
    intro γ γ' Γ Γ' hγ0 hγ'0 hΓ0 hΓ'0 hpΓ hpΓ' h1
    let subvalC : C(↥U, ℂ) := ⟨Subtype.val, continuous_subtype_val⟩
    let γc : C(unitInterval, ℂ) := subvalC.comp γ
    let γ'c : C(unitInterval, ℂ) := subvalC.comp γ'
    have hγc_green : ∀ s : unitInterval, 0 < Work.Bottcher.green c (γc s) := fun s => (γ s).2
    have hγ'c_green : ∀ s : unitInterval, 0 < Work.Bottcher.green c (γ'c s) := fun s => (γ' s).2
    have hγcne : ∀ t, γc t ≠ 0 := fun t => hne0 (γc t) (hγc_green t)
    have hγ'cne : ∀ t, γ'c t ≠ 0 := fun t => hne0 (γ'c t) (hγ'c_green t)
    let δ : C(unitInterval, ℂ) := normFactorPath c γc hγcne
    let δ' : C(unitInterval, ℂ) := normFactorPath c γ'c hγ'cne
    have hΓlifts : ∀ t, Complex.exp (Γ t) = δ t := by
      intro t
      change Complex.exp (Γ t) = Work.Bottcher.normFactor c (γc t)
      have h2 := congrArg Subtype.val (congrFun hpΓ t)
      simp only [ContinuousMap.comp_apply] at h2
      rwa [show (fmap (γ t) : ℂ) = Work.Bottcher.normFactor c (γc t) from rfl] at h2
    have hΓ'lifts : ∀ t, Complex.exp (Γ' t) = δ' t := by
      intro t
      change Complex.exp (Γ' t) = Work.Bottcher.normFactor c (γ'c t)
      have h2 := congrArg Subtype.val (congrFun hpΓ' t)
      simp only [ContinuousMap.comp_apply] at h2
      rwa [show (fmap (γ' t) : ℂ) = Work.Bottcher.normFactor c (γ'c t) from rfl] at h2
    have h00 : γc 0 = γ'c 0 := by
      have hh := congrArg Subtype.val (hγ0.trans hγ'0.symm)
      simpa [γc, γ'c, subvalC] using hh
    have h01 : γc 1 = γ'c 1 := by
      have hh := congrArg Subtype.val h1
      simpa [γc, γ'c, subvalC] using hh
    have hδ1 : δ 1 = δ' 1 := by
      change normFactorPath c γc hγcne 1 = normFactorPath c γ'c hγ'cne 1
      rw [normFactorPath_apply, normFactorPath_apply, h01]
    have hconv : γc 1 = (revC γ'c) 0 := by
      rw [revC_apply, unitInterval.symm_zero]; exact h01
    let loopC : C(unitInterval, ℂ) := concatC γc (revC γ'c) hconv
    have hloop : loopC 1 = loopC 0 := by
      change concatC γc (revC γ'c) hconv 1 = concatC γc (revC γ'c) hconv 0
      rw [concatC_one, concatC_zero, revC_one]
      exact h00.symm
    have hgreen : ∀ t, 0 < Work.Bottcher.green c (loopC t) := by
      intro t
      change 0 < Work.Bottcher.green c (concatC γc (revC γ'c) hconv t)
      by_cases ht : (t : ℝ) ≤ 1/2
      · rw [concatC_apply_le _ _ _ _ ht]; exact hγc_green _
      · rw [concatC_apply_gt _ _ _ _ ht, revC_apply]; exact hγ'c_green _
    have hne : ∀ t, loopC t ≠ 0 := fun t => hne0 (loopC t) (hgreen t)
    have hnormne : ∀ t, normFactorPath c loopC hne t ≠ 0 :=
      fun t => hnorm_ne (loopC t) (hgreen t)
    have hzero : liftChange (normFactorPath c loopC hne) hnormne = 0 :=
      hmono loopC hloop hgreen hne hnormne
    have hδδ' : δ 1 = (revC δ') 0 := by
      rw [revC_apply, unitInterval.symm_zero]; exact hδ1
    have hlam : normFactorPath c loopC hne = concatC δ (revC δ') hδδ' := by
      ext t
      by_cases ht : (t : ℝ) ≤ 1/2
      · rw [normFactorPath_apply]
        change Work.Bottcher.normFactor c (concatC γc (revC γ'c) hconv t)
          = concatC δ (revC δ') hδδ' t
        rw [concatC_apply_le _ _ _ _ ht, concatC_apply_le _ _ _ _ ht]
        simp only [δ, normFactorPath]
        rfl
      · rw [normFactorPath_apply]
        change Work.Bottcher.normFactor c (concatC γc (revC γ'c) hconv t)
          = concatC δ (revC δ') hδδ' t
        rw [concatC_apply_gt _ _ _ _ ht, concatC_apply_gt _ _ _ _ ht, revC_apply, revC_apply]
        simp only [δ', normFactorPath]
        rfl
    have hlam_pt : ∀ t, normFactorPath c loopC hne t = concatC δ (revC δ') hδδ' t :=
      fun t => DFunLike.congr_fun hlam t
    have hall : ∀ t, concatC δ (revC δ') hδδ' t ≠ 0 := fun t => by
      rw [← hlam_pt t]; exact hnormne t
    have hzero' : liftChange (concatC δ (revC δ') hδδ') hall = 0 := by
      rw [← liftChange_congr hlam hnormne hall]; exact hzero
    have hδne : ∀ t, δ t ≠ 0 := fun t => by
      change Work.Bottcher.normFactor c (γc t) ≠ 0
      exact hnorm_ne (γc t) (hγc_green t)
    have hδ'ne : ∀ t, δ' t ≠ 0 := fun t => by
      change Work.Bottcher.normFactor c (γ'c t) ≠ 0
      exact hnorm_ne (γ'c t) (hγ'c_green t)
    have hrevne : ∀ t, revC δ' t ≠ 0 := revC_ne_zero δ' hδ'ne
    have hadd : liftChange (concatC δ (revC δ') hδδ') hall
        = liftChange δ hδne + liftChange (revC δ') hrevne :=
      liftChange_concatC δ (revC δ') hδne hrevne hδδ' hall
    have hrev : liftChange (revC δ') hrevne = - liftChange δ' hδ'ne :=
      liftChange_revC δ' hδ'ne hrevne
    have heq : liftChange δ hδne = liftChange δ' hδ'ne := by
      have hsum : liftChange δ hδne + liftChange (revC δ') hrevne = 0 := by
        rw [← hadd]; exact hzero'
      rw [hrev] at hsum
      linear_combination hsum
    have hΓ : liftChange δ hδne = Γ 1 - e₀ := liftChange_eq_sub_of_lift hδne hΓlifts e₀ hΓ0
    have hΓ' : liftChange δ' hδ'ne = Γ' 1 - e₀ := liftChange_eq_sub_of_lift hδ'ne hΓ'lifts e₀ hΓ'0
    rw [hΓ, hΓ'] at heq
    linear_combination heq
  obtain ⟨F, ⟨hFa₀, hpF⟩, _⟩ :=
    Complex.isCoveringMap_exp.isLocalHomeomorph.existsUnique_continuousMap_lifts fmap a₀ e₀ he hex huniq
  let L₀ : ℂ → ℂ := fun z => if h : z ∈ U then F ⟨z, h⟩ else 0
  have hL₀cont : ContinuousOn L₀ U := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hF : U.domRestrict L₀ = ⇑F := by
      funext a
      change (if h : (a : ℂ) ∈ U then F ⟨a, h⟩ else 0) = F a
      rw [dif_pos a.2]
    rw [hF]; exact F.continuous
  have hL₀exp : ∀ z : ℂ, 0 < Work.Bottcher.green c z →
      Complex.exp (L₀ z) = Work.Bottcher.pMap c z / z ^ 4 := by
    intro z hz
    have hzU : z ∈ U := hz
    change Complex.exp (if h : z ∈ U then F ⟨z, h⟩ else 0)
      = Work.Bottcher.pMap c z / z ^ 4
    rw [dif_pos hzU]
    have h2 := congrArg Subtype.val (congrFun hpF ⟨z, hzU⟩)
    rw [show (fmap ⟨z, hzU⟩ : ℂ) = Work.Bottcher.pMap c z / z ^ 4 from rfl] at h2
    exact h2
  obtain ⟨L', hL'c, hL'exp, hL't⟩ := exists_tendsto_zero_log_of_continuous_log c hc hL₀cont hL₀exp
  exact ⟨L', hL'c, hL'exp, hL't⟩

end

end Work.Bottcher.Contraction
