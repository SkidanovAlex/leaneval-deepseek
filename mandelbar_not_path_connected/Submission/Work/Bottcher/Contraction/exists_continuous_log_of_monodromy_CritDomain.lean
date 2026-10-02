import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.Bottcher.CritBasic
import Submission.Work.Bottcher.Contraction.LiftCoreDefs
import Submission.Work.Bottcher.Contraction.NormFactorRoots
import Submission.Work.Bottcher.Contraction.exists_continuous_log_of_monodromy
import Submission.Work.Bottcher.Contraction2.exists_analytic_log_normFactor_of_mem_mandelbar
import Submission.Work.Bottcher.Series.tendsto_bottcherPartial

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Bottcher.Contraction

noncomputable section

open Filter Function
open scoped Topology ComplexConjugate

open Work.Bottcher.LogLift

/-- **Normalisation at infinity of a continuous logarithm of the Böttcher factor on the critical
domain.**  Given a continuous logarithm `L` of `normFactor c` on `CritDomain c`, subtracting the
(on the far region `{critFarRadius c < ‖z‖}` constant, `2πiℤ`-valued) discrepancy with the
principal logarithm `Complex.log ∘ normFactor c` yields a continuous logarithm which agrees with
`Complex.log ∘ normFactor c` near infinity, hence tends to `0` there. -/
theorem exists_normalized_log_CritDomain (c : ℂ) {L : ℂ → ℂ}
    (hLc : ContinuousOn L (Work.Bottcher.CritDomain c))
    (hLexp : ∀ z : ℂ, z ∈ Work.Bottcher.CritDomain c →
      Complex.exp (L z) = Work.Bottcher.normFactor c z) :
    ∃ L' : ℂ → ℂ, ContinuousOn L' (Work.Bottcher.CritDomain c) ∧
      (∀ z : ℂ, z ∈ Work.Bottcher.CritDomain c →
        Complex.exp (L' z) = Work.Bottcher.normFactor c z) ∧
      Filter.Tendsto L' (Filter.cocompact ℂ) (nhds (0 : ℂ)) := by
  classical
  set R : ℝ := Work.Bottcher.CritBasic.critFarRadius c with hRdef
  have hRpos : 0 < R := Work.Bottcher.CritBasic.critFarRadius_pos c
  have hfar_sub : {z : ℂ | R < ‖z‖} ⊆ Work.Bottcher.CritDomain c := fun z hz =>
    Work.Bottcher.CritBasic.critFar_subset_CritDomain c hz
  set z₁ : ℂ := ((R + 1 : ℝ) : ℂ) with hz₁def
  have hz₁far : R < ‖z₁‖ := by
    rw [hz₁def, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    linarith
  have hz₁mem : z₁ ∈ Work.Bottcher.CritDomain c := hfar_sub hz₁far
  have hz₁ne : Work.Bottcher.normFactor c z₁ ≠ 0 :=
    Work.Bottcher.CritBasic.normFactor_ne_zero_of_mem_CritDomain hz₁mem
  have hexpd : Complex.exp (L z₁ - Complex.log (Work.Bottcher.normFactor c z₁)) = 1 := by
    rw [Complex.exp_sub, hLexp z₁ hz₁mem, Complex.exp_log hz₁ne, div_self hz₁ne]
  refine ⟨fun z => L z - (L z₁ - Complex.log (Work.Bottcher.normFactor c z₁)),
    hLc.sub continuousOn_const, ?_, ?_⟩
  · intro z hz
    rw [Complex.exp_sub, hLexp z hz, div_eq_mul_inv, hexpd, inv_one, mul_one]
  · have hslit : ∀ z ∈ {z : ℂ | R < ‖z‖}, Work.Bottcher.normFactor c z ∈ Complex.slitPlane := by
      intro z hz
      refine Work.Bottcher.Core.normFactor_mem_slitPlane c z ?_
      have hle : (1 + ‖c‖) ≤ R := by
        rw [hRdef, Work.Bottcher.CritBasic.critFarRadius]
        have h2 : (1 + ‖c‖) ≤ Work.Bottcher.escapeRadius c := by
          rw [Work.Bottcher.escapeRadius]; nlinarith [norm_nonneg c]
        exact h2.trans (le_max_left _ _)
      exact le_trans hle (le_of_lt hz)
    have hg : ∀ z ∈ {z : ℂ | R < ‖z‖},
        Complex.exp (L z - Complex.log (Work.Bottcher.normFactor c z)) = 1 := by
      intro z hz
      rw [Complex.exp_sub, Complex.exp_log (Complex.slitPlane_ne_zero (hslit z hz)),
        hLexp z (hfar_sub hz),
        div_self (Work.Bottcher.CritBasic.normFactor_ne_zero_of_mem_CritDomain (hfar_sub hz))]
    have hdiff : DifferentiableOn ℂ (Work.Bottcher.normFactor c) {z : ℂ | R < ‖z‖} :=
      (Work.Bottcher.CritBasic.differentiableOn_normFactor_CritDomain c).mono hfar_sub
    have hlog : DifferentiableOn ℂ (fun z => Complex.log (Work.Bottcher.normFactor c z))
        {z : ℂ | R < ‖z‖} := hdiff.clog hslit
    have hcont_g : ContinuousOn (fun z => L z - Complex.log (Work.Bottcher.normFactor c z))
        {z : ℂ | R < ‖z‖} :=
      (hLc.mono hfar_sub).sub hlog.continuousOn
    have hpre : IsPreconnected {z : ℂ | R < ‖z‖} :=
      (Work.Top.isPathConnected_norm_gt (le_of_lt hRpos)).isConnected.isPreconnected
    have hkey : ∀ z ∈ {z : ℂ | R < ‖z‖},
        L z - Complex.log (Work.Bottcher.normFactor c z)
          = L z₁ - Complex.log (Work.Bottcher.normFactor c z₁) := by
      intro z hz
      refine Complex.isCoveringMap_exp.constOn_of_comp hpre hcont_g ?_ hz hz₁far
      intro a ha a' ha'
      have h1 : Complex.exp (L a - Complex.log (Work.Bottcher.normFactor c a)) = 1 := hg a ha
      have h2 : Complex.exp (L a' - Complex.log (Work.Bottcher.normFactor c a')) = 1 := hg a' ha'
      apply Subtype.ext
      show Complex.exp (L a - Complex.log (Work.Bottcher.normFactor c a))
          = Complex.exp (L a' - Complex.log (Work.Bottcher.normFactor c a'))
      rw [h1, h2]
    have hev_far : ∀ᶠ z : ℂ in cocompact ℂ, R < ‖z‖ := by
      refine Filter.mem_of_superset
        (isCompact_closedBall (0 : ℂ) R).compl_mem_cocompact ?_
      intro z hz
      rw [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right] at hz
      exact not_le.mp hz
    have hev : (fun z => L z - (L z₁ - Complex.log (Work.Bottcher.normFactor c z₁)))
        =ᶠ[cocompact ℂ] (fun z => Complex.log (Work.Bottcher.normFactor c z)) := by
      filter_upwards [hev_far] with z hz
      have h := hkey z hz
      rw [← h]; ring
    exact (Work.Bottcher.Contraction2.tendsto_log_normFactor_cocompact c).congr' hev.symm

/--
Generalises `Work.Bottcher.Contraction.exists_continuous_log_of_monodromy` from the escape set of
a mandelbar parameter to the critical domain `CritDomain c = {G_c > G_c 0}` of an arbitrary
parameter, and includes the normalisation at infinity of the theorem `exists_normalized_log`
(inside `Work.Bottcher.Contraction2.exists_analytic_log_normFactor_of_mem_mandelbar`).

If every closed loop `γ` in `CritDomain c` has trivial monodromy (the lift change of the
normalised-factor path `t ↦ pMap c (γ t)/(γ t)^4` through the exponential covering vanishes), then
`pMap c z / z^4` has a continuous logarithm `L` on `CritDomain c` vanishing at infinity:
`exp (L z) = normFactor c z` there and `L → 0` at `z → ∞`.

* Existence: `CritDomain c` is open, nonempty and preconnected (`Work.Bottcher.CritBasic`), the
  factor is continuous and nowhere zero there (`normFactor_ne_zero_of_mem_CritDomain`), so the
  covering-space lifting criterion
  (`Complex.isCoveringMap_exp.isLocalHomeomorph.existsUnique_continuousMap_lifts`) produces a
  global continuous lift.  Copy `exists_continuous_log_of_monodromy` and replace `EscapeSet c` by
  `CritDomain c` (`0 < green c z` becomes `z ∈ CritDomain c`, and `green_zero_of_mem_mandelbar` /
  `normFactor_ne_zero_of_mem_mandelbar` become `CritBasic.zero_notMem_CritDomain` /
  `CritBasic.normFactor_ne_zero_of_mem_CritDomain`).
* Normalisation at infinity: copy `exists_normalized_log`.  Note the far region must be
  `{z | Work.Bottcher.CritBasic.critFarRadius c < ‖z‖}`, *not* `{z | escapeRadius c < ‖z‖}`
  (which need not be contained in `CritDomain c` when `c ∉ M*`):
  `CritBasic.critFar_subset_CritDomain` puts it inside `CritDomain c`, it is cocompact and
  preconnected, and on it the difference `L z - Complex.log (normFactor c z)` is continuous with
  values in `2πiℤ`, hence constant; subtracting it makes `L'` agree with
  `Complex.log ∘ normFactor` at infinity, where `normFactor → 1`.
-/
theorem exists_continuous_log_of_monodromy_CritDomain (c : ℂ)
    (hmono : ∀ (γ : C(unitInterval, ℂ)) (hloop : γ 1 = γ 0)
      (hγ : ∀ t, γ t ∈ Work.Bottcher.CritDomain c) (hγne : ∀ t, γ t ≠ 0)
      (h : ∀ t, Work.Bottcher.Contraction.normFactorPath c γ hγne t ≠ 0),
      Work.Bottcher.Contraction.liftChange
        (Work.Bottcher.Contraction.normFactorPath c γ hγne) h = 0) :
    ∃ L : ℂ → ℂ, ContinuousOn L (Work.Bottcher.CritDomain c) ∧
      (∀ z : ℂ, z ∈ Work.Bottcher.CritDomain c →
        Complex.exp (L z) = Work.Bottcher.normFactor c z) ∧
      Filter.Tendsto L (Filter.cocompact ℂ) (nhds (0 : ℂ)) := by
  classical
  have hne0 : ∀ z : ℂ, z ∈ Work.Bottcher.CritDomain c → z ≠ 0 :=
    fun z hz hz0 => Work.Bottcher.CritBasic.zero_notMem_CritDomain c (hz0 ▸ hz)
  have hnorm_ne : ∀ z : ℂ, z ∈ Work.Bottcher.CritDomain c →
      Work.Bottcher.normFactor c z ≠ 0 :=
    fun z hz => Work.Bottcher.CritBasic.normFactor_ne_zero_of_mem_CritDomain hz
  obtain ⟨z₁, hz₁mem⟩ := Work.Bottcher.CritBasic.nonempty_CritDomain c
  let U : Set ℂ := Work.Bottcher.CritDomain c
  have hUo : IsOpen U := Work.Bottcher.CritBasic.isOpen_CritDomain c
  have hUc : IsPreconnected U := Work.Bottcher.CritBasic.isPreconnected_CritDomain c
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
    have hγc_mem : ∀ s : unitInterval, γc s ∈ Work.Bottcher.CritDomain c := fun s => (γ s).2
    have hγ'c_mem : ∀ s : unitInterval, γ'c s ∈ Work.Bottcher.CritDomain c := fun s => (γ' s).2
    have hγcne : ∀ t, γc t ≠ 0 := fun t => hne0 (γc t) (hγc_mem t)
    have hγ'cne : ∀ t, γ'c t ≠ 0 := fun t => hne0 (γ'c t) (hγ'c_mem t)
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
    have hgreen : ∀ t, loopC t ∈ Work.Bottcher.CritDomain c := by
      intro t
      change concatC γc (revC γ'c) hconv t ∈ Work.Bottcher.CritDomain c
      by_cases ht : (t : ℝ) ≤ 1/2
      · rw [concatC_apply_le _ _ _ _ ht]; exact hγc_mem _
      · rw [concatC_apply_gt _ _ _ _ ht, revC_apply]; exact hγ'c_mem _
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
      exact hnorm_ne (γc t) (hγc_mem t)
    have hδ'ne : ∀ t, δ' t ≠ 0 := fun t => by
      change Work.Bottcher.normFactor c (γ'c t) ≠ 0
      exact hnorm_ne (γ'c t) (hγ'c_mem t)
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
  have hL₀exp : ∀ z : ℂ, z ∈ Work.Bottcher.CritDomain c →
      Complex.exp (L₀ z) = Work.Bottcher.normFactor c z := by
    intro z hz
    have hzU : z ∈ U := hz
    change Complex.exp (if h : z ∈ U then F ⟨z, h⟩ else 0)
      = Work.Bottcher.normFactor c z
    rw [dif_pos hzU]
    have h2 := congrArg Subtype.val (congrFun hpF ⟨z, hzU⟩)
    rw [show (fmap ⟨z, hzU⟩ : ℂ) = Work.Bottcher.normFactor c z from rfl] at h2
    exact h2
  obtain ⟨L', hL'c, hL'exp, hL't⟩ := exists_normalized_log_CritDomain c hL₀cont hL₀exp
  exact ⟨L', hL'c, hL'exp, hL't⟩

end

end Work.Bottcher.Contraction
