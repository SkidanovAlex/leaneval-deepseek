import Mathlib
import Submission.Work.Bottcher.Contraction.LiftCoreDefs
import Submission.Work.Bottcher.Contraction2.liftPath_endpoint_eq_of_loop
import Submission.Work.Escape.differentiableOn_of_continuousOn_exp_eq

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Bottcher.Contraction2

open scoped Topology

noncomputable section

/-- `Path.trans` evaluated at the endpoint `1`. -/
private theorem path_trans_apply_one {X : Type*} [TopologicalSpace X] {x y z : X} (γ : Path x y)
    (γ' : Path y z) : (γ.trans γ') 1 = γ' 1 := by
  rw [Path.trans_apply]
  rw [dite_eq_right (by norm_num : ¬ (((1 : unitInterval) : ℝ)) ≤ 1 / 2)]
  congr 1
  ext
  norm_num

variable {U : Set ℂ}

/-- A nonvanishing analytic function on `U` gives a continuous map `U → ℂ*`. -/
private def toUnits (f : ℂ → ℂ) (hne : ∀ z ∈ U, f z ≠ 0) (hf : AnalyticOnNhd ℂ f U) :
    C(U, {z : ℂ // z ≠ 0}) :=
  ⟨fun x => ⟨f x, hne x x.2⟩, (hf.continuousOn.domRestrict).subtype_mk fun x => hne x x.2⟩

private theorem toUnits_apply (f : ℂ → ℂ) (hne : ∀ z ∈ U, f z ≠ 0) (hf : AnalyticOnNhd ℂ f U)
    (x : U) : (toUnits f hne hf x : ℂ) = f x := rfl

/-- The exponential covering map, as a map `ℂ → ℂ*`. -/
private def expCover : ℂ → {z : ℂ // z ≠ 0} := fun z => ⟨Complex.exp z, Complex.exp_ne_zero z⟩

private theorem expCover_apply (z : ℂ) : (expCover z : ℂ) = Complex.exp z := rfl

private theorem isCoveringMap_expCover : IsCoveringMap expCover := Complex.isCoveringMap_exp

theorem exists_analyticOnNhd_exp_eq_of_liftChange_eq_zero
    {U : Set ℂ} (hUo : IsOpen U) (hUn : U.Nonempty) (hUpc : IsPreconnected U)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U) (hne : ∀ z ∈ U, f z ≠ 0)
    (hmono : ∀ (γ : C(unitInterval, ℂ)) (hγ : ∀ t, γ t ∈ U), γ 0 = γ 1 →
      Work.Bottcher.Contraction.liftChange
        ⟨fun t => f (γ t), hf.continuousOn.comp_continuous γ.continuous hγ⟩
        (fun t => hne (γ t) (hγ t)) = 0) :
    ∃ L : ℂ → ℂ, AnalyticOnNhd ℂ L U ∧ ∀ z ∈ U, Complex.exp (L z) = f z := by
  classical
  haveI : LocallyPathConnectedSpace U := hUo.locallyPathConnectedSpace
  haveI : PathConnectedSpace U :=
    isPathConnected_iff_pathConnectedSpace.mp ((hUo.isConnected_iff_isPathConnected).mp ⟨hUn, hUpc⟩)
  obtain ⟨z0, hz0⟩ := hUn
  let F : C(U, {z : ℂ // z ≠ 0}) := toUnits f hne hf
  let e0 : ℂ := Complex.log (f z0)
  have he0 : Complex.exp e0 = f z0 := Complex.exp_log (hne z0 hz0)
  have heSub : F ⟨z0, hz0⟩ = expCover e0 := Subtype.ext he0.symm
  have hEx : ∀ γ : C(unitInterval, U), γ 0 = ⟨z0, hz0⟩ →
      ∃ Γ : C(unitInterval, ℂ), Γ 0 = e0 ∧ expCover ∘ ⇑Γ = ⇑(F.comp γ) := by
    intro γ hγ
    refine ⟨isCoveringMap_expCover.liftPath (F.comp γ) e0 ?_, ?_, ?_⟩
    · rw [show (F.comp γ) 0 = F (γ 0) from rfl, hγ]
      exact heSub
    · exact isCoveringMap_expCover.liftPath_zero _ _ _
    · exact isCoveringMap_expCover.liftPath_lifts _ _ _
  have hUniq : ∀ (γ γ' : C(unitInterval, U)) (Γ Γ' : C(unitInterval, ℂ)),
      γ 0 = ⟨z0, hz0⟩ → γ' 0 = ⟨z0, hz0⟩ → Γ 0 = e0 → Γ' 0 = e0 →
      expCover ∘ ⇑Γ = ⇑(F.comp γ) → expCover ∘ ⇑Γ' = ⇑(F.comp γ') →
      γ 1 = γ' 1 → Γ 1 = Γ' 1 := by
    intro γ γ' Γ Γ' hγ0 hγ'0 hΓ0 hΓ'0 hΓl hΓ'l hγγ'
    -- the paths in `U`
    let γp : Path ⟨z0, hz0⟩ (γ 1) := ⟨γ, hγ0, rfl⟩
    let γp' : Path ⟨z0, hz0⟩ (γ 1) := ⟨γ', hγ'0, hγγ'.symm⟩
    let σU := γp.trans γp'.symm
    -- the ℂ-valued loop
    let γℂ : C(unitInterval, ℂ) := ⟨fun t => ((σU t : U) : ℂ), σU.continuous.subtype_val⟩
    have hγℂmem : ∀ t, γℂ t ∈ U := fun t => (σU t).2
    have hloopℂ : γℂ 0 = γℂ 1 := by
      have h : σU 0 = σU 1 := (Path.source σU).trans (Path.target σU).symm
      exact congrArg (fun x : U => (x : ℂ)) h
    let δ : C(unitInterval, ℂ) :=
      ⟨fun t => f (γℂ t), hf.continuousOn.comp_continuous γℂ.continuous hγℂmem⟩
    let hδne : ∀ t, δ t ≠ 0 := fun t => hne (γℂ t) (hγℂmem t)
    have hδmono : Work.Bottcher.Contraction.liftChange δ hδne = 0 := hmono γℂ hγℂmem hloopℂ
    have hδ0 : δ 0 = f z0 := by
      have h : γℂ 0 = ((⟨z0, hz0⟩ : U) : ℂ) := congrArg (fun x : U => (x : ℂ)) (Path.source σU)
      show f (γℂ 0) = f z0
      rw [h]
    have he : Complex.exp e0 = δ 0 := by rw [hδ0]; exact he0
    have hlift1 : (Work.Bottcher.Contraction.liftOf δ hδne e0 he) 1 = e0 := by
      have h := Work.Bottcher.Contraction.liftChange_eq_liftOf δ hδne e0 he
      rw [hδmono] at h
      exact sub_eq_zero.mp h.symm
    -- the paths in `ℂ*`
    let pγ : Path (F ⟨z0, hz0⟩) (F (γ 1)) := γp.map F.continuous
    let pγ' : Path (F ⟨z0, hz0⟩) (F (γ 1)) := γp'.map F.continuous
    let W : Path (F ⟨z0, hz0⟩) (F ⟨z0, hz0⟩) := pγ.trans pγ'.symm
    -- pointwise identification of the two loops
    have hcm : (Work.Bottcher.Contraction.pathSubtype δ hδne)
        = (W : C(unitInterval, {z : ℂ // z ≠ 0})) := by
      have h1 : (Work.Bottcher.Contraction.pathSubtype δ hδne)
          = ((σU.map F.continuous) : C(unitInterval, {z : ℂ // z ≠ 0})) := by
        ext t
        rfl
      have h2 : σU.map F.continuous = W := by
        rw [show σU = γp.trans γp'.symm from rfl, Path.map_trans]
        rfl
      rw [h1, h2]
    have hΓlifts : expCover ∘ ⇑(Work.Bottcher.Contraction.liftOf δ hδne e0 he) = ⇑W := by
      funext t
      rw [Function.comp_apply]
      apply Subtype.ext
      rw [expCover_apply, Work.Bottcher.Contraction.exp_liftOf]
      have h : (Work.Bottcher.Contraction.pathSubtype δ hδne t : ℂ) = (W t : ℂ) := by
        rw [hcm]
        rfl
      rw [Work.Bottcher.Contraction.pathSubtype_apply] at h
      exact h
    have hloopW : isCoveringMap_expCover.liftPath (W : C(unitInterval, {z : ℂ // z ≠ 0})) e0
        ((Path.source W).trans heSub) 1 = e0 := by
      have key : Work.Bottcher.Contraction.liftOf δ hδne e0 he
          = isCoveringMap_expCover.liftPath (W : C(unitInterval, {z : ℂ // z ≠ 0})) e0
              ((Path.source W).trans heSub) :=
        (isCoveringMap_expCover.eq_liftPath_iff' _).mpr
          ⟨hΓlifts, by rw [Work.Bottcher.Contraction.liftOf_apply_zero]⟩
      rw [← key]
      exact hlift1
    have hΓ1 : Γ 1 = isCoveringMap_expCover.liftPath (↑pγ) e0
        ((Path.source pγ).trans heSub) 1 := by
      have h : Γ = isCoveringMap_expCover.liftPath (↑pγ) e0 ((Path.source pγ).trans heSub) :=
        (isCoveringMap_expCover.eq_liftPath_iff' (Γ := Γ) ((Path.source pγ).trans heSub)).mpr
          ⟨hΓl, hΓ0⟩
      exact congrArg (fun g : C(unitInterval, ℂ) => g 1) h
    have hΓ'1 : Γ' 1 = isCoveringMap_expCover.liftPath (↑pγ') e0
        ((Path.source pγ').trans heSub) 1 := by
      have h : Γ' = isCoveringMap_expCover.liftPath (↑pγ') e0 ((Path.source pγ').trans heSub) :=
        (isCoveringMap_expCover.eq_liftPath_iff' (Γ := Γ') ((Path.source pγ').trans heSub)).mpr
          ⟨hΓ'l, hΓ'0⟩
      exact congrArg (fun g : C(unitInterval, ℂ) => g 1) h
    rw [hΓ1, hΓ'1]
    exact liftPath_endpoint_eq_of_loop pγ pγ' e0 heSub hloopW
  obtain ⟨F', ⟨hF'0, hF'lift⟩, -⟩ :=
    (isCoveringMap_expCover.isLocalHomeomorph).existsUnique_continuousMap_lifts F ⟨z0, hz0⟩ e0
      heSub.symm hEx hUniq
  have hexpF : ∀ x : U, Complex.exp (F' x) = f x := by
    intro x
    have h := congrArg Subtype.val (congrFun hF'lift x)
    simpa [F, expCover, toUnits_apply] using h
  refine ⟨fun z => if h : z ∈ U then F' ⟨z, h⟩ else 0, ?_, ?_⟩
  · have hJL : ∀ z ∈ U, Complex.exp ((fun z => if h : z ∈ U then F' ⟨z, h⟩ else 0) z) = f z := by
      intro z hz
      simpa only [dif_pos hz] using hexpF ⟨z, hz⟩
    have hcont : ContinuousOn (fun z => if h : z ∈ U then F' ⟨z, h⟩ else 0) U := by
      rw [continuousOn_iff_continuous_domRestrict]
      have hz : U.domRestrict (fun z => if h : z ∈ U then F' ⟨z, h⟩ else 0) = ⇑F' := by
        funext x
        simp only [Set.domRestrict_apply]
        exact dif_pos x.2
      rw [hz]
      exact F'.continuous
    exact ((Work.Escape.differentiableOn_of_continuousOn_exp_eq hUo hcont hf.differentiableOn hne
      hJL).analyticOnNhd hUo)
  · intro z hz
    simpa only [dif_pos hz] using hexpF ⟨z, hz⟩

end

end Work.Bottcher.Contraction2
