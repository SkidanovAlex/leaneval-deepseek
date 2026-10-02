import Mathlib
import Submission.Work.ThomBordism.chartModelClassDefs
import Submission.Work.ThomBordism.ambientLocalDefs2
import Submission.Work.ThomBordism.stdModelGen_pm_stdThomGen
import Submission.Work.Serre.isIso_relCohMap_excision_of_interior
import Submission.Work.ThomBordism.localChartClass_ne_zero
import Submission.Work.ThomBordism.localisation_injective_zeroSection

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.ThomBordism

noncomputable section

open CategoryTheory

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-! ## The pair condition of the local chart map -/

/-- The capped chart map is nonzero away from the base zero-section point: the only point of `ν`
mapped to `0` by `p ↦ chartAffine E x (cap E ε p)` is `0_x` itself.  (Copy of the corresponding
result in an area file that carries an unrelated `sorry`, kept here for an axiom-clean build.) -/
theorem chartAffine_cap_ne_zero_of_ne_zeroSection'
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (x : V.pt) {p : Work.Tubular.NormalTotal E}
    (hp : p ≠ Work.Tubular.zeroSectionNormal E x) :
    Work.ThomBordism.chartAffine E x (Work.ThomBordism.cap E ε p) ≠ 0 := by
  intro h0
  have htube : Work.Tubular.tubeMap E (Work.ThomBordism.cap E ε p) = E.e x := by
    have h := congrArg (fun z : Work.Tubular.Euc (8 + k) => z + E.e x) h0
    rw [Work.ThomBordism.chartAffine_apply] at h
    rw [sub_add_cancel] at h
    simpa [Work.Tubular.tubeMap] using h
  have hzero : Work.Tubular.tubeMap E (Work.Tubular.zeroSectionNormal E x) = E.e x :=
    Work.ThomBordism.tubeMap_zeroSectionNormal E x
  have hle : Work.Tubular.normalNorm E (Work.ThomBordism.cap E ε p) ≤ ε :=
    Work.ThomBordism.cap_mem_disc E C.eps_pos.le p
  have hnorm0 : Work.Tubular.normalNorm E (Work.Tubular.zeroSectionNormal E x) = 0 := by
    rw [Work.Tubular.zeroSectionNormal]; simp
  have heq : Work.ThomBordism.cap E ε p = Work.Tubular.zeroSectionNormal E x := by
    have h1 := congrArg C.inv (htube.trans hzero.symm)
    rw [C.inv_tubeMap _ hle, C.inv_tubeMap _ (by rw [hnorm0]; exact C.eps_pos.le)] at h1
    exact h1
  have hproj : (p : V.pt × Work.Tubular.Euc (8 + k)).1 = x := by
    have h := congrArg (fun q : Work.Tubular.NormalTotal E =>
      (q : V.pt × Work.Tubular.Euc (8 + k)).1) heq
    unfold Work.ThomBordism.cap at h
    rw [Work.ThomBordism.radialRescale_proj] at h
    simpa using h
  have hvec : (p : V.pt × Work.Tubular.Euc (8 + k)).2 = 0 := by
    have h := congrArg (fun q : Work.Tubular.NormalTotal E =>
      (q : V.pt × Work.Tubular.Euc (8 + k)).2) heq
    unfold Work.ThomBordism.cap at h
    rw [Work.ThomBordism.radialRescale_coe] at h
    have hzero' : (Work.Tubular.zeroSectionNormal E x :
        V.pt × Work.Tubular.Euc (8 + k)).2 = 0 := by
      rw [Work.Tubular.zeroSectionNormal_apply]
    rw [hzero'] at h
    have hpos : 0 < Work.ThomBordism.capCoeff ε (Work.Tubular.normalNorm E p) :=
      Work.ThomBordism.capCoeff_pos C.eps_pos _ (Work.Tubular.normalNorm_nonneg E p)
    exact (smul_eq_zero.mp h).resolve_left (ne_of_gt hpos)
  refine hp (Subtype.ext ?_)
  rw [Work.Tubular.zeroSectionNormal_apply]
  exact Prod.ext hproj hvec

/-! ## The standard model generator is nonzero -/

/-- **The standard model generator of `H^{8+k}(ℝ^{8+k}, ℝ^{8+k}∖0)` is nonzero.** -/
theorem stdModelGen_ne_zero (k : ℕ) (hk : 1 ≤ k) : stdModelGen (8 + k) ≠ 0 := by
  intro h0
  have htop : (⊤ : Submodule ℤ (Work.Thom.RelCoh ℤ (8 + k) (Work.Tubular.Euc (8 + k))
      ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))))) = ⊥ := by
    rw [← stdModelGen_span (8 + k) (by omega), h0, Submodule.span_singleton_eq_bot]
  haveI : Subsingleton (Work.Thom.RelCoh ℤ (8 + k) (Work.Tubular.Euc (8 + k))
      ({0}ᶜ : Set (Work.Tubular.Euc (8 + k)))) :=
    ⟨fun a b => by
      have ha : a ∈ (⊥ : Submodule ℤ _) := by rw [← htop]; exact Submodule.mem_top
      have hb : b ∈ (⊥ : Submodule ℤ _) := by rw [← htop]; exact Submodule.mem_top
      rw [Submodule.mem_bot] at ha hb
      rw [ha, hb]⟩
  obtain ⟨e⟩ := Work.Thom.relCohomology_euclidean_punctured (8 + k) (by omega) (8 + k)
  rw [if_pos rfl] at e
  have h1 : (Pi.single (0 : Fin 1) (1 : ℤ) : Fin 1 → ℤ) ≠ 0 := by
    intro hh
    have := congrFun hh 0
    simpa using this
  let L : Work.Thom.RelCoh ℤ (8 + k) (Work.Tubular.Euc (8 + k))
      ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) ≃ₗ[ℤ] (Fin 1 → ℤ) := e.toLinearEquiv
  have key : (0 : Work.Thom.RelCoh ℤ (8 + k) (Work.Tubular.Euc (8 + k))
      ({0}ᶜ : Set (Work.Tubular.Euc (8 + k)))) = L.symm (Pi.single (0 : Fin 1) (1 : ℤ)) :=
    Subsingleton.elim _ _
  have h2 : (Pi.single (0 : Fin 1) (1 : ℤ) : Fin 1 → ℤ) = 0 := by
    have h3 : L (0 : Work.Thom.RelCoh ℤ (8 + k) (Work.Tubular.Euc (8 + k))
        ({0}ᶜ : Set (Work.Tubular.Euc (8 + k)))) = L (L.symm (Pi.single (0 : Fin 1) (1 : ℤ))) := by
      rw [key]
    rw [map_zero, LinearEquiv.apply_symm_apply] at h3
    exact h3.symm
  exact h1 h2





/-! ## The assembly -/

/-- **The ambient chart model class is nonzero.**  On the *local* pair at the zero-section point
`0_x` the capped ambient chart map `p ↦ chartAffine E x (cap E ε p)` is a homeomorphism of pairs onto
a neighbourhood of `0`, so the pull-back of the standard generator is nonzero
(`Work.ThomBordism.localChartClass_ne_zero`); the cohomological localisation
`H^{8+k}(ν,ν∖{0_x}) → H^{8+k}(ν,ν∖0)` is injective
(`Work.ThomBordism.localisation_injective_zeroSection`), and
`chartModelClass` is the image of that local class under it. -/
theorem chartModelClass_ne_zero {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt] {k : ℕ}
    (hk : 1 ≤ k)
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (x : V.pt)
    (hcont : Continuous fun p : Work.Tubular.NormalTotal E =>
      Work.ThomBordism.chartAffine E x (Work.ThomBordism.cap E ε p)) :
    Work.ThomBordism.chartModelClass E C x hcont ≠ 0 := by
  classical
  let Θ : C(Work.Tubular.NormalTotal E, Work.Tubular.Euc (8 + k)) :=
    ⟨fun p => Work.ThomBordism.chartAffine E x (Work.ThomBordism.cap E ε p), hcont⟩
  have hsub : Work.Tubular.normalNonzero E ⊆
      ({p : Work.Tubular.NormalTotal E | p ≠ Work.Tubular.zeroSectionNormal E x}) := by
    intro p hp
    intro h
    refine (Work.Tubular.mem_normalNonzero (E := E)).mp hp ?_
    have h2 : p = Work.Tubular.zeroSectionNormal E x := by simpa using h
    rw [h2]; simp
  have hcap : ∀ p : Work.Tubular.NormalTotal E, p ≠ Work.Tubular.zeroSectionNormal E x →
      Work.ThomBordism.chartAffine E x (Work.ThomBordism.cap E ε p) ≠ 0 :=
    fun p hp => chartAffine_cap_ne_zero_of_ne_zeroSection' E C x hp
  -- the class is nonzero on the local pair (delegated geometric input)
  have hloc : (Work.Thom.relCohMap Θ
      ({p : Work.Tubular.NormalTotal E | p ≠ Work.Tubular.zeroSectionNormal E x})
      ({0}ᶜ : Set (Work.Tubular.Euc (8 + k)))
      (fun p hp => hcap p hp) ℤ (8 + k)).hom (stdModelGen (8 + k)) ≠ 0 := by
    have h := localChartClass_ne_zero hk E C x hcont hcap
    simpa only [Θ] using h
  -- the localisation is injective (delegated)
  have hinj : Function.Injective ((Work.Thom.relCohMap (ContinuousMap.id (Work.Tubular.NormalTotal E))
      (Work.Tubular.normalNonzero E)
      ({p : Work.Tubular.NormalTotal E | p ≠ Work.Tubular.zeroSectionNormal E x})
      hsub ℤ (8 + k)).hom) := localisation_injective_zeroSection hk E x
  -- functoriality: the chart model class is the restriction of the local class
  have hcomp2 : ∀ p ∈ Work.Tubular.normalNonzero E,
      Θ p ∈ ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) := fun p hp => hcap p (hsub hp)
  have hrel : Work.ThomBordism.chartModelClass E C x hcont =
      (Work.Thom.relCohMap (ContinuousMap.id (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E)
        ({p : Work.Tubular.NormalTotal E | p ≠ Work.Tubular.zeroSectionNormal E x})
        hsub ℤ (8 + k)).hom
      ((Work.Thom.relCohMap Θ
        ({p : Work.Tubular.NormalTotal E | p ≠ Work.Tubular.zeroSectionNormal E x})
        ({0}ᶜ : Set (Work.Tubular.Euc (8 + k)))
        (fun p hp => hcap p hp) ℤ (8 + k)).hom (stdModelGen (8 + k))) := by
    have h2 := Work.Thom.relCohMap_compA_apply
      (Work.Tubular.normalNonzero E)
      ({p : Work.Tubular.NormalTotal E | p ≠ Work.Tubular.zeroSectionNormal E x})
      ({0}ᶜ : Set (Work.Tubular.Euc (8 + k)))
      (ContinuousMap.id (Work.Tubular.NormalTotal E)) Θ hsub (fun p hp => hcap p hp)
      hcomp2 ℤ (8 + k) (stdModelGen (8 + k))
    have h1 : (Work.Thom.relCohMap (Θ.comp (ContinuousMap.id (Work.Tubular.NormalTotal E)))
          (Work.Tubular.normalNonzero E) ({0}ᶜ : Set (Work.Tubular.Euc (8 + k)))
          hcomp2 ℤ (8 + k)).hom (stdModelGen (8 + k))
        = (Work.Thom.relCohMap Θ (Work.Tubular.normalNonzero E)
          ({0}ᶜ : Set (Work.Tubular.Euc (8 + k)))
          hcomp2 ℤ (8 + k)).hom (stdModelGen (8 + k)) :=
      LinearMap.congr_fun
        (congrArg (fun φ => ModuleCat.Hom.hom φ)
          (Work.Thom.relCohMap_congrA (Work.Tubular.normalNonzero E)
            ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) (ContinuousMap.comp_id Θ)
            hcomp2 hcomp2 ℤ (8 + k)))
        (stdModelGen (8 + k))
    rw [chartModelClass]
    rw [h2, h1]
  rw [hrel]
  exact fun h0 => hloc (hinj (by rw [h0, map_zero]))


end

end Work.ThomBordism