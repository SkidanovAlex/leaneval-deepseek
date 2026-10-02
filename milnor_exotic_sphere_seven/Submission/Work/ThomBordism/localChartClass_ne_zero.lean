import Mathlib
import Submission.Work.ThomBordism.chartModelClassDefs
import Submission.Work.ThomBordism.ambientLocalDefs2
import Submission.Work.ThomBordism.localChartBallDefs
import Submission.Work.Thom.ATools
import Submission.Work.Serre.isIso_relCohMap_excision_of_interior
import Submission.Work.ThomBordism.stdModelGen_pm_stdThomGen

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

namespace Work.ThomBordism

noncomputable section

open CategoryTheory

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-- **The capped chart map is a homeomorphism of pairs on the open disc bundle.**
On the open `ε`-disc bundle `chartOpenBall E ε = {p | normalNorm E p < ε}` the capping is the
identity, so `p ↦ chartAffine E x (cap E ε p)` is the tubular map translated by `-E.e x`; its image
is the open neighbourhood `chartNbhd E C x = {y | y + E.e x ∈ C.openTube}` of `0`, with continuous
inverse `y ↦ C.inv (y + E.e x)`.  The only point of the disc bundle sent to `0` is the zero-section
point `0_x`, so this is an isomorphism of the pairs
`(chartOpenBall E ε, chartOpenBall E ε ∖ {0_x})` and `(chartNbhd E C x, chartNbhd E C x ∖ {0})`. -/
theorem localChartClass_pairHomeo {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (x : V.pt)
    (hcont : Continuous fun p : Work.Tubular.NormalTotal E =>
      Work.ThomBordism.chartAffine E x (Work.ThomBordism.cap E ε p))
    (hcap : ∀ p : Work.Tubular.NormalTotal E, p ≠ Work.Tubular.zeroSectionNormal E x →
      Work.ThomBordism.chartAffine E x (Work.ThomBordism.cap E ε p) ≠ 0) :
    ∃ (Φ : ↥(Work.ThomBordism.chartOpenBall E ε) ≃ₜ ↥(Work.ThomBordism.chartNbhd E C x)),
      IsOpen (Work.ThomBordism.chartNbhd E C x) ∧
      (0 : Work.Tubular.Euc (8 + k)) ∈ Work.ThomBordism.chartNbhd E C x ∧
      (∀ p : ↥(Work.ThomBordism.chartOpenBall E ε),
        (Φ p : Work.Tubular.Euc (8 + k))
          = Work.ThomBordism.chartAffine E x (Work.ThomBordism.cap E ε
              (p : Work.Tubular.NormalTotal E))) ∧
      (∀ p : ↥(Work.ThomBordism.chartOpenBall E ε),
        ((p : Work.Tubular.NormalTotal E) ≠ Work.Tubular.zeroSectionNormal E x)
          ↔ ((Φ p : Work.Tubular.Euc (8 + k)) ≠ 0)) := by
  have htube : ∀ q : Work.Tubular.NormalTotal E,
      Work.ThomBordism.chartAffine E x q + E.e x = Work.Tubular.tubeMap E q := by
    intro q
    rw [Work.ThomBordism.chartAffine_apply]
    simp only [Work.Tubular.tubeMap]
    abel
  have hcapfix : Work.ThomBordism.cap E ε (Work.Tubular.zeroSectionNormal E x)
      = Work.Tubular.zeroSectionNormal E x := by
    refine Work.ThomBordism.cap_eq_self_of_le E C.eps_pos.le ?_
    rw [Work.Tubular.normalNorm, Work.Tubular.zeroSectionNormal_apply]
    simpa using C.eps_pos.le
  have hFmem : ∀ p : ↥(chartOpenBall E ε),
      Work.ThomBordism.chartAffine E x (Work.ThomBordism.cap E ε
          (p : Work.Tubular.NormalTotal E)) ∈ chartNbhd E C x := by
    intro p
    rw [mem_chartNbhd, htube]
    have hp : Work.Tubular.normalNorm E (p : Work.Tubular.NormalTotal E) < ε := p.2
    rw [Work.ThomBordism.cap_eq_self_of_le E C.eps_pos.le (le_of_lt hp)]
    exact ⟨(p : Work.Tubular.NormalTotal E), hp, rfl⟩
  have hGmem : ∀ y : ↥(chartNbhd E C x),
      C.inv ((y : Work.Tubular.Euc (8 + k)) + E.e x) ∈ chartOpenBall E ε := by
    intro y
    rw [mem_chartOpenBall]
    have h := y.2
    rw [mem_chartNbhd] at h
    rw [C.openTube_eq] at h
    exact h.2
  let Φ : ↥(chartOpenBall E ε) ≃ₜ ↥(chartNbhd E C x) :=
    { toFun := fun p => ⟨Work.ThomBordism.chartAffine E x (Work.ThomBordism.cap E ε
        (p : Work.Tubular.NormalTotal E)), hFmem p⟩
      invFun := fun y => ⟨C.inv ((y : Work.Tubular.Euc (8 + k)) + E.e x), hGmem y⟩
      left_inv := fun p => by
        apply Subtype.ext
        show C.inv (Work.ThomBordism.chartAffine E x (Work.ThomBordism.cap E ε
          (p : Work.Tubular.NormalTotal E)) + E.e x) = (p : Work.Tubular.NormalTotal E)
        rw [htube, Work.ThomBordism.cap_eq_self_of_le E C.eps_pos.le (le_of_lt p.2)]
        exact C.inv_tubeMap (p : Work.Tubular.NormalTotal E) (le_of_lt p.2)
      right_inv := fun y => by
        apply Subtype.ext
        show Work.ThomBordism.chartAffine E x (Work.ThomBordism.cap E ε
          (C.inv ((y : Work.Tubular.Euc (8 + k)) + E.e x))) = (y : Work.Tubular.Euc (8 + k))
        rw [Work.ThomBordism.cap_inv E C (C.openTube_subset_U y.2),
          Work.ThomBordism.chartAffine_inv E C x (C.openTube_subset_U y.2)]
        abel
      continuous_toFun := Continuous.subtype_mk (hcont.comp continuous_subtype_val) hFmem
      continuous_invFun := Continuous.subtype_mk
        (C.continuousOn_inv.comp_continuous
          (continuous_subtype_val.add continuous_const)
          (fun y => C.openTube_subset_U y.2)) hGmem }
  refine ⟨Φ, ?_, ?_, ?_, ?_⟩
  · exact C.openTube_isOpen.preimage (continuous_id.add continuous_const)
  · rw [mem_chartNbhd]
    simpa using C.mem_openTube x
  · intro p
    rfl
  · intro p
    constructor
    · intro hp
      exact hcap (p : Work.Tubular.NormalTotal E) hp
    · intro hp
      by_contra hq
      have hq' : (p : Work.Tubular.NormalTotal E) = Work.Tubular.zeroSectionNormal E x := hq
      apply hp
      show Work.ThomBordism.chartAffine E x (Work.ThomBordism.cap E ε
        (p : Work.Tubular.NormalTotal E)) = 0
      rw [hq', hcapfix, Work.ThomBordism.chartAffine_zeroSection]

/-- **The standard model generator of `H^{8+k}(ℝ^{8+k}, ℝ^{8+k}∖0)` is nonzero.** -/
theorem localChartClass_stdModelGen_ne_zero (k : ℕ) (hk : 1 ≤ k) :
    stdModelGen (8 + k) ≠ 0 := by
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

/-- **The capped ambient chart class is nonzero on the *local* pair at the zero-section point.**
`Θ := fun p => chartAffine E x (cap E ε p)` is the capped ambient chart map `ν → ℝ^{8+k}`; it is a
map of pairs `(ν, ν∖{0_x}) → (ℝ^{8+k}, {0}ᶜ)` (the hypothesis `hcap` is
`chartAffine_cap_ne_zero_of_ne_zeroSection`: the only point of `ν` at which `Θ` vanishes is
`0_x = zeroSectionNormal E x`), and this result says that the pull-back of the standard generator
`stdModelGen (8+k)` along it is *nonzero* in the local relative group `H^{8+k}(ν, ν∖{0_x}) ≅ ℤ`.

Route (all ingredients are on disk).  On the open disc bundle `U := {p | normalNorm E p < ε}` the
capping is the identity (`cap_eq_self_of_le`) and `Θ` is the homeomorphism `p ↦ tubeMap E p - E.e x`
with inverse `y ↦ C.inv (y + E.e x)` (`chartAffine_inv`, `TubeChart.tubeMap_inv`), which maps
`U ∖ {0_x}` onto `V ∖ {0}` for `V := {y | y + E.e x ∈ C.openTube}` (`TubeChart.openTube_eq`); so
`Θ|_U : (U, U∖{0_x}) ≅ (V, V∖{0})` is a homeomorphism of *pairs*.  The class is the pull-back of
`stdModelGen` along the restriction to `U` (functoriality of `relCohMap`, `relCohMap_compA`,
`relCohMap_congrA`), so it is nonzero iff `(ι_V)^* stdModelGen` is nonzero in `H^{8+k}(V, V∖0)`
(`Work.Thom.bijective_relCohMap_of_homeomorphA`), and that holds because `V` is an open
neighbourhood of `0` and the restriction `H^{8+k}(ℝ^{8+k},{0}ᶜ) → H^{8+k}(V, V∖0)` is an excision
isomorphism (`Work.Serre.isIso_relCohMap_excision_of_interior`, since `{0}ᶜ ∪ V = univ`) while
`stdModelGen (8+k) ≠ 0` (`stdModelGen_span` plus `H^{8+k}(ℝ^{8+k},{0}ᶜ) ≅ ℤ`); the excision map is
injective, so a nonzero class has nonzero image.

Note: the pair condition `hcap` is available as `chartAffine_cap_ne_zero_of_ne_zeroSection` in
`Submission/Work/ThomBordism/chartModelClass_pairing_eq_pm_one.lean`, but that file contains an
unrelated `sorry`; for an axiom-clean file, reprove it locally (its proof uses only
`ambientLocalDefs`/`ambientLocalDefs2` and the `TubeChart` API). -/
theorem localChartClass_ne_zero {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt] {k : ℕ}
    (hk : 1 ≤ k) (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (x : V.pt)
    (hcont : Continuous fun p : Work.Tubular.NormalTotal E =>
      Work.ThomBordism.chartAffine E x (Work.ThomBordism.cap E ε p))
    (hcap : ∀ p : Work.Tubular.NormalTotal E, p ≠ Work.Tubular.zeroSectionNormal E x →
      Work.ThomBordism.chartAffine E x (Work.ThomBordism.cap E ε p) ≠ 0) :
    (Work.Thom.relCohMap
      (⟨fun p : Work.Tubular.NormalTotal E =>
          Work.ThomBordism.chartAffine E x (Work.ThomBordism.cap E ε p), hcont⟩ :
        C(Work.Tubular.NormalTotal E, Work.Tubular.Euc (8 + k)))
      ({p : Work.Tubular.NormalTotal E | p ≠ Work.Tubular.zeroSectionNormal E x})
      ({0}ᶜ : Set (Work.Tubular.Euc (8 + k)))
      (fun p hp => hcap p hp)
      ℤ (8 + k)).hom (Work.ThomBordism.stdModelGen (8 + k)) ≠ 0 := by
  intro hzero
  let Θ : C(Work.Tubular.NormalTotal E, Work.Tubular.Euc (8 + k)) :=
    ⟨fun p => Work.ThomBordism.chartAffine E x (Work.ThomBordism.cap E ε p), hcont⟩
  let P : Set (Work.Tubular.NormalTotal E) := {p | p ≠ Work.Tubular.zeroSectionNormal E x}
  have hzeroP : (Work.Thom.relCohMap Θ P ({0}ᶜ : Set (Work.Tubular.Euc (8 + k)))
      (fun p hp => hcap p hp) ℤ (8 + k)).hom
        (Work.ThomBordism.stdModelGen (8 + k)) = 0 := hzero
  -- Step 1: restrict the class to the open disc bundle
  let ι : C(↥(chartOpenBall E ε), Work.Tubular.NormalTotal E) :=
    ⟨Subtype.val, continuous_subtype_val⟩
  let AU : Set ↥(chartOpenBall E ε) := {p | (p : Work.Tubular.NormalTotal E) ∈ P}
  have hι : ∀ p ∈ AU, ι p ∈ P := fun p hp => hp
  have hΘι : ∀ p ∈ AU, Θ (ι p) ∈ ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) :=
    fun p hp => hcap (ι p) (hι p hp)
  have hcompA := Work.Thom.relCohMap_compA AU P ({0}ᶜ : Set (Work.Tubular.Euc (8 + k)))
    ι Θ hι (fun p hp => hcap p hp) hΘι ℤ (8 + k)
  have hlin1 := congrArg (fun φ => φ.hom) hcompA
  simp only [ModuleCat.hom_comp] at hlin1
  have hEq1 : (Work.Thom.relCohMap (Θ.comp ι) AU ({0}ᶜ : Set (Work.Tubular.Euc (8 + k)))
      hΘι ℤ (8 + k)).hom (Work.ThomBordism.stdModelGen (8 + k)) = 0 := by
    rw [← hlin1, LinearMap.comp_apply, hzeroP, map_zero]
  -- Step 2: the geometry
  obtain ⟨Φ, hVopen, h0V, hΦval, hpair⟩ := localChartClass_pairHomeo E C x hcont hcap
  let incl : C(↥(chartNbhd E C x), Work.Tubular.Euc (8 + k)) :=
    ⟨Subtype.val, continuous_subtype_val⟩
  let Vpunct : Set ↥(chartNbhd E C x) :=
    {y | (y : Work.Tubular.Euc (8 + k)) ∈ ({0}ᶜ : Set (Work.Tubular.Euc (8 + k)))}
  have hB : ∀ y ∈ Vpunct, incl y ∈ ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) := fun y hy => hy
  have he : ∀ p : ↥(chartOpenBall E ε),
      p ∈ AU ↔ (Φ : C(↥(chartOpenBall E ε), ↥(chartNbhd E C x))) p ∈ Vpunct :=
    fun p => (hpair p).trans Set.mem_compl_singleton_iff.symm
  have hΦ : ∀ p ∈ AU, (Φ : C(↥(chartOpenBall E ε), ↥(chartNbhd E C x))) p ∈ Vpunct :=
    fun p hp => (he p).mp hp
  have hBijΦ : Function.Bijective (Work.Thom.relCohMap
      (Φ : C(↥(chartOpenBall E ε), ↥(chartNbhd E C x))) AU Vpunct hΦ ℤ (8 + k)).hom :=
    Work.Thom.bijective_relCohMap_of_homeomorphA AU Vpunct Φ he ℤ (8 + k)
  have hgf : ∀ p ∈ AU, incl ((Φ : C(↥(chartOpenBall E ε), ↥(chartNbhd E C x))) p)
      ∈ ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) :=
    fun p hp => hB _ (hΦ p hp)
  have hcompB := Work.Thom.relCohMap_compA AU Vpunct ({0}ᶜ : Set (Work.Tubular.Euc (8 + k)))
    (Φ : C(↥(chartOpenBall E ε), ↥(chartNbhd E C x))) incl hΦ hB hgf ℤ (8 + k)
  have hmap : incl.comp (Φ : C(↥(chartOpenBall E ε), ↥(chartNbhd E C x))) = Θ.comp ι := by
    apply ContinuousMap.ext
    intro p
    rw [ContinuousMap.comp_apply, ContinuousMap.comp_apply]
    exact hΦval p
  have hPull : Work.Thom.relCohMap
        (incl.comp (Φ : C(↥(chartOpenBall E ε), ↥(chartNbhd E C x))))
        AU ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) hgf ℤ (8 + k)
      = Work.Thom.relCohMap (Θ.comp ι) AU ({0}ᶜ : Set (Work.Tubular.Euc (8 + k)))
          hΘι ℤ (8 + k) :=
    Work.Thom.relCohMap_congrA AU ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) hmap hgf hΘι ℤ (8 + k)
  have hEq2 : Work.Thom.relCohMap (Θ.comp ι) AU ({0}ᶜ : Set (Work.Tubular.Euc (8 + k)))
        hΘι ℤ (8 + k)
      = Work.Thom.relCohMap incl Vpunct ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) hB ℤ (8 + k)
        ≫ Work.Thom.relCohMap (Φ : C(↥(chartOpenBall E ε), ↥(chartNbhd E C x)))
            AU Vpunct hΦ ℤ (8 + k) :=
    hPull.symm.trans hcompB.symm
  -- Step 3: the excision
  have hcov : interior ({0}ᶜ : Set (Work.Tubular.Euc (8 + k)))
      ∪ interior (chartNbhd E C x) = Set.univ := by
    rw [IsOpen.interior_eq isOpen_compl_singleton, hVopen.interior_eq]
    apply Set.eq_univ_iff_forall.mpr
    intro y
    by_cases hy : y = 0
    · subst hy; exact Or.inr h0V
    · exact Or.inl hy
  have hExcision : CategoryTheory.IsIso (Work.Thom.relCohMap incl Vpunct
      ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) hB ℤ (8 + k)) :=
    Work.Serre.isIso_relCohMap_excision_of_interior ℤ
      ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) (chartNbhd E C x) hcov (8 + k)
  have hInjIncl : Function.Injective (Work.Thom.relCohMap incl Vpunct
      ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) hB ℤ (8 + k)).hom :=
    ((CategoryTheory.ConcreteCategory.isIso_iff_bijective _).mp hExcision).1
  have hstd : Work.ThomBordism.stdModelGen (8 + k) ≠ 0 :=
    localChartClass_stdModelGen_ne_zero k hk
  have hy : (Work.Thom.relCohMap incl Vpunct ({0}ᶜ : Set (Work.Tubular.Euc (8 + k)))
      hB ℤ (8 + k)).hom (Work.ThomBordism.stdModelGen (8 + k)) ≠ 0 := by
    intro h
    exact hstd (hInjIncl (h.trans (map_zero _).symm))
  have hkey : (Work.Thom.relCohMap (Φ : C(↥(chartOpenBall E ε), ↥(chartNbhd E C x)))
        AU Vpunct hΦ ℤ (8 + k)).hom
        ((Work.Thom.relCohMap incl Vpunct ({0}ᶜ : Set (Work.Tubular.Euc (8 + k)))
          hB ℤ (8 + k)).hom (Work.ThomBordism.stdModelGen (8 + k))) = 0 := by
    have h := hEq1
    rw [hEq2, ModuleCat.hom_comp] at h
    simpa only [LinearMap.comp_apply] using h
  have hy0 : (Work.Thom.relCohMap incl Vpunct ({0}ᶜ : Set (Work.Tubular.Euc (8 + k)))
      hB ℤ (8 + k)).hom (Work.ThomBordism.stdModelGen (8 + k)) = 0 :=
    hBijΦ.1 (hkey.trans (map_zero _).symm)
  exact hy hy0



end

end Work.ThomBordism
