import Mathlib
import Submission.Work.EKLC7.LeafwiseGeom
import Submission.Work.EKLContract.Lemmas.Gamma3Facts
import Submission.Work.EKLContract.Lemmas.SL3Topology

namespace Work.EKLC7

open MeasureTheory Filter Topology
open Work.EKLContract

/-- The set of points at which the action of a subgroup `U ≤ SL₃(ℝ)` on `X₃` is free:
the orbit map `u ↦ u • x` is injective on `U`. -/
def FreeU (U : Subgroup SL3) : Set X3 :=
  {x | ∀ u₁ ∈ U, ∀ u₂ ∈ U, u₁ • x = u₂ • x → u₁ = u₂}

/-- `FreeU U` is also the set of points with trivial `U`-stabiliser. -/
theorem freeU_eq (U : Subgroup SL3) :
    FreeU U = {x : X3 | ∀ u ∈ U, u • x = x → u = 1} := by
  ext x
  constructor
  · intro h u hu hux
    exact h u hu 1 (Subgroup.one_mem U) (by rw [hux, one_smul])
  · intro h u₁ hu₁ u₂ hu₂ h12
    have hmem : u₂⁻¹ * u₁ ∈ U := U.mul_mem (U.inv_mem hu₂) hu₁
    have hfix : (u₂⁻¹ * u₁) • x = x := by
      rw [mul_smul, h12, ← mul_smul, inv_mul_cancel, one_smul]
    have h1 : u₂⁻¹ * u₁ = 1 := h _ hmem hfix
    exact (inv_mul_eq_one.mp h1).symm

/-- `v • mkX g = mkX g` iff `g⁻¹ v⁻¹ g ∈ Γ₃`. -/
theorem smul_mkX_eq_iff (v g : SL3) : v • mkX g = mkX g ↔ g⁻¹ * v⁻¹ * g ∈ Γ3 := by
  rw [show (v • mkX g = mkX g) ↔ (mkX (v * g) = mkX g) from Iff.rfl,
      show mkX (v * g) = mkX g ↔ QuotientGroup.mk (v * g) = QuotientGroup.mk g from Iff.rfl,
      QuotientGroup.eq]
  constructor <;> intro h <;> (simpa [mul_assoc] using h)

theorem OrbitCoord (U : Subgroup Work.EKLContract.SL3)
    (hU : IsClosed (U : Set Work.EKLContract.SL3)) :
    ∃ coord : Work.EKLContract.X3 → Work.EKLContract.X3 → Work.EKLContract.SL3,
      Measurable (fun p : Work.EKLContract.X3 × Work.EKLContract.X3 => coord p.1 p.2) ∧
      ∀ x y : Work.EKLContract.X3,
        (∀ u₁ ∈ U, ∀ u₂ ∈ U, u₁ • x = u₂ • x → u₁ = u₂) →
        y ∈ (fun u : Work.EKLContract.SL3 => u • x) '' (U : Set Work.EKLContract.SL3) →
        coord x y ∈ U ∧ (coord x y) • x = y := by
  classical
  haveI hSB_SL3 : StandardBorelSpace SL3 := Work.EKLContract.Lemmas.SL3Topology.1
  haveI hPol_SL3 : PolishSpace SL3 := Work.EKLContract.Lemmas.polishSpace_specialLinearGroup
  have hbg := Work.EKLComp.X3Background
  haveI hT2_X3 : T2Space X3 := hbg.1
  haveI hSC_X3 : SecondCountableTopology X3 := hbg.2.2.1
  haveI hPol_X3 : PolishSpace X3 := hbg.2.2.2.1
  haveI hCount_Γ3 : Countable Γ3 := Work.EKLContract.Lemmas.countable_Γ3
  -- the quotient Borel structure is the image of the Borel structure of `SL₃(ℝ)`
  have hmap : MeasurableSpace.map (mkX : SL3 → X3) (inferInstance : MeasurableSpace SL3)
      = (inferInstance : MeasurableSpace X3) :=
    Continuous.map_eq_borel (f := (mkX : SL3 → X3)) QuotientGroup.continuous_mk
      QuotientGroup.mk_surjective
  -- the complement of the free set, written in `SL₃(ℝ)`, is a countable union of closed sets
  set T : Set SL3 :=
    ⋃ γ : {γ : Γ3 // (γ : SL3) ≠ 1}, {g : SL3 | g * ((γ : Γ3) : SL3) * g⁻¹ ∈ U} with hTdef
  have hTmeas : MeasurableSet T := by
    rw [hTdef]
    apply MeasurableSet.iUnion
    intro γ
    exact (hU.preimage (by fun_prop)).measurableSet
  have hmemT : ∀ g : SL3, g ∈ T ↔
      ∃ γ : Γ3, (γ : SL3) ≠ 1 ∧ g * (γ : SL3) * g⁻¹ ∈ U := by
    intro g
    rw [hTdef]
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨γ, hγ⟩; exact ⟨γ.1, γ.2, hγ⟩
    · rintro ⟨γ, hne, hγ⟩; exact ⟨⟨γ, hne⟩, hγ⟩
  -- the free condition on a coset, as an assertion about a representative
  have key : ∀ g : SL3,
      (∀ u ∈ U, u • mkX g = mkX g → u = 1) ↔
        ¬ ∃ γ : Γ3, (γ : SL3) ≠ 1 ∧ g * (γ : SL3) * g⁻¹ ∈ U := by
    intro g
    have hlhs : (∀ u ∈ U, u • mkX g = mkX g → u = 1) ↔
        (∀ u ∈ U, g⁻¹ * u⁻¹ * g ∈ Γ3 → u = 1) := by
      constructor
      · intro h u hu hγ; exact h u hu ((smul_mkX_eq_iff u g).mpr hγ)
      · intro h u hu hux; exact h u hu ((smul_mkX_eq_iff u g).mp hux)
    rw [hlhs]
    constructor
    · rintro h ⟨γ, hγne, hγU⟩
      have hmem : (g * (γ : SL3) * g⁻¹)⁻¹ ∈ U := U.inv_mem hγU
      have hΓ : g⁻¹ * ((g * (γ : SL3) * g⁻¹)⁻¹)⁻¹ * g ∈ Γ3 := by
        have heq : g⁻¹ * ((g * (γ : SL3) * g⁻¹)⁻¹)⁻¹ * g = (γ : SL3) := by group
        rw [heq]; exact γ.2
      have h1 := h _ hmem hΓ
      have h2 : g * (γ : SL3) * g⁻¹ = 1 := inv_eq_one.mp h1
      have hγ1 : (γ : SL3) = 1 := by
        calc (γ : SL3) = g⁻¹ * (g * (γ : SL3) * g⁻¹) * g := by group
          _ = g⁻¹ * 1 * g := by rw [h2]
          _ = 1 := by group
      exact hγne hγ1
    · intro h u hu hΓu
      by_cases hγ1 : g⁻¹ * u⁻¹ * g = 1
      · have hu1 : u⁻¹ = 1 := by
          calc u⁻¹ = g * (g⁻¹ * u⁻¹ * g) * g⁻¹ := by group
            _ = g * 1 * g⁻¹ := by rw [hγ1]
            _ = 1 := by group
        exact inv_eq_one.mp hu1
      · exact absurd ⟨⟨g⁻¹ * u⁻¹ * g, hΓu⟩, hγ1, by
          have heq : g * (g⁻¹ * u⁻¹ * g) * g⁻¹ = u⁻¹ := by group
          rw [heq]; exact U.inv_mem hu⟩ h
  have hpre_eq : mkX ⁻¹' FreeU U = Tᶜ := by
    ext g
    rw [Set.mem_preimage, freeU_eq, Set.mem_ofPred_eq, Set.mem_compl_iff]
    exact (key g).trans (not_congr (hmemT g)).symm
  have hFree_meas : MeasurableSet (FreeU U) := by
    have key2 : MeasurableSet[MeasurableSpace.map (mkX : SL3 → X3)
        (inferInstance : MeasurableSpace SL3)] (FreeU U) := by
      rw [MeasurableSpace.map_def, hpre_eq]
      exact hTmeas.compl
    rw [hmap] at key2
    exact key2
  -- the graph of the `U`-action
  set φ : SL3 × X3 → X3 × X3 := fun p => (p.2, p.1 • p.2) with hφdef
  have hφcont : Continuous φ := by rw [hφdef]; fun_prop
  have hUmeas : MeasurableSet (U : Set SL3) := hU.measurableSet
  set S : Set (SL3 × X3) := (U : Set SL3) ×ˢ FreeU U with hSdef
  have hSmeas : MeasurableSet S := by rw [hSdef]; exact hUmeas.prod hFree_meas
  have hφinj : Set.InjOn φ S := by
    rintro ⟨u₁, x₁⟩ h₁ ⟨u₂, x₂⟩ h₂ hab
    rw [hSdef, Set.mem_prod] at h₁ h₂
    have hx : x₁ = x₂ := congrArg Prod.fst hab
    have hu : u₁ • x₁ = u₂ • x₂ := congrArg Prod.snd hab
    subst hx
    exact Prod.ext (h₁.2 u₁ h₁.1 u₂ h₂.1 hu) rfl
  haveI hSB_S : StandardBorelSpace (↥S) := hSmeas.standardBorel
  have hEmbd : MeasurableEmbedding (S.domRestrict φ) :=
    (hφcont.measurable.comp measurable_subtype_coe).measurableEmbedding
      (fun a b hab => Subtype.ext (hφinj a.2 b.2 (by simpa using hab)))
  have hgmeas : Measurable (fun s : ↥S => ((s : SL3 × X3)).1) := by fun_prop
  obtain ⟨g', hg'meas, hg'comp⟩ :=
    hEmbd.exists_measurable_extend hgmeas (fun _ => ⟨(1 : SL3)⟩)
  refine ⟨fun x y => g' (x, y), ?_, ?_⟩
  · simpa using hg'meas
  · intro x y hfree hy
    rw [Set.mem_image] at hy
    obtain ⟨u₀, hu₀U, hu₀eq⟩ := hy
    have hxfree : x ∈ FreeU U := hfree
    have hs₀ : ((u₀, x) : SL3 × X3) ∈ S := by
      rw [hSdef, Set.mem_prod]; exact ⟨hu₀U, hxfree⟩
    have hval : g' (x, y) = u₀ := by
      have hfval : (S.domRestrict φ) ⟨(u₀, x), hs₀⟩ = (x, y) := by
        simp only [Set.domRestrict, hφdef]
        rw [hu₀eq]
      calc g' (x, y) = g' ((S.domRestrict φ) ⟨(u₀, x), hs₀⟩) := by rw [hfval]
        _ = (fun s : ↥S => ((s : SL3 × X3)).1) ⟨(u₀, x), hs₀⟩ := congrFun hg'comp _
        _ = u₀ := rfl
    change g' (x, y) ∈ U ∧ g' (x, y) • x = y
    rw [hval]
    exact ⟨hu₀U, hu₀eq⟩

end Work.EKLC7
