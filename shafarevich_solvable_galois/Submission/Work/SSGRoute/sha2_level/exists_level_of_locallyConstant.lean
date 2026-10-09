import Mathlib
import Submission.Work.SSGRoute.sha2_bridge
import Submission.Work.AbsoluteKummer.All
import Submission.Work.AbsoluteKummer.Factorisation.exists_finiteGalois_le_ker_pair
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.sha2_level

open scoped Classical

/-- Local constancy is preserved by composition with a continuous map. -/
theorem isLocallyConstant_comp_continuous_aux {X Y Z : Type} [TopologicalSpace X]
    [TopologicalSpace Y] {f : Y → Z} (hf : Work.AbsoluteKummer.IsLocallyConstant f)
    {φ : X → Y} (hφ : Continuous φ) : Work.AbsoluteKummer.IsLocallyConstant (f ∘ φ) := by
  intro x
  obtain ⟨V, hV, hxV, hVc⟩ := hf (φ x)
  exact ⟨φ ⁻¹' V, hV.preimage hφ, hxV, fun y hy => hVc (φ y) hy⟩

theorem exists_level_of_locallyConstant (k : Type) [Field k] [NumberField k]
    (d : (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) × (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) →
      Additive (AlgebraicClosure k)ˣ)
    (hd : Work.AbsoluteKummer.IsLocallyConstant d) :
    ∃ (L : FiniteGaloisIntermediateField k (AlgebraicClosure k)),
      (∀ (g h u v : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k),
        u ∈ (L : IntermediateField k (AlgebraicClosure k)).fixingSubgroup →
        v ∈ (L : IntermediateField k (AlgebraicClosure k)).fixingSubgroup →
        d (g * u, h * v) = d (g, h)) ∧
      (∀ g h, ∃ x : (L : IntermediateField k (AlgebraicClosure k))ˣ,
        Units.map (algebraMap (L : IntermediateField k (AlgebraicClosure k))
          (AlgebraicClosure k)).toMonoidHom x = Additive.toMul (d (g, h))) := by
  haveI : IsGalois k (AlgebraicClosure k) := IsAlgClosure.isGalois k _
  -- ## the level containing the values
  have hvalfin : (Set.range d).Finite := Work.AbsoluteKummer.finite_image_of_isLocallyConstant hd
  let S : Set (AlgebraicClosure k) :=
    (fun u : (AlgebraicClosure k)ˣ => (u : AlgebraicClosure k)) ''
      (Additive.toMul '' (Set.range d))
  have hSfin : S.Finite := (hvalfin.image Additive.toMul).image _
  haveI : Finite S := hSfin.to_subtype
  let Lv : FiniteGaloisIntermediateField k (AlgebraicClosure k) :=
    FiniteGaloisIntermediateField.adjoin k S
  have hval : ∀ p : (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) ×
      (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k),
      ((Additive.toMul (d p) : (AlgebraicClosure k)ˣ) : AlgebraicClosure k) ∈
        (Lv : IntermediateField k (AlgebraicClosure k)) := by
    intro p
    have hxS : ((Additive.toMul (d p) : (AlgebraicClosure k)ˣ) : AlgebraicClosure k) ∈ S :=
      ⟨Additive.toMul (d p), ⟨d p, ⟨p, rfl⟩, rfl⟩, rfl⟩
    exact FiniteGaloisIntermediateField.subset_adjoin k S hxS
  -- ## the level of right invariance
  have key : ∀ x : (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) ×
      (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k),
      ∃ L : FiniteGaloisIntermediateField k (AlgebraicClosure k),
        ∀ u ∈ (L : IntermediateField k (AlgebraicClosure k)).fixingSubgroup,
          ∀ v ∈ (L : IntermediateField k (AlgebraicClosure k)).fixingSubgroup,
          d (x.1 * u, x.2 * v) = d x := by
    intro x
    have hcont : Continuous fun p : (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) ×
        (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) => (x.1 * p.1, x.2 * p.2) :=
      (continuous_const.mul continuous_fst).prodMk (continuous_const.mul continuous_snd)
    have hloc := isLocallyConstant_comp_continuous_aux hd hcont
    obtain ⟨L, hL⟩ := Work.AbsoluteKummer.Factorisation.exists_finiteGalois_le_ker_pair hloc
    refine ⟨L, fun u hu v hv => ?_⟩
    have := hL (u, v) hu hv
    simpa [Function.comp_apply, mul_one] using this
  choose Lf hLf using key
  -- ## compactness: finitely many translates cover `G_k × G_k`
  let U : (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) ×
      (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) →
      Set ((AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) ×
        (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k)) :=
    fun x => (Homeomorph.mulLeft x.1 '' ((Lf x : IntermediateField k (AlgebraicClosure k)).fixingSubgroup :
        Set (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k))) ×ˢ
      (Homeomorph.mulLeft x.2 '' ((Lf x : IntermediateField k (AlgebraicClosure k)).fixingSubgroup :
        Set (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k)))
  have hUopen : ∀ x, IsOpen (U x) := by
    intro x
    exact ((Homeomorph.mulLeft x.1).isOpenMap _
        (IntermediateField.fixingSubgroup_isOpen
          (Lf x : IntermediateField k (AlgebraicClosure k)))).prod
      ((Homeomorph.mulLeft x.2).isOpenMap _
        (IntermediateField.fixingSubgroup_isOpen
          (Lf x : IntermediateField k (AlgebraicClosure k))))
  have hUcover : (Set.univ : Set ((AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) ×
      (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k))) ⊆ ⋃ x, U x := by
    intro x _
    have hxU : x ∈ U x := by
      refine ⟨?_, ?_⟩
      · exact ⟨1, (Lf x : IntermediateField k (AlgebraicClosure k)).fixingSubgroup.one_mem, by simp⟩
      · exact ⟨1, (Lf x : IntermediateField k (AlgebraicClosure k)).fixingSubgroup.one_mem, by simp⟩
    exact Set.mem_iUnion.2 ⟨x, hxU⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hUopen hUcover
  -- ## the invariance level: the sup of the finitely many levels
  let L₀ : FiniteGaloisIntermediateField k (AlgebraicClosure k) := t.sup Lf
  have hinv₀ : ∀ g h u v : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k,
      u ∈ (L₀ : IntermediateField k (AlgebraicClosure k)).fixingSubgroup →
      v ∈ (L₀ : IntermediateField k (AlgebraicClosure k)).fixingSubgroup →
      d (g * u, h * v) = d (g, h) := by
    intro g h u v hu hv
    have hmem : (g, h) ∈ ⋃ x ∈ t, U x := ht (Set.mem_univ (g, h))
    simp only [Set.mem_iUnion] at hmem
    obtain ⟨x, hxt, hxU⟩ := hmem
    obtain ⟨⟨u₀, hu₀, rfl⟩, ⟨v₀, hv₀, rfl⟩⟩ := hxU
    have hle : Lf x ≤ L₀ := Finset.le_sup hxt
    have hfix : (L₀ : IntermediateField k (AlgebraicClosure k)).fixingSubgroup ≤
        (Lf x : IntermediateField k (AlgebraicClosure k)).fixingSubgroup :=
      IntermediateField.fixingSubgroup_antitone hle
    have hu' : u₀ * u ∈ (Lf x : IntermediateField k (AlgebraicClosure k)).fixingSubgroup :=
      Subgroup.mul_mem _ hu₀ (hfix hu)
    have hv' : v₀ * v ∈ (Lf x : IntermediateField k (AlgebraicClosure k)).fixingSubgroup :=
      Subgroup.mul_mem _ hv₀ (hfix hv)
    have h1 : d (x.1 * (u₀ * u), x.2 * (v₀ * v)) = d x := hLf x (u₀ * u) hu' (v₀ * v) hv'
    have h2 : d (x.1 * u₀, x.2 * v₀) = d x := hLf x u₀ hu₀ v₀ hv₀
    calc d ((x.1 * u₀) * u, (x.2 * v₀) * v)
        = d (x.1 * (u₀ * u), x.2 * (v₀ * v)) := by rw [mul_assoc, mul_assoc]
      _ = d x := h1
      _ = d (x.1 * u₀, x.2 * v₀) := h2.symm
  -- ## assemble: the sup of the invariance level and the values level
  refine ⟨L₀ ⊔ Lv, ?_, ?_⟩
  · intro g h u v hu hv
    exact hinv₀ g h u v
      (IntermediateField.fixingSubgroup_antitone (le_sup_left : L₀ ≤ L₀ ⊔ Lv) hu)
      (IntermediateField.fixingSubgroup_antitone (le_sup_left : L₀ ≤ L₀ ⊔ Lv) hv)
  · intro g h
    have hle : (Lv : IntermediateField k (AlgebraicClosure k)) ≤
        ((L₀ ⊔ Lv : FiniteGaloisIntermediateField k (AlgebraicClosure k)) :
          IntermediateField k (AlgebraicClosure k)) := by
      rw [← FiniteGaloisIntermediateField.le_iff]
      exact le_sup_right
    have hmem : ((Additive.toMul (d (g, h)) : (AlgebraicClosure k)ˣ) : AlgebraicClosure k) ∈
        ((L₀ ⊔ Lv : FiniteGaloisIntermediateField k (AlgebraicClosure k)) :
          IntermediateField k (AlgebraicClosure k)) :=
      hle (hval (g, h))
    refine ⟨Units.mk0 ⟨_, hmem⟩ ?_, ?_⟩
    · intro hzero
      have h2 : ((Additive.toMul (d (g, h)) : (AlgebraicClosure k)ˣ) : AlgebraicClosure k) = 0 := by
        have := congrArg
          (fun z : ((L₀ ⊔ Lv : FiniteGaloisIntermediateField k (AlgebraicClosure k)) :
            IntermediateField k (AlgebraicClosure k)) => ((z : AlgebraicClosure k))) hzero
        simpa using this
      exact Units.ne_zero (d (g, h)) h2
    · ext
      simp [Units.coe_map]

end Work.SSGRoute.sha2_level
