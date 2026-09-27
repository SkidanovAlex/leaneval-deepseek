import Mathlib
import Submission.Work.EKLGlobal.BadRatio
import Submission.Work.EKLGlobal.ProductLocal
import Submission.Work.EKLProd.continuous_uPart

/-!
# The convolution `conv ν_T ν_U` is finite on compacta

Let `T, U ≤ H ≤ SL₃(ℝ)` be closed subgroups with `T` normalising `U`, `H = T · U` and
`T ⊓ U = ⊥` (so that every `h ∈ H` factors uniquely as `h = t · u`).  If `νT, νU` are measures
finite on compacta and carried respectively by `T` and `U`, then the convolution
`conv νT νU = mul_∗ (νT ⊗ νU)` is again finite on compacta.

The point is a topological one: by `Work.EKLProd.continuous_uPart` the `U`-coordinate
`ρ : H → U` of the decomposition is continuous, so the graph map
`Ψ h = (h · (ρ h)⁻¹, ρ h)` is a continuous map of `H` into `T × U`.  The `mul`-preimage of a
compact set therefore lies in the compact set `Ψ '' (K ∩ H)` up to the `(T × U)ᶜ`-null set, and
`(νT ⊗ νU)(Ψ '' (K ∩ H)) ≤ νT (fst '' _) · νU (snd '' _) < ⊤` because the projections of a
compact set are compact.
-/

open MeasureTheory Set
open Work.EKLContract

namespace Work.EKLGlobal

theorem conv_lt_top_of_isCompact {H T U : Subgroup Work.EKLContract.SL3} (hTH : T ≤ H) (hUH : U ≤ H)
    (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U)
    (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u)
    (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    (hHc : IsClosed (H : Set Work.EKLContract.SL3)) (hTc : IsClosed (T : Set Work.EKLContract.SL3))
    (hUc : IsClosed (U : Set Work.EKLContract.SL3))
    {νT νU : MeasureTheory.Measure Work.EKLContract.SL3}
    (hTfin : ∀ K : Set Work.EKLContract.SL3, IsCompact K → νT K < ⊤)
    (hUfin : ∀ K : Set Work.EKLContract.SL3, IsCompact K → νU K < ⊤)
    (hTcar : νT (T : Set Work.EKLContract.SL3)ᶜ = 0) (hUcar : νU (U : Set Work.EKLContract.SL3)ᶜ = 0)
    {K : Set Work.EKLContract.SL3} (hK : IsCompact K) :
    Work.EKLGlobal.conv νT νU K < ⊤ := by
  classical
  haveI : SigmaCompactSpace SL3 := inferInstance
  haveI : IsFiniteMeasureOnCompacts νT := ⟨hTfin⟩
  haveI : IsFiniteMeasureOnCompacts νU := ⟨hUfin⟩
  haveI : SigmaFinite νT := SigmaFinite.of_isFiniteMeasureOnCompacts νT
  haveI : SigmaFinite νU := SigmaFinite.of_isFiniteMeasureOnCompacts νU
  haveI : SFinite νT := inferInstance
  haveI : SFinite νU := inferInstance
  -- The `U`-coordinate of the unique decomposition `h = t * u`.
  obtain ⟨ρ, hρcont, hρspec⟩ :=
    Work.EKLProd.continuous_uPart hTH hUH hnorm hcop hdisj hHc hTc hUc
  -- Uniqueness of the decomposition.
  have huniq : ∀ (a a' b b' : SL3), a ∈ T → a' ∈ T → b ∈ U → b' ∈ U →
      a * b = a' * b' → a = a' ∧ b = b' := by
    intro a a' b b' ha ha' hb hb' h
    have h1 : a⁻¹ * a' = b * b'⁻¹ := by
      suffices hsuf : a⁻¹ * a' * b' = b by rw [← hsuf]; group
      calc a⁻¹ * a' * b' = a⁻¹ * (a' * b') := by group
        _ = a⁻¹ * (a * b) := by rw [h]
        _ = b := by group
    have hU : a⁻¹ * a' ∈ U := by rw [h1]; exact U.mul_mem hb (U.inv_mem hb')
    have hT : a⁻¹ * a' ∈ T := T.mul_mem (T.inv_mem ha) ha'
    have h2 : a⁻¹ * a' = 1 := hdisj _ hT hU
    have haa : a = a' := inv_mul_eq_one.mp h2
    refine ⟨haa, ?_⟩
    rw [haa] at h
    exact mul_left_cancel h
  -- `h * (ρ h)⁻¹` is the `T`-coordinate, in particular an element of `T`.
  have htmem : ∀ h : ↥H, (h : SL3) * (ρ h : SL3)⁻¹ ∈ T := by
    intro h
    obtain ⟨t, htT, ht⟩ := hρspec h
    have : (h : SL3) * (ρ h : SL3)⁻¹ = t := by rw [ht]; group
    rw [this]; exact htT
  -- The graph map `Ψ : H → T × U`.
  let Ψ : ↥H → SL3 × SL3 := fun h => ((h : SL3) * (ρ h : SL3)⁻¹, (ρ h : SL3))
  have hΨcont : Continuous Ψ := by
    refine Continuous.prodMk ?_ ?_
    · exact continuous_subtype_val.mul ((continuous_subtype_val.comp hρcont).inv)
    · exact continuous_subtype_val.comp hρcont
  -- `K ∩ H` is compact, so its image under `Ψ` is compact.
  have hS0 : IsCompact {h : ↥H | (h : SL3) ∈ K} :=
    hHc.isClosedEmbedding_subtypeVal.isCompact_preimage hK
  have hC : IsCompact (Ψ '' {h : ↥H | (h : SL3) ∈ K}) := hS0.image hΨcont
  -- The set of pairs of the convolution.
  set A : Set (SL3 × SL3) := (fun p : SL3 × SL3 => p.1 * p.2) ⁻¹' K with hAdef
  set S : Set (SL3 × SL3) := A ∩ ((T : Set SL3) ×ˢ (U : Set SL3)) with hSdef
  have hSsubC : S ⊆ Ψ '' {h : ↥H | (h : SL3) ∈ K} := by
    rintro ⟨x, y⟩ hp
    rw [hSdef, hAdef] at hp
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod] at hp
    obtain ⟨hxyK, hxT, hyU⟩ := hp
    set h : ↥H := ⟨x * y, H.mul_mem (hTH hxT) (hUH hyU)⟩ with hh
    have hhval : (h : SL3) = x * y := rfl
    have hprod : ((h : SL3) * (ρ h : SL3)⁻¹) * (ρ h : SL3) = x * y := by
      rw [hhval]; group
    obtain ⟨h1, h2⟩ := huniq ((h : SL3) * (ρ h : SL3)⁻¹) x (ρ h) y
      (htmem h) hxT (ρ h).2 hyU hprod
    refine ⟨h, hxyK, ?_⟩
    change (((h : SL3) * (ρ h : SL3)⁻¹, (ρ h : SL3)) : SL3 × SL3) = (x, y)
    rw [h1, h2]
  -- `(νT ⊗ νU)` is carried by `T × U`.
  have hAc : (νT.prod νU) ((T : Set SL3) ×ˢ (U : Set SL3))ᶜ = 0 := by
    rw [Set.compl_prod_eq_union]
    refine le_antisymm ?_ bot_le
    calc (νT.prod νU) ((T : Set SL3)ᶜ ×ˢ Set.univ ∪ Set.univ ×ˢ (U : Set SL3)ᶜ)
        ≤ (νT.prod νU) ((T : Set SL3)ᶜ ×ˢ Set.univ)
            + (νT.prod νU) (Set.univ ×ˢ (U : Set SL3)ᶜ) := measure_union_le _ _
      _ = νT (T : Set SL3)ᶜ * νU Set.univ + νT Set.univ * νU (U : Set SL3)ᶜ := by
          rw [Measure.prod_prod, Measure.prod_prod]
      _ = 0 := by rw [hTcar, hUcar]; simp
  have hA_le : (νT.prod νU) A ≤ (νT.prod νU) S := by
    calc (νT.prod νU) A
        ≤ (νT.prod νU) (S ∪ ((T : Set SL3) ×ˢ (U : Set SL3))ᶜ) := by
          apply measure_mono
          intro p hp
          by_cases h : p ∈ (T : Set SL3) ×ˢ (U : Set SL3)
          · exact Or.inl ⟨hp, h⟩
          · exact Or.inr h
      _ ≤ (νT.prod νU) S + (νT.prod νU) ((T : Set SL3) ×ˢ (U : Set SL3))ᶜ :=
          measure_union_le _ _
      _ = (νT.prod νU) S := by rw [hAc, add_zero]
  -- Finiteness of the `prod`-measure of `S`.
  have hfin1 : νT (Prod.fst '' S) < ⊤ :=
    lt_of_le_of_lt (measure_mono (Set.image_mono hSsubC)) (hTfin _ (hC.image continuous_fst))
  have hfin2 : νU (Prod.snd '' S) < ⊤ :=
    lt_of_le_of_lt (measure_mono (Set.image_mono hSsubC)) (hUfin _ (hC.image continuous_snd))
  have hSle : (νT.prod νU) S ≤ νT (Prod.fst '' S) * νU (Prod.snd '' S) := by
    calc (νT.prod νU) S ≤ (νT.prod νU) ((Prod.fst '' S) ×ˢ (Prod.snd '' S)) := by
          apply measure_mono
          intro p hp
          simp only [Set.mem_prod, Set.mem_image]
          exact ⟨⟨p, hp, rfl⟩, ⟨p, hp, rfl⟩⟩
      _ = νT (Prod.fst '' S) * νU (Prod.snd '' S) := Measure.prod_prod _ _
  have hSlt : (νT.prod νU) S < ⊤ := lt_of_le_of_lt hSle (ENNReal.mul_lt_top hfin1 hfin2)
  have hconv : Work.EKLGlobal.conv νT νU K = (νT.prod νU) A := by
    rw [Work.EKLGlobal.conv, hAdef]
    exact Measure.map_apply ((continuous_fst.mul continuous_snd).measurable)
      hK.isClosed.measurableSet
  rw [hconv]
  exact lt_of_le_of_lt hA_le hSlt

end Work.EKLGlobal
