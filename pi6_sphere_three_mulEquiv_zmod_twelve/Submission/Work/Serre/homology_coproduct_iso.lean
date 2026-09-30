import Mathlib
import Submission.Work.Serre.LevCopDefs
import Submission.Work.Serre.kernel_sigma_map_iso
import Submission.Work.Serre.levCopIso

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Homology commutes with coproducts in `ModuleCat ℤ`

The `n`-th homology of a coproduct of homological complexes of `ℤ`-modules is the coproduct of the
`n`-th homologies.  The proof goes through the degreewise description of the coproduct of complexes
(`Work.Serre.levCop`, `Work.Serre.levCopIso`) and of the `n`-th short complex of the coproduct
(`Work.Serre.levShort`): the cycles of the levelwise coproduct short complex are the coproduct of
the cycles (this is where exactness of coproducts, i.e. `Work.Serre.kernel_sigma_map_iso`, is
used), and the comparison map between the homologies is then built explicitly from the cokernel
description `S.homology = cokernel S.toCycles` of a short complex.

The final diagram is, for `K : ι → ChainComplex (ModuleCat ℤ) ℕ`:

`(∐ K).homology n ≅ (levCop K).homology n ≅ (levShort K n).homology ≅ ∐ (K i).homology n`.
-/

open CategoryTheory Limits

namespace Work.Serre

noncomputable section

/-- The cycles of a short complex, as a kernel. -/
lemma cyclesIsoKernel (S : ShortComplex (ModuleCat ℤ)) :
    ∃ (e : S.cycles ≅ kernel S.g), e.hom ≫ kernel.ι S.g = S.iCycles := by
  refine ⟨S.cyclesIsKernel.conePointUniqueUpToIso (limit.isLimit (parallelPair S.g 0)), ?_⟩
  exact IsLimit.conePointUniqueUpToIso_hom_comp _ _ _

/-- The cycles of the levelwise coproduct short complex are the coproduct of the cycles. -/
lemma levShort_cycles_iso
    {ι : Type} {c : ComplexShape ℕ} (K : ι → HomologicalComplex (ModuleCat ℤ) c) (n : ℕ) :
    ∃ (ψ : (∐ fun i => ((K i).sc n).cycles) ≅ (levShort K n).cycles),
      ψ.hom ≫ (levShort K n).iCycles = Limits.Sigma.map (fun i => ((K i).sc n).iCycles) := by
  obtain ⟨e, he⟩ := kernel_sigma_map_iso (fun i => ((K i).sc n).g)
  obtain ⟨iS, hiS⟩ := cyclesIsoKernel (levShort K n)
  have hT : ∀ i, ∃ (e' : ((K i).sc n).cycles ≅ kernel ((K i).sc n).g),
      e'.hom ≫ kernel.ι ((K i).sc n).g = ((K i).sc n).iCycles := fun i => cyclesIsoKernel _
  choose iT hiT using hT
  have hpsi0 : (Limits.Sigma.mapIso iT ≪≫ e).hom ≫ kernel.ι (levShort K n).g
      = Limits.Sigma.map (fun i => ((K i).sc n).iCycles) := by
    rw [Iso.trans_hom, Category.assoc, he]
    apply Limits.Sigma.hom_ext
    intro j
    rw [← Category.assoc, Limits.Sigma.ι_mapIso_hom, Category.assoc, Limits.Sigma.ι_map,
      ← Category.assoc, hiT j, Limits.Sigma.ι_map]
  have h1 : iS.inv ≫ (levShort K n).iCycles = kernel.ι (levShort K n).g := by
    rw [← hiS, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  refine ⟨{ hom := (Limits.Sigma.mapIso iT ≪≫ e).hom ≫ iS.inv
            inv := iS.hom ≫ (Limits.Sigma.mapIso iT ≪≫ e).inv
            hom_inv_id := ?_
            inv_hom_id := ?_ }, ?_⟩
  · simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id]
  · simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id]
  · rw [Category.assoc, h1]
    exact hpsi0

/-- The homology of the levelwise coproduct short complex is the coproduct of the homologies. -/
lemma levShort_homology_iso
    {ι : Type} {c : ComplexShape ℕ} (K : ι → HomologicalComplex (ModuleCat ℤ) c) (n : ℕ) :
    Nonempty ((levShort K n).homology ≅ ∐ fun i => ((K i).sc n).homology) := by
  obtain ⟨ψ, hψ⟩ := levShort_cycles_iso K n
  have hto : (levShort K n).toCycles
      = Limits.Sigma.map (fun i => ((K i).sc n).toCycles) ≫ ψ.hom := by
    rw [← cancel_mono (levShort K n).iCycles, ShortComplex.toCycles_i, Category.assoc, hψ,
      Limits.Sigma.map_comp_map,
      show (fun i => ((K i).sc n).toCycles ≫ ((K i).sc n).iCycles) = (fun i => ((K i).sc n).f)
        from funext (fun i => ShortComplex.toCycles_i _)]
  have hk : (levShort K n).toCycles ≫
      (ψ.inv ≫ Limits.Sigma.map (fun i => ((K i).sc n).homologyπ)) = 0 := by
    rw [hto]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    apply Limits.Sigma.hom_ext
    intro i
    rw [← Category.assoc, Limits.Sigma.ι_map, Category.assoc, Limits.Sigma.ι_map,
      ← Category.assoc, ShortComplex.toCycles_comp_homologyπ]
    simp
  have hφ : ∀ i, ((K i).sc n).toCycles ≫
      (Limits.Sigma.ι (fun j => ((K j).sc n).cycles) i ≫ ψ.hom
        ≫ (levShort K n).homologyπ) = 0 := by
    intro i
    have h1 : ((K i).sc n).toCycles ≫ Limits.Sigma.ι (fun j => ((K j).sc n).cycles) i
        = Limits.Sigma.ι (fun j => ((K j).sc n).X₁) i
            ≫ Limits.Sigma.map (fun j => ((K j).sc n).toCycles) := by
      rw [Limits.Sigma.ι_map]
    calc ((K i).sc n).toCycles ≫
            (Limits.Sigma.ι (fun j => ((K j).sc n).cycles) i ≫ ψ.hom
              ≫ (levShort K n).homologyπ)
        = (((K i).sc n).toCycles ≫ Limits.Sigma.ι (fun j => ((K j).sc n).cycles) i)
            ≫ ψ.hom ≫ (levShort K n).homologyπ := by simp only [Category.assoc]
      _ = (Limits.Sigma.ι (fun j => ((K j).sc n).X₁) i
              ≫ Limits.Sigma.map (fun j => ((K j).sc n).toCycles)) ≫ ψ.hom
            ≫ (levShort K n).homologyπ := by rw [h1]
      _ = Limits.Sigma.ι (fun j => ((K j).sc n).X₁) i ≫ (levShort K n).toCycles
            ≫ (levShort K n).homologyπ := by rw [hto]; simp only [Category.assoc]
      _ = 0 := by simp
  let α : (levShort K n).homology ⟶ ∐ fun i => ((K i).sc n).homology :=
    (levShort K n).descHomology
      (ψ.inv ≫ Limits.Sigma.map (fun i => ((K i).sc n).homologyπ)) hk
  let β : (∐ fun i => ((K i).sc n).homology) ⟶ (levShort K n).homology :=
    Limits.Sigma.desc (fun i => ((K i).sc n).descHomology
      (Limits.Sigma.ι (fun j => ((K j).sc n).cycles) i ≫ ψ.hom
        ≫ (levShort K n).homologyπ) (hφ i))
  have hcomp : Limits.Sigma.map (fun i => ((K i).sc n).homologyπ) ≫
      Limits.Sigma.desc (fun i => ((K i).sc n).descHomology
        (Limits.Sigma.ι (fun j => ((K j).sc n).cycles) i ≫ ψ.hom
          ≫ (levShort K n).homologyπ) (hφ i))
      = Limits.Sigma.desc (fun i => Limits.Sigma.ι (fun j => ((K j).sc n).cycles) i ≫ ψ.hom
          ≫ (levShort K n).homologyπ) := by
    apply Limits.Sigma.hom_ext
    intro i
    rw [← Category.assoc, Limits.Sigma.ι_map, Category.assoc, Limits.Sigma.ι_desc,
      ShortComplex.π_descHomology, Limits.Sigma.ι_desc]
  have hdesc : Limits.Sigma.desc (fun i => Limits.Sigma.ι (fun j => ((K j).sc n).cycles) i
        ≫ ψ.hom ≫ (levShort K n).homologyπ) = ψ.hom ≫ (levShort K n).homologyπ := by
    apply Limits.Sigma.hom_ext
    intro i
    rw [Limits.Sigma.ι_desc]
  have hαβ : α ≫ β = 𝟙 _ := by
    dsimp only [α, β]
    rw [← cancel_epi (levShort K n).homologyπ]
    rw [← Category.assoc, ShortComplex.π_descHomology, Category.assoc, hcomp, hdesc]
    simpa only [Category.comp_id] using Iso.inv_hom_id_assoc ψ (levShort K n).homologyπ
  have hβα : β ≫ α = 𝟙 _ := by
    dsimp only [α, β]
    apply Limits.Sigma.hom_ext
    intro j
    rw [← Category.assoc, Limits.Sigma.ι_desc, ← cancel_epi ((K j).sc n).homologyπ,
      ← Category.assoc, ShortComplex.π_descHomology, Category.assoc, Category.assoc,
      ShortComplex.π_descHomology, Iso.hom_inv_id_assoc, Limits.Sigma.ι_map, Category.comp_id]
  exact ⟨{ hom := α, inv := β, hom_inv_id := hαβ, inv_hom_id := hβα }⟩

/-- The levelwise coproduct short complex is the `n`-th short complex of the levelwise coproduct
complex. -/
lemma levShort_iso_sc {ι : Type} {c : ComplexShape ℕ}
    (K : ι → HomologicalComplex (ModuleCat ℤ) c) (n : ℕ) :
    Nonempty ((levShort K n) ≅ (levCop K).sc n) := by
  refine ⟨ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_⟩
  · exact (Category.id_comp _).trans (Category.comp_id _).symm
  · exact (Category.id_comp _).trans (Category.comp_id _).symm

/-- **The homology of a coproduct of homological complexes is the coproduct of the homologies.** -/
theorem homology_coproduct_iso_gen
    {ι : Type} {c : ComplexShape ℕ} (K : ι → HomologicalComplex (ModuleCat ℤ) c) (n : ℕ) :
    Nonempty (((∐ K).homology n) ≅ ∐ fun i => (K i).homology n) := by
  obtain ⟨e⟩ := levCopIso K
  obtain ⟨scIso⟩ := levShort_iso_sc K n
  obtain ⟨h⟩ := levShort_homology_iso K n
  exact ⟨(HomologicalComplex.homologyMapIso e n) ≪≫ (ShortComplex.homologyMapIso scIso) ≪≫ h⟩


theorem homology_coproduct_iso {ι : Type} (K : ι → ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) :
    Nonempty (((∐ fun i => K i).homology n) ≅ ∐ fun i => (K i).homology n) :=
  homology_coproduct_iso_gen K n

end

end Work.Serre
