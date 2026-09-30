import Mathlib
import Submission.Work.BW.Minkowski2.defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW.Minkowski2

open scoped Pointwise

/-- The successive minima of a lattice with respect to a body are invariant under a linear
change of variables: pulling `Λ` back along a linear equivalence `e` and pulling the body `S`
back along `e` does not change `succMinBody`.

Indeed, `e` maps `ZLattice.comap ℝ Λ e.toLinearMap ∩ lam • (e ⁻¹' S)` bijectively onto
`Λ ∩ lam • S`, hence onto the spans, which therefore have the same `ℝ`-dimension. -/
lemma succMinBody_comap_linearEquiv {d : ℕ} (e : (Fin d → ℝ) ≃ₗ[ℝ] (Fin d → ℝ))
    (Λ : Submodule ℤ (Fin d → ℝ)) (S : Set (Fin d → ℝ)) (j : ℕ) :
    Work.BW.succMinBody (ZLattice.comap ℝ Λ e.toLinearMap) (e ⁻¹' S) j
      = Work.BW.succMinBody Λ S j := by
  unfold Work.BW.succMinBody
  -- The pulled-back lattice is the preimage of `Λ`, so `∩ lam • (e ⁻¹' S)` is the preimage of
  -- `Λ ∩ lam • S` under `e`.
  have hpre : ∀ lam : ℝ, ((ZLattice.comap ℝ Λ e.toLinearMap : Set (Fin d → ℝ))
        ∩ (lam • (e ⁻¹' S))) = e ⁻¹' ((Λ : Set (Fin d → ℝ)) ∩ (lam • S)) := by
    intro lam
    ext x
    rw [Set.mem_inter_iff, Set.mem_preimage, Set.mem_inter_iff, ZLattice.coe_comap,
      Set.mem_preimage, Set.mem_smul_set, Set.mem_smul_set]
    constructor
    · rintro ⟨hxL, y, hyS, hyx⟩
      exact ⟨hxL, e y, hyS, by rw [← hyx, map_smul]⟩
    · rintro ⟨hxL, s, hsS, hsx⟩
      refine ⟨hxL, e.symm s, by simpa using hsS, ?_⟩
      apply e.injective
      rw [map_smul, e.apply_symm_apply, hsx]
  -- Hence the spans of these two sets are related by `e`, so they have equal dimension.
  have hfin : ∀ lam : ℝ,
      Module.finrank ℝ (Submodule.span ℝ ((ZLattice.comap ℝ Λ e.toLinearMap : Set (Fin d → ℝ))
          ∩ (lam • (e ⁻¹' S))))
        = Module.finrank ℝ (Submodule.span ℝ ((Λ : Set (Fin d → ℝ)) ∩ (lam • S))) := by
    intro lam
    have hmap : (Submodule.span ℝ (e ⁻¹' ((Λ : Set (Fin d → ℝ)) ∩ (lam • S)))).map
        (e : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ))
        = Submodule.span ℝ ((Λ : Set (Fin d → ℝ)) ∩ (lam • S)) := by
      rw [Submodule.map_span]
      congr 1
      exact Set.image_preimage_eq _ e.surjective
    rw [hpre lam, ← hmap, LinearEquiv.finrank_map_eq]
  -- The two defining sets of the `sInf` therefore coincide.
  congr 1
  ext lam
  simp only [Set.mem_ofPred_eq]
  rw [hfin lam]

end Work.BW.Minkowski2
