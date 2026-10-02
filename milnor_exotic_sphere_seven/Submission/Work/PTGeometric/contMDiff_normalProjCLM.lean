import Mathlib
import Submission.Work.Tubular.Transversality
import Submission.Work.PTGeometric.exists_nowhereZero_normalSection

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Smoothness of the fibrewise orthogonal projection onto the normal space

`Work.PTGeometric.contMDiff_normalProjCLM`: for an embedding `E : V ↪ ℝ^{8+k}` of a compact smooth
`8`-manifold, the map sending `x` to the orthogonal projection of the ambient space onto the normal
space `ν_x = T_x^⊥` is `C^∞`.

The proof does not construct a smooth frame of the tangent bundle at all.  A tube chart `C` of the
embedding (`Work.Tubular.hasTubularNeighbourhood`) provides an ambient `C^∞` map, the **normal
coordinate** `y ↦ normalCoord E C y`, whose derivative at a point `e x` of the image is the
orthogonal projection onto `ν_x`:

* it kills `T_x`, because along the image it is constantly zero
  (`Work.PTGeometric.fderiv_normalCoord_apply_of_mem_tangentSpace`);
* it is the identity on `ν_x`, because along the normal directions it is a translation
  (`Work.PTGeometric.fderiv_normalCoord_apply_of_mem_normalSpace`).

Since `T_x ⊔ ν_x = ⊤`, the linear map `fderiv ℝ (normalCoord E C) (E.e x)` therefore fixes `ν_x` and
has kernel `T_x = ν_x^⊥`, so it is the orthogonal projection onto `ν_x`
(`Submodule.eq_starProjection_of_mem_orthogonal`).  Smoothness is then just smoothness of the
derivative of a smooth map (`ContDiffOn.fderiv_of_isOpen`), composed with the smooth embedding `E.e`.
-/

namespace Work.PTGeometric

theorem contMDiff_normalProjCLM {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) :
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 8)))
      (modelWithCornersSelf ℝ (Work.Tubular.Euc (8 + k) →L[ℝ] Work.Tubular.Euc (8 + k)))
      ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : V.pt => (Work.Tubular.normalSpace E x).subtypeL.comp
        ((Work.Tubular.normalSpace E x).orthogonalProjectionOnto)) := by
  by_cases hne : Nonempty V.pt
  · -- the image of the derivative of the normal coordinate is the normal projection
    obtain ⟨ε, hε, hC⟩ := @Work.Tubular.hasTubularNeighbourhood V k E hne
    obtain ⟨C⟩ := hC
    have hkey : (fun x : V.pt => (Work.Tubular.normalSpace E x).subtypeL.comp
        ((Work.Tubular.normalSpace E x).orthogonalProjectionOnto))
        = fun x : V.pt => fderiv ℝ (Work.Tubular.normalCoord E C) (E.e x) := by
      funext x
      apply ContinuousLinearMap.ext
      intro v
      change (Work.Tubular.normalSpace E x).starProjection v
        = fderiv ℝ (Work.Tubular.normalCoord E C) (E.e x) v
      refine Submodule.eq_starProjection_of_mem_orthogonal
        (K := Work.Tubular.normalSpace E x) ?_ ?_
      · -- the derivative of the normal coordinate lands in `ν_x`
        have hsup : v ∈ Work.Tubular.tangentSpace E x ⊔ Work.Tubular.normalSpace E x := by
          rw [Work.Tubular.tangentSpace_sup_normalSpace E x]; exact Submodule.mem_top
        obtain ⟨a, ha, b, hb, hab⟩ := (Submodule.mem_sup (p := Work.Tubular.tangentSpace E x)
          (p' := Work.Tubular.normalSpace E x)).mp hsup
        rw [← hab, map_add, fderiv_normalCoord_apply_of_mem_tangentSpace C x ha,
          fderiv_normalCoord_apply_of_mem_normalSpace C x hb, zero_add]
        exact hb
      · -- `v` minus its normal projection is tangent, hence orthogonal to `ν_x`
        have hsup : v ∈ Work.Tubular.tangentSpace E x ⊔ Work.Tubular.normalSpace E x := by
          rw [Work.Tubular.tangentSpace_sup_normalSpace E x]; exact Submodule.mem_top
        obtain ⟨a, ha, b, hb, hab⟩ := (Submodule.mem_sup (p := Work.Tubular.tangentSpace E x)
          (p' := Work.Tubular.normalSpace E x)).mp hsup
        have hPv : fderiv ℝ (Work.Tubular.normalCoord E C) (E.e x) v = b := by
          rw [← hab, map_add, fderiv_normalCoord_apply_of_mem_tangentSpace C x ha,
            fderiv_normalCoord_apply_of_mem_normalSpace C x hb, zero_add]
        rw [hPv, ← hab, add_sub_cancel_right]
        exact Submodule.le_orthogonal_orthogonal (Work.Tubular.tangentSpace E x) ha
    rw [hkey]
    -- smoothness: the derivative of the smooth normal coordinate, composed with the embedding
    have hderivOn : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y : Work.Tubular.Euc (8 + k) =>
          fderiv ℝ (Work.Tubular.normalCoord E C) y) C.openTube :=
      ((Work.Tubular.contMDiffOn_normalCoord E C).contDiffOn).fderiv_of_isOpen
        C.openTube_isOpen (by simp)
    have hderivMD : ContMDiffOn (modelWithCornersSelf ℝ (Work.Tubular.Euc (8 + k)))
        (modelWithCornersSelf ℝ (Work.Tubular.Euc (8 + k) →L[ℝ] Work.Tubular.Euc (8 + k)))
        ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y => fderiv ℝ (Work.Tubular.normalCoord E C) y) C.openTube :=
      contMDiffOn_iff_contDiffOn.mpr hderivOn
    have hcompOn : ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 8)))
        (modelWithCornersSelf ℝ (Work.Tubular.Euc (8 + k) →L[ℝ] Work.Tubular.Euc (8 + k)))
        ((⊤ : ℕ∞) : WithTop ℕ∞)
        ((fun y => fderiv ℝ (Work.Tubular.normalCoord E C) y) ∘ E.e) Set.univ :=
      hderivMD.comp E.smooth.contMDiffOn (fun x _ => C.mem_openTube x)
    exact contMDiffOn_univ.mp hcompOn
  · -- an empty manifold: the statement is vacuous
    intro x
    exact (hne ⟨x⟩).elim

end Work.PTGeometric
