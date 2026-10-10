import Mathlib
import Submission.Work.CrauderKatz.CylinderChart

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

namespace Work.CrauderKatz

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

/-- **`chartHom` applied to the pullback of a global section.**  For an open immersion `z : Z ⟶ D`
with `D` irreducible and `Z` nonempty, the structure map `chartHom z : Γ(Z,⊤) ⟶ κ(D)` of the chart
`z` sends the pullback `z.appTop s` of a global section `s` of `D` to the image of `s` in `κ(D)`.

This is the compatibility of `chartHom` with the restriction of rational functions along the chart,
and is the form in which the `𝕜`-linearity of `chartHom` is used below: taking `s` to be the image
of a constant `c ∈ 𝕜` under `Γ(D,⊤)` (via the `Over` structure of `D`) exhibits `chartHom z ∘ ψ` as
the structure map `𝕜 ⟶ κ(D)` of `D`. -/
theorem chartHom_appTop {D Z : Scheme.{0}} [IrreducibleSpace D] [Nonempty Z] (z : Z ⟶ D)
    [IsOpenImmersion z] (s : Γ(D, ⊤)) [Nonempty (⊤ : D.Opens)] :
    chartHom z (Scheme.Hom.appTop z s) = D.germToFunctionField ⊤ s := by
  -- `(appIso z ⊤).inv ∘ z.appTop` is the restriction of global sections of `D` to the image of `z`.
  have hM : (Scheme.Hom.appIso z ⊤).inv (z.appTop s) =
      D.presheaf.map (homOfLE (le_top : z ''ᵁ ⊤ ≤ ⊤)).op s :=
    ConcreteCategory.congr_hom (Scheme.Hom.app_appIso_inv z ⊤) s
  simp only [Work.CrauderKatz.chartHom, Work.CrauderKatz.chartIso,
    Iso.trans_symm, Iso.trans_hom, Iso.symm_hom, Iso.symm_symm_eq, Iso.op_hom, Functor.mapIso_hom,
    eqToIso.hom, eqToIso.inv, eqToHom_op, CategoryTheory.eqToHom_map, ConcreteCategory.comp_apply,
    Scheme.Hom.appIso_hom, CategoryTheory.Functor.map_comp]
  rw [hM]
  simp only [Scheme.germToFunctionField]
  -- `eqToHom` commutes with the presheaf: it is the restriction along the equality of the two opens
  -- `z ''ᵁ ⊤ = Hom.opensRange z`.
  rw [← CategoryTheory.eqToHom_map D.presheaf
    (congrArg Opposite.op (Scheme.Hom.image_top_eq_opensRange z))]
  -- and the two successive restrictions are a single restriction, whence the same germ.
  rw [show (ConcreteCategory.hom (D.presheaf.map
        (eqToHom (congrArg Opposite.op (Scheme.Hom.image_top_eq_opensRange z)))))
        ((ConcreteCategory.hom (D.presheaf.map (homOfLE (le_top : z ''ᵁ ⊤ ≤ ⊤)).op)) s)
      = (ConcreteCategory.hom (D.presheaf.map
        ((homOfLE (le_top : z ''ᵁ ⊤ ≤ ⊤)).op ≫
          (eqToHom (congrArg Opposite.op (Scheme.Hom.image_top_eq_opensRange z)))))) s from by
    rw [← ConcreteCategory.comp_apply, ← CategoryTheory.Functor.map_comp]]
  rw [D.presheaf.germ_res_apply']

/-- **`chartHom` is the structure map `𝕜 ⟶ κ(D)` of the chart.**  Let `D` be an integral scheme
over `Spec 𝕜`, `z : Z ⟶ D` an affine chart (an open immersion with `Z` affine and nonempty), and
`ψ : 𝕜 →+* Γ(Z,⊤)` the ring map induced by `z` on global sections via the identification
`Z ≅ Spec Γ(Z,⊤)`.  Then the structure map `chartHom z : Γ(Z,⊤) ⟶ κ(D)` attached to the chart is
`𝕜`-linear for `ψ`, i.e. it is the structure map `𝕜 ⟶ κ(D)` of `D`. -/
theorem chartHom_algebraMap {𝕜 : Type} [Field 𝕜] {D Z : Scheme.{0}} [IrreducibleSpace D] [IsIntegral D] [IsAffine Z] [Nonempty Z] [D.Over (Spec (CommRingCat.of 𝕜))] (z : Z ⟶ D) [IsOpenImmersion z] (ψ : 𝕜 →+* Γ(Z,⊤)) (hz : z ≫ (D ↘ Spec (CommRingCat.of 𝕜)) = Z.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom ψ)) (c : 𝕜) : Work.CrauderKatz.chartHom z (ψ c) = Work.CrauderKatz.functionFieldResMap 𝕜 D c := by
  letI : Nonempty (⊤ : D.Opens) := ⟨⟨genericPoint D, trivial⟩⟩
  -- The hypothesis `hz` says exactly that `z.appTop` intertwines the two structure maps
  -- `𝕜 ⟶ Γ(D,⊤)` and `ψ : 𝕜 ⟶ Γ(Z,⊤)`; hence `ψ c` is the pullback of the global section
  -- `f.appTop (ΓSpecIso.inv c)` defining the constant `c` on `D`.
  have h1 : z.appTop ((D ↘ Spec (CommRingCat.of 𝕜)).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of 𝕜)).inv c)) = ψ c := by
    have hcong : (D ↘ Spec (CommRingCat.of 𝕜)).appTop ≫ z.appTop =
        (Spec.map (CommRingCat.ofHom ψ)).appTop ≫ Z.isoSpec.hom.appTop := by
      rw [← Scheme.Hom.comp_appTop z (D ↘ Spec (CommRingCat.of 𝕜)),
          ← Scheme.Hom.comp_appTop Z.isoSpec.hom (Spec.map (CommRingCat.ofHom ψ)), hz]
    rw [← ConcreteCategory.comp_apply, hcong, ConcreteCategory.comp_apply]
    have hZ1 : Z.isoSpec.hom.appTop = (Scheme.ΓSpecIso Γ(Z,⊤)).hom := by
      show Z.toSpecΓ.appTop = _
      exact Scheme.toSpecΓ_appTop Z
    rw [hZ1]
    -- naturality of `ΓSpecIso` identifies `(Spec.map ψ).appTop` with `ψ` on `𝕜 ⊂ Γ(Spec 𝕜,⊤)`.
    have hnat := congrArg (fun (φ : Γ(Spec (CommRingCat.of 𝕜),⊤) ⟶ Γ(Z,⊤)) =>
        φ ((Scheme.ΓSpecIso (CommRingCat.of 𝕜)).inv c))
        (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ψ))
    rw [← ConcreteCategory.comp_apply]
    refine hnat.trans ?_
    simp only [ConcreteCategory.comp_apply, CommRingCat.hom_ofHom, Iso.inv_hom_id_apply]
  rw [← h1, chartHom_appTop z ((D ↘ Spec (CommRingCat.of 𝕜)).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of 𝕜)).inv c))]
  -- `functionFieldResMap 𝕜 D` is by definition the germ of that global section.
  unfold Work.CrauderKatz.functionFieldResMap
  simp only [ConcreteCategory.comp_apply]

end Work.CrauderKatz
