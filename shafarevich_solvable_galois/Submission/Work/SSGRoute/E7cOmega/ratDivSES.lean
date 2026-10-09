import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.E7cOmega.ratDivDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The coefficient short exact sequence `0 → ℤ → ℚ → ℚ/ℤ → 0` in `Rep Coeff G`

Second piece of the local-duality infrastructure for
`Work.SSGRoute.E7cOmega.exists_level_unramified_detecting_class`.  The objects `ℤ`, `ℚ`, `ℚ/ℤ` are
the trivial `Coeff`-representations of `ratDivDefs.lean` (`unitRep`, `ratRep`, `divRep`), and
`ℤ ⊆ ℚ` is the range of the coefficient inclusion, so the quotient map `zSpan.mkQ` is
`Coeff`-linear by construction.

Consumed by: the connecting map `Hom_G(M, ℚ/ℤ) → Ext¹_G(M, ℤ)`
(`Abelian.Ext.covariant_sequence_exact₁/₂`), which yields the finite-group Tate duality
`Ext¹_G(M,ℤ) ≅ Hom_G(M,ℚ/ℤ)`, and by the pairing formula `levelPair … φ (res h) = δ(μ ∘ h)`.
-/

open CategoryTheory SSGRoute.PTExt

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

attribute [local instance 10000] Rep.hV2 Rep.hV1 Submodule.module

namespace Work.SSGRoute.E7cOmega

variable {G : Type} [Group G]

/-- `ℤ ↪ ℚ` as a morphism of trivial `Coeff`-representations of `G`. -/
noncomputable def unitToRat : SSGRoute.PTExt.unitRep G ⟶ ratRep G :=
  Rep.ofHom { toLinearMap := unitToRatLin, isIntertwining' := fun _ => rfl }

/-- `ℚ ↠ ℚ/ℤ` as a morphism of trivial `Coeff`-representations of `G`. -/
noncomputable def ratToDiv : ratRep G ⟶ divRep G :=
  Rep.ofHom { toLinearMap := zSpan.mkQ, isIntertwining' := fun _ => rfl }

/-- **The short complex** `0 → ℤ → ℚ → ℚ/ℤ → 0` in `Rep Coeff G`. -/
noncomputable def ratDivSES : ShortComplex (Rep.{0} SSGRoute.PTExt.Coeff G) :=
  ShortComplex.mk (unitToRat (G := G)) (ratToDiv (G := G)) (by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro c
    rw [Rep.hom_comp]
    show zSpan.mkQ (unitToRatLin c) = 0
    have hmem : unitToRatLin c ∈ zSpan := ⟨c, rfl⟩
    have h : zSpan.mkQ (unitToRatLin c) = zSpan.mkQ 0 :=
      (Submodule.Quotient.eq (p := zSpan) (x := unitToRatLin c) (y := 0)).mpr (by
        simpa using hmem)
    simpa using h)

@[simp] lemma ratDivSES_X₁ : (ratDivSES (G := G)).X₁ = SSGRoute.PTExt.unitRep G := rfl
@[simp] lemma ratDivSES_X₂ : (ratDivSES (G := G)).X₂ = ratRep G := rfl
@[simp] lemma ratDivSES_X₃ : (ratDivSES (G := G)).X₃ = divRep G := rfl

/-- **The coefficient sequence is short exact.** -/
theorem ratDivSES_shortExact : (ratDivSES (G := G)).ShortExact where
  exact :=
    (forget₂ (Rep SSGRoute.PTExt.Coeff G) (ModuleCat SSGRoute.PTExt.Coeff)).reflects_exact_of_faithful _
      ((ShortComplex.moduleCat_exact_iff _).2 fun x hx => by
        have hx0 : zSpan.mkQ (x : ℚ) = 0 := hx
        have hmem : (x : ℚ) ∈ zSpan := by
          have hker : (x : ℚ) ∈ LinearMap.ker (zSpan.mkQ) :=
            (LinearMap.mem_ker (f := zSpan.mkQ)).mp hx0
          rwa [Submodule.ker_mkQ] at hker
        obtain ⟨c, hc⟩ := LinearMap.mem_range.mp hmem
        exact ⟨c, hc⟩)
  mono_f := (Rep.mono_iff_injective _).2 fun x y h => by
    have h' : ((x.down : ℤ) : ℚ) = ((y.down : ℤ) : ℚ) := h
    exact ULift.down_inj.mp (Int.cast_injective h')
  epi_g := (Rep.epi_iff_surjective _).2 fun z => by
    obtain ⟨q, hq⟩ := zSpan.mkQ_surjective z
    exact ⟨q, hq⟩

/-- **The existence form**, for consumers that want it as an existential. -/
theorem ratDivSES_exists (G : Type) [Group G] :
    ∃ S : CategoryTheory.ShortComplex (Rep.{0} SSGRoute.PTExt.Coeff G),
      S.X₁ = SSGRoute.PTExt.unitRep G ∧
      S.X₂ = Work.SSGRoute.E7cOmega.ratRep G ∧
      S.X₃ = Work.SSGRoute.E7cOmega.divRep G ∧
      S.ShortExact :=
  ⟨ratDivSES (G := G), rfl, rfl, rfl, ratDivSES_shortExact (G := G)⟩

end Work.SSGRoute.E7cOmega
