import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
import Mathlib.RepresentationTheory.Homological.GroupHomology.LongExactSequence
import Submission.Work.SSGRoute.H1Dual.Defs
import Submission.Work.SSGRoute.H1Dual.cokerExtract
import Submission.Work.SSGRoute.H1Dual.dualCoker
import Submission.Work.SSGRoute.H1Dual.kerExtract
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open CategoryTheory
open CategoryTheory.Limits

namespace Work.SSGRoute.H1Dual

universe u

variable {k : Type u} [Field k] {G : Type u} [Group G] [Fintype G]

/-- `IsZero` is transported back along an isomorphism in `ModuleCat k`. -/
theorem isZero_of_iso {X Y : ModuleCat k} (e : X ≅ Y) (h : IsZero Y) : IsZero X := by
  rw [ModuleCat.isZero_iff_subsingleton] at h ⊢
  refine ⟨fun a b => ?_⟩
  obtain ⟨a', ha'⟩ := (Iso.toLinearEquiv e).symm.surjective a
  obtain ⟨b', hb'⟩ := (Iso.toLinearEquiv e).symm.surjective b
  rw [← ha', ← hb', h.elim a' b']

/-- **The homological dimension shift.** If `H₁(G, Coind M) = 0`, then `H₁(G,M)` is the kernel
of `H₀(G,M') → H₀(G,Coind M)`, where `M' = ker (Coind M → M)`. -/
theorem H1_ker_H0 (M : Rep k G) (hF : IsZero (groupHomology (coindRep k G M.V) 1)) :
    Nonempty (groupHomology.H1 M ≃ₗ[k]
      (ModuleCat.Hom.hom (groupHomology.mapShortComplex₁ (coindSES_shortExact M)
        (show 0 + 1 = 1 from rfl)).g).ker) := by
  classical
  set hS := coindSES_shortExact M with hSdef
  set S := groupHomology.mapShortComplex₁ hS (show 0 + 1 = 1 from rfl) with Sdef
  have hex : S.Exact := groupHomology.mapShortComplex₁_exact hS (show 0 + 1 = 1 from rfl)
  have hfg : (ModuleCat.Hom.hom S.f).range = (ModuleCat.Hom.hom S.g).ker :=
    (ShortComplex.moduleCat_exact_iff_range_eq_ker S).1 hex
  have hmono : Mono S.f := groupHomology.mono_δ_of_isZero hS 0 hF
  have hinj : (ModuleCat.Hom.hom S.f).ker = ⊥ :=
    LinearMap.ker_eq_bot.mpr ((ModuleCat.mono_iff_injective S.f).1 hmono)
  obtain ⟨e⟩ := kerExtract (ModuleCat.Hom.hom S.f) (ModuleCat.Hom.hom S.g) hfg hinj
  exact ⟨e⟩

/-- **The cohomological dimension shift.** If `H¹(G, Coind(M)^∨) = 0`, then `H¹(G,M^∨)` is the
cokernel of `H⁰(G,Coind(M)^∨) → H⁰(G,(M')^∨)`. -/
theorem H1_dual_coker (M : Rep k G) (hS : (dualSES M).ShortExact)
    (hF : IsZero (groupCohomology (dualRep (coindRep k G M.V)) 1)) :
    Nonempty ((groupCohomology.mapShortComplex₃ hS (show 0 + 1 = 1 from rfl)).X₃ ≃ₗ[k]
      ((groupCohomology.mapShortComplex₃ hS (show 0 + 1 = 1 from rfl)).X₂ ⧸
        (ModuleCat.Hom.hom (groupCohomology.mapShortComplex₃ hS
          (show 0 + 1 = 1 from rfl)).f).range)) := by
  classical
  set S := groupCohomology.mapShortComplex₃ hS (show 0 + 1 = 1 from rfl) with Sdef
  have hex : S.Exact := groupCohomology.mapShortComplex₃_exact hS (show 0 + 1 = 1 from rfl)
  have hfg : (ModuleCat.Hom.hom S.f).range = (ModuleCat.Hom.hom S.g).ker :=
    (ShortComplex.moduleCat_exact_iff_range_eq_ker S).1 hex
  have hepi : Epi S.g := groupCohomology.epi_δ_of_isZero hS 0 hF
  have hsurj : (ModuleCat.Hom.hom S.g).range = ⊤ :=
    LinearMap.range_eq_top.mpr ((ModuleCat.epi_iff_surjective S.g).1 hepi)
  obtain ⟨e⟩ := cokerExtract (ModuleCat.Hom.hom S.f) (ModuleCat.Hom.hom S.g) hfg hsurj
  exact ⟨e⟩

end Work.SSGRoute.H1Dual
