import Mathlib
import Submission.Work.CWIND.Basic
import Submission.Work.CWIND.GClass.ExhSetup
import Submission.Work.CWIND.GClass.Prelim
import Submission.Work.CWIND.GClass.ExhMono
import Submission.Work.CWIND.GClass.CsingColim
import Submission.Work.CWIND.GClass.AexhColim

namespace Work.CWIND.GClass

open CategoryTheory CategoryTheory.Limits LightCondensed LightProfinite
open LightCondensed.Solid Submission.Blueprint

set_option backward.isDefEq.respectTransparency false

/-- **CWIND/T9 (the exhaustion field of the CW induction).**  If `X` is Hausdorff and
`A : ℕ → Set X` is an increasing sequence of subspaces such that every compact subset of `X` is
contained in some `A n`, and each `A n` lies in `GOf b`, then `X` lies in `GOf b` — REFS/05
section 2.  The singular chain complex and `A` both commute with the colimit
`X = ⋃ₙ A n` (a singular simplex, or a continuous map `S × Δⁿ → X` with `S` profinite, has compact
image), with monomorphic transition maps, so naturality of `b` and `ToolkitProp.seqColim` give the
solid-equivalence of `b(X)`. -/
theorem G_exhaust (hTK : ToolkitProp)
    (b : singularChainsLightCondAbComplexFunctor ⟶ AFunctor)
    (X : TopCat.{0}) [T2Space X] (A : ℕ → Set X) (hmono : Monotone A)
    (hcpt : ∀ K : Set X, IsCompact K → ∃ n, K ⊆ A n) (hG : ∀ n, GOf b (TopCat.of (A n))) :
    GOf b X := by
  obtain ⟨hC⟩ := CsingColim A hmono hcpt
  obtain ⟨hA⟩ := AexhColim A hmono hcpt
  obtain ⟨hmC, hmA⟩ := ExhMono A hmono
  refine ⟨inferInstance, ?_⟩
  have hseq : SolidEquiv (DerivedCategory.Q.map (colim.map (exhNat A hmono b))) :=
    hTK.seqColim (CsingExh A hmono) (Aexh A hmono) (exhNat A hmono b) hmC hmA
      (fun n => (hG n).2)
  set Φ := (colimit.isColimit (CsingExh A hmono)).coconePointUniqueUpToIso hC with hΦ
  set Ψ := (colimit.isColimit (Aexh A hmono)).coconePointUniqueUpToIso hA with hΨ
  have hΦι : ∀ n, colimit.ι (CsingExh A hmono) n ≫ Φ.hom =
      singularChainsLightCondAbComplexFunctor.map (Submission.Blueprint.inclTop (A n)) :=
    fun n => IsColimit.comp_coconePointUniqueUpToIso_hom _ _ n
  have hΨι : ∀ n, colimit.ι (Aexh A hmono) n ≫ Ψ.hom =
      AFunctor.map (Submission.Blueprint.inclTop (A n)) :=
    fun n => IsColimit.comp_coconePointUniqueUpToIso_hom _ _ n
  have hsquare : Φ.hom ≫ b.app X = colim.map (exhNat A hmono b) ≫ Ψ.hom := by
    apply IsColimit.hom_ext (colimit.isColimit (CsingExh A hmono))
    intro n
    calc (colimit.cocone (CsingExh A hmono)).ι.app n ≫ (Φ.hom ≫ b.app X)
        = (colimit.ι (CsingExh A hmono) n ≫ Φ.hom) ≫ b.app X := (Category.assoc _ _ _).symm
      _ = singularChainsLightCondAbComplexFunctor.map (Submission.Blueprint.inclTop (A n)) ≫
            b.app X := by rw [hΦι n]
      _ = b.app (TopCat.of (A n)) ≫ AFunctor.map (Submission.Blueprint.inclTop (A n)) :=
            b.naturality (Submission.Blueprint.inclTop (A n))
      _ = b.app (TopCat.of (A n)) ≫ (colimit.ι (Aexh A hmono) n ≫ Ψ.hom) := by rw [hΨι n]
      _ = (b.app (TopCat.of (A n)) ≫ colimit.ι (Aexh A hmono) n) ≫ Ψ.hom :=
            (Category.assoc _ _ _).symm
      _ = ((exhNat A hmono b).app n ≫ colimit.ι (Aexh A hmono) n) ≫ Ψ.hom := rfl
      _ = (colimit.ι (CsingExh A hmono) n ≫ colim.map (exhNat A hmono b)) ≫ Ψ.hom := by
            rw [← colimit.ι_map (exhNat A hmono b) n]
      _ = (colimit.cocone (CsingExh A hmono)).ι.app n ≫
            (colim.map (exhNat A hmono b) ≫ Ψ.hom) := Category.assoc _ _ _
  have hb : b.app X = Φ.inv ≫ colim.map (exhNat A hmono b) ≫ Ψ.hom := by
    calc b.app X = (Φ.inv ≫ Φ.hom) ≫ b.app X := by rw [Iso.inv_hom_id, Category.id_comp]
      _ = Φ.inv ≫ (Φ.hom ≫ b.app X) := Category.assoc _ _ _
      _ = Φ.inv ≫ (colim.map (exhNat A hmono b) ≫ Ψ.hom) := by rw [hsquare]
      _ = Φ.inv ≫ colim.map (exhNat A hmono b) ≫ Ψ.hom := (Category.assoc _ _ _).symm
  rw [hb, Functor.map_comp, Functor.map_comp]
  exact hTK.comp _ _ (hTK.of_iso _ inferInstance)
    (hTK.comp _ _ hseq (hTK.of_iso _ inferInstance))

end Work.CWIND.GClass
