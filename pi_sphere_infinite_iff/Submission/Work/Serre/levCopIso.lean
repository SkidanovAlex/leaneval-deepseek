import Mathlib
import Submission.Work.Serre.LevCopDefs

namespace Work.Serre

open CategoryTheory Limits

/-- The coproduct of a family of homological complexes of `ℤ`-modules is computed degreewise,
i.e. it is the levelwise coproduct `levCop K`. -/
theorem levCopIso {ι : Type} {c : ComplexShape ℕ} (K : ι → HomologicalComplex (ModuleCat ℤ) c) :
    Nonempty ((∐ K) ≅ levCop K) := by
  classical
  -- The cocone exhibiting `levCop K` as the coproduct of the `K i`.
  let s : Cocone (Discrete.functor K) := Cofan.mk (levCop K) (fun i => levCopι K i)
  have hs : IsColimit s := by
    apply HomologicalComplex.isColimitOfEval (Discrete.functor K) s
    intro n
    -- In degree `n` the complex `levCop K` is the coproduct of the `(K i).X n`.
    let f : ι → ModuleCat ℤ := fun i => (K i).X n
    -- The diagram `Discrete.functor K ⋙ eval _ c n` is the discrete diagram on the family `f`.
    let e : Discrete.functor K ⋙ HomologicalComplex.eval (ModuleCat ℤ) c n ≅ Discrete.functor f :=
      Discrete.natIso (fun i => Iso.refl _)
    -- The coproduct cofan over `f`, with its point written as the point of the degreewise cocone.
    let c₂ : Cofan f := Cofan.mk ((HomologicalComplex.eval (ModuleCat ℤ) c n).mapCocone s).pt
      (fun i => Sigma.ι f i)
    have hc₂ : IsColimit c₂ :=
      IsColimit.ofIsoColimit (coproductIsCoproduct f)
        (Cofan.ext (Iso.refl _) (fun i => Category.comp_id _))
    have hG : IsColimit ((Cocone.precompose e.hom).obj c₂) :=
      (IsColimit.precomposeHomEquiv e c₂).symm hc₂
    refine IsColimit.ofIsoColimit (r := (Cocone.precompose e.hom).obj c₂) hG ?_
    refine Cocone.ext (Iso.refl _) ?_
    intro j
    simp only [Cocone.precompose_obj_pt, Cocone.precompose_obj_ι, Iso.refl_hom,
      Functor.mapCocone_ι_app, Category.comp_id]
    rfl
  exact ⟨IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) hs⟩

end Work.Serre
