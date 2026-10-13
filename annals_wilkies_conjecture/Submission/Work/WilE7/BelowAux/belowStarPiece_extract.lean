import Mathlib
import Submission.Work.WilE7.BelowAux.BelowDefs
import Submission.Work.WilE7.star_proj
import Submission.Work.WilE7.reindex_component

namespace Work.WilE7.BelowAux

theorem belowStarPiece_extract
    {p m : ℕ} {X : WilkiesDesign.E.SemiPf (Work.WilE7.BelowAux.belowDim p m)}
    {q : Fin (Work.WilE7.BelowAux.belowDim p m) → ℝ}
    (e : Fin (Work.WilE7.BelowAux.belowDim p m) ≃
      Fin ((p + 1) + Work.WilE7.BelowAux.belowFib p m))
    (he : ∀ y : Fin ((p + 1) + Work.WilE7.BelowAux.belowFib p m) → ℝ,
      WilkiesDesign.E.projFirst (p + 1) (Work.WilE7.BelowAux.belowFib p m) y =
        Work.WilE7.BelowAux.belowExtract (fun i => y (e i))) :
    (⟨Work.WilE7.BelowAux.belowFib p m, Work.WilE7.SemiPf.reindex e X,
        (Work.WilE7.pullHomeo e).symm q⟩ : WilkiesDesign.E.StarPiece (p + 1)).set =
      Work.WilE7.BelowAux.belowExtract '' connectedComponentIn X.set q := by
  have hc := Work.WilE7.sp_reindex_component e X q
  show WilkiesDesign.E.projFirst (p + 1) (Work.WilE7.BelowAux.belowFib p m) ''
      connectedComponentIn (Work.WilE7.SemiPf.reindex e X).set
        ((Work.WilE7.pullHomeo e).symm q) = _
  rw [hc]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨Work.WilE7.pullHomeo e y, hy, (he y).symm⟩
  · rintro ⟨z, hz, rfl⟩
    refine ⟨(Work.WilE7.pullHomeo e).symm z, ?_, ?_⟩
    · rw [Set.mem_preimage, Homeomorph.apply_symm_apply]
      exact hz
    · rw [he ((Work.WilE7.pullHomeo e).symm z)]
      exact congrArg Work.WilE7.BelowAux.belowExtract
        (Homeomorph.apply_symm_apply (Work.WilE7.pullHomeo e) z)

end Work.WilE7.BelowAux
