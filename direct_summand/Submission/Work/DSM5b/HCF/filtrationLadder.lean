import Mathlib
import Submission.Work.DSM5b.HCF.Complex

universe u

namespace Work.DSM5b.HCF

/-- **The comparison map `toStc` is a morphism of the two filtration short exact sequences.**
There is a morphism of short complexes from the honest row
`0 → C(𝒜_{≥k+1}) → C(𝒜_{≥k}) → C(𝒜_{=k}) → 0` to the sorted row, whose three components are the
comparison morphisms `toStcHom (𝒜_{≥k+1})`, `toStcHom (𝒜_{≥k})` and `toStcHom (𝒜_{=k})`.
Route: `ShortComplex.homMk` with the two commutation squares given by the naturality of `toStcHom`
(`Work.DSM5b.toStcHom_natural`, proved), applied to `subInclHom 𝒜 k` and `subQuotHom 𝒜 k`
(note the orientation: `toStcHom_natural f : htcHom f ≫ toStcHom _ = toStcHom _ ≫ stcHom f`). -/
theorem filtrationLadder {R : Type u} [CommRing R] {ι : Type u} [DecidableEq ι] [LinearOrder ι]
    (𝒜 : Work.DSM5b.CoeffSys R ι) (k : ℕ) :
    ∃ φ : (CategoryTheory.ShortComplex.mk (Work.DSM5b.htcHom (Work.DSM5b.CoeffSys.subInclHom 𝒜 k))
          (Work.DSM5b.htcHom (Work.DSM5b.CoeffSys.subQuotHom 𝒜 k))
          (Work.DSM5b.htc_subIncl_comp_subQuot 𝒜 k)) ⟶
        (CategoryTheory.ShortComplex.mk (Work.DSM5b.stcHom (Work.DSM5b.CoeffSys.subInclHom 𝒜 k))
          (Work.DSM5b.stcHom (Work.DSM5b.CoeffSys.subQuotHom 𝒜 k))
          (Work.DSM5b.stcSubIncl_comp_subQuot 𝒜 k)),
      φ.τ₁ = Work.DSM5b.toStcHom (Work.DSM5b.CoeffSys.subCF 𝒜 (k + 1)) ∧
      φ.τ₂ = Work.DSM5b.toStcHom (Work.DSM5b.CoeffSys.subCF 𝒜 k) ∧
      φ.τ₃ = Work.DSM5b.toStcHom (Work.DSM5b.CoeffSys.exactlyCoeff 𝒜 k) := by
  refine ⟨CategoryTheory.ShortComplex.homMk
      (Work.DSM5b.toStcHom (Work.DSM5b.CoeffSys.subCF 𝒜 (k + 1)))
      (Work.DSM5b.toStcHom (Work.DSM5b.CoeffSys.subCF 𝒜 k))
      (Work.DSM5b.toStcHom (Work.DSM5b.CoeffSys.exactlyCoeff 𝒜 k)) ?_ ?_, ?_, ?_, ?_⟩
  · exact (Work.DSM5b.toStcHom_natural (Work.DSM5b.CoeffSys.subInclHom 𝒜 k)).symm
  · exact (Work.DSM5b.toStcHom_natural (Work.DSM5b.CoeffSys.subQuotHom 𝒜 k)).symm
  · rfl
  · rfl
  · rfl

end Work.DSM5b.HCF
