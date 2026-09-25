import Mathlib
import Submission.CFTLib.Interfaces
import Submission.Work.CFTLib.Basic
import Submission.Work.CFTLib.GaloisAut.exists_algEquiv_comp_eq

open NumberField
open scoped Classical nonZeroDivisors

namespace Work.CFTLib

theorem le_of_isMaximalUnramified {F K : Type} [Field F] [NumberField F] [Field K]
    [NumberField K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K] (p : ℕ) [Fact p.Prime]
    (T : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
    (hMax : CFTLib.IsMaximalUnramified F K p T)
    (ψ : K →ₐ[F] AlgebraicClosure F)
    (M : IntermediateField F (AlgebraicClosure F)) [FiniteDimensional F M] [IsGalois F M]
    [NumberField ↥M]
    (hMp : IsPGroup p (M ≃ₐ[F] M)) (hMunr : CFTLib.IsUnramified F ↥M)
    (hMsplit : CFTLib.SplitsAt F ↥M T) : M ≤ ψ.fieldRange := by
  obtain ⟨φ⟩ : Nonempty (↥M →ₐ[F] K) := hMax ↥M hMp hMunr hMsplit
  obtain ⟨σ, hσ⟩ := Work.CFTLib.GaloisAut.exists_algEquiv_comp_eq (F := F)
    (A := AlgebraicClosure F) (M := ↥M)
    (M.val : ↥M →ₐ[F] AlgebraicClosure F) ((ψ.comp φ) : ↥M →ₐ[F] AlgebraicClosure F)
  -- (1) the σ-image of `M` lies in the embedding of `K`
  have h2 : M.map (σ : AlgebraicClosure F →ₐ[F] AlgebraicClosure F) ≤ ψ.fieldRange := by
    rintro x ⟨y, hy, rfl⟩
    change (σ : AlgebraicClosure F →ₐ[F] AlgebraicClosure F) y ∈ ψ.fieldRange
    have hy' : (σ : AlgebraicClosure F →ₐ[F] AlgebraicClosure F) y = ψ (φ ⟨y, hy⟩) := by
      have := congrArg (fun f : ↥M →ₐ[F] AlgebraicClosure F => f ⟨y, hy⟩) hσ
      simpa using this
    rw [hy']
    exact ⟨φ ⟨y, hy⟩, rfl⟩
  -- (2) σ preserves the (Galois) image of `K`
  have hK'gal : IsGalois F ↥(ψ.fieldRange) := IsGalois.of_algEquiv ψ.equivFieldRange
  have hfix : (ψ.fieldRange).map (σ : AlgebraicClosure F →ₐ[F] AlgebraicClosure F) =
      ψ.fieldRange := by
    haveI : Normal F ↥(ψ.fieldRange) := hK'gal.to_normal
    have h := AlgHom.fieldRange_of_normal
      (((σ : AlgebraicClosure F →ₐ[F] AlgebraicClosure F)).comp (ψ.fieldRange).val)
    rwa [← AlgHom.map_fieldRange (ψ.fieldRange).val
      (σ : AlgebraicClosure F →ₐ[F] AlgebraicClosure F),
      IntermediateField.fieldRange_val] at h
  -- (3) conclude
  intro x hx
  have hσx : (σ : AlgebraicClosure F →ₐ[F] AlgebraicClosure F) x ∈ ψ.fieldRange :=
    h2 ⟨x, hx, rfl⟩
  have hmem : (σ : AlgebraicClosure F →ₐ[F] AlgebraicClosure F) x ∈
      (ψ.fieldRange).map (σ : AlgebraicClosure F →ₐ[F] AlgebraicClosure F) := by
    rw [hfix]
    exact hσx
  obtain ⟨y, hy, hyx⟩ := hmem
  have hyx' : y = x := (σ : AlgebraicClosure F →ₐ[F] AlgebraicClosure F).injective hyx
  rwa [← hyx']

end Work.CFTLib
