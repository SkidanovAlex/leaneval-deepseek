/-
# Proposition 3.8(2) of CKMRV for the ideal `𝓘_-`

CKMRV (Cohn--Kumar--Miller--Radchenko--Viazovska, Ann. of Math. 196 (2022)),
Proposition 3.8(2), for the right ideal
`𝓘_- = (S-I)R + (T-I)²R + (z-1)R` of `R = ℂ[SL(2,ℤ)]`, `z = -I` (this is the paper's
`(S-I)ℂ[PSL(2,ℤ)] + (T-I)²ℂ[PSL(2,ℤ)]` with the collapse ideal `(z-1)R` adjoined, since the
weights occurring in the paper are even): the images of `1, T, TS` are a basis of `R/𝓘_-`.

The proof is the paper's: part (1) of the proposition shows that the images of
`1, T, TS, S, ST, STS` are a basis of `R/𝓘` (`Work.Residues.basis_quotient_IdealI`), and
`S` acts on the left by `1` modulo `𝓘_-` (so the six elements reduce to `1, T, TS`, bounding
`dim R/𝓘_-` by `3`); the diagonal map `R/𝓘 → R/𝓘_+ × R/𝓘_-` is injective because
`𝓘_+ ∩ 𝓘_- = 𝓘`, which matches `6 = dim R/𝓘 ≤ dim R/𝓘_+ + dim R/𝓘_- ≤ 6` and forces
`dim R/𝓘_- = 3`.  The reduction argument is in `Work.Residues.IdealImAssembly`; a second
proof, using the paper's `σ`-representation for part (1) directly inside `R`
(`Work.Residues.basis_quotient_IdealI_rowDiff`, in `Work.Residues.IdealImRowDiffAll`), is
recorded as `basis_quotient_IdealIm_rowDiff` below.
-/
import Mathlib
import Submission.Work.Residues.Basic
import Submission.Work.Residues.IdealImAssembly
import Submission.Work.Residues.basis_quotient_IdealI
import Submission.Work.Residues.IdealImRowDiffAll

namespace Work.Residues

/-- **Paper Proposition 3.8(2)** for the ideal `𝓘_- = (S-I)R + (T-I)²R + (z-1)R`: the
images of `1, T, TS` are a basis of `R/𝓘_-`. -/
theorem basis_quotient_IdealIm :
    ∃ b : Module.Basis (Fin 3) ℂ (Work.Kernels.R ⧸ Work.Residues.idealIm),
      ∀ i, b i = Submodule.mkQ Work.Residues.idealIm (Work.Residues.M3 i) :=
  basis_IdealIm_of_basis_IdealI basis_quotient_IdealI

/-- The same statement, with part (1) of Proposition 3.8 supplied by the paper's
`σ`-representation argument carried out directly in `R = ℂ[SL(2,ℤ)]`
(`Work.Residues.basis_quotient_IdealI_rowDiff`) rather than by transferring the result from
`ℂ[Γ] = ℂ[PSL(2,ℤ)]`. -/
theorem basis_quotient_IdealIm_rowDiff :
    ∃ b : Module.Basis (Fin 3) ℂ (Work.Kernels.R ⧸ Work.Residues.idealIm),
      ∀ i, b i = Submodule.mkQ Work.Residues.idealIm (Work.Residues.M3 i) :=
  basis_IdealIm_of_basis_IdealI basis_quotient_IdealI_rowDiff

end Work.Residues
