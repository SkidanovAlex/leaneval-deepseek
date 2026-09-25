import Mathlib
import Submission.Work.CFTLib.RelShafReps
import Submission.Work.CFTLib.NKIdeles
import Submission.Work.CFTLib.RelShafDefs

/-!
# The two short exact sequences of the relative Shafarevich bound

For a finite Galois extension `K/F` of number fields, the four-term exact sequence
`1 → 𝒪_Kˣ → J_K → C_K → Cl(𝓞 K) → 1` of `ℤ[Gal(K/F)]`-modules is cut into two short exact
sequences at the intermediate module `C'' = im(J_K → C_K)`.  This file fixes the *interface*: a
structure carrying the intermediate module and the two short complexes, together with the
identification of their terms.  The construction is in `RelShafSES`.
-/

open scoped Classical
open NumberField CategoryTheory

noncomputable section

namespace Work.CFTLib

/-- **The two short exact sequences of the idèle sequence**
`1 → 𝒪_Kˣ → J_K → C_K → Cl(𝓞 K) → 1`.

`C''` is the image of the local-unit idèles in the idèle class group; `ses1` is the short complex
`𝒪_Kˣ → J_K → C''` and `ses2` the short complex `C'' → C_K → Cl(𝓞 K)`. -/
structure RelShafSESData (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K]
    [Algebra F K] [FiniteDimensional F K] [IsGalois F K] where
  /-- the image of the local-unit idèles in `C_K`. -/
  C'' : Rep ℤ (K ≃ₐ[F] K)
  /-- the short complex `𝒪_Kˣ → J_K → C''`. -/
  ses1 : ShortComplex (Rep ℤ (K ≃ₐ[F] K))
  /-- the first term of `ses1` is `𝒪_Kˣ`. -/
  ses1X1 : ses1.X₁ = oUnitsRep F K
  /-- the second term of `ses1` is `J_K`. -/
  ses1X2 : ses1.X₂ = jRep F K
  /-- the third term of `ses1` is `C''`. -/
  ses1X3 : ses1.X₃ = C''
  /-- `ses1` is short exact. -/
  ses1Exact : ses1.ShortExact
  /-- the short complex `C'' → C_K → Cl(𝓞 K)`. -/
  ses2 : ShortComplex (Rep ℤ (K ≃ₐ[F] K))
  /-- the first term of `ses2` is `C''`. -/
  ses2X1 : ses2.X₁ = C''
  /-- the second term of `ses2` is `C_K`. -/
  ses2X2 : ses2.X₂ = NK.GlobalCFT.IdeleClassGroup.rep F K
  /-- the third term of `ses2` is `Cl(𝓞 K)`. -/
  ses2X3 : ses2.X₃ = clRep F K
  /-- `ses2` is short exact. -/
  ses2Exact : ses2.ShortExact

end Work.CFTLib
