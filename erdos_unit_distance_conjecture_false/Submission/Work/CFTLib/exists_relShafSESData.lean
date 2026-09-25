import Mathlib
import Submission.Work.CFTLib.RelShafSESConstruct
import Submission.Work.CFTLib.NKIdeles

/-!
# Existence of the relative Shafarevich short exact sequences

`Work.CFTLib.RelShafSESData F K` bundles the two short exact sequences of `ℤ[Gal(K/F)]`-modules

`1 → 𝒪_Kˣ → J_K → C'' → 1`,  `1 → C'' → C_K → Cl(𝓞 K) → 1`

cut out of the four-term idèle sequence `1 → 𝒪_Kˣ → J_K → C_K → Cl(𝓞 K) → 1` at
`C'' = im(J_K → C_K)`.  This file assembles the existence statement from the construction in
`Submission.Work.CFTLib.RelShafSESConstruct`.
-/

open scoped Classical
open NumberField CategoryTheory

noncomputable section

namespace Work.CFTLib

/-- **There exist the two short exact sequences of the relative Shafarevich bound.** -/
theorem exists_relShafSESData {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K]
    [Algebra F K] [FiniteDimensional F K] [IsGalois F K] :
    Nonempty (Work.CFTLib.RelShafSESData F K) :=
  ⟨{ C'' := RelShafSES.Cpp F K
     ses1 := RelShafSES.ses1 F K
     ses1X1 := rfl
     ses1X2 := rfl
     ses1X3 := rfl
     ses1Exact := RelShafSES.ses1_shortExact F K
     ses2 := RelShafSES.ses2 F K
     ses2X1 := rfl
     ses2X2 := rfl
     ses2X3 := rfl
     ses2Exact := RelShafSES.ses2_shortExact F K }⟩

end Work.CFTLib

end
