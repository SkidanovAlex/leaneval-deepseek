import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Submission.NK.LocalAnabelian.Kummer.Defs
import Submission.NK.LocalAnabelian.ResidueChar.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Classical
open IntermediateField

namespace NK.LocalAnabelian

noncomputable section

/-- **The local arithmetic data of a `p`-adic field, in the form in which the
Neukirch–Uchida local input uses it.**

`κ` is the local field, `K'` a separable closure of it, `p` the residue
characteristic, `d` the absolute degree `[κ : ℚ_p]`, and `δ` the indicator of
`ζ_p ∈ κ`. -/
structure PadicGaloisInputs (p d δ : ℕ) (κ K' : Type*) [Field κ] [Field K'] [Algebra κ K']
    [IsSepClosure κ K'] : Prop where
  hp : p.Prime
  hδ : δ ≤ 1
  /-- `κ` contains a primitive `p`-th root of unity exactly when `δ = 1`. -/
  zeta_iff : (δ = 1) ↔ ∃ ζ : κ, IsPrimitiveRoot ζ p
  /-- The structure theory of `κˣ`: `|κˣ/(κˣ)^p| = p^{d+1+δ}`.  For `κ = ℚ_p` this is
  `Commons.NumberTheory.NumberField.Completion.natCard_powerQuotient_adicCompletion_rat_units`;
  see `NK.LocalAnabelian.natCard_KummerGroup_rat_adic`. -/
  powerQuotient_card : Nat.card (KummerGroup p κ) = p ^ (d + 1 + δ)
  /-- **Local reciprocity.**  The abelianised pro-`p` part of `Gal(κ̄/κ)` is
  `ℤ_p^d × (ℤ/p)^δ`, i.e. there are `(p^{d+1+δ} - 1)/(p - 1)` cyclic degree-`p`
  extensions of `κ`. -/
  abelian_rank : HasAbelianFrattiniRank p (d + 1 + δ) (Gal(K'/κ))
  /-- The `p`-torsion of the abelianisation detects `ζ_p ∈ κ` (it is `μ_κ[p]`). -/
  p_torsion_iff : (δ = 1) ↔ HasPTorsionAbelianization p (Gal(K'/κ))
  /-- **Ivanov's detection of the residue characteristic.** -/
  residueChar_detected : ResidueCharDetectedBy p (Gal(K'/κ))

end

end NK.LocalAnabelian
