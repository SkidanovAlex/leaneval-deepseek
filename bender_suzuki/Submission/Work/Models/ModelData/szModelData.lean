import Mathlib
import Submission.Work.Models.Abstract.ModelData
import Submission.Work.Models.Port.BenderPairModels
import Submission.Work.Models.Port.Sz.Main
import Submission.Work.Models.Sz.szTS_comm
import Submission.Work.Models.Sz.szTS_eq_invertedBy
import Submission.Work.Models.Sz.ncard_involutions_szBorelS
import Submission.Work.Models.Sz.szTwoGroupS_inv_central

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Model data for `Sz(2^(2n+1))`

The model-data layer of `ModelFactsProp` (see `Work.Models.Abstract.ModelData`) asks for the
rank-one `(B,N)`-pair of a Bender group together with four model-specific facts.  For the Suzuki
family we take the Bender pair `Submission.Sz.szBenderPair`, whose torus is the diagonal torus
`T = szTS n`, and `K₀ = J(T,w) = T` (the whole torus is inverted by the Weyl element `w = szWgM n`).

The four extra facts are

* `T` is abelian (it is the image of the diagonal monoid homomorphism from the abelian group
  `(SzField n)ˣ`), `szTS_comm`;
* `w² = 1`, `szWgM_mul_self`;
* `T = invertedBy T w`, `szTS_eq_invertedBy`;
* `T` is cyclic, of order `q - 1 = 2^(2n+1) - 1`, which is also the number of involutions of the
  Borel subgroup (`card_szTS`, `isCyclic_szTS`, `ncard_involutions_szBorelS`);
* involutions of the unipotent radical `U = szTwoGroupS n` are central in `U`
  (`szTwoGroupS_inv_central`).
-/

namespace Work.Models.ModelData

open Matrix LeanEval.GroupTheory.Defs
open scoped Pointwise

/-- The Weyl element of `Sz(2^(2n+1))` is an involution. -/
theorem szWgM_mul_self (n : ℕ) : Submission.Sz.szWgM n * Submission.Sz.szWgM n = 1 := by
  apply Subtype.ext
  show (Submission.Sz.szWg n : GL (Fin 4) (Submission.Sz.SzField n)) *
      Submission.Sz.szWg n = 1
  exact Submission.Sz.szWg_mul_self n

/-- The maximal torus of `Sz(2^(2n+1))` is cyclic: it is the range of the (injective) diagonal
monoid homomorphism from the multiplicative group of the Suzuki field, which is cyclic. -/
theorem isCyclic_szTS (n : ℕ) : IsCyclic (Submission.Sz.szTS n) :=
  (Subgroup.subgroupOfEquivOfLe (Submission.Sz.szTgHom_range_le_szModel n)).isCyclic.mpr
    ((MonoidHom.ofInjective (Submission.Sz.szTgHom_injective n)).isCyclic.mp inferInstance)

/-- The maximal torus of `Sz(2^(2n+1))` has order `q - 1 = 2^(2n+1) - 1`. -/
theorem card_szTS (n : ℕ) : Nat.card ↥(Submission.Sz.szTS n) = 2 ^ (2 * n + 1) - 1 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (Submission.Sz.szTgHom_range_le_szModel n)).toEquiv,
    Submission.Sz.card_range_szTgHom, Submission.Sz.card_szField]

/-- **`Sz(2^(2n+1))` carries the model data of a simple Bender group.**  Every field of
`Work.Models.ModelData` is instantiated on the Bender pair `Submission.Sz.szBenderPair`, with the
torus `T = szTS n` playing the role of `K₀ = J(T,w)`: the Weyl element inverts all of `T`, so
`J(T,w) = T`, which is cyclic of order `q - 1 = #Inv(B)`. -/
theorem szModelData (n : ℕ) (hn : 1 ≤ n) :
    Nonempty (Work.Models.ModelData (LeanEval.GroupTheory.Defs.SzModel n)) := by
  refine ⟨{ Submission.Sz.szBenderPair n hn with
    K0 := Submission.Sz.szTS n
    hTab := Work.Models.Sz.szTS_comm n
    hww := szWgM_mul_self n
    hK0 := Work.Models.Sz.szTS_eq_invertedBy n
    hK0cyc := isCyclic_szTS n
    hK0card := by
      show Nat.card ↥(Submission.Sz.szTS n) =
        (Submission.Blueprint.involutions
          (Submission.Sz.szBorelS n : Set (LeanEval.GroupTheory.Defs.SzModel n))).ncard
      rw [card_szTS, Work.Models.Sz.ncard_involutions_szBorelS]
    hK0two := by
      rw [card_szTS]
      have h3 : 3 ≤ 2 ^ (2 * n + 1) := by
        calc 3 ≤ 2 ^ 3 := by norm_num
          _ ≤ 2 ^ (2 * n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    hUinv := Work.Models.Sz.szTwoGroupS_inv_central n }⟩

end Work.Models.ModelData
