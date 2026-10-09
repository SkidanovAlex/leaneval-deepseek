import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.LTDDefs.Basic
import Submission.Work.SSGRoute.DualMod.Main
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Vocabulary for the `μ_p` case of local Tate duality

Support definitions for the two reductions of the local `μ_p` dimension equality
(`Work.SSGRoute.local_tate_duality_mup_dim`):

* `mup.decompField k Ω A` — the **decomposition field** of a place `A`, i.e. the fixed field
  `Ω^{D_A}` of the decomposition group `D_A = SSGRoute.decomp k A`; its absolute Galois group is
  `D_A` (the stabiliser of a place is closed), so Kummer theory over this field is Kummer theory
  for `D_A`.
* `mup.KummerGroup p F` — the `p`-Kummer group `Fˣ ⧸ (Fˣ)^p` of a field `F`.
* `mup.TrivMod p G` — the **trivial rank-one `𝔽_p`-module with a trivial `G`-action**, i.e. the
  coefficient module obtained from `DualMod p (DualMod p T ⊗ T)` after the identification
  `DualMod p T ⊗ T ≅ 𝔽_p`.  It is a wrapper around `ZMod p` carrying the typeclass instances
  (`AddCommGroup`, `Module (ZMod p)`, `DistribMulAction G`, `SMulCommClass G (ZMod p)`) that
  `H1loc` needs.

The two reductions are `Work.SSGRoute.h1loc_mup_card_kummer` (Kummer theory for `D_A` over the
decomposition field) and `Work.SSGRoute.h1loc_triv_card_abelianization` (the trivial-module
identification `H¹(D_A, 𝔽_p) = Hom(D_A, 𝔽_p)`, i.e. the `p`-Frattini rank of `D_A^{ab}`), and the
arithmetic input is `Work.SSGRoute.local_reciprocity_mod_p_frattini_rank` (local Artin reciprocity
modulo `p` for the completion of a number field at a finite prime).
-/

open scoped Classical Pointwise
open Classical

namespace Work.SSGRoute

noncomputable section

namespace mup

/-- **The decomposition field** of a place `A` of `Ω` over `k`: the fixed field `Ω^{D_A}` of the
decomposition group. -/
abbrev decompField (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] (A : ValuationSubring Ω) :
    IntermediateField k Ω := IntermediateField.fixedField (SSGRoute.decomp k A)

/-- The **`p`-Kummer group** of a field: `Fˣ ⧸ (Fˣ)^p`. -/
abbrev KummerGroup (p : ℕ) (F : Type) [Field F] : Type :=
  Fˣ ⧸ (MonoidHom.range (powMonoidHom p))

/-- **The trivial rank-one `𝔽_p`-module with trivial group action**, used as the coefficient
module of the second variable of local Tate duality after the identification
`DualMod p (DualMod p T ⊗ T) ≅ 𝔽_p`.  It is `ZMod p` equipped with the trivial `G`-action. -/
abbrev TrivMod (p : ℕ) (G : Type) : Type := ZMod p

namespace TrivMod

variable {p : ℕ} {G : Type}

/-- The trivial `G`-action on `𝔽_p`. -/
instance instDistribMulAction [Group G] : DistribMulAction G (TrivMod p G) where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

/-- The scalar actions of `G` (trivially) and of `𝔽_p` commute. -/
instance instSMulCommClass [Group G] : SMulCommClass G (ZMod p) (TrivMod p G) where
  smul_comm _ _ _ := rfl

end TrivMod

end mup

end

end Work.SSGRoute
