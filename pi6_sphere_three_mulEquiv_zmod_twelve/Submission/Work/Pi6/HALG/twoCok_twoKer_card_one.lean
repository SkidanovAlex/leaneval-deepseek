import Mathlib
import Submission.Work.Pi6.HALG.defs
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

namespace Work.Pi6.HALG

/-- A trivial `ℤ`-module: both `M/2M` and `M[2]` are trivial.

`twoKer M = ModuleCat.of ℤ (LinearMap.ker (mulTwo M).hom)` and
`twoCok M = ModuleCat.of ℤ (↥M ⧸ LinearMap.range (mulTwo M).hom)` are from
`Submission/Work/Pi6/HALG/defs.lean`. `Subsingleton ↥M` makes both the kernel (a subtype of `↥M`)
and the quotient of `↥M` subsingleton and nonempty; `Nat.card_eq_one_iff_unique` then gives
`Nat.card = 1`. (Instance search does not find `Subsingleton ↥(twoKer M)` /
`Subsingleton ↥(twoCok M)` by itself, so the proof has to supply them explicitly.) -/
theorem twoCok_twoKer_card_one {M : ModuleCat ℤ} (hM : Subsingleton ↥M) :
    Nat.card ↥(twoCok M) = 1 ∧ Nat.card ↥(twoKer M) = 1 := by
  haveI : Subsingleton ↥M := hM
  constructor
  · -- `M/2M` is a quotient of the trivial module `↥M`, hence trivial.
    haveI : Subsingleton ↥(twoCok M) := Quotient.instSubsingletonQuotient _
    exact Nat.card_unique
  · -- `M[2]` is a submodule of the trivial module `↥M`, hence trivial.
    haveI : Subsingleton ↥(twoKer M) := ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
    exact Nat.card_unique

end Work.Pi6.HALG
