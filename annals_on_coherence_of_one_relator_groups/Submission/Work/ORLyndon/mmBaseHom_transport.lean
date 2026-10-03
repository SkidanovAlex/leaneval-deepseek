import Mathlib
import Submission.Work.ORLyndon.mmConnDefs
import Submission.Work.ORLyndon.base_regularity_transport_of_le

/-!
# Transport of regularity along the canonical map from the Magnus base

`Work.OROneRel.mmBaseHom : ⟨mmBeta t r | mmW t r⟩ →* ⟨α | r⟩` (`eps t r = 0`) is the canonical map
of the Magnus step, `(x, k) ↦ t ^ k * x * t ^ (-k)`.  It is **injective** whenever `r` is a
cyclically reduced nontrivial relator with `z ∈ relatorLetters r` and `eps z r = 0`
(`Work.OROneRel.mmBaseHom_injective`).

This file records the consequence used by the Cohen--Lyndon induction: **regularity is transported**.
If `Y ∈ K[⟨mmBeta t r | mmW t r⟩]` is a right non-zero-divisor, then so is its image in `K[⟨α | r⟩]`
along `mmBaseHom`:

* `Work.ORLyndon.mmBaseHom_transport` -- `∀ c, c * Y = 0 → c = 0` implies
  `∀ c, c * mapDomainRingHom K (mmBaseHom …) Y = 0 → c = 0`.

The proof is `Work.ORLyndon.base_regularity_transport_of_le` with the subgroup `N = ⊤`: no
hypothesis on the *support* of `c` is needed, and indeed the support hypothesis of that lemma is
redundant.  Stating the transport separately keeps the application of the injective map
`mmBaseHom` -- and hence all the elaboration of its (large) definition -- confined to this small
module.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ORLyndon

open MonoidAlgebra

/-- **Transport of right-regularity along `mmBaseHom`.** -/
theorem mmBaseHom_transport {α : Type*} [DecidableEq α] {K : Type*} [Field K]
    {t : α} {r : FreeGroup α} (he : Work.OROneRel.eps t r = 0)
    (hm : Function.Injective (Work.OROneRel.mmBaseHom (t := t) (r := r) he))
    (Y : MonoidAlgebra K (Work.OROneRel.mmH t r))
    (hY : ∀ c : MonoidAlgebra K (Work.OROneRel.mmH t r), c * Y = 0 → c = 0) :
    ∀ c : MonoidAlgebra K (OneRelatorGroup r),
      c * MonoidAlgebra.mapDomainRingHom K
        (Work.OROneRel.mmBaseHom (t := t) (r := r) he) Y = 0 → c = 0 :=
  fun c hcY => base_regularity_transport_of_le (Work.OROneRel.mmBaseHom (t := t) (r := r) he)
    hm ⊤ le_top Y hY c (fun _ _ => trivial) hcY

end Work.ORLyndon
