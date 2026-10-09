import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.Interfaces
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The decomposition compositum `Ω^{D_A ⊓ G_K}` contains `K`

Small bookkeeping lemma for the finite-place route of the node `ext_sha2_bridge`: with
`H := SSGRoute.decomp k A ⊓ (SSGRoute.res k K).ker` (the decomposition group of the place `A` over
`K`), the fixed field `Ω^H` — the *decomposition compositum* `K·Ω^{D_A}` of the lead's
`_lead_design/flags_0030/NOTE.md` §2 — contains `K`, since `H ≤ Gal(Ω/K)`.

It is used to give the `↥K`-algebra structure on `↥(Ω^H)` that the level-change statement `(BC)`
and the push `(PUSH)` refer to, without invoking the (only finitely available) Galois
correspondence `Ω^{Gal(Ω/K)} = K`.
-/

namespace Work.SSGRoute.ExtChain

open CategoryTheory SSGRoute.PTExt

variable (k : Type) [Field k] {Ω : Type} [Field Ω] [Algebra k Ω]

/-- `K ≤ Ω^{D_A ⊓ Gal(Ω/K)}`: elements of `K` are fixed by the kernel of `res k K`, hence by the
intersection. -/
theorem le_fixedField_decomp_inf_ker (K : IntermediateField k Ω) [Normal k K]
    (A : ValuationSubring Ω) :
    K ≤ IntermediateField.fixedField (SSGRoute.decomp k A ⊓ (SSGRoute.res k K).ker) := by
  intro x hx
  rw [IntermediateField.mem_fixedField_iff]
  intro g hg
  have hgker : g ∈ (SSGRoute.res k K).ker := hg.2
  rw [MonoidHom.mem_ker] at hgker
  have h2 : (SSGRoute.res k K g) ⟨x, hx⟩ = ⟨x, hx⟩ := by rw [hgker]; rfl
  have h3 := congrArg Subtype.val h2
  simpa [SSGRoute.res, AlgEquiv.restrictNormalHom_apply] using h3

end Work.SSGRoute.ExtChain
