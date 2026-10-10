import Mathlib
import Submission.Work.MotV.Defs
import Submission.Work.MotT.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
open scoped WithZero

/-!
# The bridge from the generic T-twist layer (`Work.MotT`) to route V (`Work.MotV`)

The generic T-twist chapter `Submission/Work/MotT` proves the twist lemmas for an **arbitrary**
base field `K` and twist parameter `h ∈ Kˣ`, in particular

* `Work.MotT.twistFieldTK_regular` — `K` is algebraically closed in the twist field
  (`Work.MotT.twistFieldTK D h`), i.e. route V's node REG;
* `Work.MotT.constantsOnly_twistK` — constants-only of the twist field, i.e. route V's node CO;
* `Work.MotT.rigidityK` — non-isomorphism of the twist fields of `π` and `π²` for a uniformizer
  `π`, i.e. (part of) route V's node RIG;
* `Work.MotT.twistFieldT_algEquiv` — the identification
  `Work.MotV.twistFieldT D h ≃ₐ[RatFunc 𝕜] Work.MotT.twistFieldTK (kleinDataBaseChange D (RatFunc 𝕜)) h`.

This file contains the *transport* half of that bridge: it shows that each of route V's nodes
follows from the corresponding generic statement once the two fields are identified.  With the
generic nodes proved, route V's REG and CO become one-line corollaries; the remaining bridge work
is RIG, whose `𝕜`-linear form needs in addition the `K`-linearity upgrade of node NAT
(`Work.MotV.twist_natural`), see the report of this area.
-/

noncomputable section

namespace Work.MotV

/-- **Transport of the regularity node.**  If `K` is algebraically closed in `F₂` and
`F₁ ≃ₐ[K] F₂`, then `K` is algebraically closed in `F₁`. -/
theorem twist_regular_of_algEquiv {K F₁ F₂ : Type} [Field K] [Field F₁] [Field F₂]
    [Algebra K F₁] [Algebra K F₂] (e : F₁ ≃ₐ[K] F₂)
    (h₂ : ∀ r : F₂, IsAlgebraic K r → ∃ c, algebraMap K F₂ c = r) :
    ∀ r : F₁, IsAlgebraic K r → ∃ c, algebraMap K F₁ c = r := by
  intro r hr
  have hmap : IsAlgebraic K (e r) :=
    hr.ringHom_of_comp_eq (RingHom.id K) (e : F₁ →+* F₂) Function.injective_id
      (by ext x; exact (e.commutes x).symm)
  obtain ⟨c, hc⟩ := h₂ (e r) hmap
  exact ⟨c, e.injective (by rw [e.commutes, hc])⟩

/-- **Transport of the constants-only node.**  If `F₂` is constants-only over `𝕜` and
`F₁ ≃ₐ[RatFunc 𝕜] F₂`, then so is `F₁`. -/
theorem constantsOnly_of_algEquiv {𝕜 F₁ F₂ : Type} [Field 𝕜] [Field F₁] [Field F₂]
    [Algebra 𝕜 F₁] [Algebra 𝕜 F₂] [Algebra (RatFunc 𝕜) F₁] [Algebra (RatFunc 𝕜) F₂]
    [IsScalarTower 𝕜 (RatFunc 𝕜) F₁] [IsScalarTower 𝕜 (RatFunc 𝕜) F₂]
    (e : F₁ ≃ₐ[RatFunc 𝕜] F₂) (h₂ : ConstantsOnly 𝕜 F₂) : ConstantsOnly 𝕜 F₁ := by
  intro M _ _ ι x
  obtain ⟨c, hc⟩ := h₂ M (ι.comp (e.symm.toAlgHom.restrictScalars 𝕜)) (e x)
  exact ⟨c, by simpa using hc⟩

end Work.MotV
