import Mathlib
import Submission.Work.BG.Glauberman

/-!
# BG-L3: fixed points of the restricted action (`FixedRestrictProp`)

Leaf **BG-L3** of `Submission/Work/BG/Glauberman.lean`.  Let `φ : S →* MulAut U` be an action,
`s₀ : S`, and `φ₁ : S →* MulAut ↥(fixedSubgroup (φ s₀))` a restricted action compatible with
`φ` (`((φ₁ s u : ↥(_)) : U) = φ s u` for all `s`, `u`).  Then

* `C_U(S) = fixedSubgroupS φ` is contained in `C_U(φ s₀) = fixedSubgroup (φ s₀)`, and
* `C_{U₁}(φ₁) = fixedSubgroupS φ₁` agrees, inside `U₁ = C_U(φ s₀)`, with `C_U(S)`:

  `fixedSubgroupS φ₁ = (fixedSubgroupS φ).subgroupOf (fixedSubgroup (φ s₀))`.

Both inclusions are immediate from the defining property of `φ₁` (`Subtype.ext` plus `hφ₁`).
-/

namespace Work.BG

theorem fixedRestrict : Work.BG.FixedRestrictProp := by
  intro S U _ _ φ s₀ φ₁ hφ₁
  constructor
  · -- `C_U(S) ≤ C_U(φ s₀)`: take `s := s₀` in the defining property.
    intro u hu
    exact hu s₀
  · -- `C_{U₁}(φ₁) = C_U(S) ∩ U₁`, both viewed inside `U₁`.
    ext x
    simp only [mem_fixedSubgroupS, Subgroup.mem_subgroupOf]
    constructor
    · intro hx s
      have h2 : ((φ₁ s x : ↥(fixedSubgroup (φ s₀))) : U) = (x : U) := by rw [hx s]
      rwa [hφ₁ s x] at h2
    · intro hx s
      apply Subtype.ext
      rw [hφ₁ s x]
      exact hx s

end Work.BG
