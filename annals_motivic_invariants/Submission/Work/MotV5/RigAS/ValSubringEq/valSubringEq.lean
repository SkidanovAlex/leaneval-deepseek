import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV5.RigAS.ValSubringEq

theorem valSubringEq {F L : Type*} [Field F] [Field L] [Algebra F L]
    (v : Valuation F (WithZero (Multiplicative ℤ)))
    (V W : Valuation L (WithZero (Multiplicative ℤ)))
    (hVext : ∀ x : F, V (algebraMap F L x) = v x)
    (hWext : ∀ x : F, W (algebraMap F L x) = v x)
    (hVΓ : ∀ x : L, x ≠ 0 → ∃ y : F, y ≠ 0 ∧ V (algebraMap F L y) = V x)
    (hR : V.valuationSubring = W.valuationSubring) : V = W := by
  -- Equal valuation subrings mean the two valuations are equivalent.
  have hE : V.IsEquiv W := (Valuation.isEquiv_iff_valuationSubring V W).mpr hR
  ext x
  by_cases hx : x = 0
  · subst hx; simp
  · -- `hVΓ` exhibits `x` as having the same value as some element of `F`; equivalently,
    -- the two valuations take the same value there, which transfers across the equivalence.
    obtain ⟨y, -, hVy⟩ := hVΓ x hx
    calc V x = V (algebraMap F L y) := hVy.symm
      _ = v y := hVext y
      _ = W (algebraMap F L y) := (hWext y).symm
      _ = W x := (hE.eq_iff.mp hVy.symm).symm

end Work.MotV5.RigAS.ValSubringEq
