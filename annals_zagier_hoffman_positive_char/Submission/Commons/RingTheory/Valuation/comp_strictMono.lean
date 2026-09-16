import Mathlib.RingTheory.Valuation.Basic

namespace Commons.RingTheory.Valuation

theorem comp_strictMono {K Γ₀ Γ₁ : Type*} [Field K]
    [LinearOrderedCommGroupWithZero Γ₀] [LinearOrderedCommGroupWithZero Γ₁]
    (v : Valuation K Γ₀) (f : Γ₀ →*₀ Γ₁) (hf : StrictMono f) :
    ∃ w : Valuation K Γ₁, ∀ x, w x = f (v x) :=
  ⟨v.map f hf.monotone, fun _ => rfl⟩

end Commons.RingTheory.Valuation