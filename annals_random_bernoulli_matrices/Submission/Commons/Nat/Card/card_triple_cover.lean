import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Powerset

namespace Commons.Nat.Card

lemma card_triple_cover (D0 : Finset ℤ) (K ℓ : ℕ) :
    ((D0.product ((Finset.univ : Finset (Fin ℓ)).powerset)).product
        (Finset.powersetCard K (Finset.univ : Finset (Fin ℓ)))).card =
      D0.card * 2 ^ ℓ * (ℓ.choose K) := by
  simp [Finset.card_product, Finset.card_powersetCard]

end Commons.Nat.Card