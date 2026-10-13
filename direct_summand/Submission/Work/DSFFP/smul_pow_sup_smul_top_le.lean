import Mathlib

universe u

namespace Work.DSFFP

theorem smul_pow_sup_smul_top_le {S : Type u} [CommRing S] (I : Ideal S) {Q : Type u}
    [AddCommGroup Q] [Module S Q] (A : Submodule S Q) (m : ℕ)
    (hm : I ^ (m + 1) • (⊤ : Submodule S Q) ≤ A) :
    I ^ m • (A ⊔ I • (⊤ : Submodule S Q)) ≤ A := by
  -- Distribute `I ^ m •` over the supremum.
  rw [Submodule.smul_sup]
  apply sup_le
  · -- `I ^ m • A ≤ A` because `A` is closed under scalar multiplication.
    rw [Submodule.smul_le]
    intro r _ n hn
    exact A.smul_mem r hn
  · -- `I ^ m • (I • ⊤) = (I ^ m • I) • ⊤ = I ^ (m + 1) • ⊤ ≤ A`.
    calc I ^ m • (I • (⊤ : Submodule S Q)) = (I ^ m • I) • (⊤ : Submodule S Q) :=
          (Submodule.smul_assoc (I ^ m) I ⊤).symm
      _ = I ^ (m + 1) • (⊤ : Submodule S Q) := by rw [pow_succ]; rfl
      _ ≤ A := hm

end Work.DSFFP
