import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- In any preorder `α` and for any `x : α`, the height of `x` plus its coheight is at most the
Krull dimension of `α`. Indeed `krullDim α` is the supremum over all `a` of `height a + coheight a`
(`Order.krullDim_eq_iSup_height_add_coheight_of_nonempty`). -/
lemma height_add_coheight_le_krullDim {α : Type*} [Preorder α] (x : α) :
    ((Order.height x : ℕ∞) : WithBot ℕ∞) + ((Order.coheight x : ℕ∞) : WithBot ℕ∞) ≤
      Order.krullDim α := by
  rw [@Order.krullDim_eq_iSup_height_add_coheight_of_nonempty α _ ⟨x⟩, ← WithBot.coe_add]
  exact WithBot.coe_le_coe.mpr (le_iSup (fun a => Order.height a + Order.coheight a) x)

theorem height_add_krullDim_quotient {R : Type*} [CommRing R] (p : Ideal R) [p.IsPrime] :
    ((p.height : ℕ∞) : WithBot ℕ∞) + ringKrullDim (R ⧸ p) ≤ ringKrullDim R := by
  -- The primes of the quotient `R ⧸ p` correspond to the primes of `R` lying above `p`.
  let x : PrimeSpectrum R := ⟨p, ‹p.IsPrime›⟩
  have hset : PrimeSpectrum.zeroLocus (R := R) (p : Set R) = Set.Ici x := by
    ext q
    rw [PrimeSpectrum.mem_zeroLocus, Set.mem_Ici, SetLike.coe_subset_coe]
    exact PrimeSpectrum.asIdeal_le_asIdeal x q
  -- `dim (R ⧸ p)` is the coheight of `p` in `Spec R`.
  have hle : ringKrullDim (R ⧸ p) ≤ (↑(Order.coheight x) : WithBot ℕ∞) := by
    rw [ringKrullDim_quotient, Order.coheight_eq_krullDim_Ici x, hset]
  -- `p.height` is the order-theoretic height of `p` in `Spec R`.
  have hpx : ((p.height : ℕ∞) : WithBot ℕ∞) = (↑(Order.height x) : WithBot ℕ∞) := by
    congr 1
    simpa [x] using (PrimeSpectrum.height_eq_orderHeight x)
  calc ((p.height : ℕ∞) : WithBot ℕ∞) + ringKrullDim (R ⧸ p)
      ≤ ↑(Order.height x) + ↑(Order.coheight x) := add_le_add (le_of_eq hpx) hle
    _ ≤ ringKrullDim R := height_add_coheight_le_krullDim x

end Work.BW
