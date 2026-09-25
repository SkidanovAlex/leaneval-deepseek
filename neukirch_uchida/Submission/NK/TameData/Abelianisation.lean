/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Component 2: the residue field order from the abelianised tame quotient

The residue field cardinality `q` of a `p`-adic field `κ` is recovered from `G_κ` through the
*torsion* of the abelianised tame quotient `G_κ^{tr,ab} = (G_κ/V_κ)^{ab}` (Shimizu,
arXiv:2009.10431, Lemma 2.1, via local class field theory):

  `#(G_κ^{tr,ab})_{tor} = q - 1`.

Two routes are provided, matching the two forms of the input (the second, the classical local
class field theory statement, implies the first — see
`NK.TameData.TameAbelianisationInput.toTorsionInput`):

* from **Shimizu's torsion statement** `TameTorsionInput`: the torsion is cyclic of order `q - 1`
  (`ResidueCardRecovery.of_torsionInput`) — a two-line computation of `Nat.card`;
* from the **splitting** `TameAbelianisationInput`, `G_κ^{tr,ab} ≅ Ẑ × μ_{q-1}`
  (`ResidueCardRecovery.of_abelianisation`): the torsion of the product is the product of the
  torsions, `Ẑ` is torsion-free (`NK.TameData.isMulTorsionFree_zhat`) and `μ_{q-1}` has `q - 1`
  elements.

The `Nat.card` bookkeeping for the second route is in `NK.TameData.Torsion`.
-/
import Submission.NK.TameData.Definitions
import Submission.NK.TameData.Torsion
import Submission.NK.TameData.Abelianisation.torsion_mulEquiv_zmod
import Submission.NK.TameData.Zhat.isMulTorsionFree_zhat

open scoped Classical
open NK.LocalTame

namespace NK.TameData

universe u

variable {κ K' : Type*} [Field κ] [Field K'] [Algebra κ K'] [IsSepClosure κ K']

/-- **`Ẑ` is torsion-free**, as an instance: `NK.TameData.Zhat.isMulTorsionFree_zhat`.  With this
instance registered, every `[IsMulTorsionFree NK.LocalAnabelian.Zhat]` hypothesis in this chapter
is discharged automatically. -/
instance instIsMulTorsionFreeZhat : IsMulTorsionFree NK.LocalAnabelian.Zhat :=
  NK.TameData.Zhat.isMulTorsionFree_zhat

/-! ## The arithmetic consequence of `q = p ^ f` -/

/-- If `q = p ^ f` with `p` prime and `f > 0` then `q ≥ 2`, so `q - 1` is a positive natural
number and `ZMod (q - 1)` is a finite cyclic group. -/
theorem one_lt_of_prime_pow {p q : ℕ} (hp : p.Prime) {f : ℕ} (hf : 0 < f) (hq : q = p ^ f) :
    1 < q := by
  rw [hq]
  exact Nat.one_lt_pow hf.ne' hp.one_lt

/-! ## Route 1: Shimizu's torsion statement -/

/-- **The residue field order from the torsion of the abelianised tame quotient** (Shimizu,
arXiv:2009.10431, Lemma 2.1), from the statement that the torsion is cyclic of order `q - 1`. -/
theorem ResidueCardRecovery.of_torsionInput {p q : ℕ} (h : TameTorsionInput p q κ K') :
    ResidueCardRecovery p q κ K' where
  hp := h.hp
  q_eq := h.q_eq
  card_torsion := by
    obtain ⟨f, hf, hqf⟩ := h.q_eq
    have hq2 : 1 < q := one_lt_of_prime_pow h.hp hf hqf
    haveI : NeZero (q - 1) := ⟨by omega⟩
    obtain ⟨e⟩ := h.nonempty_torsion_iso
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]

/-! ## Route 2: the splitting `G_κ^{tr,ab} ≅ Ẑ × μ_{q-1}` -/

/-- **The residue field order from the splitting of the abelianised tame quotient** (Shimizu,
arXiv:2009.10431, Lemma 2.1; local class field theory): if
`G_κ^{tr,ab} ≅ Ẑ × μ_{q-1}` then `#(G_κ^{tr,ab})_{tor} = q - 1`.

Indeed the torsion of a product is the product of the torsions, the torsion of `Ẑ` is trivial
(`NK.TameData.isMulTorsionFree_zhat`) and that of `μ_{q-1} = Multiplicative (ZMod (q-1))` is the
whole group, of order `q - 1`. -/
theorem ResidueCardRecovery.of_abelianisation {p q : ℕ} (h : TameAbelianisationInput p q κ K') :
    ResidueCardRecovery p q κ K' where
  hp := h.hp
  q_eq := h.q_eq
  card_torsion := by
    obtain ⟨f, hf, hqf⟩ := h.q_eq
    have hq2 : 1 < q := one_lt_of_prime_pow h.hp hf hqf
    haveI : NeZero (q - 1) := ⟨by omega⟩
    obtain ⟨e⟩ := h.nonempty_iso
    rw [natCard_torsion_eq_natCard_isOfFinOrder,
      Nat.card_congr (Equiv.subtypeEquiv e.toEquiv (fun x =>
        (Function.Injective.isOfFinOrder_iff
          (f := (e.toMonoidHom : tameAbelianization (κ := κ) (K' := K') p →*
            (NK.LocalAnabelian.Zhat × Multiplicative (ZMod (q - 1))))) e.injective).symm)),
      natCard_isOfFinOrder_prod,
      natCard_isOfFinOrder_eq_one NK.LocalAnabelian.Zhat, one_mul,
      natCard_isOfFinOrder_multiplicative_zmod]

/-! ## The two forms of the input are compatible -/

/-- **The splitting of the abelianised tame quotient implies Shimizu's literal torsion
statement**: the very same input can be used in either form
(`NK.TameData.Abelianisation.torsion_mulEquiv_zmod`). -/
theorem TameAbelianisationInput.toTorsionInput {p q : ℕ} (h : TameAbelianisationInput p q κ K') :
    TameTorsionInput p q κ K' where
  hp := h.hp
  q_eq := h.q_eq
  nonempty_torsion_iso := NK.TameData.Abelianisation.torsion_mulEquiv_zmod h

end NK.TameData
