import Mathlib
import Submission.Work.ShafarevichKoch.KcRank
import Submission.Work.ShafarevichKoch.vTwo_rank_two_corrected
import Submission.Work.ShafarevichKoch.le_of_isOpen_index_two_Kc

/-!
# `Work.ShafarevichKoch.natCard_dual_VTwoQuot_Kc`

**The `𝔽₂`-dual of the Kummer quotient `V_∅/Kc^{×2}` of `Kc = ℚ(√-30030)` has `64` elements.**

Koch's Kummer radical `V_∅ = VTwo Kc` sits in

`1 → 𝓞_{Kc}ˣ/(𝓞_{Kc}ˣ)² → V_∅/Kc^{×2} → Cl(Kc)[2] → 1`,

and the exact dimension count `dim_{𝔽₂} V_∅/Kc^{×2} = d₂(𝓞_{Kc}ˣ) + rank₂ Cl(Kc) = 1 + 5 = 6`
(`Work.ShafarevichKoch.card_quotient_VTwo`, `unitTwoRank_witness_eq_one`,
`classGroupTwoRank_Kc`) gives `#(V_∅/Kc^{×2}) = 2^6 = 64`.

The quotient has exponent `2` (`Work.ShafarevichKoch.quotient_exponent_two`), i.e. it is an
`𝔽₂`-vector space, and a finite commutative group of exponent `2` has as many homomorphisms to
`𝔽₂ = Multiplicative (ZMod 2)` as it has elements
(`Work.ShafarevichKoch.natCard_monoidHom_zmodTwo`, the counting form of the self-duality of
finite-dimensional `𝔽₂`-vector spaces).  Hence

`#(V_∅/Kc^{×2} →* 𝔽₂) = #(V_∅/Kc^{×2}) = 64`.

This is the numerical identification underlying the Shafarevich--Koch relation count: the
right-hand side `6 = dim_{𝔽₂} V_∅/Kc^{×2}` is the bound that the relation rank `r(G_∅)` must
satisfy (Koch, *Galois theory of `p`-extensions*, Ch. 11 Thm. 11.3).
-/

set_option linter.style.haveILetI false

namespace Work.ShafarevichKoch

theorem natCard_dual_VTwoQuot_Kc :
    Nat.card ((↥(Work.ShafarevichKoch.VTwo Work.ClassFieldTower.Kc) ⧸
        (Work.QuadraticFields.squareSubgroup (Work.ClassFieldTower.Kc)ˣ).subgroupOf
          (Work.ShafarevichKoch.VTwo Work.ClassFieldTower.Kc)) →* Multiplicative (ZMod 2)) = 64 := by
  haveI : IsMulCommutative (↥(Work.ShafarevichKoch.VTwo Work.ClassFieldTower.Kc) ⧸
      (Work.QuadraticFields.squareSubgroup (Work.ClassFieldTower.Kc)ˣ).subgroupOf
        (Work.ShafarevichKoch.VTwo Work.ClassFieldTower.Kc)) :=
    IsMulCommutative.of_comm fun a b => mul_comm a b
  have hcard : Nat.card (↥(Work.ShafarevichKoch.VTwo Work.ClassFieldTower.Kc) ⧸
      (Work.QuadraticFields.squareSubgroup (Work.ClassFieldTower.Kc)ˣ).subgroupOf
        (Work.ShafarevichKoch.VTwo Work.ClassFieldTower.Kc)) = 64 := by
    have h := Work.ShafarevichKoch.card_quotient_VTwo Work.ClassFieldTower.Kc
    rw [Work.ClassFieldTower.unitTwoRank_witness_eq_one,
      Work.ShafarevichKoch.classGroupTwoRank_Kc] at h
    norm_num at h
    exact h
  haveI : Finite (↥(Work.ShafarevichKoch.VTwo Work.ClassFieldTower.Kc) ⧸
      (Work.QuadraticFields.squareSubgroup (Work.ClassFieldTower.Kc)ˣ).subgroupOf
        (Work.ShafarevichKoch.VTwo Work.ClassFieldTower.Kc)) :=
    (Nat.card_ne_zero.mp (by rw [hcard]; norm_num)).2
  have hsq : ∀ a : (↥(Work.ShafarevichKoch.VTwo Work.ClassFieldTower.Kc) ⧸
      (Work.QuadraticFields.squareSubgroup (Work.ClassFieldTower.Kc)ˣ).subgroupOf
        (Work.ShafarevichKoch.VTwo Work.ClassFieldTower.Kc)), a * a = 1 := by
    intro a
    rw [← pow_two]
    exact Work.ShafarevichKoch.quotient_exponent_two Work.ClassFieldTower.Kc a
  rw [Work.ShafarevichKoch.natCard_monoidHom_zmodTwo hsq, hcard]

end Work.ShafarevichKoch
