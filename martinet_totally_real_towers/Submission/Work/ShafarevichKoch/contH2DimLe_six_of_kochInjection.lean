import Mathlib
import Submission.Work.RelatorRank.CohomologyH2
import Submission.Work.ShafarevichKoch.KcRank
import Submission.Work.ShafarevichKoch.vTwo_rank_two_corrected
import Submission.Work.ShafarevichKoch.le_of_isOpen_index_two_Kc

/-!
# `Work.ShafarevichKoch.contH2DimLe_six_of_kochInjection`

**The Koch/Shafarevich injection forces the cohomological relation bound
`dim_{𝔽₂} H²(G_∅, 𝔽₂) ≤ 6` for the maximal unramified pro-`2` group `G_∅ = Gal(Kc_∅/Kc)`,
`Kc = ℚ(√-30030)`.**

The classical Shafarevich--Koch relation count (Koch, *Galois theory of `p`-extensions*, Ch. 11
Thm. 11.3; Wingberg's duality, NSW Ch. VIII §8 Thm. 8.8.1) is the statement that the continuous
cohomology `H²(G_∅, 𝔽₂)` *embeds* into the `𝔽₂`-dual of Koch's Kummer quotient
`V_∅/Kc^{×2} = VTwo Kc / (Kcˣ)²`:

```
H²(G_∅, 𝔽₂)  ↪  Hom(V_∅/Kc^{×2}, 𝔽₂) .
```

Because that dual has exactly `64 = 2^6` elements (proved below as
`natCard_dual_VTwoQuot_Kc_aux`; the same count is `Work.ShafarevichKoch.natCard_dual_VTwoQuot_Kc`
of the chapter's own module, whose statement is literally the same type), i.e.
`dim_{𝔽₂} V_∅/Kc^{×2} = d₂(𝓞_{Kc}ˣ) + rank₂ Cl(Kc) = 1 + 5 = 6`, the *arithmetic* content of
the relation count is exactly the existence of such an injection: `H²` is an `𝔽₂`-vector space
(every element is killed by `2`, so `AddCommGroup.zmodModule` makes it a module over `𝔽₂`), hence
its cardinality is `2 ^ dim`, and the injection bounds it by `2^6`.

This module proves that implication in the form the rest of the project consumes,
`Work.RelatorRank.ContH2DimLe (galoisGroup M) 6` (`∃ k ≤ 6, #H²(G_∅,𝔽₂) = 2^k`), from the bare
existence of the injection.  Nothing beyond the count `#(V_∅/Kc^{×2})^∨ = 64` is used.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Classical

namespace Work.ShafarevichKoch

open scoped IsMulCommutative

/-- **The `𝔽₂`-dual of Koch's Kummer quotient `V_∅/Kc^{×2}` has `64 = 2^6` elements.**

The quotient `VTwo Kc ⧸ (Kcˣ)²` is a finite commutative group of exponent `2` (a `2`-torsion
element of `V_∅` is a square modulo `(Kcˣ)²`, `Work.ShafarevichKoch.quotient_exponent_two`), of
order `2 ^ (unitTwoRank Kc + classGroupTwoRank Kc) = 2 ^ (1 + 5) = 2 ^ 6`
(`Work.ShafarevichKoch.card_quotient_VTwo`, `Work.ClassFieldTower.unitTwoRank_witness_eq_one`,
`Work.ShafarevichKoch.classGroupTwoRank_Kc`).  A finite commutative group of exponent `2` has as
many homomorphisms into `𝔽₂ = Multiplicative (ZMod 2)` as it has elements
(`Work.ShafarevichKoch.natCard_monoidHom_zmodTwo`, the counting form of the self-duality of finite
`𝔽₂`-vector spaces). -/
private theorem natCard_dual_VTwoQuot_Kc_aux :
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

theorem contH2DimLe_six_of_kochInjection
    (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Work.ClassFieldTower.Kc 2)
    (h : ∃ ι : Work.RelatorRank.contH2 (Work.ClassFieldTower.galoisGroup M) →+
        Additive ((↥(Work.ShafarevichKoch.VTwo Work.ClassFieldTower.Kc) ⧸
            (Work.QuadraticFields.squareSubgroup (Work.ClassFieldTower.Kc)ˣ).subgroupOf
              (Work.ShafarevichKoch.VTwo Work.ClassFieldTower.Kc)) →*
          Multiplicative (ZMod 2)),
      Function.Injective ι) :
    Work.RelatorRank.ContH2DimLe (Work.ClassFieldTower.galoisGroup M) 6 := by
  obtain ⟨ι, hι⟩ := h
  -- ### `H²(G_∅,𝔽₂)` has exponent `2`: it is a quotient of the group of `2`-cocycles with
  -- coefficients in `𝔽₂ = ℤ/2`, on which `2` acts trivially.
  have h2 : ∀ x : Work.RelatorRank.contH2 (Work.ClassFieldTower.galoisGroup M),
      (2 : ℕ) • x = 0 := by
    intro x
    letI := Work.RelatorRank.f2TrivialAction (Work.ClassFieldTower.galoisGroup M)
    letI : Work.ConCohomology.IsDiscreteGModule (Work.ClassFieldTower.galoisGroup M) (ZMod 2) :=
      Work.RelatorRank.f2Discrete (Work.ClassFieldTower.galoisGroup M)
    obtain ⟨z, rfl⟩ := QuotientAddGroup.mk'_surjective
      (Work.ConCohomology.B2' (Work.ClassFieldTower.galoisGroup M) (ZMod 2)) x
    rw [← map_nsmul]
    rw [show (2 : ℕ) • z = 0 from by
          refine Subtype.ext ?_
          ext p
          show (2 : ℕ) • (z.1 p) = 0
          exact CharTwo.two_nsmul _,
      map_zero]
  -- ### The dual of `V_∅/Kc^{×2}` has `64 = 2^6` elements.
  have hdual : Nat.card (Additive ((↥(Work.ShafarevichKoch.VTwo Work.ClassFieldTower.Kc) ⧸
            (Work.QuadraticFields.squareSubgroup (Work.ClassFieldTower.Kc)ˣ).subgroupOf
              (Work.ShafarevichKoch.VTwo Work.ClassFieldTower.Kc)) →*
          Multiplicative (ZMod 2))) = 64 := by
    rw [Nat.card_congr Additive.toMul, natCard_dual_VTwoQuot_Kc_aux]
  haveI : Finite (Additive ((↥(Work.ShafarevichKoch.VTwo Work.ClassFieldTower.Kc) ⧸
            (Work.QuadraticFields.squareSubgroup (Work.ClassFieldTower.Kc)ˣ).subgroupOf
              (Work.ShafarevichKoch.VTwo Work.ClassFieldTower.Kc)) →*
          Multiplicative (ZMod 2))) := Nat.finite_of_card_ne_zero (by rw [hdual]; norm_num)
  -- ### Hence `#H²(G_∅,𝔽₂) ≤ 64`, so `H²` is finite.
  have hcardle : Nat.card (Work.RelatorRank.contH2 (Work.ClassFieldTower.galoisGroup M)) ≤ 64 := by
    have h1 := Nat.card_le_card_of_injective ι hι
    rw [hdual] at h1
    exact h1
  haveI : Finite (Work.RelatorRank.contH2 (Work.ClassFieldTower.galoisGroup M)) :=
    Finite.of_injective ι hι
  -- ### `H²(G_∅,𝔽₂)` is an `𝔽₂`-vector space, of dimension `log₂ #H²`; the bound `#H² ≤ 64`
  -- is therefore the dimension bound.
  letI : Module (ZMod 2) (Work.RelatorRank.contH2 (Work.ClassFieldTower.galoisGroup M)) :=
    AddCommGroup.zmodModule (n := 2) h2
  haveI : Module.Finite (ZMod 2) (Work.RelatorRank.contH2 (Work.ClassFieldTower.galoisGroup M)) :=
    Module.Finite.of_finite
  have hcardfin : Nat.card (Work.RelatorRank.contH2 (Work.ClassFieldTower.galoisGroup M))
      = 2 ^ Module.finrank (ZMod 2)
          (Work.RelatorRank.contH2 (Work.ClassFieldTower.galoisGroup M)) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  refine ⟨Module.finrank (ZMod 2) (Work.RelatorRank.contH2 (Work.ClassFieldTower.galoisGroup M)),
    ?_, hcardfin⟩
  have : 2 ^ Module.finrank (ZMod 2)
      (Work.RelatorRank.contH2 (Work.ClassFieldTower.galoisGroup M)) ≤ 2 ^ 6 := by
    rw [← hcardfin]
    exact hcardle
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this

end Work.ShafarevichKoch
