import Mathlib
import Submission.Work.ShafarevichKoch.H2Half.natCard_H2Z_quot_two_le_pow_five_Kc
import Submission.Work.ShafarevichKoch.card_twoTorsionH3_le_of_wingbergDuality
import Submission.Work.ShafarevichKoch.WingbergMain
import Submission.Work.ShafarevichKoch.KcCohomology
import Submission.Work.ShafarevichKoch.WingbergDefs
import Submission.Work.ShafarevichKoch.CountZ

/-!
# `Work.ShafarevichKoch.UnitHalf.kcProTwoPresentationInput_of_unitDuality`

The *unit half* of Wingberg's duality (the identification of the Pontryagin dual of `H³(G_∅,ℤ)`
with a quotient of the units `(𝓞 Kc)ˣ = {±1}`), together with the finiteness of `H²(G_∅,ℤ)` and
`H³(G_∅,ℤ)`, suffices for the chapter's crux `Work.ShafarevichKoch.KcProTwoPresentationInput`.

Indeed the `H²`-half of the relation count — the bound `#(H²(G_∅,ℤ)/2H²(G_∅,ℤ)) ≤ 2^5` — is
*unconditional* (`Work.ShafarevichKoch.H2Half.natCard_H2Z_quot_two_le_pow_five_Kc`: it only uses
the coefficient sequence `0 → ℤ → ℚ → ℚ/ℤ → 0`, the vanishing of `H¹`/`H²` with `ℚ`-coefficients
and the elementary count `#H¹(G_∅,𝔽₂) = 2^5`), and the `ℤ`-power sequence
`Work.ShafarevichKoch.natCard_H2_zmodTwo_eq` multiplies the two halves:

```
#H²(G_∅,𝔽₂) = #(H²(G_∅,ℤ)/2H²(G_∅,ℤ)) · #H³(G_∅,ℤ)[2] .
```

So only the unit half of the duality, `PDual (H³(G_∅,ℤ)) ≅ Additive ((𝓞 Kc)ˣ ⧸ N)`, is needed; the
`H²`-half `PDual (H²(G_∅,ℤ)) ≅ Additive Cl2Part` of `WingbergDuality` is not used.

## Main declarations

* `Work.ShafarevichKoch.UnitHalf.card_twoTorsionH3_le_two_of_unitDuality`;
* `Work.ShafarevichKoch.UnitHalf.contH2DimLe_six_of_unitDuality`;
* `Work.ShafarevichKoch.UnitHalf.kcProTwoPresentationInput_of_unitDuality`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 2000000

open scoped Classical
open NumberField

noncomputable section

namespace Work.ShafarevichKoch.UnitHalf

open Work.ClassFieldTower
open Work.ConCohomology

section UnitHalf

variable (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Work.ClassFieldTower.Kc 2)

/-- **The unit half of Wingberg's duality bounds the `2`-torsion of `H³(G_∅,ℤ)`.**

If `H³(G_∅,ℤ)` is finite and its Pontryagin dual is a quotient of `(𝓞 Kc)ˣ = {±1}`, then
`#H³(G_∅,ℤ)[2] ≤ 2`.  This is
`Work.ShafarevichKoch.card_twoTorsionH3_le_of_wingbergDuality` with the `H²`-half of
`WingbergDuality` dropped from the hypotheses. -/
theorem card_twoTorsionH3_le_two_of_unitDuality
    (hfin3 : Finite (Work.ShafarevichKoch.H3 (Work.ClassFieldTower.galoisGroup M) ℤ))
    (hN : ∃ N : Subgroup ((NumberField.RingOfIntegers Work.ClassFieldTower.Kc)ˣ),
        Nonempty (Work.ShafarevichKoch.PDual
            (Work.ShafarevichKoch.H3 (Work.ClassFieldTower.galoisGroup M) ℤ) ≃+
          Additive (((NumberField.RingOfIntegers Work.ClassFieldTower.Kc)ˣ) ⧸ N))) :
    Nat.card (Work.ShafarevichKoch.twoTorsionH3 (Work.ClassFieldTower.galoisGroup M)) ≤ 2 := by
  obtain ⟨N, hN'⟩ := hN
  obtain ⟨e⟩ := hN'
  haveI hfin3' : Finite (Work.ShafarevichKoch.H3 (Work.ClassFieldTower.galoisGroup M) ℤ) := hfin3
  haveI : Fintype (Work.ShafarevichKoch.H3 (Work.ClassFieldTower.galoisGroup M) ℤ) :=
    Fintype.ofFinite _
  haveI : Finite ((NumberField.RingOfIntegers Work.ClassFieldTower.Kc)ˣ) :=
    Work.ShafarevichKoch.finite_RingUnit_Kc
  exact (Work.ShafarevichKoch.card_twoTorsion_of_dual_quotient_le
      (A := Work.ShafarevichKoch.H3 (Work.ClassFieldTower.galoisGroup M) ℤ)
      (B := (NumberField.RingOfIntegers Work.ClassFieldTower.Kc)ˣ) N e).trans
    Work.ShafarevichKoch.card_RingUnit_Kc_le_two

/-- **The relation count from the unit half of Wingberg's duality.**

`dim_{𝔽₂} H²_cont(G_∅,𝔽₂) ≤ 6`, i.e. `Work.RelatorRank.ContH2DimLe (G_∅) 6`: the H²-half of the
count is unconditional, the `H³`-half is bounded by the unit half of the duality, and the
`ℤ`-power sequence multiplies the two. -/
theorem contH2DimLe_six_of_unitDuality
    (hfin2 : Finite (Work.ConCohomology.H2 (Work.ClassFieldTower.galoisGroup M) ℤ))
    (hfin3 : Finite (Work.ShafarevichKoch.H3 (Work.ClassFieldTower.galoisGroup M) ℤ))
    (hN : ∃ N : Subgroup ((NumberField.RingOfIntegers Work.ClassFieldTower.Kc)ˣ),
        Nonempty (Work.ShafarevichKoch.PDual
            (Work.ShafarevichKoch.H3 (Work.ClassFieldTower.galoisGroup M) ℤ) ≃+
          Additive (((NumberField.RingOfIntegers Work.ClassFieldTower.Kc)ˣ) ⧸ N))) :
    Work.RelatorRank.ContH2DimLe (Work.ClassFieldTower.galoisGroup M) 6 := by
  haveI hfin2' : Finite (Work.ConCohomology.H2 (Work.ClassFieldTower.galoisGroup M) ℤ) := hfin2
  haveI hfin3' : Finite (Work.ShafarevichKoch.H3 (Work.ClassFieldTower.galoisGroup M) ℤ) := hfin3
  -- the `H²`-half (unconditional) and the `H³`-half (the unit half of the duality)
  have hA : Nat.card (Work.ConCohomology.H2 (Work.ClassFieldTower.galoisGroup M) ℤ ⧸
      Work.ShafarevichKoch.twoMulH2 (Work.ClassFieldTower.galoisGroup M)) ≤ 2 ^ 5 :=
    Work.ShafarevichKoch.H2Half.natCard_H2Z_quot_two_le_pow_five_Kc M
  have hB : Nat.card (Work.ShafarevichKoch.twoTorsionH3 (Work.ClassFieldTower.galoisGroup M)) ≤ 2 :=
    card_twoTorsionH3_le_two_of_unitDuality M hfin3 hN
  -- the cardinality bound `#H²(G_∅,𝔽₂) ≤ 2^6`
  have hcard : Nat.card (Work.ConCohomology.H2 (Work.ClassFieldTower.galoisGroup M) (ZMod 2)) ≤ 2 ^ 6 :=
    Work.ShafarevichKoch.natCard_H2_zmodTwo_le (G := Work.ClassFieldTower.galoisGroup M) hA hB
  -- `H²(G_∅,𝔽₂)` is finite
  haveI hfin : Finite (Work.ConCohomology.H2 (Work.ClassFieldTower.galoisGroup M) (ZMod 2)) := by
    have hceq := Work.ShafarevichKoch.natCard_H2_zmodTwo_eq
      (G := Work.ClassFieldTower.galoisGroup M)
    have hne1 : Nat.card (Work.ConCohomology.H2 (Work.ClassFieldTower.galoisGroup M) ℤ ⧸
        Work.ShafarevichKoch.twoMulH2 (Work.ClassFieldTower.galoisGroup M)) ≠ 0 :=
      Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩
    haveI : Finite (Work.ShafarevichKoch.twoTorsionH3 (Work.ClassFieldTower.galoisGroup M)) :=
      Finite.of_injective Subtype.val Subtype.val_injective
    have hne2 : Nat.card (Work.ShafarevichKoch.twoTorsionH3 (Work.ClassFieldTower.galoisGroup M)) ≠ 0 :=
      Nat.card_ne_zero.mpr ⟨⟨0, by simp⟩, inferInstance⟩
    exact Nat.finite_of_card_ne_zero (by rw [hceq]; exact Nat.mul_ne_zero hne1 hne2)
  -- `H²(G_∅,𝔽₂)` is an `𝔽₂`-vector space, so its cardinality is a power of `2`
  have hexp : ∀ x : Work.RelatorRank.contH2 (Work.ClassFieldTower.galoisGroup M),
      (2 : ℕ) • x = 0 := by
    intro x
    letI := Work.RelatorRank.f2TrivialAction (Work.ClassFieldTower.galoisGroup M)
    letI : Work.ConCohomology.IsDiscreteGModule
        (Work.ClassFieldTower.galoisGroup M) (ZMod 2) :=
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
  letI : Module (ZMod 2) (Work.RelatorRank.contH2 (Work.ClassFieldTower.galoisGroup M)) :=
    AddCommGroup.zmodModule (n := 2) hexp
  haveI : Module.Finite (ZMod 2)
      (Work.RelatorRank.contH2 (Work.ClassFieldTower.galoisGroup M)) := Module.Finite.of_finite
  have hcardfin : Nat.card (Work.RelatorRank.contH2 (Work.ClassFieldTower.galoisGroup M)) =
      2 ^ Module.finrank (ZMod 2)
        (Work.RelatorRank.contH2 (Work.ClassFieldTower.galoisGroup M)) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  refine ⟨Module.finrank (ZMod 2)
    (Work.RelatorRank.contH2 (Work.ClassFieldTower.galoisGroup M)), ?_, hcardfin⟩
  have : 2 ^ Module.finrank (ZMod 2)
      (Work.RelatorRank.contH2 (Work.ClassFieldTower.galoisGroup M)) ≤ 2 ^ 6 := by
    rw [← hcardfin]
    exact hcard
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this

end UnitHalf

open Work.ClassFieldTower

/-- **The chapter's crux from the unit half of Wingberg's duality** (and the shared group-theoretic
input `Work.RelatorRank.GaschutzCohomologicalValue`): the finiteness of `H²(G_∅,ℤ)` and
`H³(G_∅,ℤ)` together with the identification of the Pontryagin dual of `H³(G_∅,ℤ)` with a quotient
of `(𝓞 Kc)ˣ` implies `KcProTwoPresentationInput`. -/
theorem kcProTwoPresentationInput_of_unitDuality
    (hdict : ∀ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Work.ClassFieldTower.Kc 2,
      Work.RelatorRank.GaschutzCohomologicalValue (Work.ClassFieldTower.galoisGroup M))
    (h : ∃ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Work.ClassFieldTower.Kc 2,
      Finite (Work.ConCohomology.H2 (Work.ClassFieldTower.galoisGroup M) ℤ) ∧
      Finite (Work.ShafarevichKoch.H3 (Work.ClassFieldTower.galoisGroup M) ℤ) ∧
      (∃ N : Subgroup ((NumberField.RingOfIntegers Work.ClassFieldTower.Kc)ˣ),
        Nonempty (Work.ShafarevichKoch.PDual
            (Work.ShafarevichKoch.H3 (Work.ClassFieldTower.galoisGroup M) ℤ) ≃+
          Additive (((NumberField.RingOfIntegers Work.ClassFieldTower.Kc)ˣ) ⧸ N)))) :
    Work.ShafarevichKoch.KcProTwoPresentationInput := by
  obtain ⟨M, hfin2, hfin3, hN⟩ := h
  exact Work.ShafarevichKoch.kcProTwoPresentationInput_of_contH2DimLe M (hdict M)
    (contH2DimLe_six_of_unitDuality M hfin2 hfin3 hN)

end Work.ShafarevichKoch.UnitHalf
