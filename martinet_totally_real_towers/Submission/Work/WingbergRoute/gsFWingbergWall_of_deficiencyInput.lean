import Mathlib
import Submission.Work.WingbergRoute.All
import Submission.Work.WingbergRoute.natCard_H2Z_quot_two_le_card_H1_zmodTwo_gsF
import Submission.Work.ShafarevichKoch.UnitHalf.kcProTwoPresentationInput_of_unitDuality
import Submission.Work.ShafarevichKoch.CountZ

/-!
# `Work.WingbergRoute.gsFWingbergWall_of_deficiencyInput`

**The deficiency form of the totally real Wall.**  Over the totally real quadratic base
`gsF = ℚ(√2576450045)`, suppose that the maximal unramified pro-`2` group `G_∅ = Gal(gsF_∅/gsF)`
(realised by some `M`) has

* finite `H²(G_∅,ℤ)` and finite `H³(G_∅,ℤ)`;
* `#H¹(G_∅,𝔽₂) = 2^d` for some `d` (i.e. the generator rank is `d`);
* `#H³(G_∅,ℤ)[2] ≤ 2 ^ d₂(O_gsF^×)` -- the *deficiency* input.

Then `G_∅` satisfies Shafarevich's relation-rank bound
`dim_{𝔽₂} H²(G_∅,𝔽₂) ≤ d + d₂(O_gsF^×)`, i.e. `Work.WingbergRoute.gsFWingbergWall` holds.

The mathematical content is the `ℤ`-power sequence of `Hajir--Maire--Ramakrishna`
(arXiv:2103.09508, §1.2),

```
#H²(G,ℤ/2) = #(H²(G,ℤ) / 2H²(G,ℤ)) · #(H³(G,ℤ)[2]) ,
```

(`Work.ShafarevichKoch.natCard_H2_zmodTwo_eq`, proved in this workspace) combined with the *`H²`-half*

```
#(H²(G,ℤ) / 2H²(G,ℤ)) ≤ #H¹(G,𝔽₂)
```

of `Work.WingbergRoute.natCard_H2Z_quot_two_le_card_H1_zmodTwo_gsF`.  Both factors are bounded by
the hypotheses, and their product is `2^(d + d₂(O_gsF^×))`; the bound is then read off in the
finite-dimensional `𝔽₂`-vector space `H²(G,𝔽₂)`.

Thus the *whole* arithmetic content of the totally real Wall is the deficiency input
`#H³(G_∅,ℤ)[2] ≤ 2 ^ d₂(O_gsF^×)` together with the finiteness of `H²(G_∅,ℤ)` and `H³(G_∅,ℤ)`;
the `H²`-half is unconditional.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open scoped Classical

noncomputable section

namespace Work.WingbergRoute

/-- **Shafarevich's relation-rank bound from the deficiency input**, for an arbitrary number
field base `F`.

If `H²(G_∅,ℤ)` and `H³(G_∅,ℤ)` are finite, `#H¹(G_∅,𝔽₂) = 2 ^ d` and
`#H³(G_∅,ℤ)[2] ≤ 2 ^ d₂(O_F^×)`, then `dim_{𝔽₂} H²(G_∅,𝔽₂) ≤ d + d₂(O_F^×)`.

The proof multiplies the two halves of the `ℤ`-power sequence: the `H²`-half is
`Work.WingbergRoute.natCard_H2Z_quot_two_le_card_H1_zmodTwo_of_finite` (unconditional in the base
field, only the finiteness of `H¹(G_∅,𝔽₂)` is needed, and that follows from `#H¹ = 2 ^ d`), and the
`H³`-half is the hypothesis. -/
theorem contH2DimLe_of_deficiencyData {F : Type} [Field F] [NumberField F]
    (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} F 2)
    (hfin2 : Finite (Work.ConCohomology.H2 (Work.ClassFieldTower.galoisGroup M) ℤ))
    (hfin3 : Finite (Work.ShafarevichKoch.H3 (Work.ClassFieldTower.galoisGroup M) ℤ))
    (d : ℕ)
    (hd : Nat.card (Work.ConCohomology.H1 (Work.ClassFieldTower.galoisGroup M) (ZMod 2)) = 2 ^ d)
    (htors : Nat.card (Work.ShafarevichKoch.twoTorsionH3 (Work.ClassFieldTower.galoisGroup M)) ≤
      2 ^ Work.ClassFieldTower.unitTwoRank F) :
    Work.RelatorRank.ContH2DimLe (Work.ClassFieldTower.galoisGroup M)
      (d + Work.ClassFieldTower.unitTwoRank F) := by
  haveI hfin2' : Finite (Work.ConCohomology.H2 (Work.ClassFieldTower.galoisGroup M) ℤ) := hfin2
  haveI hfin3' : Finite (Work.ShafarevichKoch.H3 (Work.ClassFieldTower.galoisGroup M) ℤ) := hfin3
  -- `H¹(G_∅,𝔽₂)` is finite, since its cardinality is `2 ^ d`
  have hfinH1 : Finite (Work.ConCohomology.H1 (Work.ClassFieldTower.galoisGroup M) (ZMod 2)) :=
    Nat.finite_of_card_ne_zero (by rw [hd]; exact pow_ne_zero _ (by norm_num))
  -- (A) the `H²`-half: `#(H²(G,ℤ)/2H²(G,ℤ)) ≤ #H¹(G,𝔽₂) = 2 ^ d`
  have hA : Nat.card (Work.ConCohomology.H2 (Work.ClassFieldTower.galoisGroup M) ℤ ⧸
      Work.ShafarevichKoch.twoMulH2 (Work.ClassFieldTower.galoisGroup M)) ≤ 2 ^ d := by
    rw [← hd]
    exact Work.WingbergRoute.natCard_H2Z_quot_two_le_card_H1_zmodTwo_of_finite M hfinH1
  -- the product bound of the `ℤ`-power sequence
  have hcard : Nat.card (Work.ConCohomology.H2 (Work.ClassFieldTower.galoisGroup M) (ZMod 2)) ≤
      2 ^ (d + Work.ClassFieldTower.unitTwoRank F) := by
    rw [Work.ShafarevichKoch.natCard_H2_zmodTwo_eq]
    calc Nat.card (Work.ConCohomology.H2 (Work.ClassFieldTower.galoisGroup M) ℤ ⧸
          Work.ShafarevichKoch.twoMulH2 (Work.ClassFieldTower.galoisGroup M)) *
          Nat.card (Work.ShafarevichKoch.twoTorsionH3 (Work.ClassFieldTower.galoisGroup M))
        ≤ 2 ^ d * 2 ^ Work.ClassFieldTower.unitTwoRank F := Nat.mul_le_mul hA htors
      _ = 2 ^ (d + Work.ClassFieldTower.unitTwoRank F) := (pow_add 2 d _).symm
  -- `H²(G_∅,𝔽₂)` is finite (both factors of the product identity are non-zero)
  haveI hfin : Finite (Work.ConCohomology.H2 (Work.ClassFieldTower.galoisGroup M) (ZMod 2)) := by
    have hceq := Work.ShafarevichKoch.natCard_H2_zmodTwo_eq
      (G := Work.ClassFieldTower.galoisGroup M)
    have hne1 : Nat.card (Work.ConCohomology.H2 (Work.ClassFieldTower.galoisGroup M) ℤ ⧸
        Work.ShafarevichKoch.twoMulH2 (Work.ClassFieldTower.galoisGroup M)) ≠ 0 :=
      Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩
    haveI : Finite (Work.ShafarevichKoch.twoTorsionH3 (Work.ClassFieldTower.galoisGroup M)) :=
      Finite.of_injective Subtype.val Subtype.val_injective
    have hne2 : Nat.card (Work.ShafarevichKoch.twoTorsionH3
        (Work.ClassFieldTower.galoisGroup M)) ≠ 0 :=
      Nat.card_ne_zero.mpr ⟨⟨0, by simp⟩, inferInstance⟩
    exact Nat.finite_of_card_ne_zero (by rw [hceq]; exact Nat.mul_ne_zero hne1 hne2)
  -- `H²(G_∅,𝔽₂)` is an `𝔽₂`-vector space (every action of `G` on `ℤ/2` is trivial)
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
  have hle : 2 ^ Module.finrank (ZMod 2)
        (Work.RelatorRank.contH2 (Work.ClassFieldTower.galoisGroup M)) ≤
      2 ^ (d + Work.ClassFieldTower.unitTwoRank F) := by
    rw [← hcardfin]
    exact hcard
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hle

theorem gsFWingbergWall_of_deficiencyInput
    (h : ∃ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Work.WingbergRoute.gsF 2,
      Finite (Work.ConCohomology.H2 (Work.ClassFieldTower.galoisGroup M) ℤ) ∧
      Finite (Work.ShafarevichKoch.H3 (Work.ClassFieldTower.galoisGroup M) ℤ) ∧
      (∃ d : ℕ, Nat.card (Work.ConCohomology.H1 (Work.ClassFieldTower.galoisGroup M) (ZMod 2)) = 2 ^ d) ∧
      Nat.card (Work.ShafarevichKoch.twoTorsionH3 (Work.ClassFieldTower.galoisGroup M)) ≤
        2 ^ Work.ClassFieldTower.unitTwoRank Work.WingbergRoute.gsF) :
    Work.WingbergRoute.gsFWingbergWall := by
  obtain ⟨M, hfin2, hfin3, ⟨d, hd⟩, htors⟩ := h
  obtain ⟨k, hk, hcard⟩ := contH2DimLe_of_deficiencyData M hfin2 hfin3 d hd htors
  exact ⟨M, k, d, hcard, hd, hk⟩

end Work.WingbergRoute
