import Mathlib
import Submission.Work.WingbergH3.Dual
import Submission.Work.WingbergRoute.gsFWall

/-!
# `Work.WingbergH3.H3Wall` -- the `H³`-half of Wingberg's duality, reduced

This module proves the machine-checked implication web between the three forms of the `H³`-half of
Wingberg's duality (`H3UnitDualityWall`, `H3DeficiencyWall`, `SharpH3Wall`, see `Defs.lean`) and the
walls of `Submission/Work/WingbergRoute/`, and derives the consumer's relation count
`dim_{𝔽₂} H²(G_∅,𝔽₂) ≤ d₁(G_∅) + d₂(O_F^×)`.

The only mathematical input is the general bookkeeping lemma
`card_twoTorsionH3_le_of_dual_quotient`: if the Pontryagin dual of `H³(G_∅,ℤ)` is a quotient of a
commutative group `B`, then the `2`-torsion of `H³(G_∅,ℤ)` has at most `#B` elements.  For `Kc`
this is applied with `B = (𝓞 Kc)^× = {±1}` (`#B = 2`, giving `#H³[2] ≤ 2`), and in general with
`B = (𝓞 F)^× ⧸ N`, whose cardinality is bounded by `2 ^ d₂(O_F^×) = #((𝓞 F)^×/((𝓞 F)^×)²)`
(Dirichlet; `Work.ClassFieldTower.unitTwoRank_eq_finrank_units_modSquares`).

## Main declarations

* `Work.WingbergH3.card_twoTorsionH3_le_of_dual_quotient`;
* `Work.WingbergH3.H3DeficiencyWall_of_H3UnitDualityWall`,
  `Work.WingbergH3.H3DeficiencyWall_of_sharpH3Wall`;
* `Work.WingbergH3.H3DeficiencyWall_iff_gsFDeficiencyWall`,
  `Work.WingbergH3.H3DeficiencyWall_Kc_iff_kcH3Wall`;
* `Work.WingbergH3.shafarevichBound_of_H3DeficiencyWall`,
  `Work.WingbergH3.gsFWingbergWall_of_H3DeficiencyWall`,
  `Work.WingbergH3.kcWingbergWall_of_H3DeficiencyWall`;
* `Work.WingbergH3.H3UnitDualityWall_Kc_iff_kcUnitDualityWall`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 16000000

open scoped Classical
open NumberField

noncomputable section

namespace Work.WingbergH3

open Work.ConCohomology Work.ShafarevichKoch Work.ClassFieldTower

variable {F : Type*} [Field F] [NumberField F]

/-- **The `2`-torsion of `H³(G_∅,ℤ)` is no larger than any group whose quotient is its Pontryagin
dual.**  This is the general bookkeeping behind the unit half of Wingberg's duality: the
universal-norm quotient `Ĥ⁰(G_∅, O_{F_∅}^×)` is a quotient of `(𝓞 F)^×`, and
`H³(G_∅,ℤ)^∨ ≅ Ĥ⁰(G_∅, O_{F_∅}^×)`, so `#H³(G_∅,ℤ)[2] ≤ #(𝓞 F)^×`
(`Work.ShafarevichKoch.card_twoTorsion_of_dual_quotient_le`). -/
theorem card_twoTorsionH3_le_of_dual
    (M : MaximalUnramifiedProP.{0} F 2)
    (hfin3 : Finite (H3 (galoisGroup M) ℤ))
    {C : Type*} [CommGroup C] [Finite C]
    (e : PDual (H3 (galoisGroup M) ℤ) ≃+ Additive C) :
    Nat.card (twoTorsionH3 (galoisGroup M)) ≤ Nat.card C := by
  haveI : Fintype (H3 (galoisGroup M) ℤ) := Fintype.ofFinite _
  calc Nat.card (twoTorsionH3 (galoisGroup M))
      = Nat.card {φ : PDual (H3 (galoisGroup M) ℤ) // (2 : ℕ) • φ = 0} :=
        (Work.ShafarevichKoch.card_twoTorsion_dual_eq_card_twoTorsion
          (H3 (galoisGroup M) ℤ)).symm
    _ = Nat.card {y : Additive C // (2 : ℕ) • y = 0} :=
        Work.ShafarevichKoch.card_twoTorsion_addEquiv (A := PDual (H3 (galoisGroup M) ℤ)) e
    _ ≤ Nat.card (Additive C) :=
        Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
    _ = Nat.card C := Nat.card_congr (Equiv.mk Additive.toMul Additive.ofMul
        (fun _ => rfl) (fun _ => rfl))

/-- **The unit half of Wingberg's duality gives the `H³`-half.**  If the Pontryagin dual of
`H³(G_∅,ℤ)` is a quotient of the finite group `(𝓞 F)^×/((𝓞 F)^×)²` of order
`2 ^ d₂(O_F^×)`, then `#H³(G_∅,ℤ)[2] ≤ 2 ^ d₂(O_F^×)`.

This is the passage from the classical normalisation of Wingberg's theorem to the deficiency form
used by the consumers of `Submission/Work/WingbergRoute/`. -/
theorem H3DeficiencyWall_of_H3UnitDualityWall (h : H3UnitDualityWall F) :
    H3DeficiencyWall F := by
  obtain ⟨M, h2, h3, hd, N, _hsq, hfinN, hcard, ⟨e⟩⟩ := h
  haveI := hfinN
  exact ⟨M, h2, h3, hd, (card_twoTorsionH3_le_of_dual M h3 e).trans hcard⟩

/-- **The sharp form of the duality implies the deficiency form.**  Wingberg's theorem with the
roots of unity removed gives `#H³[2] ≤ 2 ^ (d₂(O_F^×) - 1) ≤ 2 ^ d₂(O_F^×)`. -/
theorem H3DeficiencyWall_of_sharpH3Wall (h : SharpH3Wall F) : H3DeficiencyWall F := by
  obtain ⟨M, h2, h3, hd, hle⟩ := h
  exact ⟨M, h2, h3, hd,
    hle.trans (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _))⟩

/-- **The `H³`-half of the wall at `gsF` is literally `Work.WingbergRoute.gsFDeficiencyWall`.** -/
theorem H3DeficiencyWall_iff_gsFDeficiencyWall :
    H3DeficiencyWall gsF ↔ Work.WingbergRoute.gsFDeficiencyWall :=
  Iff.rfl

/-- **The `H³`-half of the wall at `Kc` is `Work.WingbergRoute.KcH3Wall`** (`#H³(G_∅,ℤ)[2] ≤ 2`),
because `d₂(O_Kc^×) = 1` and `#H¹(G_∅,𝔽₂) = 2^5` for *every* maximal unramified pro-`2` extension
(`Work.ShafarevichKoch.H2Half.natCard_H1_zmodTwo_galoisGroup_Kc`, proved in the workspace without
class field theory). -/
theorem H3DeficiencyWall_Kc_iff_kcH3Wall :
    H3DeficiencyWall Kc ↔ Work.WingbergRoute.KcH3Wall := by
  constructor
  · rintro ⟨M, h2, h3, _hd, hle⟩
    rw [Work.WingbergRoute.unitTwoRank_Kc] at hle
    exact ⟨M, h2, h3, by simpa using hle⟩
  · rintro ⟨M, h2, h3, hle⟩
    exact ⟨M, h2, h3, ⟨5, Work.ShafarevichKoch.H2Half.natCard_H1_zmodTwo_galoisGroup_Kc M⟩,
      by rw [Work.WingbergRoute.unitTwoRank_Kc]; simpa using hle⟩

/-- **The `H³`-half gives Shafarevich's relation-rank bound**: `ShafarevichBound F M` for some
maximal unramified pro-`2` extension `M` of `F`.  This is
`Work.WingbergRoute.contH2DimLe_of_deficiencyData`, which combines the (unconditional) `H²`-half of
the relation count with the `H³`-half. -/
theorem contH2DimLe_of_H3DeficiencyWall {F : Type} [Field F] [NumberField F]
    (h : H3DeficiencyWall F) :
    ∃ M : MaximalUnramifiedProP.{0} F 2, ∃ k d : ℕ,
      Nat.card (Work.RelatorRank.contH2 (galoisGroup M)) = 2 ^ k ∧
        Nat.card (H1 (galoisGroup M) (ZMod 2)) = 2 ^ d ∧ k ≤ d + unitTwoRank F := by
  obtain ⟨M, h2, h3, ⟨d, hd⟩, htors⟩ := h
  obtain ⟨k, hk, hcard⟩ :=
    Work.WingbergRoute.contH2DimLe_of_deficiencyData M h2 h3 d hd htors
  exact ⟨M, k, d, hcard, hd, hk⟩

/-- **The `H³`-half gives Shafarevich's relation-rank bound** (`Work.WingbergRoute.ShafarevichBound`),
i.e. `Work.WingbergRoute.gsFWingbergWall` at `gsF` and `Work.WingbergRoute.KcWingbergWall` at `Kc`. -/
theorem shafarevichBound_of_H3DeficiencyWall {F : Type} [Field F] [NumberField F]
    (h : H3DeficiencyWall F) :
    ∃ M : MaximalUnramifiedProP.{0} F 2, Work.WingbergRoute.ShafarevichBound F M := by
  obtain ⟨M, k, d, hcard, hd, hk⟩ := contH2DimLe_of_H3DeficiencyWall h
  exact ⟨M, k, d, hcard, hd, hk⟩

/-- **The totally real wall `gsFWingbergWall` from the `H³`-half.** -/
theorem gsFWingbergWall_of_H3DeficiencyWall (h : H3DeficiencyWall gsF) :
    Work.WingbergRoute.gsFWingbergWall :=
  Work.WingbergRoute.gsFWingbergWall_of_deficiencyInput h

/-- **The `Kc` wall from the `H³`-half.** -/
theorem kcWingbergWall_of_H3DeficiencyWall (h : H3DeficiencyWall Kc) :
    Work.WingbergRoute.KcWingbergWall :=
  Work.WingbergRoute.kcWingbergWall_of_kcH3Wall (H3DeficiencyWall_Kc_iff_kcH3Wall.mp h)

/-! ## The units of `Kc` have exponent `2` -/

/-- **Every unit of `Kc` is its own inverse**: `(𝓞 Kc)^× = {±1}`
(`Work.ShafarevichKoch.unitEmbed_Kc_eq_one_or_eq_neg_one`), so the group of units has exponent
`2`, hence `(𝓞 Kc)^×` modulo squares is the group itself.  This is the small bookkeeping fact that
makes the general unit-duality wall reduce to `Work.WingbergRoute.KcUnitDualityWall`. -/
theorem ringUnit_Kc_mul_self (u : RingUnit Kc) : u * u = 1 := by
  have hinj : Function.Injective (Work.ShafarevichKoch.unitEmbed Kc) := fun x y h => by
    apply Units.ext
    have h' : ((x : 𝓞 Kc) : Kc) = ((y : 𝓞 Kc) : Kc) := by
      simpa [Work.ShafarevichKoch.unitEmbed_coe] using congrArg (fun z : Kcˣ => (z : Kc)) h
    exact Subtype.ext h'
  apply hinj
  simp only [Work.ShafarevichKoch.unitEmbed_mul, Work.ShafarevichKoch.unitEmbed_one]
  rcases Work.ShafarevichKoch.unitEmbed_Kc_eq_one_or_eq_neg_one u with h | h
  · rw [h, one_mul]
  · rw [h, neg_mul_neg, one_mul]

/-! ## The `Kc` unit half of Wingberg's duality -/

/-- **The `H³`-half in its unit normalisation, at `Kc`, is `Work.WingbergRoute.KcUnitDualityWall`.**
The two statements differ only in bookkeeping: the cardinality bound `#((𝓞 Kc)^× ⧸ N) ≤ 2` is
automatic because `(𝓞 Kc)^× = {±1}`, the squares clause is automatic because every element of
`{±1}` squares to `1`, and the generator-rank clause is
`Work.ShafarevichKoch.H2Half.natCard_H1_zmodTwo_galoisGroup_Kc`. -/
theorem H3UnitDualityWall_Kc_iff_kcUnitDualityWall :
    H3UnitDualityWall Kc ↔ Work.WingbergRoute.KcUnitDualityWall := by
  constructor
  · rintro ⟨M, h2, h3, _hd, N, _hsq, _hfinN, _hcard, hN⟩
    exact ⟨M, h2, h3, N, hN⟩
  · rintro ⟨M, h2, h3, N, hN⟩
    haveI : Finite (RingUnit Kc) := Work.ShafarevichKoch.finite_RingUnit_Kc
    have hsq : Subgroup.closure (Set.range (fun x : RingUnit Kc => x ^ 2)) ≤ N := by
      rw [Subgroup.closure_le]
      rintro _ ⟨x, rfl⟩
      simpa only [pow_two, ringUnit_Kc_mul_self x, SetLike.mem_coe] using N.one_mem
    have hfin : Finite (RingUnit Kc ⧸ N) := inferInstance
    have hcard : Nat.card (RingUnit Kc ⧸ N) ≤ 2 ^ unitTwoRank Kc := by
      rw [Work.WingbergRoute.unitTwoRank_Kc]
      exact (Work.ShafarevichKoch.card_quotient_le_of_subgroup N).trans
        Work.ShafarevichKoch.card_RingUnit_Kc_le_two
    exact ⟨M, h2, h3,
      ⟨5, Work.ShafarevichKoch.H2Half.natCard_H1_zmodTwo_galoisGroup_Kc M⟩,
      N, hsq, hfin, hcard, hN⟩

