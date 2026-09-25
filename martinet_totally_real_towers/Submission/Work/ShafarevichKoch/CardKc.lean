import Mathlib
import Submission.Work.ShafarevichKoch.Defs
import Submission.Work.ShafarevichKoch.Kc_unit_eq_or_eq_neg
import Submission.Work.ShafarevichKoch.no_sqrt_neg_one_in_maximalUnramified
import Submission.Work.ShafarevichKoch.card_unramifiedQuadraticLevels_le_classGroupTwoRank

/-!
# `Work.ShafarevichKoch.CardKc` -- the Kummer upper bound for `Kc`, with the sharpness
hypothesis discharged

For `Kc = ℚ(√-30030)` the sharp form of the Kummer two-descent bound
(`card_unramifiedQuadraticLevels_le_classGroupTwoRank`) needs the hypothesis that every unit of
`𝓞 Kc` that becomes a square in the maximal unramified pro-`2` extension `Kc_∅` is already a square
in `Kcˣ`.  Here that hypothesis is *proved*:

* the units of `𝓞 Kc` are `±1` up to squares (`Kc_unit_eq_or_eq_neg`);
* `√-1 ∉ Kc_∅` (`no_sqrt_neg_one_in_maximalUnramified`), i.e. `-1` is not a local square at the
  prime of `Kc` above `2`, equivalently `Kc(√-1)/Kc` is ramified (it is ramified at `2`, where
  `Kc(√-1)/ℚ` has ramification index `4` and `Kc/ℚ` has `2`).

Consequently, for every family of pairwise distinct unramified quadratic subextensions of `Kc_∅`,
the index set has at most `2 ^ classGroupTwoRank Kc` elements, i.e.

`dim_{F₂} H¹(G_∅, F₂) ≤ rank₂ Cl(Kc)`,

the *upper bound* half of the Shafarevich--Koch identification `d(G_∅) = rank₂ Cl(Kc)`.  The lower
bound `5 ≤ d(G_∅)` is genus theory (`Work.ClassFieldTower.hasGenusLevel_witness`, which produces an
unramified exponent-`2` extension of degree `2 ^ 5`).
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Classical
open scoped nonZeroDivisors
open scoped NumberField
open NumberField

noncomputable section

namespace Work.ShafarevichKoch

open Work.ClassFieldTower

/-- **The sharpness hypothesis of the Kummer two-descent, for `Kc`.**  Every unit of `𝓞 Kc` whose
image in `Kcˣ` has a square root in the maximal unramified pro-`2` extension `Kc_∅` is already a
square in `Kcˣ`. -/
theorem hunits_Kc (M : MaximalUnramifiedProP.{0} Kc 2) :
    ∀ (u : RingUnit Kc) (z : M.K),
      z * z = algebraMap Kc M.K (unitEmbed Kc u : Kc) → ∃ y : Kcˣ, unitEmbed Kc u = y ^ 2 := by
  intro u z hz
  obtain ⟨y, hy | hy⟩ := Kc_unit_eq_or_eq_neg u
  · exact ⟨y, hy⟩
  · exfalso
    have hyK : ((unitEmbed Kc u : Kcˣ) : Kc) = -((y : Kc) ^ 2) := by
      rw [hy]
      simp
    have hyM : algebraMap Kc M.K (unitEmbed Kc u : Kc)
        = -(algebraMap Kc M.K (y : Kc)) ^ 2 := by
      rw [hyK, map_neg, map_pow]
    have hz' : z * z = -(algebraMap Kc M.K (y : Kc)) ^ 2 := by rw [hz, hyM]
    have hy0 : (algebraMap Kc M.K (y : Kc)) ≠ 0 := by
      simpa using (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (y.ne_zero) :
        algebraMap Kc M.K (y : Kc) ≠ 0)
    refine no_sqrt_neg_one_in_maximalUnramified M
      ⟨z / algebraMap Kc M.K (y : Kc), ?_⟩
    have ha : algebraMap Kc M.K (y : Kc) * algebraMap Kc M.K (y : Kc) ≠ 0 :=
      mul_ne_zero hy0 hy0
    have hgoal : z / algebraMap Kc M.K (y : Kc) * (z / algebraMap Kc M.K (y : Kc)) = -1 := by
      rw [div_mul_div_comm, hz', pow_two, neg_div, div_self ha]
    rw [hgoal, map_neg, map_one]

/-- **The sharp Kummer upper bound for `Kc`, unconditional.**  Every family of pairwise distinct
unramified quadratic subextensions of `Kc_∅` has at most `2 ^ classGroupTwoRank Kc` members, i.e.
`dim_{F₂} H¹(G_∅, F₂) ≤ rank₂ Cl(Kc)`. -/
theorem card_unramifiedQuadraticLevels_le_Kc {ι : Type*} [Fintype ι]
    (M : MaximalUnramifiedProP.{0} Kc 2)
    (L : ι → IntermediateField Kc M.K) (hNF : ∀ i, NumberField ↥(L i))
    (hfd : ∀ i, FiniteDimensional Kc (L i)) (hgal : ∀ i, IsGalois Kc (L i))
    (h2 : ∀ i, Module.finrank Kc (L i) = 2) (hinj : Function.Injective L) :
    Fintype.card ι ≤ 2 ^ classGroupTwoRank Kc :=
  card_unramifiedQuadraticLevels_le_classGroupTwoRank Kc M L hNF hfd hgal h2 hinj
    (hunits_Kc M)

end Work.ShafarevichKoch
