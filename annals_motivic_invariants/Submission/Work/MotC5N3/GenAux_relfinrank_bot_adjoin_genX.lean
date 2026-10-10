import Mathlib
import Submission.Work.MotC5N3.Defs
import Submission.Work.MotV5.Defs
import Submission.Work.MotV.Defs
import Submission.Work.MotC5N3.TwistField.kleinField_eq_adjoin_genXY
import Submission.Work.MotC2.TranslationDefs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotC5N3
open Work.MotV5
open Polynomial IntermediateField

/-! ## The relative degree of a simple transcendental extension

If `x` is transcendental over `K`, then the simple extension `K⟮x⟯` has infinite degree over
`K ≅ ⊥`, so its `relfinrank` over the bottom intermediate field `⊥` vanishes (`relfinrank` is
`Cardinal.toNat` of the relative rank, hence `0` for an infinite-dimensional extension).

The proof exhibits the infinite `↥⊥`-linearly independent family `1, x, x², …` inside `↥K⟮x⟯`.
A vanishing `↥⊥`-linear combination `∑ cⱼ xʲ = 0` is pushed into `L`; each coefficient `cⱼ ∈ ⊥`
lies in the range of `algebraMap K L` (`IntermediateField.mem_bot`), so it can be rewritten as
`algebraMap K L kⱼ`. The resulting identity `aeval x (∑ C kⱼ · Xʲ) = 0` forces the polynomial to be
`0` by transcendence, so every `kⱼ` — hence every `cⱼ` — vanishes. -/
theorem relfinrank_bot_adjoin_singleton_eq_zero_of_transcendental {K L : Type*} [Field K] [Field L]
    [Algebra K L] {x : L} (hx : Transcendental K x) :
    (⊥ : IntermediateField K L).relfinrank (IntermediateField.adjoin K ({x} : Set L)) = 0 := by
  have h : (⊥ : IntermediateField K L) ≤ IntermediateField.adjoin K ({x} : Set L) := bot_le
  rw [IntermediateField.relfinrank_eq_finrank_of_le h]
  set T : IntermediateField ↥(⊥ : IntermediateField K L) L := IntermediateField.extendScalars h
  have hw : x ∈ (T : Set L) := IntermediateField.mem_adjoin_simple_self K x
  let w : ↥T := ⟨x, hw⟩
  have hwL : (w : L) = x := rfl
  have hLI : LinearIndependent ↥(⊥ : IntermediateField K L) (fun n : ℕ => w ^ n) := by
    rw [linearIndependent_iff']
    intro s g hg i hi
    -- push the vanishing linear combination into `L`
    have h1 : (algebraMap ↥T L) (∑ j ∈ s, g j • w ^ j) = 0 := by rw [hg, map_zero]
    rw [map_sum] at h1
    have h2 : ∀ j ∈ s, (algebraMap ↥T L) (g j • w ^ j)
        = ((g j : ↥(⊥ : IntermediateField K L)) : L) * x ^ j := by
      intro j _
      simp only [map_mul, map_pow, Algebra.smul_def, IntermediateField.coe_algebraMap_apply,
        IntermediateField.algebraMap_apply, hwL]
    rw [Finset.sum_congr rfl h2] at h1
    -- lift the coefficients from `⊥ ≅ K` to `K`
    choose k hk using fun j : ℕ => mem_bot.mp (g j).2
    -- the corresponding polynomial over `K` kills `x`
    have hP : Polynomial.aeval x (∑ j ∈ s, Polynomial.C (k j) * Polynomial.X ^ j) = 0 := by
      rw [map_sum]
      simp only [map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X]
      rw [show (∑ j ∈ s, algebraMap K L (k j) * x ^ j) = ∑ j ∈ s, ↑(g j) * x ^ j from
        Finset.sum_congr rfl fun j _ => by rw [hk j]]
      exact h1
    have hP0 : (∑ j ∈ s, Polynomial.C (k j) * Polynomial.X ^ j) = 0 :=
      (transcendental_iff.mp hx) _ hP
    -- hence all the coefficients vanish
    have hki : k i = 0 := by
      have hc : (∑ j ∈ s, Polynomial.C (k j) * Polynomial.X ^ j).coeff i = k i := by
        rw [Polynomial.finsetSum_coeff]
        simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
        rw [Finset.sum_eq_single i]
        · simp
        · intro j _ hji
          simp [Ne.symm hji]
        · intro hi'
          exact absurd hi hi'
      rw [← hc, hP0]
      simp
    have hgi : ((g i : ↥(⊥ : IntermediateField K L)) : L) = 0 := by
      rw [← hk i, hki]
      simp
    exact Subtype.ext (by simpa using hgi)
  exact hLI.finrank_eq_zero_of_infinite

/-- **`genX` is transcendental over `K`.**

`Work.MotV.genX` and `Work.MotC2.genX` are the same element (`Work.MotC2.coordX_eq_mk`), and the
`x`-coordinate of the function field of a Weierstrass curve is transcendental over the base field
(`Work.MotC2.transcendental_genX`). Transcendence over `Work.MotC5N3.KbA K = AlgebraicClosure (K)`
descends to `K` along the tower. -/
theorem transcendental_genX_ratFunc (𝕜 : Type) [Field 𝕜] {K : Type} [Field K] [Algebra 𝕜 K] (D : Work.MotV.KleinData 𝕜) :
    Transcendental (K) (Work.MotV.genX (D.E.baseChange (Work.MotC5N3.KbA K))) := by
  have hbridge : Work.MotV.genX (D.E.baseChange (Work.MotC5N3.KbA K))
      = Work.MotC2.genX (D.E.baseChange (Work.MotC5N3.KbA K)) := by
    rw [Work.MotV.genX, Work.MotC2.genX, Work.MotC2.coordX_eq_mk]
  have hxtKb : Transcendental (Work.MotC5N3.KbA K)
      (Work.MotV.genX (D.E.baseChange (Work.MotC5N3.KbA K))) := by
    rw [hbridge]
    exact Work.MotC2.transcendental_genX _
  exact fun halg => hxtKb (IsAlgebraic.tower_top (Work.MotC5N3.KbA K) halg)

theorem GenAux_relfinrank_bot_adjoin_genX (𝕜 : Type) [Field 𝕜] {K : Type} [Field K] [Algebra 𝕜 K]
    (D : Work.MotV.KleinData 𝕜) (g : K) :
    (⊥ : IntermediateField (K) (Work.MotC5N3.OmA K D)).relfinrank
      (IntermediateField.adjoin (K)
        {Work.MotV.genX (D.E.baseChange (Work.MotC5N3.KbA K))}) = 0 :=
  relfinrank_bot_adjoin_singleton_eq_zero_of_transcendental (transcendental_genX_ratFunc 𝕜 D)

end Work.MotC5N3