import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension.SeriesP
import Submission.Work.ORHughesFree.NaturalExtension.rk_toeplitzSeries_sub_mul_le
import Submission.Work.ORHughesFree.NaturalExtension.blim_le_of_eventually_le
import Submission.Work.ORHughesFree.NaturalExtension.blim_of_tendsto
import Submission.Work.ORHughesFree.NaturalExtension.blim_mono
import Submission.Work.ORHughesFree.SkewLaurentSeries.exists_injective_ringHom_skewMonoidAlgebra
import Submission.Work.ORHughesFree.NaturalExtension.envelopeToeplitz
import Submission.Work.ORHughesFree.NaturalExtension.tok_sub_mul_mem_SPideal

namespace Work.ORHughesFree.NaturalExtension

open Matrix

/-- For a polynomial `p : U[t^{±1};τ]`, the Toeplitz *series* family `tok` of the embedded series
`SkewLaurentSeries.toRingHom p` coincides with the truncation family `toeplitzFamily p`: the
`(r, s)` entry of the `(n+1) × (n+1)` matrix is `τ^r (p_{s-r})` in both cases, since the
`k`-th series coefficient of `toRingHom p` is `p.coeff (ofAdd k) = coeffElt p k`. -/
theorem tok_toRingHom_eq_toeplitzFamily {U : Type} [Ring U]
    [MulSemiringAction (Multiplicative ℤ) U]
    (p : SkewMonoidAlgebra U (Multiplicative ℤ)) :
    tok (SkewLaurentSeries.toRingHom p) = toeplitzFamily p := by
  funext n
  ext r s
  rw [toeplitzFamily, toeplitz_apply]
  simp [tok, toeplitzSeries, SkewLaurentSeries.toSeries_apply, coeffElt,
    SkewLaurentSeries.toRingHom]

/-- The composite `mkSP ω rk ∘ tok` of the Toeplitz family of a skew Laurent series with the
quotient map `W U →+* P^U_{ω,τ}`.

`tok` is additive and unital *exactly*, and multiplicative *modulo* the rank-zero ideal
(`tok_sub_mul_mem_SPideal`), so this composition is a ring homomorphism: an element of the
rank-zero ideal is killed by the quotient map, which lets the product in `W U` be replaced by the
product in `U((t;τ))`. -/
noncomputable def psiHom {U : Type} [Ring U] [MulSemiringAction (Multiplicative ℤ) U]
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ Filter.atTop) (rk : SylvesterRank U) :
    SkewLaurentSeries U →+* SP ω rk where
  toFun p := mkSP ω rk (tok p)
  map_one' := by rw [tok_one, map_one]
  map_mul' p q := by
    rw [← map_mul]
    exact Ideal.Quotient.eq.mpr (tok_sub_mul_mem_SPideal ω hω rk p q)
  map_zero' := by rw [tok_zero, map_zero]
  map_add' p q := by rw [tok_add, map_add]

/-- **[JZLA20, (4)]**: the Toeplitz family `tok : U((t;τ)) → W U` of a skew Laurent *series*
descends to a ring homomorphism `Ψ : U((t;τ)) →+* P^U_{ω,τ}`.  On the skew Laurent *polynomial*
part `Ψ` agrees with the Toeplitz family `toeplitzFamily` used in the construction of `f_ω`
(`NaturalExtension.ultrafilterEnvelope_exists2`), because for a polynomial the series Toeplitz
matrix coincides with the truncation `toeplitz (n+1) p`.

Route: `mkSP ω rk ∘ tok` is a ring hom because `tok` is additive and unital *exactly*
(`tok_add`, `tok_zero`, `tok_one` in `NaturalExtension/SeriesP.lean`) and multiplicative *modulo*
`SPideal ω rk`: by `mem_SPideal` and `blimRank_oneByOne` it suffices that
`blim ω (fun n => rk.rk (n+1) (n+1) (defect n) / (n+1)) = 0`, which follows from the rank bound
`rk_toeplitzSeries_sub_mul_le` (the defect has rank at most the constant
`max 0 (-lo p) + max 0 (-lo q)`) together with `blim_mono`, `blim_le_of_eventually_le` and
`blim_of_tendsto` applied to `n ↦ C/(n+1) → 0`.  The identification with `toeplitzFamily` on
polynomials is `(toRingHom p).1 n = p.coeff (Multiplicative.ofAdd n) = coeffElt p n` for the
embedding `SkewLaurentSeries.toRingHom`. -/
theorem exists_Psi {U : Type} [Ring U] [MulSemiringAction (Multiplicative ℤ) U]
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ Filter.atTop) (rk : Work.ORHughesFree.SylvesterRank U) :
    ∃ Ψ : Work.ORHughesFree.SkewLaurentSeries U →+*
        Work.ORHughesFree.NaturalExtension.SP ω rk,
      (∀ p : Work.ORHughesFree.SkewLaurentSeries U,
        Ψ p = Work.ORHughesFree.NaturalExtension.mkSP ω rk
          (Work.ORHughesFree.NaturalExtension.tok p)) ∧
      (∀ p : SkewMonoidAlgebra U (Multiplicative ℤ),
        Ψ (Work.ORHughesFree.SkewLaurentSeries.toRingHom p)
          = Work.ORHughesFree.NaturalExtension.mkSP ω rk
              (Work.ORHughesFree.NaturalExtension.toeplitzFamily p)) := by
  refine ⟨psiHom ω hω rk, ?_, ?_⟩
  · intro p; rfl
  · intro p
    show mkSP ω rk (tok (SkewLaurentSeries.toRingHom p)) = mkSP ω rk (toeplitzFamily p)
    rw [tok_toRingHom_eq_toeplitzFamily p]

end Work.ORHughesFree.NaturalExtension
