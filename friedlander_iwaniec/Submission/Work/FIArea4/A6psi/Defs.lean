/-
# Area 4 (round 6): the §15 vocabulary at **FI's ratio symbol** `(z₂/z₁|d)`

The frozen (`Work.FIArea4.S15cutDefs`/`S15expSumDefs`/`S15stratumDefs`) §15 chain is written at
the *frozen* symbol `(Re(z̄₁z₂)|d)`, while the round-6 kernel `Work.FITop4.Tcut` carries FI's
symbol `(z₂/z₁|d)` (`Work.FITop4.ratioSym`).  The two differ by the twist `(|z₁|²|d)`
(`Work.FIArea7.jacobiSym_re_eq_ratioSym_mul`).

Everything in the §15 chain (the separation of variables, the log-sine Fourier expansion, the
`e`-stratification, the class Cauchy–Schwarz, the variance sums `EvarG` and the Proposition 14.1
summation) is *symbol-agnostic* except for the **coefficient** `S15coef` of a pair `(z₁,z₂,d)`.
This module therefore introduces only the round-6 coefficient and the sums built from it, reusing
`S15theta`, `S15x`, `S15y`, `S15phase`, `S15ixSet`, `S15Y`, `EvarG`, `jwG`, `S15strU`, `S15strV`
and `Work.FITop4.logFac6` unchanged.

Contents:
* `S15w6`, `S15coef6`: the per-pair weight `(φ(d)/d)·(z₂/z₁|d)` and the coefficient
  `2β_{z₁}β̄_{z₂}·(φ(d)/d)·(z₂/z₁|d)` of the round-6 §15 sum;
* `S15expSum6`, `S15expLog6`, `S15psiSum6`: the separated (relaxed) sum, its exponential
  companion (with `logFac6` in place of the angular character) and the `ψ`-cut sum;
* `S15pD6`, `S15pDng6`, `S15expSum6ng`: the per-modulus pieces, with and without the coprimality
  filter of `Tcut`.

The key *round-6* facts (to be proved elsewhere) are:
* the twist `(|z₁|²|d)` **is a class function** on the `e`-strata of FI (15.2): it equals the
  frozen class factor `(e²+a²|oddPart(d/e))` (`A6psi.twist_eq_clsFactor`), so the kernel of the
  round-6 sum factorises *with class factor `1`* — the round-6 §15 chain is the frozen one with a
  different (still `±1`-valued, still class-local) factor;
* consequently the per-modulus class Cauchy–Schwarz of the round-6 sum has the *same* right-hand
  side `Σ_e √(EvarG (4(d/e)) (S15strU β … e))·√(EvarG (4(d/e)) (S15strV β … e))` as the frozen one
  (`A6psi.pDng6_le_EvarG`), so the whole variance half of FI §§11–15 (`S15En.strUvarSum_filtered`,
  `S15En.evarGSumLe`, `S15exSumng_le_assembly`, Proposition 14.1) transfers verbatim.
-/
import Mathlib
import Submission.Work.FITop4.Defs6
import Submission.Work.FIArea4.S15cutDefs
import Submission.Work.FIArea4.S15expSumDefs
import Submission.Work.FIArea4.S15stratumDefs
import Submission.Work.FIArea4.S15prim_defs

namespace Work.FIArea4.A6psi

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The weight `(φ(d)/d)·(z₂/z₁|d)` of a modulus `d` of the round-6 §15 pair sum (the round-6
analogue of `Work.FIArea4.S15w`, with FI's ratio symbol in place of the frozen symbol). -/
def S15w6 (i : Work.FIArea4.S15Id) : ℂ :=
  (((Nat.totient i.2 : ℝ) / (i.2 : ℝ) : ℝ) : ℂ)
    * ((Work.FITop4.ratioSym i.1.1 i.1.2 i.2 : ℤ) : ℂ)

/-- The round-6 coefficient `2 β_{z₁} conj β_{z₂} (φ(d)/d)(z₂/z₁|d)` of a pair (the round-6
analogue of `Work.FIArea4.S15coef`). -/
def S15coef6 (β : GaussianInt → ℂ) (i : Work.FIArea4.S15Id) : ℂ :=
  2 * (β i.1.1 * star (β i.1.2)) * S15w6 i

/-- **The separated (relaxed) round-6 §15 sum**: the round-6 analogue of
`Work.FIArea4.S15expSum`. -/
def S15expSum6 (Pa : Work.FITop.Params) (X j : ℕ) (β : GaussianInt → ℂ) (ℓ : ℤ)
    (u t : ℝ) : ℂ :=
  ∑ i ∈ Work.FIArea4.S15ixSet Pa X j,
    S15coef6 β i * Work.FIArea4.S15theta ℓ i.1.1 i.1.2 * Work.FIArea4.S15phase X j u t i

/-- The round-6 analogue of `Work.FIArea4.S15expLog`: the separated sum with the logarithmic
weight `logFac6` of `Work.FITop4.Tcut` in place of the angular character. -/
def S15expLog6 (Pa : Work.FITop.Params) (X j : ℕ) (β : GaussianInt → ℂ) (u t : ℝ) : ℂ :=
  ∑ i ∈ Work.FIArea4.S15ixSet Pa X j,
    S15coef6 β i * ((Work.FITop4.logFac6 i.1.1 i.1.2 : ℝ) : ℂ)
      * Work.FIArea4.S15phase X j u t i

/-- The round-6 `ψ`-cut sum over the relaxed index set (the round-6 analogue of
`Work.FIArea4.S15psiSum`); for `ψ = A6psi X` and `j = 0` it reindexes the round-6 `A6psiCut`. -/
def S15psiSum6 (Pa : Work.FITop.Params) (X j : ℕ) (ψ : ℝ → ℝ) (β : GaussianInt → ℂ) : ℂ :=
  ∑ i ∈ Work.FIArea4.S15ixSet Pa X j,
    S15coef6 β i * ((Work.FITop4.logFac6 i.1.1 i.1.2 : ℝ) : ℂ)
      * ((ψ (|Work.FIArea4.S15x i.1.1 i.1.2| * Work.FIArea4.S15y X j i.2 i.1.1 i.1.2) : ℝ) : ℂ)

/-- The round-6 per-modulus §15 sum **with** the coprimality filter of `Tcut` (the round-6
analogue of `Work.FIArea4.S15pD`). -/
def S15pD6 (Pa : Work.FITop.Params) (X j d : ℕ) (β : GaussianInt → ℂ) (ℓ : ℤ)
    (u t : ℝ) : ℂ :=
  ∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
    (if Work.FIPlan.GaussCoprime z1 z2 ∧ X < d ∧
        4 * d ∣ Work.FIPlan.absDelta z1 z2 ∧ 0 < Work.FIPlan.absDelta z1 z2
      then S15coef6 β ((z1, z2), d) * Work.FIArea4.S15theta ℓ z1 z2
        * Work.FIArea4.S15phase X j u t ((z1, z2), d)
      else 0)

/-- The round-6 per-modulus §15 sum **without** the coprimality filter (the round-6 analogue of
`Work.FIArea4.S15pDng`). -/
def S15pDng6 (Pa : Work.FITop.Params) (X j d : ℕ) (β : GaussianInt → ℂ) (ℓ : ℤ)
    (u t : ℝ) : ℂ :=
  ∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
    (if X < d ∧ 4 * d ∣ Work.FIPlan.absDelta z1 z2 ∧ 0 < Work.FIPlan.absDelta z1 z2
      then S15coef6 β ((z1, z2), d) * Work.FIArea4.S15theta ℓ z1 z2
        * Work.FIArea4.S15phase X j u t ((z1, z2), d)
      else 0)

/-- The unfiltered separated round-6 sum (the round-6 analogue of
`Work.FIArea4.S15expSumng`). -/
def S15expSum6ng (Pa : Work.FITop.Params) (X j : ℕ) (β : GaussianInt → ℂ) (ℓ : ℤ)
    (u t : ℝ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 (Work.FIArea4.S15Y Pa X j), S15pDng6 Pa X j d β ℓ u t

/-- `S15expSum6` is the sum of its per-modulus pieces `S15pD6` (the round-6 analogue of
`Work.FIArea4.S15expSum_eq_sum_pD`). -/
lemma S15expSum6_eq_sum_pD (Pa : Work.FITop.Params) (X j : ℕ) (β : GaussianInt → ℂ) (ℓ : ℤ)
    (u t : ℝ) :
    S15expSum6 Pa X j β ℓ u t = ∑ d ∈ Finset.Icc 1 (Work.FIArea4.S15Y Pa X j),
      S15pD6 Pa X j d β ℓ u t := by
  classical
  let G : (GaussianInt × GaussianInt) × ℕ → ℂ := fun p =>
    (if Work.FIPlan.GaussCoprime p.1.1 p.1.2 ∧ X < p.2 ∧
        4 * p.2 ∣ Work.FIPlan.absDelta p.1.1 p.1.2 ∧ 0 < Work.FIPlan.absDelta p.1.1 p.1.2
     then S15coef6 β p * Work.FIArea4.S15theta ℓ p.1.1 p.1.2
       * Work.FIArea4.S15phase X j u t p else 0)
  have h1 : S15expSum6 Pa X j β ℓ u t
      = ∑ p ∈ (Work.FITop.boxN Pa ×ˢ Work.FITop.boxN Pa) ×ˢ Finset.Icc 1
          (Work.FIArea4.S15Y Pa X j), G p := by
    unfold S15expSum6 Work.FIArea4.S15ixSet
    rw [Finset.sum_filter]
    rfl
  have h2 : (∑ p ∈ (Work.FITop.boxN Pa ×ˢ Work.FITop.boxN Pa) ×ˢ
        Finset.Icc 1 (Work.FIArea4.S15Y Pa X j), G p)
      = ∑ d ∈ Finset.Icc 1 (Work.FIArea4.S15Y Pa X j), S15pD6 Pa X j d β ℓ u t := by
    rw [Finset.sum_product, Finset.sum_product, Work.FIArea4.sum_comm3]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    unfold S15pD6
    rfl
  exact h1.trans h2

/-- The pieces vanish for `d ≤ X` (the round-6 analogue of `Work.FIArea4.S15pD_eq_zero_of_le`). -/
lemma S15pDng6_eq_zero_of_le (Pa : Work.FITop.Params) (X j d : ℕ) (β : GaussianInt → ℂ)
    (ℓ : ℤ) (u t : ℝ) (h : d ≤ X) : S15pDng6 Pa X j d β ℓ u t = 0 := by
  rw [S15pDng6]
  refine Finset.sum_eq_zero (fun z1 _ => Finset.sum_eq_zero (fun z2 _ => ?_))
  rw [if_neg (fun hh => absurd hh.1 (not_lt.mpr h))]

end

end Work.FIArea4.A6psi
