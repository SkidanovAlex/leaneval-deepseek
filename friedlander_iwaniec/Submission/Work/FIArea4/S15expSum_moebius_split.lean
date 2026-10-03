/-
# FI §15: the exact Möbius split of the separated sum `S15expSum`

`Work.FIArea4.S15expSum` carries the *pair* condition `GaussCoprime z₁ z₂` (FI (15.2)).  That
condition is not a condition on the classes of the class Cauchy–Schwarz, so it has to be removed
*before* the large sieve is applied, and (unlike in FI, whose frozen statements have no room for
the `O(P^{-1}N²)` loss) it has to be removed **exactly**.

The exact removal is the Möbius identity `Σ_{w ∣ z₁, w ∣ z₂} μ w = [ (z₁,z₂) = 1 ]`
(`Work.FIArea4.gaussMoebius_coprime_indicator`).  This module pushes that identity through the
per-modulus sums of `Work.S15alt.S15pD_eq_moebius` and sums over the modulus, obtaining

  `S15expSum Pa X j β ℓ u t = ∑_{w ∈ W} μ w · S15expSumng Pa X j (restrArray β w) ℓ u t`

where `S15expSumng` is the *unfiltered* separated sum (`Work.FIArea4.S15expSumng`) and
`restrArray β w = z ↦ (if w ∣ z then β z else 0)`.  Its point is that each summand on the right
is an unfiltered §15 sum of an array that is again an `IsPrimBoxCoeff` (the support only shrinks),
so the whole unfiltered machinery is applicable *termwise*; and, because the number of Gaussian
integers of norm `≤ 2(1+θ)N` that divide a fixed support point `z` and are not units is controlled
by `NoSmallPrimes` (`gnorm w > Pa.Pz` for every non-unit divisor of a support point), the
`Σ_{w}` is logarithmically cheap.

Consequently

  `‖S15expSum β‖ ≤ ∑_{w ∈ W} ‖S15expSumng (restrArray β w)‖`,

and the whole task reduces to a *single* family of estimates, one per `w`, in which the modulus
`4d` of the `w`-term is effectively `4d/gcd(4d, gnorm w)` and the box is the *shrunk* polar box of
parameter `Pa.N / gnorm w` (the substitution `z = w u`); this is what supplies the required decay
in `w`.  See `Submission/Work/FIArea4/S15psi_NOTES.md`.
-/
import Mathlib
import Submission.Work.FIArea4.S15expSumDefs
import Submission.Work.FIArea4.S15cutDefs
import Submission.Work.FIArea4.S15prim_defs
import Submission.Work.S15alt.Defs
import Submission.Work.FIPlan.Interface
import Submission.Work.FIArea4.gaussMoebius_coprime_indicator


namespace Work.FIArea4

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The coefficient of a pair for the array restricted to the multiples of `w` is the
`w`-divisibility restriction of `S15coef β`. -/
lemma S15coef_restrArray (β : GaussianInt → ℂ) (w : GaussianInt) (i : S15Id) :
    S15coef (Work.S15alt.restrArray β w) i
      = (if w ∣ i.1.1 ∧ w ∣ i.1.2 then S15coef β i else 0) := by
  unfold S15coef Work.S15alt.restrArray
  by_cases h1 : w ∣ i.1.1 <;> by_cases h2 : w ∣ i.1.2 <;> simp [h1, h2]

/-- **The `w`-restricted per-modulus Möbius sum is the unfiltered per-modulus sum of the
restricted array**: the per-element conditions `w ∣ z₁`, `w ∣ z₂` of
`Work.S15alt.moebiusRestricted` are exactly the support of `restrArray β w` in the two
coefficient factors. -/
lemma moebiusRestricted_eq_pDng_restrArray (Pa : Work.FITop.Params) (X j d : ℕ)
    (β : GaussianInt → ℂ) (ℓ : ℤ) (u t : ℝ) (w : GaussianInt) :
    Work.S15alt.moebiusRestricted Pa X j d β ℓ u t w
      = S15pDng Pa X j d (Work.S15alt.restrArray β w) ℓ u t := by
  unfold Work.S15alt.moebiusRestricted S15pDng
  refine Finset.sum_congr rfl (fun z1 _ => Finset.sum_congr rfl (fun z2 _ => ?_))
  have hcoef := S15coef_restrArray β w ((z1, z2), d)
  simp only [hcoef]
  by_cases h1 : w ∣ z1 <;> by_cases h2 : w ∣ z2 <;>
    by_cases hX : X < d <;>
    by_cases hD : 4 * d ∣ Work.FIPlan.absDelta z1 z2 <;>
    by_cases hd0 : 0 < Work.FIPlan.absDelta z1 z2 <;>
    simp [h1, h2, hX, hD, hd0]

/-- `S15expSumng` is the sum of its per-modulus pieces `S15pDng` over the modulus window. -/
lemma S15expSumng_eq_sum_pDng' (Pa : Work.FITop.Params) (X j : ℕ) (β : GaussianInt → ℂ)
    (ℓ : ℤ) (u t : ℝ) :
    S15expSumng Pa X j β ℓ u t = ∑ d ∈ Finset.Icc 1 (S15Y Pa X j), S15pDng Pa X j d β ℓ u t :=
  rfl

/-- The restriction `restrArray β w` is again an `IsPrimBoxCoeff` whenever `β` is (its support
only shrinks, so all three defining properties are inherited). -/
theorem isPrimBoxCoeff_restrArray (Pa : Work.FITop.Params) {φ : ℝ} {β : GaussianInt → ℂ}
    (hβ : IsPrimBoxCoeff Pa φ β) (w : GaussianInt) :
    IsPrimBoxCoeff Pa φ (Work.S15alt.restrArray β w) := by
  refine ⟨⟨fun z => ?_, fun z hz => ?_⟩, fun z hz => ?_⟩
  · unfold Work.S15alt.restrArray
    by_cases h : w ∣ z <;> simp [h, hβ.1.1 z]
  · unfold Work.S15alt.restrArray at hz
    by_cases h : w ∣ z
    · simp only [h, ↓reduceIte] at hz
      exact hβ.1.2 z hz
    · simp [h] at hz
  · unfold Work.S15alt.restrArray at hz
    by_cases h : w ∣ z
    · simp only [h, ↓reduceIte] at hz
      exact hβ.2 z hz
    · simp [h] at hz

end

end Work.FIArea4
