import Mathlib
import Submission.Work.MotC2.NeTwoRatFuncSqMul
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotC2

/-- In `L(X)` the class of `2` is nonzero as soon as `2 ≠ 0` in `L`. -/
private lemma two_ne_zero_ratFunc (L : Type*) [Field L] (h2 : (2 : L) ≠ 0) :
    (2 : RatFunc L) ≠ 0 := by
  rw [show (2 : RatFunc L) = algebraMap (Polynomial L) (RatFunc L) (Polynomial.C (2 : L)) by
    rw [RatFunc.algebraMap_C]
    exact (map_ofNat (algebraMap L (RatFunc L)) 2).symm]
  intro hh
  have hC : Polynomial.C (2 : L) = 0 := by
    apply (IsFractionRing.injective (Polynomial L) (RatFunc L))
    rw [hh, map_zero]
  have h3 : (2 : L) = 0 := by simpa using congrArg (fun p : Polynomial L => p.coeff 0) hC
  exact h2 h3

/-- The image of the constant polynomial `2⁻¹` in `L(X)` is the inverse of `2`. -/
private lemma algebraMap_C_inv_two (L : Type*) [Field L] (_h2 : (2 : L) ≠ 0) :
    algebraMap (Polynomial L) (RatFunc L) (Polynomial.C (2 : L)⁻¹) = (2 : RatFunc L)⁻¹ := by
  change (algebraMap L (RatFunc L)) (2 : L)⁻¹ = (2 : RatFunc L)⁻¹
  rw [map_inv₀, show (algebraMap L (RatFunc L)) (2 : L) = 2 from map_ofNat _ 2]

/-- **Crux (characteristic ≠ 2), form over `L(X)`.**  Let `e c ∈ L[X]` with `e ^ 2 + 4 * c`
squarefree.  If `p q ∈ RatFunc L = L(X)` satisfy `2 * p - q * ē ∈ range (algebraMap L[X] L(X))`
and `p ^ 2 - p * (q * ē) - q ^ 2 * c̄ ∈ range (algebraMap L[X] L(X))` (with `ē`, `c̄` the images of
`e`, `c`), then `p` and `q` are polynomials.  Proof route: with `T := 2 * p - q * ē` and
`N := p ^ 2 - p * (q * ē) - q ^ 2 * c̄` one has `T ^ 2 - 4 * N = q ^ 2 * algebraMap (e ^ 2 + 4 * c)`
by `ring`; so `q ^ 2 * algebraMap (e ^ 2 + 4 * c) ∈ range` and `Work.MotC2.NeTwoRatFuncSqMul`
(module `Submission.Work.MotC2.NeTwoRatFuncSqMul`) gives `q ∈ range`.  Then `2 * p = T + q * ē ∈
range`, and `algebraMap (Polynomial.C (2⁻¹)) = (2 : RatFunc L)⁻¹` (using `h2`) gives `p ∈ range`. -/
theorem NeTwoRatFuncCrux (L : Type*) [Field L] (h2 : (2 : L) ≠ 0)
    (e c : Polynomial L) (hd : Squarefree (e ^ 2 + 4 * c))
    (p q : RatFunc L)
    (hT : 2 * p - q * algebraMap (Polynomial L) (RatFunc L) e ∈
      Set.range (algebraMap (Polynomial L) (RatFunc L)))
    (hN : p ^ 2 - p * (q * algebraMap (Polynomial L) (RatFunc L) e) -
      q ^ 2 * algebraMap (Polynomial L) (RatFunc L) c ∈
      Set.range (algebraMap (Polynomial L) (RatFunc L))) :
    p ∈ Set.range (algebraMap (Polynomial L) (RatFunc L)) ∧
      q ∈ Set.range (algebraMap (Polynomial L) (RatFunc L)) := by
  obtain ⟨t, ht⟩ := hT
  obtain ⟨n, hn⟩ := hN
  -- `T ^ 2 - 4 * N = q ^ 2 * algebraMap (e ^ 2 + 4 * c)` is a polynomial.
  have hqmem : q ^ 2 * algebraMap (Polynomial L) (RatFunc L) (e ^ 2 + 4 * c) ∈
      Set.range (algebraMap (Polynomial L) (RatFunc L)) := by
    refine ⟨t ^ 2 - 4 * n, ?_⟩
    rw [map_sub, map_mul, map_pow, map_add, map_pow, map_mul, ht, hn, map_ofNat]
    first | refl_ring1 | ring
  obtain ⟨q', hq'⟩ := NeTwoRatFuncSqMul L (e ^ 2 + 4 * c) hd q hqmem
  -- hence `2 * p = T + q * ē` is a polynomial.
  have h2p : 2 * p ∈ Set.range (algebraMap (Polynomial L) (RatFunc L)) := by
    refine ⟨t + q' * e, ?_⟩
    rw [map_add, map_mul, ht, hq']
    first | refl_ring1 | ring
  obtain ⟨u, hu⟩ := h2p
  refine ⟨⟨Polynomial.C (2 : L)⁻¹ * u, ?_⟩, ⟨q', hq'⟩⟩
  rw [map_mul, hu, algebraMap_C_inv_two L h2, ← mul_assoc,
    inv_mul_cancel₀ (two_ne_zero_ratFunc L h2), one_mul]

end Work.MotC2
