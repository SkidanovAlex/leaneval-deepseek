import Mathlib
import Submission.Work.MotC5N3.AK
import Submission.Work.MotAS.Prime_sdualAS2
import Submission.Work.Reflect.PolyId

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotC5N3.Prime_sdualAS2`

The target ruling quintic `sdualAS2 (aK K D) (bK K D) g` of the corrected AS chart is a prime
element of `K[x₀,x₁,x₂]`, for an arbitrary `𝕜`-algebra field `K` of characteristic `5` and an
arbitrary Artin–Schreier class `g : K` with `g ∉ ℘(K)`.

This is the `RatFunc 𝕜 ↦ K` fork of `Work.MotAS.Prime_sdualAS2`.  Its proof is the *generic*
assembly `Work.MotAS.prime_sdualAS2_of` (already stated over any field `K`), whose inputs are

* irreducibility of the chart quintic `C g * X ^ 5 - X ^ 4 + 1`, which is
  `Work.MotAS.irreducible_quintic K g` as soon as `g` is not of the form `u ^ 5 - u`;
* the degree/leading-coefficient computation `Work.MotAS.sdualAS2_finSuccEquiv_deg_lc`;
* the substitution computation `Work.MotAS.sdualAS2_finSuccEquiv_map`.

Nothing about `RatFunc 𝕜` or `fAS 𝕜` is used: only `g ≠ 0` (from `hg`) and the Frobenius
identity `a ^ 10 - a ^ 5 b ^ 5 - b ^ 10 = (a ^ 2 - a b - b ^ 2) ^ 5`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 100000

namespace Work.MotC5N3

/-- **The target ruling quintic of the AS chart is a prime element.** -/
theorem Prime_sdualAS2 (K : Type) [Field K] [CharP K 5] {𝕜 : Type} [Field 𝕜] [Algebra 𝕜 K]
    (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D) (g : K)
    (hg : ¬ ∃ u : K, u ^ 5 - u = g) :
    Prime (Work.MotAS.sdualAS2 (aK K D) (bK K D) g) := by
  have hd : (aK K D) ^ 2 - (aK K D) * (bK K D) - (bK K D) ^ 2 ≠ 0 := aK_sq_sub_ne D hD
  have hg0 : g ≠ 0 := by
    intro h
    exact hg ⟨0, by rw [h]; ring⟩
  have hfrob : (aK K D) ^ 10 - (aK K D) ^ 5 * (bK K D) ^ 5 - (bK K D) ^ 10
      = ((aK K D) ^ 2 - (aK K D) * (bK K D) - (bK K D) ^ 2) ^ 5 := by
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have hA := sub_pow_char_pow ((aK K D) ^ 2 - (aK K D) * (bK K D)) ((bK K D) ^ 2) 1
    have hB := sub_pow_char_pow ((aK K D) ^ 2) ((aK K D) * (bK K D)) 1
    simp only [pow_one] at hA hB
    rw [hA, hB]
    first | refl_ring1 | ring
  have hcc : (aK K D) ^ 10 - (aK K D) ^ 5 * (bK K D) ^ 5 - (bK K D) ^ 10 ≠ 0 := by
    rw [hfrob]
    exact pow_ne_zero 5 hd
  have h : g * ((aK K D) ^ 10 - (aK K D) ^ 5 * (bK K D) ^ 5 - (bK K D) ^ 10) ≠ 0 :=
    mul_ne_zero hg0 hcc
  have hdl := Work.MotAS.sdualAS2_finSuccEquiv_deg_lc (aK K D) (bK K D) g h
  have hirr : Irreducible ((Polynomial.C g : Polynomial K) * Polynomial.X ^ 5
      - Polynomial.X ^ 4 + 1) := by
    refine Work.MotAS.irreducible_quintic K g ?_
    intro b hb
    refine hg ⟨-b, ?_⟩
    calc (-b) ^ 5 - (-b) = -(b ^ 5 - b) := by ring
      _ = -(-g) := by rw [hb]
      _ = g := neg_neg g
  exact Work.MotAS.prime_sdualAS2_of (aK K D) (bK K D) g h hirr hdl.1 hdl.2
    (Work.MotAS.sdualAS2_finSuccEquiv_map (aK K D) (bK K D) g)

end Work.MotC5N3
