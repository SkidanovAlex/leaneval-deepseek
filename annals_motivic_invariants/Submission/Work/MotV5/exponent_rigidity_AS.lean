import Mathlib
import Submission.Work.MotV5.Defs
import Submission.Work.MotV.Defs
import Submission.Work.MotV.not_fifth_pow_of_exp_value
import Submission.Work.MotV5.linear_of_algEquiv
import Submission.Work.MotV5.asG_natDegree

set_option linter.unusedVariables false -- v435-speed

set_option autoImplicit false

open scoped WithZero

namespace Work.MotV5
noncomputable section

/-- **The exponent count of the Artin–Schreier branch (paper node V4_AS).**

For a `𝕜`-algebra automorphism `α` of `𝕜(t)` in characteristic `5`, `f = t³ + t` and
`m ∈ {±2, ±3}`, the element `f - m·α(f)` of `𝕜(t)` is *not* fifth-power valued at every valuation
at which it has a pole.  Equivalently, there is a `ℤᵐ⁰`-valued valuation `v` of `𝕜(t)`, trivial on
`𝕜`, at which `f - m·α(f)` has a pole whose order is not divisible by `5`.

Witness: the valuation `v_∞` at `t = ∞` (`RatFunc.inftyValuation`).

* If `α(t)` is regular at `∞`, then `f` has a pole of order `3` at `∞` while
  `α(f) = α(t)³ + α(t)` is regular there, so `v_∞ (f - m·α f) = exp 3`.
* If `1 < v_∞ (α t)`, then `RatFunc.finrank_eq_max_natDegree` shows that `α` is affine,
  `α(t) = c t + d` (`c ≠ 0`), so `f - m α(f)` is the polynomial
  `G = (X³ + X) - m·((cX + d)³ + (cX + d))`; its degree is `1`, `2` or `3`.

In both cases `v_∞ (f - m·α f) = exp k` with `k ∈ {1,2,3}`, which is `> 1` and not divisible
by `5`, whence `v_∞ (f - m·α f)` is not a fifth power. -/
theorem exponent_rigidity_AS (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5]
    (α : RatFunc 𝕜 ≃ₐ[𝕜] RatFunc 𝕜) (m : 𝕜) (hm : m = 2 ∨ m = 3 ∨ m = -2 ∨ m = -3) :
    ¬ ∀ v : Valuation (RatFunc 𝕜) (WithZero (Multiplicative ℤ)), Work.MotV.TrivOn 𝕜 v →
      1 < v (Work.MotV.fAS 𝕜 - algebraMap 𝕜 (RatFunc 𝕜) m * α (Work.MotV.fAS 𝕜)) →
      ∃ u, v (Work.MotV.fAS 𝕜 - algebraMap 𝕜 (RatFunc 𝕜) m * α (Work.MotV.fAS 𝕜)) = v u ^ 5 := by
  classical
  intro hcon
  -- `m ≠ 0`
  have hm0 : m ≠ 0 := by
    rcases hm with h | h | h | h <;> rw [h]
    · intro hc; exact absurd ((CharP.cast_eq_zero_iff 𝕜 5 2).mp hc) (by norm_num)
    · intro hc; exact absurd ((CharP.cast_eq_zero_iff 𝕜 5 3).mp hc) (by norm_num)
    · intro hc
      exact absurd ((CharP.cast_eq_zero_iff 𝕜 5 2).mp (neg_eq_zero.mp hc)) (by norm_num)
    · intro hc
      exact absurd ((CharP.cast_eq_zero_iff 𝕜 5 3).mp (neg_eq_zero.mp hc)) (by norm_num)
  set a : RatFunc 𝕜 := α RatFunc.X with ha
  have ha0 : a ≠ 0 := by
    rw [ha]
    intro h0
    exact RatFunc.X_ne_zero (by simpa using congrArg α.symm h0)
  have haA : α RatFunc.X = a := ha.symm
  have hαfAS : α (Work.MotV.fAS 𝕜) = a ^ 3 + a := by
    simp only [Work.MotV.fAS, map_add, map_pow, haA]
  have hval_a : (RatFunc.inftyValuation 𝕜) a = WithZero.exp a.intDegree := by
    rw [RatFunc.inftyValuation_apply, RatFunc.inftyValuation_of_nonzero 𝕜 ha0]
  -- the exponent at the place `t = ∞`
  have key : ∃ k : ℤ, 1 < WithZero.exp k ∧ ¬ (5 : ℤ) ∣ k ∧
      (RatFunc.inftyValuation 𝕜)
        (Work.MotV.fAS 𝕜 - algebraMap 𝕜 (RatFunc 𝕜) m * α (Work.MotV.fAS 𝕜)) =
        WithZero.exp k := by
    rcases lt_or_ge (0 : ℤ) a.intDegree with hpos | hnonpos
    · -- Case II: `α(t)` has a pole at infinity; `α` is affine
      obtain ⟨c, d, hc, hlin⟩ := linear_of_algEquiv α (by rw [← ha]; omega)
      have ha_lin : a = RatFunc.C c * RatFunc.X + RatFunc.C d := ha.trans hlin
      set G : Polynomial 𝕜 := (Polynomial.X ^ 3 + Polynomial.X) -
        Polynomial.C m * ((Polynomial.C c * Polynomial.X + Polynomial.C d) ^ 3
          + (Polynomial.C c * Polynomial.X + Polynomial.C d)) with hGdef
      have hGdeg : G.natDegree = 1 ∨ G.natDegree = 2 ∨ G.natDegree = 3 := by
        simpa only [hGdef] using asG_natDegree m c d hc hm
      have hGne : G ≠ 0 := by
        intro h0
        rcases hGdeg with h1 | h1 | h1 <;>
          rw [h0, Polynomial.natDegree_zero] at h1 <;> norm_num at h1
      have hmap : (algebraMap (Polynomial 𝕜) (RatFunc 𝕜))
          (Polynomial.C c * Polynomial.X + Polynomial.C d) = a := by
        rw [ha_lin]
        simp only [map_add, map_mul, RatFunc.algebraMap_C, RatFunc.algebraMap_X]
      have hmC : algebraMap 𝕜 (RatFunc 𝕜) m =
          (algebraMap (Polynomial 𝕜) (RatFunc 𝕜)) (Polynomial.C m) := by
        rw [RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C]
      have hgG : Work.MotV.fAS 𝕜 - algebraMap 𝕜 (RatFunc 𝕜) m * α (Work.MotV.fAS 𝕜)
          = algebraMap (Polynomial 𝕜) (RatFunc 𝕜) G := by
        simp only [Work.MotV.fAS, hαfAS, hmC]
        rw [← hmap]
        simp only [← RatFunc.algebraMap_X, ← map_pow, ← map_add, ← map_mul, ← map_sub, hGdef]
      have hvalG : (RatFunc.inftyValuation 𝕜) (algebraMap (Polynomial 𝕜) (RatFunc 𝕜) G)
          = WithZero.exp (G.natDegree : ℤ) := by
        have hne : (algebraMap (Polynomial 𝕜) (RatFunc 𝕜)) G ≠ 0 :=
          fun h0 => hGne ((RatFunc.algebraMap_injective 𝕜) (by simpa using h0))
        rw [RatFunc.inftyValuation_apply, RatFunc.inftyValuation_of_nonzero 𝕜 hne,
          RatFunc.intDegree_polynomial]
      rcases hGdeg with h1 | h1 | h1
      · exact ⟨1, by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num,
          by norm_num, by rw [hgG, hvalG, h1]; norm_num⟩
      · exact ⟨2, by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num,
          by norm_num, by rw [hgG, hvalG, h1]; norm_num⟩
      · exact ⟨3, by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num,
          by norm_num, by rw [hgG, hvalG, h1]; norm_num⟩
    · -- Case I: `α(t)` is regular at infinity
      have hle : (RatFunc.inftyValuation 𝕜) a ≤ 1 := by
        rw [hval_a, ← WithZero.exp_zero, WithZero.exp_le_exp]
        exact hnonpos
      let v : Valuation (RatFunc 𝕜) (WithZero (Multiplicative ℤ)) := RatFunc.inftyValuation 𝕜
      have hX : v RatFunc.X = WithZero.exp 1 := RatFunc.inftyValuation.X 𝕜
      have hX3 : v (RatFunc.X ^ 3) = WithZero.exp 3 := by
        rw [map_pow, hX, ← WithZero.exp_nsmul]; norm_num
      have hFAS : v (Work.MotV.fAS 𝕜) = WithZero.exp 3 := by
        rw [show Work.MotV.fAS 𝕜 = RatFunc.X ^ 3 + RatFunc.X from rfl,
          Valuation.map_add_eq_of_lt_left v (by rw [hX, hX3, WithZero.exp_lt_exp]; norm_num)]
        exact hX3
      have hFASgt : 1 < v (Work.MotV.fAS 𝕜) := by
        rw [hFAS, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
      have hαle : v (algebraMap 𝕜 (RatFunc 𝕜) m * α (Work.MotV.fAS 𝕜)) ≤ 1 := by
        rw [map_mul, hαfAS]
        have hmv : v (algebraMap 𝕜 (RatFunc 𝕜) m) = 1 := Valuation.IsTrivialOn.eq_one m hm0
        rw [hmv, one_mul]
        have hsq : v (a ^ 2 + 1) ≤ 1 := by
          have h1 : v (a ^ 2 + 1) ≤ max (v (a ^ 2)) (v 1) := v.map_add_le_max' (a ^ 2) 1
          refine h1.trans ?_
          rw [Valuation.map_pow, map_one, max_le_iff]
          exact ⟨pow_le_one₀ zero_le hle, le_rfl⟩
        have hmul : v (a ^ 3 + a) = v a * v (a ^ 2 + 1) := by
          rw [← map_mul]; ring_nf
        rw [hmul]
        calc v a * v (a ^ 2 + 1) ≤ 1 * 1 := mul_le_mul hle hsq zero_le zero_le
          _ = 1 := one_mul 1
      have hlt : v (-(algebraMap 𝕜 (RatFunc 𝕜) m * α (Work.MotV.fAS 𝕜)))
          < v (Work.MotV.fAS 𝕜) := by
        rw [Valuation.map_neg]
        exact lt_of_le_of_lt hαle hFASgt
      have hgv : v (Work.MotV.fAS 𝕜 - algebraMap 𝕜 (RatFunc 𝕜) m * α (Work.MotV.fAS 𝕜))
          = WithZero.exp 3 := by
        rw [sub_eq_add_neg]
        exact (Valuation.map_add_eq_of_lt_left v hlt).trans hFAS
      exact ⟨3, by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num, by norm_num, hgv⟩
  obtain ⟨k, hk1, hk5, hkv⟩ := key
  exact Work.MotV.not_fifth_pow_of_exp_value (RatFunc.inftyValuation 𝕜) hkv hk5
    (hcon (RatFunc.inftyValuation 𝕜) (fun c hc => Valuation.IsTrivialOn.eq_one c hc)
      (by rw [hkv]; exact hk1))

end
end Work.MotV5
