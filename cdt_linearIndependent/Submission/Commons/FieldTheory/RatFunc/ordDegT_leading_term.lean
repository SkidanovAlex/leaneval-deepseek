import Mathlib
import Submission.Commons.FieldTheory.RatFunc.ordDegT_def
import Submission.Commons.FieldTheory.RatFunc.ordInfT_def
import Submission.Commons.FieldTheory.RatFunc.ordInfT_eq_top_iff
import Submission.Commons.FieldTheory.RatFunc.ordInfT_exists_leading_term_corrected

namespace Commons.FieldTheory.RatFunc

/-- `ordDegT = -ordInfT`: the `min`-valuation at `∞` is the negative of the `natDegree`-valuation
at `∞`.  (Private: the companion development `ordDegT_adjoint_eq_of_indicial` provides the same
identity publicly.) -/
private theorem ordDegT_eq_neg_ordInfT_aux {K : Type*} [Field K] (x : RatFunc K) :
    ordDegT x = -ordInfT x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [ordDegT, ordInfT]
  · rw [ordDegT_def hx, ordInfT_def hx, neg_sub]

/-- **Every nonzero rational function has a leading term at `∞`** — the `min`-valuation form.  For
`b ≠ 0` with `N = ordDegT b` (the `min`-valuation at infinity, `FieldTheory/RatFunc/ordDegT_def`),
there is `r ≠ 0` with `ordDegT (b - r·X^{-N}) ≥ N + 1`.  This is the counterpart of
`Commons.FieldTheory.RatFunc.exists_leading_term` at `α = ∞`, and it supplies the leading-coefficient
hypothesis of `Commons.FieldTheory.RatFunc.ordDegT_adjoint_eq_of_indicial`. -/
theorem ordDegT_leading_term {K : Type*} [Field K] {b : RatFunc K} (hb : b ≠ 0)
    (N : ℤ) (hN : ordDegT b = (N : WithTop ℤ)) :
    ∃ r : K, r ≠ 0 ∧ ((N + 1 : ℤ) : WithTop ℤ) ≤ ordDegT
      (b - algebraMap (Polynomial K) (RatFunc K) (Polynomial.C r)
        * (algebraMap (Polynomial K) (RatFunc K) Polynomial.X) ^ (-N)) := by
  -- `ordInfT b` is finite, say `m`; and `hN` forces `N = -m`.
  have hb_inf_ne : ordInfT b ≠ ⊤ := by
    simp [ordInfT_eq_top_iff, hb]
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hb_inf_ne
  have hN_eq : (N : WithTop ℤ) = ((-m : ℤ) : WithTop ℤ) := by
    rw [← hN, ordDegT_eq_neg_ordInfT_aux b, ← hm,
      ← WithTop.LinearOrderedAddCommGroup.coe_neg m]
  have hNm : N = -m := WithTop.coe_inj.mp hN_eq
  have hNinf : ordInfT b = ((-N : ℤ) : WithTop ℤ) := by
    rw [← hm, hNm]
    simp
  -- Apply the corrected leading-term statement at `∞` with `N` replaced by `-N`.
  obtain ⟨r, hr, hcase⟩ := ordInfT_exists_leading_term_corrected hb (-N) hNinf
  refine ⟨r, hr, ?_⟩
  rcases hcase with heq | hle
  · -- `b` is exactly the monomial `r·X^{-N}`, so the residual vanishes.
    rw [heq, sub_self]
    simp [ordDegT]
  · -- The residual is nonzero with `ordInfT` strictly below `-N`; negate the valuation.
    set res : RatFunc K := b - algebraMap (Polynomial K) (RatFunc K) (Polynomial.C r)
        * (algebraMap (Polynomial K) (RatFunc K) Polynomial.X) ^ (-N) with hresdef
    have hle' : ordInfT res ≤ (((-N - 1 : ℤ)) : WithTop ℤ) := by
      rw [hresdef]; exact hle
    have hres_ne : res ≠ 0 := by
      intro h0
      have htop : ordInfT res = ⊤ := by rw [h0]; simp [ordInfT]
      rw [htop] at hle'
      exact absurd hle' (not_le.mpr (WithTop.coe_lt_top (-N - 1)))
    obtain ⟨m', hm'⟩ : ∃ m' : ℤ, (m' : WithTop ℤ) = ordInfT res :=
      WithTop.ne_top_iff_exists.mp (by simp [ordInfT_eq_top_iff, hres_ne])
    have hm'_le : m' ≤ -N - 1 := by
      have h := hle'
      rw [← hm'] at h
      exact WithTop.coe_le_coe.mp h
    have hgoal : ordDegT res = ((-m' : ℤ) : WithTop ℤ) := by
      rw [ordDegT_eq_neg_ordInfT_aux res, ← hm',
        ← WithTop.LinearOrderedAddCommGroup.coe_neg m']
    rw [hgoal]
    exact WithTop.coe_le_coe.mpr (by linarith)

end Commons.FieldTheory.RatFunc
