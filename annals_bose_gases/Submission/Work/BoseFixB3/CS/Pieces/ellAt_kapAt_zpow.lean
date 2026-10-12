import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseFixB3.CS.Arith
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The parameter arithmetic of `ellAt`/`kapAt` at FS's exponents

At FS's parameters `ℓ = K_ℓ(μa)^{-1/2}` with `K_ℓ = (μa³)^{-3/646}` and
`κ = (d²ℓ)^{-1}` with `d = (μa³)^{6/323}`, so

    ℓ = μ^{-163/323} a^{-166/323},
    κ = μ^{151/323} a^{130/323},
    ℓκ = μ^{-12/323} a^{-36/323},
    μ ℓ⁵ = μ^{-492/323} a^{-830/323}.

The two identities of `ellAt_kapAt_zpow` are the `zpow`-form bookkeeping used in
the `CS` step: `(ℓκ)^{-50} = (μa³)^{600/323}` and
`μ ℓ⁵ (ℓκ)^{-50} = (μa³)^{108/323} a²`, both exponents being computed in `323`ths
from `-12·(-50) = 600`, `-3/2·(-50) + 5·(-3/646) + 1 = 108/323` (via `a³`).

All the work is `Real.rpow` bookkeeping on the positive bases `μ` and `a`, for
which we record the canonical-form lemmas below: a product of `rpow`s of `μ` and
`a` is again of that form, with the exponents added, multiplied or negated.
-/

namespace Work.BoseFixB3.CS.Pieces

/-! ## 1. `Real.rpow` bookkeeping on a positive base -/

/-- `(x^y)^n = x^{yn}` for `x > 0`. -/
private lemma rpow_pow {x : ℝ} (hx : 0 < x) (y : ℝ) (n : ℕ) : (x ^ y) ^ n = x ^ (y * n) := by
  rw [← Real.rpow_natCast (x ^ y) n, ← Real.rpow_mul hx.le y (n : ℝ)]

/-- `x^p · x^q = x^{p+q}` for `x > 0`. -/
private lemma rpow_self_mul {x : ℝ} (hx : 0 < x) (p q : ℝ) : x ^ p * x ^ q = x ^ (p + q) :=
  (Real.rpow_add hx p q).symm

/-- The canonical product form of §2 is closed under multiplication. -/
private lemma rpow_mul_canon (μ a : ℝ) (hμ : 0 < μ) (ha : 0 < a) (p q r s : ℝ) :
    (μ ^ p * a ^ q) * (μ ^ r * a ^ s) = μ ^ (p + r) * a ^ (q + s) := by
  rw [mul_mul_mul_comm, rpow_self_mul hμ, rpow_self_mul ha]

/-- The canonical product form of §2 is closed under natural powers. -/
private lemma rpow_pow_canon (μ a : ℝ) (hμ : 0 < μ) (ha : 0 < a) (p q : ℝ) (n : ℕ) :
    (μ ^ p * a ^ q) ^ n = μ ^ (p * n) * a ^ (q * n) := by
  rw [mul_pow]
  congr 1
  · exact rpow_pow hμ p n
  · exact rpow_pow ha q n

/-- The canonical product form of §2 is closed under real powers. -/
private lemma rpow_rpow_canon (μ a : ℝ) (hμ : 0 < μ) (ha : 0 < a) (p q r : ℝ) :
    (μ ^ p * a ^ q) ^ r = μ ^ (p * r) * a ^ (q * r) := by
  rw [Real.mul_rpow (Real.rpow_nonneg hμ.le p) (Real.rpow_nonneg ha.le q),
      ← Real.rpow_mul hμ.le p r, ← Real.rpow_mul ha.le q r]

/-- `(μa³)^e = μ^e a^{3e}` for `μ, a > 0`. -/
private lemma rpow_mul_t (μ a : ℝ) (hμ : 0 < μ) (ha : 0 < a) (e : ℝ) :
    (μ * a ^ 3) ^ e = μ ^ e * a ^ (3 * e) := by
  rw [Real.mul_rpow hμ.le (by positivity : (0 : ℝ) ≤ a ^ 3), ← Real.rpow_natCast a 3,
      ← Real.rpow_mul ha.le ((3 : ℕ) : ℝ) e]
  norm_num

/-- `(μa)^e = μ^e a^e` for `μ, a > 0`. -/
private lemma rpow_mul_a (μ a : ℝ) (hμ : 0 < μ) (ha : 0 < a) (e : ℝ) :
    (μ * a) ^ e = μ ^ e * a ^ e := Real.mul_rpow hμ.le ha.le

/-- The canonical product form of §2 is closed under inversion. -/
private lemma rpow_inv_canon (μ a : ℝ) (hμ : 0 < μ) (ha : 0 < a) (p q : ℝ) :
    (μ ^ p * a ^ q)⁻¹ = μ ^ (-p) * a ^ (-q) := by
  rw [mul_inv_rev, ← Real.rpow_neg hμ.le p, ← Real.rpow_neg ha.le q, mul_comm]

/-- Multiplying a canonical product by `μ = μ^1`. -/
private lemma mu_mul_canon (μ a : ℝ) (hμ : 0 < μ) (p q : ℝ) :
    μ * (μ ^ p * a ^ q) = μ ^ (1 + p) * a ^ q := by
  rw [← rpow_self_mul hμ 1 p, Real.rpow_one]
  ring

/-! ## 2. The canonical forms of `ℓ`, `κ` and the two combinations used -/

/-- `ℓ = K_ℓ(μa)^{-1/2} = μ^{-163/323}a^{-166/323}`. -/
private lemma ellAt_canon (μ a : ℝ) (hμ : 0 < μ) (ha : 0 < a) :
    Work.BoseFixB3.ellAt μ a = μ ^ (-(163 / 323 : ℝ)) * a ^ (-(166 / 323 : ℝ)) := by
  rw [Work.BoseFixB3.ellAt, Work.BoseBox.sideAt, Work.BoseBox.boxSide, Work.BoseBox.paramsAt]
  simp only [Work.BoseBox.fsParams, Work.BoseBox.fsXp]
  rw [rpow_mul_t μ a hμ ha, rpow_mul_a μ a hμ ha]
  rw [rpow_mul_canon μ a hμ ha]
  norm_num

/-- `κ = (d²ℓ)^{-1} = μ^{151/323}a^{130/323}` (with `d = (μa³)^{6/323}`). -/
private lemma kapAt_canon (μ a : ℝ) (hμ : 0 < μ) (ha : 0 < a) :
    Work.BoseFixB3.kapAt μ a = μ ^ ((151 : ℝ) / 323) * a ^ ((130 : ℝ) / 323) := by
  have hℓ := ellAt_canon μ a hμ ha
  have ht : 0 < μ * a ^ 3 := by positivity
  have hd : Work.BoseFixB3.kapAt μ a
      = (((μ * a ^ 3) ^ (6 / 323 : ℝ)) ^ 2 * Work.BoseFixB3.ellAt μ a)⁻¹ := by
    simp only [Work.BoseFixB3.kapAt, Work.BoseBox.paramsAt,
               Work.BoseBox.fsParams, Work.BoseBox.fsXp, Work.BoseFixB3.ellAt,
               Work.BoseBox.sideAt, Work.BoseBox.boxSide]
  rw [hd]
  have hD : ((μ * a ^ 3) ^ (6 / 323 : ℝ)) ^ 2 * Work.BoseFixB3.ellAt μ a
      = μ ^ (-(151 / 323 : ℝ)) * a ^ (-(130 / 323 : ℝ)) := by
    calc ((μ * a ^ 3) ^ (6 / 323 : ℝ)) ^ 2 * Work.BoseFixB3.ellAt μ a
        = (μ * a ^ 3) ^ ((12 : ℝ) / 323) * Work.BoseFixB3.ellAt μ a := by
            rw [rpow_pow ht (6 / 323) 2]; norm_num
      _ = (μ ^ ((12 : ℝ) / 323) * a ^ ((36 : ℝ) / 323)) * Work.BoseFixB3.ellAt μ a := by
            rw [rpow_mul_t μ a hμ ha]; norm_num
      _ = (μ ^ ((12 : ℝ) / 323) * a ^ ((36 : ℝ) / 323))
            * (μ ^ (-(163 / 323 : ℝ)) * a ^ (-(166 / 323 : ℝ))) := by rw [hℓ]
      _ = μ ^ (-(151 / 323 : ℝ)) * a ^ (-(130 / 323 : ℝ)) := by
            rw [rpow_mul_canon μ a hμ ha]; norm_num
  rw [hD, rpow_inv_canon μ a hμ ha]
  norm_num

/-! ## 3. The target -/

theorem ellAt_kapAt_zpow (μ a : ℝ) (hμ : 0 < μ) (ha : 0 < a) :
    (Work.BoseFixB3.ellAt μ a * Work.BoseFixB3.kapAt μ a) ^ (-(50 : ℝ))
        = (μ * a ^ 3) ^ ((600 : ℝ) / 323)
      ∧ μ * (Work.BoseFixB3.ellAt μ a) ^ 5
          * (Work.BoseFixB3.ellAt μ a * Work.BoseFixB3.kapAt μ a) ^ (-(50 : ℝ))
        = (μ * a ^ 3) ^ ((108 : ℝ) / 323) * a ^ 2 := by
  have hℓ := ellAt_canon μ a hμ ha
  have hκ := kapAt_canon μ a hμ ha
  have hprod : Work.BoseFixB3.ellAt μ a * Work.BoseFixB3.kapAt μ a
      = μ ^ (-(12 / 323 : ℝ)) * a ^ (-(36 / 323 : ℝ)) := by
    rw [hℓ, hκ, rpow_mul_canon μ a hμ ha]
    norm_num
  have hpow : (Work.BoseFixB3.ellAt μ a * Work.BoseFixB3.kapAt μ a) ^ (-(50 : ℝ))
      = μ ^ ((600 : ℝ) / 323) * a ^ ((1800 : ℝ) / 323) := by
    rw [hprod, rpow_rpow_canon μ a hμ ha]
    norm_num
  have h5 : μ * (Work.BoseFixB3.ellAt μ a) ^ 5
      = μ ^ (-(492 / 323 : ℝ)) * a ^ (-(830 / 323 : ℝ)) := by
    calc μ * (Work.BoseFixB3.ellAt μ a) ^ 5
        = μ * (μ ^ (-(163 / 323 : ℝ)) * a ^ (-(166 / 323 : ℝ))) ^ 5 := by rw [hℓ]
      _ = μ ^ (-(492 / 323 : ℝ)) * a ^ (-(830 / 323 : ℝ)) := by
            rw [rpow_pow_canon μ a hμ ha, mu_mul_canon μ a hμ]
            norm_num
  constructor
  · rw [hpow, rpow_mul_t μ a hμ ha]
    norm_num
  · calc μ * (Work.BoseFixB3.ellAt μ a) ^ 5
          * (Work.BoseFixB3.ellAt μ a * Work.BoseFixB3.kapAt μ a) ^ (-(50 : ℝ))
        = (μ ^ (-(492 / 323 : ℝ)) * a ^ (-(830 / 323 : ℝ)))
            * (μ ^ ((600 : ℝ) / 323) * a ^ ((1800 : ℝ) / 323)) := by rw [h5, hpow]
      _ = μ ^ ((108 : ℝ) / 323) * a ^ ((970 : ℝ) / 323) := by
            rw [rpow_mul_canon μ a hμ ha]
            norm_num
      _ = (μ * a ^ 3) ^ ((108 : ℝ) / 323) * a ^ 2 := by
            rw [rpow_mul_t μ a hμ ha, ← Real.rpow_natCast a 2, mul_assoc, rpow_self_mul ha]
            norm_num

end Work.BoseFixB3.CS.Pieces
