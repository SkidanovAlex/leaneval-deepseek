import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseBox.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.chAimg_arith5` — the pure-real slot arithmetic at the `(A)`-images,
second shape

With `fsXp t c = t ^ (c / 323)` (FS's monomial `(μa³)^{c/323}`) and the box side / chemical
potential tied to the diluteness by

`ℓ = fsXp t (−3/2)·(t/a²)^{−1/2} = a·t^{−163/323}`,   `μ = t/a³`,

the slot budget `K0·a/(8μ(1+ℓ³))` is a reciprocal quantity; multiplying the slot expression

`C·(fsXp t 6)^{192}·(√(2ℓ/π) + √a)·(√a·μ·ℓ³ + √ℓ)`

by `8μ(1+ℓ³)/a` turns the comparison into a sum of monomials `a^j·t^{e}` whose `t`-exponents are
all non-negative.  Concretely, the kernel is `fsXp t (−3/2)·(t/a²)^{−1/2} = a·t^{−163/323}`, so

`√(2ℓ/π) = √(2a/π)·t^{−163/646}`,  `√ℓ = √a·t^{−163/646}`,  `ℓ³ = a³·t^{−489/323}`,
`μ·ℓ³ = t^{−166/323}`,  `(fsXp t 6)^{192} = t^{1152/323}`,

and

`C·(fsXp t 6)^{192}·(√(2ℓ/π)+√a)·(√a·μ·ℓ³+√ℓ)·(8μ(1+ℓ³)/a)`

` = 8C·a^{−4}·( √(2a/π)√a·(t^{2455/646}+t^{2624/646}) + √a√a·(t^{2618/646}+t^{2787/646})`

`      + a³·(√(2a/π)√a·(t^{1477/646}+t^{1646/646}) + √a√a·(t^{1640/646}+t^{1809/646})) )`.

All eight exponents lie in `[0, 2127/323]` (the largest is `2787/646 < 4254/646 = 2127/323`), so
`t ≤ ε₀ ≤ max 1 ε₀` and monotonicity of `x ↦ x^r` (`r ≥ 0`) on `[0,∞)` bound every monomial by
`(max 1 ε₀)^{2127/323}`, which produces the announced `K0`.

The proof is pure `Real.rpow` bookkeeping: the kernel identity `ℓ = a t^{−163/323}`, the exact
identity for the expanded slot, and the term-by-term comparison.
-/

namespace Work.BoseBoxFock.PCFU

set_option maxHeartbeats 1600000

theorem chAimg_arith5 {a ε₀ C : ℝ} (ha : 0 < a) (hC : 0 ≤ C) :
    ∃ K0 : ℝ, 0 < K0 ∧ ∀ t ℓ μ : ℝ, 0 < t → t ≤ ε₀ →
      ℓ = Work.BoseBox.fsXp t (-(3 / 2 : ℝ)) * (t / a ^ 2) ^ (-(1 / 2 : ℝ)) →
      μ = t / a ^ 3 →
      C * (Work.BoseBox.fsXp t 6) ^ (192 : ℕ)
          * (Real.sqrt (2 * ℓ / Real.pi) + Real.sqrt a)
          * (Real.sqrt a * μ * ℓ ^ 3 + Real.sqrt ℓ)
        ≤ K0 * a / (8 * μ * (1 + ℓ ^ 3)) := by
  refine ⟨max 1 (8 * C * (a ^ 4)⁻¹ *
      ((Real.sqrt (2 * a / Real.pi) * Real.sqrt a) * (2 * (max 1 ε₀) ^ ((2127 : ℝ) / 323))
       + (Real.sqrt a * Real.sqrt a) * (2 * (max 1 ε₀) ^ ((2127 : ℝ) / 323))
       + a ^ 3 * ((Real.sqrt (2 * a / Real.pi) * Real.sqrt a) * (2 * (max 1 ε₀) ^ ((2127 : ℝ) / 323))
          + (Real.sqrt a * Real.sqrt a) * (2 * (max 1 ε₀) ^ ((2127 : ℝ) / 323))))), ?_, ?_⟩
  · exact lt_of_lt_of_le one_pos (le_max_left 1 _)
  · intro t ℓ μ ht htε hℓ hμ
    have ht0 : (0 : ℝ) ≤ t := ht.le
    have hE1 : (1 : ℝ) ≤ max 1 ε₀ := le_max_left 1 ε₀
    have hEt : t ≤ max 1 ε₀ := le_trans htε (le_max_right 1 ε₀)
    -- ## the kernel `ℓ = a·t^{−163/323}`
    have hℓk : ℓ = a * t ^ (-(163 / 323 : ℝ)) := by
      rw [hℓ, Work.BoseBox.fsXp]
      have ha2 : ((a ^ 2 : ℝ)) ^ (-(1 / 2 : ℝ)) = a⁻¹ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul ha.le,
          show ((2 : ℕ) : ℝ) * (-(1 / 2 : ℝ)) = -1 by norm_num, Real.rpow_neg_one]
      have hdiv : (t / a ^ 2) ^ (-(1 / 2 : ℝ)) = a * t ^ (-(1 / 2 : ℝ)) := by
        rw [Real.div_rpow ht0 (by positivity : (0 : ℝ) ≤ a ^ 2), ha2, div_eq_mul_inv, inv_inv]
        ring
      rw [hdiv,
        show t ^ ((-(3 / 2 : ℝ)) / 323) * (a * t ^ (-(1 / 2 : ℝ)))
            = a * (t ^ ((-(3 / 2 : ℝ)) / 323) * t ^ (-(1 / 2 : ℝ))) from by ring,
        ← Real.rpow_add ht,
        show (-(3 / 2 : ℝ)) / 323 + (-(1 / 2 : ℝ)) = -(163 / 323 : ℝ) by norm_num]
    have hℓpos : 0 < ℓ := by rw [hℓk]; exact mul_pos ha (Real.rpow_pos_of_pos ht _)
    have hμ1 : μ = t ^ (1 : ℝ) / a ^ 3 := by rw [hμ, Real.rpow_one]
    -- ## the elementary pieces of `ℓ` and `μ`
    have hT6 : (Work.BoseBox.fsXp t 6) ^ (192 : ℕ) = t ^ ((1152 : ℝ) / 323) := by
      rw [Work.BoseBox.fsXp, ← Real.rpow_natCast (t ^ ((6 : ℝ) / 323)) 192, ← Real.rpow_mul ht0]
      congr 1
      push_cast
      ring
    have hℓ3 : ℓ ^ 3 = a ^ 3 * t ^ (-(489 / 323 : ℝ)) := by
      rw [hℓk, mul_pow]
      rw [show (t ^ (-(163 / 323 : ℝ))) ^ 3 = t ^ (-(489 / 323 : ℝ)) from by
        rw [← Real.rpow_natCast, ← Real.rpow_mul ht0]; congr 1; norm_num]
    have hsq : Real.sqrt (2 * ℓ / Real.pi)
        = Real.sqrt (2 * a / Real.pi) * t ^ (-(163 / 646 : ℝ)) := by
      have h2 : Real.sqrt (t ^ (-(163 / 323 : ℝ))) = t ^ (-(163 / 646 : ℝ)) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul ht0]; congr 1; norm_num
      have harg : 2 * ℓ / Real.pi = (2 * a / Real.pi) * t ^ (-(163 / 323 : ℝ)) := by
        rw [hℓk]; field_simp
      rw [harg, Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * a / Real.pi), h2]
    have hsqr : Real.sqrt ℓ = Real.sqrt a * t ^ (-(163 / 646 : ℝ)) := by
      have h2 : Real.sqrt (t ^ (-(163 / 323 : ℝ))) = t ^ (-(163 / 646 : ℝ)) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul ht0]; congr 1; norm_num
      rw [hℓk, Real.sqrt_mul ha.le, h2]
    have hμl3 : μ * ℓ ^ 3 = t ^ (-(166 / 323 : ℝ)) := by
      rw [hμ1, hℓ3]
      rw [show t ^ (1 : ℝ) / a ^ 3 * (a ^ 3 * t ^ (-(489 / 323 : ℝ)))
            = t ^ (1 : ℝ) * t ^ (-(489 / 323 : ℝ)) from by field_simp]
      rw [show t ^ (1 : ℝ) * t ^ (-(489 / 323 : ℝ)) = t ^ (-(166 / 323 : ℝ)) from by
        rw [← Real.rpow_add ht]; congr 1; norm_num]
    have hB2 : Real.sqrt a * μ * ℓ ^ 3 + Real.sqrt ℓ
        = Real.sqrt a * t ^ (-(166 / 323 : ℝ)) + Real.sqrt a * t ^ (-(163 / 646 : ℝ)) := by
      rw [show Real.sqrt a * μ * ℓ ^ 3 = Real.sqrt a * t ^ (-(166 / 323 : ℝ)) from by
        rw [← hμl3]; ring, hsqr]
    have hFacC : 8 * (t ^ (1 : ℝ) / a ^ 3) * (1 + a ^ 3 * t ^ (-(489 / 323 : ℝ))) / a
        = 8 * (a ^ 4)⁻¹ * (t ^ (1 : ℝ) + a ^ 3 * t ^ (-(166 / 323 : ℝ))) := by
      rw [show 8 * (t ^ (1 : ℝ) / a ^ 3) * (1 + a ^ 3 * t ^ (-(489 / 323 : ℝ))) / a
            = 8 * ((t ^ (1 : ℝ) / a ^ 3) + ((t ^ (1 : ℝ) / a ^ 3) * a ^ 3)
                * t ^ (-(489 / 323 : ℝ))) / a from by ring]
      rw [show (t ^ (1 : ℝ) / a ^ 3) * a ^ 3 = t ^ (1 : ℝ) from by field_simp]
      rw [show t ^ (1 : ℝ) * t ^ (-(489 / 323 : ℝ)) = t ^ (-(166 / 323 : ℝ)) from by
        rw [← Real.rpow_add ht]; congr 1; norm_num]
      rw [show 8 * ((t ^ (1 : ℝ) / a ^ 3) + t ^ (-(166 / 323 : ℝ))) / a
            = 8 * (a ^ 4)⁻¹ * (t ^ (1 : ℝ) + a ^ 3 * t ^ (-(166 / 323 : ℝ))) from by
        field_simp]
    -- ## step 1: the exact value of `LHS · (8μ(1+ℓ³)/a)`
    have hR : C * (Work.BoseBox.fsXp t 6) ^ (192 : ℕ)
          * (Real.sqrt (2 * ℓ / Real.pi) + Real.sqrt a)
          * (Real.sqrt a * μ * ℓ ^ 3 + Real.sqrt ℓ) * (8 * μ * (1 + ℓ ^ 3) / a)
        = 8 * C * (a ^ 4)⁻¹ * t ^ ((1152 : ℝ) / 323)
          * (t ^ (1 : ℝ) + a ^ 3 * t ^ (-(166 / 323 : ℝ)))
          * (Real.sqrt (2 * a / Real.pi) * t ^ (-(163 / 646 : ℝ)) + Real.sqrt a)
          * (Real.sqrt a * t ^ (-(166 / 323 : ℝ)) + Real.sqrt a * t ^ (-(163 / 646 : ℝ))) := by
      rw [hT6, hsq, hB2,
        show 8 * μ * (1 + ℓ ^ 3) / a
            = 8 * (t ^ (1 : ℝ) / a ^ 3) * (1 + a ^ 3 * t ^ (-(489 / 323 : ℝ))) / a from by
          rw [hμ1, hℓ3], hFacC]
      ring
    -- ## step 2: expanding into the eight monomials `a^j t^{e}`
    have c1 : t ^ ((1152 : ℝ) / 323) * t ^ (1 : ℝ) * t ^ (-(163 / 646 : ℝ))
        * t ^ (-(166 / 323 : ℝ)) = t ^ ((2455 : ℝ) / 646) := by
      simp only [← Real.rpow_add ht]; congr 1; norm_num
    have c2 : t ^ ((1152 : ℝ) / 323) * t ^ (1 : ℝ) * t ^ (-(163 / 646 : ℝ))
        * t ^ (-(163 / 646 : ℝ)) = t ^ ((2624 : ℝ) / 646) := by
      simp only [← Real.rpow_add ht]; congr 1; norm_num
    have c3 : t ^ ((1152 : ℝ) / 323) * t ^ (1 : ℝ) * t ^ (-(166 / 323 : ℝ))
        = t ^ ((2618 : ℝ) / 646) := by
      simp only [← Real.rpow_add ht]; congr 1; norm_num
    have c4 : t ^ ((1152 : ℝ) / 323) * t ^ (1 : ℝ) * t ^ (-(163 / 646 : ℝ))
        = t ^ ((2787 : ℝ) / 646) := by
      simp only [← Real.rpow_add ht]; congr 1; norm_num
    have c5 : t ^ ((1152 : ℝ) / 323) * t ^ (-(166 / 323 : ℝ)) * t ^ (-(163 / 646 : ℝ))
        * t ^ (-(166 / 323 : ℝ)) = t ^ ((1477 : ℝ) / 646) := by
      simp only [← Real.rpow_add ht]; congr 1; norm_num
    have c6 : t ^ ((1152 : ℝ) / 323) * t ^ (-(166 / 323 : ℝ)) * t ^ (-(163 / 646 : ℝ))
        * t ^ (-(163 / 646 : ℝ)) = t ^ ((1646 : ℝ) / 646) := by
      simp only [← Real.rpow_add ht]; congr 1; norm_num
    have c7 : t ^ ((1152 : ℝ) / 323) * t ^ (-(166 / 323 : ℝ)) * t ^ (-(166 / 323 : ℝ))
        = t ^ ((1640 : ℝ) / 646) := by
      simp only [← Real.rpow_add ht]; congr 1; norm_num
    have c8 : t ^ ((1152 : ℝ) / 323) * t ^ (-(166 / 323 : ℝ)) * t ^ (-(163 / 646 : ℝ))
        = t ^ ((1809 : ℝ) / 646) := by
      simp only [← Real.rpow_add ht]; congr 1; norm_num
    have hExp : 8 * C * (a ^ 4)⁻¹ * t ^ ((1152 : ℝ) / 323)
          * (t ^ (1 : ℝ) + a ^ 3 * t ^ (-(166 / 323 : ℝ)))
          * (Real.sqrt (2 * a / Real.pi) * t ^ (-(163 / 646 : ℝ)) + Real.sqrt a)
          * (Real.sqrt a * t ^ (-(166 / 323 : ℝ)) + Real.sqrt a * t ^ (-(163 / 646 : ℝ)))
        = 8 * C * (a ^ 4)⁻¹ *
            ((Real.sqrt (2 * a / Real.pi) * Real.sqrt a)
                * (t ^ ((2455 : ℝ) / 646) + t ^ ((2624 : ℝ) / 646))
              + (Real.sqrt a * Real.sqrt a) * (t ^ ((2618 : ℝ) / 646) + t ^ ((2787 : ℝ) / 646))
              + a ^ 3 * ((Real.sqrt (2 * a / Real.pi) * Real.sqrt a)
                    * (t ^ ((1477 : ℝ) / 646) + t ^ ((1646 : ℝ) / 646))
                  + (Real.sqrt a * Real.sqrt a)
                    * (t ^ ((1640 : ℝ) / 646) + t ^ ((1809 : ℝ) / 646)))) := by
      rw [← c1, ← c2, ← c3, ← c4, ← c5, ← c6, ← c7, ← c8]
      ring
    -- ## step 3: the term-by-term bound against `(max 1 ε₀)^{2127/323}`
    have hb : ∀ e : ℝ, 0 ≤ e → e ≤ (2127 : ℝ) / 323 →
        t ^ e ≤ (max 1 ε₀) ^ ((2127 : ℝ) / 323) := by
      intro e he0 he1
      exact le_trans (Real.rpow_le_rpow ht0 hEt he0) (Real.rpow_le_rpow_of_exponent_le hE1 he1)
    have ht1 := hb ((2455 : ℝ) / 646) (by norm_num) (by norm_num)
    have ht2 := hb ((2624 : ℝ) / 646) (by norm_num) (by norm_num)
    have ht3 := hb ((2618 : ℝ) / 646) (by norm_num) (by norm_num)
    have ht4 := hb ((2787 : ℝ) / 646) (by norm_num) (by norm_num)
    have ht5 := hb ((1477 : ℝ) / 646) (by norm_num) (by norm_num)
    have ht6 := hb ((1646 : ℝ) / 646) (by norm_num) (by norm_num)
    have ht7 := hb ((1640 : ℝ) / 646) (by norm_num) (by norm_num)
    have ht8 := hb ((1809 : ℝ) / 646) (by norm_num) (by norm_num)
    have hS : (Real.sqrt (2 * a / Real.pi) * Real.sqrt a)
          * (t ^ ((2455 : ℝ) / 646) + t ^ ((2624 : ℝ) / 646))
        + (Real.sqrt a * Real.sqrt a) * (t ^ ((2618 : ℝ) / 646) + t ^ ((2787 : ℝ) / 646))
        + a ^ 3 * ((Real.sqrt (2 * a / Real.pi) * Real.sqrt a)
              * (t ^ ((1477 : ℝ) / 646) + t ^ ((1646 : ℝ) / 646))
            + (Real.sqrt a * Real.sqrt a)
              * (t ^ ((1640 : ℝ) / 646) + t ^ ((1809 : ℝ) / 646)))
        ≤ (Real.sqrt (2 * a / Real.pi) * Real.sqrt a) * (2 * (max 1 ε₀) ^ ((2127 : ℝ) / 323))
          + (Real.sqrt a * Real.sqrt a) * (2 * (max 1 ε₀) ^ ((2127 : ℝ) / 323))
          + a ^ 3 * ((Real.sqrt (2 * a / Real.pi) * Real.sqrt a)
                * (2 * (max 1 ε₀) ^ ((2127 : ℝ) / 323))
              + (Real.sqrt a * Real.sqrt a) * (2 * (max 1 ε₀) ^ ((2127 : ℝ) / 323))) := by
      have h1 : t ^ ((2455 : ℝ) / 646) + t ^ ((2624 : ℝ) / 646)
          ≤ 2 * (max 1 ε₀) ^ ((2127 : ℝ) / 323) := by linarith
      have h2 : t ^ ((2618 : ℝ) / 646) + t ^ ((2787 : ℝ) / 646)
          ≤ 2 * (max 1 ε₀) ^ ((2127 : ℝ) / 323) := by linarith
      have h3 : t ^ ((1477 : ℝ) / 646) + t ^ ((1646 : ℝ) / 646)
          ≤ 2 * (max 1 ε₀) ^ ((2127 : ℝ) / 323) := by linarith
      have h4 : t ^ ((1640 : ℝ) / 646) + t ^ ((1809 : ℝ) / 646)
          ≤ 2 * (max 1 ε₀) ^ ((2127 : ℝ) / 323) := by linarith
      have m1 := mul_le_mul_of_nonneg_left h1
        (by positivity : (0 : ℝ) ≤ Real.sqrt (2 * a / Real.pi) * Real.sqrt a)
      have m2 := mul_le_mul_of_nonneg_left h2
        (by positivity : (0 : ℝ) ≤ Real.sqrt a * Real.sqrt a)
      have m3 := mul_le_mul_of_nonneg_left h3
        (by positivity : (0 : ℝ) ≤ Real.sqrt (2 * a / Real.pi) * Real.sqrt a)
      have m4 := mul_le_mul_of_nonneg_left h4
        (by positivity : (0 : ℝ) ≤ Real.sqrt a * Real.sqrt a)
      have h34 : (Real.sqrt (2 * a / Real.pi) * Real.sqrt a)
              * (t ^ ((1477 : ℝ) / 646) + t ^ ((1646 : ℝ) / 646))
            + (Real.sqrt a * Real.sqrt a) * (t ^ ((1640 : ℝ) / 646) + t ^ ((1809 : ℝ) / 646))
          ≤ (Real.sqrt (2 * a / Real.pi) * Real.sqrt a)
              * (2 * (max 1 ε₀) ^ ((2127 : ℝ) / 323))
            + (Real.sqrt a * Real.sqrt a) * (2 * (max 1 ε₀) ^ ((2127 : ℝ) / 323)) :=
        add_le_add m3 m4
      have hsum := mul_le_mul_of_nonneg_left h34 (by positivity : (0 : ℝ) ≤ a ^ 3)
      linarith [m1, m2, hsum]
    -- ## step 4: assembly
    have hkey : C * (Work.BoseBox.fsXp t 6) ^ (192 : ℕ)
          * (Real.sqrt (2 * ℓ / Real.pi) + Real.sqrt a)
          * (Real.sqrt a * μ * ℓ ^ 3 + Real.sqrt ℓ) * (8 * μ * (1 + ℓ ^ 3) / a)
        ≤ max 1 (8 * C * (a ^ 4)⁻¹ *
            ((Real.sqrt (2 * a / Real.pi) * Real.sqrt a) * (2 * (max 1 ε₀) ^ ((2127 : ℝ) / 323))
             + (Real.sqrt a * Real.sqrt a) * (2 * (max 1 ε₀) ^ ((2127 : ℝ) / 323))
             + a ^ 3 * ((Real.sqrt (2 * a / Real.pi) * Real.sqrt a)
                  * (2 * (max 1 ε₀) ^ ((2127 : ℝ) / 323))
                + (Real.sqrt a * Real.sqrt a) * (2 * (max 1 ε₀) ^ ((2127 : ℝ) / 323))))) := by
      have h8C : (0 : ℝ) ≤ 8 * C * (a ^ 4)⁻¹ := by
        have ha4 : (0 : ℝ) < a ^ 4 := by positivity
        exact mul_nonneg (mul_nonneg (by norm_num) hC) (inv_nonneg.mpr ha4.le)
      rw [hR, hExp]
      refine le_trans (mul_le_mul_of_nonneg_left hS h8C) ?_
      exact le_max_right _ _
    have hμpos : 0 < μ := by rw [hμ]; positivity
    have hfac : 0 < 8 * μ * (1 + ℓ ^ 3) := by positivity
    rw [le_div_iff₀ hfac]
    rw [show ∀ x : ℝ, x * (8 * μ * (1 + ℓ ^ 3)) = x * (8 * μ * (1 + ℓ ^ 3) / a) * a from by
      intro x; field_simp]
    exact mul_le_mul_of_nonneg_right hkey ha.le

end Work.BoseBoxFock.PCFU
