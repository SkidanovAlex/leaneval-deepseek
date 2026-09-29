import Mathlib
import Submission.Work.Holonomy3.assembly_defs

namespace Work.Holonomy3

/-- Expansion of `sieveErr` with the common factor `2/(d·D)` distributed, valid for `d, D ≠ 0`. -/
lemma sieveErr_expand {m l d D : ℕ} {G₀ B C₀ M' U₀ ε η : ℝ}
    (hd : 0 < d) (hD : 0 < D) :
    sieveErr m l d D G₀ B C₀ M' U₀ ε η =
      2 * ε + 2 * Real.log ((D : ℝ) + 1) / (D : ℝ) + 2 * Real.log (m : ℝ) / (D : ℝ)
      + 2 * Real.log M' / (D : ℝ) + 2 * Real.log 2 / ((d : ℝ) * (D : ℝ))
      + (8 * ((l : ℝ) + 1) ^ 2 * ((d : ℝ) + 1) + (d : ℝ)) * G₀ / (d : ℝ) ^ 2
      + 2 * G₀ * (ε + 2 / (D : ℝ) + 1 / (d : ℝ))
      + 2 * ((m : ℝ) * B) * (3 * ε + 1 / (D : ℝ) + 16 * ((l : ℝ) + 1) / (d : ℝ))
      + 2 * (C₀ + U₀) / (D : ℝ) + (m : ℝ) * η := by
  unfold sieveErr
  have hd' : ((d : ℝ)) ≠ 0 := by
    have : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    exact ne_of_gt this
  have hD' : ((D : ℝ)) ≠ 0 := by
    have : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
    exact ne_of_gt this
  field_simp

/-- The `G₀`-quadratic term of the expansion is dominated by the hypothesis `h2`-style term. -/
lemma sieveErr_term6_le {l d : ℕ} {G₀ : ℝ} (hd : 0 < d) (hG₀ : 0 ≤ G₀) :
    (8 * ((l : ℝ) + 1) ^ 2 * ((d : ℝ) + 1) + (d : ℝ)) * G₀ / (d : ℝ) ^ 2
      ≤ G₀ * (16 * ((l : ℝ) + 1) ^ 2 + 1) / (d : ℝ) := by
  set x : ℝ := (l : ℝ) + 1 with hxdef
  set dd : ℝ := (d : ℝ) with hddef
  have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
  have hdd1 : 1 ≤ dd := by simp only [hddef]; exact_mod_cast hd
  have hbase : 8 * x ^ 2 * (dd + 1) + dd ≤ (16 * x ^ 2 + 1) * dd := by
    have hprod : 0 ≤ x ^ 2 * (dd - 1) := mul_nonneg hx2 (by linarith)
    nlinarith [hprod]
  have hkey : (8 * x ^ 2 * (dd + 1) + dd) * G₀ ≤ ((16 * x ^ 2 + 1) * dd) * G₀ := by
    have := mul_le_mul_of_nonneg_right hbase hG₀
    linarith [this]
  have hd2 : (0 : ℝ) < dd ^ 2 := by positivity
  calc (8 * ((l : ℝ) + 1) ^ 2 * ((d : ℝ) + 1) + (d : ℝ)) * G₀ / (d : ℝ) ^ 2
      = (8 * x ^ 2 * (dd + 1) + dd) * G₀ / dd ^ 2 := by simp only [hxdef, hddef]
    _ ≤ ((16 * x ^ 2 + 1) * dd) * G₀ / dd ^ 2 :=
        div_le_div_of_nonneg_right hkey (le_of_lt hd2)
    _ = G₀ * (16 * ((l : ℝ) + 1) ^ 2 + 1) / (d : ℝ) := by
        simp only [hxdef, hddef]; field_simp

/-- The numeric core of the sift of the fine holonomy bound (`Work.Holonomy3.sieveErr`).
`Work.Holonomy3.sieveErr m l d D G₀ B C₀ M' U₀ ε η` equals (for `d, D ≠ 0`)
`2ε + 2log(D+1)/D + 2log m/D + 2log M'/D + 2log2/(dD) + (8(l+1)²(d+1)+d)G₀/d²
+ 2G₀(ε+2/D+1/d) + 2mB(3ε+1/D+16(l+1)/d) + 2(C₀+U₀)/D + mη`,
so if the `ε`-group `ε·(2 + 2G₀ + 6mB)` is at most `η₁/4`, each of the ten remaining terms is at
most `η₁/32`, and `η = η₁/(16m)`, then `sieveErr ≤ η₁` (`1/4 + 10/32 + 1/16 = 20/32 < 1`). -/
lemma sieve_err_bound {m l d D : ℕ} {G₀ B C₀ M' U₀ ε η η₁ : ℝ}
    (hm : 0 < m) (hd : 0 < d) (hD : 1 ≤ D)
    (hG₀ : 0 ≤ G₀) (hB : 0 ≤ B) (hε0 : 0 ≤ ε) (hη₁ : 0 < η₁)
    (h1 : ε * (2 + 2 * G₀ + 6 * ((m : ℝ) * B)) ≤ η₁ / 4)
    (h2 : G₀ * (16 * ((l : ℝ) + 1) ^ 2 + 1) / (d : ℝ) ≤ η₁ / 32)
    (h3 : 2 * G₀ / (d : ℝ) ≤ η₁ / 32)
    (h4 : 32 * ((m : ℝ) * B) * ((l : ℝ) + 1) / (d : ℝ) ≤ η₁ / 32)
    (h5 : 2 * Real.log 2 / (d : ℝ) ≤ η₁ / 32)
    (h6 : 2 * Real.log ((D : ℝ) + 1) / (D : ℝ) ≤ η₁ / 32)
    (h7 : 2 * Real.log (m : ℝ) / (D : ℝ) ≤ η₁ / 32)
    (h8 : 2 * Real.log M' / (D : ℝ) ≤ η₁ / 32)
    (h9 : 4 * G₀ / (D : ℝ) ≤ η₁ / 32)
    (h10 : 2 * ((m : ℝ) * B) / (D : ℝ) ≤ η₁ / 32)
    (h11 : 2 * (C₀ + U₀) / (D : ℝ) ≤ η₁ / 32)
    (hη : η = η₁ / (16 * (m : ℝ))) :
    Work.Holonomy3.sieveErr m l d D G₀ B C₀ M' U₀ ε η ≤ η₁ := by
  have _unusedB := hB
  have _unusedε := hε0
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hD1 : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  have hDpos : (0 : ℝ) < (D : ℝ) := by linarith
  -- the `ε`-group
  have b1 : 2 * ε + 2 * G₀ * ε + 6 * ((m : ℝ) * B) * ε ≤ η₁ / 4 := by nlinarith [h1]
  -- the `2log 2/(dD)` term
  have b5 : 2 * Real.log 2 / ((d : ℝ) * (D : ℝ)) ≤ η₁ / 32 := by
    have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have he : 2 * Real.log 2 / ((d : ℝ) * (D : ℝ)) = (2 * Real.log 2 / (d : ℝ)) / (D : ℝ) := by
      ring
    rw [he]
    have h := div_le_self (a := 2 * Real.log 2 / (d : ℝ)) (b := (D : ℝ)) (by positivity) hD1
    linarith
  -- the `G₀`-quadratic term
  have b6 : (8 * ((l : ℝ) + 1) ^ 2 * ((d : ℝ) + 1) + (d : ℝ)) * G₀ / (d : ℝ) ^ 2 ≤ η₁ / 32 :=
    le_trans (sieveErr_term6_le hd hG₀) h2
  -- the `m·η` term
  have bη : (m : ℝ) * η = η₁ / 16 := by
    have hmne : ((m : ℝ)) ≠ 0 := by
      have : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
      exact ne_of_gt this
    rw [hη]; field_simp
  -- split the two mixed terms into their monomial parts
  have e7 : 2 * G₀ * (ε + 2 / (D : ℝ) + 1 / (d : ℝ))
      = 2 * G₀ * ε + 4 * G₀ / (D : ℝ) + 2 * G₀ / (d : ℝ) := by ring
  have e8 : 2 * ((m : ℝ) * B) * (3 * ε + 1 / (D : ℝ) + 16 * ((l : ℝ) + 1) / (d : ℝ))
      = 6 * ((m : ℝ) * B) * ε + 2 * ((m : ℝ) * B) / (D : ℝ)
        + 32 * ((m : ℝ) * B) * ((l : ℝ) + 1) / (d : ℝ) := by ring
  rw [sieveErr_expand hd (by omega : 0 < D), e7, e8]
  linarith [b1, b5, b6, bη, h3, h4, h6, h7, h8, h9, h10, h11]

end Work.Holonomy3
