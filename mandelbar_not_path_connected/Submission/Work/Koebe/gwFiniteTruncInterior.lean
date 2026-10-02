import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The finite truncated Grönwall (area-theorem) circle integral

For a finite coefficient sequence `c : ℕ → ℂ`, a radius `r > 0` and a truncation length `M`, the
circle integral

`∮_{|z| = r} conj (1/z + ∑_{n<M} c n · z^n) · (1/z + ∑_{n<M} c n · z^n)' dz`

equals `2 π i (∑_{n<M} n ‖c n‖² r^{2n} - r⁻²)`.

This is the finite version of the area-theorem identity `∮ conj F F' = 2πi (Ssum H r - r⁻²)`.

The proof rewrites, on the circle `|z| = r`, the conjugate `conj z` as `r²/z`, expands the product
into the four terms `A1·N`, `A1·D`, `S·N`, `S·D`, and evaluates each by the residue formula
`∮ z^k = 0` for `k ≠ -1` and `∮ z⁻¹ = 2πi`.
-/

namespace Work.Koebe

open Complex MeasureTheory Finset
open scoped Topology

noncomputable section

/-! ## Continuity of (integer) powers on a circle -/

private lemma sphere_ne_zero (r : ℝ) (hr : 0 < r) :
    ∀ z ∈ Metric.sphere (0 : ℂ) r, z ≠ 0 := by
  intro z hz h
  rw [Metric.mem_sphere, dist_zero_right] at hz
  rw [h, norm_zero] at hz
  linarith

private lemma continuousOn_zpow {s : Set ℂ} (hs : ∀ z ∈ s, z ≠ 0) (k : ℤ) :
    ContinuousOn (fun z : ℂ => z ^ k) s := by
  rcases k with n | n
  · convert (continuousOn_id.pow n : ContinuousOn (id ^ n : ℂ → ℂ) s) using 1
    ext z; simp
  · have h : ContinuousOn (fun z : ℂ => (z ^ (n + 1))⁻¹) s :=
      ((continuousOn_id.pow (n + 1) : ContinuousOn (id ^ (n + 1) : ℂ → ℂ) s)).inv₀
        (fun z hz => pow_ne_zero _ (hs z hz))
    simpa only [zpow_negSucc] using h

private lemma continuousOn_zpow_sphere (r : ℝ) (hr : 0 < r) (k : ℤ) :
    ContinuousOn (fun z : ℂ => z ^ k) (Metric.sphere (0 : ℂ) r) :=
  continuousOn_zpow (sphere_ne_zero r hr) k

private lemma continuousOn_const_zpow (r : ℝ) (hr : 0 < r) (a : ℂ) (k : ℤ) :
    ContinuousOn (fun z : ℂ => a * z ^ k) (Metric.sphere (0 : ℂ) r) :=
  (continuousOn_zpow_sphere r hr k).const_mul a

private lemma continuousOn_laurentSum (r : ℝ) (hr : 0 < r) (M : ℕ) (a : ℕ → ℂ) (j : ℕ → ℤ) :
    ContinuousOn (fun z : ℂ => ∑ n ∈ Finset.range M, a n * z ^ (j n))
      (Metric.sphere (0 : ℂ) r) :=
  continuousOn_finsetSum _ (fun n _ => continuousOn_const_zpow r hr (a n) (j n))

/-! ## The residue rules on a circle -/

private lemma circleIntegral_zpow_of_ne (r : ℝ) (k : ℤ) (hk : k ≠ -1) :
    (∮ z in C(0, r), z ^ k) = 0 := by
  simpa using circleIntegral.integral_sub_zpow_of_ne (n := k) hk (0 : ℂ) 0 r

private lemma circleIntegral_zpow_neg_one (r : ℝ) (hr : 0 < r) :
    (∮ z in C(0, r), (z : ℂ) ^ (-1 : ℤ)) = 2 * Real.pi * Complex.I := by
  simpa using circleIntegral.integral_sub_center_inv (0 : ℂ) (R := r) hr.ne'

/-! ## Circle integrals of products of Laurent monomials -/

private lemma circleIntegral_mono_times_zpow (r : ℝ) (hr : 0 < r) (a b : ℂ) (j k : ℤ) :
    (∮ z in C(0, r), (a * z ^ j) * (b * z ^ k)) = a * b * (∮ z in C(0, r), z ^ (j + k)) := by
  have hfun : (∮ z in C(0, r), (a * z ^ j) * (b * z ^ k))
      = ∮ z in C(0, r), (a * b) * z ^ (j + k) := by
    apply circleIntegral.integral_congr hr.le
    intro z hz
    show (a * z ^ j) * (b * z ^ k) = (a * b) * z ^ (j + k)
    rw [zpow_add₀ (sphere_ne_zero r hr z hz)]
    ring
  rw [hfun, circleIntegral.integral_const_mul]

private lemma circleIntegral_mono_times_sum (r : ℝ) (hr : 0 < r) (M : ℕ) (a : ℂ) (j : ℤ)
    (b : ℕ → ℂ) (k : ℕ → ℤ) :
    (∮ z in C(0, r), (a * z ^ j) * (∑ m ∈ Finset.range M, b m * z ^ (k m)))
      = ∑ m ∈ Finset.range M, a * b m * (∮ z in C(0, r), z ^ (j + k m)) := by
  have hsplit : (∮ z in C(0, r), (a * z ^ j) * (∑ m ∈ Finset.range M, b m * z ^ (k m)))
      = ∑ m ∈ Finset.range M, (∮ z in C(0, r), (a * z ^ j) * (b m * z ^ (k m))) := by
    have h1 : (fun z : ℂ => (a * z ^ j) * (∑ m ∈ Finset.range M, b m * z ^ (k m)))
        = fun z : ℂ => ∑ m ∈ Finset.range M, (a * z ^ j) * (b m * z ^ (k m)) := by
      funext z; rw [Finset.mul_sum]
    rw [h1]
    exact circleIntegral.integral_fun_sum (f := fun m z => (a * z ^ j) * (b m * z ^ (k m)))
      (fun m _ => ContinuousOn.circleIntegrable hr.le
        ((continuousOn_const_zpow r hr a j).mul (continuousOn_const_zpow r hr (b m) (k m))))
  rw [hsplit]
  exact Finset.sum_congr rfl (fun m _ => circleIntegral_mono_times_zpow r hr a (b m) j (k m))

private lemma circleIntegral_sum_times_mono (r : ℝ) (hr : 0 < r) (M : ℕ) (a : ℕ → ℂ)
    (j : ℕ → ℤ) (b : ℂ) (k : ℤ) :
    (∮ z in C(0, r), (∑ n ∈ Finset.range M, a n * z ^ (j n)) * (b * z ^ k))
      = ∑ n ∈ Finset.range M, a n * b * (∮ z in C(0, r), z ^ (j n + k)) := by
  have hsplit : (∮ z in C(0, r), (∑ n ∈ Finset.range M, a n * z ^ (j n)) * (b * z ^ k))
      = ∑ n ∈ Finset.range M, (∮ z in C(0, r), (a n * z ^ (j n)) * (b * z ^ k)) := by
    have h1 : (fun z : ℂ => (∑ n ∈ Finset.range M, a n * z ^ (j n)) * (b * z ^ k))
        = fun z : ℂ => ∑ n ∈ Finset.range M, (a n * z ^ (j n)) * (b * z ^ k) := by
      funext z; rw [Finset.sum_mul]
    rw [h1]
    exact circleIntegral.integral_fun_sum (f := fun n z => (a n * z ^ (j n)) * (b * z ^ k))
      (fun n _ => ContinuousOn.circleIntegrable hr.le
        ((continuousOn_const_zpow r hr (a n) (j n)).mul (continuousOn_const_zpow r hr b k)))
  rw [hsplit]
  exact Finset.sum_congr rfl (fun n _ => circleIntegral_mono_times_zpow r hr (a n) b (j n) k)

private lemma circleIntegral_doubleSum (r : ℝ) (hr : 0 < r) (M N : ℕ)
    (a : ℕ → ℂ) (j : ℕ → ℤ) (b : ℕ → ℂ) (k : ℕ → ℤ) :
    (∮ z in C(0, r),
        (∑ n ∈ Finset.range M, a n * z ^ (j n)) * (∑ m ∈ Finset.range N, b m * z ^ (k m)))
      = ∑ n ∈ Finset.range M, ∑ m ∈ Finset.range N,
          a n * b m * (∮ z in C(0, r), z ^ (j n + k m)) := by
  have hsplit : (∮ z in C(0, r),
        (∑ n ∈ Finset.range M, a n * z ^ (j n)) * (∑ m ∈ Finset.range N, b m * z ^ (k m)))
      = ∑ n ∈ Finset.range M,
          (∮ z in C(0, r), (a n * z ^ (j n)) * (∑ m ∈ Finset.range N, b m * z ^ (k m))) := by
    have h1 : (fun z : ℂ =>
          (∑ n ∈ Finset.range M, a n * z ^ (j n)) * (∑ m ∈ Finset.range N, b m * z ^ (k m)))
        = fun z : ℂ => ∑ n ∈ Finset.range M,
            (a n * z ^ (j n)) * (∑ m ∈ Finset.range N, b m * z ^ (k m)) := by
      funext z; rw [Finset.sum_mul]
    rw [h1]
    exact circleIntegral.integral_fun_sum
      (f := fun n z => (a n * z ^ (j n)) * (∑ m ∈ Finset.range N, b m * z ^ (k m)))
      (fun n _ => ContinuousOn.circleIntegrable hr.le
        ((continuousOn_const_zpow r hr (a n) (j n)).mul (continuousOn_laurentSum r hr N b k)))
  rw [hsplit]
  exact Finset.sum_congr rfl (fun n _ => circleIntegral_mono_times_sum r hr N (a n) (j n) b k)

/-! ## The derivative and the conjugate of `1/w + ∑ c n w^n` -/

private lemma deriv_gw (c : ℕ → ℂ) (M : ℕ) (z : ℂ) (hz : z ≠ 0) :
    deriv (fun w : ℂ => w⁻¹ + ∑ n ∈ Finset.range M, c n * w ^ n) z
      = -(z ^ 2)⁻¹ + ∑ n ∈ Finset.range M, c n * (n : ℂ) * z ^ ((n : ℤ) - 1) := by
  have hfun : (fun w : ℂ => w⁻¹ + ∑ n ∈ Finset.range M, c n * w ^ n)
      = (fun w : ℂ => w⁻¹) + (∑ n ∈ Finset.range M, fun w : ℂ => c n * w ^ n) := by
    funext w; simp [Finset.sum_apply]
  rw [hfun]
  have h1 : HasDerivAt (fun w : ℂ => w⁻¹) (-(z ^ 2)⁻¹) z := hasDerivAt_inv hz
  have h2 : HasDerivAt (∑ n ∈ Finset.range M, fun w : ℂ => c n * w ^ n)
      (∑ n ∈ Finset.range M, c n * (n : ℂ) * z ^ ((n : ℤ) - 1)) z := by
    refine HasDerivAt.sum (𝕜 := ℂ) (F := ℂ) (u := Finset.range M) (fun n _ => ?_)
    have h : HasDerivAt (fun w : ℂ => c n * w ^ ((n : ℤ)))
        (c n * ((n : ℂ) * z ^ ((n : ℤ) - 1))) z :=
      (hasDerivAt_zpow (n : ℤ) z (Or.inr (Int.natCast_nonneg n))).const_mul (c n)
    simpa [mul_assoc] using h
  exact (h1.add h2).deriv

private lemma star_gw (c : ℕ → ℂ) (M : ℕ) (r : ℝ) (hr : 0 < r) (z : ℂ)
    (hz : z ∈ Metric.sphere (0 : ℂ) r) :
    starRingEnd ℂ (z⁻¹ + ∑ n ∈ Finset.range M, c n * z ^ n)
      = z * ((r : ℂ) ^ 2)⁻¹
        + ∑ n ∈ Finset.range M, starRingEnd ℂ (c n) * (r : ℂ) ^ (2 * n) * (z ^ n)⁻¹ := by
  have hnorm : ‖z‖ = r := by
    rw [Metric.mem_sphere, dist_zero_right] at hz; exact hz
  have hz0 : z ≠ 0 := by intro h; rw [h, norm_zero] at hnorm; linarith
  have h1 : z * starRingEnd ℂ z = ((r : ℂ)) ^ 2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm, Complex.ofReal_pow]
  have hstar : starRingEnd ℂ z = (r : ℂ) ^ 2 * z⁻¹ := by
    have h2 : z⁻¹ * (z * starRingEnd ℂ z) = z⁻¹ * ((r : ℂ) ^ 2) :=
      congrArg (fun t => z⁻¹ * t) h1
    rw [← mul_assoc, inv_mul_cancel₀ hz0, one_mul] at h2
    rw [h2, mul_comm]
  rw [map_add, map_sum]
  congr 1
  · rw [map_inv₀, hstar, mul_inv_rev, inv_inv]
  · refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [map_mul, map_pow, hstar, mul_pow, inv_pow, ← pow_mul]
    ring

/-! ## The main theorem -/

private lemma continuousOn_inv_pow_sphere (r : ℝ) (hr : 0 < r) (n : ℕ) :
    ContinuousOn (fun z : ℂ => (z ^ n)⁻¹) (Metric.sphere (0 : ℂ) r) := by
  have h : ContinuousOn (fun z : ℂ => z ^ n) (Metric.sphere (0 : ℂ) r) := by
    convert (continuousOn_id.pow n : ContinuousOn (id ^ n : ℂ → ℂ) _) using 1
    ext z; simp
  exact h.inv₀ (fun z hz => pow_ne_zero n (sphere_ne_zero r hr z hz))

private lemma continuousOn_sum_inv_pow (r : ℝ) (hr : 0 < r) (M : ℕ) (a : ℕ → ℂ) :
    ContinuousOn (fun z : ℂ => ∑ n ∈ Finset.range M, a n * (z ^ n)⁻¹)
      (Metric.sphere (0 : ℂ) r) :=
  continuousOn_finsetSum _ (fun n _ => (continuousOn_inv_pow_sphere r hr n).const_mul (a n))

private lemma zpow_neg_two (z : ℂ) : z ^ (-2 : ℤ) = (z ^ 2)⁻¹ := by
  rw [zpow_neg]; rfl

theorem gwFiniteTruncInterior (c : ℕ → ℂ) (r : ℝ) (hr : 0 < r) (M : ℕ) :
    (∮ z in C(0, r), (starRingEnd ℂ (z⁻¹ + ∑ n ∈ Finset.range M, c n * z ^ n)) *
        deriv (fun w : ℂ => w⁻¹ + ∑ n ∈ Finset.range M, c n * w ^ n) z)
      = 2 * Real.pi * Complex.I *
        (((∑ n ∈ Finset.range M, (n : ℝ) * ‖c n‖ ^ 2 * r ^ (2 * n)) - r ^ (-2 : ℤ) : ℝ) : ℂ) := by
  set A : ℂ → ℂ := fun z => z * ((r : ℂ) ^ 2)⁻¹
      + ∑ n ∈ Finset.range M, starRingEnd ℂ (c n) * (r : ℂ) ^ (2 * n) * (z ^ n)⁻¹ with hA
  set B : ℂ → ℂ := fun z => -(z ^ 2)⁻¹
      + ∑ n ∈ Finset.range M, c n * (n : ℂ) * z ^ ((n : ℤ) - 1) with hB
  set A1 : ℂ → ℂ := fun z => z * ((r : ℂ) ^ 2)⁻¹ with hA1
  set S : ℂ → ℂ := fun z => ∑ n ∈ Finset.range M,
      starRingEnd ℂ (c n) * (r : ℂ) ^ (2 * n) * (z ^ n)⁻¹ with hS
  set N : ℂ → ℂ := fun z => -(z ^ 2)⁻¹ with hN
  set D : ℂ → ℂ := fun z => ∑ n ∈ Finset.range M, c n * (n : ℂ) * z ^ ((n : ℤ) - 1) with hD
  -- Step 1: the integrand on the circle.
  have hcongr : (∮ z in C(0, r), (starRingEnd ℂ (z⁻¹ + ∑ n ∈ Finset.range M, c n * z ^ n)) *
        deriv (fun w : ℂ => w⁻¹ + ∑ n ∈ Finset.range M, c n * w ^ n) z)
      = ∮ z in C(0, r), A z * B z := by
    apply circleIntegral.integral_congr hr.le
    intro z hz
    simp only [hA, hB]
    rw [star_gw c M r hr z hz, deriv_gw c M z (sphere_ne_zero r hr z hz)]
  rw [hcongr]
  -- Continuity on the circle.
  have hA1c : ContinuousOn A1 (Metric.sphere (0 : ℂ) r) := by
    simp only [hA1]
    exact continuousOn_id.mul_const ((r : ℂ) ^ 2)⁻¹
  have hSc : ContinuousOn S (Metric.sphere (0 : ℂ) r) := by
    simp only [hS]
    exact continuousOn_sum_inv_pow r hr M (fun n => starRingEnd ℂ (c n) * (r : ℂ) ^ (2 * n))
  have hNc : ContinuousOn N (Metric.sphere (0 : ℂ) r) := by
    simp only [hN]
    exact (continuousOn_inv_pow_sphere r hr 2).neg
  have hDc : ContinuousOn D (Metric.sphere (0 : ℂ) r) := by
    simp only [hD]
    exact continuousOn_laurentSum r hr M (fun n => c n * (n : ℂ)) (fun n => (n : ℤ) - 1)
  have hBc : ContinuousOn B (Metric.sphere (0 : ℂ) r) := by
    simp only [hB]
    exact (continuousOn_inv_pow_sphere r hr 2).neg.add
      (continuousOn_laurentSum r hr M (fun n => c n * (n : ℂ)) (fun n => (n : ℤ) - 1))
  -- Step 2: split.
  have hsplit1 : (∮ z in C(0, r), A z * B z)
      = (∮ z in C(0, r), A1 z * B z) + (∮ z in C(0, r), S z * B z) := by
    have hpt : (fun z : ℂ => A z * B z) = fun z : ℂ => A1 z * B z + S z * B z := by
      funext z; simp only [hA, hA1, hS]; ring
    rw [hpt]
    exact circleIntegral.integral_add
      (ContinuousOn.circleIntegrable hr.le (hA1c.mul hBc))
      (ContinuousOn.circleIntegrable hr.le (hSc.mul hBc))
  have hsplit2 : (∮ z in C(0, r), A1 z * B z)
      = (∮ z in C(0, r), A1 z * N z) + (∮ z in C(0, r), A1 z * D z) := by
    have hpt : (fun z : ℂ => A1 z * B z) = fun z : ℂ => A1 z * N z + A1 z * D z := by
      funext z; simp only [hB, hN, hD]; ring
    rw [hpt]
    exact circleIntegral.integral_add
      (ContinuousOn.circleIntegrable hr.le (hA1c.mul hNc))
      (ContinuousOn.circleIntegrable hr.le (hA1c.mul hDc))
  have hsplit3 : (∮ z in C(0, r), S z * B z)
      = (∮ z in C(0, r), S z * N z) + (∮ z in C(0, r), S z * D z) := by
    have hpt : (fun z : ℂ => S z * B z) = fun z : ℂ => S z * N z + S z * D z := by
      funext z; simp only [hB, hN, hD]; ring
    rw [hpt]
    exact circleIntegral.integral_add
      (ContinuousOn.circleIntegrable hr.le (hSc.mul hNc))
      (ContinuousOn.circleIntegrable hr.le (hSc.mul hDc))
  -- Step 3: the four values.
  have hAN : (∮ z in C(0, r), A1 z * N z) = -(((r : ℂ) ^ 2)⁻¹) * (2 * Real.pi * Complex.I) := by
    have hpt : (fun z : ℂ => A1 z * N z)
        = fun z : ℂ => (((r : ℂ) ^ 2)⁻¹ * z ^ (1 : ℤ)) * ((-1) * z ^ (-2 : ℤ)) := by
      funext z; simp only [hA1, hN, zpow_one, zpow_neg_two]
      ring
    rw [hpt, circleIntegral_mono_times_zpow r hr ((r : ℂ) ^ 2)⁻¹ (-1) 1 (-2),
      show (1 : ℤ) + (-2) = -1 by norm_num, circleIntegral_zpow_neg_one r hr]
    ring
  have hAD : (∮ z in C(0, r), A1 z * D z) = 0 := by
    have hpt : (fun z : ℂ => A1 z * D z)
        = fun z : ℂ => (((r : ℂ) ^ 2)⁻¹ * z ^ (1 : ℤ))
            * (∑ m ∈ Finset.range M, (c m * (m : ℂ)) * z ^ ((m : ℤ) - 1)) := by
      funext z; simp only [hA1, hD, zpow_one]; ring
    rw [hpt, circleIntegral_mono_times_sum r hr M ((r : ℂ) ^ 2)⁻¹ 1
      (fun m => c m * (m : ℂ)) (fun m => (m : ℤ) - 1)]
    refine Finset.sum_eq_zero (fun m _ => ?_)
    have hexp : (1 : ℤ) + ((m : ℤ) - 1) ≠ -1 := by
      have h1 : (1 : ℤ) + ((m : ℤ) - 1) = (m : ℤ) := by ring
      rw [h1]; exact fun h => by omega
    rw [circleIntegral_zpow_of_ne r _ hexp, mul_zero]
  have hSN : (∮ z in C(0, r), S z * N z) = 0 := by
    have hpt : (fun z : ℂ => S z * N z)
        = fun z : ℂ => (∑ n ∈ Finset.range M,
            (starRingEnd ℂ (c n) * (r : ℂ) ^ (2 * n)) * z ^ (-(n : ℤ)))
            * ((-1) * z ^ (-2 : ℤ)) := by
      funext z; simp only [hS, hN]
      rw [show (∑ n ∈ Finset.range M, starRingEnd ℂ (c n) * (r : ℂ) ^ (2 * n) * (z ^ n)⁻¹)
            = ∑ n ∈ Finset.range M,
                (starRingEnd ℂ (c n) * (r : ℂ) ^ (2 * n)) * z ^ (-(n : ℤ)) from by
          refine Finset.sum_congr rfl (fun n _ => ?_)
          rw [show z ^ (-(n : ℤ)) = (z ^ n)⁻¹ by rw [zpow_neg, zpow_natCast]]]
      rw [zpow_neg_two]
      ring
    rw [hpt, circleIntegral_sum_times_mono r hr M
      (fun n => starRingEnd ℂ (c n) * (r : ℂ) ^ (2 * n)) (fun n => -(n : ℤ)) (-1) (-2)]
    refine Finset.sum_eq_zero (fun n _ => ?_)
    have hexp : (-(n : ℤ) + (-2 : ℤ)) ≠ -1 := fun h => by omega
    rw [circleIntegral_zpow_of_ne r _ hexp, mul_zero]
  have hSD : (∮ z in C(0, r), S z * D z)
      = 2 * Real.pi * Complex.I *
          (((∑ n ∈ Finset.range M, (n : ℝ) * ‖c n‖ ^ 2 * r ^ (2 * n)) : ℝ) : ℂ) := by
    have hS_eq : S = fun z : ℂ => ∑ n ∈ Finset.range M,
        (starRingEnd ℂ (c n) * (r : ℂ) ^ (2 * n)) * z ^ (-(n : ℤ)) := by
      funext z; simp only [hS]
      refine Finset.sum_congr rfl (fun n _ => ?_)
      rw [show z ^ (-(n : ℤ)) = (z ^ n)⁻¹ by rw [zpow_neg, zpow_natCast]]
    have hD_eq : D = fun z : ℂ => ∑ m ∈ Finset.range M,
        (c m * (m : ℂ)) * z ^ ((m : ℤ) - 1) := by
      funext z; simp only [hD]
    rw [hS_eq, hD_eq]
    rw [circleIntegral_doubleSum r hr M M
      (fun n => starRingEnd ℂ (c n) * (r : ℂ) ^ (2 * n)) (fun n => -(n : ℤ))
      (fun m => c m * (m : ℂ)) (fun m => (m : ℤ) - 1)]
    have hcollapse : (∑ n ∈ Finset.range M, ∑ m ∈ Finset.range M,
          (starRingEnd ℂ (c n) * (r : ℂ) ^ (2 * n)) * (c m * (m : ℂ))
            * (∮ z in C(0, r), z ^ (-(n : ℤ) + ((m : ℤ) - 1))))
        = ∑ n ∈ Finset.range M, (starRingEnd ℂ (c n) * (r : ℂ) ^ (2 * n)) * (c n * (n : ℂ))
            * (∮ z in C(0, r), z ^ (-(n : ℤ) + ((n : ℤ) - 1))) := by
      refine Finset.sum_congr rfl (fun n hn => ?_)
      refine Finset.sum_eq_single n (fun b _ hbn => ?_) (fun h => absurd hn h)
      have hexp : (-(n : ℤ) + ((b : ℤ) - 1)) ≠ -1 := by
        intro hc
        have hb : (b : ℤ) = (n : ℤ) := by omega
        exact hbn (by exact_mod_cast hb)
      rw [circleIntegral_zpow_of_ne r _ hexp, mul_zero]
    rw [hcollapse,
      Finset.sum_congr rfl (fun n _ => by
        rw [show (-(n : ℤ) + ((n : ℤ) - 1)) = (-1 : ℤ) by ring,
          circleIntegral_zpow_neg_one r hr])]
    have hY : (∑ n ∈ Finset.range M,
          (starRingEnd ℂ (c n) * (r : ℂ) ^ (2 * n)) * (c n * (n : ℂ)))
        = (((∑ n ∈ Finset.range M, (n : ℝ) * ‖c n‖ ^ 2 * r ^ (2 * n)) : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum]
      refine Finset.sum_congr rfl (fun n _ => ?_)
      have hcs : (((‖c n‖ : ℝ)) : ℂ) ^ 2 = starRingEnd ℂ (c n) * c n := by
        rw [← Complex.ofReal_pow (‖c n‖) 2, ← Complex.normSq_eq_norm_sq, mul_comm,
          Complex.mul_conj]
      push_cast
      rw [hcs]
      ring
    rw [← Finset.sum_mul, hY, mul_comm]
  -- Step 4: assemble.
  rw [hsplit1, hsplit2, hsplit3, hAN, hAD, hSN, hSD]
  have hz : ((r ^ (-2 : ℤ) : ℝ) : ℂ) = ((r : ℂ) ^ 2)⁻¹ := by
    rw [Complex.ofReal_zpow, show (-2 : ℤ) = -(2 : ℤ) by norm_num, zpow_neg, zpow_ofNat]
  rw [Complex.ofReal_sub, hz]
  ring

end

end Work.Koebe
