import Mathlib

/-!
# Objects for the `S₃` main-term assembly (`JutilaPieces/S3MainTermClaim`)

These are the objects in which the whole `S₃` main-term computation is phrased.  The target sum is

`T(z,N) = Σ_{q ≤ N/z} Σ_{r,t ≤ N/(qz)} [r ⟂ t]·μ(r)μ(t)·s3c(rt)·⌊N/(qrt)⌋·Wt(...)`

with `s3c(c) = (π²/6)⁻¹·∏_{p|c} p/(p+1)`.  Two structural facts drive everything:

* for `(r,t) = 1`, `s3c(rt) = (π²/6)⁻¹·pfac(r)·pfac(t)` (`pfac` is multiplicative), and
* `⌊N/(qrt)⌋ ≈ N/(qrt) = (N/q)·(1/r)·(1/t)`,

so the summand is `(N/q)·(π²/6)⁻¹·w(r)w(t)·(...)` with `w(n) = μ(n)·pfac(n)/n`: with
`x = N/(qz)` and `M = N/(qrt)` one has `log(M t/z) = log(x/r)`, `log(M r/z) = log(x/t)`.  This file
introduces `s3w` and the resulting "clean" double sum `s3Phi`.
-/

namespace Work.LinnikAreas.JutilaPieces

open Finset

noncomputable section

/-- The `1/κ`-weight `w(n) = μ(n)·∏_{p ∣ n} p/(p+1)/n` (the weight `μ(n)/κ(n)` of An's §5, since
`κ(n) = n·∏_{p ∣ n}(1+1/p)`). -/
def s3w (n : ℕ) : ℝ :=
  (ArithmeticFunction.moebius n : ℝ) * (∏ p ∈ n.primeFactors, (p : ℝ) / ((p : ℝ) + 1))
    / (n : ℝ)

/-- `pfac(n) = ∏_{p ∣ n} p/(p+1)`, the multiplicative density factor. -/
def s3pfac (n : ℕ) : ℝ := ∏ p ∈ n.primeFactors, (p : ℝ) / ((p : ℝ) + 1)

/-- The "clean" double sum attached to a real cut-off `x ≥ 1`:

`Φ(x) = (π²/6)⁻¹·Σ_{r,t ≤ ⌊x⌋, (r,t)=1} w(r)w(t)·((log(x/r)−1)(log(x/t)−1)+1)`.

By the reindexing described in the module docstring, `Σ_q (N/q)·Φ(N/(qz))` is the continuous
(rather than floored) version of the target triple sum. -/
def s3Phi (x : ℝ) : ℝ :=
  (Real.pi ^ 2 / 6)⁻¹ *
    ∑ r ∈ Finset.Icc 1 ⌊x⌋₊, ∑ t ∈ Finset.Icc 1 ⌊x⌋₊,
      (if Nat.Coprime r t then
        s3w r * s3w t * ((Real.log (x / (r : ℝ)) - 1) * (Real.log (x / (t : ℝ)) - 1) + 1)
      else 0)

/-- The main-term formula `s3main` of `BzS3/S3InnerDefs` with a **real** cut-off:
`s3MainReal c α β s = (π²/6)⁻¹·∏_{p ∣ c} p/(p+1)·s·((log s − α − 1)(log s − β − 1) + 1)`. -/
def s3MainReal (c : ℕ) (α β s : ℝ) : ℝ :=
  (Real.pi ^ 2 / 6)⁻¹ * (∏ p ∈ c.primeFactors, (p : ℝ) / ((p : ℝ) + 1)) * s
    * ((Real.log s - α - 1) * (Real.log s - β - 1) + 1)

/-- `s3pfac` is multiplicative on coprime nonzero arguments. -/
lemma s3pfac_mul {r t : ℕ} (hr : r ≠ 0) (ht : t ≠ 0) (h : Nat.Coprime r t) :
    s3pfac (r * t) = s3pfac r * s3pfac t := by
  simp only [s3pfac]
  rw [Nat.primeFactors_mul hr ht, Finset.prod_union ((Nat.disjoint_primeFactors hr ht).mpr h)]

/-- On coprime nonzero arguments, `pfac(r·t)/(r·t) = (pfac r/r)(pfac t/t)`. -/
lemma s3pfac_div_mul {r t : ℕ} (hr : r ≠ 0) (ht : t ≠ 0) (h : Nat.Coprime r t) :
    s3pfac (r * t) / ((r * t : ℕ) : ℝ) = s3pfac r / (r : ℝ) * (s3pfac t / (t : ℝ)) := by
  have hh := s3pfac_mul hr ht h
  simp only [s3pfac] at hh ⊢
  rw [hh]
  have hr0 : (r:ℝ) ≠ 0 := by exact_mod_cast hr
  have ht0 : (t:ℝ) ≠ 0 := by exact_mod_cast ht
  push_cast
  field_simp

/-- The weight `w` factorises on coprime nonzero arguments against `μ(r)μ(t)pfac(r·t)/(r·t)`. -/
lemma s3w_mul {r t : ℕ} (hr : r ≠ 0) (ht : t ≠ 0) (h : Nat.Coprime r t) :
    s3w r * s3w t
      = (ArithmeticFunction.moebius r : ℝ) * (ArithmeticFunction.moebius t : ℝ)
          * (s3pfac (r * t) / ((r * t : ℕ) : ℝ)) := by
  rw [s3pfac_div_mul hr ht h]
  simp only [s3w, s3pfac]
  ring

end

end Work.LinnikAreas.JutilaPieces
