import Mathlib
import Submission.Work.LinnikAreas.Density4.LamRDefs

/-!
# Definitions for the bilinear `B_z` estimate (`Bz_bilinear_sum_bound`)

`B_z(n) = Σ_{z < d | n} μ(d) log(d/z)` is the correction term of the Selberg weight
(`LamRDefs`).  Here we collect the numerical objects needed to evaluate
`Σ_{n ≤ x} B_w(n) B_y(n)` in the *hard* range `x < w y` following
An, arXiv:2206.10104 §5 (specialised to `k = ℚ`):

* `kappaBz n = ∏_{p | n} (p+1)`;
* `sqDens n = ∏_{p | n} p/(p+1)` — the density factor of the squarefree integers coprime to `n`
  (equal to `n/κ(n)` only for squarefree `n`, so we use this form uniformly);
* `kappaOver n = ∏_{p | n}(1 + 1/p)` — the main-term factor of the `κ`-Mertens sum
  (equal to `κ(n)/n` only for squarefree `n`);
* `sigmaHalf n = Σ_{d | n} d^{-1/2}` — the error-tail factor `σ_{-1/2}`.
-/

namespace Work.LinnikAreas.Density4

open Finset

noncomputable section

/-- `κ(n) = ∏_{p | n}(p+1)` (for squarefree `n` this is the paper's `κ(n) = n∏(1+1/p)`). -/
def kappaBz (n : ℕ) : ℝ := ∏ p ∈ n.primeFactors, ((p : ℝ) + 1)

/-- `∏_{p | n} p/(p+1)`; the density constant for the squarefree integers coprime to `n`
(`= n/κ(n)` when `n` is squarefree). -/
def sqDens (n : ℕ) : ℝ := ∏ p ∈ n.primeFactors, ((p : ℝ) / ((p : ℝ) + 1))

/-- `∏_{p | n}(1 + 1/p)`; the main-term factor of the `κ`-Mertens sum
(`= κ(n)/n` when `n` is squarefree). -/
def kappaOver (n : ℕ) : ℝ := ∏ p ∈ n.primeFactors, (1 + (1 : ℝ) / (p : ℝ))

/-- `σ_{-1/2}(n) = Σ_{d | n} d^{-1/2}`, the tail factor in An's Lemma 0108. -/
def sigmaHalf (n : ℕ) : ℝ := ∑ d ∈ n.divisors, (1 : ℝ) / Real.sqrt (d : ℝ)

@[simp] lemma kappaR_one : kappaBz 1 = 1 := by simp [kappaBz]
@[simp] lemma sqDens_one : sqDens 1 = 1 := by simp [sqDens]
@[simp] lemma kappaOver_one : kappaOver 1 = 1 := by simp [kappaOver]

lemma kappaR_pos (n : ℕ) : 0 < kappaBz n := by
  rw [kappaBz]; exact Finset.prod_pos (fun p _ => by positivity)

lemma sqDens_nonneg (n : ℕ) : 0 ≤ sqDens n := by
  rw [sqDens]; exact Finset.prod_nonneg (fun p _ => by positivity)

lemma kappaOver_pos (n : ℕ) : 0 < kappaOver n := by
  rw [kappaOver]; exact Finset.prod_pos (fun p _ => by positivity)

lemma sigmaHalf_nonneg (n : ℕ) : 0 ≤ sigmaHalf n := by
  rw [sigmaHalf]; exact Finset.sum_nonneg (fun d _ => by positivity)

/-- For squarefree `n`, `sqDens n = n / κ(n)`. -/
lemma sqDens_eq_of_squarefree {n : ℕ} (hn : Squarefree n) :
    sqDens n = (n : ℝ) / kappaBz n := by
  have hprod : (n : ℝ) = ∏ p ∈ n.primeFactors, (p : ℝ) := by
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hn]
  rw [sqDens, kappaBz, hprod, Finset.prod_div_distrib]

/-- For squarefree `n`, `kappaOver n = κ(n)/n`. -/
lemma kappaOver_eq_of_squarefree {n : ℕ} (hn : Squarefree n) :
    kappaOver n = kappaBz n / (n : ℝ) := by
  have hprod : (n : ℝ) = ∏ p ∈ n.primeFactors, (p : ℝ) := by
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hn]
  rw [kappaOver, kappaBz, hprod]
  rw [show (∏ p ∈ n.primeFactors, (1 + 1 / (p : ℝ)))
        = ∏ p ∈ n.primeFactors, (((p : ℝ) + 1) / (p : ℝ)) from
      Finset.prod_congr rfl (fun p hp => by
        have hp2 : (0 : ℝ) < (p : ℝ) := by
          have := Nat.prime_of_mem_primeFactors hp
          exact_mod_cast this.pos
        field_simp)]
  rw [Finset.prod_div_distrib]

end

end Work.LinnikAreas.Density4
