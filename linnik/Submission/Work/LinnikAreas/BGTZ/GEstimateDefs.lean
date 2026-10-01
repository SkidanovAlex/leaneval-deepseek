/-
# `Work.LinnikAreas.BGTZ` — the vocabulary of the `G`-estimate (BGTZ Lemma 4.3)

This file introduces the *arithmetic weights* through which the `G`-estimate is proved:

* `gwt χ₁ p = (1 + χ₁(p)) / √p + 1/p` — the bound (BGTZ (4.10)) for the local factor of the
  Selberg sieve function at the prime `p`, for a real character `χ₁` (`χ₁ ^ 2 = 1`);
* `gw χ₁ n = ∏_{p | n} gwt χ₁ p` — the multiplicative weight (`f(n) n^{-1/2}` for BGTZ's `f`);
* `gsum χ₁ R = Σ_{d ≤ R} gw χ₁ d` — the single sum `Σ_{d ≤ R} f(d) d^{-1/2}` of BGTZ Lemma 4.3;
* `gpairsum χ₁ R = Σ_{d,e ≤ R} gw χ₁ (lcm d e)` — the double sum dominating `‖sieveG‖`.

The mathematical content of BGTZ Lemma 4.3 is then the two facts

* `gpairsum χ₁ R ≤ K * (gsum χ₁ R)^2` (the paper's `ΣΣ f([d,e])[d,e]^{-1/2} ≤ (Σ f(d)d^{-1/2})^2`,
  valid with a universal constant), and
* `gsum χ₁ R ≤ c * (‖L(1,χ₁)‖ √R + A q^θ e^{(log q)^{3/4}} log^6(2eR))` (the Mellin inversion and
  contour shift of `Φ(s) = ζ(s+1/2)L(s+1/2,χ₁)B(s+1/2)`).
-/
import Mathlib
import Submission.Work.LinnikAreas.BGTZSetup

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikAreas

namespace BGTZ

variable {q : ℕ} [NeZero q]

/-- The local weight `γ(p) = (1 + χ₁(p))/√p + 1/p` of the `G`-estimate. -/
def gwt (χ₁ : DirichletCharacter ℂ q) (p : ℕ) : ℝ :=
  (1 + (χ₁ p).re) / Real.sqrt p + 1 / p

/-- The multiplicative weight `gw χ₁ n = ∏_{p | n} gwt χ₁ p` for squarefree `n`, and `0` for
non-squarefree `n`: this is exactly BGTZ's `f(n) n^{-1/2}`, i.e. `f(n) = Σ_{p | n} gwt χ₁ p`
extended multiplicatively to the squarefree integers and put equal to `0` otherwise.  (The
`Squarefree` restriction is essential: without it the single sum gains an extra `ζ(s)` factor and
the `R`-linear term of the estimate would acquire a spurious factor `log R`.) -/
def gw (χ₁ : DirichletCharacter ℂ q) (n : ℕ) : ℝ :=
  if Squarefree n then ∏ p ∈ n.primeFactors, gwt χ₁ p else 0

/-- For squarefree `n` the weight is the product of the local weights. -/
lemma gw_of_squarefree (χ₁ : DirichletCharacter ℂ q) {n : ℕ} (hn : Squarefree n) :
    gw χ₁ n = ∏ p ∈ n.primeFactors, gwt χ₁ p := if_pos hn

/-- For non-squarefree `n` the weight vanishes. -/
lemma gw_of_not_squarefree (χ₁ : DirichletCharacter ℂ q) {n : ℕ} (hn : ¬ Squarefree n) :
    gw χ₁ n = 0 := if_neg hn

/-- The single sum `Σ_{d ≤ R} gw χ₁ d = Σ_{d ≤ R} f(d) d^{-1/2}` of BGTZ Lemma 4.3. -/
def gsum (χ₁ : DirichletCharacter ℂ q) (R : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 R, gw χ₁ d

/-- The double sum `Σ_{d,e ≤ R} f([d,e]) [d,e]^{-1/2} = Σ_{d,e ≤ R} gw χ₁ (lcm d e)`. -/
def gpairsum (χ₁ : DirichletCharacter ℂ q) (R : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 R, gw χ₁ (Nat.lcm d e)

/-! ## The corrected pair-sum reduction

The printed proof of BGTZ Lemma 4.3 replaces the double `lcm`-sum by the *square* of the single sum,
`ΣΣ f([d,e])[d,e]^{-1/2} ≤ (Σ f(d)d^{-1/2})²`.  **That step is false.**  Writing
`∏_{p|[d,e]}gwt p = gw(d)·∏_{p|e, p∤d}gwt p` and decomposing `e = e₁e₂` with `e₁ = gcd(e,d)`,
`(e₂,d) = 1` shows that the correct replacement carries the extra factor `2^{ω(d)}`:

`gpairsum χ₁ R ≤ gsum χ₁ R · gsum2 χ₁ R`,

with `gsum2 χ₁ R = Σ_{d ≤ R} 2^{ω(d)} gw χ₁ d`.  (The printed step fails already at `R = 2` for a
real `χ₁` with `χ₁(2) = -1`: `ΣΣ = 5/2 > (Σ)² = 9/4`.)  The replacement is still strong enough for
the detector: `gsum` is `≍ L(1,χ₁)√R + err` (BGTZ's contour shift) and `gsum2` is
`≍ L(1,χ₁)²√R log R + err`, so the product is `≍ L(1,χ₁)³R log R`, whose `(1-β₁)³` factor — three
powers, versus the two the printed statement needs — is more than enough inside the detector,
because the sifting level there is `R ≍ A²q^{2θ}e^{2(log q)^{3/4}}(1-β₁)^{-2}`. -/

/-- The second single sum `Σ_{d ≤ R} 2^{ω(d)} gw χ₁ d` of the corrected pair-sum reduction. -/
def gsum2 (χ₁ : DirichletCharacter ℂ q) (R : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 R, (2 : ℝ) ^ d.primeFactors.card * gw χ₁ d

/-- The real part of a character value is at most `1`. -/
lemma re_apply_le_one (χ₁ : DirichletCharacter ℂ q) (p : ℕ) : (χ₁ p).re ≤ 1 :=
  le_trans (Complex.re_le_norm _) (norm_le_one χ₁ p)

/-- The real part of a character value is at least `-1`. -/
lemma neg_one_le_re_apply (χ₁ : DirichletCharacter ℂ q) (p : ℕ) : -1 ≤ (χ₁ p).re := by
  have h1 : |(χ₁ p).re| ≤ ‖χ₁ p‖ := Complex.abs_re_le_norm (χ₁ p)
  have h2 : ‖χ₁ p‖ ≤ 1 := norm_le_one χ₁ p
  have h3 : -(1:ℝ) ≤ -|(χ₁ p).re| := by linarith
  have h4 : -|(χ₁ p).re| ≤ (χ₁ p).re := neg_abs_le _
  linarith

/-- The local weight is non-negative. -/
lemma gwt_nonneg (χ₁ : DirichletCharacter ℂ q) (p : ℕ) : 0 ≤ gwt χ₁ p := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp [gwt]
  · have h1 : -1 ≤ (χ₁ p).re := neg_one_le_re_apply χ₁ p
    have hs : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hp)
    have h2 : 0 ≤ (1 + (χ₁ p).re) / Real.sqrt (p : ℝ) := div_nonneg (by linarith) hs.le
    have h3 : 0 ≤ 1 / (p : ℝ) := by positivity
    simp only [gwt]
    linarith

/-- The multiplicative weight is non-negative. -/
lemma gw_nonneg (χ₁ : DirichletCharacter ℂ q) (n : ℕ) : 0 ≤ gw χ₁ n := by
  rw [gw]
  split
  · exact Finset.prod_nonneg fun p _ => gwt_nonneg χ₁ p
  · exact le_refl 0

/-- `gw χ₁ 1 = 1`. -/
@[simp] lemma gw_one (χ₁ : DirichletCharacter ℂ q) : gw χ₁ 1 = 1 := by
  rw [gw_of_squarefree χ₁ squarefree_one, Nat.primeFactors_one, Finset.prod_empty]

/-- The single sum is non-negative. -/
lemma gsum_nonneg (χ₁ : DirichletCharacter ℂ q) (R : ℕ) : 0 ≤ gsum χ₁ R :=
  Finset.sum_nonneg fun d _ => gw_nonneg χ₁ d

/-- The double sum is non-negative. -/
lemma gpairsum_nonneg (χ₁ : DirichletCharacter ℂ q) (R : ℕ) : 0 ≤ gpairsum χ₁ R :=
  Finset.sum_nonneg fun d _ => Finset.sum_nonneg fun e _ => gw_nonneg χ₁ _

end BGTZ

end Work.LinnikAreas
