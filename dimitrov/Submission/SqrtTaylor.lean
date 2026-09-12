import Mathlib
import Submission.SqrtUnique

/-!
# Taylor coefficients of a holomorphic square root equal the formal square root

`Submission.PowRev.powRev_sqrt_integral` produces the integer sequence
`a : ℕ → ℤ` with `a 0 = 1` whose convolution square is the coefficient
sequence of `G := (pow2 P).reflect d * (pow4 P).reflect d ∈ ℤ[w]`.

Suppose `f` is holomorphic on a ball `ball 0 r` around `0` with `f 0 = 1`
and `f z ^ 2 = G(z)` (polynomial evaluation over `ℂ`) on that ball.  This
module proves that the Taylor coefficients of `f` at `0`,

    taylorCoeff f k := (Nat.factorial k : ℂ)⁻¹ * iteratedDeriv k f 0,

satisfy the same convolution identities as `a`, and hence equal `a`:

    taylorCoeff f k = (a k : ℂ)     for all k.

The engine uses this to know that the holomorphic square root produced by
`Submission.HoloSqrt.exists_holomorphic_sq_eq` on a simply connected domain
(which restricts to such an `f` on a small ball around `0`) carries the
*integer* Taylor coefficients `a` -- the input needed by the rationality
theorem (Pólya / Bertrandias).

## Proof route

1. `taylorCoeff_mul`: for functions smooth at `0`,
   `taylorCoeff (f * g) k = (∑ i ∈ range (k+1), taylorCoeff f i * taylorCoeff g (k - i))`.
   *Proof:* `iteratedDeriv_mul` (Leibniz rule; `Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas`):
   `iteratedDeriv k (f*g) 0 = ∑ i ∈ range (k+1), k.choose i * iteratedDeriv i f 0 * iteratedDeriv (k-i) g 0`; multiply by
   `(k!)⁻¹` and use `k.choose i / k! = 1/(i!·(k-i)!)` (i.e.
   `Nat.choose_mul_factorial_mul_factorial`), so that
   `(k!)⁻¹ * k.choose i = (i!)⁻¹ * ((k-i)!)⁻¹` in `ℂ`.
2. `taylorCoeff_sq`: with `g = f`: the convolution square of `taylorCoeff f`
   is `taylorCoeff (fun w => f w ^ 2)`.
   Needs `ContDiffAt ℂ k f 0` for every `k`, which follows from holomorphy on a
   ball around `0` (`DifferentiableOn.contDiffOn` + `contDiffOn.contDiffAt`).
3. `taylorCoeff_poly`: for `p : ℂ[X]`, `taylorCoeff (fun w => p.eval w) k =
   p.coeff k` (for every `k`; for `k > natDegree` both sides vanish).  Use the
   linearity of `iteratedDeriv` and `iteratedDeriv_pow` (iterated derivative
   of `w ↦ w^m` at `0` is `if k = m then m! else 0`).
4. If additionally `f z ^ 2 = G(z)` on a neighbourhood of `0` (e.g. on the
   ball), then the iterated derivatives of both sides at `0` agree, so
   `taylorCoeff (fun w => f w ^ 2) k = (G.coeff k : ℂ)`; combine with 2 and 3.
5. `taylorCoeff_sqrt_eq`: with `f 0 = 1` we have `taylorCoeff f 0 = 1`, so by
   `Submission.SqrtUnique.sqrt_seq_unique` applied to `taylorCoeff f` and
   `fun k => (a k : ℂ)` (both have first value 1 and the same convolution
   square `(G.coeff k : ℂ)`), `taylorCoeff f k = (a k : ℂ)` for all `k`.

You may add helper lemmas/definitions.  Do NOT change the statements of the
declarations below (add any helpers you like above them).  No sorries may
remain in this file.
-/

noncomputable section

open Complex
open Filter
open Polynomial
open scoped Polynomial Real Topology

namespace Submission.SqrtTaylor

/-- The `k`-th Taylor coefficient of `f` at `0`: `f⁽ᵏ⁾(0) / k!`. -/
def taylorCoeff (f : ℂ → ℂ) (k : ℕ) : ℂ :=
  (Nat.factorial k : ℂ)⁻¹ * iteratedDeriv k f 0

/-- `(k!)⁻¹ * (k choose i) = (i!)⁻¹ * ((k-i)!)⁻¹` in `ℂ`, for `i ≤ k`. -/
lemma factorial_inv_choose (k i : ℕ) (hi : i ≤ k) :
    ((Nat.factorial k : ℂ))⁻¹ * (Nat.choose k i : ℂ) =
      ((Nat.factorial i : ℂ))⁻¹ * ((Nat.factorial (k - i) : ℂ))⁻¹ := by
  have hC : (Nat.choose k i : ℂ) * (Nat.factorial i : ℂ) *
      (Nat.factorial (k - i) : ℂ) = (Nat.factorial k : ℂ) := by
    exact_mod_cast (Nat.choose_mul_factorial_mul_factorial (k := i) hi)
  have hfi : (Nat.factorial i : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
  have hfkmi : (Nat.factorial (k - i) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (k - i)
  have hfk : (Nat.factorial k : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  field_simp [hfi, hfkmi, hfk]
  ring_nf
  exact hC

/-- Taylor coefficients multiply by convolution (Leibniz rule), provided both
functions are sufficiently smooth at `0`. -/
theorem taylorCoeff_mul {f g : ℂ → ℂ} {k : ℕ}
    (hf : ContDiffAt ℂ k f 0) (hg : ContDiffAt ℂ k g 0) :
    taylorCoeff (fun w => f w * g w) k =
      ∑ i ∈ Finset.range (k + 1), taylorCoeff f i * taylorCoeff g (k - i) := by
  unfold taylorCoeff
  change (↑k.factorial)⁻¹ * iteratedDeriv k (f * g) 0 =
      ∑ i ∈ Finset.range (k + 1),
        (↑i.factorial)⁻¹ * iteratedDeriv i f 0 *
          ((↑(k - i).factorial)⁻¹ * iteratedDeriv (k - i) g 0)
  rw [iteratedDeriv_mul hf hg]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hik : i ≤ k := by
    exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  calc
    (↑k.factorial)⁻¹ * (↑(k.choose i) * iteratedDeriv i f 0 * iteratedDeriv (k - i) g 0)
        = (↑k.factorial)⁻¹ * ↑(k.choose i) *
            (iteratedDeriv i f 0 * iteratedDeriv (k - i) g 0) := by
          ring
    _ = (↑i.factorial)⁻¹ * (↑(k - i).factorial)⁻¹ *
            (iteratedDeriv i f 0 * iteratedDeriv (k - i) g 0) := by
          rw [factorial_inv_choose k i hik]
    _ = (↑i.factorial)⁻¹ * iteratedDeriv i f 0 *
          ((↑(k - i).factorial)⁻¹ * iteratedDeriv (k - i) g 0) := by
          ring

/-- The Taylor coefficients of the square are the convolution square. -/
theorem taylorCoeff_sq {f : ℂ → ℂ} {k : ℕ} (hf : ContDiffAt ℂ k f 0) :
    taylorCoeff (fun w => f w ^ 2) k =
      ∑ i ∈ Finset.range (k + 1), taylorCoeff f i * taylorCoeff f (k - i) := by
  simpa [pow_two] using (taylorCoeff_mul (f := f) (g := f) hf hf)

/-- The `k`-th iterated derivative at `0` of a monomial `w ↦ c * w ^ i`. -/
lemma iteratedDeriv_monomial (c : ℂ) (k i : ℕ) :
    iteratedDeriv k (fun w : ℂ => c * w ^ i) 0 = c * (if k = i then (i.factorial : ℂ) else 0) := by
  have hpw : ContDiffAt ℂ k (fun w : ℂ => w ^ i) 0 := by
    simpa using (ContDiffAt.pow (n := (k : ℕ∞)) (x := (0 : ℂ))
      (f := fun w : ℂ => w) contDiffAt_id i)
  rw [iteratedDeriv_const_mul (c := c) hpw]
  rw [iteratedDeriv_fun_pow_zero (𝕜 := ℂ) (n := k) (m := i)]
  by_cases hki : k = i
  · simp [hki]
  · simp [hki]

/-- Monomials are smooth. -/
lemma contDiffAt_monomial (c : ℂ) (k i : ℕ) : ContDiffAt ℂ k (fun w : ℂ => c * w ^ i) 0 := by
  have h1 : ContDiffAt ℂ k (fun _ : ℂ => c) 0 := contDiffAt_const
  have h2 : ContDiffAt ℂ k (fun w : ℂ => w ^ i) 0 := by
    simpa using (ContDiffAt.pow (n := (k : ℕ∞)) (x := (0 : ℂ))
      (f := fun w : ℂ => w) contDiffAt_id i)
  simpa using (ContDiffAt.mul (𝕜 := ℂ) (x := (0 : ℂ)) (n := (k : ℕ∞)) h1 h2)

/-- In `∑ i < natDegree p + 1`, `p.coeff i * (if k = i then i! else 0)`, only the
term `i = k` survives and contributes `k! * p.coeff k`. -/
lemma sum_if_factorial (p : ℂ[X]) (k : ℕ) :
    (∑ i ∈ Finset.range (p.natDegree + 1),
        p.coeff i * (if k = i then (i.factorial : ℂ) else 0))
      = (k.factorial : ℂ) * p.coeff k := by
  by_cases hk : k < p.natDegree + 1
  · have hkmem : k ∈ Finset.range (p.natDegree + 1) := Finset.mem_range.mpr hk
    calc
      (∑ i ∈ Finset.range (p.natDegree + 1),
          p.coeff i * (if k = i then (i.factorial : ℂ) else 0))
          = p.coeff k * (if k = k then (k.factorial : ℂ) else 0) := by
            apply Finset.sum_eq_single (a := k)
            · intro b hb hbk
              have : ¬ k = b := fun h => hbk h.symm
              simp [this]
            · intro hknotmem
              exact False.elim (hknotmem hkmem)
      _ = (k.factorial : ℂ) * p.coeff k := by simp; ring
  · have hknd : p.natDegree < k := by omega
    have hcoeff : p.coeff k = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt hknd
    have hsum0 :
        (∑ i ∈ Finset.range (p.natDegree + 1),
          p.coeff i * (if k = i then (i.factorial : ℂ) else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hilt : i < p.natDegree + 1 := Finset.mem_range.mp hi
      have hik : i ≠ k := by omega
      have : ¬ k = i := fun h => hik h.symm
      simp [this]
    rw [hsum0, hcoeff]
    simp

/-- The `k`-th iterated derivative at `0` of a polynomial evaluation. -/
lemma iteratedDeriv_poly_eval (p : ℂ[X]) (k : ℕ) :
    iteratedDeriv k (fun w : ℂ => p.eval w) 0 = (k.factorial : ℂ) * p.coeff k := by
  have hfun : (fun w : ℂ => p.eval w) =
      (fun w : ℂ => ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * w ^ i) := by
    funext w
    exact Polynomial.eval_eq_sum_range (p := p) w
  rw [hfun]
  calc
    iteratedDeriv k (fun w : ℂ => ∑ i ∈ Finset.range (p.natDegree + 1),
        p.coeff i * w ^ i) 0
        = ∑ i ∈ Finset.range (p.natDegree + 1),
            iteratedDeriv k (fun w : ℂ => p.coeff i * w ^ i) 0 := by
            rw [iteratedDeriv_fun_sum]
            intro i hi
            exact contDiffAt_monomial (p.coeff i) k i
    _ = ∑ i ∈ Finset.range (p.natDegree + 1),
          p.coeff i * (if k = i then (i.factorial : ℂ) else 0) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact iteratedDeriv_monomial (p.coeff i) k i
    _ = (k.factorial : ℂ) * p.coeff k := sum_if_factorial p k

/-- The Taylor coefficients at `0` of the evaluation function of a polynomial
are its coefficients. -/
theorem taylorCoeff_poly (p : ℂ[X]) (k : ℕ) :
    taylorCoeff (fun w : ℂ => p.eval w) k = p.coeff k := by
  unfold taylorCoeff
  rw [iteratedDeriv_poly_eval p k]
  have hfk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  rw [← mul_assoc, inv_mul_cancel₀ hfk, one_mul]

/-- The Taylor coefficients at `0` of `G.eval₂ (algebraMap ℤ ℂ)` are the
integer coefficients of `G`. -/
lemma taylorCoeff_poly_int (G : ℤ[X]) (k : ℕ) :
    taylorCoeff (fun w : ℂ => G.eval₂ (algebraMap ℤ ℂ) w) k = (G.coeff k : ℂ) := by
  have hmap : (fun w : ℂ => G.eval₂ (algebraMap ℤ ℂ) w) =
      (fun w : ℂ => (G.map (algebraMap ℤ ℂ)).eval w) := by
    funext w
    rw [Polynomial.eval₂_eq_eval_map]
  rw [hmap]
  rw [taylorCoeff_poly (G.map (algebraMap ℤ ℂ)) k]
  simp

/-- **Main bridge.**  Let `G : ℤ[X]` with `G.coeff 0 = 1` and let
`a : ℕ → ℤ` be the (unique) formal square root of `G` (`a 0 = 1`, convolution
square `= G.coeff`).  If `f` is holomorphic on the ball around `0` with
`f 0 = 1` and `f z ^ 2 = G(z)` there, then the Taylor coefficients of `f`
at `0` are the integers `a k`. -/
theorem taylorCoeff_sqrt_eq {G : ℤ[X]} (hG0 : G.coeff 0 = 1)
    {a : ℕ → ℤ} (ha0 : a 0 = 1)
    (ha : ∀ k : ℕ, (∑ i ∈ Finset.range (k + 1), a i * a (k - i)) = G.coeff k)
    {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (Metric.ball 0 r)) (hf0 : f 0 = 1)
    (hfsq : ∀ z ∈ Metric.ball 0 r,
      f z ^ 2 = G.eval₂ (algebraMap ℤ ℂ) z) :
    ∀ k : ℕ, taylorCoeff f k = (a k : ℂ) := by
  have hcdat : ∀ k : ℕ, ContDiffAt ℂ k f 0 := by
    intro k
    have hcd : ContDiffOn ℂ (k : ℕ∞) f (Metric.ball 0 r) :=
      hf.contDiffOn (s := Metric.ball 0 r) (n := (k : ℕ∞)) Metric.isOpen_ball
    exact hcd.contDiffAt (Metric.ball_mem_nhds 0 hr)
  have hfG : (fun w : ℂ => f w ^ 2) =ᶠ[𝓝 0]
      (fun w : ℂ => G.eval₂ (algebraMap ℤ ℂ) w) := by
    filter_upwards [Metric.ball_mem_nhds 0 hr] with z hz
    exact hfsq z hz
  have hsqcoeff : ∀ k : ℕ,
      taylorCoeff (fun w : ℂ => f w ^ 2) k =
        taylorCoeff (fun w : ℂ => G.eval₂ (algebraMap ℤ ℂ) w) k := by
    intro k
    unfold taylorCoeff
    rw [Filter.EventuallyEq.iteratedDeriv_eq k hfG]
  refine SqrtUnique.sqrt_seq_unique (b := taylorCoeff f)
    (c := fun k => (a k : ℂ)) ?hb0 ?hc0 ?hconv
  · unfold taylorCoeff
    simp [hf0]
  · exact_mod_cast ha0
  · intro k
    calc
      (∑ i ∈ Finset.range (k + 1), taylorCoeff f i * taylorCoeff f (k - i))
          = taylorCoeff (fun w : ℂ => f w ^ 2) k := by
              exact (taylorCoeff_sq (f := f) (k := k) (hcdat k)).symm
      _ = taylorCoeff (fun w : ℂ => G.eval₂ (algebraMap ℤ ℂ) w) k := hsqcoeff k
      _ = (G.coeff k : ℂ) := taylorCoeff_poly_int G k
      _ = (∑ i ∈ Finset.range (k + 1), (a i : ℂ) * (a (k - i) : ℂ)) := by
          rw [← ha k]
          rw [Int.cast_sum]
          apply Finset.sum_congr rfl
          intro i hi
          rw [Int.cast_mul]

end Submission.SqrtTaylor

end
