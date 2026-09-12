import Mathlib
import Submission.ModFour
import Submission.SqrtInt
import Submission.RootCorr

/-!
# GOAL: integer-coefficient square root of the reversed power product

For a monic `P : ℤ[X]`, let `P₂ := pow2 P`, `P₄ := pow4 P` (Submission.Powers;
both monic of the same degree `d := P.natDegree` by Submission.RootCorr).
Define the *reversed* polynomials at degree `d` via `Polynomial.reflect d`:
`R₂ := (pow2 P).reflect d` and `R₄ := (pow4 P).reflect d`.  (For the root form
`P = ∏(X-αᵢ)` one has `R₂(X) = ∏(1-αᵢ²X)` etc.; coefficient-wise,
`(f.reflect d).coeff i = f.coeff (d - i)` for `i ≤ d`, by `Polynomial.coeff_reflect`.)

Prove that the formal square root of `G := R₂ * R₄` with constant term 1 has
integer coefficients: i.e. there is an integer sequence `a` with `a 0 = 1` and
`(∑ i ∈ range (k+1), a i * a (k-i)) = G.coeff k` for every `k`
(the coefficient-wise form of `f² = G` with `f := Σ a k X^k ∈ ℤ[[X]]`).

## Proof plan

1. **Reversed mod-4.**  From `Submission.ModFour.pow4_sub_pow2_mod4`:
   `4 ∣ (pow4 P).coeff m - (pow2 P).coeff m` for all `m`.
   Using `Polynomial.coeff_reflect` (`(f.reflect d).coeff i = f.coeff (revAt d i)`)
   and `Polynomial.reflect_sub` / `reflect_add` (reflection is additive), prove
   `4 ∣ (R₄.coeff i - R₂.coeff i)` for all `i` (case split `i ≤ d` /
   `d < i`; the `revAt d i` is `d - i` resp. `i`, see `Polynomial.revAt_le` /
   `Polynomial.revAt_eq_self_of_lt`).  Use
   `ZMod.intCast_zmod_eq_zero_iff_dvd` if convenient.

2. **Factor G − R₂² = R₂·(R₄ − R₂).**  Its coefficients are divisible by 4:
   if `4 ∣ s j` for all `j`, then `4 ∣ (R₂ * s).coeff k` for all `k`
   (expand `coeff_mul` over the antidiagonal; each summand divisible by 4).
   Hence obtain `v : ℕ → ℤ` with `G.coeff k = conv(u,u) k + 4 * v k` where
   `u i := R₂.coeff i`, `conv(c,c) k := ∑ i ∈ range (k+1), c i * c (k-i)`
   (construct `v` with `Classical.choose` from the divisibility, as in
   `Submission.ModFour.exists_eq_add_two_mul`; note `G - R₂*R₂ = R₂*(R₄ - R₂)`
   in ℤ[X], compare coefficients).

3. **The ℚ square-root sequence.**  Define recursively
   `b 0 := 1`, `b (k+1) := (g (k+1) - ∑ i ∈ range (k+1), b i * b (k+1 - i)) / 2`
   with `g k := G.coeff k : ℚ`, division in the field ℚ.  Prove by induction
   that `conv(b) k = g k` for all `k` (i.e. `hbsq` of `Submission.SqrtInt.sqrt_integral`).
   Note `u 0 = 1` (monic `pow2 P` has leading coefficient 1, and reflection at
   degree d sends the leading coefficient to the constant coefficient; prove
   `R₂.coeff 0 = 1` from `pow2_monic`).

4. Apply `Submission.SqrtInt.sqrt_integral` to get integer witnesses
   `∀ k, ∃ z : ℤ, (z : ℚ) = b k`.  Round `b k` to integers `a k` (with
   `Classical.choose`) and prove `a 0 = 1` and `conv(a) = g` by casting the
   ℚ identities to ℤ (use `Int.cast_inj`/exact_mod_cast; note conv(a) as ℚ
   equals conv(b) since each `a i = b i` as ℚ).  Assemble into the conclusion.

Useful facts: `Polynomial.coeff_reflect`, `Polynomial.reflect_add`,
`Polynomial.reflect_sub` (check availability; if absent prove additive
reflect by ext+coeff), `Polynomial.coeff_mul`, `Finset.sum_range_succ`,
`pow2_monic` (Submission.Powers), `pow2_natDegree` (Submission.RootCorr),
`pow4_monic`/degree via `pow4 P = pow2 (pow2 P)` and the same lemmas.
You may add helper lemmas/definitions.  Do NOT change the statement of
`powRev_sqrt_integral`.  No unfilled obligations may remain in this file.
-/

noncomputable section

open Polynomial
open scoped Polynomial

namespace Submission.PowRev

open Submission.Powers
open Submission.RootCorr
open Submission.ModFour
open Submission.SqrtInt

/-- `bseq g n m` is the `m`-th coefficient of the rational square-root
sequence, computed from the first `n` coefficients (valid for `m ≤ n`).
The recursion is on the number `n` of already-known coefficients, so that the
convolution sum inside only references the *previous* stage `bseq g n`. -/
def bseq (g : ℕ → ℚ) : ℕ → ℕ → ℚ
  | 0, m => if m = 0 then 1 else 0
  | n + 1, m =>
      if m ≤ n then bseq g n m
      else (g (n + 1) - ∑ i ∈ Finset.range n,
              bseq g n (i + 1) * bseq g n (n - i)) / 2

/-- The rational square-root sequence: `sqrtRat g 0 = 1` and
`sqrtRat g (n+1) = (g(n+1) - mid (sqrtRat g)(n+1)) / 2` (so that the
convolution `conv (sqrtRat g) = g`). -/
def sqrtRat (g : ℕ → ℚ) (k : ℕ) : ℚ := bseq g k k

lemma bseq_succ_of_le (g : ℕ → ℚ) {n m : ℕ} (h : m ≤ n) :
    bseq g (n + 1) m = bseq g n m := by
  simp [bseq, h]

lemma bseq_succ_gt (g : ℕ → ℚ) {n m : ℕ} (h : ¬ m ≤ n) :
    bseq g (n + 1) m = (g (n + 1) - ∑ i ∈ Finset.range n,
        bseq g n (i + 1) * bseq g n (n - i)) / 2 := by
  simp [bseq, h]

lemma bseq_consistent (g : ℕ → ℚ) : ∀ {n m : ℕ}, m ≤ n → bseq g n m = bseq g m m
  | 0, m, hm => by
      have : m = 0 := by omega
      subst m
      rfl
  | n + 1, m, hm => by
      by_cases hmn : m ≤ n
      · rw [bseq_succ_of_le g hmn]
        exact bseq_consistent g hmn
      · have hm' : m = n + 1 := by omega
        subst m
        rfl

lemma sqrtRat_zero (g : ℕ → ℚ) : sqrtRat g 0 = 1 := by
  simp [sqrtRat, bseq]

lemma sqrtRat_succ (g : ℕ → ℚ) (n : ℕ) :
    sqrtRat g (n + 1) = (g (n + 1) - mid (sqrtRat g) (n + 1)) / 2 := by
  let S : ℚ := ∑ i ∈ Finset.range n, bseq g n (i + 1) * bseq g n (n - i)
  have hmid : mid (sqrtRat g) (n + 1) = S := by
    unfold mid S
    have hrange : Finset.range ((n + 1) - 1) = Finset.range n := by
      congr 1
    rw [hrange]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i < n := Finset.mem_range.mp hi
    have hidx : n + 1 - 1 - i = n - i := by omega
    simp only [sqrtRat]
    rw [hidx]
    rw [← bseq_consistent g (by omega : i + 1 ≤ n)]
    rw [← bseq_consistent g (by omega : n - i ≤ n)]
  calc
    sqrtRat g (n + 1) = (g (n + 1) - S) / 2 := by
      rw [show sqrtRat g (n + 1) = bseq g (n + 1) (n + 1) by rfl]
      rw [bseq_succ_gt g (n := n) (m := n + 1) (by omega)]
    _ = (g (n + 1) - mid (sqrtRat g) (n + 1)) / 2 := by
      rw [hmid]

/-- `sqrtRat g` squares to `g` in the convolution sense, provided `g 0 = 1`. -/
lemma conv_sqrtRat (g : ℕ → ℚ) (hg0 : g 0 = 1) : ∀ k : ℕ, conv (sqrtRat g) k = g k := by
  intro k
  induction k with
  | zero =>
      simp [conv, sqrtRat_zero, hg0]
  | succ k ih =>
      rw [split_conv (sqrtRat g) (sqrtRat_zero g) (by omega : 0 < k + 1)]
      rw [sqrtRat_succ g k]
      field_simp
      ring

/-- The "squarerad" integrality theorem for two integer polynomials `R₂,R₄`
with `R₂(0) = R₄(0) = 1` and `R₄ ≡ R₂ (mod 4)` coefficientwise: the formal
square root of `R₂·R₄` with constant term `1` has integer coefficients. -/
theorem sqrt_integral_poly (R₂ R₄ : ℤ[X])
    (hu0 : R₂.coeff 0 = 1) (hw0 : R₄.coeff 0 = 1)
    (hrev : ∀ i : ℕ, (4 : ℤ) ∣ R₄.coeff i - R₂.coeff i) :
    ∃ a : ℕ → ℤ, a 0 = 1 ∧ ∀ k : ℕ,
      (∑ i ∈ Finset.range (k + 1), a i * a (k - i)) =
        ((R₂ * R₄ : ℤ[X]).coeff k) := by
  classical
  let G : ℤ[X] := R₂ * R₄
  let u : ℕ → ℤ := fun i => R₂.coeff i
  let g : ℕ → ℤ := fun k => G.coeff k
  have hu0' : u 0 = 1 := by simp [u, hu0]
  have hsqcoeff : ∀ k : ℕ, (R₂ * R₂).coeff k =
      ∑ i ∈ Finset.range (k + 1), u i * u (k - i) := by
    intro k
    rw [coeff_mul]
    simpa [u] using (Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => R₂.coeff i * R₂.coeff j) k)
  have hrev' : ∀ j : ℕ, (4 : ℤ) ∣ (R₄ - R₂).coeff j := by
    intro j
    rw [coeff_sub]
    exact hrev j
  have hdiv : ∀ k : ℕ, (4 : ℤ) ∣ G.coeff k - (R₂ * R₂).coeff k := by
    intro k
    have hcoef : G.coeff k - (R₂ * R₂).coeff k = (R₂ * (R₄ - R₂)).coeff k := by
      dsimp [G]
      rw [← coeff_sub]
      congr 1
      ring
    rw [hcoef]
    rw [coeff_mul]
    exact Finset.dvd_sum (fun x hx =>
      dvd_mul_of_dvd_right (hrev' x.2) (R₂.coeff x.1))
  let v : ℕ → ℤ := fun k => Classical.choose (hdiv k)
  have hv : ∀ k, G.coeff k - (R₂ * R₂).coeff k = (4 : ℤ) * v k := by
    intro k
    simp [v]
    exact Classical.choose_spec (hdiv k)
  have hconv : ∀ k, g k = (∑ i ∈ Finset.range (k + 1), u i * u (k - i)) + 4 * v k := by
    intro k
    have hmain : G.coeff k = (R₂ * R₂).coeff k + 4 * v k := by
      linarith [hv k]
    rw [hsqcoeff k] at hmain
    simpa [g] using hmain
  have hg0 : g 0 = 1 := by
    dsimp [g, G]
    rw [coeff_mul]
    simp [hu0, hw0]
  let gr : ℕ → ℚ := fun k => (g k : ℚ)
  have hgr0 : gr 0 = 1 := by simp [gr, hg0]
  have hint := sqrt_integral g u v hu0' hconv (sqrtRat gr) (sqrtRat_zero gr)
      (conv_sqrtRat gr hgr0)
  let a : ℕ → ℤ := fun k => Classical.choose (hint k)
  have ha : ∀ k, (a k : ℚ) = sqrtRat gr k := by
    intro k
    simpa [a] using Classical.choose_spec (hint k)
  have ha0 : a 0 = 1 := by
    have hc : (a 0 : ℚ) = (1 : ℚ) := by
      rw [ha 0]
      exact sqrtRat_zero gr
    exact_mod_cast hc
  refine ⟨a, ha0, ?_⟩
  intro k
  have hQ : ((∑ i ∈ Finset.range (k + 1), a i * a (k - i) : ℤ) : ℚ) =
      (((R₂ * R₄ : ℤ[X]).coeff k : ℤ) : ℚ) := by
    have h1 : ((∑ i ∈ Finset.range (k + 1), a i * a (k - i) : ℤ) : ℚ)
        = ∑ i ∈ Finset.range (k + 1), ((a i : ℤ) : ℚ) * ((a (k - i) : ℤ) : ℚ) := by
      rw [Int.cast_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Int.cast_mul]
    have h2 : (∑ i ∈ Finset.range (k + 1), ((a i : ℤ) : ℚ) * ((a (k - i) : ℤ) : ℚ))
        = ∑ i ∈ Finset.range (k + 1), sqrtRat gr i * sqrtRat gr (k - i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [ha i, ha (k - i)]
    have h3 : (∑ i ∈ Finset.range (k + 1), sqrtRat gr i * sqrtRat gr (k - i)) = (g k : ℚ) := by
      simpa [conv, gr] using conv_sqrtRat gr hgr0 k
    have h4 : (g k : ℚ) = (((R₂ * R₄ : ℤ[X]).coeff k : ℤ) : ℚ) := by
      simp [g, G]
    exact h1.trans (h2.trans (h3.trans h4))
  exact_mod_cast hQ

/-- Constant coefficient of the reflected square polynomial: since `pow2 P` is
monic of degree `P.natDegree`, reflection sends the leading coefficient to the
constant coefficient, which is 1. -/
lemma reflect_pow2_coeff_zero (P : ℤ[X]) (hP : P.Monic) :
    (((pow2 P).reflect P.natDegree).coeff 0) = 1 := by
  rw [coeff_reflect]
  have hdeg : (pow2 P).natDegree = P.natDegree := pow2_natDegree P hP
  have hm := (pow2_monic P hP).coeff_natDegree
  simpa [hdeg] using hm

/-- Same for the fourth-power polynomial. -/
lemma reflect_pow4_coeff_zero (P : ℤ[X]) (hP : P.Monic) :
    (((pow4 P).reflect P.natDegree).coeff 0) = 1 := by
  rw [coeff_reflect]
  have hmonic : (pow4 P).Monic := pow2_monic (pow2 P) (pow2_monic P hP)
  have hdeg : (pow4 P).natDegree = P.natDegree := by
    change (pow2 (pow2 P)).natDegree = P.natDegree
    rw [pow2_natDegree (pow2 P) (pow2_monic P hP)]
    exact pow2_natDegree P hP
  simpa [hdeg] using hmonic.coeff_natDegree

/-- Reflection preserves the mod-4 congruence `pow4 P ≡ pow2 P`. -/
lemma reflect_pow4_sub_pow2_mod4 (P : ℤ[X]) (hP : P.Monic) (i : ℕ) :
    (4 : ℤ) ∣ (((pow4 P).reflect P.natDegree).coeff i -
      ((pow2 P).reflect P.natDegree).coeff i) := by
  simpa [coeff_reflect] using pow4_sub_pow2_mod4 P hP (revAt P.natDegree i)

/-- Integer-coefficient formal square root of the reversed power product:
`R₂(X) := reflect d (pow2 P)`, `R₄(X) := reflect d (pow4 P)`, `G := R₂·R₄`:
there is `a : ℕ → ℤ`, `a 0 = 1`, with `Σ_{i≤k} a i · a (k-i) = G.coeff k`. -/
theorem powRev_sqrt_integral (P : ℤ[X]) (hP : P.Monic) :
    ∃ a : ℕ → ℤ,
      a 0 = 1 ∧
        ∀ k : ℕ,
          (∑ i ∈ Finset.range (k + 1), a i * a (k - i)) =
            ((((pow2 P).reflect P.natDegree) * ((pow4 P).reflect P.natDegree)) :
              ℤ[X]).coeff k := by
  have hr2 : ((pow2 P).reflect P.natDegree).coeff 0 = 1 := reflect_pow2_coeff_zero P hP
  have hr4 : ((pow4 P).reflect P.natDegree).coeff 0 = 1 := reflect_pow4_coeff_zero P hP
  have hrev : ∀ i : ℕ, (4 : ℤ) ∣ ((pow4 P).reflect P.natDegree).coeff i -
      ((pow2 P).reflect P.natDegree).coeff i := reflect_pow4_sub_pow2_mod4 P hP
  simpa using (sqrt_integral_poly ((pow2 P).reflect P.natDegree)
    ((pow4 P).reflect P.natDegree) hr2 hr4 hrev)

end Submission.PowRev

end
