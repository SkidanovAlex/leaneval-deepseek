import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.WedgeDefs
import Submission.Work.HP.VW.multinomial_veronese
import Submission.Work.HP.tau_basic
import Submission.Work.HP.EE.WedgeAux
import Submission.Work.HP.EE.gram_double_sum
import Submission.Work.HP.EE.pow_sub_pow_ge

set_option autoImplicit false

noncomputable section

open Finset

open Work.HP (rNorm dotR veronese Mon monWeight wedgeR eNorm toR wedgeNorm veroneseR)

namespace Work.HP.EE

/-! ## Elementary facts about `wedgeR` -/

/-- The real Veronese map agrees with the general one. -/
lemma veroneseR_eq_veronese (d n : ℕ) (u : Fin (n + 1) → ℝ) :
    veroneseR d n u = veronese d n u := rfl

/-- `wedgeR` is nonnegative. -/
lemma wedgeR_nonneg {ι : Type*} [Fintype ι] (v w : ι → ℝ) : 0 ≤ wedgeR v w :=
  Real.sqrt_nonneg _

/-- Cauchy--Schwarz for `dotR` in squared form. -/
lemma dotR_sq_le {ι : Type*} [Fintype ι] (v w : ι → ℝ) :
    (dotR v w) ^ 2 ≤ rNorm v ^ 2 * rNorm w ^ 2 := by
  have h := Work.HP.abs_dotR_le v w
  have h2 : (dotR v w) ^ 2 ≤ (rNorm v * rNorm w) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  nlinarith [h2]

/-- `wedgeR` squared is the Gram determinant. -/
lemma wedgeR_sq {ι : Type*} [Fintype ι] (v w : ι → ℝ) :
    wedgeR v w ^ 2 = rNorm v ^ 2 * rNorm w ^ 2 - (dotR v w) ^ 2 := by
  have h3 : 0 ≤ rNorm v ^ 2 * rNorm w ^ 2 - (dotR v w) ^ 2 := by
    have h := dotR_sq_le v w; linarith
  show (Real.sqrt (rNorm v ^ 2 * rNorm w ^ 2 - (dotR v w) ^ 2)) ^ 2
      = rNorm v ^ 2 * rNorm w ^ 2 - (dotR v w) ^ 2
  exact Real.sq_sqrt h3

/-- `(x^m)^2 (y^m)^2 = (x²y²)^m`. -/
lemma sq_mul_sq (x y : ℝ) (m : ℕ) : (x ^ m) ^ 2 * (y ^ m) ^ 2 = (x ^ 2 * y ^ 2) ^ m := by
  rw [mul_pow (x ^ 2) (y ^ 2) m]
  congr 1
  · rw [← pow_mul, ← pow_mul, mul_comm]
  · rw [← pow_mul, ← pow_mul, mul_comm]

/-! ## The weighted Gram comparison -/

/-- If the entries of the diagonal weight `w` are nonnegative and bounded by `W`, then the
weighted Gram determinant of `(a, b)` is at most `W²` times the unweighted one.

Proof: both determinants are, by Lagrange's identity (`gram_double_sum`), the sums of the
squared `2 × 2` minors `(aᵢbⱼ - aⱼbᵢ)`, and the weighted sums are obtained from the unweighted
ones by multiplying the term `(i,j)` with `√(wᵢ)√(wⱼ)`, hence by at most `W` on each side. -/
lemma gram_weighted_le {ι : Type*} [Fintype ι] (w a b : ι → ℝ) (W : ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hwW : ∀ i, w i ≤ W) (hW0 : 0 ≤ W) :
    (∑ i, w i * a i ^ 2) * (∑ i, w i * b i ^ 2) - (∑ i, w i * a i * b i) ^ 2
      ≤ W ^ 2 * ((∑ i, a i ^ 2) * (∑ i, b i ^ 2) - (∑ i, a i * b i) ^ 2) := by
  have hw := gram_double_sum (fun i => Real.sqrt (w i) * a i) (fun i => Real.sqrt (w i) * b i)
  have hsq : ∀ i, Real.sqrt (w i) ^ 2 = w i := fun i => Real.sq_sqrt (hw0 i)
  have h1 : ∑ i, (Real.sqrt (w i) * a i) ^ 2 = ∑ i, w i * a i ^ 2 := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [mul_pow, hsq i]
  have h2 : ∑ i, (Real.sqrt (w i) * b i) ^ 2 = ∑ i, w i * b i ^ 2 := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [mul_pow, hsq i]
  have h3 : ∑ i, (Real.sqrt (w i) * a i) * (Real.sqrt (w i) * b i) = ∑ i, w i * a i * b i := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have : (Real.sqrt (w i) * a i) * (Real.sqrt (w i) * b i)
        = Real.sqrt (w i) ^ 2 * (a i * b i) := by ring
    rw [this, hsq i]
    ring
  rw [h1, h2, h3] at hw
  have hterm : ∑ i, ∑ j, ((Real.sqrt (w i) * a i) * (Real.sqrt (w j) * b j)
        - (Real.sqrt (w j) * a j) * (Real.sqrt (w i) * b i)) ^ 2
      ≤ W ^ 2 * ∑ i, ∑ j, (a i * b j - a j * b i) ^ 2 := by
    calc ∑ i, ∑ j, ((Real.sqrt (w i) * a i) * (Real.sqrt (w j) * b j)
          - (Real.sqrt (w j) * a j) * (Real.sqrt (w i) * b i)) ^ 2
        ≤ ∑ i, ∑ j, W ^ 2 * (a i * b j - a j * b i) ^ 2 := by
          refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ?_))
          have hfac : (Real.sqrt (w i) * a i) * (Real.sqrt (w j) * b j)
              - (Real.sqrt (w j) * a j) * (Real.sqrt (w i) * b i)
              = Real.sqrt (w i) * Real.sqrt (w j) * (a i * b j - a j * b i) := by ring
          rw [hfac, mul_pow, mul_pow, hsq i, hsq j]
          have hW2 : w i * w j ≤ W ^ 2 := by
            have hi := hwW i; have hj := hwW j
            nlinarith [hw0 i, hw0 j, hW0]
          exact mul_le_mul_of_nonneg_right hW2 (sq_nonneg _)
      _ = W ^ 2 * ∑ i, ∑ j, (a i * b j - a j * b i) ^ 2 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finset.mul_sum]
  have hw2 := gram_double_sum a b
  rw [hw2] at hterm
  linarith [hw, hterm]

/-! ## The Gram determinant of the Veronese embedding -/

/-- The Gram determinant `‖ν(u)‖²‖ν(v)‖² - ⟨ν(u),ν(v)⟩²` of the Veronese pair is bounded below
by `(n+1)^{-2d}` times `(‖u‖²‖v‖²)^{d-1} (‖u‖²‖v‖² - ⟨u,v⟩²)`.

This is the crux: multiply the two vectors `ν(u), ν(v)` by the square roots of the multinomial
coefficients and use the multinomial theorem (`weight_sum_sq`, `weight_sum_mul`), which turns the
sums over the monomials into powers of `‖u‖², ‖v‖²` and `⟨u,v⟩`. -/
lemma veronese_gram_bound (d n : ℕ) (hd : 1 ≤ d) (u v : Fin (n + 1) → ℝ) :
    ((((n : ℝ) + 1) ^ d)⁻¹) ^ 2 * ((rNorm u ^ 2 * rNorm v ^ 2) ^ (d - 1) *
        (rNorm u ^ 2 * rNorm v ^ 2 - (∑ i, u i * v i) ^ 2))
      ≤ rNorm (veronese d n u) ^ 2 * rNorm (veronese d n v) ^ 2
        - (∑ m : Mon d n, veronese d n u m * veronese d n v m) ^ 2 := by
  have hW0 : 0 < ((n : ℝ) + 1) ^ d := by positivity
  have hWne : ((n : ℝ) + 1) ^ d ≠ 0 := ne_of_gt hW0
  have hkey := gram_weighted_le (fun m : Mon d n => (monWeight d n m : ℝ))
      (veronese d n u) (veronese d n v) (((n : ℝ) + 1) ^ d)
      (fun m => Nat.cast_nonneg _) (fun m => weight_le d n m) (le_of_lt hW0)
  rw [weight_sum_sq d n u, weight_sum_sq d n v, weight_sum_mul d n u v] at hkey
  rw [← rNorm_sq u, ← rNorm_sq v] at hkey
  rw [← rNorm_sq (veronese d n u), ← rNorm_sq (veronese d n v)] at hkey
  have hcs : (∑ i, u i * v i) ^ 2 ≤ rNorm u ^ 2 * rNorm v ^ 2 := dotR_sq_le u v
  have hpow := pow_sub_pow_ge d hd (sq_nonneg (∑ i, u i * v i)) hcs
  have h1 : (rNorm u ^ 2) ^ d * (rNorm v ^ 2) ^ d = (rNorm u ^ 2 * rNorm v ^ 2) ^ d := by
    rw [mul_pow]
  have h2 : ((∑ i, u i * v i) ^ d) ^ 2 = ((∑ i, u i * v i) ^ 2) ^ d := by
    rw [← pow_mul, ← pow_mul, mul_comm]
  rw [h1, h2] at hkey
  have hstep : (rNorm u ^ 2 * rNorm v ^ 2 - (∑ i, u i * v i) ^ 2)
        * (rNorm u ^ 2 * rNorm v ^ 2) ^ (d - 1)
      ≤ (((n : ℝ) + 1) ^ d) ^ 2 * (rNorm (veronese d n u) ^ 2 * rNorm (veronese d n v) ^ 2
          - (∑ m : Mon d n, veronese d n u m * veronese d n v m) ^ 2) :=
    le_trans hpow hkey
  calc ((((n : ℝ) + 1) ^ d)⁻¹) ^ 2 * ((rNorm u ^ 2 * rNorm v ^ 2) ^ (d - 1) *
        (rNorm u ^ 2 * rNorm v ^ 2 - (∑ i, u i * v i) ^ 2))
      = (((n : ℝ) + 1) ^ d)⁻¹ ^ 2 * ((rNorm u ^ 2 * rNorm v ^ 2 - (∑ i, u i * v i) ^ 2)
          * (rNorm u ^ 2 * rNorm v ^ 2) ^ (d - 1)) := by ring
    _ ≤ (((n : ℝ) + 1) ^ d)⁻¹ ^ 2 * ((((n : ℝ) + 1) ^ d) ^ 2 *
          (rNorm (veronese d n u) ^ 2 * rNorm (veronese d n v) ^ 2
            - (∑ m : Mon d n, veronese d n u m * veronese d n v m) ^ 2)) :=
        mul_le_mul_of_nonneg_left hstep (sq_nonneg _)
    _ = (((n : ℝ) + 1) ^ d)⁻¹ ^ 2 * (((n : ℝ) + 1) ^ d) ^ 2
          * (rNorm (veronese d n u) ^ 2 * rNorm (veronese d n v) ^ 2
            - (∑ m : Mon d n, veronese d n u m * veronese d n v m) ^ 2) := by ring
    _ = rNorm (veronese d n u) ^ 2 * rNorm (veronese d n v) ^ 2
          - (∑ m : Mon d n, veronese d n u m * veronese d n v m) ^ 2 := by
        rw [show (((n : ℝ) + 1) ^ d)⁻¹ ^ 2 * (((n : ℝ) + 1) ^ d) ^ 2 = 1 from by
          rw [← mul_pow, inv_mul_cancel₀ hWne, one_pow]]
        ring

/-- The real form of the angular estimate: the Veronese map of a real vector does not shrink
angles, quantitatively. -/
lemma wedgeR_veronese_le_real (d n : ℕ) (hd : 1 ≤ d) (u v : Fin (n + 1) → ℝ) :
    (((n : ℝ) + 1) ^ d)⁻¹ * rNorm u ^ (d - 1) * rNorm v ^ (d - 1) * wedgeR u v
      ≤ wedgeR (veronese d n u) (veronese d n v) := by
  have hW0 : 0 < ((n : ℝ) + 1) ^ d := by positivity
  have hg := veronese_gram_bound d n hd u v
  have hsu : wedgeR u v ^ 2 = rNorm u ^ 2 * rNorm v ^ 2 - (∑ i, u i * v i) ^ 2 := wedgeR_sq u v
  have hsv : wedgeR (veronese d n u) (veronese d n v) ^ 2
      = rNorm (veronese d n u) ^ 2 * rNorm (veronese d n v) ^ 2
        - (∑ m : Mon d n, veronese d n u m * veronese d n v m) ^ 2 := wedgeR_sq _ _
  have hsq : ((((n : ℝ) + 1) ^ d)⁻¹ * rNorm u ^ (d - 1) * rNorm v ^ (d - 1) * wedgeR u v) ^ 2
      ≤ (wedgeR (veronese d n u) (veronese d n v)) ^ 2 := by
    rw [mul_pow, mul_pow, mul_pow, hsu, hsv]
    have hrr : ((((n : ℝ) + 1) ^ d)⁻¹) ^ 2 * (rNorm u ^ (d - 1)) ^ 2 * (rNorm v ^ (d - 1)) ^ 2
          * (rNorm u ^ 2 * rNorm v ^ 2 - (∑ i, u i * v i) ^ 2)
        = ((((n : ℝ) + 1) ^ d)⁻¹) ^ 2
          * ((rNorm u ^ (d - 1)) ^ 2 * (rNorm v ^ (d - 1)) ^ 2
            * (rNorm u ^ 2 * rNorm v ^ 2 - (∑ i, u i * v i) ^ 2)) := by ring
    rw [hrr, sq_mul_sq]
    exact hg
  have hL0 : 0 ≤ (((n : ℝ) + 1) ^ d)⁻¹ * rNorm u ^ (d - 1) * rNorm v ^ (d - 1) * wedgeR u v := by
    have h1 : (0 : ℝ) ≤ (((n : ℝ) + 1) ^ d)⁻¹ := inv_nonneg.mpr (le_of_lt hW0)
    exact mul_nonneg (mul_nonneg (mul_nonneg h1 (pow_nonneg (rNorm_nonneg u) _))
      (pow_nonneg (rNorm_nonneg v) _)) (wedgeR_nonneg u v)
  have hR0 : 0 ≤ wedgeR (veronese d n u) (veronese d n v) := wedgeR_nonneg _ _
  rw [← Real.sqrt_sq hL0, ← Real.sqrt_sq hR0]
  exact Real.sqrt_le_sqrt hsq

/-- The Veronese embedding does not shrink the angle between two vectors, quantitatively:
there is `c > 0` (depending on `d, n`) with
`c · ‖x‖^{d-1} ‖y‖^{d-1} · wedgeNorm x y ≤ wedgeNorm (ν_{d,n}(x)) (ν_{d,n}(y))` for all integer
`x, y`.  Equivalently `sin ∠(ν x, ν y) ≥ c' · sin ∠(x,y)`.

This is the Cauchy--Schwarz step in the proof of the paper's "Lemma upper and lower bounds det"
(tex lines 1984–2056).

Implementation: write `a_m = ν(u)_m`, `b_m = ν(v)_m` for real `u, v` and let `M_m` be the
multinomial coefficient of the exponent `m`.  Lagrange's identity (`gram_double_sum`) shows that
the Gram determinant `‖νu‖²‖νv‖² - ⟨νu,νv⟩²` is the sum of the squared minors
`(a_m b_{m'} - a_{m'} b_m)`, and the weighted sums `∑_m M_m a_m² = ‖u‖^{2d}`,
`∑_m M_m a_m b_m = ⟨u,v⟩^d` (multinomial theorem, `weight_sum_sq`/`weight_sum_mul`) identify the
weighted Gram determinant with `(‖u‖²‖v‖²)^d - ⟨u,v⟩^{2d} ≥ (‖u‖²‖v‖²)^{d-1}(‖u‖²‖v‖² - ⟨u,v⟩²)`.
Since every multinomial coefficient of a degree-`d` exponent is at most `(n+1)^d`
(`weight_le`), `gram_weighted_le` compares the two sums and yields
`‖νu‖²‖νv‖² - ⟨νu,νv⟩² ≥ (n+1)^{-2d}(‖u‖²‖v‖²)^{d-1}(‖u‖²‖v‖² - ⟨u,v⟩²)`, i.e. the claim with
`c = (n+1)^{-d}` after taking square roots.  Linearly dependent `x, y` give `0 ≤ 0`. -/
theorem wedgeNorm_veronese (d n : ℕ) (hd : 2 ≤ d) :
    ∃ c : ℝ, 0 < c ∧ ∀ x y : Fin (n + 1) → ℤ,
      c * eNorm x ^ (d - 1) * eNorm y ^ (d - 1) * wedgeNorm x y
        ≤ wedgeNorm (veronese d n x) (veronese d n y) := by
  refine ⟨(((n : ℝ) + 1) ^ d)⁻¹, by positivity, ?_⟩
  intro x y
  have h := wedgeR_veronese_le_real d n (by omega) (toR x) (toR y)
  simpa only [eNorm_eq_rNorm_toR_W, wedgeNorm_eq_wedgeR, toR_veronese_R, veroneseR_eq_veronese] using h

end Work.HP.EE
