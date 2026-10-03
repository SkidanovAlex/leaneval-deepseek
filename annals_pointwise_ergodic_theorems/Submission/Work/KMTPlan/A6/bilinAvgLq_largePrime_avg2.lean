/-
Krause--Mirek--Tao, *Pointwise ergodic theorems for non-conventional bilinear polynomial
averages*, Annals 195 (2022), Section 10, equation `(avg-2)`.

The bilinear arithmetic average on `ℤ/Qℤ`,
`A(f,g)(x) = Q⁻¹ ∑_y f (x - y) g (x - P y)`,
satisfies `‖A(f,g)‖_{L^q} ≤ ‖f‖_{L²}‖g‖_{L²}` (constant `1`!) for every exponent
`2 < q < 2d/(d-1)`, every sufficiently large prime power `Q = p^j`, and all `f, g`.

The proof is the paper's: split off the means `f = a + f₀`, `g = b + g₀`, so that
`A(f,g) = ab + A(f,g₀)`, and Taylor-expand `|ab + A(f,g₀)|^q` around `ab` with the *signed*
first-order term `q‖ab‖^{q-2}Re(conj(ab)·A(f,g₀))`.  Averaging, the first-order term is bounded
by `‖ab‖·|𝔼 A(f,g₀)|` and `𝔼 A(f,g₀) = 𝔼 A(f₀,g₀)`, which the large-prime mean-zero gain
(`(eq:39)`, the `r = 1` case of `improv`) makes small; the quadratic terms are controlled by the
mean-zero `L^q` gain (`(eq:42)`).

Inputs used: the proved `MdlBileR1OfImprov` (`r = 1` estimate from `ImprovKMT`), the proved
`MdlIwMinorArc_of_meanZero_largePrime`, the proved `bileInterpIwClean` (interpolation, giving
`(eq:42)`), and the concentration estimate `Corollary1` of Appendix C (`(avg-1)`).
-/
import Mathlib
import Submission.Work.KMTPlan.A6.MdlIwMinorArc_of_meanZero_largePrime
import Submission.Work.KMTPlan.A6.BileGeneralRClean
import Submission.Work.KMTPlan.A6.BilinearAverageLqBasic

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6

open Work.Analysis.Concentration Filter
open scoped Topology

noncomputable section

/-! ## Elementary complex norm identities -/

/-- The squared modulus of a sum, with the inner product written as `Re(conj z * w)`. -/
lemma avg2_norm_add_sq (z w : ℂ) :
    ‖z + w‖ ^ 2 = ‖z‖ ^ 2 + 2 * (star z * w).re + ‖w‖ ^ 2 := by
  have hconj : (z * star w).re = (star z * w).re := by
    have h : star (z * star w) = star z * w := by rw [star_mul, star_star]; ring
    calc (z * star w).re = (star (z * star w)).re := (Complex.conj_re _).symm
      _ = (star z * w).re := by rw [h]
  calc ‖z + w‖ ^ 2 = Complex.normSq (z + w) := (Complex.normSq_eq_norm_sq (z + w)).symm
    _ = Complex.normSq z + Complex.normSq w + 2 * (z * star w).re := Complex.normSq_add z w
    _ = ‖z‖ ^ 2 + 2 * (star z * w).re + ‖w‖ ^ 2 := by
          rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, hconj.symm]
          ring

/-- Cauchy--Schwarz for `Re(conj z * w)`. -/
lemma avg2_re_conj_le (z w : ℂ) : |(star z * w).re| ≤ ‖z‖ * ‖w‖ := by
  have h1 : |(star z * w).re| ≤ ‖star z * w‖ := Complex.abs_re_le_norm _
  rwa [norm_mul, norm_star] at h1

/-- Conversion from an integer power to a real power (rpow). -/
lemma avg2_rpow_natCast (x : ℝ) (n : ℕ) : x ^ n = x ^ (n : ℝ) := (Real.rpow_natCast x n).symm

/-- `X ^ q = (X ^ 2) ^ (q / 2)` for `X ≥ 0` (with the integer power on the right). -/
lemma avg2_rpow_two (X : ℝ) (hX : 0 ≤ X) (q : ℝ) : X ^ q = (X ^ 2) ^ (q / 2) := by
  rw [avg2_rpow_natCast X 2, ← Real.rpow_mul hX ((2 : ℕ) : ℝ) (q / 2),
    show ((2 : ℕ) : ℝ) * (q / 2) = q by ring]

/-! ## Elementary real inequalities: a signed second-order Taylor bound -/

/-- `(1+s)^N ≤ 1 + N s + 2^N s²` for `0 ≤ s ≤ 1` and `N : ℕ`. -/
lemma avg2_one_add_pow_le (N : ℕ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (1 + s) ^ N ≤ 1 + (N : ℝ) * s + ((2 : ℝ) ^ N - (N : ℝ) - 1) * s ^ 2 := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    have hN1 : (N : ℝ) + 1 ≤ (2 : ℝ) ^ N := by
      have h := Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := N))
      exact_mod_cast h
    have hs2 : (0 : ℝ) ≤ s ^ 2 := sq_nonneg s
    have h3 : s ^ 3 ≤ s ^ 2 := by nlinarith [hs0, hs1, sq_nonneg s, sq_nonneg (s - 1)]
    have hCnn : (0 : ℝ) ≤ (2 : ℝ) ^ N - (N : ℝ) - 1 := by linarith
    have h4 : ((2 : ℝ) ^ N - (N : ℝ) - 1) * s ^ 3
        ≤ ((2 : ℝ) ^ N - (N : ℝ) - 1) * s ^ 2 := mul_le_mul_of_nonneg_left h3 hCnn
    have h2 : (2 : ℝ) ^ (N + 1) = 2 * (2 : ℝ) ^ N := by rw [pow_succ]; ring
    have hcast : (↑(N + 1) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
    calc (1 + s) ^ (N + 1) = (1 + s) ^ N * (1 + s) := by rw [pow_succ]
      _ ≤ (1 + (N : ℝ) * s + ((2 : ℝ) ^ N - (N : ℝ) - 1) * s ^ 2) * (1 + s) :=
            mul_le_mul_of_nonneg_right ih (by linarith)
      _ = 1 + ((N : ℝ) + 1) * s
            + (((2 : ℝ) ^ N - (N : ℝ) - 1) + (N : ℝ)) * s ^ 2
            + ((2 : ℝ) ^ N - (N : ℝ) - 1) * s ^ 3 := by ring
      _ ≤ 1 + ↑(N + 1) * s + ((2 : ℝ) ^ (N + 1) - ↑(N + 1) - 1) * s ^ 2 := by
            rw [hcast, h2]
            nlinarith [h4, hs2, hCnn]

/-- `(1-s)^N ≤ 1 - N s + N(N-1)/2 s²` for `0 ≤ s ≤ 1` and `N : ℕ`. -/
lemma avg2_one_sub_pow_le (N : ℕ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (1 - s) ^ N ≤ 1 - (N : ℝ) * s + ((N : ℝ)) ^ 2 * s ^ 2 := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    have hs2 : (0 : ℝ) ≤ s ^ 2 := sq_nonneg s
    have h4 : (0 : ℝ) ≤ ((N : ℝ)) ^ 2 * s ^ 3 := by positivity
    have hkey : ((N : ℝ)) ^ 2 + (N : ℝ) ≤ ((N : ℝ) + 1) ^ 2 := by
      have hsk : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
      nlinarith
    have hcast : (↑(N + 1) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
    calc (1 - s) ^ (N + 1) = (1 - s) ^ N * (1 - s) := by rw [pow_succ]
      _ ≤ (1 - (N : ℝ) * s + ((N : ℝ)) ^ 2 * s ^ 2) * (1 - s) :=
            mul_le_mul_of_nonneg_right ih (by linarith)
      _ = 1 - ((N : ℝ) + 1) * s + (((N : ℝ)) ^ 2 + (N : ℝ)) * s ^ 2
            - ((N : ℝ)) ^ 2 * s ^ 3 := by ring
      _ ≤ 1 - ↑(N + 1) * s + ((↑(N + 1)) ^ 2) * s ^ 2 := by
            rw [hcast]
            nlinarith [hkey, h4, hs2]

/-- `(1+s)^q ≤ 1 + q s + C s²` for `0 ≤ s ≤ 1`, `q ≥ 2`. -/
lemma avg2_one_add_rpow_le_unit {q : ℝ} (hq : 2 ≤ q) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (1 + s) ^ q
      ≤ 1 + q * s + ((2 : ℝ) ^ (Nat.floor q + 1) + q + 1 + ((Nat.floor q : ℝ)) ^ 2) * s ^ 2 := by
  set k : ℕ := Nat.floor q with hk
  have hkq : (k : ℝ) ≤ q := Nat.floor_le (by linarith)
  have hkq1 : q < (k : ℝ) + 1 := Nat.lt_floor_add_one q
  have hθ0 : 0 ≤ q - k := by linarith
  have hθ1 : q - k ≤ 1 := by linarith
  have hpos : (0 : ℝ) < 1 + s := by linarith
  have hsplit : (1 + s) ^ q = (1 + s) ^ k * (1 + s) ^ (q - k) := by
    rw [← Real.rpow_natCast (1 + s) k, ← Real.rpow_add hpos,
      show ((k : ℝ) + (q - k)) = q by ring]
  have hk' : (1 + s) ^ k ≤ 1 + (k : ℝ) * s + ((2 : ℝ) ^ k - (k : ℝ) - 1) * s ^ 2 :=
    avg2_one_add_pow_le k hs0 hs1
  have hfrac : (1 + s) ^ (q - k) ≤ 1 + (q - k) * s :=
    rpow_one_add_le_one_add_mul_self (s := s) (by linarith) hθ0 hθ1
  have hbnn : (0 : ℝ) ≤ 1 + (k : ℝ) * s + ((2 : ℝ) ^ k - (k : ℝ) - 1) * s ^ 2 :=
    le_trans (pow_nonneg (by linarith) k) hk'
  have hprod : (1 + (k : ℝ) * s + ((2 : ℝ) ^ k - (k : ℝ) - 1) * s ^ 2) * (1 + (q - k) * s)
      = 1 + q * s + (((2 : ℝ) ^ k - (k : ℝ) - 1) + (k : ℝ) * (q - k)) * s ^ 2
        + ((2 : ℝ) ^ k - (k : ℝ) - 1) * (q - k) * s ^ 3 := by ring
  have hkey : 1 + q * s + (((2 : ℝ) ^ k - (k : ℝ) - 1) + (k : ℝ) * (q - k)) * s ^ 2
        + ((2 : ℝ) ^ k - (k : ℝ) - 1) * (q - k) * s ^ 3
      ≤ 1 + q * s + ((2 : ℝ) ^ (k + 1) + q + 1 + ((k : ℝ)) ^ 2) * s ^ 2 := by
    have hs3 : s ^ 3 ≤ s ^ 2 := by nlinarith [hs0, hs1, sq_nonneg s, sq_nonneg (s - 1)]
    have hs2 : (0 : ℝ) ≤ s ^ 2 := sq_nonneg s
    have hbk : (0 : ℝ) ≤ (2 : ℝ) ^ k := by positivity
    have hCnn : (0 : ℝ) ≤ (2 : ℝ) ^ k - (k : ℝ) - 1 := by
      have h1 : (k : ℝ) + 1 ≤ (2 : ℝ) ^ k := by
        have h := Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := k))
        exact_mod_cast h
      linarith
    have hAk : (0 : ℝ) ≤ ((2 : ℝ) ^ k - (k : ℝ) - 1) * (q - k) := mul_nonneg hCnn hθ0
    have hA : ((2 : ℝ) ^ k - (k : ℝ) - 1) * (q - k) * s ^ 3
        ≤ ((2 : ℝ) ^ k - (k : ℝ) - 1) * (q - k) * s ^ 2 :=
      mul_le_mul_of_nonneg_left hs3 hAk
    have hB : (k : ℝ) * (q - k) ≤ q := by nlinarith [hkq, hθ0, hθ1]
    have hC : ((2 : ℝ) ^ k - (k : ℝ) - 1) * (q - k) ≤ (2 : ℝ) ^ k := by
      nlinarith [hCnn, hθ0, hθ1, hbk]
    have h2 : (2 : ℝ) ^ (k + 1) = 2 * (2 : ℝ) ^ k := by rw [pow_succ]; ring
    nlinarith [hA, hB, hC, hs2, hbk, h2, hCnn, sq_nonneg (k : ℝ)]
  calc (1 + s) ^ q = (1 + s) ^ k * (1 + s) ^ (q - k) := hsplit
    _ ≤ (1 + (k : ℝ) * s + ((2 : ℝ) ^ k - (k : ℝ) - 1) * s ^ 2) * (1 + (q - k) * s) :=
          mul_le_mul hk' hfrac (Real.rpow_nonneg hpos.le _) hbnn
    _ = 1 + q * s + (((2 : ℝ) ^ k - (k : ℝ) - 1) + (k : ℝ) * (q - k)) * s ^ 2
          + ((2 : ℝ) ^ k - (k : ℝ) - 1) * (q - k) * s ^ 3 := hprod
    _ ≤ 1 + q * s + ((2 : ℝ) ^ (k + 1) + q + 1 + ((k : ℝ)) ^ 2) * s ^ 2 := hkey

/-- `(1-s)^q ≤ 1 - q s + C s²` for `0 ≤ s ≤ 1`, `q ≥ 2`. -/
lemma avg2_one_sub_rpow_le_unit {q : ℝ} (hq : 2 ≤ q) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (1 - s) ^ q
      ≤ 1 - q * s + ((2 : ℝ) ^ (Nat.floor q + 1) + q + 1 + ((Nat.floor q : ℝ)) ^ 2) * s ^ 2 := by
  set k : ℕ := Nat.floor q with hk
  have hkq : (k : ℝ) ≤ q := Nat.floor_le (by linarith)
  have hkq1 : q < (k : ℝ) + 1 := Nat.lt_floor_add_one q
  have hθ0 : 0 ≤ q - k := by linarith
  have hθ1 : q - k ≤ 1 := by linarith
  have hnonneg : (0 : ℝ) ≤ 1 - s := by linarith
  have hsum : ((k : ℝ) + (q - k)) ≠ 0 := by
    have : (k : ℝ) + (q - k) = q := by ring
    rw [this]; linarith
  have hsplit : (1 - s) ^ q = (1 - s) ^ k * (1 - s) ^ (q - k) := by
    rw [← Real.rpow_natCast (1 - s) k, ← Real.rpow_add' hnonneg hsum,
      show ((k : ℝ) + (q - k)) = q by ring]
  have hk' : (1 - s) ^ k ≤ 1 - (k : ℝ) * s + ((k : ℝ)) ^ 2 * s ^ 2 :=
    avg2_one_sub_pow_le k hs0 hs1
  have hbnn : (0 : ℝ) ≤ 1 - (k : ℝ) * s + ((k : ℝ)) ^ 2 * s ^ 2 :=
    le_trans (pow_nonneg hnonneg k) hk'
  have hfrac : (1 - s) ^ (q - k) ≤ 1 - (q - k) * s := by
    have h := rpow_one_add_le_one_add_mul_self (s := -s) (by linarith) hθ0 hθ1
    rw [show (1 : ℝ) + -s = 1 - s by ring, show (q - k) * (-s) = -((q - k) * s) by ring] at h
    linarith
  have hprod : (1 - (k : ℝ) * s + ((k : ℝ)) ^ 2 * s ^ 2) * (1 - (q - k) * s)
      = 1 - q * s + (((k : ℝ)) ^ 2 + (k : ℝ) * (q - k)) * s ^ 2
        - ((k : ℝ)) ^ 2 * (q - k) * s ^ 3 := by ring
  have hkey : 1 - q * s + (((k : ℝ)) ^ 2 + (k : ℝ) * (q - k)) * s ^ 2
        - ((k : ℝ)) ^ 2 * (q - k) * s ^ 3
      ≤ 1 - q * s + ((2 : ℝ) ^ (k + 1) + q + 1 + ((k : ℝ)) ^ 2) * s ^ 2 := by
    have hs2 : (0 : ℝ) ≤ s ^ 2 := sq_nonneg s
    have h3 : (0 : ℝ) ≤ ((k : ℝ)) ^ 2 * (q - k) * s ^ 3 := by positivity
    have hB : (k : ℝ) * (q - k) ≤ q := by nlinarith [hkq, hθ0, hθ1]
    have hBs : (k : ℝ) * (q - k) * s ^ 2 ≤ q * s ^ 2 := mul_le_mul_of_nonneg_right hB hs2
    have hksq : (0 : ℝ) ≤ ((k : ℝ)) ^ 2 * s ^ 2 := by positivity
    have hK : (0 : ℝ) ≤ (2 : ℝ) ^ (k + 1) := by positivity
    have hKs : (0 : ℝ) ≤ (2 : ℝ) ^ (k + 1) * s ^ 2 := mul_nonneg hK hs2
    have hh : (0 : ℝ) ≤ q * s ^ 2 := by positivity
    linarith [h3, hBs, hksq, hKs, hh]
  calc (1 - s) ^ q = (1 - s) ^ k * (1 - s) ^ (q - k) := hsplit
    _ ≤ (1 - (k : ℝ) * s + ((k : ℝ)) ^ 2 * s ^ 2) * (1 - (q - k) * s) :=
          mul_le_mul hk' hfrac (Real.rpow_nonneg hnonneg _) hbnn
    _ = 1 - q * s + (((k : ℝ)) ^ 2 + (k : ℝ) * (q - k)) * s ^ 2
          - ((k : ℝ)) ^ 2 * (q - k) * s ^ 3 := hprod
    _ ≤ 1 - q * s + ((2 : ℝ) ^ (k + 1) + q + 1 + ((k : ℝ)) ^ 2) * s ^ 2 := hkey

/-- `(1+s)^q ≤ 1 + q s + C (s² + s^q)` for all `s ≥ 0`, `q ≥ 2`. -/
lemma avg2_one_add_rpow_le (q : ℝ) (hq : 2 ≤ q) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ, 0 ≤ s → (1 + s) ^ q ≤ 1 + q * s + C * (s ^ 2 + s ^ q) := by
  refine ⟨max ((2 : ℝ) ^ (Nat.floor q + 1) + q + 1 + ((Nat.floor q : ℝ)) ^ 2) (2 ^ q),
    lt_max_of_lt_right (by positivity), fun s hs => ?_⟩
  by_cases hs1 : s ≤ 1
  · have h := avg2_one_add_rpow_le_unit hq hs hs1
    have hsq : (0 : ℝ) ≤ s ^ q := Real.rpow_nonneg hs q
    have hsq2 : (0 : ℝ) ≤ s ^ 2 := sq_nonneg s
    have hC : (0 : ℝ) ≤ 2 ^ q := Real.rpow_nonneg (by norm_num) q
    have hmul : ((2 : ℝ) ^ (Nat.floor q + 1) + q + 1 + ((Nat.floor q : ℝ)) ^ 2) * s ^ 2
        ≤ max ((2 : ℝ) ^ (Nat.floor q + 1) + q + 1 + ((Nat.floor q : ℝ)) ^ 2) (2 ^ q)
            * (s ^ 2 + s ^ q) := by
      have h1 : ((2 : ℝ) ^ (Nat.floor q + 1) + q + 1 + ((Nat.floor q : ℝ)) ^ 2) * s ^ 2
          ≤ max ((2 : ℝ) ^ (Nat.floor q + 1) + q + 1 + ((Nat.floor q : ℝ)) ^ 2) (2 ^ q)
              * s ^ 2 :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hsq2
      have h2 : max ((2 : ℝ) ^ (Nat.floor q + 1) + q + 1 + ((Nat.floor q : ℝ)) ^ 2) (2 ^ q) * s ^ 2
          ≤ max ((2 : ℝ) ^ (Nat.floor q + 1) + q + 1 + ((Nat.floor q : ℝ)) ^ 2) (2 ^ q)
              * (s ^ 2 + s ^ q) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hsq) (by positivity)
      exact h1.trans h2
    linarith [h, hmul]
  · have h1 : (1 + s) ^ q ≤ (2 * s) ^ q :=
      Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)
    have h2 : (2 * s) ^ q = 2 ^ q * s ^ q := Real.mul_rpow (by norm_num) hs
    have h3 : (0 : ℝ) ≤ s ^ q := Real.rpow_nonneg hs q
    have h4 : (0 : ℝ) ≤ s ^ 2 := sq_nonneg s
    have h5 : (0 : ℝ) ≤ q * s := by positivity
    have h7 : (0 : ℝ) ≤ 2 ^ q := Real.rpow_nonneg (by norm_num) q
    have h8 : 2 ^ q * s ^ q ≤ 2 ^ q * (s ^ 2 + s ^ q) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_left h4) h7
    have h9 : (2 : ℝ) ^ q * (s ^ 2 + s ^ q)
        ≤ max ((2 : ℝ) ^ (Nat.floor q + 1) + q + 1 + ((Nat.floor q : ℝ)) ^ 2) (2 ^ q)
            * (s ^ 2 + s ^ q) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
    linarith [h1, h2, h8, h9, h3, h4, h5]

/-- `|1-s|^q ≤ 1 - q s + C (s² + s^q)` for all `s ≥ 0`, `q ≥ 2`. -/
lemma avg2_one_sub_abs_rpow_le (q : ℝ) (hq : 2 ≤ q) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ, 0 ≤ s → |1 - s| ^ q ≤ 1 - q * s + C * (s ^ 2 + s ^ q) := by
  refine ⟨max (max ((2 : ℝ) ^ (Nat.floor q + 1) + q + 1 + ((Nat.floor q : ℝ)) ^ 2) (q ^ 2 + 1))
      (2 ^ q), ?_, fun s hs => ?_⟩
  · exact lt_max_of_lt_left (lt_max_of_lt_left (by positivity))
  by_cases hs1 : s ≤ 1
  · have habs : |1 - s| = 1 - s := abs_of_nonneg (by linarith)
    rw [habs]
    have h := avg2_one_sub_rpow_le_unit hq hs hs1
    have hsq : (0 : ℝ) ≤ s ^ q := Real.rpow_nonneg hs q
    have hsq2 : (0 : ℝ) ≤ s ^ 2 := sq_nonneg s
    have hle : (2 : ℝ) ^ (Nat.floor q + 1) + q + 1 + ((Nat.floor q : ℝ)) ^ 2
        ≤ max (max ((2 : ℝ) ^ (Nat.floor q + 1) + q + 1 + ((Nat.floor q : ℝ)) ^ 2) (q ^ 2 + 1))
            (2 ^ q) := le_trans (le_max_left _ _) (le_max_left _ _)
    have hmul : ((2 : ℝ) ^ (Nat.floor q + 1) + q + 1 + ((Nat.floor q : ℝ)) ^ 2) * s ^ 2
        ≤ max (max ((2 : ℝ) ^ (Nat.floor q + 1) + q + 1 + ((Nat.floor q : ℝ)) ^ 2) (q ^ 2 + 1))
            (2 ^ q) * (s ^ 2 + s ^ q) := by
      have h1 : ((2 : ℝ) ^ (Nat.floor q + 1) + q + 1 + ((Nat.floor q : ℝ)) ^ 2) * s ^ 2
          ≤ max (max ((2 : ℝ) ^ (Nat.floor q + 1) + q + 1 + ((Nat.floor q : ℝ)) ^ 2) (q ^ 2 + 1))
              (2 ^ q) * s ^ 2 :=
        mul_le_mul_of_nonneg_right hle hsq2
      have h2 : max (max ((2 : ℝ) ^ (Nat.floor q + 1) + q + 1 + ((Nat.floor q : ℝ)) ^ 2)
              (q ^ 2 + 1)) (2 ^ q) * s ^ 2
          ≤ max (max ((2 : ℝ) ^ (Nat.floor q + 1) + q + 1 + ((Nat.floor q : ℝ)) ^ 2) (q ^ 2 + 1))
              (2 ^ q) * (s ^ 2 + s ^ q) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hsq) (by positivity)
      exact h1.trans h2
    linarith [h, hmul]
  · have hsge : 1 ≤ s := le_of_lt (not_le.mp hs1)
    have habs : |1 - s| = s - 1 := by
      rw [abs_of_nonpos (sub_nonpos.mpr hsge)]
      ring
    rw [habs]
    set C : ℝ := max (max ((2 : ℝ) ^ (Nat.floor q + 1) + q + 1 + ((Nat.floor q : ℝ)) ^ 2)
      (q ^ 2 + 1)) (2 ^ q) with hC
    have hCge : q ^ 2 + 1 ≤ C := le_trans (le_max_right _ _) (le_max_left _ _)
    have hCpos : 0 < C := lt_of_lt_of_le (by positivity) hCge
    have h1 : (s - 1) ^ q ≤ s ^ q :=
      Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)
    have hsq : (0 : ℝ) ≤ s ^ q := Real.rpow_nonneg hs q
    have hquad : (0 : ℝ) ≤ 1 - q * s + C * s ^ 2 := by
      have hCq : q ^ 2 ≤ 4 * C := by nlinarith [hCge]
      have hnn : (0 : ℝ) ≤ (2 * C * s - q) ^ 2 + (4 * C - q ^ 2) := by
        nlinarith [sq_nonneg (2 * C * s - q), hCq]
      have hfact : (2 * C * s - q) ^ 2 + (4 * C - q ^ 2)
          = 4 * C * (C * s ^ 2 - q * s + 1) := by ring
      rw [hfact] at hnn
      have h7 := (mul_nonneg_iff_of_pos_left (by positivity : (0 : ℝ) < 4 * C)).mp hnn
      linarith
    have hC1 : 1 ≤ C := by
      have h7 : (0 : ℝ) ≤ q ^ 2 := sq_nonneg q
      linarith [hCge]
    have h2 : 0 ≤ (C - 1) * s ^ q := mul_nonneg (by linarith) hsq
    have hquad' : 0 ≤ 1 - q * s + C * s ^ 2 + (C - 1) * s ^ q := by linarith [hquad, h2]
    have h3' : 1 - q * s + C * (s ^ 2 + s ^ q) - s ^ q
        = 1 - q * s + C * s ^ 2 + (C - 1) * s ^ q := by ring
    have hquad'' : 0 ≤ 1 - q * s + C * (s ^ 2 + s ^ q) - s ^ q := by rw [h3']; exact hquad'
    linarith [h1, hquad'']

/-- **The scalar inequality behind the signed Taylor expansion.** -/
lemma avg2_scalar (q : ℝ) (hq : 2 ≤ q) :
    ∃ C : ℝ, 0 < C ∧ ∀ s c : ℝ, 0 ≤ s → -1 ≤ c → c ≤ 1 →
      (1 + 2 * s * c + s ^ 2) ^ (q / 2) ≤ 1 + q * s * c + C * (s ^ 2 + s ^ q) := by
  obtain ⟨C1, hC1, h1⟩ := avg2_one_add_rpow_le q hq
  obtain ⟨C2, hC2, h2⟩ := avg2_one_sub_abs_rpow_le q hq
  refine ⟨max C1 C2, lt_max_of_lt_left hC1, fun s c hs hc1 hc2 => ?_⟩
  have hq2 : (1 : ℝ) ≤ q / 2 := by linarith
  have hB : 0 ≤ 1 + 2 * s * c + s ^ 2 := by nlinarith [sq_nonneg (s + c), hc1, hc2]
  set t : ℝ := (1 + c) / 2 with htdef
  have ht0 : 0 ≤ t := by rw [htdef]; linarith
  have ht1 : t ≤ 1 := by rw [htdef]; linarith
  have htne : t + (1 - t) = 1 := by ring
  have hdecomp : 1 + 2 * s * c + s ^ 2 = t * (1 + s) ^ 2 + (1 - t) * (1 - s) ^ 2 := by
    rw [htdef]; ring
  have hconv : (t * (1 + s) ^ 2 + (1 - t) * (1 - s) ^ 2) ^ (q / 2)
      ≤ t * ((1 + s) ^ 2) ^ (q / 2) + (1 - t) * ((1 - s) ^ 2) ^ (q / 2) :=
    (convexOn_rpow hq2).2 (show (0 : ℝ) ≤ (1 + s) ^ 2 from by positivity)
      (show (0 : ℝ) ≤ (1 - s) ^ 2 from by positivity) ht0 (by linarith) htne
  have hstep : (1 + 2 * s * c + s ^ 2) ^ (q / 2) ≤ t * (1 + s) ^ q + (1 - t) * |1 - s| ^ q := by
    rw [hdecomp]
    refine hconv.trans (le_of_eq ?_)
    have h1 : ((1 + s) ^ 2) ^ (q / 2) = (1 + s) ^ q :=
      (avg2_rpow_two (1 + s) (by linarith) q).symm
    have h2 : ((1 - s) ^ 2) ^ (q / 2) = |1 - s| ^ q := by
      rw [← sq_abs (1 - s), avg2_rpow_two |1 - s| (abs_nonneg _) q]
    rw [h1, h2]
  calc (1 + 2 * s * c + s ^ 2) ^ (q / 2)
      ≤ t * (1 + s) ^ q + (1 - t) * |1 - s| ^ q := hstep
    _ ≤ t * (1 + q * s + C1 * (s ^ 2 + s ^ q))
          + (1 - t) * (1 - q * s + C2 * (s ^ 2 + s ^ q)) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left (h1 s hs) ht0
        · exact mul_le_mul_of_nonneg_left (h2 s hs) (by linarith)
    _ = 1 + q * s * c + (t * C1 + (1 - t) * C2) * (s ^ 2 + s ^ q) := by
        rw [htdef]; ring
    _ ≤ 1 + q * s * c + max C1 C2 * (s ^ 2 + s ^ q) := by
        have hs2 : (0 : ℝ) ≤ s ^ 2 + s ^ q :=
          add_nonneg (sq_nonneg s) (Real.rpow_nonneg hs q)
        have hcoef : t * C1 + (1 - t) * C2 ≤ max C1 C2 := by
          have hle1 : C1 ≤ max C1 C2 := le_max_left _ _
          have hle2 : C2 ≤ max C1 C2 := le_max_right _ _
          nlinarith [ht0, ht1, hle1, hle2]
        have hmul := mul_le_mul_of_nonneg_right hcoef hs2
        linarith

/-- **Signed Taylor bound**: the second-order Taylor expansion of `z ↦ ‖z‖^q` at `x`, with the
*first-order* term kept in the signed form `q‖x‖^{q-2}Re(conj x · y)`. -/
lemma avg2Taylor (q : ℝ) (hq : 2 ≤ q) :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : ℂ,
      ‖x + y‖ ^ q ≤ ‖x‖ ^ q + q * ‖x‖ ^ (q - 2) * (star x * y).re
        + C * (‖x‖ ^ (q - 2) * ‖y‖ ^ 2 + ‖y‖ ^ q) := by
  obtain ⟨C₀, hC₀, hsc⟩ := avg2_scalar q hq
  have hqpos : (0 : ℝ) < q := by linarith
  have hCm : 0 < max C₀ 1 := lt_max_of_lt_left hC₀
  refine ⟨max C₀ 1, hCm, fun x y => ?_⟩
  by_cases hx : x = 0
  · subst hx
    have hz : (star (0 : ℂ) * y).re = 0 := by simp
    simp only [zero_add, hz, norm_zero]
    rw [Real.zero_rpow (ne_of_gt hqpos), mul_zero, zero_add]
    by_cases h2 : q = 2
    · subst h2
      rw [sub_self, Real.rpow_zero, one_mul]
      have h3 := le_mul_of_one_le_left (by positivity : (0 : ℝ) ≤ ‖y‖ ^ 2) (le_max_right C₀ 1)
      have h4 : max C₀ 1 * ‖y‖ ^ 2 ≤ max C₀ 1 * (‖y‖ ^ 2 + ‖y‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (by linarith [sq_nonneg ‖y‖]) (by positivity)
      rw [Real.rpow_two]
      have hgoal : ‖y‖ ^ 2 ≤ 0 + max C₀ 1 * (‖y‖ ^ 2 + ‖y‖ ^ 2) := by
        rw [zero_add]
        exact le_trans h3 h4
      exact hgoal
    · have hq2' : 0 < q - 2 := by
        by_contra h
        exact h2 (le_antisymm (by linarith) hq)
      rw [Real.zero_rpow (ne_of_gt hq2'), zero_mul, zero_add]
      have h := le_mul_of_one_le_left (Real.rpow_nonneg (norm_nonneg y) q) (le_max_right C₀ 1)
      have h2 := mul_le_mul_of_nonneg_left
        (le_of_eq (by ring : ‖y‖ ^ q = 0 + ‖y‖ ^ q)) (by positivity : (0 : ℝ) ≤ max C₀ 1)
      linarith [h, h2]
  · by_cases hy : y = 0
    · subst hy
      have hz : (star x * (0 : ℂ)).re = 0 := by simp
      rw [add_zero, hz, norm_zero, Real.zero_rpow (ne_of_gt hqpos),
        zero_pow (by norm_num : 2 ≠ 0)]
      simp only [mul_zero, zero_mul, add_zero]
      exact le_refl _
    · push_neg at hx hy
      have hu : 0 < ‖x‖ := norm_pos_iff.mpr hx
      have hv : 0 < ‖y‖ := norm_pos_iff.mpr hy
      set u : ℝ := ‖x‖ with hudef
      set v : ℝ := ‖y‖ with hvdef
      set w : ℝ := (star x * y).re with hwdef
      have hCS : |w| ≤ u * v := by
        rw [hwdef, hudef, hvdef]
        exact avg2_re_conj_le x y
      have huv : 0 < u * v := mul_pos hu hv
      set c : ℝ := w / (u * v) with hcdef
      have hc1 : -1 ≤ c := by
        rw [hcdef, le_div_iff₀ huv]
        have h7 := neg_abs_le w
        nlinarith [hCS]
      have hc2 : c ≤ 1 := by
        rw [hcdef, div_le_iff₀ huv]
        have h7 := le_abs_self w
        nlinarith [hCS]
      set s : ℝ := v / u with hsdef
      have hs0 : 0 ≤ s := by rw [hsdef]; positivity
      have hkey : u ^ 2 + 2 * w + v ^ 2 = u ^ 2 * (1 + 2 * s * c + s ^ 2) := by
        rw [hsdef, hcdef, hwdef, hudef, hvdef]
        field_simp
      have hnorm : ‖x + y‖ ^ 2 = u ^ 2 + 2 * w + v ^ 2 := by
        rw [hudef, hvdef, hwdef]
        exact avg2_norm_add_sq x y
      have hB : 0 ≤ 1 + 2 * s * c + s ^ 2 := by nlinarith [sq_nonneg (s + c), hc1, hc2]
      have hsc' := hsc s c hs0 hc1 hc2
      have hL : ‖x + y‖ ^ q = u ^ q * (1 + 2 * s * c + s ^ 2) ^ (q / 2) := by
        rw [avg2_rpow_two ‖x + y‖ (norm_nonneg _) q, hnorm, hkey,
          Real.mul_rpow (by positivity) hB, avg2_rpow_two u (le_of_lt hu) q]
      have hdiv : u ^ q / u ^ 2 = u ^ (q - 2) := by
        rw [avg2_rpow_natCast u 2,
          show (q : ℝ) - 2 = q - ((2 : ℕ) : ℝ) by push_cast; ring]
        exact (Real.rpow_sub hu q ((2 : ℕ) : ℝ)).symm
      have hsc1 : s * c = w / u ^ 2 := by rw [hsdef, hcdef]; field_simp
      have hsc2 : s ^ 2 = v ^ 2 / u ^ 2 := by rw [hsdef]; field_simp
      have e1 : u ^ q * s * c = u ^ (q - 2) * w := by
        calc u ^ q * s * c = u ^ q * (s * c) := by ring
          _ = u ^ q * (w / u ^ 2) := by rw [hsc1]
          _ = (u ^ q / u ^ 2) * w := by ring
          _ = u ^ (q - 2) * w := by rw [hdiv]
      have e2 : u ^ q * s ^ 2 = u ^ (q - 2) * v ^ 2 := by
        calc u ^ q * s ^ 2 = u ^ q * (v ^ 2 / u ^ 2) := by rw [hsc2]
          _ = (u ^ q / u ^ 2) * v ^ 2 := by ring
          _ = u ^ (q - 2) * v ^ 2 := by rw [hdiv]
      have e3 : u ^ q * s ^ q = v ^ q := by
        rw [hsdef, ← Real.mul_rpow (le_of_lt hu) (by positivity : (0 : ℝ) ≤ v / u)]
        congr 1
        field_simp
      have hfin : u ^ q * (1 + q * s * c + C₀ * (s ^ 2 + s ^ q))
          = u ^ q + q * u ^ (q - 2) * w + C₀ * (u ^ (q - 2) * v ^ 2 + v ^ q) := by
        have h1' : u ^ q * (q * s * c) = q * (u ^ (q - 2) * w) := by
          rw [show u ^ q * (q * s * c) = q * (u ^ q * s * c) by ring, e1]
        have h4' : u ^ q * (C₀ * (s ^ 2 + s ^ q)) = C₀ * (u ^ (q - 2) * v ^ 2 + v ^ q) := by
          rw [show u ^ q * (C₀ * (s ^ 2 + s ^ q))
              = C₀ * (u ^ q * s ^ 2 + u ^ q * s ^ q) by ring, e2, e3]
        have h5' : u ^ q * 1 = u ^ q := mul_one _
        rw [mul_add, mul_add, h1', h4', h5']
        ring
      have hstep : u ^ q * (1 + 2 * s * c + s ^ 2) ^ (q / 2)
          ≤ u ^ q * (1 + q * s * c + C₀ * (s ^ 2 + s ^ q)) :=
        mul_le_mul_of_nonneg_left hsc' (Real.rpow_nonneg (le_of_lt hu) q)
      rw [hL]
      refine hstep.trans (hfin.le.trans ?_)
      rw [hudef, hvdef, hwdef]
      have hcc : C₀ * (u ^ (q - 2) * v ^ 2 + v ^ q)
          ≤ max C₀ 1 * (u ^ (q - 2) * v ^ 2 + v ^ q) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      linarith

end

noncomputable section

/-! ## The mean decomposition and its elementary properties -/

/-- The mean-free part of a function on `ℤ/Qℤ` has zero sum. -/
lemma avg2_sum_center (Q : ℕ) [NeZero Q] (f : ZMod Q → ℂ) :
    ∑ x : ZMod Q, (f x - (Q : ℂ)⁻¹ * ∑ y : ZMod Q, f y) = 0 := by
  have hQ : (Q : ℂ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (NeZero.ne Q)
  have hc : (Q : ℂ) * ((Q : ℂ)⁻¹ * ∑ y : ZMod Q, f y) = ∑ y : ZMod Q, f y := by
    rw [← mul_assoc, mul_inv_cancel₀ hQ, one_mul]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, hc,
    sub_self]

/-- The normalized `L²` norm vanishes only for the zero function. -/
lemma avg2_eq_zero_of_LpNormZMod_two_mul_eq_zero (Q : ℕ) [NeZero Q] {f : ZMod Q → ℂ}
    (h : LpNormZMod Q 2 f = 0) : ∀ x, f x = 0 := by
  have h2 := Work.Analysis.Paraproduct.LpNormZMod_two_sq Q f
  rw [h] at h2
  have hsum : ∑ x : ZMod Q, ‖f x‖ ^ 2 = 0 := by
    have h0 : (Q : ℝ)⁻¹ * ∑ x : ZMod Q, ‖f x‖ ^ 2 = 0 := by rw [← h2]; ring
    exact (mul_eq_zero.mp h0).resolve_left (inv_ne_zero (by exact_mod_cast (NeZero.ne Q)))
  intro x
  have hx : ‖f x‖ ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by positivity)).mp hsum x (Finset.mem_univ x)
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hx)

/-- `‖(Q⁻¹ ∑_x u x)‖ ≤ ‖u‖_{L¹}`. -/
lemma avg2_norm_mean_le (Q : ℕ) [NeZero Q] (u : ZMod Q → ℂ) :
    ‖(Q : ℂ)⁻¹ * ∑ x : ZMod Q, u x‖ ≤ LpNormZMod Q 1 u := by
  rw [LpNormZMod_one_eq]
  calc ‖(Q : ℂ)⁻¹ * ∑ x : ZMod Q, u x‖ ≤ ‖(Q : ℂ)⁻¹‖ * ‖∑ x : ZMod Q, u x‖ :=
        norm_mul_le _ _
    _ ≤ ‖(Q : ℂ)⁻¹‖ * ∑ x : ZMod Q, ‖u x‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
    _ = (Q : ℝ)⁻¹ * ∑ x : ZMod Q, ‖u x‖ := by
        congr 1
        rw [norm_inv, Complex.norm_def, Complex.normSq_natCast,
          Real.sqrt_mul_self (by positivity)]

/-- `(Q⁻¹ ∑_x (z * u x).re) = Re(z · (Q⁻¹ ∑_x u x))`. -/
lemma avg2_sum_re (Q : ℕ) [NeZero Q] (z : ℂ) (u : ZMod Q → ℂ) :
    (Q : ℝ)⁻¹ * ∑ x : ZMod Q, (z * u x).re = (z * ((Q : ℂ)⁻¹ * ∑ x : ZMod Q, u x)).re := by
  have hcast : (((Q : ℝ)⁻¹ : ℝ) : ℂ) = (Q : ℂ)⁻¹ := by
    rw [Complex.ofReal_inv, Complex.ofReal_natCast]
  have h1 : (∑ x : ZMod Q, z * u x).re = ∑ x : ZMod Q, (z * u x).re :=
    Complex.re_sum Finset.univ (fun x : ZMod Q => z * u x)
  have h2 : (Q : ℝ)⁻¹ * (∑ x : ZMod Q, z * u x).re
      = ((((Q : ℝ)⁻¹ : ℝ) : ℂ) * (∑ x : ZMod Q, z * u x)).re := by
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [← h1, h2, hcast, ← Finset.mul_sum]
  congr 1
  ring

/-- **Pythagoras** for the mean decomposition: `‖f - 𝔼f‖₂² + ‖𝔼f‖² = ‖f‖₂²`. -/
lemma avg2_energy (Q : ℕ) [NeZero Q] (f : ZMod Q → ℂ) :
    (LpNormZMod Q 2 (fun x => f x - (Q : ℂ)⁻¹ * ∑ y : ZMod Q, f y)) ^ 2
      + ‖(Q : ℂ)⁻¹ * ∑ y : ZMod Q, f y‖ ^ 2
      = (LpNormZMod Q 2 f) ^ 2 := by
  set m : ℂ := (Q : ℂ)⁻¹ * ∑ y : ZMod Q, f y with hm
  have hQc : (Q : ℂ) ≠ 0 := by exact Nat.cast_ne_zero.mpr (NeZero.ne Q)
  have hsumf : ∑ y : ZMod Q, f y = (Q : ℂ) * m := by
    rw [hm]
    field_simp
  have hpt : ∀ x : ZMod Q, ‖f x - m‖ ^ 2 = ‖f x‖ ^ 2 + ‖m‖ ^ 2 - 2 * (star (f x) * m).re := by
    intro x
    have h := avg2_norm_add_sq (f x) (-m)
    have h1 : (star (f x) * (-m)).re = -((star (f x) * m).re) := by
      rw [mul_neg, Complex.neg_re]
    rw [show f x - m = f x + (-m) by ring, h, norm_neg, h1]
    ring
  have hmul : ∑ x : ZMod Q, star (f x) * m = (((Q : ℝ) * Complex.normSq m : ℝ) : ℂ) := by
    have h1 : ∑ x : ZMod Q, star (f x) * m = star (∑ x : ZMod Q, f x) * m := by
      rw [← Finset.sum_mul, ← star_sum]
    have h2 : star ((Q : ℂ) * m) = (Q : ℂ) * star m := by
      simp [star_mul, mul_comm]
    have h5 : m * star m = (((Complex.normSq m : ℝ)) : ℂ) := by
      rw [show m * star m = m * (starRingEnd ℂ) m from rfl, Complex.mul_conj]
    rw [h1, hsumf, h2, mul_assoc, mul_comm (star m) m, h5]
    push_cast
    ring
  have hreal : ∑ x : ZMod Q, (star (f x) * m).re = (Q : ℝ) * Complex.normSq m := by
    rw [← Complex.re_sum Finset.univ (fun x : ZMod Q => star (f x) * m), hmul,
      Complex.ofReal_re]
  have hm2 : ‖m‖ ^ 2 = Complex.normSq m := (Complex.normSq_eq_norm_sq m).symm
  have hsum3 : ∑ x : ZMod Q, ‖f x - m‖ ^ 2
      = (∑ x : ZMod Q, ‖f x‖ ^ 2) - (Q : ℝ) * Complex.normSq m := by
    have h1 : ∑ x : ZMod Q, ‖f x - m‖ ^ 2
        = ∑ x : ZMod Q, (‖f x‖ ^ 2 + ‖m‖ ^ 2 - 2 * (star (f x) * m).re) :=
      Finset.sum_congr rfl (fun x _ => hpt x)
    rw [h1, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      ZMod.card, nsmul_eq_mul]
    have h2 : ∑ x : ZMod Q, 2 * (star (f x) * m).re = 2 * ((Q : ℝ) * Complex.normSq m) := by
      rw [← Finset.mul_sum, hreal]
    rw [h2, hm2]
    ring
  rw [Work.Analysis.Paraproduct.LpNormZMod_two_sq, Work.Analysis.Paraproduct.LpNormZMod_two_sq,
    hsum3, hm2]
  have hQr : (Q : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne Q)
  field_simp
  ring_nf

/-- **The mean decomposition** of the arithmetic bilinear average. -/
lemma avg2_decomp (P : Polynomial ℤ) (Q : ℕ) [NeZero Q] (f g : ZMod Q → ℂ) (x : ZMod Q) :
    polyBilinearAverageZMod Polynomial.X P Q f g x
      = ((Q : ℂ)⁻¹ * ∑ y : ZMod Q, f y) * ((Q : ℂ)⁻¹ * ∑ y : ZMod Q, g y)
        + polyBilinearAverageZMod Polynomial.X P Q f
            (fun y => g y - (Q : ℂ)⁻¹ * ∑ z : ZMod Q, g z) x := by
  set c : ℂ := (Q : ℂ)⁻¹ * ∑ z : ZMod Q, g z with hc
  have hsumf : ∑ y : ZMod Q, f (x - y) = ∑ y : ZMod Q, f y := by
    rw [← Equiv.sum_comp (Equiv.subLeft x) (fun z : ZMod Q => f z)]
    exact Finset.sum_congr rfl (fun y _ => by rw [Equiv.subLeft_apply])
  have hsplit : (∑ y : ZMod Q, f (x - y) * g (x - polyEvalZMod P Q y))
      = (∑ y : ZMod Q, f (x - y) * (g (x - polyEvalZMod P Q y) - c))
        + (∑ y : ZMod Q, f (x - y)) * c := by
    rw [Finset.sum_congr rfl (fun y _ => by ring : ∀ y ∈ Finset.univ,
      f (x - y) * g (x - polyEvalZMod P Q y)
        = f (x - y) * (g (x - polyEvalZMod P Q y) - c) + f (x - y) * c),
      Finset.sum_add_distrib, Finset.sum_mul]
  simp only [polyBilinearAverageZMod, polyEvalZMod_X]
  rw [hsplit, hsumf, hc]
  ring

/-- The mean of `A(f,g)` over the first variable only depends on the mean-free part of `f`. -/
lemma avg2_mean_eq (P : Polynomial ℤ) (Q : ℕ) [NeZero Q] (f g : ZMod Q → ℂ)
    (hg : ∑ y : ZMod Q, g y = 0) :
    ∑ x : ZMod Q, polyBilinearAverageZMod Polynomial.X P Q f g x
      = ∑ x : ZMod Q, polyBilinearAverageZMod Polynomial.X P Q
          (fun x => f x - (Q : ℂ)⁻¹ * ∑ y : ZMod Q, f y) g x := by
  set m : ℂ := (Q : ℂ)⁻¹ * ∑ y : ZMod Q, f y with hm
  have hpt : ∀ x : ZMod Q, polyBilinearAverageZMod Polynomial.X P Q f g x
      = polyBilinearAverageZMod Polynomial.X P Q (fun x => f x - m) g x
        + m * ((Q : ℂ)⁻¹ * ∑ y : ZMod Q, g (x - polyEvalZMod P Q y)) := by
    intro x
    simp only [polyBilinearAverageZMod, polyEvalZMod_X]
    have hexp : (∑ y : ZMod Q, (f (x - y) - m) * g (x - polyEvalZMod P Q y))
        = (∑ y : ZMod Q, f (x - y) * g (x - polyEvalZMod P Q y))
          - m * (∑ y : ZMod Q, g (x - polyEvalZMod P Q y)) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun y _ => by ring)
    rw [hexp]
    ring
  have hzero : ∑ x : ZMod Q, ((Q : ℂ)⁻¹ * ∑ y : ZMod Q, g (x - polyEvalZMod P Q y)) = 0 := by
    have hinner : ∀ y : ZMod Q, ∑ x : ZMod Q, g (x - polyEvalZMod P Q y)
        = ∑ z : ZMod Q, g z := by
      intro y
      have h := Equiv.sum_comp (Equiv.subRight (polyEvalZMod P Q y)) (fun z : ZMod Q => g z)
      simpa [Equiv.subRight_apply] using h
    have h1 : ∑ x : ZMod Q, (∑ y : ZMod Q, g (x - polyEvalZMod P Q y)) = 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_eq_zero
      intro y _
      rw [hinner y, hg]
    rw [← Finset.mul_sum, h1, mul_zero]
  calc ∑ x : ZMod Q, polyBilinearAverageZMod Polynomial.X P Q f g x
      = ∑ x : ZMod Q, (polyBilinearAverageZMod Polynomial.X P Q (fun x => f x - m) g x
          + m * ((Q : ℂ)⁻¹ * ∑ y : ZMod Q, g (x - polyEvalZMod P Q y))) :=
        Finset.sum_congr rfl (fun x _ => hpt x)
    _ = (∑ x : ZMod Q, polyBilinearAverageZMod Polynomial.X P Q (fun x => f x - m) g x)
          + m * (∑ x : ZMod Q, ((Q : ℂ)⁻¹ * ∑ y : ZMod Q, g (x - polyEvalZMod P Q y))) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ = ∑ x : ZMod Q, polyBilinearAverageZMod Polynomial.X P Q (fun x => f x - m) g x := by
        rw [hzero, mul_zero, add_zero]
    _ = ∑ x : ZMod Q, polyBilinearAverageZMod Polynomial.X P Q
          (fun x => f x - (Q : ℂ)⁻¹ * ∑ y : ZMod Q, f y) g x := by
        rw [hm]

end

noncomputable section

/-! ## The core energy estimate -/

/-- **The core estimate** for functions of unit `L²` norm: if the mean-zero `L¹` and `L^q` gains
hold with sufficiently small constants `δ₁, δ₂`, then `‖A(f,g)‖_{L^q} ≤ 1`. -/
theorem avg2CoreNorm (P : Polynomial ℤ) (Q : ℕ) [NeZero Q] {q δ₁ δ₂ C : ℝ}
    (hq2 : 2 ≤ q) (hδ₁ : 0 ≤ δ₁) (hδ₂ : 0 ≤ δ₂) (hC : 0 ≤ C)
    (hTaylor : ∀ x y : ℂ, ‖x + y‖ ^ q ≤ ‖x‖ ^ q + q * ‖x‖ ^ (q - 2) * (star x * y).re
        + C * (‖x‖ ^ (q - 2) * ‖y‖ ^ 2 + ‖y‖ ^ q))
    (h₁ : ∀ f g : ZMod Q → ℂ, (∑ x, g x) = 0 →
        LpNormZMod Q 1 (polyBilinearAverageZMod Polynomial.X P Q f g)
          ≤ δ₁ * LpNormZMod Q 2 f * LpNormZMod Q 2 g)
    (h₂ : ∀ f g : ZMod Q → ℂ, (∑ x, g x) = 0 →
        LpNormZMod Q q (polyBilinearAverageZMod Polynomial.X P Q f g)
          ≤ δ₂ * LpNormZMod Q 2 f * LpNormZMod Q 2 g)
    (hsmall : q * δ₁ + 2 * C * (δ₂ ^ 2 + δ₂ ^ q) ≤ 1) :
    ∀ f g : ZMod Q → ℂ, LpNormZMod Q 2 f = 1 → LpNormZMod Q 2 g = 1 →
      LpNormZMod Q q (polyBilinearAverageZMod Polynomial.X P Q f g) ≤ 1 := by
  intro f g hf2 hg2
  have hqpos : (0 : ℝ) < q := by linarith
  set a : ℂ := (Q : ℂ)⁻¹ * ∑ y : ZMod Q, f y with ha
  set b : ℂ := (Q : ℂ)⁻¹ * ∑ y : ZMod Q, g y with hb
  set f₀ : ZMod Q → ℂ := fun x => f x - a with hf₀
  set g₀ : ZMod Q → ℂ := fun x => g x - b with hg₀
  set X : ZMod Q → ℂ := polyBilinearAverageZMod Polynomial.X P Q f g₀ with hX
  set Y : ZMod Q → ℂ := polyBilinearAverageZMod Polynomial.X P Q f g with hY
  have hsum_g₀ : ∑ x : ZMod Q, g₀ x = 0 := by
    rw [hg₀, hb]
    exact avg2_sum_center Q g
  have hEf : (LpNormZMod Q 2 f₀) ^ 2 + ‖a‖ ^ 2 = 1 := by
    have h := avg2_energy Q f
    rw [hf2, one_pow] at h
    rw [← ha, ← hf₀] at h
    exact h
  have hEg : (LpNormZMod Q 2 g₀) ^ 2 + ‖b‖ ^ 2 = 1 := by
    have h := avg2_energy Q g
    rw [hg2, one_pow] at h
    rw [← hb, ← hg₀] at h
    exact h
  have hdecomp : ∀ x : ZMod Q, Y x = a * b + X x := by
    intro x
    rw [hY, hX, hg₀, hb]
    exact avg2_decomp P Q f g x
  have hX1 : LpNormZMod Q 1 (polyBilinearAverageZMod Polynomial.X P Q f₀ g₀)
      ≤ δ₁ * LpNormZMod Q 2 f₀ * LpNormZMod Q 2 g₀ :=
    h₁ f₀ g₀ hsum_g₀
  have hXq : LpNormZMod Q q X ≤ δ₂ * LpNormZMod Q 2 g₀ := by
    have h := h₂ f g₀ hsum_g₀
    rw [hf2, mul_one] at h
    exact h
  have hmeanX : ‖(Q : ℂ)⁻¹ * ∑ x : ZMod Q, X x‖
      ≤ δ₁ * LpNormZMod Q 2 f₀ * LpNormZMod Q 2 g₀ := by
    have h1 : ∑ x : ZMod Q, X x
        = ∑ x : ZMod Q, polyBilinearAverageZMod Polynomial.X P Q f₀ g₀ x := by
      rw [hX, hf₀, ha]
      exact avg2_mean_eq P Q f g₀ hsum_g₀
    rw [h1]
    exact (avg2_norm_mean_le Q _).trans hX1
  have hX2 : (LpNormZMod Q 2 X) ^ 2 ≤ δ₂ ^ 2 * (LpNormZMod Q 2 g₀) ^ 2 := by
    have h1 : LpNormZMod Q 2 X ≤ LpNormZMod Q q X :=
      LpNormZMod_le_of_le (Q := Q) (q := 2) (p := q) (by norm_num) hq2 X
    have h2 : LpNormZMod Q 2 X ≤ δ₂ * LpNormZMod Q 2 g₀ := h1.trans hXq
    nlinarith [h2, LpNormZMod_nonneg Q 2 X, hδ₂, LpNormZMod_nonneg Q 2 g₀]
  have hXq2 : (LpNormZMod Q q X) ^ q ≤ δ₂ ^ q * (LpNormZMod Q 2 g₀) ^ q := by
    have h2 : 0 ≤ LpNormZMod Q q X := LpNormZMod_nonneg Q q X
    calc (LpNormZMod Q q X) ^ q ≤ (δ₂ * LpNormZMod Q 2 g₀) ^ q :=
          Real.rpow_le_rpow h2 hXq (by linarith)
      _ = δ₂ ^ q * (LpNormZMod Q 2 g₀) ^ q := Real.mul_rpow hδ₂ (LpNormZMod_nonneg Q 2 g₀)
  have hpt : ∀ x : ZMod Q, ‖Y x‖ ^ q ≤ ‖a * b‖ ^ q
      + q * ‖a * b‖ ^ (q - 2) * (star (a * b) * X x).re
      + C * (‖a * b‖ ^ (q - 2) * ‖X x‖ ^ 2 + ‖X x‖ ^ q) := by
    intro x
    have h := hTaylor (a * b) (X x)
    rw [← hdecomp x] at h
    exact h
  have hsum : ∑ x : ZMod Q, ‖Y x‖ ^ q ≤ ∑ x : ZMod Q, (‖a * b‖ ^ q
      + q * ‖a * b‖ ^ (q - 2) * (star (a * b) * X x).re
      + C * (‖a * b‖ ^ (q - 2) * ‖X x‖ ^ 2 + ‖X x‖ ^ q)) :=
    Finset.sum_le_sum (fun x _ => hpt x)
  have hQinv : (0 : ℝ) ≤ (Q : ℝ)⁻¹ := by positivity
  have hQne : (Q : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne Q)
  have hsum1 : (Q : ℝ)⁻¹ * ∑ x : ZMod Q, ‖a * b‖ ^ q = ‖a * b‖ ^ q := by
    rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
    field_simp
  have hsum2 : (Q : ℝ)⁻¹ * ∑ x : ZMod Q, q * ‖a * b‖ ^ (q - 2) * (star (a * b) * X x).re
      = q * ‖a * b‖ ^ (q - 2)
        * (star (a * b) * ((Q : ℂ)⁻¹ * ∑ x : ZMod Q, X x)).re := by
    have h1 : ∑ x : ZMod Q, q * ‖a * b‖ ^ (q - 2) * (star (a * b) * X x).re
        = (q * ‖a * b‖ ^ (q - 2)) * ∑ x : ZMod Q, (star (a * b) * X x).re := by
      rw [Finset.mul_sum]
    rw [h1, ← mul_assoc, mul_comm (Q : ℝ)⁻¹ (q * ‖a * b‖ ^ (q - 2)), mul_assoc,
      avg2_sum_re]
  have hsum3 : (Q : ℝ)⁻¹ * ∑ x : ZMod Q, C * (‖a * b‖ ^ (q - 2) * ‖X x‖ ^ 2 + ‖X x‖ ^ q)
      = C * (‖a * b‖ ^ (q - 2) * (LpNormZMod Q 2 X) ^ 2 + (LpNormZMod Q q X) ^ q) := by
    have h1 : ∑ x : ZMod Q, C * (‖a * b‖ ^ (q - 2) * ‖X x‖ ^ 2 + ‖X x‖ ^ q)
        = C * ∑ x : ZMod Q, (‖a * b‖ ^ (q - 2) * ‖X x‖ ^ 2 + ‖X x‖ ^ q) := by
      rw [Finset.mul_sum]
    have h2 : ∑ x : ZMod Q, (‖a * b‖ ^ (q - 2) * ‖X x‖ ^ 2 + ‖X x‖ ^ q)
        = ‖a * b‖ ^ (q - 2) * ∑ x : ZMod Q, ‖X x‖ ^ 2 + ∑ x : ZMod Q, ‖X x‖ ^ q := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    have h3 : (Q : ℝ)⁻¹ * ∑ x : ZMod Q, ‖X x‖ ^ 2 = (LpNormZMod Q 2 X) ^ 2 :=
      (Work.Analysis.Paraproduct.LpNormZMod_two_sq Q X).symm
    have h4 : (Q : ℝ)⁻¹ * ∑ x : ZMod Q, ‖X x‖ ^ q = (LpNormZMod Q q X) ^ q :=
      (LpNormZMod_rpow Q hqpos X).symm
    calc (Q : ℝ)⁻¹ * ∑ x : ZMod Q, C * (‖a * b‖ ^ (q - 2) * ‖X x‖ ^ 2 + ‖X x‖ ^ q)
        = (Q : ℝ)⁻¹ * (C * (‖a * b‖ ^ (q - 2) * ∑ x : ZMod Q, ‖X x‖ ^ 2
            + ∑ x : ZMod Q, ‖X x‖ ^ q)) := by rw [h1, h2]
      _ = C * (‖a * b‖ ^ (q - 2) * ((Q : ℝ)⁻¹ * ∑ x : ZMod Q, ‖X x‖ ^ 2)
            + (Q : ℝ)⁻¹ * ∑ x : ZMod Q, ‖X x‖ ^ q) := by ring
      _ = C * (‖a * b‖ ^ (q - 2) * (LpNormZMod Q 2 X) ^ 2 + (LpNormZMod Q q X) ^ q) := by
            rw [h3, h4]
  have hkey : (LpNormZMod Q q Y) ^ q
      ≤ ‖a * b‖ ^ q
        + q * ‖a * b‖ ^ (q - 2) * (star (a * b) * ((Q : ℂ)⁻¹ * ∑ x : ZMod Q, X x)).re
        + C * (‖a * b‖ ^ (q - 2) * (LpNormZMod Q 2 X) ^ 2 + (LpNormZMod Q q X) ^ q) := by
    rw [LpNormZMod_rpow Q hqpos Y]
    refine (mul_le_mul_of_nonneg_left hsum hQinv).trans (le_of_eq ?_)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, mul_add, mul_add,
      hsum1, hsum2, hsum3]
  -- numeric bookkeeping
  have hEf0 : 0 ≤ (LpNormZMod Q 2 f₀) ^ 2 := sq_nonneg _
  have hEg0 : 0 ≤ (LpNormZMod Q 2 g₀) ^ 2 := sq_nonneg _
  have hEf1 : (LpNormZMod Q 2 f₀) ^ 2 ≤ 1 := by
    have h := sq_nonneg ‖a‖
    linarith [hEf]
  have hEg1 : (LpNormZMod Q 2 g₀) ^ 2 ≤ 1 := by
    have h := sq_nonneg ‖b‖
    linarith [hEg]
  have hkg : ‖a * b‖ ^ (q - 2) ≤ 1 := by
    have h1 : ‖a * b‖ = ‖a‖ * ‖b‖ := norm_mul _ _
    have h2 : ‖a‖ * ‖b‖ ≤ 1 := by
      have h3 : ‖a‖ ^ 2 = 1 - (LpNormZMod Q 2 f₀) ^ 2 := by linarith [hEf]
      have h4 : ‖b‖ ^ 2 = 1 - (LpNormZMod Q 2 g₀) ^ 2 := by linarith [hEg]
      nlinarith [norm_nonneg a, norm_nonneg b, hEf1, hEg1, hEf0, hEg0,
        sq_nonneg (‖a‖ - ‖b‖), sq_nonneg (‖a‖ + ‖b‖)]
    rw [h1]
    exact Real.rpow_le_one (by positivity) h2 (by linarith)
  have hnormab1 : ‖a * b‖ ≤ 1 := by
    rw [norm_mul]
    nlinarith [hEf, hEg, norm_nonneg a, norm_nonneg b, hEf0, hEg0, hEf1, hEg1]
  have habs : ‖a * b‖ ^ q
      = ((1 - (LpNormZMod Q 2 f₀) ^ 2) * (1 - (LpNormZMod Q 2 g₀) ^ 2)) ^ (q / 2) := by
    have h3 : ‖a‖ ^ 2 = 1 - (LpNormZMod Q 2 f₀) ^ 2 := by linarith [hEf]
    have h4 : ‖b‖ ^ 2 = 1 - (LpNormZMod Q 2 g₀) ^ 2 := by linarith [hEg]
    rw [avg2_rpow_two ‖a * b‖ (norm_nonneg _) q, norm_mul, mul_pow, h3, h4]
  have hmain1 : ((1 - (LpNormZMod Q 2 f₀) ^ 2) * (1 - (LpNormZMod Q 2 g₀) ^ 2)) ^ (q / 2)
      ≤ 1 - ((LpNormZMod Q 2 f₀) ^ 2 + (LpNormZMod Q 2 g₀) ^ 2) / 2 := by
    have h1 : (1 - (LpNormZMod Q 2 f₀) ^ 2) * (1 - (LpNormZMod Q 2 g₀) ^ 2)
        ≤ 1 - ((LpNormZMod Q 2 f₀) ^ 2 + (LpNormZMod Q 2 g₀) ^ 2) / 2 := by
      nlinarith [hEf0, hEg0, hEf1, hEg1,
        sq_nonneg ((LpNormZMod Q 2 f₀) ^ 2 - (LpNormZMod Q 2 g₀) ^ 2)]
    have h2 : 0 ≤ (1 - (LpNormZMod Q 2 f₀) ^ 2) * (1 - (LpNormZMod Q 2 g₀) ^ 2) :=
      mul_nonneg (by linarith) (by linarith)
    have h3 : (1 - (LpNormZMod Q 2 f₀) ^ 2) * (1 - (LpNormZMod Q 2 g₀) ^ 2) ≤ 1 := by
      linarith [h1, hEf0, hEg0]
    exact (Real.rpow_le_self_of_le_one h2 h3 (by linarith : (1 : ℝ) ≤ q / 2)).trans h1
  have hlin : q * ‖a * b‖ ^ (q - 2) * (star (a * b) * ((Q : ℂ)⁻¹ * ∑ x : ZMod Q, X x)).re
      ≤ q * δ₁ * Real.sqrt ((LpNormZMod Q 2 f₀) ^ 2 * (LpNormZMod Q 2 g₀) ^ 2) := by
    have h1 : (star (a * b) * ((Q : ℂ)⁻¹ * ∑ x : ZMod Q, X x)).re
        ≤ ‖a * b‖ * ‖(Q : ℂ)⁻¹ * ∑ x : ZMod Q, X x‖ := by
      have h := Complex.re_le_norm (star (a * b) * ((Q : ℂ)⁻¹ * ∑ x : ZMod Q, X x))
      rwa [norm_mul, norm_star] at h
    have h2 : ‖(Q : ℂ)⁻¹ * ∑ x : ZMod Q, X x‖
        ≤ δ₁ * LpNormZMod Q 2 f₀ * LpNormZMod Q 2 g₀ := hmeanX
    have h5 : 0 ≤ q * ‖a * b‖ ^ (q - 2) := by positivity
    have h6 : Real.sqrt ((LpNormZMod Q 2 f₀) ^ 2 * (LpNormZMod Q 2 g₀) ^ 2)
        = LpNormZMod Q 2 f₀ * LpNormZMod Q 2 g₀ := by
      rw [Real.sqrt_mul (sq_nonneg _) _, Real.sqrt_sq (LpNormZMod_nonneg Q 2 f₀),
        Real.sqrt_sq (LpNormZMod_nonneg Q 2 g₀)]
    rw [h6]
    have hqk : q * ‖a * b‖ ^ (q - 2) ≤ q * 1 := mul_le_mul_of_nonneg_left hkg (by linarith)
    have hprod : ‖a * b‖ * ‖(Q : ℂ)⁻¹ * ∑ x : ZMod Q, X x‖
        ≤ 1 * (δ₁ * LpNormZMod Q 2 f₀ * LpNormZMod Q 2 g₀) :=
      mul_le_mul hnormab1 h2 (by positivity) (by norm_num)
    calc q * ‖a * b‖ ^ (q - 2) * (star (a * b) * ((Q : ℂ)⁻¹ * ∑ x : ZMod Q, X x)).re
        ≤ q * ‖a * b‖ ^ (q - 2) * (‖a * b‖ * ‖(Q : ℂ)⁻¹ * ∑ x : ZMod Q, X x‖) :=
          mul_le_mul_of_nonneg_left h1 h5
      _ ≤ q * 1 * (1 * (δ₁ * LpNormZMod Q 2 f₀ * LpNormZMod Q 2 g₀)) :=
          mul_le_mul hqk hprod (by positivity) (by positivity)
      _ = q * δ₁ * (LpNormZMod Q 2 f₀ * LpNormZMod Q 2 g₀) := by ring
  have hquad1 : C * (‖a * b‖ ^ (q - 2) * (LpNormZMod Q 2 X) ^ 2)
      ≤ C * 1 * (δ₂ ^ 2 * (LpNormZMod Q 2 g₀) ^ 2) := by
    have hstep : ‖a * b‖ ^ (q - 2) * (LpNormZMod Q 2 X) ^ 2
        ≤ 1 * (δ₂ ^ 2 * (LpNormZMod Q 2 g₀) ^ 2) :=
      mul_le_mul hkg hX2 (by positivity) (by norm_num)
    calc C * (‖a * b‖ ^ (q - 2) * (LpNormZMod Q 2 X) ^ 2)
        ≤ C * (1 * (δ₂ ^ 2 * (LpNormZMod Q 2 g₀) ^ 2)) :=
          mul_le_mul_of_nonneg_left hstep hC
      _ = C * 1 * (δ₂ ^ 2 * (LpNormZMod Q 2 g₀) ^ 2) := by ring
  have hquad2 : C * (LpNormZMod Q q X) ^ q ≤ C * (δ₂ ^ q * (LpNormZMod Q 2 g₀) ^ q) :=
    mul_le_mul_of_nonneg_left hXq2 hC
  have htot : (LpNormZMod Q q Y) ^ q
      ≤ 1 - ((LpNormZMod Q 2 f₀) ^ 2 + (LpNormZMod Q 2 g₀) ^ 2) / 2
        + q * δ₁ * ((LpNormZMod Q 2 f₀) ^ 2 + (LpNormZMod Q 2 g₀) ^ 2) / 2
        + C * (δ₂ ^ 2 * (LpNormZMod Q 2 g₀) ^ 2)
        + C * (δ₂ ^ q * (LpNormZMod Q 2 g₀) ^ q) := by
    have hAM : Real.sqrt ((LpNormZMod Q 2 f₀) ^ 2 * (LpNormZMod Q 2 g₀) ^ 2)
        ≤ ((LpNormZMod Q 2 f₀) ^ 2 + (LpNormZMod Q 2 g₀) ^ 2) / 2 := by
      have h0 : 0 ≤ (LpNormZMod Q 2 f₀) ^ 2 * (LpNormZMod Q 2 g₀) ^ 2 :=
        mul_nonneg hEf0 hEg0
      have hs : (Real.sqrt ((LpNormZMod Q 2 f₀) ^ 2 * (LpNormZMod Q 2 g₀) ^ 2)) ^ 2
          = (LpNormZMod Q 2 f₀) ^ 2 * (LpNormZMod Q 2 g₀) ^ 2 := Real.sq_sqrt h0
      nlinarith [hs, Real.sqrt_nonneg ((LpNormZMod Q 2 f₀) ^ 2 * (LpNormZMod Q 2 g₀) ^ 2),
        sq_nonneg ((LpNormZMod Q 2 f₀) ^ 2 - (LpNormZMod Q 2 g₀) ^ 2)]
    have hq1 : q * δ₁ * Real.sqrt ((LpNormZMod Q 2 f₀) ^ 2 * (LpNormZMod Q 2 g₀) ^ 2)
        ≤ q * δ₁ * (((LpNormZMod Q 2 f₀) ^ 2 + (LpNormZMod Q 2 g₀) ^ 2) / 2) :=
      mul_le_mul_of_nonneg_left hAM (by positivity)
    rw [habs] at hkey
    linarith [hkey, hmain1, hlin, hquad1, hquad2, hq1]
  have hEr : (LpNormZMod Q 2 g₀) ^ q ≤ (LpNormZMod Q 2 g₀) ^ 2 := by
    rw [avg2_rpow_two (LpNormZMod Q 2 g₀) (LpNormZMod_nonneg Q 2 g₀) q]
    exact Real.rpow_le_self_of_le_one hEg0 hEg1 (by linarith : (1 : ℝ) ≤ q / 2)
  have hfin : (LpNormZMod Q q Y) ^ q ≤ 1 := by
    set S : ℝ := (LpNormZMod Q 2 f₀) ^ 2 + (LpNormZMod Q 2 g₀) ^ 2 with hSdef
    have hS : 0 ≤ S := by rw [hSdef]; positivity
    have hSg : (LpNormZMod Q 2 g₀) ^ 2 ≤ S := by rw [hSdef]; linarith [hEf0]
    have hSq : (LpNormZMod Q 2 g₀) ^ q ≤ S := hEr.trans hSg
    have hsmall' : q * δ₁ / 2 + C * (δ₂ ^ 2 + δ₂ ^ q) ≤ 1 / 2 := by linarith [hsmall]
    have hm : (q * δ₁ / 2 + C * (δ₂ ^ 2 + δ₂ ^ q)) * S ≤ (1 / 2) * S :=
      mul_le_mul_of_nonneg_right hsmall' hS
    have hC2 : C * δ₂ ^ 2 * (LpNormZMod Q 2 g₀) ^ 2 ≤ C * δ₂ ^ 2 * S :=
      mul_le_mul_of_nonneg_left hSg (by positivity)
    have hCq : C * δ₂ ^ q * (LpNormZMod Q 2 g₀) ^ q ≤ C * δ₂ ^ q * S :=
      mul_le_mul_of_nonneg_left hSq (by positivity)
    rw [hSdef] at htot
    nlinarith [htot, hC2, hCq, hm, hS]
  have h1 : ((LpNormZMod Q q Y) ^ q) ^ (1 / q) ≤ (1 : ℝ) ^ (1 / q) :=
    Real.rpow_le_rpow (Real.rpow_nonneg (LpNormZMod_nonneg Q q Y) q) hfin
      (div_nonneg zero_le_one (le_of_lt hqpos))
  rw [← Real.rpow_mul (LpNormZMod_nonneg Q q Y) q (1 / q), mul_one_div,
    div_self (ne_of_gt hqpos), Real.rpow_one, Real.one_rpow] at h1
  exact h1

/-- **The core estimate** in the unnormalized form. -/
theorem avg2Core (P : Polynomial ℤ) (Q : ℕ) [NeZero Q] {q δ₁ δ₂ C : ℝ}
    (hq2 : 2 ≤ q) (hδ₁ : 0 ≤ δ₁) (hδ₂ : 0 ≤ δ₂) (hC : 0 ≤ C)
    (hTaylor : ∀ x y : ℂ, ‖x + y‖ ^ q ≤ ‖x‖ ^ q + q * ‖x‖ ^ (q - 2) * (star x * y).re
        + C * (‖x‖ ^ (q - 2) * ‖y‖ ^ 2 + ‖y‖ ^ q))
    (h₁ : ∀ f g : ZMod Q → ℂ, (∑ x, g x) = 0 →
        LpNormZMod Q 1 (polyBilinearAverageZMod Polynomial.X P Q f g)
          ≤ δ₁ * LpNormZMod Q 2 f * LpNormZMod Q 2 g)
    (h₂ : ∀ f g : ZMod Q → ℂ, (∑ x, g x) = 0 →
        LpNormZMod Q q (polyBilinearAverageZMod Polynomial.X P Q f g)
          ≤ δ₂ * LpNormZMod Q 2 f * LpNormZMod Q 2 g)
    (hsmall : q * δ₁ + 2 * C * (δ₂ ^ 2 + δ₂ ^ q) ≤ 1) :
    ∀ f g : ZMod Q → ℂ,
      LpNormZMod Q q (polyBilinearAverageZMod Polynomial.X P Q f g)
        ≤ LpNormZMod Q 2 f * LpNormZMod Q 2 g := by
  have hqpos : (0 : ℝ) < q := by linarith
  intro f g
  set F : ℝ := LpNormZMod Q 2 f with hF
  set G : ℝ := LpNormZMod Q 2 g with hG
  have hFnn : 0 ≤ F := LpNormZMod_nonneg Q 2 f
  have hGnn : 0 ≤ G := LpNormZMod_nonneg Q 2 g
  rcases eq_or_lt_of_le hFnn with hF0 | hFpos
  · have hf0 : ∀ x, f x = 0 :=
      avg2_eq_zero_of_LpNormZMod_two_mul_eq_zero Q (f := f) (by rw [← hF]; exact hF0.symm)
    have hL : LpNormZMod Q q (polyBilinearAverageZMod Polynomial.X P Q f g) = 0 := by
      have hzero : polyBilinearAverageZMod Polynomial.X P Q f g = fun _ => 0 := by
        funext x
        simp only [polyBilinearAverageZMod, polyEvalZMod_X]
        have hz : (∑ y : ZMod Q, f (x - y) * g (x - polyEvalZMod P Q y)) = 0 := by
          apply Finset.sum_eq_zero
          intro y _
          rw [hf0 (x - y), zero_mul]
        rw [hz, mul_zero]
      rw [hzero, LpNormZMod]
      simp only [norm_zero]
      rw [Real.zero_rpow (ne_of_gt hqpos), Finset.sum_const_zero, mul_zero]
      exact Real.zero_rpow (by positivity : (1 / q : ℝ) ≠ 0)
    rw [hL]
    rw [hF0.symm, zero_mul]
  · rcases eq_or_lt_of_le hGnn with hG0 | hGpos
    · have hg0 : ∀ x, g x = 0 :=
        avg2_eq_zero_of_LpNormZMod_two_mul_eq_zero Q (f := g) (by rw [← hG]; exact hG0.symm)
      have hL : LpNormZMod Q q (polyBilinearAverageZMod Polynomial.X P Q f g) = 0 := by
        have hzero : polyBilinearAverageZMod Polynomial.X P Q f g = fun _ => 0 := by
          funext x
          simp only [polyBilinearAverageZMod, polyEvalZMod_X]
          have hz : (∑ y : ZMod Q, f (x - y) * g (x - polyEvalZMod P Q y)) = 0 := by
            apply Finset.sum_eq_zero
            intro y _
            rw [hg0 (x - polyEvalZMod P Q y), mul_zero]
          rw [hz, mul_zero]
        rw [hzero, LpNormZMod]
        simp only [norm_zero]
        rw [Real.zero_rpow (ne_of_gt hqpos), Finset.sum_const_zero, mul_zero]
        exact Real.zero_rpow (by positivity : (1 / q : ℝ) ≠ 0)
      rw [hL]
      rw [hG0.symm, mul_zero]
    · have hFne : (F : ℂ) ≠ 0 := fun h => (ne_of_gt hFpos) (by
        have := congrArg Complex.re h
        simpa using this)
      have hGne : (G : ℂ) ≠ 0 := fun h => (ne_of_gt hGpos) (by
        have := congrArg Complex.re h
        simpa using this)
      set f' : ZMod Q → ℂ := fun x => ((F : ℝ)⁻¹ : ℂ) * f x with hf'
      set g' : ZMod Q → ℂ := fun x => ((G : ℝ)⁻¹ : ℂ) * g x with hg'
      have hF' : LpNormZMod Q 2 f' = 1 := by
        rw [hf', ← Complex.ofReal_inv]
        rw [LpNormZMod_const_mul Q (s := 2) (c := (F : ℝ)⁻¹) (by norm_num)
          (by positivity) f, ← hF]
        exact inv_mul_cancel₀ (ne_of_gt hFpos)
      have hG' : LpNormZMod Q 2 g' = 1 := by
        rw [hg', ← Complex.ofReal_inv]
        rw [LpNormZMod_const_mul Q (s := 2) (c := (G : ℝ)⁻¹) (by norm_num)
          (by positivity) g, ← hG]
        exact inv_mul_cancel₀ (ne_of_gt hGpos)
      have hnorm := avg2CoreNorm P Q hq2 hδ₁ hδ₂ hC hTaylor h₁ h₂ hsmall f' g' hF' hG'
      have hpt : ∀ x : ZMod Q, polyBilinearAverageZMod Polynomial.X P Q f g x
          = ((F * G : ℝ) : ℂ) * polyBilinearAverageZMod Polynomial.X P Q f' g' x := by
        intro x
        have hfx : ∀ y, f y = (F : ℂ) * f' y := by
          intro y
          rw [hf', ← mul_assoc, mul_inv_cancel₀ hFne, one_mul]
        have hgy : ∀ y, g y = (G : ℂ) * g' y := by
          intro y
          rw [hg', ← mul_assoc, mul_inv_cancel₀ hGne, one_mul]
        have hFG : (∑ y : ZMod Q, (F : ℂ) * f' (x - y) * ((G : ℂ) * g' (x - polyEvalZMod P Q y)))
            = ((F * G : ℝ) : ℂ)
              * ∑ y : ZMod Q, f' (x - y) * g' (x - polyEvalZMod P Q y) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro y _
          push_cast
          ring
        simp only [polyBilinearAverageZMod, polyEvalZMod_X]
        rw [Finset.sum_congr rfl (fun y _ => by rw [hfx (x - y), hgy (x - polyEvalZMod P Q y)]),
          hFG]
        ring
      have hscale : polyBilinearAverageZMod Polynomial.X P Q f g
          = fun x => ((F * G : ℝ) : ℂ) * polyBilinearAverageZMod Polynomial.X P Q f' g' x :=
        funext hpt
      rw [hscale, LpNormZMod_const_mul Q (s := q) (c := F * G) (by linarith) (by positivity) _]
      calc (F * G) * LpNormZMod Q q (polyBilinearAverageZMod Polynomial.X P Q f' g')
          ≤ (F * G) * 1 := mul_le_mul_of_nonneg_left hnorm (by positivity)
        _ = LpNormZMod Q 2 f * LpNormZMod Q 2 g := by rw [mul_one, ← hF, ← hG]

end

noncomputable section

/-! ## The two large-prime gains -/

/-- Arbitrarily large levels `l` with `C₁ 2^{-c l} ≤ ε` (for `c > 0`, `ε > 0`). -/
lemma avg2_exists_level (c C₁ ε : ℝ) (hc : 0 < c) (hε : 0 < ε) :
    ∃ l : ℕ, C₁ * (2 : ℝ) ^ (-(c * l)) ≤ ε := by
  have hbase1 : (2 : ℝ) ^ (-c) < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  have hbase0 : (0 : ℝ) ≤ (2 : ℝ) ^ (-c) := Real.rpow_nonneg (by norm_num) _
  have htend : Tendsto (fun l : ℕ => C₁ * ((2 : ℝ) ^ (-c)) ^ l) atTop (nhds 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one hbase0 hbase1
    simpa using h.const_mul C₁
  have hev : ∀ᶠ l : ℕ in atTop, C₁ * ((2 : ℝ) ^ (-c)) ^ l ≤ ε := by
    filter_upwards [htend.eventually (isOpen_Iio.mem_nhds (Set.mem_Iio.mpr hε))] with l hl
    exact hl.le
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine ⟨N, ?_⟩
  have h := hN N le_rfl
  have h2 : (2 : ℝ) ^ (-(c * (N : ℝ))) = ((2 : ℝ) ^ (-c)) ^ N := by
    rw [show (-(c * (N : ℝ))) = -c * (N : ℝ) by ring, Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),
      Real.rpow_natCast]
  rw [h2]
  exact h

/-- **Mean-zero `L¹` gain for large primes** (the paper's `(eq:39)`). -/
theorem avg2GainL1 (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (hI : Work.KMTContract.ImprovKMT P) :
    ∀ ε : ℝ, 0 < ε → ∃ p₀ : ℕ, ∀ (p j : ℕ) [Fact p.Prime] [NeZero (p ^ j)], p₀ ≤ p → 1 ≤ j →
      ∀ (f g : ZMod (p ^ j) → ℂ), (∑ x : ZMod (p ^ j), g x) = 0 →
        LpNormZMod (p ^ j) 1 (polyBilinearAverageZMod Polynomial.X P (p ^ j) f g)
          ≤ ε * LpNormZMod (p ^ j) 2 f * LpNormZMod (p ^ j) 2 g := by
  intro ε hε
  obtain ⟨c, hc, hB⟩ := MdlBileR1OfImprov P hd hI
  obtain ⟨C₁, hC₁pos, hC₁b⟩ := hB 1 one_pos le_rfl
  obtain ⟨l, hl⟩ := avg2_exists_level c C₁ ε hc hε
  obtain ⟨B, hB'⟩ := MdlIwMinorArc_of_meanZero_largePrime 1 one_pos le_rfl l
  refine ⟨max l (B + 1), fun p j _ _ hp hj f g hg => ?_⟩
  have hpB : B < p :=
    lt_of_lt_of_le (Nat.lt_succ_self B) (le_trans (le_max_right l (B + 1)) hp)
  have hminor : MdlIwMinorArc 1 l (p ^ j) g := hB' p j hpB g hg
  have hmain := hC₁b (p ^ j) l f g (Or.inr hminor)
  calc LpNormZMod (p ^ j) 1 (polyBilinearAverageZMod Polynomial.X P (p ^ j) f g)
      ≤ C₁ * (2 : ℝ) ^ (-(c * l)) * LpNormZMod (p ^ j) 2 f * LpNormZMod (p ^ j) 2 g := hmain
    _ ≤ ε * LpNormZMod (p ^ j) 2 f * LpNormZMod (p ^ j) 2 g := by
        apply mul_le_mul_of_nonneg_right _ (LpNormZMod_nonneg _ 2 _)
        exact mul_le_mul_of_nonneg_right hl (LpNormZMod_nonneg _ 2 _)

/-- **Mean-zero `L^q` gain for large primes** (the paper's `(eq:42)`). -/
theorem avg2GainLq (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (hI : Work.KMTContract.ImprovKMT P)
    (hConc : Work.Analysis.Concentration.Corollary1 P P.natDegree)
    {q : ℝ} (hq2 : 2 < q)
    (hq : q < 2 * (P.natDegree : ℝ) / ((P.natDegree : ℝ) - 1)) :
    ∀ ε : ℝ, 0 < ε → ∃ p₀ : ℕ, ∀ (p j : ℕ) [Fact p.Prime] [NeZero (p ^ j)], p₀ ≤ p → 1 ≤ j →
      ∀ (f g : ZMod (p ^ j) → ℂ), (∑ x : ZMod (p ^ j), g x) = 0 →
        LpNormZMod (p ^ j) q (polyBilinearAverageZMod Polynomial.X P (p ^ j) f g)
          ≤ ε * LpNormZMod (p ^ j) 2 f * LpNormZMod (p ^ j) 2 g := by
  intro ε hε
  set d : ℝ := (P.natDegree : ℝ) with hddef
  have hd2 : 2 ≤ d := by rw [hddef]; exact_mod_cast hd
  have hq' : q < 2 * d / (d - 1) := by rw [hddef]; exact hq
  set q₀ : ℝ := (q + 2 * d / (d - 1)) / 2 with hq₀def
  have hqq₀ : q < q₀ := by rw [hq₀def]; linarith [hq']
  have hq₀Qm : q₀ < 2 * d / (d - 1) := by rw [hq₀def]; linarith [hq']
  have hq₀2 : 2 < q₀ := lt_trans hq2 hqq₀
  have hs0 : 0 < q₀ / 2 := by linarith
  have hs1 : 1 ≤ q₀ / 2 := by linarith
  have hslt : q₀ / 2 < d / (d - 1) := by
    have h2 : 2 * d / (d - 1) / 2 = d / (d - 1) := by ring
    linarith [hq₀Qm, h2]
  obtain ⟨Cfib, hCfibpos, hCfibl⟩ := hConc (q₀ / 2) hs0 hslt
  set KA : ℝ := Real.sqrt Cfib with hKAdef
  have hKApos : 0 < KA := Real.sqrt_pos.mpr hCfibpos
  have hAvg1 : ∀ (p j : ℕ) [Fact p.Prime] [NeZero (p ^ j)], 1 ≤ j →
      ∀ f g : ZMod (p ^ j) → ℂ,
        LpNormZMod (p ^ j) q₀ (polyBilinearAverageZMod Polynomial.X P (p ^ j) f g)
          ≤ KA * LpNormZMod (p ^ j) 2 f * LpNormZMod (p ^ j) 2 g := by
    intro p j _ _ hj f g
    have hfib : FiberLpBound P (p ^ j) (q₀ / 2) Cfib := hCfibl p j hj
    have hnorm := Work.Analysis.Paraproduct.lpNorm_fiberCard_le_of_fiberLpBound P (p ^ j)
      hs0 hCfibpos.le hfib
    have h := Work.Analysis.Paraproduct.bilinearAverageLq_of_fiber P (p ^ j) hs1 hnorm
    rw [show 2 * (q₀ / 2) = q₀ by ring] at h
    exact h f g
  have hq1 : 1 < q := by linarith
  have hqpos : (0 : ℝ) < q := by linarith
  have hq₀pos : (0 : ℝ) < q₀ := by linarith
  have hden : (0 : ℝ) < 1 - 1 / q₀ := by
    have h : (1 : ℝ) / q₀ < 1 := by rw [div_lt_one hq₀pos]; linarith
    linarith
  set θ : ℝ := (1 / q - 1 / q₀) / (1 - 1 / q₀) with hθdef
  have hθpos : 0 < θ := by
    rw [hθdef]
    apply div_pos _ hden
    have h : 1 / q₀ < 1 / q := one_div_lt_one_div_of_lt hqpos hqq₀
    linarith
  have hθ0 : 0 ≤ θ := hθpos.le
  have hθ1 : θ ≤ 1 := by
    rw [hθdef, div_le_one hden]
    have h : 1 / q₀ < 1 / q := one_div_lt_one_div_of_lt hqpos hqq₀
    have h1 : 1 / q ≤ 1 := by
      rw [div_le_one hqpos]; linarith
    linarith
  have hrel : 1 / q = θ / 1 + (1 - θ) / q₀ := by
    have hdne : 1 - 1 / q₀ ≠ 0 := ne_of_gt hden
    have h : θ * (1 - 1 / q₀) = 1 / q - 1 / q₀ := by
      rw [hθdef, div_mul_cancel₀ _ hdne]
    have h2 : θ + (1 - θ) / q₀ = 1 / q := by
      have h3 : (1 - θ) / q₀ = (1 - θ) * (1 / q₀) := by ring
      rw [h3]
      nlinarith [h]
    rw [div_one]
    linarith [h2]
  obtain ⟨c, hc, hB⟩ := MdlBileR1OfImprov P hd hI
  obtain ⟨CB, hCBpos, hCBb⟩ := hB 1 one_pos le_rfl
  obtain ⟨ε₁, hε₁pos, hε₁⟩ : ∃ ε₁ : ℝ, 0 < ε₁ ∧ ε₁ ^ θ * KA ^ (1 - θ) ≤ ε := by
    set D : ℝ := 2 * KA ^ (1 - θ) with hD
    have hDpos : 0 < D := by rw [hD]; positivity
    have hb : 0 < (ε / D) ^ (1 / θ) := Real.rpow_pos_of_pos (by positivity) _
    refine ⟨min 1 ((ε / D) ^ (1 / θ)), lt_min one_pos hb, ?_⟩
    have h1 : min 1 ((ε / D) ^ (1 / θ)) ≤ (ε / D) ^ (1 / θ) := min_le_right _ _
    have h2 : (min 1 ((ε / D) ^ (1 / θ))) ^ θ ≤ ((ε / D) ^ (1 / θ)) ^ θ :=
      Real.rpow_le_rpow (le_of_lt (lt_min one_pos hb)) h1 hθ0
    have h3 : ((ε / D) ^ (1 / θ)) ^ θ = ε / D := by
      rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ ε / D),
        one_div_mul_cancel (ne_of_gt hθpos), Real.rpow_one]
    rw [h3] at h2
    have h4 : 0 ≤ KA ^ (1 - θ) := Real.rpow_nonneg hKApos.le _
    have h5 : ε / D * KA ^ (1 - θ) = ε / 2 := by
      rw [hD]; field_simp
    calc (min 1 ((ε / D) ^ (1 / θ))) ^ θ * KA ^ (1 - θ)
        ≤ (ε / D) * KA ^ (1 - θ) := mul_le_mul_of_nonneg_right h2 h4
      _ = ε / 2 := h5
      _ ≤ ε := by linarith
  obtain ⟨l, hl⟩ := avg2_exists_level c CB ε₁ hc hε₁pos
  obtain ⟨B, hB'⟩ := MdlIwMinorArc_of_meanZero_largePrime 1 one_pos le_rfl l
  refine ⟨max l (B + 1), fun p j _ _ hp hj f g hg => ?_⟩
  have hpB : B < p :=
    lt_of_lt_of_le (Nat.lt_succ_self B) (le_trans (le_max_right l (B + 1)) hp)
  have hminor : MdlIwMinorArc 1 l (p ^ j) g := hB' p j hpB g hg
  have h1 : ∀ f g : ZMod (p ^ j) → ℂ,
      (MdlIwMinorArc 1 l (p ^ j) f ∨ MdlIwMinorArc 1 l (p ^ j) g) →
      LpNormZMod (p ^ j) 1 (polyBilinearAverageZMod Polynomial.X P (p ^ j) f g)
        ≤ (CB * (2 : ℝ) ^ (-(c * l))) * LpNormZMod (p ^ j) 2 f * LpNormZMod (p ^ j) 2 g :=
    fun f g hfg => hCBb (p ^ j) l f g hfg
  have h2 : ∀ f g : ZMod (p ^ j) → ℂ,
      LpNormZMod (p ^ j) q₀ (polyBilinearAverageZMod Polynomial.X P (p ^ j) f g)
        ≤ KA * LpNormZMod (p ^ j) 2 f * LpNormZMod (p ^ j) 2 g := hAvg1 p j hj
  have hinterp := bileInterpIwClean P (p ^ j) (ρ := 1) (l := l) (q := q₀) (r := q) (θ := θ)
      (ε := CB * (2 : ℝ) ^ (-(c * l))) (C := KA) (by linarith) hθ0 hθ1 hrel
      (by positivity) hKApos.le h1 h2 f g (Or.inr hminor)
  have hεb : (CB * (2 : ℝ) ^ (-(c * l))) ^ θ * KA ^ (1 - θ) ≤ ε := by
    have h0 : 0 ≤ CB * (2 : ℝ) ^ (-(c * l)) := by positivity
    calc (CB * (2 : ℝ) ^ (-(c * l))) ^ θ * KA ^ (1 - θ)
        ≤ ε₁ ^ θ * KA ^ (1 - θ) :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow h0 hl hθ0)
            (Real.rpow_nonneg hKApos.le _)
      _ ≤ ε := hε₁
  calc LpNormZMod (p ^ j) q (polyBilinearAverageZMod Polynomial.X P (p ^ j) f g)
      ≤ (CB * (2 : ℝ) ^ (-(c * l))) ^ θ * KA ^ (1 - θ) * LpNormZMod (p ^ j) 2 f
          * LpNormZMod (p ^ j) 2 g := hinterp
    _ ≤ ε * LpNormZMod (p ^ j) 2 f * LpNormZMod (p ^ j) 2 g := by
        apply mul_le_mul_of_nonneg_right _ (LpNormZMod_nonneg _ 2 _)
        exact mul_le_mul_of_nonneg_right hεb (LpNormZMod_nonneg _ 2 _)

/-- **(avg-2)**, the paper's constant-`1` `L² × L² → L^q` bound for large prime powers. -/
theorem bilinAvgLq_largePrime_avg2 (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (hI : Work.KMTContract.ImprovKMT P)
    (hConc : Work.Analysis.Concentration.Corollary1 P P.natDegree)
    (q : ℝ) (hq2 : 2 < q) (hq : q < 2 * (P.natDegree : ℝ) / ((P.natDegree : ℝ) - 1)) :
    ∃ p₀ : ℕ, ∀ (p j : ℕ) [Fact p.Prime] [NeZero (p ^ j)], p₀ ≤ p → 1 ≤ j →
      Work.Analysis.Concentration.BilinearAverageLq P (p ^ j) q 1 := by
  obtain ⟨C, hCpos, hTaylor⟩ := avg2Taylor q (le_of_lt hq2)
  set δ₁ : ℝ := 1 / (4 * q) with hδ₁def
  set δ₂ : ℝ := min 1 (1 / (8 * C + 1)) with hδ₂def
  have hδ₁pos : 0 < δ₁ := by rw [hδ₁def]; positivity
  have hδ₂pos : 0 < δ₂ := by rw [hδ₂def]; positivity
  have hδ₂1 : δ₂ ≤ 1 := by rw [hδ₂def]; exact min_le_left _ _
  have hδ₂sq : δ₂ ^ 2 ≤ 1 / (8 * C) := by
    have h2 : δ₂ ^ 2 ≤ (1 / (8 * C + 1)) ^ 2 := by
      rw [hδ₂def]
      exact pow_le_pow_left₀ (by positivity) (min_le_right _ _) 2
    have h3 : (1 / (8 * C + 1)) ^ 2 ≤ 1 / (8 * C) := by
      rw [div_pow, one_pow, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hCpos.le]
    exact h2.trans h3
  have hδ₂q : δ₂ ^ q ≤ 1 / (8 * C) := by
    have h2 : δ₂ ^ (q - 2) ≤ 1 := Real.rpow_le_one hδ₂pos.le hδ₂1 (by linarith)
    have h3 : δ₂ ^ q = δ₂ ^ (2 : ℝ) * δ₂ ^ (q - 2) := by
      rw [← Real.rpow_add' hδ₂pos.le (by linarith : (2 : ℝ) + (q - 2) ≠ 0)]
      congr 1
      ring
    have h3' : δ₂ ^ (2 : ℝ) = δ₂ ^ 2 := Real.rpow_natCast δ₂ 2
    rw [h3, h3']
    calc δ₂ ^ 2 * δ₂ ^ (q - 2) ≤ δ₂ ^ 2 * 1 := mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
      _ ≤ 1 / (8 * C) := by rw [mul_one]; exact hδ₂sq
  have hsmall : q * δ₁ + 2 * C * (δ₂ ^ 2 + δ₂ ^ q) ≤ 1 := by
    have h1 : q * δ₁ = 1 / 4 := by rw [hδ₁def]; field_simp
    have h2 : 2 * C * (δ₂ ^ 2 + δ₂ ^ q) ≤ 2 * C * (2 * (1 / (8 * C))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith [hδ₂sq, hδ₂q]
    have h3 : 2 * C * (2 * (1 / (8 * C))) = 1 / 2 := by field_simp; ring
    have h4 : (0 : ℝ) ≤ 1 / (8 * C + 1) := by positivity
    have h5 : (1 / (8 * C + 1)) ^ 2 ≤ 1 / (8 * C) := by
      rw [div_pow, one_pow, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hCpos.le]
    linarith [h1, h2, h3]
  obtain ⟨p₁, hp₁⟩ := avg2GainL1 P hd hI δ₁ hδ₁pos
  obtain ⟨p₂, hp₂⟩ := avg2GainLq P hd hI hConc hq2 hq δ₂ hδ₂pos
  refine ⟨max p₁ p₂, fun p j _ _ hp hj => ?_⟩
  intro f g
  have h1 : ∀ f g : ZMod (p ^ j) → ℂ, (∑ x : ZMod (p ^ j), g x) = 0 →
      LpNormZMod (p ^ j) 1 (polyBilinearAverageZMod Polynomial.X P (p ^ j) f g)
        ≤ δ₁ * LpNormZMod (p ^ j) 2 f * LpNormZMod (p ^ j) 2 g :=
    fun f g hg => hp₁ p j (le_trans (le_max_left _ _) hp) hj f g hg
  have h2 : ∀ f g : ZMod (p ^ j) → ℂ, (∑ x : ZMod (p ^ j), g x) = 0 →
      LpNormZMod (p ^ j) q (polyBilinearAverageZMod Polynomial.X P (p ^ j) f g)
        ≤ δ₂ * LpNormZMod (p ^ j) 2 f * LpNormZMod (p ^ j) 2 g :=
    fun f g hg => hp₂ p j (le_trans (le_max_right _ _) hp) hj f g hg
  have hcore := avg2Core P (p ^ j) (le_of_lt hq2) hδ₁pos.le hδ₂pos.le hCpos.le hTaylor h1 h2
    hsmall f g
  simpa using hcore

end

end Work.KMTPlan.A6
