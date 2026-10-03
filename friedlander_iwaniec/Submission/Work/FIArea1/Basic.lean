/-
# `Submission.Work.FIArea1.Basic` — AREA 1 (*FI* §5): the structural layer

This module is the first layer of the proof of `Work.FITop3.Area1` (area 1 of the round-3
contract, *FI* §5).  See `NOTES.md` in this directory for the complete route: the two conjuncts of
`Area1` are *FI* (5.10) (removal of the coprimality constraint) and (5.22) (`D = D* + error`), and
the paper's proof of (5.10) reduces to

* the structure of the coefficient's support (`IsBetaCoeff` gives `β z = q p μ(n_z) γ(n_z;C)` on
  the polar box, so `β z ≠ 0` forces `n_z = gnorm z` squarefree, hence `(r,s) = 1` and
  `p ∤ r, p ∤ s` for every prime `p | n_z`), and
* for a non-coprime pair `(w,z)` a *common rational prime* `p | gnorm w`, `p | gnorm z` whose
  lattice-theoretic consequences are the content of `Count.lean`.

Everything here is elementary; the lemmas are stated in the vocabulary of
`Submission.Work.FITop3.Defs3`.
-/
import Mathlib
import Submission.Work.FITop3.Defs3
import Submission.Work.FITop3.Smooth
import Submission.Work.FITop3.Smooth.sm_props
import Submission.Work.FITop3.Majorant.majorant_props
import Submission.Work.FITop3.Witness.exists_primary_norm

set_option autoImplicit false

namespace Work.FIArea1

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. The Gaussian norm in coordinates -/

/-- `gnorm` is the absolute value of the field norm; in coordinates
`gnorm ⟨r,s⟩ = r² + s²`. -/
lemma gnorm_int (z : GaussianInt) : (Work.FIPlan.gnorm z : ℤ) = z.re ^ 2 + z.im ^ 2 := by
  have hnorm : z.norm = z.re ^ 2 + z.im ^ 2 := by rw [Zsqrtd.norm_def]; ring
  rw [Work.FIPlan.gnorm, hnorm,
    Int.natAbs_of_nonneg (by positivity : (0 : ℤ) ≤ z.re ^ 2 + z.im ^ 2)]

/-- `gnorm` in coordinates, as a natural number. -/
lemma gnorm_coords (z : GaussianInt) : Work.FIPlan.gnorm z = z.re.natAbs ^ 2 + z.im.natAbs ^ 2 := by
  apply Nat.cast_injective (R := ℤ)
  rw [gnorm_int]
  push_cast
  rw [← Int.natAbs_sq]
  rw [show (z.im : ℤ) ^ 2 = ((z.im.natAbs ^ 2 : ℕ) : ℤ) from by
    rw [← Int.natAbs_sq]; push_cast; ring_nf]
  push_cast
  ring_nf

/-- `gnorm` is multiplicative. -/
lemma gnorm_mul (w z : GaussianInt) :
    Work.FIPlan.gnorm (w * z) = Work.FIPlan.gnorm w * Work.FIPlan.gnorm z := by
  simp only [Work.FIPlan.gnorm, Zsqrtd.norm_mul, Int.natAbs_mul]

/-- `gnorm` of an integer cast. -/
lemma gnorm_intCast (n : ℤ) : Work.FIPlan.gnorm ((n : ℤ) : GaussianInt) = n.natAbs ^ 2 := by
  apply Nat.cast_injective (R := ℤ)
  rw [gnorm_int]
  have hre : (((n : ℤ) : GaussianInt)).re = n := Zsqrtd.re_ofInt n
  have him : (((n : ℤ) : GaussianInt)).im = 0 := Zsqrtd.im_ofInt n
  rw [hre, him]
  push_cast
  rw [sq_abs]
  ring

/-- `gnorm (n z) = n² gnorm z` for an integer `n`. -/
lemma gnorm_mul_intCast (n : ℤ) (z : GaussianInt) :
    Work.FIPlan.gnorm (((n : ℤ) : GaussianInt) * z) = n.natAbs ^ 2 * Work.FIPlan.gnorm z := by
  rw [gnorm_mul, gnorm_intCast]

/-- If an integer `p` divides both coordinates of `z`, then `p² ∣ gnorm z`. -/
lemma sq_dvd_gnorm_of_dvd_coords {z : GaussianInt} {p : ℤ} (h1 : p ∣ z.re) (h2 : p ∣ z.im) :
    p.natAbs ^ 2 ∣ Work.FIPlan.gnorm z := by
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  have hz : z = (p : GaussianInt) * (⟨a, b⟩ : GaussianInt) := by
    ext <;> simp [ha, hb]
  rw [hz, gnorm_mul, gnorm_intCast]
  exact dvd_mul_right _ _

/-! ## 2. Squarefree norms force coprime coordinates (the paper's `(r,s) = 1`) -/

/-- **The paper's `(r,s) = 1`.**  A squarefree `|z|²` forces the coordinates of `z` to be coprime:
a common prime `ℓ` would give `ℓ² ∣ |z|²`. -/
lemma coprime_coords_of_sqfree {z : GaussianInt} (h : Squarefree (Work.FIPlan.gnorm z)) :
    Nat.Coprime z.re.natAbs z.im.natAbs := by
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra hne
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
  have h1 : p ∣ z.re.natAbs := hpd.trans (Nat.gcd_dvd_left _ _)
  have h2 : p ∣ z.im.natAbs := hpd.trans (Nat.gcd_dvd_right _ _)
  have h1' : (p : ℤ) ∣ z.re := Int.natCast_dvd.mpr h1
  have h2' : (p : ℤ) ∣ z.im := Int.natCast_dvd.mpr h2
  have hsq : p ^ 2 ∣ Work.FIPlan.gnorm z := sq_dvd_gnorm_of_dvd_coords h1' h2'
  exact (Nat.squarefree_iff_prime_squarefree.mp h p hp) (by rwa [pow_two] at hsq)

/-- If `p` is a prime divisor of a squarefree `|z|²`, then `p` divides neither coordinate.  (This
is the paper's "note that `p ∤ rs`".) -/
lemma prime_not_dvd_coords {z : GaussianInt} (h : Squarefree (Work.FIPlan.gnorm z)) {p : ℕ}
    (hp : p.Prime) (hpd : p ∣ Work.FIPlan.gnorm z) : ¬p ∣ z.re.natAbs ∧ ¬p ∣ z.im.natAbs := by
  have hpc : (p : ℤ) ∣ (Work.FIPlan.gnorm z : ℤ) := Int.natCast_dvd_natCast.mpr hpd
  have hgi : (Work.FIPlan.gnorm z : ℤ) = z.re ^ 2 + z.im ^ 2 := gnorm_int z
  have key : ∀ y : ℤ, (p : ℤ) ∣ y ^ 2 → p ∣ y.natAbs := by
    intro y hy
    have h1 : p ∣ (y ^ 2).natAbs := Int.natCast_dvd.mp hy
    rw [Int.natAbs_pow] at h1
    exact hp.dvd_of_dvd_pow h1
  constructor <;> intro hd
  · have hpr : (p : ℤ) ∣ z.re := Int.natCast_dvd.mpr hd
    have hpr2 : (p : ℤ) ∣ z.re ^ 2 := by
      obtain ⟨k, hk⟩ := hpr; exact ⟨(p : ℤ) * k ^ 2, by rw [hk]; ring⟩
    have hsum : (p : ℤ) ∣ z.re ^ 2 + z.im ^ 2 := by rw [← hgi]; exact hpc
    have him : p ∣ z.im.natAbs := key z.im ((dvd_add_right hpr2).mp hsum)
    have him' : (p : ℤ) ∣ z.im := Int.natCast_dvd.mpr him
    have : p ^ 2 ∣ Work.FIPlan.gnorm z := sq_dvd_gnorm_of_dvd_coords hpr him'
    exact (Nat.squarefree_iff_prime_squarefree.mp h p hp) (by rwa [pow_two] at this)
  · have hpr : (p : ℤ) ∣ z.im := Int.natCast_dvd.mpr hd
    have hpr2 : (p : ℤ) ∣ z.im ^ 2 := by
      obtain ⟨k, hk⟩ := hpr; exact ⟨(p : ℤ) * k ^ 2, by rw [hk]; ring⟩
    have hsum : (p : ℤ) ∣ z.im ^ 2 + z.re ^ 2 := by rw [add_comm]; rw [← hgi]; exact hpc
    have him : p ∣ z.re.natAbs := key z.re ((dvd_add_right hpr2).mp hsum)
    have him' : (p : ℤ) ∣ z.re := Int.natCast_dvd.mpr him
    have : p ^ 2 ∣ Work.FIPlan.gnorm z := sq_dvd_gnorm_of_dvd_coords him' hpr
    exact (Nat.squarefree_iff_prime_squarefree.mp h p hp) (by rwa [pow_two] at this)

/-- A primary Gaussian integer has odd norm (`r` odd, `s` even): this is what makes the modulus
`p` of the paper's local count odd. -/
lemma odd_gnorm_of_primary {z : GaussianInt} (hz : Work.FIPlan.IsPrimary z) :
    Odd (Work.FIPlan.gnorm z) := by
  obtain ⟨h1, h2, -⟩ := hz
  have h1' : Odd z.re.natAbs := h1.natAbs
  have h2' : Even z.im.natAbs := h2.natAbs
  obtain ⟨a, ha⟩ := h1'
  obtain ⟨b, hb⟩ := h2'
  rw [gnorm_coords, ha, hb]
  exact ⟨2 * a ^ 2 + 2 * a + 2 * b ^ 2, by ring⟩

/-! ## 3. The kernel `Z(Re wz)` of the bilinear form -/

/-- `‖Zc w z‖ ≤ 2`: the square indicator is `1` at `0`, `2` at non-zero squares and `0` off the
squares (paper §3). -/
lemma Zc_norm_le_two (w z : GaussianInt) : ‖Work.FITop3.Zc w z‖ ≤ 2 := by
  have h : Work.FIPlan.Zint (Work.FIPlan.cForm w z) ≤ 2 := by
    unfold Work.FIPlan.Zint
    split_ifs with hb
    · simp
    · unfold Work.FIPlan.Zb
      split_ifs <;> omega
  simp only [Work.FITop3.Zc, Complex.norm_natCast]
  exact_mod_cast h

/-- `Zint b ≠ 0` means that `b` is a square. -/
lemma Zint_ne_zero_imp_sq (b : ℤ) (h : Work.FIPlan.Zint b ≠ 0) : ∃ c : ℤ, b = c ^ 2 := by
  have hb : ¬b < 0 := by
    intro hlt
    exact h (by unfold Work.FIPlan.Zint; rw [if_pos hlt])
  have hb0 : 0 ≤ b := le_of_not_gt hb
  unfold Work.FIPlan.Zint at h
  rw [if_neg hb] at h
  unfold Work.FIPlan.Zb at h
  split_ifs at h with h0 hs
  · exact ⟨0, by simp [Int.natAbs_eq_zero.mp h0]⟩
  · refine ⟨(Nat.sqrt b.natAbs : ℤ), ?_⟩
    have hsq : (((Nat.sqrt b.natAbs : ℕ) : ℤ)) ^ 2 = (b.natAbs : ℤ) := by
      rw [← Nat.cast_pow, hs]
    rw [hsq]
    exact (Int.natAbs_of_nonneg hb0).symm
  · exact absurd h (by norm_num)

/-- `Zc w z ≠ 0` means that `cForm w z = Re(wz)` is a square. -/
lemma Zc_ne_zero_imp_sq (w z : GaussianInt) (h : Work.FITop3.Zc w z ≠ 0) :
    ∃ c : ℤ, Work.FIPlan.cForm w z = c ^ 2 := by
  refine Zint_ne_zero_imp_sq _ ?_
  intro h0
  exact h (by simp [Work.FITop3.Zc, h0])

/-- Cauchy–Schwarz-in-the-line: `(Re wz)² ≤ |w|² |z|²`. -/
lemma cForm_sq_le (w z : GaussianInt) :
    ((Work.FIPlan.cForm w z) ^ 2 : ℤ) ≤ (Work.FIPlan.gnorm w : ℤ) * (Work.FIPlan.gnorm z : ℤ) := by
  have h : (Work.FIPlan.cForm w z) ^ 2 ≤ (Work.FIPlan.gnorm (w * z) : ℤ) := by
    rw [gnorm_int]
    simp only [Work.FIPlan.cForm]
    nlinarith [sq_nonneg ((w * z).im)]
  have h2 : (Work.FIPlan.gnorm (w * z) : ℤ) =
      (Work.FIPlan.gnorm w : ℤ) * (Work.FIPlan.gnorm z : ℤ) := by
    simp only [Work.FIPlan.gnorm, Zsqrtd.norm_mul, Int.natAbs_mul]
    push_cast
    ring
  rwa [h2] at h

/-! ## 4. Non-coprime pairs have a common rational prime -/

/-- **A common rational prime.**  If `w` and `z` are not coprime in `ℤ[i]`, then some rational
prime divides both norms.  (Proof: `ℤ[i]` is a PID, so `¬IsCoprime` gives a common non-unit
divisor `d`; `gnorm d ≥ 2` has a prime divisor `p`, and multiplicativity of `gnorm` gives
`p ∣ gnorm w`, `p ∣ gnorm z`.)  This replaces the paper's "`π | w`, `π | z` for a Gaussian prime
`π`", and needs no splitting theory of `ℤ[i]`.) -/
lemma common_prime_of_not_coprime {w z : GaussianInt}
    (h : ¬Work.FIPlan.GaussCoprime w z) :
    ∃ p : ℕ, p.Prime ∧ p ∣ Work.FIPlan.gnorm w ∧ p ∣ Work.FIPlan.gnorm z := by
  rw [Work.FIPlan.GaussCoprime] at h
  have hrp : ¬IsRelPrime w z := fun hc => h ((isRelPrime_iff_isCoprime).mp hc)
  rw [IsRelPrime] at hrp
  push Not at hrp
  obtain ⟨d, hdw, hdz, hdu⟩ := hrp
  obtain ⟨w', hw'⟩ := hdw
  obtain ⟨z', hz'⟩ := hdz
  have hg : Work.FIPlan.gnorm d ∣ Work.FIPlan.gnorm w := by
    rw [hw', gnorm_mul]; exact Nat.dvd_mul_right _ _
  have hg' : Work.FIPlan.gnorm d ∣ Work.FIPlan.gnorm z := by
    rw [hz', gnorm_mul]; exact Nat.dvd_mul_right _ _
  have hne : Work.FIPlan.gnorm d ≠ 1 := fun h1 => hdu (Zsqrtd.norm_eq_one_iff.mp h1)
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
  exact ⟨p, hp, hpd.trans hg, hpd.trans hg'⟩

/-! ## 5. The structure of the support of `β` -/

/-- **The support of `β`.**  For a coefficient `β` of (4.13)+(5.13) (represented by
`IsBetaCoeff`) and `β z ≠ 0`, the norm `n_z = |z|²` is *squarefree*, the point `z` lies in the
polar box (5.14), and `n_z` is free of primes `≤ P`.  In particular (with `coprime_coords_of_sqfree`
and `prime_not_dvd_coords`) the hypotheses of the lattice count of `Count.lean` hold for every
prime `p ∣ n_z`. -/
lemma beta_ne_zero_structure {Pa : Work.FITop.Params} {φ : ℝ} {β : GaussianInt → ℂ}
    (h : Work.FITop3.IsBetaCoeff Pa φ β) {z : GaussianInt} (hz : β z ≠ 0) :
    Squarefree (Work.FIPlan.gnorm z) ∧ Work.FITop3.InPolarBox Pa φ z ∧
      Work.FITop3.NoSmallPrimes Pa z := by
  obtain ⟨q, p, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, hβ⟩ := h
  have hcond : Work.FITop3.InPolarBox Pa φ z ∧ Work.FITop3.NoSmallPrimes Pa z ∧
      (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ) := by
    by_contra hc
    rw [hβ z, if_neg hc] at hz
    exact hz rfl
  rw [hβ z, if_pos hcond] at hz
  have hmu : (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ) ≠ 0 := by
    intro h0
    exact hz (by rw [h0]; ring)
  have hmu' : ArithmeticFunction.moebius (Work.FIPlan.gnorm z) ≠ 0 := by
    intro h0; exact hmu (by rw [h0]; norm_num)
  exact ⟨ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hmu', hcond.1, hcond.2.1⟩

/-- `‖β z‖ ≤ τ(|z|²)` (the paper's `|β_z| ≤ τ(n)`, from `γ(n;C) = Σ_{d|n} μ(d)`). -/
lemma norm_beta_le_divisors_card {Pa : Work.FITop.Params} {φ : ℝ} {β : GaussianInt → ℂ}
    (h : Work.FITop3.IsBetaCoeff Pa φ β) (z : GaussianInt) :
    ‖β z‖ ≤ ((Work.FIPlan.gnorm z).divisors.card : ℝ) :=
  h.toBoxCoeff.1 z

end

end Work.FIArea1
