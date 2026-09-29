import Mathlib
import Submission.Commons.Algebra.Polynomial.eulerOperator_factor

namespace Commons.Algebra.Polynomial

/-!
**The Euler cascade divisibility (the Frobenius leading-term estimate).**

Setting: `f = p/q ∈ K(X)`, `z = X - C α` (so `z.derivative = 1`), `N = C (rm_α p - rm_α q)`,
`F j` the falling factorials of `N` (`F 0 = 1`, `F (j+1) = F j * (N - j)`, each `F j` a
*constant* polynomial), and `C_j` the numerator of the `j`-th derivative of `f`:
`C_0 = p`, `C_{j+1} = C_j' * q - C (j+1) * (C_j * q')`, so that `f^{(j)} = C_j / q^{j+1}`.
Write `D_j = z^j * C_j - F_j * p * q^j`; then `D_j / q^{j+1} = z^j f^{(j)} - (N)_j f`.

The recursion (provable by `ring`; already formalized elsewhere as `DbN_rec`):

  `D_{j+1} = F_j * q^j * (z * (p'q - p q') - N * p q)
              + z * D_j' * q - (j+1) * z * D_j * q' - j * D_j * q`

The claim: `z ^ (rm_α p + j * rm_α q + 1) ∣ D_j` for all `j`.

Sketch of the induction step, with `a = rm_α p`, `b = rm_α q`:
* `z^(a+b+1) ∣ z*(p'q - pq') - N*p*q` (this is `Commons.Algebra.Polynomial.eulerOperator_factor`).
  Also `z^b ∣ q` (`Polynomial.pow_rootMultiplicity_dvd`).  So the first summand is
  divisible by `z^(a+(j+1)b+1)`.
* Write `D_j = z^(a+jb+1) * u` (induction hypothesis) and `q = z^b * q₁`.  Then
  `z*D_j'*q - (j+1)*z*D_j*q' - j*D_j*q`
  ` = z^(a+jb+1) * ((a+jb+1-j)*u*q₁ + z*(z*u'*q₁ - (j+1)*u*(b*q₁ + z*q₁')))`
  up to the substitution `q = z^b*q₁`; the bracket is divisible by `z^b`, which gives
  divisibility by `z^(a+(j+1)b+1)`.
-/

/-- The "power rule with a factor", in the form
`z * (z^n * u)' = z^n * (n * u + z * u')`, valid when `z' = 1`. -/
lemma z_mul_deriv_pow_mul {R : Type*} [CommRing R] (z u : Polynomial R)
    (hz : z.derivative = 1) (n : ℕ) :
    z * (z ^ n * u).derivative = z ^ n * ((n : Polynomial R) * u + z * u.derivative) := by
  have key : z * (z ^ n).derivative = (n : Polynomial R) * z ^ n := deriv_pow_mul_self z hz n
  calc z * (z ^ n * u).derivative
      = z * ((z ^ n).derivative * u + z ^ n * u.derivative) := by
        rw [Polynomial.derivative_mul]
      _ = (z * (z ^ n).derivative) * u + (z * (z ^ n)) * u.derivative := by ring
      _ = ((n : Polynomial R) * z ^ n) * u + (z ^ n * z) * u.derivative := by
        rw [key, mul_comm z (z ^ n)]
      _ = z ^ n * ((n : Polynomial R) * u + z * u.derivative) := by ring

/-- One step of the cascade, isolated: from the divisibility of `D_j` and of the
Euler expression together with `z^b ∣ q`, obtain the divisibility of `D_{j+1}`'s
explicit expression. -/
lemma cascade_succ {R : Type*} [CommRing R] (z : Polynomial R) (hz : z.derivative = 1)
    (q : Polynomial R) (b : ℕ) (hqb : z ^ b ∣ q) (a : ℕ) (Fj : Polynomial R)
    (j : ℕ) (Dj E : Polynomial R)
    (hDj : z ^ (a + j * b + 1) ∣ Dj)
    (hE : z ^ (a + b + 1) ∣ E) :
    z ^ (a + (j + 1) * b + 1) ∣
      Fj * q ^ j * E + z * Dj.derivative * q
        - ((j : Polynomial R) + 1) * z * Dj * q.derivative - (j : Polynomial R) * Dj * q := by
  have hexp : a + (j + 1) * b + 1 = a + j * b + 1 + b := by ring
  rw [hexp]
  have hP1 : z ^ (a + j * b + 1 + b) ∣ Fj * q ^ j * E := by
    have hdiv : z ^ (a + j * b + 1 + b) ∣ E * q ^ j := by
      have h2 : z ^ (j * b) ∣ q ^ j := by
        have hzb : z ^ (j * b) = (z ^ b) ^ j := by rw [← pow_mul, Nat.mul_comm]
        rw [hzb]
        exact pow_dvd_pow_of_dvd hqb j
      have hprod : z ^ (a + b + 1) * z ^ (j * b) ∣ E * q ^ j := mul_dvd_mul hE h2
      have hze : z ^ (a + b + 1) * z ^ (j * b) = z ^ (a + j * b + 1 + b) := by
        rw [← pow_add]; congr 1; ring
      rwa [hze] at hprod
    have hre : Fj * q ^ j * E = (E * q ^ j) * Fj := by ring
    rw [hre]
    exact hdiv.mul_right Fj
  have hP2 : z ^ (a + j * b + 1 + b) ∣
      z * Dj.derivative * q - ((j : Polynomial R) + 1) * z * Dj * q.derivative
        - (j : Polynomial R) * Dj * q := by
    have hDj' := hDj
    have hqb' := hqb
    obtain ⟨u, hu⟩ := hDj'
    obtain ⟨q1, hq1⟩ := hqb'
    have hX1 : z ^ (a + j * b + 1 + b) ∣ z * Dj.derivative * q := by
      have h1 : z ^ (a + j * b + 1) ∣ z * Dj.derivative := by
        rw [hu]
        exact ⟨((a + j * b + 1 : ℕ) : Polynomial R) * u + z * u.derivative,
          z_mul_deriv_pow_mul z u hz (a + j * b + 1)⟩
      have hprod : z ^ (a + j * b + 1) * z ^ b ∣ z * Dj.derivative * q :=
        mul_dvd_mul h1 hqb
      rwa [← pow_add] at hprod
    have hX2 : z ^ (a + j * b + 1 + b) ∣ (j : Polynomial R) * Dj * q := by
      have hprod : z ^ (a + j * b + 1) * z ^ b ∣ Dj * q := mul_dvd_mul hDj hqb
      rw [← pow_add] at hprod
      simpa only [mul_assoc] using hprod.mul_left (j : Polynomial R)
    have hY : z ^ (a + j * b + 1 + b) ∣ ((j : Polynomial R) + 1) * Dj * (z * q.derivative) := by
      have hq' : z ^ b ∣ z * q.derivative := by
        rw [hq1]
        exact ⟨((b : ℕ) : Polynomial R) * q1 + z * q1.derivative, z_mul_deriv_pow_mul z q1 hz b⟩
      have hprod : z ^ (a + j * b + 1) * z ^ b ∣ Dj * (z * q.derivative) :=
        mul_dvd_mul hDj hq'
      rw [← pow_add] at hprod
      simpa only [mul_assoc] using hprod.mul_left ((j : Polynomial R) + 1)
    have h1 : z ^ (a + j * b + 1 + b) ∣
        z * Dj.derivative * q - ((j : Polynomial R) + 1) * Dj * (z * q.derivative) :=
      dvd_sub hX1 hY
    have h2 : z ^ (a + j * b + 1 + b) ∣
        (z * Dj.derivative * q - ((j : Polynomial R) + 1) * Dj * (z * q.derivative))
          - (j : Polynomial R) * Dj * q := dvd_sub h1 hX2
    convert h2 using 1
    ring
  have hgoal : (Fj * q ^ j * E + z * Dj.derivative * q
        - ((j : Polynomial R) + 1) * z * Dj * q.derivative - (j : Polynomial R) * Dj * q)
      = Fj * q ^ j * E + (z * Dj.derivative * q
        - ((j : Polynomial R) + 1) * z * Dj * q.derivative - (j : Polynomial R) * Dj * q) := by
    ring
  rw [hgoal]
  exact dvd_add hP1 hP2

theorem euler_cascade_dvd {K : Type*} [Field K]
    (z : Polynomial K) (hz : z.derivative = 1) (p q : Polynomial K) (α : K)
    (hα : z = Polynomial.X - Polynomial.C α) (N : Polynomial K)
    (F : ℕ → Polynomial K) (hF0 : F 0 = 1) (hFc : ∀ j, (F j).derivative = 0)
    (hF : ∀ j, F (j + 1) = F j * (N - (j : Polynomial K)))
    (hN : N = Polynomial.C ((((Polynomial.rootMultiplicity α p : ℤ) - Polynomial.rootMultiplicity α q : ℤ)) : K))
    (D : ℕ → Polynomial K)
    (hDE : ∀ j, D j = z ^ j * (Nat.rec (motive := fun _ => Polynomial K) p
        (fun k ih => ih.derivative * q - Polynomial.C ((k : ℕ) + 1 : K) * (ih * q.derivative)) j)
        - F j * (p * q ^ j))
    (hD : ∀ j, D (j + 1) = F j * q ^ j * (z * (p.derivative * q - p * q.derivative) - N * (p * q))
        + z * (D j).derivative * q
        - ((j : Polynomial K) + 1) * z * (D j) * q.derivative
        - (j : Polynomial K) * (D j) * q) :
    ∀ j : ℕ, z ^ (Polynomial.rootMultiplicity α p + j * Polynomial.rootMultiplicity α q + 1) ∣ D j := by
  have hEuler : z ^ (Polynomial.rootMultiplicity α p + Polynomial.rootMultiplicity α q + 1) ∣
      z * (p.derivative * q - p * q.derivative) - N * (p * q) := by
    obtain ⟨r, hr⟩ := eulerOperator_factor p q α
    refine ⟨r, ?_⟩
    rw [hN, hα]
    exact hr
  have hqb : z ^ Polynomial.rootMultiplicity α q ∣ q := by
    rw [hα]
    exact Polynomial.pow_rootMultiplicity_dvd q α
  intro j
  induction j with
  | zero =>
    rw [hDE 0]
    simp only [pow_zero, Nat.rec_zero, hF0, one_mul, mul_one, sub_self]
    exact dvd_zero _
  | succ j ih =>
    have hstep := cascade_succ z hz q (Polynomial.rootMultiplicity α q) hqb
      (Polynomial.rootMultiplicity α p) (F j) j (D j)
      (z * (p.derivative * q - p * q.derivative) - N * (p * q)) ih hEuler
    rw [hD j]
    exact hstep

end Commons.Algebra.Polynomial
