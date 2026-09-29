/-
`U a = Σ_n u_n(a) Xⁿ` is the formal Beukers generating series of the
two-sided-bound chapter (`Work.C17.U`, coefficients
`u_n(a) = Submission.CDT.beukersUR a n`).  We prove that it is the formal
inverse square root of `1 - 2a·X + X²`, i.e.

`(Work.C17.U a) ^ 2 * (1 - C (2a) * X + X ^ 2) = 1`   (`Usq_mul`),

the real-parameter lift of the rational identity `beukersA_sq_mul`
(`Submission.CDT`, paper eq. (beukersA)).

The route mirrors the rational proof:
* `beukersUR_recur` — the coefficient recurrence in its "shifted" form
  `(n+1)·u_{n+1} = (2n+1)·a·u_n - n·u_{n-1}`;
* `beukersUR_ode_coeff` / `beukersUR_ode` — the first-order ODE of the paper
  (eq. (odeone)) `Q·U′ + (X - a)·U = 0` over `ℝ`, proved coefficient-wise;
* `sq_mul_eq_one_of_ode` — the abstract Leibniz argument: if
  `Q·A′ + (X - a)·A = 0`, `Q′ = -2a + 2X` and `A`, `Q` both have constant
  coefficient `1`, then `A²·Q = 1` (differentiate `A²·Q`, use the ODE, and
  conclude with `PowerSeries.derivative.ext`).
-/
import Mathlib
import Submission.Work.C17.beukersUR_defs

open PowerSeries

namespace Work.C17

noncomputable section

/-- The Beukers recurrence in "shifted" form:
`(n+1)·u_{n+1} = (2n+1)·a·u_n - n·u_{n-1}` for `u = beukersUR a`
(equivalent to `beukersUR_step` after the substitution `n ↦ n-1`). -/
lemma beukersUR_recur (a : ℝ) (n : ℕ) :
    ((n : ℝ) + 1) * Submission.CDT.beukersUR a (n + 1) =
      ((2 * (n : ℝ)) + 1) * a * Submission.CDT.beukersUR a n -
        (n : ℝ) * Submission.CDT.beukersUR a (n - 1) := by
  rcases n with _ | m
  · simp [Submission.CDT.beukersUR]
  · have h := Submission.CDT.beukersUR_step a m
    rw [show m + 1 + 1 = m + 2 by omega, show m + 1 - 1 = m by omega]
    push_cast
    linarith [h]

/-- Coefficient form of the first-order ODE (paper eq. (odeone)),
real-parameter version of `Submission.CDT.beukersA_ode_coeff`:
`coeff n ((1 - 2a·X + X²)·U′ + (X - a)·U) = 0`. -/
lemma beukersUR_ode_coeff (a : ℝ) (n : ℕ) :
    PowerSeries.coeff n (((1 : PowerSeries ℝ) - PowerSeries.C (2 * a) * PowerSeries.X + PowerSeries.X ^ 2) *
        (PowerSeries.derivative (R := ℝ) (Work.C17.U a)) + (PowerSeries.X - PowerSeries.C a) * Work.C17.U a) = 0 := by
  let F : PowerSeries ℝ := Work.C17.U a
  let dF : PowerSeries ℝ := PowerSeries.derivative (R := ℝ) (Work.C17.U a)
  have hder : ∀ m : ℕ, PowerSeries.coeff m dF =
      ((m : ℝ) + 1) * Submission.CDT.beukersUR a (m + 1) := by
    intro m
    rw [show PowerSeries.coeff m dF = PowerSeries.coeff (m + 1) (Work.C17.U a) * ((m : ℝ) + 1) from by
      simp [dF, PowerSeries.coeff_derivative]]
    rw [coeff_U]
    ring
  have hFc : ∀ m : ℕ, PowerSeries.coeff m F = Submission.CDT.beukersUR a m := by
    intro m; simp [F, coeff_U]
  change PowerSeries.coeff n
      (((1 : PowerSeries ℝ) - PowerSeries.C (2 * a) * PowerSeries.X + PowerSeries.X ^ 2) * dF
        + (PowerSeries.X - PowerSeries.C a) * F) = 0
  rw [show ((1 : PowerSeries ℝ) - PowerSeries.C (2 * a) * PowerSeries.X + PowerSeries.X ^ 2) * dF
        + (PowerSeries.X - PowerSeries.C a) * F
      = dF - PowerSeries.C (2 * a) * (PowerSeries.X * dF) + PowerSeries.X ^ 2 * dF
        + PowerSeries.X * F - PowerSeries.C a * F from by ring]
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul]
  have hXm : ∀ (g : PowerSeries ℝ) (m : ℕ),
      PowerSeries.coeff (m + 1) (PowerSeries.X * g) = PowerSeries.coeff m g := by
    intro g m
    simpa using (PowerSeries.coeff_X_pow_mul g 1 m)
  have hX2m : ∀ (g : PowerSeries ℝ) (m : ℕ),
      PowerSeries.coeff (m + 2) (PowerSeries.X ^ 2 * g) = PowerSeries.coeff m g := by
    intro g m
    exact PowerSeries.coeff_X_pow_mul g 2 m
  cases n with
  | zero =>
      have hz1 : PowerSeries.coeff 0 (PowerSeries.X * dF) = 0 := by simp
      have hz2 : PowerSeries.coeff 0 (PowerSeries.X ^ 2 * dF) = 0 := by simp
      have hz3 : PowerSeries.coeff 0 (PowerSeries.X * F) = 0 := by simp
      rw [hz1, hz2, hz3, hder 0, hFc 0,
        Submission.CDT.beukersUR_zero, Submission.CDT.beukersUR_one]
      ring
  | succ m =>
    cases m with
    | zero =>
        have hx1 : PowerSeries.coeff 1 (PowerSeries.X * dF) = PowerSeries.coeff 0 dF := by
          simpa using (hXm dF 0)
        have hx2 : PowerSeries.coeff 1 (PowerSeries.X ^ 2 * dF) = 0 := by
          simpa [pow_two, mul_assoc] using (hXm (PowerSeries.X * dF) 0)
        have hx3 : PowerSeries.coeff 1 (PowerSeries.X * F) = PowerSeries.coeff 0 F := by
          simpa using (hXm F 0)
        rw [hx1, hx2, hx3, hder 1, hder 0, hFc 1, hFc 0]
        have hs := beukersUR_recur a 1
        norm_num at hs ⊢
        linarith [hs]
    | succ k =>
        have hx1 : PowerSeries.coeff (k + 2) (PowerSeries.X * dF) = PowerSeries.coeff (k + 1) dF := by
          simpa [Nat.add_assoc] using (hXm dF (k + 1))
        have hx2 : PowerSeries.coeff (k + 2) (PowerSeries.X ^ 2 * dF) = PowerSeries.coeff k dF := by
          exact hX2m dF k
        have hx3 : PowerSeries.coeff (k + 2) (PowerSeries.X * F) = PowerSeries.coeff (k + 1) F := by
          simpa [Nat.add_assoc] using (hXm F (k + 1))
        rw [hx1, hx2, hx3, hder (k + 2), hder (k + 1), hder k, hFc (k + 2), hFc (k + 1)]
        have hs := beukersUR_recur a (k + 2)
        rw [show k + 2 - 1 = k + 1 by omega] at hs
        simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at hs ⊢
        ring_nf at hs ⊢
        linear_combination hs

/-- The first-order ODE of the paper (eq. (odeone)) for the real-parameter
Beukers series `U a`:
`(1 - 2a·X + X²)·U′ + (X - a)·U = 0` (real version of `beukersA_ode`). -/
lemma beukersUR_ode (a : ℝ) :
    ((1 : PowerSeries ℝ) - PowerSeries.C (2 * a) * PowerSeries.X + PowerSeries.X ^ 2) *
        (PowerSeries.derivative (R := ℝ) (Work.C17.U a)) +
      (PowerSeries.X - PowerSeries.C a) * Work.C17.U a = 0 := by
  apply PowerSeries.ext
  intro n
  exact beukersUR_ode_coeff a n

/-- Abstract square-root identity: if `A` solves the first-order ODE
`Q·A′ + (X - a)·A = 0` with `Q′ = -2a + 2X`, and both `A` and `Q` have
constant coefficient `1`, then `A²·Q = 1`.

(The Leibniz rule gives `(A²Q)′ = A²·(Q′ - 2(X-a)) = 0`, and the constant
term is `1`; two power series are equal when their derivatives and constant
terms agree, characteristic zero.) -/
lemma sq_mul_eq_one_of_ode {A Q : PowerSeries ℝ} {a : ℝ}
    (hode : Q * (PowerSeries.derivative (R := ℝ)) A + (PowerSeries.X - PowerSeries.C a) * A = 0)
    (hQ : (PowerSeries.derivative (R := ℝ)) Q = -PowerSeries.C (2 * a) + 2 * PowerSeries.X)
    (hA0 : PowerSeries.constantCoeff A = 1)
    (hQ0 : PowerSeries.constantCoeff Q = 1) :
    A ^ 2 * Q = 1 := by
  have hder : (PowerSeries.derivative (R := ℝ)) (A ^ 2 * Q) = 0 := by
    have hsq : (PowerSeries.derivative (R := ℝ)) (A ^ 2) = 2 * (A * (PowerSeries.derivative (R := ℝ)) A) := by
      rw [Derivation.leibniz_pow]
      simp
    have hQmul : Q * (PowerSeries.derivative (R := ℝ)) A = -((PowerSeries.X - PowerSeries.C a) * A) := by
      rw [eq_neg_iff_add_eq_zero]
      exact hode
    have hC2a : PowerSeries.C (2 * a) = (2 : PowerSeries ℝ) * PowerSeries.C a := by
      rw [map_mul,
        show PowerSeries.C (2 : ℝ) = (2 : PowerSeries ℝ) from by exact map_ofNat PowerSeries.C 2]
    calc (PowerSeries.derivative (R := ℝ)) (A ^ 2 * Q)
        = (A ^ 2) * ((PowerSeries.derivative (R := ℝ)) Q)
            + Q * ((PowerSeries.derivative (R := ℝ)) (A ^ 2)) := by
          rw [Derivation.leibniz]; simp
      _ = (A ^ 2) * (-PowerSeries.C (2 * a) + 2 * PowerSeries.X)
            + Q * (2 * (A * (PowerSeries.derivative (R := ℝ)) A)) := by rw [hQ, hsq]
      _ = (A ^ 2) * (-PowerSeries.C (2 * a) + 2 * PowerSeries.X)
            + 2 * A * (Q * (PowerSeries.derivative (R := ℝ)) A) := by ring
      _ = (A ^ 2) * (-PowerSeries.C (2 * a) + 2 * PowerSeries.X)
            - 2 * A * ((PowerSeries.X - PowerSeries.C a) * A) := by rw [hQmul]; ring
      _ = 0 := by rw [hC2a]; ring
  exact PowerSeries.derivative.ext (by rw [hder, PowerSeries.derivative_one])
    (by simp [hA0, hQ0])

theorem Usq_mul (a : ℝ) :
    (Work.C17.U a) ^ 2 * (1 - PowerSeries.C (2 * a) * PowerSeries.X + PowerSeries.X ^ 2) = 1 := by
  apply sq_mul_eq_one_of_ode (A := Work.C17.U a)
    (Q := 1 - PowerSeries.C (2 * a) * PowerSeries.X + PowerSeries.X ^ 2)
  · exact beukersUR_ode a
  · simp [PowerSeries.derivative_C, PowerSeries.derivative_X]
  · exact coefficient_zero_U a
  · simp

end

end Work.C17
