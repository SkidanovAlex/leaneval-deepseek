import Mathlib
import Submission.CDTPlan.InterfacesC
import Submission.CDT.LogMIdentities

/-!
# Area CLift — infrastructure for the continuation of `P` along the lift `Φ`

This module collects the definitions shared by the lemmas of area `CLift`:

* `evA` — the evaluation of a rational power series at a complex point;
* the explicit polynomial data `P2poly`, `P1poly`, `P0poly`, `Rhpoly` underlying the
  operator `logPAODE` of `Submission.CDT.LogMIdentities`;
* the gauge polynomials `Muq`, `Nq`, `Mcq` removing the apparent singularity at `x = -1`;
* the radii `r0`, `r1` and the matrix/vector `A₀`, `c₀` of the pulled-back system.
-/

namespace Work.CLift

open PowerSeries Submission.CDTPlan
open scoped BigOperators

noncomputable section

/-- Evaluation of a rational power series at a complex point. -/
def evA (A : PowerSeries ℚ) (x : ℂ) : ℂ := ∑' k : ℕ, ((PowerSeries.coeff k A : ℚ) : ℂ) * x ^ k

/-! ## Basic evaluation lemmas -/

lemma evA_zero (x : ℂ) : evA 0 x = 0 := by
  simp [evA]

lemma evA_C (q : ℚ) (x : ℂ) : evA (PowerSeries.C q) x = (q : ℂ) := by
  rw [evA, tsum_eq_single 0]
  · simp
  · intro k hk
    simp [PowerSeries.coeff_C, hk]

lemma evA_X (x : ℂ) : evA (PowerSeries.X : PowerSeries ℚ) x = x := by
  rw [evA, tsum_eq_single 1]
  · simp
  · intro k hk
    rw [PowerSeries.coeff_X]
    simp [hk]

lemma evA_one (x : ℂ) : evA (1 : PowerSeries ℚ) x = 1 := by
  rw [evA, tsum_eq_single 0]
  · simp
  · intro k hk
    rw [PowerSeries.coeff_one]
    simp [hk]

lemma evA_C_mul_X_pow (q : ℚ) (j : ℕ) (x : ℂ) :
    evA (PowerSeries.C q * PowerSeries.X ^ j : PowerSeries ℚ) x = (q : ℂ) * x ^ j := by
  rw [evA, tsum_eq_single j]
  · simp
  · intro k hk
    rw [PowerSeries.coeff_C_mul_X_pow]
    simp [hk]

lemma evA_add (A B : PowerSeries ℚ) (x : ℂ)
    (hA : Summable fun k => ((PowerSeries.coeff k A : ℚ) : ℂ) * x ^ k)
    (hB : Summable fun k => ((PowerSeries.coeff k B : ℚ) : ℂ) * x ^ k) :
    evA (A + B) x = evA A x + evA B x := by
  rw [evA, evA, evA, ← Summable.tsum_add hA hB]
  apply tsum_congr
  intro k
  simp only [map_add]
  push_cast
  ring

lemma evA_mul (A B : PowerSeries ℚ) (x : ℂ)
    (hA : Summable fun k => ‖((PowerSeries.coeff k A : ℚ) : ℂ) * x ^ k‖)
    (hB : Summable fun k => ‖((PowerSeries.coeff k B : ℚ) : ℂ) * x ^ k‖) :
    evA (A * B) x = evA A x * evA B x := by
  rw [evA, evA, evA, tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hA hB]
  apply tsum_congr
  intro n
  rw [PowerSeries.coeff_mul]
  have hcast : ((∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, (PowerSeries.coeff p.1 A) * (PowerSeries.coeff p.2 B) : ℚ) : ℂ)
      = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
          (((PowerSeries.coeff p.1 A : ℚ) : ℂ) * ((PowerSeries.coeff p.2 B : ℚ) : ℂ)) := by
    push_cast; ring
  rw [hcast]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun k l => (((PowerSeries.coeff k A : ℚ) : ℂ) * ((PowerSeries.coeff l B : ℚ) : ℂ)))]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  have hkn : k ≤ n := by omega
  rw [show (x : ℂ) ^ n = x ^ k * x ^ (n - k) by rw [← pow_add, Nat.add_sub_cancel' hkn]]
  ring

/-! ## The data of Theorem C -/

variable (m n : ℕ) (ra rb rab r0 : ℤ)

/-- `a = 2m+1` (as a rational). -/
def aa : ℚ := (2 * m + 1 : ℕ)
/-- `b = 2n+1` (as a rational). -/
def bb : ℚ := (2 * n + 1 : ℕ)

/-- The power series `P` of Theorem C. -/
def Pt : PowerSeries ℚ := PC m n ra rb rab r0

/-- The complex coefficients of `P`. -/
@[irreducible] def coef (k : ℕ) : ℂ := ((PowerSeries.coeff k (Pt m n ra rb rab r0) : ℚ) : ℂ)

/-! ### The polynomial coefficients of the operator `logPAODE` -/

/-- `P2(x) = (x-1)x(x+1)Q4(x)`. -/
def P2p (x : ℂ) : ℂ :=
  (x - 1) * x * (x + 1) *
    (1 - 4 * (aa m : ℂ) * (bb n : ℂ) * x
      + (4 * (aa m : ℂ) ^ 2 + 4 * (bb n : ℂ) ^ 2 - 2) * x ^ 2
      - 4 * (aa m : ℂ) * (bb n : ℂ) * x ^ 3 + x ^ 4)

/-- `P1(x)`. -/
def P1p (x : ℂ) : ℂ :=
  -1 + 8 * (aa m : ℂ) * (bb n : ℂ) * x
    + (5 - 12 * (aa m : ℂ) ^ 2 - 12 * (bb n : ℂ) ^ 2) * x ^ 2
    + 16 * (aa m : ℂ) * (bb n : ℂ) * x ^ 3
    + (4 * (aa m : ℂ) ^ 2 + 4 * (bb n : ℂ) ^ 2 - 7) * x ^ 4
    - 8 * (aa m : ℂ) * (bb n : ℂ) * x ^ 5 + 3 * x ^ 6

/-- `P0(x)`. -/
def P0p (x : ℂ) : ℂ :=
  (aa m : ℂ) * (bb n : ℂ) + (1 - 3 * (aa m : ℂ) ^ 2 - 3 * (bb n : ℂ) ^ 2) * x
    + 8 * (aa m : ℂ) * (bb n : ℂ) * x ^ 2
    - ((aa m : ℂ) ^ 2 + (bb n : ℂ) ^ 2 + 2) * x ^ 3
    - (aa m : ℂ) * (bb n : ℂ) * x ^ 4 + x ^ 5

/-- The right-hand side `r_a·Ra + r_b·Rb + r_ab·Rab`. -/
def Rhp (x : ℂ) : ℂ :=
  (ra : ℂ) * (-(bb n : ℂ) + 3 * (aa m : ℂ) * x - 3 * (bb n : ℂ) * x ^ 2 + (aa m : ℂ) * x ^ 3)
    + (rb : ℂ) * (-(aa m : ℂ) + 3 * (bb n : ℂ) * x - 3 * (aa m : ℂ) * x ^ 2 + (bb n : ℂ) * x ^ 3)
    + (rab : ℂ) * (-1 + 2 * x ^ 2 - x ^ 4)

/-- `R2 = (x-1)xQ4`, so that `P2 = (x+1)R2`. -/
def R2p (x : ℂ) : ℂ :=
  (x - 1) * x *
    (1 - 4 * (aa m : ℂ) * (bb n : ℂ) * x
      + (4 * (aa m : ℂ) ^ 2 + 4 * (bb n : ℂ) ^ 2 - 2) * x ^ 2
      - 4 * (aa m : ℂ) * (bb n : ℂ) * x ^ 3 + x ^ 4)

/-- `Muq = Mu/(x+1)^2` with `Mu = -P1/2 - P0 - P2/4`. -/
def Muqp (x : ℂ) : ℂ :=
  1/2 - 7/4 * x + 1/2 * x ^ 2 + 2 * x ^ 3 - x ^ 4 - 1/4 * x ^ 5
    - (aa m : ℂ) * (bb n : ℂ) - 2 * (aa m : ℂ) * (bb n : ℂ) * x
    - 4 * (aa m : ℂ) * (bb n : ℂ) * x ^ 2 + 2 * (aa m : ℂ) * (bb n : ℂ) * x ^ 3
    + (aa m : ℂ) * (bb n : ℂ) * x ^ 4
    + (3 * (aa m : ℂ) ^ 2 + 3 * (bb n : ℂ) ^ 2) * x
    - ((aa m : ℂ) ^ 2 + (bb n : ℂ) ^ 2) * x ^ 3

/-- `Nq = -(P1+R2)/(x+1)`. -/
def Nqp (x : ℂ) : ℂ :=
  1 - 8 * (aa m : ℂ) * (bb n : ℂ) * x
    + (-6 + 12 * (bb n : ℂ) ^ 2 + 4 * (aa m : ℂ) * (bb n : ℂ) + 12 * (aa m : ℂ) ^ 2) * x ^ 2
    + (4 - 8 * (bb n : ℂ) ^ 2 - 16 * (aa m : ℂ) * (bb n : ℂ) - 8 * (aa m : ℂ) ^ 2) * x ^ 3
    + (5 + 12 * (aa m : ℂ) * (bb n : ℂ)) * x ^ 4 - 4 * x ^ 5

/-- `Mcq = (2(a+b)R - (r_a+r_b)(P1 + P2/2))/(x+1)^2`. -/
def Mcqp (x : ℂ) : ℂ :=
  ((rb : ℂ) + (ra : ℂ) - 2 * (bb n : ℂ) * (rab : ℂ) - 2 * (aa m : ℂ) * (rab : ℂ)
      - 2 * (bb n : ℂ) ^ 2 * (ra : ℂ) - 2 * (aa m : ℂ) * (bb n : ℂ) * (rb : ℂ)
      - 2 * (aa m : ℂ) * (bb n : ℂ) * (ra : ℂ) - 2 * (aa m : ℂ) ^ 2 * (rb : ℂ))
  + ((-3/2 * ((rb : ℂ) + (ra : ℂ)) + 4 * (bb n : ℂ) * (rab : ℂ) + 4 * (aa m : ℂ) * (rab : ℂ)
      + 6 * (bb n : ℂ) ^ 2 * (rb : ℂ) + 4 * (bb n : ℂ) ^ 2 * (ra : ℂ)
      + 2 * (aa m : ℂ) * (bb n : ℂ) * (rb : ℂ) + 2 * (aa m : ℂ) * (bb n : ℂ) * (ra : ℂ)
      + 4 * (aa m : ℂ) ^ 2 * (rb : ℂ) + 6 * (aa m : ℂ) ^ 2 * (ra : ℂ))) * x
  + ((-3 * ((rb : ℂ) + (ra : ℂ)) - 2 * (bb n : ℂ) * (rab : ℂ) - 2 * (aa m : ℂ) * (rab : ℂ)
      - 10 * (aa m : ℂ) * (bb n : ℂ) * (rb : ℂ) - 10 * (aa m : ℂ) * (bb n : ℂ) * (ra : ℂ))) * x ^ 2
  + ((6 * ((rb : ℂ) + (ra : ℂ)) - 2 * (bb n : ℂ) ^ 2 * (rb : ℂ) - 2 * (bb n : ℂ) ^ 2 * (ra : ℂ)
      + 4 * (aa m : ℂ) * (bb n : ℂ) * (rb : ℂ) + 4 * (aa m : ℂ) * (bb n : ℂ) * (ra : ℂ)
      - 2 * (aa m : ℂ) ^ 2 * (rb : ℂ) - 2 * (aa m : ℂ) ^ 2 * (ra : ℂ))) * x ^ 3
  + ((-2 * ((rb : ℂ) + (ra : ℂ)) + 2 * (aa m : ℂ) * (bb n : ℂ) * (rb : ℂ)
      + 2 * (aa m : ℂ) * (bb n : ℂ) * (ra : ℂ))) * x ^ 4
  + ((-1/2 * ((rb : ℂ) + (ra : ℂ)))) * x ^ 5

/-! ### The gauge identities -/

lemma Mu_identity (x : ℂ) :
    -(P1p m n x) / 2 - P0p m n x - P2p m n x / 4 = (x + 1) ^ 2 * Muqp m n x := by
  simp only [P1p, P0p, P2p, Muqp]; ring

lemma Nq_identity (x : ℂ) :
    -(P1p m n x + R2p m n x) = (x + 1) * Nqp m n x := by
  simp only [P1p, R2p, Nqp]; ring

lemma Mc_identity (x : ℂ) :
    2 * (((aa m : ℂ) + (bb n : ℂ))) * Rhp m n ra rb rab x
        - ((ra : ℂ) + (rb : ℂ)) * (P1p m n x + P2p m n x / 2)
      = (x + 1) ^ 2 * Mcqp m n ra rb rab x := by
  simp only [P1p, P2p, Rhp, Mcqp]; ring


/-! ### The analytic functions defined by `P` and its derivatives -/

/-- `U0(x) = Σ_k c_k x^k`, the analytic function defined by `P` near `0`. -/
def U0 (x : ℂ) : ℂ := ∑' k : ℕ, coef m n ra rb rab r0 k * x ^ k

/-- The evaluation of the derivative series of `P`. -/
def U1 (x : ℂ) : ℂ := ∑' k : ℕ, (((k : ℂ) + 1) * coef m n ra rb rab r0 (k + 1)) * x ^ k

/-- The evaluation of the second derivative series of `P`. -/
def U2 (x : ℂ) : ℂ := ∑' k : ℕ, (((k : ℂ) + 1) * ((k : ℂ) + 2) * coef m n ra rb rab r0 (k + 2)) * x ^ k

/-- `β = (r_a+r_b)/(2(a+b))`. -/
def bbeta : ℂ := ((ra : ℂ) + (rb : ℂ)) / (2 * ((aa m : ℂ) + (bb n : ℂ)))

/-- The gauge coordinate `v = (P' - P/2 - β)/(x+1)`. -/
def Vp (x : ℂ) : ℂ := (U1 m n ra rb rab r0 x - U0 m n ra rb rab r0 x / 2 - bbeta m n ra rb) / (x + 1)

/-! ### The pulled-back system -/

/-- `(1,1)`-entry of the gauge system matrix. -/
def A11 : ℂ := 1 / 2
/-- `(1,2)`-entry of the gauge system matrix. -/
def A12 (x : ℂ) : ℂ := x + 1
/-- `(2,1)`-entry of the gauge system matrix. -/
def A21 (x : ℂ) : ℂ := Muqp m n x / R2p m n x
/-- `(2,2)`-entry of the gauge system matrix. -/
def A22 (x : ℂ) : ℂ := Nqp m n x / R2p m n x - 1 / 2
/-- second component of the inhomogeneity. -/
def c2 (x : ℂ) : ℂ := Mcqp m n ra rb rab x / (2 * ((aa m : ℂ) + (bb n : ℂ)) * R2p m n x)

/-- The matrix `A₀(x)` of the gauge system. -/
def A0 (x : ℂ) : Fin 2 → Fin 2 → ℂ :=
  ![![A11, A12 x], ![A21 m n x, A22 m n x]]

/-- The vector `c₀(x)` of the gauge system. -/
def c0 (x : ℂ) : Fin 2 → ℂ := ![bbeta m n ra rb, c2 m n ra rb rab x]

/-- The inner radius `r₀ = 3.2·10⁻⁴`. -/
def rrad0 : ℝ := 3.2e-4
/-- The radius `r₁ = 10⁻³` of the initial disc. -/
def rrad1 : ℝ := 1e-3


/-! ### The pulled-back system along `Φ` -/

/-- The system matrix pulled back along `Φ`: `A(z) = Φ'(z)·A₀(Φ z)`. -/
def sysA (m n : ℕ) (Φ : ℂ → ℂ) (z : ℂ) : Fin 2 → Fin 2 → ℂ :=
  fun i j => deriv Φ z *
    (if i = 0 then (if j = 0 then A11 else A12 (Φ z))
      else (if j = 0 then A21 m n (Φ z) else A22 m n (Φ z)))

/-- The inhomogeneity pulled back along `Φ`. -/
def sysb (m n : ℕ) (ra rb rab : ℤ) (Φ : ℂ → ℂ) (z : ℂ) : Fin 2 → ℂ :=
  fun i => deriv Φ z *
    (if i = 0 then bbeta m n ra rb else c2 m n ra rb rab (Φ z))

/-- `Y₀ = (u,v)(Φ z)`, the initial solution on the small disc. -/
def Y0v (m n : ℕ) (ra rb rab r0 : ℤ) (Φ : ℂ → ℂ) (z : ℂ) : Fin 2 → ℂ :=
  fun i => if i = 0 then U0 m n ra rb rab r0 (Φ z) else Vp m n ra rb rab r0 (Φ z)

end
end Work.CLift
