import Mathlib
import Submission.CDT.Beukers
import Submission.Commons.RingTheory.PowerSeries.logPA_ode

/-!
# Item 3 of the Theorem-C route: Hadamard products (CDT §"Products of two logarithms")

The route map of `Submission.cdt_theoremC_li` (Theorem C, `m ≠ n` = CDT
Theorem `logsmain` part 2) proceeds — after reparametrizing `a = 1+2m`,
`b = 1+2n` with `η_a := ½·log(1+1/m)` — through the Hadamard products of
the Beukers pair `A(a,x) = Σuₙ(a)xⁿ` and `H(a,x) = Σvₙ(a)xⁿ`
(`Submission.CDT.Beukers`: `beukersA`, `beukersH`, recurrences, closed
forms, integrality, and the exponential Apéry limit
`vₙ/uₙ → η_a` with the coefficient-growth bound `beukers_apéry_coeff_growth`).

This module lays the **first permanent stretch** of that road: the formal
Hadamard-product language and the paper's four functions

```lean
P_A  := A(a) ⋆ A(b)                          -- eq. (defPA)
P_a  := (H(a) − η_a·A(a)) ⋆ A(b)
P_b  := A(a) ⋆ (H(b) − η_b·A(b))
P_ab := H(a) ⋆ H(b) − η_{a,b}·(A(a) ⋆ A(b)) -- eq. (Pabdef)
```

**Proved here** (all declarations below, zero `sorry`):

* the coefficient-wise product `hadamard` on `ℚ⟦X⟧` and its coefficient
  law `hadamard_coeff` (Mathlib has no Hadamard product for power series;
  this local definition is the seed of a future commons API);
* `PA a b := hadamard (beukersA a) (beukersA b)` with `PA_coeff`
  (`[xⁿ]P_A = uₙ(a)·uₙ(b)`), the initial values `[x⁰]P_A = 1`,
  `[x¹]P_A = a·b`, and the **integrality** `PA_coeff_int_of_odd`
  (`[xⁿ]P_A(a,b) ∈ ℤ` for odd integer `a,b`) — the input to the
  future symmetrization claim `G_A ∈ ℤ[[y]]` (def `PtoG` of the paper,
  machinery `SympDescent.sympSym_int`);
* the coefficient-level η-combinations (`beukersD a n := vₙ(a) − η_a uₙ(a)`,
  `beukersPaCoeff`, `beukersPbCoeff`, `beukersPabCoeff`), the
  **decomposition identity** `beukersPabCoeff_decomp` (the last two lines
  of eq. (Pabdef): `P_ab = η_a·A_a ⋆ (H_b−η_bA_b) + η_b·(H_a−η_aA_a) ⋆ A_b
  + (H_a−η_aA_a) ⋆ (H_b−η_bA_b)`), and the exponential-decay bound
  `beukersD_norm_bound` for `dₙ(a)` (repackaging of
  `beukers_apéry_coeff_growth`);
* the bridge `beukersEta_one_add_two_mul`: for `a = 1+2m`,
  `η_a = ½·log(1+1/m)` (the reparametrization of the route map).

**Target statements (next layer, `1.` and `2.` are PROVED below).**
1. *The order-2 ODE of `P_A`* (paper eq. (ODE)) — **DONE**
   (`logPA_ode`, see below): the coefficients `cₙ = uₙ(a)uₙ(b)` satisfy the
   order-7 P-recurrence obtained by expanding `[xⁿ]M_{a,b}(P_A)`,
   certified by creative telescoping in the commons
   (`Commons.RingTheory.PowerSeries.logPA_ode`).  Its four nonzero finite
   singularities are the products `(a±√(a²−1))(b±√(b²−1))` — grouped near
   `0`, near `1` (twice) and near `∞` when `a/b` is close to `1` — which is
   what makes the operator ``passable'' for the holonomy bounds after the
   symmetrization step.
2. *Overconvergence beyond the smallest cusp* — **DONE for the `P`-family**
   (`beukersPaCoeff_beyond_cusp`, `beukersPbCoeff_beyond_cusp`,
   `beukersPabCoeff_beyond_cusp`, end of file): each of `P_a, P_b, P_ab`
   has coefficients bounded by `C·sⁿ` with
   `s·((a−√(a²−1))(b−√(b²−1))) < 1`, i.e. each series is overconvergent
   beyond the smallest cusp `ρ_a·ρ_b`.  The engine (end of file):
   `Q_b` maps the disc `|z| < ρ_b` into the slit plane
   (`beukersQuadC_mem_slitPlane_of_norm_le`), so `Aℂ(b,·) = 1/√Q_b` is
   holomorphic there with the sup bound `beukersAComplex_norm_le`
   (`‖Aℂ(b,z)‖ ≤ 1/√((ρ_b−r)(ρ_b⁻¹−r))`), giving the radius-form sharp
   growth `beukersUR_cauchy_growth` (`|u_n(b)| ≤ C_r/r^n`, every
   `r < ρ_b`); times the sharp `d`-decay `beukersD_sharp_decay` (base
   `s_d(·)` with `s_d(a)·ρ_a < 1`, `beukers_sd_rho_lt_one` /
   `beukers_three_rho_lt_two_sqrt`) at the radius
   `ρ_b·(s_d(a)ρ_a+1)/2` (resp. swapped, resp. both `d`'s decaying) this
   bounds each coefficient family.  `P_a` and `P_b` are the two products
   `d·u` (symmetrically), `P_ab` is the sum of the three products of the
   decomposition `beukersPabCoeff_decomp`
   (`η_a·u_a·d_b + η_b·d_a·u_b + d_a·d_b`), each overconvergent, with a
   single base `s` obtained as the max of the three rates (all
   `< 1/(ρ_aρ_b)`).
3. The subsequent layers (unlikely-`G`-function, symmetrization `G(y)`,
   denominator types, holonomy refutation) are documented in the docstring
   of `Submission.cdt_theoremC_li`.

**`M_{a,b}(P_A) = 0` is PROVED.**  The paper's order-2 ODE (eq. (ODE))
was dispatched to the commons as a Mathlib-only creative-telescoping
statement and returned as the permanent brick
`Commons.RingTheory.PowerSeries.logPA_ode` (the coefficients `cₙ = uₙ(a)uₙ(b)`
satisfy the order-7 P-recurrence obtained by expanding `[xⁿ]M_{a,b}(P_A)`
— *not* a 3-term recurrence: the leading coefficient `P2` has degree 7 —
certified from the two three-term recurrences of `u(a,·)`, `u(b,·)`);
`logPA_ode` below connects it to the present definitions.

**The analytic gates of the overconvergence claim are PROVED** (the new
§"Sharp `u`-growth and the beyond-cusp bound" at the end of the file —
targets 1, 3 of the code fence below, and the full `P_a, P_b, P_ab`
overconvergence of target statement 2):

* the complex analytic step: `Q_b(z) = z² − 2bz + 1` stays in the slit plane
  on the disc `‖z‖ ≤ r < ρ_b` (`beukersQuadC_mem_slitPlane_of_norm_le`; the
  negative-real preimages of `Q_b` are the real points `|x| ≥ ρ_b`),
  so `Aℂ(b,·) = 1/√Q_b` is holomorphic on every closed disc `‖z‖ ≤ r < ρ_b`
  (`DifferentiableOn`, via `beukersAComplex_analyticAt_of_slitPlane`), with
  the explicit sup bound `‖Aℂ(b,z)‖ ≤ 1/√((ρ_b − r)(ρ_b⁻¹ − r))`
  (`beukersAComplex_norm_le`, using `‖√q‖ = √‖q‖` — the new lemma
  `norm_sqrt_of_mem_slitPlane` — and the factor lower bound
  `beukers_quadC_abs_lower`);
* **target 1 (radius form)** `beukersUR_cauchy_growth`: for every
  `0 < r < ρ_b`, `|u_n(b)| ≤ C_r/r^n` (the Cauchy pipeline of the sharp
  `d`-decay applied to `Aℂ` with its coefficient series
  `Σ (u_n(b):ℂ) zⁿ`, `beukersAComplex_hasSum_series`); the refined
  `(n+1)`-form with base exactly `b + √(b²−1) = 1/ρ_b` is not needed for
  the beyond-cusp claim and is deferred;
* **target 3** `beukersPaCoeff_beyond_cusp`: `|d_n(a)·u_n(b)| ≤ C·sⁿ` with
  `s·ρ_a·ρ_b < 1` — the sharp `d`-decay (`beukersD_sharp_decay`, base
  `s_d := 2/(2√(a²−1) − ρ_a)` satisfies `s_d·ρ_a < 1` by
  `beukers_three_rho_lt_two_sqrt`) times the radius-form `u`-growth at the
  fixed radius `r = ρ_b·c`, `c := (s_d·ρ_a + 1)/2 ∈ (s_d·ρ_a, 1)`, so
  `s := s_d/r` gives `s·ρ_a·ρ_b = (s_d·ρ_a)/c < 1` — the overconvergence of
  `P_a` beyond the smallest cusp `ρ_a·ρ_b`.

All declarations in this module are fully proved (no axioms, no `sorry`).
-/

open scoped BigOperators
open scoped NNReal ENNReal

noncomputable section

namespace Submission.CDT

open PowerSeries

/-! ## The Hadamard product on `ℚ⟦X⟧` -/

/-- the coefficient-wise (Hadamard) product of two power series:
`(Σ aₙxⁿ) ⋆ (Σ bₙxⁿ) = Σ aₙbₙxⁿ` -/
def hadamard (F G : PowerSeries ℚ) : PowerSeries ℚ :=
  PowerSeries.mk (fun n => PowerSeries.coeff n F * PowerSeries.coeff n G)

/-- coefficient of a Hadamard product is the product of the coefficients -/
lemma hadamard_coeff (F G : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff n (hadamard F G) = PowerSeries.coeff n F * PowerSeries.coeff n G := by
  rw [hadamard, PowerSeries.coeff_mk]

/-- the Hadamard product is commutative -/
lemma hadamard_comm (F G : PowerSeries ℚ) : hadamard F G = hadamard G F := by
  apply PowerSeries.ext
  intro n
  rw [hadamard_coeff, hadamard_coeff]
  ring

/-! ## `P_A = A(a) ⋆ A(b)` (paper eq. (defPA)) -/

/-- `P_A(a,b) := A(a) ⋆ A(b)`, the Hadamard product of the two Beukers
`A`-series; its coefficients `cₙ(a,b) = uₙ(a)uₙ(b)` satisfy the order-2
ODE (paper eq. (ODE)) — the target statement documented above. -/
def PA (a b : ℚ) : PowerSeries ℚ := hadamard (beukersA a) (beukersA b)

/-- `[xⁿ]P_A(a,b) = uₙ(a)·uₙ(b)` -/
lemma PA_coeff (a b : ℚ) (n : ℕ) :
    PowerSeries.coeff n (PA a b) = beukersU a n * beukersU b n := by
  rw [PA, hadamard_coeff, beukersA_coeff, beukersA_coeff]

/-- `P_A(a,b)(0) = 1` -/
lemma PA_coeff_zero (a b : ℚ) : PowerSeries.coeff 0 (PA a b) = 1 := by
  rw [PA_coeff, beukersU_zero a, beukersU_zero b]
  norm_num

/-- `[x]P_A(a,b) = a·b` -/
lemma PA_coeff_one (a b : ℚ) : PowerSeries.coeff 1 (PA a b) = a * b := by
  rw [PA_coeff, beukersU_one a, beukersU_one b]

/-- for odd integers `a,b` all coefficients of `P_A(a,b)` are integers
(the rational coefficients are the casts of integers) -/
lemma PA_coeff_int_of_odd (z1 z2 : ℤ) (hz1 : Odd z1) (hz2 : Odd z2) (n : ℕ) :
    ∃ t : ℤ, (t : ℚ) = PowerSeries.coeff n (PA (z1 : ℚ) (z2 : ℚ)) := by
  classical
  rw [PA_coeff]
  obtain ⟨t1, ht1⟩ := beukersU_int_of_odd z1 hz1 n
  obtain ⟨t2, ht2⟩ := beukersU_int_of_odd z2 hz2 n
  refine ⟨t1 * t2, ?_⟩
  rw [Int.cast_mul]
  rw [ht1, ht2]

/-! ## The η-combinations `P_a`, `P_b`, `P_ab` (paper eq. (Pabdef)) -/

/-- `dₙ(a) = vₙ(a) − η_a·uₙ(a)`: the coefficients of the overconvergent
difference `H(a,x) − η_a·A(a,x)` (the exponentially decaying part of the
Apéry pair; `beukersD_norm_bound` below). -/
def beukersD (a : ℝ) (n : ℕ) : ℝ := beukersVR a n - beukersEta a * beukersUR a n

/-- the coefficients of `P_a = (H(a) − η_a·A(a)) ⋆ A(b)` -/
def beukersPaCoeff (a b : ℝ) (n : ℕ) : ℝ := beukersD a n * beukersUR b n

/-- the coefficients of `P_b = A(a) ⋆ (H(b) − η_b·A(b))` -/
def beukersPbCoeff (a b : ℝ) (n : ℕ) : ℝ := beukersUR a n * beukersD b n

/-- the coefficients of `P_ab = H(a) ⋆ H(b) − η_{a,b}·(A(a) ⋆ A(b))` -/
def beukersPabCoeff (a b : ℝ) (n : ℕ) : ℝ :=
  beukersVR a n * beukersVR b n
    - beukersEta a * beukersEta b * beukersUR a n * beukersUR b n

/-- the decomposition identity for the `P_ab` coefficients (last two lines
of paper eq. (Pabdef)):
`v_av_b − η_aη_b·u_au_b = η_a·u_a·d_b + η_b·d_a·u_b + d_a·d_b` -/
lemma beukersPabCoeff_decomp (a b : ℝ) (n : ℕ) :
    beukersPabCoeff a b n =
      beukersEta a * beukersUR a n * beukersD b n
        + beukersEta b * beukersD a n * beukersUR b n
        + beukersD a n * beukersD b n := by
  unfold beukersPabCoeff beukersD
  ring

/-- the exponential decay of the `dₙ(a)` coefficients (repackaging of the
A6/A7 coefficient-growth theorem `beukers_apéry_coeff_growth`):
`‖dₙ(a)‖ ≤ C/rⁿ` with `1/a < r < 1` -/
lemma beukersD_norm_bound (a : ℝ) (ha : 3 ≤ a) :
    ∃ C r : ℝ, 0 < C ∧ 0 < r ∧ (1 : ℝ) / a < r ∧
      ∀ n : ℕ, ‖(beukersD a n : ℂ)‖ ≤ C / r ^ n := by
  simpa [beukersD] using beukers_apéry_coeff_growth a ha

/-! ## The reparametrization `a = 1+2m` -/

/-- with `a = 1+2m`, `η_a = ½·log((a+1)/(a−1)) = ½·log(1+1/m)` -/
lemma beukersEta_one_add_two_mul (m : ℤ) (hm0 : m ≠ 0) :
    beukersEta (1 + 2 * (m : ℝ)) = (1 / 2 : ℝ) * Real.log (1 + 1 / (m : ℝ)) := by
  unfold beukersEta
  congr 1
  have hmℝ : (m : ℝ) ≠ 0 := by exact_mod_cast hm0
  have hlog : ((1 + 2 * (m : ℝ)) + 1) / ((1 + 2 * (m : ℝ)) - 1) = 1 + 1 / (m : ℝ) := by
    field_simp [hmℝ]
    ring
  rw [hlog]


/-! ## The order-2 ODE of `P_A` (paper eq. (ODE)) — operator and open skeleton

The paper's eq. (ODE) exhibits an explicit order-2 differential operator
`M_{a,b} = P2·(d/dx)² + P1·(d/dx) + P0` (with polynomial coefficients
`P2, P1, P0` of degrees `7, 6, 5`; after expansion
`P2 = X⁷ − 4abX⁶ + (4a²+4b²−3)X⁵ − (4a²+4b²−3)X³ + 4abX² − X`,
`P1 = 3X⁶ − 8abX⁵ + (4a²+4b²−7)X⁴ + 16abX³ + (5−12a²−12b²)X² + 8abX − 1`,
`P0 = X⁵ − abX⁴ − (a²+b²+2)X³ + 8abX² + (1−3a²−3b²)X + ab`) such that
`M_{a,b}(P_A(a,b)) = 0` — verified numerically against the closed forms
coefficient-by-coefficient (the transcription below is the paper's
eq. (ODE) verbatim, and the factored form of `P2` has been checked in
exact arithmetic for many `(a,b,n)`).  The coefficients `cₙ = uₙ(a)uₙ(b)`
therefore satisfy the P-recurrence obtained by expanding
`[xⁿ]M_{a,b}(P_A) = 0` (an 8-term recurrence — *not* a 3-term one: the
leading coefficient `P2` has degree 7 — whose verification by creative
telescoping on the binomial closed forms is dispatched to the commons;
`Commons.RingTheory.PowerSeries.logPA_ode`).  The four nonzero finite
singularities of `M_{a,b}` are the products `(a±√(a²−1))(b±√(b²−1))`,
grouped near `0`, near `1` (twice) and near `∞` when `a/b` is close to `1`. -/

/-- the quartic factor `1−4abX+(4a²+4b²−2)X²−4abX³+X⁴` of `P2` -/
def logPAQ4 (a b : ℚ) : PowerSeries ℚ :=
  (1 : PowerSeries ℚ) - C (4 * a * b) * X + C (4 * a ^ 2 + 4 * b ^ 2 - 2) * X ^ 2
    - C (4 * a * b) * X ^ 3 + X ^ 4

/-- the `y''`-coefficient `P2 = (X−1)·X·(X+1)·Q4` of the paper's eq. (ODE) -/
def logPAP2 (a b : ℚ) : PowerSeries ℚ :=
  (X - 1) * X * (X + 1) * logPAQ4 a b

/-- the `y'`-coefficient `P1` of the paper's eq. (ODE) -/
def logPAP1 (a b : ℚ) : PowerSeries ℚ :=
  (-1 : PowerSeries ℚ) + C (8 * a * b) * X + C (5 - 12 * a ^ 2 - 12 * b ^ 2) * X ^ 2
    + C (16 * a * b) * X ^ 3 + C (4 * a ^ 2 + 4 * b ^ 2 - 7) * X ^ 4
    - C (8 * a * b) * X ^ 5 + 3 * X ^ 6

/-- the `y`-coefficient `P0` of the paper's eq. (ODE) -/
def logPAP0 (a b : ℚ) : PowerSeries ℚ :=
  C (a * b) + C (1 - 3 * a ^ 2 - 3 * b ^ 2) * X + C (8 * a * b) * X ^ 2
    - C (a ^ 2 + b ^ 2 + 2) * X ^ 3 - C (a * b) * X ^ 4 + X ^ 5

/-- the order-2 differential operator `M_{a,b} = P2·y'' + P1·y' + P0·y`
of the paper's eq. (ODE) -/
def logPAODE (a b : ℚ) (y : PowerSeries ℚ) : PowerSeries ℚ :=
  logPAP2 a b * PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) y)
    + logPAP1 a b * PowerSeries.derivative (R := ℚ) y
    + logPAP0 a b * y

/-- the closed form of the Beukers coefficients as dispatched to the commons
(`logPAU t m = u_m(t)`; here written with `C(m,2j)·C(2j,j)`, equal to the
`centralBinom`-form of `beukersU_closed` since `C(2j,j) = centralBinom j`) -/
def logPAU (t : ℚ) (m : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (m / 2 + 1),
    (Nat.choose m (2 * j) : ℚ) * (Nat.choose (2 * j) j : ℚ) * t ^ (m - 2 * j) *
      (((t * t - 1) / 4) ^ j)

/-- the dispatched closed form is the Beukers sequence -/
lemma logPAU_eq_beukersU (t : ℚ) (m : ℕ) : logPAU t m = beukersU t m := by
  unfold logPAU
  rw [beukersU_closed t m]
  apply Finset.sum_congr rfl
  intro j hj
  have hcb : (Nat.centralBinom j : ℚ) = (Nat.choose (2 * j) j : ℚ) := by rfl
  rw [hcb]
  ac_rfl

/-- `P_A(a,b)` is the series with the dispatched closed-form coefficients -/
lemma PA_eq_mk_logPAU (a b : ℚ) :
    PA a b = PowerSeries.mk (fun m => logPAU a m * logPAU b m) := by
  apply PowerSeries.ext
  intro m
  rw [PowerSeries.coeff_mk]
  rw [PA, hadamard_coeff, beukersA_coeff, beukersA_coeff]
  rw [logPAU_eq_beukersU a m, logPAU_eq_beukersU b m]

/-- `P_A(a,b) = A(a) ⋆ A(b)` satisfies the order-2 ODE
`M_{a,b}(P_A) = 0` of the paper's eq. (ODE).  Proved from the commons
creative-telescoping brick `Commons.RingTheory.PowerSeries.logPA_ode`
(dispatched as a Mathlib-only statement; see the module docstring). -/
theorem logPA_ode (a b : ℚ) : logPAODE a b (PA a b) = 0 := by
  rw [PA_eq_mk_logPAU]
  have h := Commons.RingTheory.PowerSeries.logPA_ode a b
  unfold logPAODE logPAP2 logPAP1 logPAP0 logPAQ4
  exact h


/-- geometric growth of the coefficients of `P_a = (H(a)−η_aA(a)) ⋆ A(b)`:
`|dₙ(a)·uₙ(b)| ≤ C·Rⁿ` (the input to the overconvergence analysis; the
cusp comparison with `(a−√(a²−1))(b−√(b²−1))` awaits the sharp rates) -/
lemma beukersPaCoeff_growth (a b : ℝ) (ha : 3 ≤ a) (hb : 3 ≤ b) :
    ∃ C R : ℝ, 0 < C ∧ 0 < R ∧ ∀ n : ℕ, |beukersPaCoeff a b n| ≤ C * R ^ n := by
  rcases beukersD_norm_bound a ha with ⟨Cd, rd, hCd, hrd, hr1, hd⟩
  rcases beukersUR_growth b hb with ⟨Cu, ρ, hCu, hρ, hu⟩
  refine ⟨Cd * Cu, ρ / rd, by positivity, by positivity, ?_⟩
  intro n
  have hdn : |beukersD a n| ≤ Cd / rd ^ n := by
    simpa using (hd n)
  have hun : |beukersUR b n| ≤ Cu * ρ ^ n := hu n
  calc
    |beukersPaCoeff a b n| = |beukersD a n * beukersUR b n| := by rfl
    _ ≤ |beukersD a n| * |beukersUR b n| := by rw [abs_mul]
    _ ≤ (Cd / rd ^ n) * (Cu * ρ ^ n) := mul_le_mul hdn hun (abs_nonneg _) (by positivity : 0 ≤ Cd / rd ^ n)
    _ = (Cd * Cu) * (ρ / rd) ^ n := by
          have hpp : (ρ / rd) ^ n = ρ ^ n / rd ^ n := div_pow ρ rd n
          rw [hpp]
          field_simp [ne_of_gt hrd]



/-! ## The sharp growth upgrade — target statements

The current coefficient bounds have *uncontrolled* geometric rates
(`beukersUR_growth` returns an unknown base; `beukersPaCoeff_growth` hence
proves only *some* geometric growth).  For the overconvergence claim of the
paper's §"Products of two logarithms" the rates must be tied to the actual
singularities.  The key radii (`beukersRho`, `beukersRhoC`):

* `rho_a := a − √(a²−1)` (`beukersRho`) is the smallest positive
  singularity of `A(a,x) = (1−2ax+x²)^(−1/2)` (the other is
  `rho_a^{-1} = a+√(a²−1)`);
* the even-descent machinery (`beukersG0`, `beukersG0_descends_sq_onBall`,
  brick A4) makes the companion `H − eta_a·A` holomorphic on the
  `w = u²`-disc of any radius `R0² < R_u² := 2·√(a²−1)`, i.e. on the
  `x`-disc of radius `R0² − rho_a` around `0`; the **reachable radius** is
  therefore any `R < R_a := 2·√(a²−1) − rho_a`, and
  `rho_a < R_a < 1/rho_a` (numerically `rho_3 ≈ 0.1716`,
  `R_a(3) ≈ 5.485 < 1/rho_3 ≈ 5.828`), so the decay base `s = 1/R` can be
  pushed to `s_a := 1/R_a ≈ rho_a·(1+O(1/a²))` — rate
  `rho_a^{n(1−o(1))}`, the paper's `O(rho_a^{n(1−ε)})`.  It is *not*
  possible to reach `s < rho_a` (that would need radius `> 1/rho_a`); the
  true bound from the descent is `R < 2·√(a²−1) − rho_a < 1/rho_a`.

```lean
-- target 1 (sharp `u`-growth): the radius of Σ u_n(a)·x^n is rho_a
lemma beukersUR_sharp_growth (a : ℝ) (ha : 3 ≤ a) :
    ∃ C R : ℝ, 0 < C ∧ (a - Real.sqrt (a ^ 2 - 1)) < R ∧
      ∀ n : ℕ, |beukersUR a n| ≤ C * (1 / R) ^ n

-- target 2 (sharp `d`-decay) — **DONE** (`beukersD_sharp_decay` below): the
-- companion overconverges through x = rho_a with the Cauchy circle at
-- rv = (2√(a²−1) − rho_a)/2, giving decay base 2/(2√(a²−1) − rho_a):
lemma beukersD_sharp_decay (a : ℝ) (ha : 3 ≤ a) :
    ∃ C : ℝ, 0 < C ∧
      ∀ n : ℕ, ‖(beukersD a n : ℂ)‖ ≤ C * (2 / (2 * Real.sqrt (a ^ 2 - 1) - beukersRho a)) ^ n

-- target 3 (beyond the smallest cusp) — CORRECTED: the P_a coefficients
-- d_n(a)·u_n(b) genuinely GROW (decay base s_a of d times the u-growth
-- base ≈ b+√(b²−1)), so the right claim is that the *series radius*
-- 1/(s_a·(b+√(b²−1))) exceeds the cusp rho_a·rho_b — equivalently, by
-- (b+√(b²−1))·rho_b = 1, that s·rho_a·rho_b < 1 with
-- s := s_a·(b+√(b²−1)) (reduces to s_a·rho_a < 1, true with slack:
-- 3·rho_a < 2√(a²−1)); numerically radius ≈ 0.5–0.94 ≫ cusps ≤ 0.03.
lemma beukersPaCoeff_beyond_cusp (a b : ℝ) (ha : 3 ≤ a) (hb : 3 ≤ b) :
    ∃ C s : ℝ, 0 < C ∧ 0 < s ∧
      s * ((a - Real.sqrt (a ^ 2 - 1)) * (b - Real.sqrt (b ^ 2 - 1))) < 1 ∧
      ∀ n : ℕ, |beukersPaCoeff a b n| ≤ C * s ^ n
```

**Gate for target 3** (the single remaining analytic brick, analogous to the
`d`-case just completed but simpler): *target 1* — sharp `u`-growth,
`|u_n(b)| ≤ C·(b+√(b²−1))^n·(1+ε)^n`.  It follows exactly like the sharp
`d`-decay: `A(b,x) = (1−2bx+x²)^{−1/2}` has nearest singularity `rho_b`, so
on the circle `|z| = r < rho_b` one has
`|1−2bz+z²| ≥ (rho_b−r)(1/rho_b−r)` and hence the sup bound
`M(r) = ((rho_b−r)(1/rho_b−r))^{−1/2}`; Cauchy gives
`|u_n(b)| ≤ M(r)/r^n` for any `r < rho_b` — base `1/r` arbitrarily close
to `1/rho_b = b+√(b²−1)`.  (The complex-analytic ingredients: the explicit
`sqrt`-bound and an analyticity/boundedness statement for
`beukersAComplex` on the disc `|z| ≤ r`, `r < rho_b`.)  With target 1 in
hand, target 3 is the short product: sharp decay × sharp growth, and the
identity `(b+√(b²−1))·rho_b = 1` collapses `s·rho_a·rho_b` to `s_a·rho_a < 1`
(`3·rho_a < 2√(a²−1)`).

**TARGETS 1 (radius form) and 3 are DONE** (end of this file, §"Sharp
`u`-growth and the beyond-cusp bound"): the sup bound
`beukersAComplex_norm_le` (`‖Aℂ(b,z)‖ ≤ 1/√((ρ_b−r)(ρ_b⁻¹−r))` on
`‖z‖ ≤ r < ρ_b`, from the slit-plane lemma
`beukersQuadC_mem_slitPlane_of_norm_le` — `Q_b(D(0,ρ_b)) ⊆ ℂ∖(−∞,0]` —
and `‖√q‖ = √‖q‖`, `norm_sqrt_of_mem_slitPlane`), the Cauchy growth
`beukersUR_cauchy_growth` (`|u_n(b)| ≤ C_r/r^n` for every `r < ρ_b`), and
`beukersPaCoeff_beyond_cusp` (rate `s` with `s·ρ_a·ρ_b < 1`, via
`beukers_three_rho_lt_two_sqrt` giving `s_d·ρ_a < 1` and the fixed radius
`r = ρ_b·(s_d·ρ_a + 1)/2`).  The `(1+ε)`-refined exact-base statement
below (code fence after the "First connective lemma" paragraph) remains a
scheme: the module-level product claims need only the radius form.
```

**First connective lemma — DONE** (proved below: the three lemmas
`beukersApéryRhoExt_analyticAt_of_cuspDisc` (ingredient (i)),
`beukersApéryRhoExt_continuousOn_closedBall` and
`beukersApéryRhoExt_bddOn_closedBall` (ingredient (ii))).  Original target
statement:

```lean
-- the rho-extension g(z) := F(rho − z) is analytic on the disc
-- |z| < R0² − rho whenever F is analytic on |w| < R0² (substitute the
-- affine map w = rho − z into the brick-A4 ball power series
-- beukersG0_descends_sq_onBall); together with the germ equality
-- beukers_apéry_g_eq_HComplex_eventually (the d-series IS g's series
-- near 0) and the Commons Cauchy bound `cauchy_coeff_bound`, this
-- upgrades beukers_apéry_coeff_growth's rate from "some r > 1/a" to
-- "any r < R_a = 2·√(a²−1) − rho_a", i.e. gives target 2.
-- Needed ingredients: (i) analyticity of F∘(rho − z) on |z| < R0² − rho
-- from the ball power series; (ii) a sup bound of g on the circle of
-- radius r < R0² − rho, from beukersG0_differentiableOn /
-- beukersG0_continuousOn + compactness.  Both are on our concrete
-- functions (not Mathlib-only, hence not fleet-delegatable).
```
-/


/-- **affine precomposition (ingredient i of the sharp decay)**: the
`ρ`-extension `g(z) = F(ρ−z)` is holomorphic at every `z` with
`‖z‖ < R0² − ρ` whenever `F` is holomorphic on the `w`-disc of radius
`R0²` (then `‖ρ−z‖ ≤ ρ + ‖z‖ < ρ + (R0² − ρ) = R0²`); this is the
`of_unitBall`-lemma with the unit radius replaced by `R0² − ρ`. -/
lemma beukersApéryRhoExt_analyticAt_of_cuspDisc (a : ℝ) (ha : 3 ≤ a) {R0 : ℝ≥0}
    (hR0 : beukersRho a < (R0 : ℝ) ^ 2) {F : ℂ → ℂ}
    {q : FormalMultilinearSeries ℂ ℂ ℂ}
    (hF : HasFPowerSeriesOnBall F q 0 (((R0 : ℝ≥0∞) ^ 2))) {z : ℂ}
    (hz : ‖z‖ < (R0 : ℝ) ^ 2 - beukersRho a) :
    AnalyticAt ℂ (beukersApéryRhoExt a F) z := by
  have hρ0 : 0 ≤ beukersRho a := le_of_lt (beukers_rho_pos a ha)
  have hR0pos : 0 < (R0 : ℝ) ^ 2 - beukersRho a := by linarith
  let y : ℂ := ((beukersRho a : ℝ) : ℂ) - z
  have hyn : ‖y‖ < (R0 : ℝ) ^ 2 := by
    have hnorm_le : ‖y‖ ≤ ‖((beukersRho a : ℝ) : ℂ)‖ + ‖z‖ := by
      dsimp [y]
      exact norm_sub_le (((beukersRho a : ℝ) : ℂ)) z
    have hρn : ‖((beukersRho a : ℝ) : ℂ)‖ = beukersRho a := by
      simp [abs_of_nonneg hρ0]
    calc
      ‖y‖ ≤ ‖((beukersRho a : ℝ) : ℂ)‖ + ‖z‖ := hnorm_le
      _ = beukersRho a + ‖z‖ := by rw [hρn]
      _ < (R0 : ℝ) ^ 2 := by linarith
  have hFy : AnalyticAt ℂ F y := by
    apply hF.analyticAt_of_mem
    rw [mem_eball_zero_iff]
    have hlt : (‖y‖₊ : ℝ≥0∞) < ((R0 ^ 2 : ℝ≥0) : ℝ≥0∞) := by
      apply ENNReal.coe_lt_coe.mpr
      exact_mod_cast hyn
    simpa [ENNReal.coe_pow, enorm] using hlt
  have hZ : AnalyticAt ℂ (fun w : ℂ => ((beukersRho a : ℝ) : ℂ) - w) z := by
    fun_prop
  have hF0 : AnalyticAt ℂ F (((beukersRho a : ℝ) : ℂ) - z) := by
    simpa [y] using hFy
  have hcomp : AnalyticAt ℂ (F ∘ (fun w : ℂ => ((beukersRho a : ℝ) : ℂ) - w)) z :=
    hF0.comp (x := z) hZ
  change AnalyticAt ℂ (fun w : ℂ => F (((beukersRho a : ℝ) : ℂ) - w)) z
  exact hcomp



/-- **sup-bound ingredient (ii)**: `g = F(ρ−z)` is continuous on the closed
disc `‖z‖ ≤ r` for every `r < R0² − ρ` (it is analytic at each point there
by ingredient (i)) -/
lemma beukersApéryRhoExt_continuousOn_closedBall (a : ℝ) (ha : 3 ≤ a) {R0 : ℝ≥0}
    (hR0 : beukersRho a < (R0 : ℝ) ^ 2) {F : ℂ → ℂ}
    {q : FormalMultilinearSeries ℂ ℂ ℂ}
    (hF : HasFPowerSeriesOnBall F q 0 (((R0 : ℝ≥0∞) ^ 2))) {r : ℝ}
    (hr : r < (R0 : ℝ) ^ 2 - beukersRho a) :
    ContinuousOn (beukersApéryRhoExt a F) (Metric.closedBall (0 : ℂ) r) := by
  intro x hx
  have hxr : ‖x‖ ≤ r := by
    simpa using (Metric.mem_closedBall.mp hx)
  have hxR : ‖x‖ < (R0 : ℝ) ^ 2 - beukersRho a := by linarith
  exact (beukersApéryRhoExt_analyticAt_of_cuspDisc a ha hR0 hF hxR).continuousAt.continuousWithinAt

/-- `g` is bounded on the closed disc `‖z‖ ≤ r` for `r < R0² − ρ` -/
lemma beukersApéryRhoExt_bddOn_closedBall (a : ℝ) (ha : 3 ≤ a) {R0 : ℝ≥0}
    (hR0 : beukersRho a < (R0 : ℝ) ^ 2) {F : ℂ → ℂ}
    {q : FormalMultilinearSeries ℂ ℂ ℂ}
    (hF : HasFPowerSeriesOnBall F q 0 (((R0 : ℝ≥0∞) ^ 2))) {r : ℝ}
    (hr : r < (R0 : ℝ) ^ 2 - beukersRho a) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℂ, z ∈ Metric.closedBall (0 : ℂ) r → ‖beukersApéryRhoExt a F z‖ ≤ M := by
  have hc : ContinuousOn (fun z : ℂ => ‖beukersApéryRhoExt a F z‖) (Metric.closedBall (0 : ℂ) r) := by
    exact (beukersApéryRhoExt_continuousOn_closedBall a ha hR0 hF hr).norm
  have hcomp : IsCompact (Metric.closedBall (0 : ℂ) r) := isCompact_closedBall (0 : ℂ) r
  by_cases hne : (Metric.closedBall (0 : ℂ) r).Nonempty
  · rcases hcomp.exists_isMaxOn hne hc with ⟨z, hz, hmax⟩
    refine ⟨‖beukersApéryRhoExt a F z‖, norm_nonneg _, ?_⟩
    intro w hw
    exact hmax hw
  · refine ⟨0, le_rfl, ?_⟩
    intro z hz
    exact False.elim (hne ⟨z, hz⟩)



/-- **cusp-disc differentiability**: from ingredient (i) (pointwise
analyticity of `g = F(ρ−z)` on `‖z‖ < R0² − ρ`) `g` is complex
differentiable on every open ball `‖z‖ < r` with `r < R0² − ρ` — the
hypothesis needed for `DifferentiableOn.hasFPowerSeriesOnBall` (Cauchy
circle of radius up to `R0² − ρ`, giving any rate `s = 1/r` with
`1 < r < R0² − ρ`) -/
lemma beukers_apéry_g_differentiableOn_cuspDisc (a : ℝ) (ha : 3 ≤ a) {R0 : ℝ≥0}
    (hR0 : beukersRho a < (R0 : ℝ) ^ 2) {F : ℂ → ℂ}
    {q : FormalMultilinearSeries ℂ ℂ ℂ}
    (hF : HasFPowerSeriesOnBall F q 0 (((R0 : ℝ≥0∞) ^ 2))) :
    ∀ r : ℝ, r < (R0 : ℝ) ^ 2 - beukersRho a →
      DifferentiableOn ℂ (beukersApéryRhoExt a F) (Metric.ball (0 : ℂ) r) := by
  intro r hr z hz
  have hzn : ‖z‖ < (R0 : ℝ) ^ 2 - beukersRho a := by
    have hzr : dist z 0 < r := Metric.mem_ball.mp hz
    have hn : ‖z‖ < r := by simpa using hzr
    linarith
  exact (beukersApéryRhoExt_analyticAt_of_cuspDisc a ha hR0 hF hzn).differentiableAt.differentiableWithinAt

/-- **closed-disc holomorphy data**: on the closed disc `‖z‖ ≤ r`
(`r < R0² − ρ`) `g` is differentiable (hence has the ball power series
`cauchyPowerSeries`) and bounded — the exact inputs of the Cauchy estimate -/
lemma beukers_apéry_g_holomorphicOn_closedDisc (a : ℝ) (ha : 3 ≤ a) {R0 : ℝ≥0}
    (hR0 : beukersRho a < (R0 : ℝ) ^ 2) {F : ℂ → ℂ}
    {q : FormalMultilinearSeries ℂ ℂ ℂ}
    (hF : HasFPowerSeriesOnBall F q 0 (((R0 : ℝ≥0∞) ^ 2))) {r : ℝ}
    (hr : r < (R0 : ℝ) ^ 2 - beukersRho a) :
    DifferentiableOn ℂ (beukersApéryRhoExt a F) (Metric.closedBall (0 : ℂ) r) := by
  -- enlarge: r < r' < R0² − ρ
  have hpos : 0 < (R0 : ℝ) ^ 2 - beukersRho a - r := by linarith
  let r' : ℝ := (r + ((R0 : ℝ) ^ 2 - beukersRho a)) / 2
  have hrr' : r < r' := by dsimp [r']; linarith
  have hr' : r' < (R0 : ℝ) ^ 2 - beukersRho a := by dsimp [r']; linarith
  have hd : DifferentiableOn ℂ (beukersApéryRhoExt a F) (Metric.ball (0 : ℂ) r') :=
    beukers_apéry_g_differentiableOn_cuspDisc a ha hR0 hF r' hr'
  exact hd.mono (Metric.closedBall_subset_ball hrr')



/-- the sharp descent radius `R0` with `R0² = 2√(a²−1) − 1` -/
def beukersR0sharp (a : ℝ) : ℝ≥0 :=
  ⟨Real.sqrt (2 * Real.sqrt (a ^ 2 - 1) - 1), Real.sqrt_nonneg _⟩

lemma beukersR0sharp_sq (a : ℝ) (ha : 3 ≤ a) : ((beukersR0sharp a : ℝ) ^ 2) = 2 * Real.sqrt (a ^ 2 - 1) - 1 := by
  have hnn : 0 ≤ 2 * Real.sqrt (a ^ 2 - 1) - 1 := by
    have hsq : 0 ≤ a ^ 2 - 1 := by nlinarith [sq_nonneg a]
    have h8 : 8 ≤ a ^ 2 - 1 := by nlinarith
    have hs := Real.sqrt_le_sqrt (by exact_mod_cast h8)
    have hq : (1 / 2 : ℝ) ^ 2 < 8 := by norm_num
    have hlt := Real.sqrt_lt_sqrt (by positivity : 0 ≤ (1 / 2 : ℝ) ^ 2) hq
    have hA : Real.sqrt ((1 / 2 : ℝ) ^ 2) = 1 / 2 := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ))]
    have h12 : (1 / 2 : ℝ) < Real.sqrt 8 := by simpa [hA] using hlt
    have : Real.sqrt 8 ≤ Real.sqrt (a ^ 2 - 1) := hs
    nlinarith
  change (Real.sqrt (2 * Real.sqrt (a ^ 2 - 1) - 1)) ^ 2 = 2 * Real.sqrt (a ^ 2 - 1) - 1
  rw [Real.sq_sqrt hnn]

/-- `ρ_a + 2 < 2√(a²−1)` for `a ≥ 3` (the inequality making `R0²` clear
`ρ_a + 1` and the Cauchy circle `rv` sit strictly inside the companion radius) -/
lemma beukers_rho_add_two_lt_two_sqrt (a : ℝ) (ha : 3 ≤ a) :
    beukersRho a + 2 < 2 * Real.sqrt (a ^ 2 - 1) := by
  have hsqlt : ((a + 2) / 3) ^ 2 < a ^ 2 - 1 := by nlinarith [sq_nonneg a]
  have hlt := Real.sqrt_lt_sqrt (sq_nonneg ((a + 2) / 3)) hsqlt
  have hA : Real.sqrt (((a + 2) / 3) ^ 2) = (a + 2) / 3 := by
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (a + 2) / 3)]
  have h13 : (a + 2) / 3 < Real.sqrt (a ^ 2 - 1) := by simpa [hA] using hlt
  unfold beukersRho
  nlinarith

/-- `R0 < R_u = √(2√(a²−1))`, the descent hypothesis -/
lemma beukersR0sharp_lt_Ru (a : ℝ) (ha : 3 ≤ a) :
    ((beukersR0sharp a : ℝ) < Real.sqrt (2 * Real.sqrt (a ^ 2 - 1))) := by
  have hnn : 0 ≤ 2 * Real.sqrt (a ^ 2 - 1) - 1 := by
    have hsq : 0 ≤ a ^ 2 - 1 := by nlinarith [sq_nonneg a]
    have h8 : 8 ≤ a ^ 2 - 1 := by nlinarith
    have hs := Real.sqrt_le_sqrt (by exact_mod_cast h8)
    have hq : (1 / 2 : ℝ) ^ 2 < 8 := by norm_num
    have hlt := Real.sqrt_lt_sqrt (by positivity : 0 ≤ (1 / 2 : ℝ) ^ 2) hq
    have hA : Real.sqrt ((1 / 2 : ℝ) ^ 2) = 1 / 2 := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ))]
    have h12 : (1 / 2 : ℝ) < Real.sqrt 8 := by simpa [hA] using hlt
    have : Real.sqrt 8 ≤ Real.sqrt (a ^ 2 - 1) := hs
    nlinarith
  have hpos : 0 ≤ 2 * Real.sqrt (a ^ 2 - 1) := by positivity
  have hlt : 2 * Real.sqrt (a ^ 2 - 1) - 1 < 2 * Real.sqrt (a ^ 2 - 1) := by linarith
  dsimp [beukersR0sharp]
  exact Real.sqrt_lt_sqrt hnn hlt

theorem beukersD_sharp_decay (a : ℝ) (ha : 3 ≤ a) :
    ∃ C : ℝ, 0 < C ∧
      ∀ n : ℕ, ‖(beukersD a n : ℂ)‖ ≤
        C * (2 / (2 * Real.sqrt (a ^ 2 - 1) - beukersRho a)) ^ n := by
  classical
  let R0 : ℝ≥0 := beukersR0sharp a
  have hR0posNN : 0 < R0 := by
    dsimp [R0, beukersR0sharp]
    apply Real.sqrt_pos_of_pos
    have hsq : 0 ≤ a ^ 2 - 1 := by nlinarith [sq_nonneg a]
    have h8 : 8 ≤ a ^ 2 - 1 := by nlinarith
    have hs := Real.sqrt_le_sqrt (by exact_mod_cast h8)
    have hq : (1 / 2 : ℝ) ^ 2 < 8 := by norm_num
    have hlt := Real.sqrt_lt_sqrt (by positivity : 0 ≤ (1 / 2 : ℝ) ^ 2) hq
    have hA : Real.sqrt ((1 / 2 : ℝ) ^ 2) = 1 / 2 := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ))]
    have h12 : (1 / 2 : ℝ) < Real.sqrt 8 := by simpa [hA] using hlt
    have hsqrt : Real.sqrt 8 ≤ Real.sqrt (a ^ 2 - 1) := hs
    nlinarith
  rcases beukersG0_descends_sq_onBall a ha R0 hR0posNN (beukersR0sharp_lt_Ru a ha) with ⟨F, q, hF, hF0, hFdesc⟩
  let g : ℂ → ℂ := beukersApéryRhoExt a F
  have hR0big_ρ : beukersRho a < (R0 : ℝ) ^ 2 := by
    rw [beukersR0sharp_sq a ha]
    have h2 : beukersRho a + 2 < 2 * Real.sqrt (a ^ 2 - 1) := beukers_rho_add_two_lt_two_sqrt a ha
    nlinarith
  -- companion radius Rd := R0² − ρ and Cauchy circle rv := (2√(a²−1) − ρ)/2
  let Rd : ℝ := (R0 : ℝ) ^ 2 - beukersRho a
  let rv : ℝ := (2 * Real.sqrt (a ^ 2 - 1) - beukersRho a) / 2
  have hρ2 : beukersRho a + 2 < 2 * Real.sqrt (a ^ 2 - 1) := beukers_rho_add_two_lt_two_sqrt a ha
  have hr0 : 0 < rv := by
    dsimp [rv]
    nlinarith
  have hrRd : rv < Rd := by
    dsimp [rv, Rd]
    rw [beukersR0sharp_sq a ha]
    nlinarith
  have hr1 : 1 < rv := by
    dsimp [rv]
    nlinarith
  -- g differentiable on ball 0 rv' for some rv' with rv < rv' < Rd (for the closed disc)
  let rv' : ℝ := (rv + Rd) / 2
  have hrr' : rv < rv' := by dsimp [rv']; linarith
  have hr' : rv' < Rd := by dsimp [rv']; linarith
  have hd_ball : DifferentiableOn ℂ g (Metric.ball (0 : ℂ) rv') := by
    have h := beukers_apéry_g_differentiableOn_cuspDisc a ha hR0big_ρ hF rv' hr'
    simpa [g] using h
  have hd_cl : DifferentiableOn ℂ g (Metric.closedBall (0 : ℂ) rv) := by
    exact hd_ball.mono (Metric.closedBall_subset_ball hrr')
  -- M bound on the closed disc (ingredient (ii))
  rcases beukersApéryRhoExt_bddOn_closedBall a ha hR0big_ρ hF hrRd with ⟨M, hM0, hM⟩
  have hM_sphere : ∀ z : ℂ, z ∈ Metric.sphere (0 : ℂ) rv → ‖g z‖ ≤ M := by
    intro z hz
    have hmem : z ∈ Metric.closedBall (0 : ℂ) rv := by
      rw [Metric.mem_closedBall]
      have hzn : ‖z‖ = rv := by simpa [dist_zero_right] using hz
      rw [Metric.mem_sphere] at hz
      linarith
    simpa [g] using (hM z hmem)
  -- the series: ofScalars of the d-coefficients
  let cseq : ℕ → ℂ := fun n => (beukersD a n : ℂ)
  let p0 : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ cseq
  have hFPS0 : HasFPowerSeriesAt g p0 0 := by
    have h1 := beukers_apéry_g_hasFPowerSeriesAt a ha hR0big_ρ hF hFdesc
    dsimp [g, p0, cseq]
    simpa [beukersD] using h1
  have hrv0 : 0 ≤ rv := le_of_lt hr0
  let Rv : ℝ≥0 := ⟨rv, hrv0⟩
  have hd_clR : DifferentiableOn ℂ g (Metric.closedBall (0 : ℂ) Rv) := hd_cl
  have hRnn : 0 < Rv := by exact_mod_cast hr0
  have hp_ball : HasFPowerSeriesOnBall g (cauchyPowerSeries g (0 : ℂ) Rv) (0 : ℂ) Rv :=
    DifferentiableOn.hasFPowerSeriesOnBall hd_clR hRnn
  have hEqSeries : cauchyPowerSeries g (0 : ℂ) Rv = p0 := by
    exact hp_ball.hasFPowerSeriesAt.eq_formalMultilinearSeries hFPS0
  have hp0ball : HasFPowerSeriesOnBall g p0 (0 : ℂ) Rv := by
    simpa [hEqSeries] using hp_ball
  have hp_final : HasFPowerSeriesOnBall g p0 (0 : ℂ) (ENNReal.ofReal rv) := by
    rw [ENNReal.ofReal_eq_coe_nnreal hrv0]
    exact hp0ball
  refine ⟨M + 1, by positivity, ?_⟩
  intro n
  have hcau := Commons.Analysis.Complex.cauchy_coeff_bound (f := g) (ρ := rv) (M := M)
    hr0 hM_sphere hd_cl hp_final n
  have hpcoeff : p0 n (fun _ : Fin n => (1 : ℂ)) = (beukersD a n : ℂ) := by
    dsimp [p0, cseq]
    simp
  calc
    ‖(beukersD a n : ℂ)‖ = ‖p0 n (fun _ : Fin n => (1 : ℂ))‖ := by rw [hpcoeff]
    _ ≤ M / rv ^ n := hcau
    _ ≤ (M + 1) / rv ^ n := by
      have hpow : 0 < rv ^ n := pow_pos hr0 n
      have hinv : 0 ≤ (rv ^ n)⁻¹ := le_of_lt (inv_pos.mpr hpow)
      have hle : M ≤ M + 1 := by linarith
      calc
        M / rv ^ n = M * (rv ^ n)⁻¹ := by rw [div_eq_mul_inv]
        _ ≤ (M + 1) * (rv ^ n)⁻¹ := mul_le_mul_of_nonneg_right hle hinv
        _ = (M + 1) / rv ^ n := by rw [div_eq_mul_inv]
    _ = (M + 1) * (2 / (2 * Real.sqrt (a ^ 2 - 1) - beukersRho a)) ^ n := by
      have hrv2 : rv = (2 * Real.sqrt (a ^ 2 - 1) - beukersRho a) / 2 := rfl
      have hden : 2 * Real.sqrt (a ^ 2 - 1) - beukersRho a ≠ 0 := by
        have hpos : 0 < 2 * Real.sqrt (a ^ 2 - 1) - beukersRho a := by
          have h2 : beukersRho a + 2 < 2 * Real.sqrt (a ^ 2 - 1) := beukers_rho_add_two_lt_two_sqrt a ha
          nlinarith
        exact ne_of_gt hpos
      have hbase : (1 / rv) = 2 / (2 * Real.sqrt (a ^ 2 - 1) - beukersRho a) := by
        dsimp [rv]
        field_simp [hden, ne_of_gt hr0]
      have hpow_ : (1 / rv) ^ n = (2 / (2 * Real.sqrt (a ^ 2 - 1) - beukersRho a)) ^ n := by rw [hbase]
      calc
        (M + 1) / rv ^ n = (M + 1) * (1 / rv) ^ n := by
          rw [div_eq_mul_inv]
          congr 1
          rw [← inv_pow, one_div]
        _ = (M + 1) * (2 / (2 * Real.sqrt (a ^ 2 - 1) - beukersRho a)) ^ n := by rw [hbase]




/-! ## Target 1 — sharp `u`-growth: statement and first brick

Precise target-1 lemma (the statement to prove; see the rationale above):

```lean
-- |u_n(b)| ≤ C·(b + √(b²−1))^n·(1+ε)^n, equivalently: the coefficients of
-- Aℂ(b, ·) decay from a Cauchy circle of any radius r < ρ_b with the sup
-- M(r) = ((ρ_b − r)·(1/ρ_b − r))^(−1/2)
lemma beukersUR_sharp_growth_target (b : ℝ) (hb : 3 ≤ b) :
    ∃ C : ℝ, 0 < C ∧
      ∀ n : ℕ, |beukersUR b n| ≤
        C * (b + Real.sqrt (b ^ 2 - 1)) ^ n * (n + 1)
-- (first instance; an (1+ε)-refinement and the M(r) form follow from the
--  Cauchy pipeline with Aℂ's power-series coefficients
--  `beukersAComplex_coeff_eq`)
```

First brick — the quadratic identity behind the factorization:
`ρ_b` (a root of `T² − 2bT + 1`) satisfies `ρ² − 2bρ + 1 = 0`, so
`Q_b(z) = z² − 2bz + 1 = (z − ρ_b)·(z − (2b − ρ_b))` (since
`ρ_b·(2b − ρ_b) = 1`).  Proved here.
-/

/-- `ρ_b` is a root of `T² − 2bT + 1` (for `b ≥ 3`; `ρ_b := b − √(b²−1)`) -/
lemma beukers_rho_quadratic (b : ℝ) (hb : 3 ≤ b) :
    beukersRho b ^ 2 - 2 * b * beukersRho b + 1 = 0 := by
  have hsq : (Real.sqrt (b ^ 2 - 1)) ^ 2 = b ^ 2 - 1 := by
    rw [Real.sq_sqrt]
    nlinarith [sq_nonneg b]
  unfold beukersRho
  nlinarith

/-- `ρ_b·(2b − ρ_b) = 1` (i.e. `2b − ρ_b = 1/ρ_b`, the far root of the
quadratic) -/
lemma beukers_rho_mul_two_mul_sub (b : ℝ) (hb : 3 ≤ b) :
    beukersRho b * (2 * b - beukersRho b) = 1 := by
  have hq := beukers_rho_quadratic b hb
  nlinarith

/-- the factorization `Q_b(z) = z² − 2bz + 1 = (z − ρ_b)·(z − (2b − ρ_b))`
over `ℂ` (the two roots of the quadratic are `ρ_b` and `1/ρ_b = 2b − ρ_b`) -/
lemma beukers_quadC_factor (b : ℝ) (hb : 3 ≤ b) (z : ℂ) :
    beukersQuadC b z = (z - (beukersRho b : ℂ)) * (z - ((2 * b - beukersRho b : ℝ) : ℂ)) := by
  have hmm := beukers_rho_mul_two_mul_sub b hb
  have hprodC : ((beukersRho b : ℂ) * ((2 * b - beukersRho b : ℝ) : ℂ)) = 1 := by
    have hc := congrArg (fun t : ℝ => (t : ℂ)) hmm
    rw [← Complex.ofReal_mul]
    exact hc
  have hsumC : ((beukersRho b : ℂ) + ((2 * b - beukersRho b : ℝ) : ℂ)) = 2 * (b : ℂ) := by
    have hr : beukersRho b + (2 * b - beukersRho b) = 2 * b := by ring
    have hc := congrArg (fun t : ℝ => (t : ℂ)) hr
    rw [← Complex.ofReal_add]
    simp
  calc
    beukersQuadC b z = z ^ 2 - 2 * (b : ℂ) * z + 1 := by
          dsimp [beukersQuadC]
          ring
    _ = z ^ 2 - (((beukersRho b : ℂ) + ((2 * b - beukersRho b : ℝ) : ℂ))) * z + 1 := by
          rw [← hsumC]
    _ = (z - (beukersRho b : ℂ)) * (z - ((2 * b - beukersRho b : ℝ) : ℂ)) := by
          rw [← hprodC]
          ring


/-- one-sided reverse triangle: `‖z − (w : ℂ)‖ ≥ w − ‖z‖` for real `w ≥ 0` -/
lemma abs_sub_real_ge (w : ℝ) (hw0 : 0 ≤ w) (z : ℂ) : w - ‖z‖ ≤ ‖z - (w : ℂ)‖ := by
  have htri2 : ‖(w : ℂ)‖ ≤ ‖z‖ + ‖z - (w : ℂ)‖ := by
    have h' := norm_sub_le z (z - (w : ℂ))
    have hz : z - (z - (w : ℂ)) = (w : ℂ) := by ring
    rw [hz] at h'
    exact h'
  have hnw : ‖(w : ℂ)‖ = w := by simp [abs_of_nonneg hw0]
  rw [hnw] at htri2
  linarith

/-- `2b − ρ_b = 1/ρ_b` (from `ρ_b·(2b − ρ_b) = 1`) -/
lemma beukers_two_mul_sub_eq_inv (b : ℝ) (hb : 3 ≤ b) :
    2 * b - beukersRho b = (beukersRho b)⁻¹ := by
  have hmm := beukers_rho_mul_two_mul_sub b hb
  have hρne : beukersRho b ≠ 0 := ne_of_gt (beukers_rho_pos b hb)
  have hc : beukersRho b * (2 * b - beukersRho b) = beukersRho b * (beukersRho b)⁻¹ := by
    rw [hmm]
    rw [mul_inv_cancel₀ hρne]
  exact mul_left_cancel₀ hρne hc

/-- the product lower bound: on `‖z‖ ≤ r < ρ_b`, `|Q_b(z)| ≥ (ρ_b − r)·(1/ρ_b − r)` -/
lemma beukers_quadC_abs_lower (b : ℝ) (hb : 3 ≤ b) {z : ℂ} {r : ℝ}
    (hz : ‖z‖ ≤ r) (hr : r < beukersRho b) :
    (beukersRho b - r) * ((beukersRho b)⁻¹ - r) ≤ ‖beukersQuadC b z‖ := by
  have hρpos : 0 < beukersRho b := beukers_rho_pos b hb
  have hρ0 : 0 ≤ beukersRho b := le_of_lt hρpos
  have hs0 : 0 ≤ 2 * b - beukersRho b := by
    have hρb : beukersRho b ≤ b := by
      unfold beukersRho
      have hsqrt : 0 ≤ Real.sqrt (b ^ 2 - 1) := Real.sqrt_nonneg _
      nlinarith
    nlinarith
  have hρs : beukersRho b < 2 * b - beukersRho b := by
    have hρb : beukersRho b < b := by
      unfold beukersRho
      have hs : 0 < Real.sqrt (b ^ 2 - 1) := by
        apply Real.sqrt_pos_of_pos
        nlinarith [sq_nonneg b]
      linarith
    linarith
  have h1 : beukersRho b - ‖z‖ ≤ ‖z - (beukersRho b : ℂ)‖ := abs_sub_real_ge (beukersRho b) hρ0 z
  have h2 : (2 * b - beukersRho b) - ‖z‖ ≤ ‖z - ((2 * b - beukersRho b : ℝ) : ℂ)‖ :=
    abs_sub_real_ge (2 * b - beukersRho b) hs0 z
  have hz1 : beukersRho b - r ≤ ‖z - (beukersRho b : ℂ)‖ := by linarith
  have hz2 : (2 * b - beukersRho b) - r ≤ ‖z - ((2 * b - beukersRho b : ℝ) : ℂ)‖ := by linarith
  have hnr1 : 0 ≤ ‖z - (beukersRho b : ℂ)‖ := norm_nonneg _
  have hposc : 0 ≤ (2 * b - beukersRho b) - r := by linarith
  have hprod : (beukersRho b - r) * ((2 * b - beukersRho b) - r) ≤ ‖beukersQuadC b z‖ := by
    rw [beukers_quadC_factor b hb z]
    rw [norm_mul]
    exact mul_le_mul hz1 hz2 hposc hnr1
  have hEq := beukers_two_mul_sub_eq_inv b hb
  rw [hEq] at hprod
  -- goal: (ρ−r)(ρ⁻¹−r) ≤ ‖Q‖ ; hprod has (ρ−r)((2b−ρ)−r) ≤ ‖Q‖ with (2b−ρ) replaced by ρ⁻¹
  exact hprod

/-! ## Sharp `u`-growth and the beyond-cusp bound (analytic targets 1, 3)

The complex-analytic step of target 1: `Q_b(z) = z² − 2bz + 1` maps the
closed disc `‖z‖ ≤ r < ρ_b` into the slit plane (`beukersQuadC_im`,
`beukers_rho_lt_one`, `beukersQuadC_mem_slitPlane_of_norm_le` — the negative
real preimages of `Q_b` are the real points `|x| ≥ ρ_b`), hence
`Aℂ(b,·) = 1/√Q_b` is holomorphic on every such closed disc
(`DifferentiableOn` via `beukersAComplex_analyticAt_of_slitPlane`) with the
explicit sup bound `beukersAComplex_norm_le`; `‖√q‖ = √‖q‖` is
`norm_sqrt_of_mem_slitPlane`.  The Cauchy pipeline then gives
`beukersUR_cauchy_growth` (any radius `r < ρ_b`), and the product with the
sharp `d`-decay (`beukersD_sharp_decay`) at the radius
`r = ρ_b·(s_d·ρ_a+1)/2` gives the beyond-cusp bound
`beukersPaCoeff_beyond_cusp` (target 3: `s·ρ_a·ρ_b < 1`).
-/

lemma beukersQuadC_im (b : ℝ) (z : ℂ) : (beukersQuadC b z).im = 2 * z.im * (z.re - b) := by
  have hz : z = (z.re : ℂ) + z.im * Complex.I := by rw [Complex.re_add_im]
  dsimp [beukersQuadC]
  rw [hz]
  simp only [Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.add_re,
    Complex.ofReal_im, Complex.ofReal_re, Complex.I_im, Complex.I_re, pow_two]
  norm_num
  ring

lemma beukers_rho_lt_one (b : ℝ) (hb : 3 ≤ b) : beukersRho b < 1 := by
  have hsq : (b - 1) ^ 2 < b ^ 2 - 1 := by nlinarith [sq_nonneg b]
  have hlt := Real.sqrt_lt_sqrt (by positivity : 0 ≤ (b - 1) ^ 2) hsq
  have hA : Real.sqrt ((b - 1) ^ 2) = b - 1 := by
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by linarith : 0 ≤ b - 1)]
  have hsqrt : b - 1 < Real.sqrt (b ^ 2 - 1) := by simpa [hA] using hlt
  unfold beukersRho
  linarith

/-- `Q_b(z) ∈ slitPlane` on the closed disc `‖z‖ ≤ r < ρ_b` -/
lemma beukersQuadC_mem_slitPlane_of_norm_le (b : ℝ) (hb : 3 ≤ b) {z : ℂ} {r : ℝ}
    (hz : ‖z‖ ≤ r) (hr : r < beukersRho b) : beukersQuadC b z ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_cases hIm : (beukersQuadC b z).im = 0
  · left
    have hfac : z.im * (z.re - b) = 0 := by
      have h := beukersQuadC_im b z
      rw [hIm] at h
      nlinarith
    rcases mul_eq_zero.mp hfac with hzi | hzb
    · have hzr : z = (z.re : ℂ) := by
        apply Complex.ext
        · rfl
        · simp [hzi]
      have hzQ : beukersQuadC b z = (beukersQuad b z.re : ℂ) := by
        rw [hzr, beukersQuadC_ofReal]
        simp
      have hxρ : z.re < beukersRho b := by
        have hle : z.re ≤ r := by
          calc
            z.re ≤ |z.re| := le_abs_self z.re
            _ ≤ ‖z‖ := Complex.abs_re_le_norm z
            _ ≤ r := hz
        linarith
      have hQpos : 0 < beukersQuad b z.re := beukersQuad_pos_of_lt_rho b z.re hb hxρ
      show 0 < (beukersQuadC b z).re
      rw [hzQ]
      rw [Complex.ofReal_re]
      exact hQpos
    · have hle : b ≤ r := by
        calc
          b = z.re := by linarith
          _ ≤ ‖z‖ := Complex.re_le_norm z
          _ ≤ r := hz
      have hρb : beukersRho b < b := beukers_rho_lt_a b hb
      linarith
  · right
    exact hIm

/-- the norm of the complex square root on `ℂ` is the real square root of the norm -/
lemma norm_sqrt_of_mem_slitPlane {q : ℂ} (hq : q ∈ Complex.slitPlane) :
    ‖Complex.sqrt q‖ = Real.sqrt ‖q‖ := by
  have hsq : (Complex.sqrt q) ^ 2 = q := by
    exact Commons.Analysis.Complex.sq_sqrt_of_slitPlane hq
  have hnorm2 : ‖Complex.sqrt q‖ ^ 2 = ‖q‖ := by
    calc
      ‖Complex.sqrt q‖ ^ 2 = ‖Complex.sqrt q‖ * ‖Complex.sqrt q‖ := by rw [pow_two]
      _ = ‖Complex.sqrt q * Complex.sqrt q‖ := by rw [norm_mul]
      _ = ‖(Complex.sqrt q) ^ 2‖ := by rw [pow_two]
      _ = ‖q‖ := by rw [hsq]
  have hnn : 0 ≤ ‖Complex.sqrt q‖ := norm_nonneg _
  rw [← hnorm2]
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hnn]

/-- sup bound of `Aℂ(b,·) = 1/√Q_b` on the closed disc `‖z‖ ≤ r < ρ_b`:
`‖Aℂ(b,z)‖ ≤ 1/√((ρ_b − r)(ρ_b⁻¹ − r))` -/
lemma beukersAComplex_norm_le (b : ℝ) (hb : 3 ≤ b) {z : ℂ} {r : ℝ}
    (hz : ‖z‖ ≤ r) (hr : r < beukersRho b) :
    ‖beukersAComplex b z‖ ≤ (Real.sqrt ((beukersRho b - r) * ((beukersRho b)⁻¹ - r)))⁻¹ := by
  have hQslit : beukersQuadC b z ∈ Complex.slitPlane :=
    beukersQuadC_mem_slitPlane_of_norm_le b hb hz hr
  have hQnz : beukersQuadC b z ≠ 0 := Complex.slitPlane_ne_zero hQslit
  have hlb := beukers_quadC_abs_lower b hb hz hr
  have hρpos : 0 < beukersRho b := beukers_rho_pos b hb
  have hρlt1 : beukersRho b < 1 := beukers_rho_lt_one b hb
  have hρinv1 : 1 < (beukersRho b)⁻¹ := (one_lt_inv₀ hρpos).2 hρlt1
  have hprod_pos : 0 < (beukersRho b - r) * ((beukersRho b)⁻¹ - r) := by
    apply mul_pos
    · linarith
    · have hrρinv : r < (beukersRho b)⁻¹ := lt_trans hr (lt_trans hρlt1 hρinv1)
      linarith
  have hsqrt_pos : 0 < Real.sqrt ((beukersRho b - r) * ((beukersRho b)⁻¹ - r)) :=
    Real.sqrt_pos.2 hprod_pos
  have hnorm_sqrt : ‖Complex.sqrt (beukersQuadC b z)‖ = Real.sqrt ‖beukersQuadC b z‖ :=
    norm_sqrt_of_mem_slitPlane hQslit
  have hsqrt_lb : Real.sqrt ((beukersRho b - r) * ((beukersRho b)⁻¹ - r)) ≤
      Real.sqrt ‖beukersQuadC b z‖ := by
    exact Real.sqrt_le_sqrt hlb
  have hsqrt_ge : Real.sqrt ((beukersRho b - r) * ((beukersRho b)⁻¹ - r)) ≤
      ‖Complex.sqrt (beukersQuadC b z)‖ := by
    rwa [hnorm_sqrt]
  have hsqrt_norm_pos : 0 < ‖Complex.sqrt (beukersQuadC b z)‖ :=
    lt_of_lt_of_le hsqrt_pos hsqrt_ge
  dsimp [beukersAComplex]
  rw [norm_inv]
  exact (inv_le_inv₀ hsqrt_norm_pos hsqrt_pos).2 hsqrt_ge

/-- sharp Cauchy growth of the `u`-coefficients of `Aℂ(b,·)` at any radius
`r < ρ_b` (the nearest singularity of the generating series of `u_n(b)`):
`|u_n(b)| ≤ C / r^n` with an `r`-dependent constant -/
theorem beukersUR_cauchy_growth (b : ℝ) (hb : 3 ≤ b) {r : ℝ} (hr0 : 0 < r)
    (hrρ : r < beukersRho b) : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, |beukersUR b n| ≤ C / r ^ n := by
  classical
  let M : ℝ := (Real.sqrt ((beukersRho b - r) * ((beukersRho b)⁻¹ - r)))⁻¹
  have hρpos : 0 < beukersRho b := beukers_rho_pos b hb
  have hρlt1 : beukersRho b < 1 := beukers_rho_lt_one b hb
  have hρinv1 : 1 < (beukersRho b)⁻¹ := (one_lt_inv₀ hρpos).2 hρlt1
  have hrρinv : r < (beukersRho b)⁻¹ := lt_trans hrρ (lt_trans hρlt1 hρinv1)
  have hprod_pos : 0 < (beukersRho b - r) * ((beukersRho b)⁻¹ - r) := by
    apply mul_pos <;> linarith
  have hM0 : 0 < M := by
    dsimp [M]
    exact inv_pos.mpr (Real.sqrt_pos.2 hprod_pos)
  -- differentiability of Aℂ on the closed disc of radius r
  have hd_cl : DifferentiableOn ℂ (beukersAComplex b) (Metric.closedBall (0 : ℂ) r) := by
    intro z hz
    have hzr : ‖z‖ ≤ r := by simpa using (Metric.mem_closedBall.mp hz)
    have hzρ : ‖z‖ < beukersRho b := lt_of_le_of_lt hzr hrρ
    have hQslit : beukersQuadC b z ∈ Complex.slitPlane :=
      beukersQuadC_mem_slitPlane_of_norm_le b hb (r := ‖z‖) le_rfl hzρ
    exact (beukersAComplex_analyticAt_of_slitPlane b hQslit).differentiableAt.differentiableWithinAt
  -- M bounds Aℂ on the sphere of radius r (hence on the whole closed disc)
  have hM_sphere : ∀ z : ℂ, z ∈ Metric.sphere (0 : ℂ) r → ‖beukersAComplex b z‖ ≤ M := by
    intro z hz
    have hzn : ‖z‖ = r := by simpa [dist_zero_right] using hz
    have hzr : ‖z‖ ≤ r := by linarith
    have hle := beukersAComplex_norm_le b hb hzr hrρ
    simpa [M] using hle
  -- the coefficient series p0 of Aℂ at 0
  let p0 : FormalMultilinearSeries ℂ ℂ ℂ :=
    FormalMultilinearSeries.ofScalars ℂ (fun n : ℕ => (beukersUR b n : ℂ))
  have hFPS0 : HasFPowerSeriesAt (beukersAComplex b) p0 0 := by
    let pC : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ
      (fun n : ℕ => iteratedDeriv (𝕜 := ℂ) n (beukersAComplex b) 0 / (n.factorial : ℂ))
    have hcanon : HasFPowerSeriesAt (beukersAComplex b) pC 0 := by
      simpa [pC] using (AnalyticAt.hasFPowerSeriesAt (beukersAComplex_analyticAt_zero b))
    rw [hasFPowerSeriesAt_iff] at hcanon ⊢
    filter_upwards [hcanon] with z hz
    refine hz.congr_fun ?_
    intro n
    simp [pC, p0, beukersAComplex_coeff_eq b hb n]
  have hrv0 : 0 ≤ r := le_of_lt hr0
  let Rv : ℝ≥0 := ⟨r, hrv0⟩
  have hRnn : 0 < Rv := by exact_mod_cast hr0
  have hp_ball : HasFPowerSeriesOnBall (beukersAComplex b)
      (cauchyPowerSeries (beukersAComplex b) (0 : ℂ) Rv) (0 : ℂ) Rv :=
    DifferentiableOn.hasFPowerSeriesOnBall hd_cl hRnn
  have hEqSeries : cauchyPowerSeries (beukersAComplex b) (0 : ℂ) Rv = p0 := by
    exact hp_ball.hasFPowerSeriesAt.eq_formalMultilinearSeries hFPS0
  have hp0ball : HasFPowerSeriesOnBall (beukersAComplex b) p0 (0 : ℂ) Rv := by
    simpa [hEqSeries] using hp_ball
  have hp_final : HasFPowerSeriesOnBall (beukersAComplex b) p0 (0 : ℂ) (ENNReal.ofReal r) := by
    rw [ENNReal.ofReal_eq_coe_nnreal hrv0]
    exact hp0ball
  refine ⟨M + 1, by positivity, ?_⟩
  intro n
  have hcau := Commons.Analysis.Complex.cauchy_coeff_bound (f := beukersAComplex b) (ρ := r) (M := M)
    hr0 hM_sphere hd_cl hp_final n
  have hpcoeff : p0 n (fun _ : Fin n => (1 : ℂ)) = (beukersUR b n : ℂ) := by
    dsimp [p0]
    simp
  calc
    |beukersUR b n| = ‖(beukersUR b n : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    _ = ‖p0 n (fun _ : Fin n => (1 : ℂ))‖ := by rw [hpcoeff]
    _ ≤ M / r ^ n := hcau
    _ ≤ (M + 1) / r ^ n := by
      have hpow : 0 < r ^ n := pow_pos hr0 n
      have hinv : 0 ≤ (r ^ n)⁻¹ := le_of_lt (inv_pos.mpr hpow)
      have hle : M ≤ M + 1 := by linarith
      calc
        M / r ^ n = M * (r ^ n)⁻¹ := by rw [div_eq_mul_inv]
        _ ≤ (M + 1) * (r ^ n)⁻¹ := mul_le_mul_of_nonneg_right hle hinv
        _ = (M + 1) / r ^ n := by rw [div_eq_mul_inv]

lemma beukers_three_rho_lt_two_sqrt (a : ℝ) (ha : 3 ≤ a) :
    3 * beukersRho a < 2 * Real.sqrt (a ^ 2 - 1) := by
  have hρ1 : beukersRho a < 1 := beukers_rho_lt_one a ha
  have hsum : 3 * beukersRho a < beukersRho a + 2 := by nlinarith
  exact lt_trans hsum (beukers_rho_add_two_lt_two_sqrt a ha)

/-- target 3 (beyond the smallest cusp): the `P_a = D_a ⋆ A_b` coefficients
`d_n(a)·u_n(b)` grow at most like `C·s^n` with `s·(ρ_a·ρ_b) < 1` -/
theorem beukersPaCoeff_beyond_cusp (a b : ℝ) (ha : 3 ≤ a) (hb : 3 ≤ b) :
    ∃ C s : ℝ, 0 < C ∧ 0 < s ∧
      s * ((a - Real.sqrt (a ^ 2 - 1)) * (b - Real.sqrt (b ^ 2 - 1))) < 1 ∧
      ∀ n : ℕ, |beukersPaCoeff a b n| ≤ C * s ^ n := by
  classical
  rcases beukersD_sharp_decay a ha with ⟨Cd, hCd0, hd⟩
  let sd : ℝ := 2 / (2 * Real.sqrt (a ^ 2 - 1) - beukersRho a)
  have hden_pos : 0 < 2 * Real.sqrt (a ^ 2 - 1) - beukersRho a := by
    have h2 : beukersRho a + 2 < 2 * Real.sqrt (a ^ 2 - 1) := beukers_rho_add_two_lt_two_sqrt a ha
    nlinarith
  have h3ρ : 3 * beukersRho a < 2 * Real.sqrt (a ^ 2 - 1) := beukers_three_rho_lt_two_sqrt a ha
  have h2ρlt : 2 * beukersRho a < 2 * Real.sqrt (a ^ 2 - 1) - beukersRho a := by nlinarith
  have hsd_pos : 0 < sd := by
    dsimp [sd]
    exact div_pos (by norm_num) hden_pos
  have hρa0 : 0 < beukersRho a := beukers_rho_pos a ha
  have hsda_pos : 0 < sd * beukersRho a := mul_pos hsd_pos hρa0
  have hsda : sd * beukersRho a < 1 := by
    have hstep : (2 / (2 * Real.sqrt (a ^ 2 - 1) - beukersRho a)) * beukersRho a =
        (2 * beukersRho a) / (2 * Real.sqrt (a ^ 2 - 1) - beukersRho a) := by ring
    rw [hstep]
    exact (div_lt_one hden_pos).2 h2ρlt
  let c : ℝ := (sd * beukersRho a + 1) / 2
  have hc0 : 0 < c := by
    dsimp [c]
    positivity
  have hc_gt : sd * beukersRho a < c := by
    dsimp [c]
    linarith
  have hc1 : c < 1 := by
    dsimp [c]
    linarith
  have hρb0 : 0 < beukersRho b := beukers_rho_pos b hb
  have hr0 : 0 < beukersRho b * c := mul_pos hρb0 hc0
  have hrρ : beukersRho b * c < beukersRho b := by
    have hcpos : c > 0 := hc0
    nlinarith
  rcases beukersUR_cauchy_growth b hb hr0 hrρ with ⟨Cu, hCu0, hu⟩
  let s : ℝ := sd / (beukersRho b * c)
  have hs0 : 0 < s := by
    dsimp [s]
    exact div_pos hsd_pos (mul_pos hρb0 hc0)
  have hsc : s * ((a - Real.sqrt (a ^ 2 - 1)) * (b - Real.sqrt (b ^ 2 - 1))) < 1 := by
    have hρa : beukersRho a = a - Real.sqrt (a ^ 2 - 1) := rfl
    have hρb : beukersRho b = b - Real.sqrt (b ^ 2 - 1) := rfl
    -- goal: s · (ρ_a·ρ_b) < 1 ⟺ (sd·ρ_a)/c < 1
    have hbne : beukersRho b ≠ 0 := ne_of_gt hρb0
    have hcne : c ≠ 0 := ne_of_gt hc0
    have hcalc : s * (beukersRho a * beukersRho b) = (sd * beukersRho a) / c := by
      dsimp [s]
      field_simp [hbne, hcne]
    have hprod : s * (beukersRho a * beukersRho b) < 1 := by
      rw [hcalc]
      -- (sd ρa)/c < 1 ⟺ sd ρa < c (c > 0)
      exact (div_lt_one hc0).2 hc_gt
    -- reshape multiplication order
    calc
      s * ((a - Real.sqrt (a ^ 2 - 1)) * (b - Real.sqrt (b ^ 2 - 1)))
          = s * (beukersRho a * beukersRho b) := by rw [← hρa, ← hρb]
      _ < 1 := hprod
  refine ⟨Cd * Cu + 1, s, by positivity, hs0, hsc, ?_⟩
  intro n
  have hdn : |beukersD a n| ≤ Cd * sd ^ n := by
    have h := hd n
    -- ‖(D:ℂ)‖ ≤ Cd·sd^n ; |D| = ‖(D:ℂ)‖
    have hnorm : ‖(beukersD a n : ℂ)‖ = |beukersD a n| := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    rw [hnorm] at h
    simpa [sd] using h
  have hun : |beukersUR b n| ≤ Cu / (beukersRho b * c) ^ n := hu n
  calc
    |beukersPaCoeff a b n| = |beukersD a n * beukersUR b n| := rfl
    _ ≤ |beukersD a n| * |beukersUR b n| := by rw [abs_mul]
    _ ≤ (Cd * sd ^ n) * (Cu / (beukersRho b * c) ^ n) := mul_le_mul hdn hun (abs_nonneg _) (by positivity)
    _ = (Cd * Cu) * (sd / (beukersRho b * c)) ^ n := by
          have hpp : (sd / (beukersRho b * c)) ^ n = sd ^ n / (beukersRho b * c) ^ n := div_pow sd (beukersRho b * c) n
          rw [hpp]
          field_simp [ne_of_gt hr0]
    _ ≤ (Cd * Cu + 1) * s ^ n := by
          dsimp [s]
          have hs0' : 0 ≤ (sd / (beukersRho b * c)) ^ n := by positivity
          have hmain : Cd * Cu ≤ Cd * Cu + 1 := by linarith
          calc
            (Cd * Cu) * (sd / (beukersRho b * c)) ^ n
                ≤ (Cd * Cu + 1) * (sd / (beukersRho b * c)) ^ n := by
                    exact mul_le_mul_of_nonneg_right hmain hs0'
            _ = (Cd * Cu + 1) * s ^ n := by rfl

/-- beyond the smallest cusp for `P_b = A(a) ⋆ (H(b) − η_b·A(b))`:
`|u_n(a)·d_n(b)| ≤ C·sⁿ` with `s·ρ_a·ρ_b < 1` (swap of the `P_a` claim) -/
theorem beukersPbCoeff_beyond_cusp (a b : ℝ) (ha : 3 ≤ a) (hb : 3 ≤ b) :
    ∃ C s : ℝ, 0 < C ∧ 0 < s ∧
      s * ((a - Real.sqrt (a ^ 2 - 1)) * (b - Real.sqrt (b ^ 2 - 1))) < 1 ∧
      ∀ n : ℕ, |beukersPbCoeff a b n| ≤ C * s ^ n := by
  rcases beukersPaCoeff_beyond_cusp b a hb ha with ⟨C, s, hC, hs, hsc, hbnd⟩
  refine ⟨C, s, hC, hs, ?_, ?_⟩
  · have hρa : beukersRho a = a - Real.sqrt (a ^ 2 - 1) := rfl
    have hρb : beukersRho b = b - Real.sqrt (b ^ 2 - 1) := rfl
    -- hsc : s·(ρ_b·ρ_a) < 1
    calc
      s * ((a - Real.sqrt (a ^ 2 - 1)) * (b - Real.sqrt (b ^ 2 - 1)))
          = s * ((b - Real.sqrt (b ^ 2 - 1)) * (a - Real.sqrt (a ^ 2 - 1))) := by ring
      _ < 1 := by simpa [hρa, hρb] using hsc
  · intro n
    have h := hbnd n  -- |d_b(n)·u_a(n)| ≤ C s^n
    -- target |u_a(n)·d_b(n)| ≤ C s^n
    have hcast : |beukersPbCoeff a b n| = |beukersD b n * beukersUR a n| := by
      dsimp [beukersPbCoeff]
      rw [abs_mul, abs_mul]
      ring
    rw [hcast]
    exact h

/-- the sharp `d`-decay in real-absolute form, with the base named `sda` -/
lemma beukersD_real_abs_decay (a : ℝ) (ha : 3 ≤ a) :
    ∃ C : ℝ, 0 < C ∧
      ∀ n : ℕ, |beukersD a n| ≤ C * (2 / (2 * Real.sqrt (a ^ 2 - 1) - beukersRho a)) ^ n := by
  rcases beukersD_sharp_decay a ha with ⟨C, hC, hd⟩
  refine ⟨C, hC, ?_⟩
  intro n
  have h := hd n
  rw [Complex.norm_real, Real.norm_eq_abs] at h
  simpa using h

/-- `s_d(a)·ρ_a < 1` where `s_d(a) := 2/(2√(a²−1) − ρ_a)` (the sharp
`d`-decay base overconverges beyond the singularity) -/
lemma beukers_sd_rho_lt_one (a : ℝ) (ha : 3 ≤ a) :
    (2 / (2 * Real.sqrt (a ^ 2 - 1) - beukersRho a)) * beukersRho a < 1 := by
  have hden_pos : 0 < 2 * Real.sqrt (a ^ 2 - 1) - beukersRho a := by
    have h2 : beukersRho a + 2 < 2 * Real.sqrt (a ^ 2 - 1) := beukers_rho_add_two_lt_two_sqrt a ha
    nlinarith
  have h2ρlt : 2 * beukersRho a < 2 * Real.sqrt (a ^ 2 - 1) - beukersRho a := by
    have h3ρ : 3 * beukersRho a < 2 * Real.sqrt (a ^ 2 - 1) := beukers_three_rho_lt_two_sqrt a ha
    nlinarith
  have hstep : (2 / (2 * Real.sqrt (a ^ 2 - 1) - beukersRho a)) * beukersRho a =
      (2 * beukersRho a) / (2 * Real.sqrt (a ^ 2 - 1) - beukersRho a) := by ring
  rw [hstep]
  exact (div_lt_one hden_pos).2 h2ρlt

/-- beyond the smallest cusp for `P_ab = H(a) ⋆ H(b) − η_{a,b}·(A(a) ⋆ A(b))`:
`|P_ab-coeffₙ| ≤ C·sⁿ` with `s·ρ_a·ρ_b < 1` (decomposition
`beukersPabCoeff_decomp` into `η_a·u_a·d_b + η_b·d_a·u_b + d_a·d_b`,
each factor product overconvergent beyond the cusp) -/
theorem beukersPabCoeff_beyond_cusp (a b : ℝ) (ha : 3 ≤ a) (hb : 3 ≤ b) :
    ∃ C s : ℝ, 0 < C ∧ 0 < s ∧
      s * ((a - Real.sqrt (a ^ 2 - 1)) * (b - Real.sqrt (b ^ 2 - 1))) < 1 ∧
      ∀ n : ℕ, |beukersPabCoeff a b n| ≤ C * s ^ n := by
  classical
  let p : ℝ := beukersRho a * beukersRho b
  have hρa0 : 0 < beukersRho a := beukers_rho_pos a ha
  have hρb0 : 0 < beukersRho b := beukers_rho_pos b hb
  have hρp : 0 < p := by dsimp [p]; positivity
  -- P_a / P_b beyond-cusp bounds (each rate < 1/p)
  rcases beukersPaCoeff_beyond_cusp a b ha hb with ⟨Ca, sa, hCa0, hsa0, hsca, hpa⟩
  rcases beukersPbCoeff_beyond_cusp a b ha hb with ⟨Cb, sb, hCb0, hsb0, hscb, hpb⟩
  -- sharp d-decays
  rcases beukersD_real_abs_decay a ha with ⟨Cda, hCda0, hda⟩
  rcases beukersD_real_abs_decay b hb with ⟨Cdb, hCdb0, hdb⟩
  let sda : ℝ := 2 / (2 * Real.sqrt (a ^ 2 - 1) - beukersRho a)
  let sdb : ℝ := 2 / (2 * Real.sqrt (b ^ 2 - 1) - beukersRho b)
  have hdaρa : sda * beukersRho a < 1 := by
    have h := beukers_sd_rho_lt_one a ha
    simpa [sda] using h
  have hdbρb : sdb * beukersRho b < 1 := by
    have h := beukers_sd_rho_lt_one b hb
    simpa [sdb] using h
  have hsdapos : 0 < sda := by
    dsimp [sda]
    exact div_pos (by norm_num) (by
      have h2 : beukersRho a + 2 < 2 * Real.sqrt (a ^ 2 - 1) := beukers_rho_add_two_lt_two_sqrt a ha
      nlinarith)
  have hsdbpos : 0 < sdb := by
    dsimp [sdb]
    exact div_pos (by norm_num) (by
      have h2 : beukersRho b + 2 < 2 * Real.sqrt (b ^ 2 - 1) := beukers_rho_add_two_lt_two_sqrt b hb
      nlinarith)
  let s3 : ℝ := sda * sdb
  have hs30 : 0 < s3 := mul_pos hsdapos hsdbpos
  have hsc3 : s3 * p < 1 := by
    -- (sda ρa)(sdb ρb) = s3·p < 1
    have hstep : (sda * beukersRho a) * (sdb * beukersRho b) = s3 * p := by
      dsimp [s3, p]
      ring
    have hfirst : (sda * beukersRho a) * (sdb * beukersRho b) < sdb * beukersRho b := by
      simpa [one_mul] using (mul_lt_mul_of_pos_right hdaρa (mul_pos hsdbpos hρb0))
    rw [← hstep]
    exact lt_trans hfirst hdbρb
  -- one base s := max (max sa sb) s3
  let s : ℝ := max (max sa sb) s3
  have hle_a : sa ≤ s := by dsimp [s]; exact le_trans (le_max_left sa sb) (le_max_left (max sa sb) s3)
  have hle_b : sb ≤ s := by dsimp [s]; exact le_trans (le_max_right sa sb) (le_max_left (max sa sb) s3)
  have hle_3 : s3 ≤ s := by dsimp [s]; exact le_max_right (max sa sb) s3
  have hs0 : 0 < s := lt_of_lt_of_le hs30 hle_3
  -- each rate · p < 1
  have hsca' : sa * p < 1 := by simpa [p, beukersRho] using hsca
  have hscb' : sb * p < 1 := by simpa [p, beukersRho] using hscb
  have hs_lt_invp : s < 1 / p := by
    dsimp [s]
    apply max_lt
    · apply max_lt
      · exact (lt_div_iff₀ hρp).2 hsca'
      · exact (lt_div_iff₀ hρp).2 hscb'
    · exact (lt_div_iff₀ hρp).2 hsc3
  have hsc : s * p < 1 := by
    have hmul := mul_lt_mul_of_pos_right hs_lt_invp hρp
    calc
      s * p < (1 / p) * p := hmul
      _ = 1 := by field_simp [ne_of_gt hρp]
  let C0 : ℝ := |beukersEta a| * Cb + |beukersEta b| * Ca + Cda * Cdb
  have hC0pos : 0 < C0 + 1 := by
    have h1 : 0 ≤ |beukersEta a| * Cb := mul_nonneg (abs_nonneg _) (le_of_lt hCb0)
    have h2 : 0 ≤ |beukersEta b| * Ca := mul_nonneg (abs_nonneg _) (le_of_lt hCa0)
    have h3 : 0 ≤ Cda * Cdb := mul_nonneg (le_of_lt hCda0) (le_of_lt hCdb0)
    nlinarith
  refine ⟨C0 + 1, s, hC0pos, hs0, ?_, ?_⟩
  · -- s·((a−√)(b−√)) < 1 : the product IS p
    simpa [p, beukersRho] using hsc
  · intro n
    -- bound each summand
    have hpow0 : 0 ≤ s ^ n := pow_nonneg (le_of_lt hs0) n
    have hpowA : sa ^ n ≤ s ^ n := pow_le_pow_left₀ (le_of_lt hsa0) hle_a n
    have hpowB : sb ^ n ≤ s ^ n := pow_le_pow_left₀ (le_of_lt hsb0) hle_b n
    have hpow3 : s3 ^ n ≤ s ^ n := pow_le_pow_left₀ (le_of_lt hs30) hle_3 n
    -- |u_a d_b| ≤ Cb sb^n ≤ Cb s^n
    have h1 : |beukersUR a n * beukersD b n| ≤ Cb * s ^ n := by
      have h := hpb n
      have hle : Cb * sb ^ n ≤ Cb * s ^ n := by
        exact mul_le_mul_of_nonneg_left hpowB (le_of_lt hCb0)
      exact le_trans h hle
    -- |d_a u_b| ≤ Ca sa^n ≤ Ca s^n
    have h2 : |beukersD a n * beukersUR b n| ≤ Ca * s ^ n := by
      have h := hpa n
      have hle : Ca * sa ^ n ≤ Ca * s ^ n := by
        exact mul_le_mul_of_nonneg_left hpowA (le_of_lt hCa0)
      exact le_trans h hle
    -- |d_a d_b| ≤ Cda·Cdb·s3^n ≤ Cda·Cdb·s^n
    have h3 : |beukersD a n * beukersD b n| ≤ Cda * Cdb * s ^ n := by
      have hda' : |beukersD a n| ≤ Cda * sda ^ n := by
        have h := hda n
        simpa [sda] using h
      have hdb' : |beukersD b n| ≤ Cdb * sdb ^ n := by
        have h := hdb n
        simpa [sdb] using h
      calc
        |beukersD a n * beukersD b n| ≤ |beukersD a n| * |beukersD b n| := by rw [abs_mul]
        _ ≤ (Cda * sda ^ n) * (Cdb * sdb ^ n) := mul_le_mul hda' hdb' (abs_nonneg _) (by positivity : 0 ≤ Cda * sda ^ n)
        _ = (Cda * Cdb) * (sda * sdb) ^ n := by
              rw [mul_pow]
              ring
        _ ≤ (Cda * Cdb) * s ^ n := by
              have hprod : (Cda * Cdb) * s3 ^ n ≤ (Cda * Cdb) * s ^ n := by
                exact mul_le_mul_of_nonneg_left hpow3 (mul_nonneg (le_of_lt hCda0) (le_of_lt hCdb0))
              simpa [s3] using hprod
    -- assemble from the decomposition
    have hdecomp := beukersPabCoeff_decomp a b n
    have htri (x y : ℝ) : |x + y| ≤ |x| + |y| := by
      have h := norm_add_le x y
      simpa [Real.norm_eq_abs] using h
    -- hdecomp: Pab n = η_a·u_a·d_b + η_b·d_a·u_b + d_a·d_b
    calc
      |beukersPabCoeff a b n|
          = |beukersEta a * beukersUR a n * beukersD b n
              + beukersEta b * beukersD a n * beukersUR b n
              + beukersD a n * beukersD b n| := by rw [hdecomp]
      _ ≤ |beukersEta a| * |beukersUR a n * beukersD b n|
            + |beukersEta b| * |beukersD a n * beukersUR b n|
            + |beukersD a n * beukersD b n| := by
              have htri3 (x y z : ℝ) : |x + y + z| ≤ |x| + |y| + |z| := by
                have h12 := htri (x + y) z
                have h1 := htri x y
                nlinarith
              have hη1 : |beukersEta a * beukersUR a n * beukersD b n| = |beukersEta a * (beukersUR a n * beukersD b n)| := by ring_nf
              have hη2 : |beukersEta b * beukersD a n * beukersUR b n| = |beukersEta b * (beukersD a n * beukersUR b n)| := by ring_nf
              have h1m : |beukersEta a * (beukersUR a n * beukersD b n)| = |beukersEta a| * |beukersUR a n * beukersD b n| := by rw [abs_mul]
              have h2m : |beukersEta b * (beukersD a n * beukersUR b n)| = |beukersEta b| * |beukersD a n * beukersUR b n| := by rw [abs_mul]
              calc
                |beukersEta a * beukersUR a n * beukersD b n + beukersEta b * beukersD a n * beukersUR b n + beukersD a n * beukersD b n|
                    ≤ |beukersEta a * beukersUR a n * beukersD b n| + |beukersEta b * beukersD a n * beukersUR b n| + |beukersD a n * beukersD b n| := htri3 _ _ _
                _ = |beukersEta a| * |beukersUR a n * beukersD b n|
                      + |beukersEta b| * |beukersD a n * beukersUR b n|
                      + |beukersD a n * beukersD b n| := by rw [hη1, hη2, h1m, h2m]
      _ ≤ (|beukersEta a| * (Cb * s ^ n)) + (|beukersEta b| * (Ca * s ^ n)) + (Cda * Cdb * s ^ n) := by
              have hm1 : |beukersEta a| * |beukersUR a n * beukersD b n| ≤ |beukersEta a| * (Cb * s ^ n) := by
                exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
              have hm2 : |beukersEta b| * |beukersD a n * beukersUR b n| ≤ |beukersEta b| * (Ca * s ^ n) := by
                exact mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
              have hm3 : |beukersD a n * beukersD b n| ≤ Cda * Cdb * s ^ n := h3
              nlinarith
      _ = (|beukersEta a| * Cb + |beukersEta b| * Ca + Cda * Cdb) * s ^ n := by ring
      _ ≤ (C0 + 1) * s ^ n := by
            dsimp [C0]
            have hmul : (|beukersEta a| * Cb + |beukersEta b| * Ca + Cda * Cdb) * s ^ n
                ≤ (|beukersEta a| * Cb + |beukersEta b| * Ca + Cda * Cdb + 1) * s ^ n := by
              exact mul_le_mul_of_nonneg_right (by linarith) hpow0
            simpa [add_assoc] using hmul


end Submission.CDT
