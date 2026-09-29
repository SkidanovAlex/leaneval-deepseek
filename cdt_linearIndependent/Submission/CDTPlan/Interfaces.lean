import Mathlib

/-!
# cdt_linearIndependent — the fm3 blueprint contracts (orchestrator-owned; do not edit)

Definitions and `Prop`s only.  Each area of the drive proves one of the `Prop`s below (possibly
assuming others as hypotheses); the final proof is composition.  See `HANDOFF.md` at the workspace
root and `REFS/` (paper `REFS/L2chi.tex` = arXiv:2408.15403).

Conventions.
* Power series over `ℚ` are `PowerSeries ℚ`; the variable is `x` (or the symmetrised `y`).
* `lcmUpto N = lcm(1,…,N)` (`lcmUpto 0 = 1`).
* Denominator type (paper eq. `(den type int)`, with the harmless relaxations of Remark
  `rem:overflow`: a fixed shift `c` inside every lcm and a fixed integer factor `K`).
* `ℚ(x)`-linear independence is stated with polynomial coefficients (clear denominators).
-/

open Complex Metric Filter Topology
open scoped BigOperators

namespace Submission.CDTPlan

/-! ## Arithmetic of denominators -/

/-- `lcm(1, …, N)`. -/
def lcmUpto (N : ℕ) : ℕ := (Finset.Icc 1 N).lcm id

/-- `f` has denominator type `K · n^e · ∏_j [1,…,b_j n + c]` for some fixed `K ≥ 1`, `c`:
every coefficient `n ≥ 1` times that quantity is an integer. -/
def HasDenomType {r : ℕ} (e : ℕ) (b : Fin r → ℕ) (f : PowerSeries ℚ) : Prop :=
  ∃ K c : ℕ, 0 < K ∧ ∀ n : ℕ, 1 ≤ n → ∃ a : ℤ,
    ((K : ℚ) * (n : ℚ) ^ e * ∏ j, (lcmUpto (b j * n + c) : ℚ)) * PowerSeries.coeff n f = a

/-- The paper's column shape `(column shape)`: column `j` is `0` on the first `u_j` rows and a
constant `b_j` on the remaining rows. -/
def ColumnShape {m r : ℕ} (b : Fin m → Fin r → ℕ) : Prop :=
  ∀ j : Fin r, ∃ u bj : ℕ, ∀ i : Fin m, b i j = if (i : ℕ) < u then 0 else bj

/-- Row sum `σ_i`. -/
def rowSum {m r : ℕ} (b : Fin m → Fin r → ℕ) (i : Fin m) : ℕ := ∑ j, b i j

/-- `τ♭(b) = (1/m²) Σ_{i=1}^m (2i-1) σ_i` (0-indexed rows: weight `2i+1`). -/
noncomputable def tauFlat {m r : ℕ} (b : Fin m → Fin r → ℕ) : ℝ :=
  (1 / (m : ℝ) ^ 2) * ∑ i : Fin m, (2 * (i : ℝ) + 1) * (rowSum b i : ℝ)

/-- The paper's Definition `integrated lcm` `I_u^v(w)` (verbatim copy of
`Submission.CDT.IntegratedLcm.integratedLcm`; the two are equal by `rfl` after unfolding). -/
noncomputable def harmonicFun (w : ℝ) : ℝ → ℝ :=
  fun t => ∑ h ∈ Finset.Icc 1 ⌊(t - 1) / max 1 w⌋₊, (1 : ℝ) / h

/-- Second integrand of `I_u^v(w)`. -/
noncomputable def correctionFun (w : ℝ) : ℝ → ℝ :=
  fun t => max (t / ((⌊(t + max 0 (w - 1)) / max 1 w⌋₊ : ℕ) : ℝ) - w) 0

/-- `I_u^v(w)` (paper Definition `integrated lcm`). -/
noncomputable def integratedLcm (u v w : ℝ) : ℝ :=
  (∫ t in min u 1..1, max (t - w) 0)
  + (∫ t in max u 1..v, harmonicFun w t)
  + (∫ t in max u 1..v, correctionFun w t)

/-- The quantity minimised in `τ♯(e)` (paper eq. `(taue)`), at a fixed `ξ ∈ [0,m]`;
`τ♯(e) = min_ξ tauSharpAt e ξ`, so any `ξ` gives a valid (weaker) holonomy bound. -/
noncomputable def tauSharpAt {m : ℕ} (e : Fin m → ℕ) (ξ : ℝ) : ℝ :=
  (2 / (m : ℝ) ^ 2) * (ξ * (∑ i, (e i : ℝ)) +
    ((Finset.univ.sup e : ℕ) : ℝ) * integratedLcm ξ m ξ)

/-! ## Functional hypotheses -/

/-- `ℚ(x)`-linear independence of `f₁,…,f_m`, with polynomial coefficients. -/
def PolyIndependent {m : ℕ} (f : Fin m → PowerSeries ℚ) : Prop :=
  ∀ P : Fin m → Polynomial ℚ, ∑ i, (P i : PowerSeries ℚ) * f i = 0 → ∀ i, P i = 0

/-- The `ℚ(x)`-span of `f₁,…,f_m` is closed under `d/dx` (hence every `f_i` is holonomic). -/
def DClosed {m : ℕ} (f : Fin m → PowerSeries ℚ) : Prop :=
  ∃ q : Polynomial ℚ, q ≠ 0 ∧ ∃ A : Fin m → Fin m → Polynomial ℚ,
    ∀ i, (q : PowerSeries ℚ) * PowerSeries.derivative (R := ℚ) (f i) = ∑ j, (A i j : PowerSeries ℚ) * f j

/-- The pullback `f ∘ φ` (a germ at `0`, defined by the convergent series `Σ aₙ φ(z)ⁿ` near `0`)
is meromorphic on the open unit disc, with a polynomial denominator not vanishing at `0`. -/
def PullbackMero (f : PowerSeries ℚ) (φ : ℂ → ℂ) : Prop :=
  ∃ (P : Polynomial ℂ) (N : ℂ → ℂ), P.eval 0 ≠ 0 ∧ DifferentiableOn ℂ N (ball 0 1) ∧
    ∀ᶠ z in 𝓝 (0 : ℂ),
      HasSum (fun n : ℕ => ((PowerSeries.coeff n f : ℚ) : ℂ) * φ z ^ n) (N z / P.eval z)

/-- An admissible analytic map for the holonomy bound: continuous on the closed disc,
holomorphic on the open disc, `φ(0) = 0`, and zero-free on the unit circle. -/
def AdmissibleMap (φ : ℂ → ℂ) : Prop :=
  ContinuousOn φ (closedBall 0 1) ∧ DifferentiableOn ℂ φ (ball 0 1) ∧ φ 0 = 0 ∧
    ∀ z : ℂ, ‖z‖ = 1 → φ z ≠ 0

/-- `t ↦ log |φ(e^{2πit})|`. -/
noncomputable def circleLog (φ : ℂ → ℂ) (t : ℝ) : ℝ :=
  Real.log ‖φ (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)))‖

/-- The rearrangement integral `∫₀¹ 2t g*(t) dt = ∫∫ max(g(s), g(t)) ds dt` of the patched
function `g` (paper eq. `(rearrangement fine)`), written blockwise: block `k` carries the map
`φ k` and has weight `w k = (γ_{k+1} - γ_k)/m`. -/
noncomputable def rearrInt {l : ℕ} (w : Fin (l + 1) → ℝ) (φ : Fin (l + 1) → ℂ → ℂ) : ℝ :=
  ∑ k, ∑ k', w k * w k' *
    ∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, max (circleLog (φ k) s) (circleLog (φ k') t)

/-! ## Area H — the fine holonomy bound (paper Theorem `main:elementary form`, holonomic case) -/

/-- Theorem `main:elementary form` of arXiv:2408.15403, in the a-priori-holonomic case
(`D`-closed span), for conformal maps (`φ_k'(0) ≠ 0`), a fixed `ξ ∈ [0,m]` in `τ♯`, with meromorphic pullbacks having
polynomial denominators, and maps continuous up to the circle. -/
def HolonomyBound : Prop :=
  ∀ (m r l : ℕ) (b : Fin m → Fin r → ℕ) (e : Fin m → ℕ) (f : Fin m → PowerSeries ℚ)
    (φ : Fin (l + 1) → ℂ → ℂ) (γ : Fin (l + 2) → ℝ) (ξ : ℝ),
    0 < m → ColumnShape b → (∀ i, HasDenomType (e i) (b i) (f i)) →
    PolyIndependent f → DClosed f →
    (∀ k, AdmissibleMap (φ k)) → (∀ i k, PullbackMero (f i) (φ k)) →
    (∀ k, 0 < ‖deriv (φ k) 0‖) → StrictMono (fun k => ‖deriv (φ k) 0‖) →
    γ 0 = 0 → γ (Fin.last (l + 1)) = m → StrictMono γ →
    0 ≤ ξ → ξ ≤ m →
    tauFlat b + tauSharpAt e ξ < Real.log ‖deriv (φ (Fin.last l)) 0‖ →
    (m : ℝ) * (Real.log ‖deriv (φ (Fin.last l)) 0‖ - (tauFlat b + tauSharpAt e ξ)) ≤
      rearrInt (fun k => (γ k.succ - γ k.castSucc) / m) φ +
      (1 / (m : ℝ)) * ∑ k : Fin l, (γ k.succ.castSucc) ^ 2 *
        Real.log (‖deriv (φ k.succ) 0‖ / ‖deriv (φ k.castSucc) 0‖)

/-- `HolonomyBound` restricted to at most three maps (`l ≤ 2`): all that Theorems A (l = 2) and
C (l = 0) need.  Implied by `HolonomyBound`. -/
def HolonomyBoundL2 : Prop :=
  ∀ (m r l : ℕ) (b : Fin m → Fin r → ℕ) (e : Fin m → ℕ) (f : Fin m → PowerSeries ℚ)
    (φ : Fin (l + 1) → ℂ → ℂ) (γ : Fin (l + 2) → ℝ) (ξ : ℝ),
    0 < m → l ≤ 2 → ColumnShape b → (∀ i, HasDenomType (e i) (b i) (f i)) →
    PolyIndependent f → DClosed f →
    (∀ k, AdmissibleMap (φ k)) → (∀ i k, PullbackMero (f i) (φ k)) →
    (∀ k, 0 < ‖deriv (φ k) 0‖) → StrictMono (fun k => ‖deriv (φ k) 0‖) →
    γ 0 = 0 → γ (Fin.last (l + 1)) = m → StrictMono γ →
    0 ≤ ξ → ξ ≤ m →
    tauFlat b + tauSharpAt e ξ < Real.log ‖deriv (φ (Fin.last l)) 0‖ →
    (m : ℝ) * (Real.log ‖deriv (φ (Fin.last l)) 0‖ - (tauFlat b + tauSharpAt e ξ)) ≤
      rearrInt (fun k => (γ k.succ - γ k.castSucc) / m) φ +
      (1 / (m : ℝ)) * ∑ k : Fin l, (γ k.succ.castSucc) ^ 2 *
        Real.log (‖deriv (φ k.succ) 0‖ / ‖deriv (φ k.castSucc) 0‖)

/-! ## Area Z — the zero estimate (paper Lemma `lem_Shidlovsky`, `D`-closed case, ε = 0) -/

/-- `f(x_s)` as a power series in `d` variables. -/
noncomputable def embedVar {d : ℕ} (s : Fin d) (f : PowerSeries ℚ) : MvPowerSeries (Fin d) ℚ :=
  fun n => if n = Finsupp.single s (n s) then PowerSeries.coeff (n s) f else 0

/-- The auxiliary series `F(x) = Σ_i Q_i(x) f_{i_1}(x_1)⋯f_{i_d}(x_d)`. -/
noncomputable def auxSeries {m d : ℕ} (f : Fin m → PowerSeries ℚ)
    (Q : (Fin d → Fin m) → MvPolynomial (Fin d) ℚ) : MvPowerSeries (Fin d) ℚ :=
  ∑ i, (Q i : MvPowerSeries (Fin d) ℚ) * ∏ s, embedVar s (f (i s))

/-- Multivariable Shidlovsky lemma for a `D`-closed independent system: if `F ≠ 0`, some
nonzero monomial of minimal total degree has every exponent `≤ m·D + C`. -/
def ZeroEstimate : Prop :=
  ∀ (m : ℕ) (f : Fin m → PowerSeries ℚ), PolyIndependent f → DClosed f →
    ∃ C : ℕ, ∀ (d D : ℕ) (Q : (Fin d → Fin m) → MvPolynomial (Fin d) ℚ),
      (∀ i j, (Q i).degreeOf j < D) → auxSeries f Q ≠ 0 →
      ∃ n : Fin d →₀ ℕ, MvPowerSeries.coeff n (auxSeries f Q) ≠ 0 ∧
        (∀ n' : Fin d →₀ ℕ, n'.degree < n.degree → MvPowerSeries.coeff n' (auxSeries f Q) = 0) ∧
        ∀ j, n j ≤ m * D + C

/-- Strong form (what the paper's Lemma `lem_Shidlovsky` states): EVERY nonzero monomial of
minimal total degree has all exponents `≤ m·D + C`. (The multivariate reduction
`Work.ZeroEst.reduction` works for an arbitrary minimal-degree monomial.) -/
def ZeroEstimateAll : Prop :=
  ∀ (m : ℕ) (f : Fin m → PowerSeries ℚ), PolyIndependent f → DClosed f →
    ∃ C : ℕ, ∀ (d D : ℕ) (Q : (Fin d → Fin m) → MvPolynomial (Fin d) ℚ),
      (∀ i j, (Q i).degreeOf j < D) →
      ∀ n : Fin d →₀ ℕ, MvPowerSeries.coeff n (auxSeries f Q) ≠ 0 →
        (∀ n' : Fin d →₀ ℕ, n'.degree < n.degree → MvPowerSeries.coeff n' (auxSeries f Q) = 0) →
        ∀ j, n j ≤ m * D + C

/-! ## Area M — the `Γ₀(2)` hauptmodul `h` -/

/-- `h(q) = -256 q ∏_{n≥1} (1+qⁿ)^24` (paper eq. `(defofh)`). -/
noncomputable def hauptH (q : ℂ) : ℂ := -256 * q * ∏' n : ℕ, (1 + q ^ (n + 1)) ^ 24

/-- Basic facts on `h` and the square root of `h - 4` (the orbifold point `y = 4`). -/
def HauptFacts : Prop :=
  DifferentiableOn ℂ hauptH (ball 0 1) ∧ deriv hauptH 0 = -256 ∧
    (∀ q ∈ ball (0 : ℂ) 1, hauptH q = 0 → q = 0) ∧
    ∃ k : ℂ → ℂ, DifferentiableOn ℂ k (ball 0 1) ∧ ∀ q ∈ ball (0 : ℂ) 1, hauptH q - 4 = k q ^ 2

/-! ## Area K1 — continuation of solutions of linear ODE systems on the disc -/

/-- A solution of `Y' = A Y + b`, known near `0`, extends holomorphically to the whole unit disc
when `A, b` are holomorphic on the annulus `r₀ < |z| < 1`. -/
def OdeContinuation : Prop :=
  ∀ (k : ℕ) (A : ℂ → Fin k → Fin k → ℂ) (b : ℂ → Fin k → ℂ) (r0 r1 : ℝ) (Y0 : ℂ → Fin k → ℂ),
    0 < r0 → r0 < r1 → r1 ≤ 1 →
    DifferentiableOn ℂ A {z : ℂ | r0 < ‖z‖ ∧ ‖z‖ < 1} →
    DifferentiableOn ℂ b {z : ℂ | r0 < ‖z‖ ∧ ‖z‖ < 1} →
    DifferentiableOn ℂ Y0 (ball 0 r1) →
    (∀ z : ℂ, r0 < ‖z‖ → ‖z‖ < r1 →
      HasDerivAt Y0 (fun i => ∑ j, A z i j * Y0 z j + b z i) z) →
    ∃ Y : ℂ → Fin k → ℂ, DifferentiableOn ℂ Y (ball 0 1) ∧ Set.EqOn Y Y0 (ball 0 r1)

/-! ## Theorem C data -/

/-- The lune map `h(z,c)` of the paper (eq. `(firstgobble)`), principal square root. -/
noncomputable def lune (c : ℝ) (z : ℂ) : ℂ :=
  (z * (1 + (c : ℂ) ^ 2) - 1 - (c : ℂ) ^ 2 +
      ((1 + (c : ℂ) ^ 2) ^ 2 * (1 + z) ^ 2 - 16 * (c : ℂ) ^ 2 * z) ^ (1 / 2 : ℂ)) /
    (2 * ((c : ℂ) ^ 2 - 1))

/-- The paper's Theorem C contour map `ψ(z) = -(3/4) h(z, 23/10)` (§`contour choiceC`). -/
noncomputable def psiC (z : ℂ) : ℂ := -(3 / 4) * lune (23 / 10) z

/-- `φ_C = h ∘ ψ_C`. -/
noncomputable def phiC (z : ℂ) : ℂ := hauptH (psiC z)

/-- The `17 × 2` denominator array of Theorem C (rows: B₁,B₂,B₃,B₄,B₅,G,G',G'',G''',B₆,B₇,
`∫yG`, `∫G`, and the four `∫(G - jet)/y^k`). -/
def bC : Fin 17 → Fin 2 → ℕ := fun i j =>
  if j = 0 then (if (i : ℕ) = 0 then 0 else 2) else (if (i : ℕ) < 3 then 0 else 2)

/-- The added-integrations vector of Theorem C. -/
def eC : Fin 17 → ℕ := ![0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1]

/-- The `14 × 2` array of Theorem A. -/
def bA : Fin 14 → Fin 2 → ℕ := fun i j =>
  if j = 0 then (if (i : ℕ) = 0 then 0 else 2) else (if (i : ℕ) < 3 then 0 else 2)

/-- The added-integrations vector of Theorem A. -/
def eA : Fin 14 → ℕ := ![0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1]

/-- The exact denominator rates used by the paper (`ξ = 7/4` for C, `ξ = 2` for A). -/
def TauValues : Prop :=
  tauFlat bC + tauSharpAt eC (7 / 4) = 1032659 / 242760 ∧
    tauFlat bA + tauSharpAt eA 2 = 16603 / 3920

/-- Analytic facts on `ψ_C, φ_C` (no numerics beyond exact algebra). -/
def PsiCFacts : Prop :=
  ContinuousOn psiC (closedBall 0 1) ∧ DifferentiableOn ℂ psiC (ball 0 1) ∧ psiC 0 = 0 ∧
    deriv psiC 0 = -(1287 / 2516) ∧
    (∀ z ∈ closedBall (0 : ℂ) 1, ‖psiC z‖ ≤ 3 / 4) ∧
    (∀ z ∈ closedBall (0 : ℂ) 1, psiC z = 0 → z = 0)

/-- Certified numerics for Theorem C: the rearrangement integral of `log|φ_C|` on the circle
(true value 9.972…) and the boundary range of `|φ_C|` (true: 3.2e-13 … 6.72e5). -/
def CNumerics : Prop :=
  rearrInt (fun _ : Fin 1 => (1 : ℝ)) (fun _ => phiC) ≤ 102 / 10 ∧
    ∀ z : ℂ, ‖z‖ = 1 → (1 : ℝ) / 10 ^ 13 ≤ ‖phiC z‖ ∧ ‖phiC z‖ ≤ 700000

/-! ## Theorem C: singular points of the Hadamard-product ODE -/

/-- `x_{a^±,b^±} = (a ± √(a²-1))(b ± √(b²-1))` with `a = 2m+1`, `b = 2n+1`. -/
noncomputable def xRoot (m n : ℕ) (sa sb : ℝ) : ℝ :=
  ((2 * m + 1 : ℝ) + sa * Real.sqrt ((2 * m + 1 : ℝ) ^ 2 - 1)) *
    ((2 * n + 1 : ℝ) + sb * Real.sqrt ((2 * n + 1 : ℝ) ^ 2 - 1))

/-- `y = x²/(x-1)`. -/
noncomputable def yOf (x : ℝ) : ℝ := x ^ 2 / (x - 1)

/-- Location of the singularities (paper §`sec:location`), for the NON-strict gap
`10⁶|m-n| ≤ n` (needed after the reduction of negative `m,n`). True margins: `|y_{--}| ≈ 4e-27`,
the three others `≥ 999998`. -/
def CLocation : Prop :=
  ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → m ≠ n → 10 ^ 6 * ((m : ℤ) - n).natAbs ≤ n →
    |yOf (xRoot m n (-1) (-1))| ≤ 1 / 10 ^ 20 ∧ 900000 ≤ |yOf (xRoot m n 1 1)| ∧
      900000 ≤ |yOf (xRoot m n 1 (-1))| ∧ 900000 ≤ |yOf (xRoot m n (-1) 1)|

/-- Theorem C, four-number part, for POSITIVE `m, n` with the non-strict gap. -/
def CPos : Prop :=
  ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → m ≠ n → 10 ^ 6 * ((m : ℤ) - n).natAbs ≤ n →
    LinearIndependent ℚ ![1, Real.log (1 + 1 / (m : ℝ)), Real.log (1 + 1 / (n : ℝ)),
      Real.log (1 + 1 / (m : ℝ)) * Real.log (1 + 1 / (n : ℝ))]

/-! ## Pure functions `B₁,…,B₇` (paper eqs. `(defB)`, `(defB5)`, `(defB67)`) in the variable `y` -/

/-- `B₁ = 1`. -/
noncomputable def B1 : PowerSeries ℚ := 1
/-- `B₂ = Σ_{n≥2} 2 (n-2)! n!/(2n)! yⁿ`. -/
noncomputable def B2 : PowerSeries ℚ := PowerSeries.mk fun n =>
  if n < 2 then 0 else 2 * ((n - 2).factorial * n.factorial : ℚ) / (2 * n).factorial
/-- `B₃ = Σ_{n≥1} (n-1)!²/(2n)! yⁿ`. -/
noncomputable def B3 : PowerSeries ℚ := PowerSeries.mk fun n =>
  if n = 0 then 0 else ((n - 1).factorial : ℚ) ^ 2 / (2 * n).factorial
/-- `B₄ = 4 Σ_{n≥0} y^{n+1}/16ⁿ Σ_k C(2k,k)C(2n-2k,n-k)/((2k-1)(2n-2k+1)²)`. -/
noncomputable def B4 : PowerSeries ℚ := PowerSeries.mk fun n =>
  if n = 0 then 0 else 4 / 16 ^ (n - 1) * ∑ k ∈ Finset.range n,
    ((Nat.centralBinom k * Nat.centralBinom (n - 1 - k) : ℚ) /
      ((2 * (k : ℚ) - 1) * (2 * ((n - 1 - k : ℕ) : ℚ) + 1) ^ 2))
/-- `B₅ = Σ_{n≥1} (n-1)!²/((2n-1)!(2n-1)) yⁿ`. -/
noncomputable def B5 : PowerSeries ℚ := PowerSeries.mk fun n =>
  if n = 0 then 0 else ((n - 1).factorial : ℚ) ^ 2 / ((2 * n - 1).factorial * (2 * (n : ℚ) - 1))
/-- `B₆ = ∫ B₃/y = Σ_{n≥1} (n-1)!²/(n (2n)!) yⁿ`. -/
noncomputable def B6 : PowerSeries ℚ := PowerSeries.mk fun n =>
  if n = 0 then 0 else ((n - 1).factorial : ℚ) ^ 2 / ((n : ℚ) * (2 * n).factorial)
/-- `B₇ = ∫ B₄/y`. -/
noncomputable def B7 : PowerSeries ℚ := PowerSeries.mk fun n =>
  if n = 0 then 0 else PowerSeries.coeff n B4 / n

/-- The seven pure functions in the paper's order. -/
noncomputable def pureB : Fin 7 → PowerSeries ℚ := ![B1, B2, B3, B4, B5, B6, B7]

/-- Denominator types of `B₁,…,B₇` as used in the arrays `bC`/`bA` (paper Lemma
`bdenominators`, crude form), and the `D`-closure of their `ℚ(y)`-span. -/
def PureFacts : Prop :=
  HasDenomType 0 ![0, 0] B1 ∧ HasDenomType 0 ![2, 0] B2 ∧ HasDenomType 1 ![2, 0] B3 ∧
    HasDenomType 0 ![2, 2] B4 ∧ HasDenomType 0 ![2, 2] B5 ∧ HasDenomType 1 ![2, 2] B6 ∧
    HasDenomType 1 ![2, 2] B7 ∧ DClosed pureB

end Submission.CDTPlan
