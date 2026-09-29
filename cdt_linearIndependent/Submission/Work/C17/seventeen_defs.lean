import Mathlib
import Submission.CDTPlan.InterfacesC
import Submission.CDT.LogUnlikelyG
import Submission.CDT.SympDescent
import Submission.CDT.LogHadamard
import Submission.CDT.RatFuncDeriv

/-! Guidance from the project lead (the requester):

# Area C17 — Lemma `17functions` (`Submission.CDTPlan.Seventeen`, InterfacesC), assuming `LemmaSeven`

Do NOT follow the paper's proof (order-4 LL, monodromy, 10×10 determinant). Use the x-side design
worked out by the lead: `REFS/design/ct17/CT17_design.lean.txt` (exact Lean-level statements of every
ingredient, `:= by sorry`) and the scripts next to it (m_local.py, adjoint_solve.py, fastdet.py,
cyclic_fast.py, pure_x.py, psi8.py, numerics2.py). READ IT FIRST. Summary:
Relation Σ p_i f_i = 0 (p_i ∈ ℚ[y]); WLOG a < b by the symmetry (a,r_a) ↔ (b,r_b) of logP/Sym⁺.
1. Formal: apply ∂_y^{D+1} (D ≥ degrees of the coefficients of the integrals, B₆, B₇): kills the six
   integrals and B₆, B₇. Pull back along y = x²/(x−1) (`Submission.CDT.sympSym_subst`: (Sym⁺P)∘y =
   P + P∘φ, φ = x/(x−1)). Reduce all derivatives of P with `logP_ode` (M(P) = cubic) to
   αP + βP' + (same for P∘φ) + Σγ_j B_j(y(x)) + ρ = 0 with polynomial α, β, γ_j, ρ.
2. Analytic core (ACL): α = β = 0. At x_s = (a+√(a²−1))(b−√(b²−1)) (Taylor radius of P): P∘φ, the
   pure part and ρ are holomorphic near x_s, hence so is E := αP + βP'. If β ≠ 0, (I1) the Riccati
   equation of M has no rational solution ⇒ P is meromorphic at x_s; if β = 0, α ≠ 0 same. Local
   exponents of M at x_s are (0,0) and M(P) is a polynomial ⇒ P holomorphic at x_s ⇒ contradicts
   Vivanti–Pringsheim for F = E_a ⋆ A(b) (coefficients ε_n(a)u_n(b) < 0 all n; P = κF + K,
   κ = r_a + r_ab η_b ≠ 0 since η_b is irrational — Lindemann–Weierstrass chapter; K has radius
   > x_s).
3. Algebra: α = β = 0 for all derivative orders forces the G-coefficients to vanish: free
   differential module over ℂ(x) with the adjoint certificate (I2; 13-minors = c(a−b)²(a+b)²Ψ₈(a,b),
   Ψ₈ given in the design, nonzero for admissible a,b by a triangle inequality, I4) and the 4×4
   cyclicity determinant (I3; numerator constant term 4a²b²). Use the prior run's differential-field
   infrastructure (`Submission/CDT/RatFuncDeriv.lean` `dRat`, `OrdAtT.lean`, `Residue.lean`).
4. The remaining relation among B₁..B₇ is killed by `hS : LemmaSeven`.
Parallel pieces already dispatched by the lead (do not duplicate; you may assume them as
hypotheses of your children if they are not proved yet, by stating them identically):
`Work.C17g.pringsheim` (Vivanti–Pringsheim), `Work.C17g.linear_ode_convex` (holomorphic linear
systems on convex open sets have global solutions), `Work.CRad.p_radius` (`PRadius`).
Request everything else (I1–I4, A2 two-sided Legendre/ε bounds, X1 continuation of P∘φ to a convex
neighbourhood of [x_s-ish], X5 pure functions in x, the formal ∂_y^{D+1} bookkeeping) in PARALLEL.

## THE ARCHITECTURE NOW IN FORCE (C17, session 2) — x-side route, no monodromy, no LL

Notation: `x_s = (a+√(a²−1))(b−√(b²−1)) ∈ (0,1)` (`xs a b`), `y = x²/(x−1)`, `φ(x) = x/(x−1)` (the
deck involution of the double cover `y`), `P = logP a b ra rb rab r0` (`Pfun`), `G = Sym⁺P` with
`G∘y = P + P∘φ` (`sympSym_subst`), `M = P₂∂² + P₁∂ + P₀` (my `Mx`), `M(P) = ρ` (`logP_ode`).

**Key analytic fact.** `P` is analytic on `|x| < x_s` and has a *log-type* singularity at `x_s`:
near `x_s`, `P = κ·y₁·log(x_s − ·) + h` with `κ ≠ 0`, `y₁, h` holomorphic with `y₁(x_s) ≠ 0` and
`y₁` solving `M` (child `Work.C17.logP_local_structure`, from Pringsheim +
`Work.C17.logP_not_holomorphic_at_xs`).  Everything else occurring in the relation —
`P∘φ` (continued along a convex stadium, child (X1)), the seven pure series `Bⱼ∘y` (radius ≥ 1,
child `Work.C17.Bsubst_poly_growth`), the rational functions — is *holomorphic* at `x_s`.

**The one analytic input (Λ).** Define the "log-coefficient" functional `Λ` on functions of the form
`A(z)·log(x_s − z) + B(z)` (`A, B` holomorphic at `x_s`) by `Λ = A`.  Then `Λ` is linear and
commutes with differential operators with coefficients holomorphic at `x_s`.  Applying `Λ` to the
pulled-back relation `(R)`: `Λ(LHS) = 0` — since the identity is valid on the lens
`ball(x_s,δ) ∩ ball(0,x_s)`, where the continued functions are analytic — gives, using
`Λ(P) = κy₁`, `Λ(P∘φ) = 0`, `Λ(Bⱼ∘y) = 0`, `Λ(∂_y^k G∘y) = ∂_y^k(Λ(G∘y))` and
`Λ(∫ y^{i−4}G(y)dy ∘ y) = κ·J_i` with `J_i` the antiderivative of `y^{i−4}y'·y₁` vanishing at `x_s`:

  `(LC)`  `Σ_k p_k(y(x))·D_y^k y₁ + Σ_i q_i(y(x))·J_i = 0`   on the lens,

where `p_k, q_i` are the relation's coefficients of `G^{(k)}` (`k ≤ 3`) and of the six integrals,
and `D_y = ρ∂_x = y'^{-1}∂_x`.

**The algebraic input (I3).** In the module `WQ` of §4 below, `Σ_k p_k(y) • cls k = 0` (i.e. the
operator `Σ_{k≤3}p_k(y)∂_y^k` is a left multiple of `M`) forces `p = 0`
(`Work.C17I.order3_class_injective`; proof: apply the deck conjugation `x ↦ x/(x−1)` — which fixes
`y` and hence the `p_k(y)` — to the two class equations, obtaining four equations whose matrix
`[u_k, v_k, u_k∘φ, v_k∘φ]` has non-zero determinant, computed symbolically: its numerator has
`x⁰`-coefficient `4a²b²` and `x²⁶`-coefficient `−32(a−b)⁴`).

**The independence input (IND).** `1, y₁, y₁', J_0, …, J_5` are `ℚ(x)`-linearly independent on
the ball (`Work.C17I.y1_periods_indep`).  Then `(LC)` gives `(the class of Σp_k(y)∂_y^k) = 0` and
`q = 0`; **(I3)** turns the first into `p = 0`.  Hence the relation becomes a relation among the
pure functions only, and `hS : LemmaSeven` gives `γ = 0`.  Done.

### STATUS (end of session 2)

Proved and importable: `Work.C17.local_exp_data`, `Work.C17.beukersEta_irrational`,
`Work.C17.beukersUR_two_sided`, `Work.C17.beukersD_two_sided`,
`Work.C17.logP_not_holomorphic_at_xs`, `Work.C17.Bsubst_poly_growth` (the seven `Bᵢ∘y` have
polynomially bounded coefficients ⟹ radius ≥ 1), `Work.C17.riccati_no_rational` (I1),
`Work.C17.acl_log_compare` (the log/polar-coefficient comparison).

Proved as well, in this file: `seventeen_swap` (the `(m,r_a) ↔ (n,r_b)` symmetry of the seventeen
functions, via `logP_swap`), `seventeen_pure_eq` (entries `0..4,9,10` of `seventeen` are `pureB 0..6`),
`admQ_of_CAdm` (`CAdm m n` with `m < n` gives `AdmQ (2m+1) (2n+1)`).

Also **proved** by children since: `Work.C17.logP_local_structure` (ACL-a: the local structure
`P = κ·y₁·log(x_s − ·) + hh`), `Work.C17.exists_cleared_pAtY`, `Work.C17.Q4x_eval_xs`.

Delegated (running, exact statements as requested): `Work.C17.Pfun_hasSum` (the convergence
`hconv` needed by ACL-a), `Work.C17.adjoint_no_solution` (I2), `Work.C17.order3_class_injective`
(I3), `Work.C17.logPw_continuation` (X1), `Work.C17.y1_periods_indep` (IND),
`Work.C17.relation_to_LC` (Λ and `(LC)`; the crux analytic input, stated with the local structure
as hypothesis and concluding the `(LC)` identity **and** the `J`-package needed by
`y1_periods_indep`), `Work.C17.DyIter_eq_cls` (the reduction `D_y^k y₁ = u_k y₁ + v_k y₁'`
with `(u_k, v_k) = cls k`, in denominator-cleared form).

Note on the index convention (fixed after two reviewers caught a reversal): in `seventeen`, entry
`11+i` is `∫ y^{1−i}G`, so the coefficient `P ⟨11+i⟩` is paired in `(LC)` with `J ⟨5−i⟩` where
`J i' ` has derivative `y^{i'−4}y'y₁` — this is the convention of the delegated
`relation_to_LC` and of `y1_periods_indep`.

Assembly still to be written (in this file), given the six running children:
1. read the relation `Σ_i P_i·f_i = 0` (`f = seventeen m n ra rb rab r0`), WLOG `m < n` using the
   symmetry `logP a b ra rb rab r0 = logP b a rb ra rab r0` of the coefficients;
2. shrink `δ` from ACL-a to satisfy `2δ ≤ x_s`, `2δ ≤ 1−x_s`;
3. `relation_to_LC` ⟹ the `(LC)` identity on the ball + the `J`-package;
4. clear denominators (`(z−1)^M`) and reduce `D_y^k y₁` (`k ≤ 3`) to `y₁, y₁'` modulo `M`
   (the class coordinates `cls` do this automatically, so the reduction is the identity
   `(DyIter k y1) z = u_k(z)·y₁(z) + v_k(z)·y₁'(z)` with `(u_k,v_k) = cls k`);
5. `y1_periods_indep` ⟹ the four `G`-coefficients `P ⟨5+k⟩` and the six integral coefficients
   `P ⟨11+i⟩` all vanish (after extracting `p = 0` from `p(y) = 0`, `y = x²/(x−1)` transcendental);
6. the residue is a relation among `B₁,…,B₇` only: `hS : LemmaSeven` kills it.

So the whole lemma rests on exactly four new inputs:
 * `Work.C17.logP_local_structure` (running, ACL-a) — the local structure of `P` at `x_s`;
 * `Work.C17I.logcoeff_relation` (Λ and `(LC)`) — the analytic continuation to the lens + log-coeff;
 * `Work.C17I.order3_class_injective` (I3) — the symbolic determinant;
 * `Work.C17I.y1_periods_indep` (IND) — `1, y₁, y₁', J_i` independent over `ℚ(x)`.
plus X1 (`Work.C17I.logPw_continuation`) inside `logcoeff_relation`, the pure-part radius
(`Work.C17.Bsubst_poly_growth`, proved) and `Work.C17.Bsubst_poly_growth`'s companions.

**Why this route.** It avoids completely: the paper's monodromy step, the order-4 operator `LL`,
its irreducibility, the `∂_y^{D+1}` bookkeeping, the LCLM, the adjoint certificate (I2) and the
pure-part elimination.  The pure part is invisible to `Λ` and is disposed of at the very end by
`hS : LemmaSeven`.  The price is `(IND)`, a statement about *one* holomorphic solution `y₁` (not
about `G`), which is a "period independence" statement for the integrals `∫ y^{i−4}y'y₁`.
-/

namespace Work.C17

open Polynomial
open scoped BigOperators
open Submission.CDTPlan

noncomputable section

/-! ## 1. The order-2 operator `M` of the paper's eq. (ODE), over `ℚ[x]` -/

/-- The quartic `1 − 4abX + (4a²+4b²−2)X² − 4abX³ + X⁴` whose roots are the four
singularities `(a±√(a²−1))(b±√(b²−1))`. -/
def Q4x (a b : ℚ) : Polynomial ℚ :=
  1 - C (4 * a * b) * X + C (4 * a ^ 2 + 4 * b ^ 2 - 2) * X ^ 2
    - C (4 * a * b) * X ^ 3 + X ^ 4

/-- `P₂ = (X−1)·X·(X+1)·Q₄`, the `y''`-coefficient of `M`. -/
def P2x (a b : ℚ) : Polynomial ℚ := (X - 1) * X * (X + 1) * Q4x a b

/-- `P₁`, the `y'`-coefficient of `M`. -/
def P1x (a b : ℚ) : Polynomial ℚ :=
  - (1 : Polynomial ℚ) + C (8 * a * b) * X + C (5 - 12 * a ^ 2 - 12 * b ^ 2) * X ^ 2
    + C (16 * a * b) * X ^ 3 + C (4 * a ^ 2 + 4 * b ^ 2 - 7) * X ^ 4
    - C (8 * a * b) * X ^ 5 + C 3 * X ^ 6

/-- `P₀`, the `y`-coefficient of `M`. -/
def P0x (a b : ℚ) : Polynomial ℚ :=
  C (a * b) + C (1 - 3 * a ^ 2 - 3 * b ^ 2) * X + C (8 * a * b) * X ^ 2
    - C (a ^ 2 + b ^ 2 + 2) * X ^ 3 - C (a * b) * X ^ 4 + X ^ 5

lemma coe_P2x (a b : ℚ) :
    ((P2x a b : Polynomial ℚ) : PowerSeries ℚ) = Submission.CDT.logPAP2 a b := by
  simp only [P2x, Submission.CDT.logPAP2, Q4x, Submission.CDT.logPAQ4, Polynomial.coe_add,
    Polynomial.coe_sub, Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_one,
    Polynomial.coe_X, Polynomial.coe_C]

lemma coe_P1x (a b : ℚ) :
    ((P1x a b : Polynomial ℚ) : PowerSeries ℚ) = Submission.CDT.logPAP1 a b := by
  simp only [P1x, Submission.CDT.logPAP1, Polynomial.coe_add, Polynomial.coe_sub,
    Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_X, Polynomial.coe_C,
    Polynomial.coe_neg, Polynomial.coe_one]
  have h3 : (PowerSeries.C (3 : ℚ) : PowerSeries ℚ) = (3 : PowerSeries ℚ) :=
    map_natCast PowerSeries.C 3
  rw [h3]

lemma coe_P0x (a b : ℚ) :
    ((P0x a b : Polynomial ℚ) : PowerSeries ℚ) = Submission.CDT.logPAP0 a b := by
  simp only [P0x, Submission.CDT.logPAP0, Polynomial.coe_add, Polynomial.coe_sub,
    Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_X, Polynomial.coe_C]

/-- `logPAODE` is `M` with the explicit polynomial coefficients. -/
lemma logPAODE_eq (a b : ℚ) (f : PowerSeries ℚ) :
    Submission.CDT.logPAODE a b f
      = ((P2x a b : Polynomial ℚ) : PowerSeries ℚ)
          * PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) f)
        + ((P1x a b : Polynomial ℚ) : PowerSeries ℚ) * PowerSeries.derivative (R := ℚ) f
        + ((P0x a b : Polynomial ℚ) : PowerSeries ℚ) * f := by
  rw [Submission.CDT.logPAODE, coe_P2x, coe_P1x, coe_P0x]

/-! ## 2. The analytic objects of the x-side route -/

/-- `x_s = (a+√(a²−1))·(b−√(b²−1))` for `a < b`: the Taylor radius of the unlikely series `P`
(and the point at which `P` is `Pringsheim`-singular). -/
noncomputable def xs (a b : ℝ) : ℝ :=
  (a + Real.sqrt (a ^ 2 - 1)) * (b - Real.sqrt (b ^ 2 - 1))

/-- The power-series function `z ↦ Σ cₙ zⁿ` of `P = logP a b ra rb rab r0`
(paper eq. (defP)); this is `P` as an analytic function wherever the series converges. -/
noncomputable def Pfun (a b : ℚ) (ra rb rab r0 : ℤ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, ((PowerSeries.coeff n (Submission.CDT.logP a b ra rb rab r0) : ℚ) : ℂ) * z ^ n


/-! ## 4. The `ℚ(x)`-module of the `P`-branch (interface for the algebraic endgame)

`WQ` models "the class of a differential operator modulo `M`, together with the six formal
integrals `∫ y^{i-4} G`".  Writing `e₀` for the class of `1` and `e₁` for the class of `∂_x`, the
derivation `∂_y = ρ·∂_x` acts by

* `∂_y e₀ = ρ e₁`,  `∂_y e₁ = -ρ (P₁/P₂) e₁ - ρ (P₀/P₂) e₀`  (the class of `∂_y²` modulo `M`),
* `∂_y φ_i = y^{i-4} e₀`  (the `y`-derivative of `∫ y^{i-4} G`).

The `y`-coefficients of a `ℚ[y]`-combination `Σ_k p_k(y) ∂_y^k` (`k ≤ 3`) are the components of
`Σ_k p_k(y(x)) • cls k`; the `P`-branch part of a relation among the seventeen functions is that
element, which is the interface used by `Work.C17I.order3_class_injective`. -/

/-- `x` as an element of `ℚ(x)`. -/
noncomputable def xQ : RatFunc ℚ := RatFunc.X

/-- `y = x²/(x−1)` as an element of `ℚ(x)`. -/
noncomputable def yQ : RatFunc ℚ := xQ ^ 2 / (xQ - 1)

/-- `dy/dx` as an element of `ℚ(x)`. -/
noncomputable def dyQ : RatFunc ℚ := (xQ ^ 2 - 2 * xQ) / (xQ - 1) ^ 2

/-- `dx/dy = 1/(dy/dx)`, the multiplier turning `∂_x` into `∂_y`. -/
noncomputable def rhoQ : RatFunc ℚ := (xQ - 1) ^ 2 / (xQ ^ 2 - 2 * xQ)

/-- `P₂` of the order-2 operator `M`, as an element of `ℚ(x)`. -/
noncomputable def P2Q (a b : ℚ) : RatFunc ℚ :=
  algebraMap (Polynomial ℚ) (RatFunc ℚ) (P2x a b)

/-- `P₁` of the order-2 operator `M`, as an element of `ℚ(x)`. -/
noncomputable def P1Q (a b : ℚ) : RatFunc ℚ :=
  algebraMap (Polynomial ℚ) (RatFunc ℚ) (P1x a b)

/-- `P₀` of the order-2 operator `M`, as an element of `ℚ(x)`. -/
noncomputable def P0Q (a b : ℚ) : RatFunc ℚ :=
  algebraMap (Polynomial ℚ) (RatFunc ℚ) (P0x a b)

/-- `a = 2m+1` as a rational number. -/
noncomputable def aOf (m : ℕ) : ℚ := 2 * (m : ℚ) + 1

/-- `x_s(2m+1, 2n+1)`. -/
noncomputable def xsOf (m n : ℕ) : ℝ := xs (2 * (m : ℝ) + 1) (2 * (n : ℝ) + 1)

/-- `y(z) = z²/(z−1)`, the symmetrisation variable as a function of `z`. -/
noncomputable def yC (z : ℂ) : ℂ := z ^ 2 / (z - 1)

/-- `D_y = y'⁻¹·d/dz`, the `y`-derivative acting on functions of `z`. -/
noncomputable def Dy (f : ℂ → ℂ) : ℂ → ℂ :=
  fun z => deriv f z * (z - 1) ^ 2 / (z ^ 2 - 2 * z)

/-- The `k`-fold iterate of `D_y`. -/
noncomputable def DyIter (k : ℕ) (f : ℂ → ℂ) : ℂ → ℂ := (Dy^[k]) f

/-- The polynomial `p` evaluated on the `y`-variable: `z ↦ p(y(z))`. -/
noncomputable def pAtY (p : Polynomial ℚ) (z : ℂ) : ℂ := p.eval₂ (algebraMap ℚ ℂ) (yC z)

/-- Admissibility of the pair `(a,b)` (the design's `Adm`): both are odd integers `≥ 3`, `a < b`,
and the gap is small (`10⁶(b−a) ≤ b`).  These are exactly the hypotheses under which the numerical
certificates (`Ψ₈(a,b) ≠ 0`, the local data) are established; the final application only ever uses
`a = 2m+1`, `b = 2n+1` with `10⁶|m−n| ≤ n`. -/
def AdmQ (a b : ℚ) : Prop :=
  3 ≤ a ∧ a < b ∧ 10 ^ 6 * (b - a) ≤ b ∧ ∃ m n : ℤ, a = 2 * m + 1 ∧ b = 2 * n + 1

/-- The `P`-branch module: `(e₀,e₁)`-coordinates of an operator class, and the six integrals. -/
abbrev WQ : Type := (RatFunc ℚ × RatFunc ℚ) × (Fin 6 → RatFunc ℚ)

/-- The derivation `∂_y` on the `P`-branch module. -/
noncomputable def dW (a b : ℚ) (w : WQ) : WQ :=
  ((rhoQ * (Submission.CDT.dRat w.1.1 - w.1.2 * P0Q a b / P2Q a b)
      + ∑ i : Fin 6, w.2 i * yQ ^ ((i : ℤ) - 4),
    rhoQ * (w.1.1 + Submission.CDT.dRat w.1.2 - w.1.2 * P1Q a b / P2Q a b)),
   fun i => rhoQ * Submission.CDT.dRat (w.2 i))

/-- The class of `∂_y^k` (`k ≤ 3`) in the `P`-branch module. -/
noncomputable def cls (a b : ℚ) (k : Fin 4) : RatFunc ℚ × RatFunc ℚ :=
  ((dW a b)^[(k : ℕ)] ((1, 0), 0)).1

/-- The `x ↦ x/(x-1)` (deck transformation) conjugate of a rational function. -/
noncomputable def wQ (f : RatFunc ℚ) : RatFunc ℚ :=
  (f.num.eval₂ (algebraMap ℚ (RatFunc ℚ)) (xQ / (xQ - 1)))
    / (f.denom.eval₂ (algebraMap ℚ (RatFunc ℚ)) (xQ / (xQ - 1)))

/-- The cubic `−b + 3aX − 3bX² + aX³` of the paper's display
`M(H(a)⋆A(b)) = −b+3aX−3bX²+aX³`. -/
def cubicHA (a b : ℚ) : Polynomial ℚ :=
  - C b + 3 * C a * X - 3 * C b * X ^ 2 + C a * X ^ 3

/-- The quartic `−1 + 2X² − X⁴` of the paper's display `M(H(a)⋆H(b)) = −1+2X²−X⁴`. -/
def cubicHH : Polynomial ℚ := -1 + 2 * X ^ 2 - X ^ 4

/-- The order-2 operator `M = P₂·d²/dx² + P₁·d/dx + P₀` of the paper's eq. (ODE), as an
operator on `ℚ⟦x⟧`; definitionally the workspace's `logPAODE`. -/
def Mx (a b : ℚ) (f : PowerSeries ℚ) : PowerSeries ℚ := Submission.CDT.logPAODE a b f

/-- The inhomogeneity of `M` on the unlikely series: under nothing but the paper's
combination, `M(logP) = r_a(−b+3aX−3bX²+aX³) + r_b(−a+3bX−3aX²+bX³) + r_{ab}(−1+2X²−X⁴)`. -/
def rhoMx (a b : ℚ) (ra rb rab : ℤ) : Polynomial ℚ :=
  C (ra : ℚ) * (- C b + 3 * C a * X - 3 * C b * X ^ 2 + C a * X ^ 3)
    + C (rb : ℚ) * (- C a + 3 * C b * X - 3 * C a * X ^ 2 + C b * X ^ 3)
    + C (rab : ℚ) * (-1 + 2 * X ^ 2 - X ^ 4)

/-! ## 5. The symmetry `(a, r_a) ↔ (b, r_b)` (for the WLOG `a < b`) -/

lemma logPCoeffQ_swap (a b : ℚ) (ra rb rab r0 : ℤ) (n : ℕ) :
    Submission.CDT.logPCoeffQ a b ra rb rab r0 n
      = Submission.CDT.logPCoeffQ b a rb ra rab r0 n := by
  unfold Submission.CDT.logPCoeffQ
  ring

/-- `P` is symmetric under the exchange `(a,r_a) ↔ (b,r_b)`. -/
lemma logP_swap (a b : ℚ) (ra rb rab r0 : ℤ) :
    Submission.CDT.logP a b ra rb rab r0 = Submission.CDT.logP b a rb ra rab r0 := by
  ext n
  rw [Submission.CDT.logP, Submission.CDT.logP, PowerSeries.coeff_mk, PowerSeries.coeff_mk,
    logPCoeffQ_swap]

/-- The seventeen functions are symmetric under `(m,r_a) ↔ (n,r_b)`. -/
lemma seventeen_swap (m n : ℕ) (ra rb rab r0 : ℤ) :
    Submission.CDTPlan.seventeen m n ra rb rab r0
      = Submission.CDTPlan.seventeen n m rb ra rab r0 := by
  have hlog : Submission.CDT.logP (2 * (m : ℚ) + 1) (2 * (n : ℚ) + 1) ra rb rab r0
      = Submission.CDT.logP (2 * (n : ℚ) + 1) (2 * (m : ℚ) + 1) rb ra rab r0 :=
    logP_swap _ _ _ _ _ _
  have hG : Submission.CDTPlan.GC m n ra rb rab r0
      = Submission.CDTPlan.GC n m rb ra rab r0 := by
    unfold Submission.CDTPlan.GC Submission.CDTPlan.PC
    rw [hlog]
  simp only [Submission.CDTPlan.seventeen, hG]

/-- The seven pure entries of `seventeen` are `pureB 0, …, pureB 6`. -/
lemma seventeen_pure_eq (m n : ℕ) (ra rb rab r0 : ℤ) :
    Submission.CDTPlan.seventeen m n ra rb rab r0 0 = Submission.CDTPlan.pureB 0 ∧
    Submission.CDTPlan.seventeen m n ra rb rab r0 1 = Submission.CDTPlan.pureB 1 ∧
    Submission.CDTPlan.seventeen m n ra rb rab r0 2 = Submission.CDTPlan.pureB 2 ∧
    Submission.CDTPlan.seventeen m n ra rb rab r0 3 = Submission.CDTPlan.pureB 3 ∧
    Submission.CDTPlan.seventeen m n ra rb rab r0 4 = Submission.CDTPlan.pureB 4 ∧
    Submission.CDTPlan.seventeen m n ra rb rab r0 9 = Submission.CDTPlan.pureB 5 ∧
    Submission.CDTPlan.seventeen m n ra rb rab r0 10 = Submission.CDTPlan.pureB 6 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [Submission.CDTPlan.seventeen, Submission.CDTPlan.pureB, Submission.CDTPlan.dY,
      Submission.CDTPlan.intY, Submission.CDTPlan.tq, Submission.CDTPlan.GC,
      Submission.CDTPlan.PC]

/-- `CAdm m n` with `m < n` implies the admissibility `AdmQ (2m+1) (2n+1)`. -/
lemma admQ_of_CAdm (m n : ℕ) (hm : 1 ≤ m) (h : m < n)
    (hgap : 10 ^ 6 * ((m : ℤ) - n).natAbs ≤ n) : AdmQ (aOf m) (aOf n) := by
  have hmn : (((m : ℤ) - n).natAbs : ℤ) = (n : ℤ) - m := by omega
  refine ⟨?_, ?_, ?_, ⟨(m : ℤ), (n : ℤ), ?_, ?_⟩⟩
  · unfold aOf
    have : (1 : ℚ) ≤ (m : ℚ) := by exact_mod_cast hm
    linarith
  · unfold aOf
    have : (m : ℚ) < (n : ℚ) := by exact_mod_cast h
    linarith
  · unfold aOf
    have hg : (10 : ℚ) ^ 6 * ((n : ℚ) - (m : ℚ)) ≤ (n : ℚ) := by
      have h1 : (10 : ℤ) ^ 6 * ((n : ℤ) - m) ≤ (n : ℤ) := by omega
      have h2 : ((10 : ℤ) ^ 6 * ((n : ℤ) - m) : ℚ) ≤ ((n : ℤ) : ℚ) := by exact_mod_cast h1
      push_cast at h2 ⊢
      linarith
    linarith
  · unfold aOf; norm_num
  · unfold aOf; norm_num

/-! ## 6. Cast bookkeeping for `aOf`, the cusp bounds, and the index involution `jrev`

These are the small interface lemmas shared by the assembly and by the children
`Work.C17.acl_a_local` (the ACL package in the `xsOf`/`aOf` normalisation) and
`Work.C17.clear_denoms_LC` (clearing the denominators of the `(LC)` identity). -/

/-- `aOf` is `2m+1` also after the cast to `ℝ`. -/
lemma aOf_cast (m : ℕ) : ((aOf m : ℚ) : ℝ) = 2 * (m : ℝ) + 1 := by
  unfold aOf; push_cast; ring

/-- The cusp of the pair `(aOf m, aOf n)` is `xsOf m n`. -/
lemma xsOf_eq_xs (m n : ℕ) :
    xs ((aOf m : ℚ) : ℝ) ((aOf n : ℚ) : ℝ) = xsOf m n := by
  rw [aOf_cast, aOf_cast]; rfl

/-- For `3 ≤ a < b` the cusp `x_s = (a+√(a²−1))(b−√(b²−1))` lies in `(0,1)`. -/
lemma xs_pos_and_lt_one_real (a b : ℝ) (ha : 3 ≤ a) (hb : 3 ≤ b) (hab : a < b) :
    0 < xs a b ∧ xs a b < 1 := by
  have ha1 : (0 : ℝ) ≤ a ^ 2 - 1 := by nlinarith
  have hb1 : (0 : ℝ) ≤ b ^ 2 - 1 := by nlinarith
  have hsb : Real.sqrt (b ^ 2 - 1) ^ 2 = b ^ 2 - 1 := Real.sq_sqrt hb1
  set A : ℝ := a + Real.sqrt (a ^ 2 - 1) with hA
  set B : ℝ := b + Real.sqrt (b ^ 2 - 1) with hB
  have hBpos : 0 < B := by
    rw [hB]
    have hs := Real.sqrt_nonneg (b ^ 2 - 1)
    linarith
  have hBβ : B * (b - Real.sqrt (b ^ 2 - 1)) = 1 := by
    rw [hB]; nlinarith
  have hβ : b - Real.sqrt (b ^ 2 - 1) = 1 / B := by
    rw [eq_div_iff (ne_of_gt hBpos), mul_comm]; exact hBβ
  have hxs : xs a b = A / B := by
    rw [xs, ← hA, hβ]; ring
  have hAltB : A < B := by
    rw [hA, hB]
    have hs : Real.sqrt (a ^ 2 - 1) < Real.sqrt (b ^ 2 - 1) :=
      Real.sqrt_lt_sqrt ha1 (by nlinarith)
    linarith
  have h1 : xs a b < 1 := by
    rw [hxs, div_lt_one hBpos]; exact hAltB
  have h2 : 0 < xs a b := by rw [hxs]; positivity
  exact ⟨h2, h1⟩

/-- The cusp of the admissible pair: `0 < xsOf m n`. -/
lemma xsOf_pos (m n : ℕ) (hm : 1 ≤ m) (hlt : m < n) : 0 < xsOf m n := by
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmn : (m : ℝ) < (n : ℝ) := by exact_mod_cast hlt
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by linarith
  exact (xs_pos_and_lt_one_real (2 * (m : ℝ) + 1) (2 * (n : ℝ) + 1)
    (by linarith) (by linarith) (by linarith)).1

/-- The cusp of the admissible pair: `xsOf m n < 1`. -/
lemma xsOf_lt_one (m n : ℕ) (hm : 1 ≤ m) (hlt : m < n) : xsOf m n < 1 := by
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmn : (m : ℝ) < (n : ℝ) := by exact_mod_cast hlt
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by linarith
  exact (xs_pos_and_lt_one_real (2 * (m : ℝ) + 1) (2 * (n : ℝ) + 1)
    (by linarith) (by linarith) (by linarith)).2

/-- The index involution `i ↦ 5 − i` of `Fin 6`: in the seventeen-function relation the integral
`∫ y^{1−i}G` (entry `11+(5−i)` of `seventeen`) is paired with `J ⟨i⟩` where `J i` is the
antiderivative of `y^{i−4}·y'·y₁`. -/
def jrev (i : Fin 6) : Fin 6 := ⟨5 - (i : ℕ), by omega⟩

/-- `jrev` is an involution. -/
lemma jrev_invol (i : Fin 6) : jrev (jrev i) = i := by
  apply Fin.ext
  simp only [jrev]
  omega

/-- `jrev` as a permutation of `Fin 6`. -/
def jrevEquiv : Fin 6 ≃ Fin 6 where
  toFun := jrev
  invFun := jrev
  left_inv := jrev_invol
  right_inv := jrev_invol

/-- A sum over `Fin 6` can be reindexed by `jrev`. -/
lemma sum_jrev {M : Type*} [AddCommMonoid M] (F G : Fin 6 → M)
    (h : ∀ i, F (jrev i) = G i) : (∑ i : Fin 6, F i) = ∑ i : Fin 6, G i := by
  rw [← jrevEquiv.sum_comp F]
  exact Finset.sum_congr rfl fun i _ => h i

/-! ## 7. The `ℂ`-images of the basic data (for the `ℂ(x)` inputs of `Work.GenShared`)

`Work.GenShared.periods_indep_gen` works over `ℂ(x)`; the coefficient polynomials of `M` and the
six ratios `y^{i−4}·y'` are therefore needed as polynomials over `ℂ`. -/

/-- The `ℂ`-image of the `y''`-coefficient `P₂` of `M`. -/
noncomputable def P2C (a b : ℚ) : Polynomial ℂ := (P2x a b).map (algebraMap ℚ ℂ)

/-- The `ℂ`-image of the `y'`-coefficient `P₁` of `M`. -/
noncomputable def P1C (a b : ℚ) : Polynomial ℂ := (P1x a b).map (algebraMap ℚ ℂ)

/-- The `ℂ`-image of the `y`-coefficient `P₀` of `M`. -/
noncomputable def P0C (a b : ℚ) : Polynomial ℂ := (P0x a b).map (algebraMap ℚ ℂ)

/-- Numerator of the ratio `y^{i−4}·y'` over `ℂ`. -/
noncomputable def rnC (i : Fin 6) : Polynomial ℂ :=
  (((yQ ^ ((i : ℤ) - 4)) * dyQ).num).map (algebraMap ℚ ℂ)

/-- Denominator of the ratio `y^{i−4}·y'` over `ℂ`. -/
noncomputable def rdC (i : Fin 6) : Polynomial ℂ :=
  (((yQ ^ ((i : ℤ) - 4)) * dyQ).denom).map (algebraMap ℚ ℂ)

end

end Work.C17
