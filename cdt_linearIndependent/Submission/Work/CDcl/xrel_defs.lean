import Mathlib
import Submission.Work.CDcl.setup
import Submission.CDT.LogMIdentities
import Submission.CDT.SympDescent
import Submission.CDT.RatFuncDeriv
import Submission.Commons.RingTheory.Derivation.exists_derivation_fractionRing

/-!
# The field `ℚ((x)) = Frac ℚ⟦x⟧` and its derivation, for `Work.CDcl.x_relation`

The reduction of the pullbacks `T k = (G^{(k)})∘y` to a finite-dimensional `ℚ(x)`-vector space
has to be carried out in a single-variable field containing both `ℚ⟦x⟧` and `ℚ(x)`: the multiplier
`ρ = (x-1)²/(x(x-2)) = dx/dy` and the coefficients `α = -P₁/P₂` of the paper's operator have poles
at `x = 0`, so `A f = ρ·f'` is *not* an operator on `ℚ⟦x⟧`, while it is an operator on

`LF := FractionRing ℚ⟦x⟧ = ℚ((x))`.

In this field the polynomial `P₂` is invertible, so the ODE `P₂P'' + P₁P' + P₀P = p` can be solved
for `P''`, and `ρ = 1/y'` is a legitimate scalar.  This file collects the definitions and the
structural lemmas that the substantive modules (`ode_P`, `ode_Pw`, `iterate_T`, `shift`,
`norm_form`) build on.
-/

noncomputable section

open Polynomial PowerSeries

namespace Work.CDcl

/-- `ℚ((x))`, the fraction field of the power series ring `ℚ⟦x⟧`. -/
abbrev LF : Type := FractionRing (PowerSeries ℚ)

/-- The canonical `ℤ`-algebra structure on `ℚ((x))` (the one carried by the derivation below). -/
local instance instAlgZL : Algebra ℤ LF := Ring.toIntAlgebra LF

/-- The chosen derivation of `ℚ((x))` (its instance arguments are those of the construction;
we only ever use its underlying function `dL`). -/
noncomputable def dL0 := by
  letI : CommSemiring (PowerSeries ℚ) := (inferInstance : CommRing (PowerSeries ℚ)).toCommSemiring
  letI : Algebra ℤ (PowerSeries ℚ) := Ring.toIntAlgebra (PowerSeries ℚ)
  exact Classical.choose (Commons.RingTheory.Derivation.exists_derivation_fractionRing
    (R := PowerSeries ℚ) (K := LF) (Derivation.restrictScalars ℤ (PowerSeries.derivative (R := ℚ))))

/-- The characteristic property of the chosen derivation. -/
theorem dL0_algebraMap (f : PowerSeries ℚ) :
    dL0 (algebraMap (PowerSeries ℚ) LF f)
      = algebraMap (PowerSeries ℚ) LF (PowerSeries.derivative (R := ℚ) f) := by
  letI : CommSemiring (PowerSeries ℚ) := (inferInstance : CommRing (PowerSeries ℚ)).toCommSemiring
  letI : Algebra ℤ (PowerSeries ℚ) := Ring.toIntAlgebra (PowerSeries ℚ)
  exact Classical.choose_spec
    (Commons.RingTheory.Derivation.exists_derivation_fractionRing
      (R := PowerSeries ℚ) (K := LF) (Derivation.restrictScalars ℤ (PowerSeries.derivative (R := ℚ)))) f

/-- The derivation `d/dx` of `ℚ((x))`, extending the formal derivative of `ℚ⟦x⟧`.
This is the underlying function of a choice witness; use `dL_algebraMap` and the lemmas below. -/
noncomputable abbrev dL : LF → LF := dL0

/-- **Characteristic property of `dL`**: on the image of `ℚ⟦x⟧` it is the formal derivative. -/
theorem dL_algebraMap (f : PowerSeries ℚ) :
    dL (algebraMap (PowerSeries ℚ) LF f)
      = algebraMap (PowerSeries ℚ) LF (PowerSeries.derivative (R := ℚ) f) :=
  dL0_algebraMap f

theorem dL_add (x y : LF) : dL (x + y) = dL x + dL y := map_add dL0 x y

theorem dL_zero : dL (0 : LF) = 0 := map_zero dL0

theorem dL_mul (x y : LF) : dL (x * y) = x * dL y + y * dL x := by
  have h := Derivation.leibniz dL0 x y
  simpa only [dL, smul_eq_mul] using h

theorem dL_one : dL (1 : LF) = 0 := by
  have h := Derivation.map_one_eq_zero dL0
  simpa [dL] using h

theorem dL_neg (x : LF) : dL (-x) = -dL x := map_neg dL0 x

theorem dL_sub (x y : LF) : dL (x - y) = dL x - dL y := map_sub dL0 x y

theorem dL_inv (x : LF) : dL x⁻¹ = -(x⁻¹) ^ 2 * dL x := by
  have h := Derivation.leibniz_inv dL0 x
  simpa only [dL, smul_eq_mul] using h

theorem dL_div (x y : LF) (hy : y ≠ 0) : dL (x / y) = (dL x * y - x * dL y) / y ^ 2 := by
  rw [div_eq_mul_inv, dL_mul, dL_inv]
  field_simp
  ring

/-- Leibniz for an image of a power series times an arbitrary element. -/
theorem dL_algebraMap_mul (f : PowerSeries ℚ) (x : LF) :
    dL (algebraMap (PowerSeries ℚ) LF f * x)
      = algebraMap (PowerSeries ℚ) LF (PowerSeries.derivative (R := ℚ) f) * x
        + algebraMap (PowerSeries ℚ) LF f * dL x := by
  rw [dL_mul, dL_algebraMap]
  ring

/-! ## The embedding `ℚ(x) ↪ ℚ((x))` -/

/-- The canonical embedding `ℚ(x) ↪ ℚ((x))`. -/
noncomputable def toL : RatFunc ℚ →+* LF :=
  IsFractionRing.lift (g := (algebraMap (PowerSeries ℚ) LF).comp
      Polynomial.coeToPowerSeries.ringHom)
    ((IsFractionRing.injective (PowerSeries ℚ) LF).comp (Polynomial.coe_injective ℚ))

/-- On polynomials, `toL` is the inclusion `ℚ[x] → ℚ⟦x⟧ → ℚ((x))`. -/
theorem toL_algebraMap (p : Polynomial ℚ) :
    toL (algebraMap (Polynomial ℚ) (RatFunc ℚ) p)
      = algebraMap (PowerSeries ℚ) LF p := by
  rw [toL, IsFractionRing.lift_algebraMap]
  rfl

/-- `toL` sends the rational function `x` to the image of the power series `X`. -/
theorem toL_X :
    toL (RatFunc.X : RatFunc ℚ) = algebraMap (PowerSeries ℚ) LF (PowerSeries.X : PowerSeries ℚ) := by
  have h : (RatFunc.X : RatFunc ℚ) = algebraMap (Polynomial ℚ) (RatFunc ℚ) Polynomial.X :=
    RatFunc.algebraMap_X.symm
  rw [h, toL_algebraMap, Polynomial.coe_X]

theorem toL_one : toL (1 : RatFunc ℚ) = 1 := map_one toL
theorem toL_add (x y : RatFunc ℚ) : toL (x + y) = toL x + toL y := map_add toL x y
theorem toL_mul (x y : RatFunc ℚ) : toL (x * y) = toL x * toL y := map_mul toL x y
theorem toL_neg (x : RatFunc ℚ) : toL (-x) = -toL x := map_neg toL x
theorem toL_sub (x y : RatFunc ℚ) : toL (x - y) = toL x - toL y := map_sub toL x y
theorem toL_inv (x : RatFunc ℚ) : toL x⁻¹ = (toL x)⁻¹ := map_inv₀ toL x
theorem toL_div (x y : RatFunc ℚ) : toL (x / y) = toL x / toL y := map_div₀ toL x y
theorem toL_zero : toL (0 : RatFunc ℚ) = 0 := map_zero toL
theorem toL_pow (x : RatFunc ℚ) (n : ℕ) : toL (x ^ n) = toL x ^ n := map_pow toL x n
theorem toL_natCast (n : ℕ) : toL (n : RatFunc ℚ) = (n : LF) := map_natCast toL n
theorem toL_intCast (n : ℤ) : toL (n : RatFunc ℚ) = (n : LF) := map_intCast toL n
theorem toL_sub_one (c : RatFunc ℚ) : toL (c - 1) = toL c - 1 := by
  rw [toL_sub, toL_one]
theorem toL_add_one (c : RatFunc ℚ) : toL (c + 1) = toL c + 1 := by
  rw [toL_add, toL_one]

/-- **`dL` on rational functions is `dRat`**. -/
theorem dL_toL (c : RatFunc ℚ) : dL (toL c) = toL (Submission.CDT.dRat c) := by
  obtain ⟨p, q, hq, hpq⟩ := IsFractionRing.div_surjective (Polynomial ℚ) c
  have hq0 : q ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hq
  have hmap : Function.Injective (algebraMap (PowerSeries ℚ) LF) :=
    IsFractionRing.injective (PowerSeries ℚ) LF
  have hqL : toL (algebraMap (Polynomial ℚ) (RatFunc ℚ) q) ≠ 0 := by
    rw [toL_algebraMap]
    intro h
    have h2 : (q : PowerSeries ℚ) = 0 := hmap (by rw [h, map_zero])
    exact hq0 (Polynomial.coe_injective ℚ h2)
  have hpoly : ∀ r : Polynomial ℚ,
      dL (toL (algebraMap (Polynomial ℚ) (RatFunc ℚ) r))
        = toL (algebraMap (Polynomial ℚ) (RatFunc ℚ) r.derivative) := by
    intro r
    rw [toL_algebraMap, dL_algebraMap, PowerSeries.derivative_coe, ← toL_algebraMap]
  rw [← hpq, map_div₀, dL_div _ _ hqL, hpoly p, hpoly q, Submission.CDT.dRat_div p q]
  simp only [map_div₀, map_sub, map_mul, map_pow]
  try field_simp
  try ring

/-- Leibniz for a rational-function coefficient times an arbitrary element. -/
theorem dL_toL_mul (c : RatFunc ℚ) (x : LF) :
    dL (toL c * x) = toL (Submission.CDT.dRat c) * x + toL c * dL x := by
  rw [dL_mul, dL_toL]
  ring

/-- The image of a polynomial in `ℚ(x)` is the image of the corresponding power series. -/
theorem toL_eq_algebraMap_of_polynomial (p : Polynomial ℚ) :
    toL (algebraMap (Polynomial ℚ) (RatFunc ℚ) p) = algebraMap (PowerSeries ℚ) LF p :=
  toL_algebraMap p

/-! ## The concrete elements -/

/-- `ρ = (x-1)²/(x(x-2))` as an element of `ℚ((x))`. -/
noncomputable def rhoL : LF := toL rhoK

/-- `α = -P₁/P₂` as an element of `ℚ((x))`. -/
noncomputable def alphaL (a b : ℚ) : LF := toL (alphaK a b)
/-- `β = -P₀/P₂` as an element of `ℚ((x))`. -/
noncomputable def betaL (a b : ℚ) : LF := toL (betaK a b)
/-- `γ = p/P₂` as an element of `ℚ((x))`. -/
noncomputable def gammaL (a b : ℚ) (ra rb rab r0 : ℤ) : LF := toL (gammaK a b ra rb rab r0)
/-- `α̃ = -Q₁/Q₂` as an element of `ℚ((x))`. -/
noncomputable def alphaLt (a b : ℚ) : LF := toL (alphaKt a b)
/-- `β̃ = -Q₀/Q₂` as an element of `ℚ((x))`. -/
noncomputable def betaLt (a b : ℚ) : LF := toL (betaKt a b)
/-- `γ̃ = (p∘φ)/Q₂` as an element of `ℚ((x))`. -/
noncomputable def gammaLt (a b : ℚ) (ra rb rab r0 : ℤ) : LF := toL (gammaKt a b ra rb rab r0)

/-- `P = logP a b ra rb rab r0`, viewed in `ℚ((x))`. -/
noncomputable def Pfun (a b : ℚ) (ra rb rab r0 : ℤ) : LF :=
  algebraMap (PowerSeries ℚ) LF (Submission.CDT.logP a b ra rb rab r0)

/-- `Pw = P∘φ`, viewed in `ℚ((x))`. -/
noncomputable def Pwfun (a b : ℚ) (ra rb rab r0 : ℤ) : LF :=
  algebraMap (PowerSeries ℚ) LF
    ((Submission.CDT.logP a b ra rb rab r0).subst Submission.CDT.sympPhi)

/-- `S = P + Pw = (Sym⁺P)∘y = T 0`. -/
noncomputable def Sfun (a b : ℚ) (ra rb rab r0 : ℤ) : LF :=
  Pfun a b ra rb rab r0 + Pwfun a b ra rb rab r0

/-- The pullback `T k = (G^{(k)})∘y`, viewed in `ℚ((x))`. -/
noncomputable def Tfun (a b : ℚ) (ra rb rab r0 : ℤ) (k : ℕ) : LF :=
  algebraMap (PowerSeries ℚ) LF (Work.CDcl.T a b ra rb rab r0 k)

/-- `A f = ρ·f'`, the `y`-derivative acting on the `x`-side. -/
noncomputable def Aop : LF → LF := fun f => rhoL * dL f

/-- `T 0 = S`. -/
theorem Tfun_zero (a b : ℚ) (ra rb rab r0 : ℤ) :
    Tfun a b ra rb rab r0 0 = Sfun a b ra rb rab r0 := by
  unfold Tfun Sfun Pfun Pwfun Work.CDcl.T G0
  rw [Function.iterate_zero_apply, Submission.CDT.sympSym_subst, map_add]

/-! ## The recurrences computing `A^k` on `P` and on `Pw` -/

/-- The coefficient triple `(a_k, b_k, d_k)` of the normal form `A^k P = a_k P + b_k P' + d_k`. -/
def Pseq (a b : ℚ) (ra rb rab r0 : ℤ) : ℕ → RatFunc ℚ × RatFunc ℚ × RatFunc ℚ
  | 0 => (1, 0, 0)
  | (k + 1) =>
      let t := Pseq a b ra rb rab r0 k
      (rhoK * (Submission.CDT.dRat t.1 + t.2.1 * betaK a b),
       rhoK * (t.1 + Submission.CDT.dRat t.2.1 + t.2.1 * alphaK a b),
       rhoK * (Submission.CDT.dRat t.2.2 + t.2.1 * gammaK a b ra rb rab r0))

/-- The coefficient triple `(ã_k, b̃_k, d̃_k)` of the normal form `A^k Pw = ã_k Pw + b̃_k Pw' + d̃_k`. -/
def Pwseq (a b : ℚ) (ra rb rab r0 : ℤ) : ℕ → RatFunc ℚ × RatFunc ℚ × RatFunc ℚ
  | 0 => (1, 0, 0)
  | (k + 1) =>
      let t := Pwseq a b ra rb rab r0 k
      (rhoK * (Submission.CDT.dRat t.1 + t.2.1 * betaKt a b),
       rhoK * (t.1 + Submission.CDT.dRat t.2.1 + t.2.1 * alphaKt a b),
       rhoK * (Submission.CDT.dRat t.2.2 + t.2.1 * gammaKt a b ra rb rab r0))

/-!
## Proof plans for the sibling modules (guidance for the colleagues proving them)

All the facts below live in `LF = ℚ((x))`, with `dL` the derivation (a function, see
`dL_algebraMap`, `dL_toL`, `dL_mul`), `toL : ℚ(x) →+* LF` the embedding, and
`Φ := algebraMap (PowerSeries ℚ) LF` the inclusion of `ℚ⟦x⟧`.

### `xco_ode_P` (the order-two ODE for `P`)

From `Submission.CDT.logP_ode`:
`logPAODE a b (logP a b ra rb rab r0) = C ra * RaFam a b + C rb * RbFam a b + C rab * RabFam a b`.
Useful auxiliary facts (all provable by `simp [defs]; ring`, in the spirit of
`Work.C17.seventeen_indep.coe_P2x`):
`((p2poly a b : ℚ[x]) : ℚ⟦x⟧) = Submission.CDT.logPAP2 a b`, the same for `p1poly`/`p0poly`,
and `((ppoly a b ra rb rab r0 : ℚ[x]) : ℚ⟦x⟧) = C ra * RaFam a b + C rb * RbFam a b + C rab * RabFam a b`,
and `p2poly a b ≠ 0` (all its factors are nonzero and `ℚ[x]` is a domain; `q4poly` has constant
term `1`).  Also `p2K a b = algebraMap ℚ[x] ℚ(x) (p2poly a b)`, and similarly for `p1K`, `p0K`,
`pK` (the map `p ↦ p.eval₂ (algebraMap ℚ K) xK` is `algebraMap ℚ[x] ℚ(x)` — both are `ℚ`-algebra
maps `ℚ[x] → ℚ(x)` sending `X` to `RatFunc.X`; use `RatFunc.algebraMap_X` and `Polynomial.algHom_ext`).
Then `toL (p2K a b) = Φ ((p2poly a b : ℚ[x]) : ℚ⟦x⟧)` by `toL_algebraMap`, and `dL∘Φ = Φ∘d/dx`
(`dL_algebraMap`).  Lifting `logP_ode` to `LF` and dividing by `toL (p2K a b) ≠ 0` gives the ODE
with `alphaL = toL (-p1K/p2K)`, `betaL = toL (-p0K/p2K)`, `gammaL = toL (pK/p2K)` (these are
definitionally the setup's `alphaK`, `betaK`, `gammaK`).

### `xco_ode_Pw` (the pulled-back ODE for `Pw = P∘φ`)

Let `σ : ℚ⟦x⟧ → LF`, `f ↦ Φ (f.subst sympPhi)` (a ring hom, using
`PowerSeries.subst_mul/add/pow` and `sympPhi_hasSubst`).  Then `Pwfun = σ (logP …)`.

Ingredients (each a short computation):
* `toL phiK = Φ sympPhi` (from `toL_div`, `toL_X`, `toL_algebraMap`, `sympPhi = X * (X-1)⁻¹`);
* `toL yK = Φ sympY`;
* for every `q : ℚ[x]`: `Φ (q.subst sympPhi) = toL (q.eval₂ (algebraMap ℚ ℚ(x)) phiK)`
  (both sides are ring homs in `q` agreeing on `X`, using the first item and
  `PowerSeries.subst_X`; e.g. `Polynomial.induction_on` + `map_add/mul/pow`);
* `Φ (d/dx sympPhi) = toL (dRat phiK)`, and `Φ (d²/dx² sympPhi) = toL (dRat (dRat phiK))`
  (compute `d/dx sympPhi = -(Φ ((x-1)⁻²))` using `PowerSeries.derivative_inv'` /
  `derivative_subst`, then `toL ((x-1)⁻²)` by `toL_algebraMap`/`toL_X`/`toL_sub`/`toL_inv`).

Then the chain rule `dL (σ f) = σ (d/dx f) * Ψ` with `Ψ := Φ (d/dx sympPhi)` (from `dL_algebraMap`
and `PowerSeries.derivative_subst`), hence `dL (dL (σ f)) = σ (d²/dx² f) * Ψ² + σ (d/dx f) * dL Ψ`.
Substituting `f = logP …` and applying `σ` to the `x`-side ODE gives
`toL (p2phiK) * σ (P'') + toL (p1phiK) * σ (P') + toL (p0phiK) * σ (P) = toL (pphiK)`,
i.e. with `σ (P) = Pw`, `σ (P') = dL Pw / Ψ`, `σ (P'') = (dL²Pw - (dL Pw / Ψ) * dL Ψ) / Ψ²`:
`dL²Pw = (dL Ψ / Ψ - Ψ * toL (p1phiK) / toL (p2phiK)) * dL Pw
        - (Ψ² * toL (p0phiK) / toL (p2phiK)) * Pw + Ψ² * toL (pphiK) / toL (p2phiK)`.
The coefficients are `toL (alphaKt a b)`, `toL (betaKt a b)`, `toL (gammaKt a b ra rb rab r0)`:
using `Ψ = toL (dRat phiK)`, `dRat phiK = -1/(xK-1)^2`, `dRat (dRat phiK) = 2/(xK-1)^3`,
`p2phiK = eval₂ phiK p2poly` etc., `Q2K = p2phiK * (xK-1)^4`, this is `field_simp; ring` in `ℚ(x)`.

### `xco_iter` (`T k = A^k (T 0)`)

`Tfun 0 = Sfun = Pfun + Pwfun` is `Tfun_zero`.  For `f : ℚ⟦x⟧`,
`Aop (Φ (f.subst sympY)) = ρ * dL (Φ (f.subst sympY)) = ρ * Φ ((d/dx f).subst sympY) * Φ (d/dx sympY)`
by `PowerSeries.derivative_subst`.  So it suffices that
`rhoL * Φ (d/dx sympY) = 1`: this follows from `toL yK = Φ sympY` plus `dL_toL`
(`dL (toL yK) = toL (dRat yK)`), `dL (Φ sympY) = Φ (d/dx sympY)`, and `rhoK * dRat yK = 1`
(a `field_simp; ring` computation with `rhoK = (xK-1)^2/(xK*(xK-2))`, `yK = xK^2/(xK-1)`).
Then `Tfun k = Aop^[k] (Tfun 0)` is an induction using `T a b … (k+1) = (d/dx (G^{(k)})) ∘ y`
and the definition of `T`.

### `xco_norm` (the normal form of `A^k`)

`Aop` is additive, `Aop (toL c * x) = toL (rhoK * dRat c) * x + toL (rhoK * c) * Aop x`
(from `dL_toL_mul`, `rhoL = toL rhoK`, `toL_mul`), and `Aop` of `Pfun`, `Pwfun` is known:
`Aop Pfun = rhoL * dL Pfun` (which is `toL rhoK * dL Pfun`, the `(a_1,b_1,d_1)` shape),
while `Aop (dL Pfun) = rhoL * dL²Pfun` must be rewritten with `xco_ode_P`, and likewise for `Pw`.
Induction on `k` with the recurrences defining `Pseq`/`Pwseq` gives the stated normal form.

### Assembling `x_relation`

`xrel_linalg` applied to `F k := Tfun a b ra rb rab r0 k` with
`u k = ![ (Pseq … k).1, (Pseq … k).2.1, (Pwseq … k).1, (Pwseq … k).2.1 ]`,
`d k = (Pseq … k).2.2 + (Pwseq … k).2.2` (using `xco_norm`) and the identification
`toL (Q k) = Φ (Q k)`, `toL r = Φ r` then gives the relation in `ℚ⟦x⟧` by injectivity of `Φ`
(`IsFractionRing.injective`).
-/



/-! ## Identification lemmas for the pullback by `φ = x/(x-1)` -/

/-- `x - 1 ≠ 0` in `ℚ(x)`. -/
theorem xK_sub_one_ne_zero : (xK - 1 : RatFunc ℚ) ≠ 0 := by
  have h : (xK - 1 : RatFunc ℚ)
      = algebraMap (Polynomial ℚ) (RatFunc ℚ) (Polynomial.X - 1) := by
    rw [map_sub, RatFunc.algebraMap_X, map_one]
    rfl
  rw [h]
  exact RatFunc.algebraMap_ne_zero (Polynomial.X_sub_C_ne_zero 1)

/-- `algebraMap` of a power series vanishes only for the zero series. -/
theorem algebraMap_eq_zero {f : PowerSeries ℚ} (h : algebraMap (PowerSeries ℚ) LF f = 0) :
    f = 0 :=
  IsFractionRing.injective (PowerSeries ℚ) LF
    (show algebraMap (PowerSeries ℚ) LF f = algebraMap (PowerSeries ℚ) LF 0 from by
      rw [h, map_zero])

/-- Casting a rational to `ℚ((x))`. -/
theorem toL_ratCast (c : ℚ) : toL (c : RatFunc ℚ) = (c : LF) := map_ratCast toL c

/-- `t ↦ (t : ℚ((x)))` on rational numbers is `algebraMap ℚ LF`. -/
theorem toL_algebraMap_rat (c : ℚ) : toL (algebraMap ℚ (RatFunc ℚ) c) = algebraMap ℚ LF c := by
  have h : ((c : RatFunc ℚ)) = algebraMap ℚ (RatFunc ℚ) c := rfl
  rw [← h, toL_ratCast]
  exact (map_ratCast (algebraMap ℚ LF) c).symm

/-- `Φ (X - 1) = x - 1`. -/
theorem algebraMap_X_sub_one :
    algebraMap (PowerSeries ℚ) LF ((PowerSeries.X : PowerSeries ℚ) - 1) = toL (xK - 1) := by
  rw [show ((PowerSeries.X : PowerSeries ℚ) - 1 : PowerSeries ℚ)
      = (((Polynomial.X - 1 : Polynomial ℚ)) : PowerSeries ℚ) from by
        rw [Polynomial.coe_sub, Polynomial.coe_X, Polynomial.coe_one],
    ← toL_algebraMap]
  congr 1
  rw [map_sub, RatFunc.algebraMap_X, map_one]
  rfl

theorem algebraMap_X_sub_one_ne_zero :
    algebraMap (PowerSeries ℚ) LF ((PowerSeries.X : PowerSeries ℚ) - 1) ≠ 0 := by
  intro h
  have h1 : PowerSeries.constantCoeff ((PowerSeries.X : PowerSeries ℚ) - 1) = 0 :=
    congrArg PowerSeries.constantCoeff (algebraMap_eq_zero h)
  have h2 : PowerSeries.constantCoeff ((PowerSeries.X : PowerSeries ℚ) - 1) = -1 := by simp
  rw [h2] at h1
  norm_num at h1

/-- The rational function `φ = x/(x-1)` is the image of the power series `sympPhi`. -/
theorem toL_phiK : toL phiK = algebraMap (PowerSeries ℚ) LF Submission.CDT.sympPhi := by
  have hU0 : toL (xK - 1) ≠ 0 := by
    rw [← algebraMap_X_sub_one]
    exact algebraMap_X_sub_one_ne_zero
  have h1 : toL phiK * toL (xK - 1) = toL xK := by
    rw [← map_mul, show phiK * (xK - 1) = xK from by
      rw [show phiK = xK / (xK - 1) from rfl, div_mul_cancel₀]
      exact xK_sub_one_ne_zero]
  have h2 : algebraMap (PowerSeries ℚ) LF Submission.CDT.sympPhi * toL (xK - 1) = toL xK := by
    rw [← algebraMap_X_sub_one, ← map_mul, Submission.CDT.sympPhi_mul_sub_one]
    exact toL_X.symm
  exact mul_right_cancel₀ hU0 (h1.trans h2.symm)

/-- `Φ (C c) = c`. -/
theorem algebraMap_PS_C (c : ℚ) :
    algebraMap (PowerSeries ℚ) LF (MvPowerSeries.C c) = algebraMap ℚ LF c := by
  rw [show (MvPowerSeries.C c : PowerSeries ℚ) = PowerSeries.C c from rfl,
    PowerSeries.C_eq_algebraMap]
  exact (IsScalarTower.algebraMap_apply ℚ (PowerSeries ℚ) LF c).symm

/-- **The substitution of a polynomial by `sympPhi`.** -/
theorem substPhi_poly (q : Polynomial ℚ) :
    algebraMap (PowerSeries ℚ) LF ((q : PowerSeries ℚ).subst Submission.CDT.sympPhi)
      = toL (q.eval₂ (algebraMap ℚ (RatFunc ℚ)) phiK) := by
  rw [PowerSeries.subst_coe Submission.CDT.sympPhi_hasSubst, Polynomial.aeval_def]
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [Polynomial.eval₂_add, Polynomial.eval₂_add, map_add, hp, hq, map_add]
  | monomial n a =>
      rw [Polynomial.eval₂_monomial, Polynomial.eval₂_monomial, map_mul, map_pow, toL_mul,
        toL_pow, ← toL_phiK, ← IsScalarTower.algebraMap_apply ℚ (PowerSeries ℚ) LF a,
        ← toL_algebraMap_rat a]

/-- **The derivative of `sympPhi`.** -/
theorem substPhi_deriv :
    algebraMap (PowerSeries ℚ) LF (PowerSeries.derivative (R := ℚ) Submission.CDT.sympPhi)
      = toL (Submission.CDT.dRat phiK) := by
  have hU0 : toL (xK - 1) ≠ 0 := by
    rw [← algebraMap_X_sub_one]
    exact algebraMap_X_sub_one_ne_zero
  have hd : (PowerSeries.derivative (R := ℚ) Submission.CDT.sympPhi)
        * ((PowerSeries.X : PowerSeries ℚ) - 1) + Submission.CDT.sympPhi = 1 := by
    have h := congrArg (PowerSeries.derivative (R := ℚ)) Submission.CDT.sympPhi_mul_sub_one
    rw [Derivation.leibniz, map_sub, Derivation.map_one_eq_zero, sub_zero] at h
    simp only [smul_eq_mul, PowerSeries.derivative_X, mul_one] at h
    linear_combination h
  have hd' : algebraMap (PowerSeries ℚ) LF (PowerSeries.derivative (R := ℚ) Submission.CDT.sympPhi)
        * toL (xK - 1) = 1 - toL phiK := by
    have h := congrArg (algebraMap (PowerSeries ℚ) LF) hd
    rw [map_add, map_mul, map_one, algebraMap_X_sub_one, ← toL_phiK] at h
    exact (eq_sub_iff_add_eq).mpr h
  have hdphiK : Submission.CDT.dRat phiK * (xK - 1) = 1 - phiK := by
    have h := congrArg Submission.CDT.dRat (show phiK * (xK - 1) = xK from by
      rw [show phiK = xK / (xK - 1) from rfl, div_mul_cancel₀]
      exact xK_sub_one_ne_zero)
    rw [Submission.CDT.dRat_mul] at h
    have h2 : Submission.CDT.dRat (xK : RatFunc ℚ) = 1 := by
      have hx : (xK : RatFunc ℚ) = algebraMap (Polynomial ℚ) (RatFunc ℚ) Polynomial.X :=
        RatFunc.algebraMap_X.symm
      rw [hx, Submission.CDT.dRat_algebraMap]
      have hX : Polynomial.derivative (Polynomial.X : Polynomial ℚ) = 1 :=
        Polynomial.derivative_X
      rw [hX, map_one]
    have h1 : Submission.CDT.dRat (xK - 1 : RatFunc ℚ) = 1 := by
      have hx1 : (xK - 1 : RatFunc ℚ)
          = algebraMap (Polynomial ℚ) (RatFunc ℚ) (Polynomial.X - 1) := by
        rw [map_sub, RatFunc.algebraMap_X, map_one]
        rfl
      rw [hx1, Submission.CDT.dRat_algebraMap]
      have hX : Polynomial.derivative ((Polynomial.X : Polynomial ℚ) - 1) = 1 := by
        rw [Polynomial.derivative_sub, Polynomial.derivative_X]
        simp
      rw [hX, map_one]
    rw [h1, mul_one, h2] at h
    linear_combination h
  have hb : toL (Submission.CDT.dRat phiK) * toL (xK - 1) = 1 - toL phiK := by
    rw [← toL_mul, ← toL_one, ← toL_sub, hdphiK]
  exact mul_right_cancel₀ hU0 (hd'.trans hb.symm)


/-- The value of `dRat phiK`: `(x/(x-1))' = -1/(x-1)²`. -/
theorem dRat_phiK_val : Submission.CDT.dRat phiK = -1 / (xK - 1) ^ 2 := by
  have hx : (xK : RatFunc ℚ) = algebraMap (Polynomial ℚ) (RatFunc ℚ) Polynomial.X :=
    RatFunc.algebraMap_X.symm
  have hx1 : (xK - 1 : RatFunc ℚ)
      = algebraMap (Polynomial ℚ) (RatFunc ℚ) (Polynomial.X - 1) := by
    rw [map_sub, RatFunc.algebraMap_X, map_one]
    rfl
  rw [show phiK = xK / (xK - 1) from rfl, hx1, hx, Submission.CDT.dRat_div]
  have hnp : Polynomial.derivative (Polynomial.X : Polynomial ℚ) * (Polynomial.X - 1)
      - Polynomial.X * Polynomial.derivative ((Polynomial.X : Polynomial ℚ) - 1) = -1 := by
    have h1 : Polynomial.derivative ((Polynomial.X : Polynomial ℚ) - 1) = 1 := by
      rw [Polynomial.derivative_sub, Polynomial.derivative_X]
      simp
    rw [Polynomial.derivative_X, h1]
    ring
  rw [hnp, map_neg, map_one]

/-- `dRat (dRat phiK) = 2/(x-1)³`. -/
theorem dRat2_phiK_val :
    Submission.CDT.dRat (Submission.CDT.dRat phiK) = 2 / (xK - 1) ^ 3 := by
  have hrel : phiK * (xK - 1) = xK := by
    rw [show phiK = xK / (xK - 1) from rfl, div_mul_cancel₀]
    exact xK_sub_one_ne_zero
  have hdx : Submission.CDT.dRat (xK : RatFunc ℚ) = 1 := by
    have hx : (xK : RatFunc ℚ) = algebraMap (Polynomial ℚ) (RatFunc ℚ) Polynomial.X :=
      RatFunc.algebraMap_X.symm
    rw [hx, Submission.CDT.dRat_algebraMap, Polynomial.derivative_X, map_one]
  have hdx1 : Submission.CDT.dRat (xK - 1 : RatFunc ℚ) = 1 := by
    have hx1 : (xK - 1 : RatFunc ℚ)
        = algebraMap (Polynomial ℚ) (RatFunc ℚ) (Polynomial.X - 1) := by
      rw [map_sub, RatFunc.algebraMap_X, map_one]
      rfl
    rw [hx1, Submission.CDT.dRat_algebraMap]
    have h1 : Polynomial.derivative ((Polynomial.X : Polynomial ℚ) - 1) = 1 := by
      rw [Polynomial.derivative_sub, Polynomial.derivative_X]
      simp
    rw [h1, map_one]
  have h : Submission.CDT.dRat phiK * (xK - 1) + phiK = 1 := by
    have hh := congrArg Submission.CDT.dRat hrel
    rw [Submission.CDT.dRat_mul, hdx1, mul_one, hdx] at hh
    linear_combination hh
  have h2 : Submission.CDT.dRat (Submission.CDT.dRat phiK) * (xK - 1)
      = -2 * Submission.CDT.dRat phiK := by
    have hh := congrArg Submission.CDT.dRat h
    rw [Submission.CDT.dRat_add, Submission.CDT.dRat_mul, hdx1, Submission.CDT.dRat_one,
      mul_one] at hh
    linear_combination hh
  have h3 : Submission.CDT.dRat (Submission.CDT.dRat phiK)
      = -2 * Submission.CDT.dRat phiK / (xK - 1) := by
    rw [eq_div_iff xK_sub_one_ne_zero]
    exact h2
  rw [h3, dRat_phiK_val]
  field_simp


end Work.CDcl
