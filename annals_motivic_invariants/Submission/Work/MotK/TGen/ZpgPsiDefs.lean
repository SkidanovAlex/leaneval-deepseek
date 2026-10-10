import Mathlib
import Submission.Work.MotK.TGen.ZTwistDivGeomDefs
import Submission.Work.MotK.TGen.ZTwistDivGeomCerts
import Submission.Work.MotK.TGen.ZpgEIrreducible
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

set_option synthInstance.maxHeartbeats 400000 -- v435-synth

/-!
# `Work.MotK.TGen.ZTwistChartFrac`

The chart `y₀ = 1` of the twisted Klein curve `C_{h²} = V(kleinTwP a b (h²))` is birational to the
plane model `V(zpgE a b h)` of the residual curve: the fraction fields agree.  This is the
"geometric leaf" of node K6 (the paper's `C' = Jac²(C_h)`, twist `2T = h²`).

Coordinates: `S4 = K[y₁,y₂,y₃,y₄]` (`X 0 = y₁, X 1 = y₂, X 2 = y₃, X 3 = y₄`) with chart ideal
`zpgI4 = span (range (zpgQ a b h))`; `S2 = K[X₀,X₁]` (`X 0 = y₁, X 1 = y₃`) with plane eliminant
`zpgE a b h`.

The birational map is the graph of the rational map
`y₄ ↦ c/(h²W)`, `y₂ ↦ (a²h²y₃y₄ − ab y₁²)/b²` over the plane curve, where
`W = b⁴y₁ − a⁴h²y₃²`, `c = −ab³ − a³bh²y₁²y₃`; the *projection* `(y₁,y₂,y₃,y₄) ↦ (y₁,y₃)` is the
inverse.  The certificates `zpgE4 ∈ zpgI4`, `zpgG3 ∈ zpgI4`, `zpg_surj` are imported from
`ZTwistDivGeomCerts`.  See `NOTE_ZTwistChartFrac.md`, `NOTE_ZpgI4SatW.md`.
-/

set_option maxHeartbeats 4000000
set_option autoImplicit false

namespace Work.MotK.TGen

open MvPolynomial

variable {K : Type} [Field K]

/-! ## The plane model, its fraction field, and the graph map `ψ` -/

/-- The plane model of the residual curve. -/
abbrev ZP (K : Type) [Field K] (a b h : K) : Type :=
  MvPolynomial (Fin 2) K ⧸ Ideal.span {zpgE a b h}

/-- The function field of the plane model. -/
abbrev ZPF (K : Type) [Field K] (a b h : K) : Type := FractionRing (ZP K a b h)

section Model

variable (K : Type) [Field K] (a b h : K) [IsDomain (ZP K a b h)]

/-- The class of `X 0` in the function field of the plane model (`= y₁`). -/
noncomputable def zpgx : ZPF K a b h :=
  algebraMap (ZP K a b h) (ZPF K a b h) (Ideal.Quotient.mk _ (X 0 : MvPolynomial (Fin 2) K))

/-- The class of `X 1` in the function field of the plane model (`= y₃`). -/
noncomputable def zpgz : ZPF K a b h :=
  algebraMap (ZP K a b h) (ZPF K a b h) (Ideal.Quotient.mk _ (X 1 : MvPolynomial (Fin 2) K))

/-- `W = b⁴y₁ − a⁴h²y₃²` evaluated at the two plane coordinates (the image of `zpgW`). -/
noncomputable def zpgWbar : ZPF K a b h :=
  algebraMap K (ZPF K a b h) (b ^ 4) * zpgx K a b h
    - algebraMap K (ZPF K a b h) (a ^ 4 * h ^ 2) * (zpgz K a b h) ^ 2

/-- `c = −ab³ − a³bh²y₁²y₃` evaluated at the two plane coordinates (the image of `zpgC`). -/
noncomputable def zpgCbar : ZPF K a b h :=
  algebraMap K (ZPF K a b h) (-(a * b ^ 3))
    - algebraMap K (ZPF K a b h) (a ^ 3 * b * h ^ 2) * (zpgx K a b h) ^ 2 * zpgz K a b h

/-- `y₄ = c/(h²W)` in the plane function field. -/
noncomputable def zpgCc : ZPF K a b h :=
  zpgCbar K a b h
    / (algebraMap K (ZPF K a b h) (h ^ 2) * zpgWbar K a b h)

/-- `y₂ = (a²h²y₃y₄ − ab y₁²)/b²` in the plane function field. -/
noncomputable def zpgf2 : ZPF K a b h :=
  (algebraMap K (ZPF K a b h) (a ^ 2 * h ^ 2) * zpgz K a b h * zpgCc K a b h
      - algebraMap K (ZPF K a b h) (a * b) * (zpgx K a b h) ^ 2)
    / algebraMap K (ZPF K a b h) (b ^ 2)

/-- **The graph map**: `S4 → Frac (K[y₁,y₃]/(zpgE))`,
`y₁ ↦ x`, `y₂ ↦ (a²h²y₃y₄−ab y₁²)/b²`, `y₃ ↦ z`, `y₄ ↦ c/(h²W)`. -/
noncomputable def zpgPsi : MvPolynomial (Fin 4) K →ₐ[K] ZPF K a b h :=
  MvPolynomial.aeval ![zpgx K a b h, zpgf2 K a b h, zpgz K a b h, zpgCc K a b h]

@[simp] theorem zpgPsi_X0 : zpgPsi K a b h (X 0) = zpgx K a b h := by
  simp [zpgPsi]
@[simp] theorem zpgPsi_X1 : zpgPsi K a b h (X 1) = zpgf2 K a b h := by
  simp [zpgPsi]
@[simp] theorem zpgPsi_X2 : zpgPsi K a b h (X 2) = zpgz K a b h := by
  simp [zpgPsi]
@[simp] theorem zpgPsi_X3 : zpgPsi K a b h (X 3) = zpgCc K a b h := by
  simp [zpgPsi]

/-- `ψ` of a constant. -/
@[simp] theorem zpgPsi_C (r : K) : zpgPsi K a b h (C r) = algebraMap K (ZPF K a b h) r := by
  simp [zpgPsi]

/-- `ψ` kills the third chart quadric (this is the definition of `y₂`). -/
theorem zpgPsi_zpgQ3 (hb : (b : K) ≠ 0) : zpgPsi K a b h (zpgQ a b h 3) = 0 := by
  have hb' : algebraMap K (ZPF K a b h) b ≠ 0 := by
    intro hz
    exact hb (RingHom.injective (algebraMap K (ZPF K a b h)) (by rw [hz, map_zero]))
  have hb2 : algebraMap K (ZPF K a b h) (b ^ 2) ≠ 0 := by
    rw [map_pow]; exact pow_ne_zero 2 hb'
  simp only [zpgQ, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, zpgf2,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, zpgPsi_X0, zpgPsi_X1, zpgPsi_X2,
    zpgPsi_X3, zpgPsi_C]
  field_simp
  first | refl_ring1 | ring

/-- `ψ(W)` is `zpgWbar`. -/
theorem zpgPsi_zpgW4 : zpgPsi K a b h (zpgW4 a b h) = zpgWbar K a b h := by
  simp only [zpgW4, zpgWbar, map_sub, map_mul, map_pow, zpgPsi_X0, zpgPsi_X2, zpgPsi_C]

/-- `ψ(c)` is `zpgCbar`. -/
theorem zpgPsi_zpgC4 : zpgPsi K a b h (zpgC4 a b h) = zpgCbar K a b h := by
  simp only [zpgC4, zpgCbar, map_sub, map_mul, map_pow, zpgPsi_X0, zpgPsi_X2, zpgPsi_C]

/-- `ψ` kills the chart relation `zpgG3 = h²W y₄ − zpgC4` (this is the definition of `y₄`). -/
theorem zpgPsi_zpgG3 (hw : zpgWbar K a b h ≠ 0) (hh : (h : K) ≠ 0) :
    zpgPsi K a b h (zpgG3 a b h) = 0 := by
  have hh' : algebraMap K (ZPF K a b h) h ≠ 0 := by
    intro hz
    exact hh (RingHom.injective (algebraMap K (ZPF K a b h)) (by rw [hz, map_zero]))
  have h2 : algebraMap K (ZPF K a b h) (h ^ 2) ≠ 0 := by
    rw [map_pow]; exact pow_ne_zero 2 hh'
  have hden : algebraMap K (ZPF K a b h) (h ^ 2) * zpgWbar K a b h ≠ 0 := mul_ne_zero h2 hw
  rw [zpgG3]
  simp only [map_sub, map_mul, zpgPsi_zpgW4, zpgPsi_zpgC4, zpgPsi_X3, zpgPsi_C, zpgCc]
  rw [div_eq_mul_inv, mul_comm (zpgCbar K a b h), ← mul_assoc, mul_inv_cancel₀ hden, one_mul,
    sub_self]

/-- The chart relation is a combination of the zeroth and third chart quadrics. -/
theorem zpgG3_eq (a b h : K) :
    zpgG3 a b h = -(C (b ^ 2) * zpgQ a b h 0) - C (a ^ 2 * h ^ 2) * X 2 * zpgQ a b h 3 := by
  rw [zpgG3, zpgC4, zpgW4, zpgQ]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, map_mul,
    map_pow, map_neg, map_add, map_sub]
  first | refl_ring1 | ring

end Model

end Work.MotK.TGen
