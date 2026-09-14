import Mathlib
import Submission.Vdw.LocalField.TeichMinpoly
import Submission.Commons.FieldTheory.IntermediateField.finrank_intermediateField_mul

open Classical
open scoped NumberField Polynomial WithZero

set_option autoImplicit false
set_option linter.style.haveILetI false

/-!
# Local-field chapter (G3, tower relations): `[K_P : W] = e_P` over the completion

This module closes the DEGREE half of the tower relations `(b3)` of the
Roadmap Session-85/86 sketch for the unramified-subfield programme:

* `W = Wk p P α := ℚ_p(ζ)` is the subfield of `K_P = kpAdic p P` generated
  over `QpAdic p` by the Teichmüller lift `ζ := teich p P α` of a generator
  `α` of the unit group of the residue field `κ = kap p P` (so `α ≠ 0` and
  `hgen : orderOf (Units.mk0 α hα) = p^f − 1`, `f := P.inertiaDeg ℤ`).

The theorems:

1. `finrank_QpAdic_Wk_eq_inertiaDeg` — `[W : ℚ_p] = f`: the degree of the
   Teichmüller subfield equals the inertia degree (Session-87's
   `teich_minpoly_natDegree_eq_inertiaDeg` attached to the adjoin-degree
   `adjoin_finrank_eq_minpoly_natDegree`).
2. `finrank_kpAdic_over_Wk_eq_ramIdx` — `[K_P : W] = e_P`:
   `Module.finrank (Wk p P α) (kpAdic p P) = P.ramificationIdx ℤ` — by the
   tower identity `finrank_intermediateField_mul` (fleet L112) on the two
   known degrees `[K_P:ℚ_p] = e_P·f_P` (`finrank_kpAdic_eq_global`,
   RamificationCompat) and `[W:ℚ_p] = f_P`, cancelling `f_P > 0`.

3. Finite-generation instances needed by Mathlib's trace API (next stone:
   the local trace identity `Tr_{K_P/ℚ_p}(w) = e_P·Tr_{W/ℚ_p}(w)`, which
   requires `Module.Finite`/`Module.Free` on the towers):
   * `moduleFinite_kpAdic_QpAdic` — `Module.Finite (QpAdic p) (kpAdic p P)`
     (transport of `moduleFinite_kpAdic` over `Padic p` along the base
     identification `qpPadicEquiv p`, via restriction of scalars through the
     scalar tower `Padic → QpAdic → kpAdic`);
   * `moduleFinite_kpAdic_Wk` — `Module.Finite (Wk p P α) (kpAdic p P)`
     (same restriction argument at `QpAdic → Wk → kpAdic`).

Axioms of every statement: propext / Classical.choice / Quot.sound only.
-/

namespace Submission.Vdw.LocalField

noncomputable section

universe u

variable {K : Type u} [Field K] [NumberField K]

/-- `QpAdic p` as an algebra over `Padic p` through the identification
`qpPadicEquiv p` (its inverse is a ring hom `Padic p →+* QpAdic p`). -/
noncomputable instance qpAdicAlgebraPadic (p : ℕ) [Fact (Nat.Prime p)] :
    Algebra (Padic p) (QpAdic p) :=
  RingHom.toAlgebra ((qpPadicEquiv p).symm.toRingEquiv.toRingHom)

/-- The scalar tower `ℚ_[p] → QpAdic → K_P` is consistent: the rebased
`Padic`-algebra structure on `kpAdic` (`kpAdicAlgebraPadic`) is exactly the
native `QpAdic`-structure factored through the identification. -/
instance isScalarTower_Padic_QpAdic_kpAdic (p : ℕ) [Fact (Nat.Prime p)]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    IsScalarTower (Padic p) (QpAdic p) (kpAdic p P) := by
  refine IsScalarTower.of_algebraMap_eq ?_
  intro x
  rfl

/-- **`K_P` is finite-dimensional over `QpAdic p`**: the `Padic p`-finiteness
`moduleFinite_kpAdic` is transported along the base identification
`qpPadicEquiv` (restriction of scalars through the tower
`Padic → QpAdic → K_P` preserves finite generation, with the same
generators). -/
instance moduleFinite_kpAdic_QpAdic (p : ℕ) [Fact (Nat.Prime p)]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    Module.Finite (QpAdic p) (kpAdic p P) := by
  classical
  exact Module.Finite.of_restrictScalars_finite (R := Padic p) (A := QpAdic p)
    (M := kpAdic p P) (hM := moduleFinite_kpAdic p P)

/-- **`K_P` is finite-dimensional over the Teichmüller subfield `W`**: the
`QpAdic`-finiteness restricts to `W` (the scalar tower
`QpAdic → W → K_P`; the `W`-span of the finite `QpAdic`-generating set is
all of `K_P`, since `QpAdic ⊆ W`). -/
instance moduleFinite_kpAdic_Wk (p : ℕ) [Fact (Nat.Prime p)]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (α : kap p P) :
    Module.Finite (Wk p P α) (kpAdic p P) := by
  classical
  exact Module.Finite.of_restrictScalars_finite (R := QpAdic p) (A := Wk p P α)
    (M := kpAdic p P) (hM := moduleFinite_kpAdic_QpAdic p P)

/-- **[W : ℚ_p] = f**: for `W = ℚ_p(ζ)` the Teichmüller subfield, the degree
of `W` over `QpAdic p` equals the inertia degree `f := P.inertiaDeg ℤ`
(Session-87's exact cyclotomic-degree bridge attached to the adjoin-degree
identity). -/
theorem finrank_QpAdic_Wk_eq_inertiaDeg (p : ℕ) [Fact (Nat.Prime p)]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {α : kap p P} (hα : α ≠ 0)
    (hgen : orderOf (Units.mk0 α hα) = p ^ P.inertiaDeg ℤ - 1) :
    Module.finrank (QpAdic p) (Wk p P α) = P.inertiaDeg ℤ := by
  rw [adjoin_finrank_eq_minpoly_natDegree (p := p) (P := P) (α := α) hα]
  exact teich_minpoly_natDegree_eq_inertiaDeg (p := p) (P := P) (α := α) hα hgen

/-- **Tower-degree identity over the completion**: `[K_P : W] = e_P`.  For
`W = ℚ_p(ζ)` the Teichmüller subfield of `K_P` (degree `f := P.inertiaDeg ℤ`
over `QpAdic p`, so `K_P = W·K_P` is a degree-`[K_P:W]` extension), the
degree of `K_P` over `W` equals the ramification index
`e := P.ramificationIdx ℤ`.  Proof: `[K_P:ℚ_p] = e·f`
(`finrank_kpAdic_eq_global`), `[W:ℚ_p] = f`
(`finrank_QpAdic_Wk_eq_inertiaDeg`), the tower identity
`[K_P:ℚ_p] = [W:ℚ_p]·[K_P:W]` (fleet L112
`Commons.FieldTheory.IntermediateField.finrank_intermediateField_mul`), then
cancel `f > 0`.  With the degree half in place, the tower relations `(b3)`
of the Session-85 roadmap reduce to the unramifiedness `e(W) = 1` of
`W/ℚ_p` (the μ_{p'}-content; see Roadmap Session-86). -/
theorem finrank_kpAdic_over_Wk_eq_ramIdx (p : ℕ) [Fact (Nat.Prime p)]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {α : kap p P} (hα : α ≠ 0)
    (hgen : orderOf (Units.mk0 α hα) = p ^ P.inertiaDeg ℤ - 1) :
    Module.finrank (Wk p P α) (kpAdic p P) = P.ramificationIdx ℤ := by
  classical
  have hW : Module.finrank (QpAdic p) (Wk p P α) = P.inertiaDeg ℤ :=
    finrank_QpAdic_Wk_eq_inertiaDeg (p := p) (P := P) (α := α) hα hgen
  have htop : Module.finrank (QpAdic p) (kpAdic p P) =
      P.ramificationIdx ℤ * P.inertiaDeg ℤ :=
    finrank_kpAdic_eq_global p P
  have hfpos : 0 < P.inertiaDeg ℤ := Ideal.inertiaDeg_pos P ℤ
  have hmul := Commons.FieldTheory.IntermediateField.finrank_intermediateField_mul
    (K := QpAdic p) (L := kpAdic p P) (E := Wk p P α)
  -- hmul : finrank (QpAdic p) (Wk p P α) * finrank (Wk p P α) (kpAdic p P)
  --       = finrank (QpAdic p) (kpAdic p P)
  have hmain : P.inertiaDeg ℤ * Module.finrank (Wk p P α) (kpAdic p P) =
      P.ramificationIdx ℤ * P.inertiaDeg ℤ := by
    rw [hW] at hmul
    rw [htop] at hmul
    exact hmul
  have hmain' : P.inertiaDeg ℤ * Module.finrank (Wk p P α) (kpAdic p P) =
      P.inertiaDeg ℤ * P.ramificationIdx ℤ := by
    simpa [Nat.mul_comm] using hmain
  exact Nat.eq_of_mul_eq_mul_left hfpos hmain'


/-- **Scalar-trace reduction at the completed tower**: for `w ∈ W` (the
Teichmüller subfield), the trace of the scalar `w` from `K_P` down to `W` is
`e_P · w`: the `W`-trace of `w ∈ W` inside `K_P` equals
`finrank (Wk) (kpAdic) • w = e_P • w` (`Algebra.trace_algebraMap` +
`finrank_kpAdic_over_Wk_eq_ramIdx`).  This is the `e`-factor of the eventual
local trace identity `Tr_{K_P/ℚ_p}(w) = e_P · Tr_{W/ℚ_p}(w)` (stone 4 of the
Session-53 roadmap); the missing ingredient is trace-transitivity through
the tower (not present in Mathlib — see Roadmap Session-88). -/
theorem trace_kpAdic_of_Wk_eq_smul_ramIdx (p : ℕ) [Fact (Nat.Prime p)]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {α : kap p P} (hα : α ≠ 0)
    (hgen : orderOf (Units.mk0 α hα) = p ^ P.inertiaDeg ℤ - 1)
    (w : Wk p P α) :
    Algebra.trace (Wk p P α) (kpAdic p P)
        (algebraMap (Wk p P α) (kpAdic p P) w)
      = P.ramificationIdx ℤ • w := by
  classical
  have htr := Algebra.trace_algebraMap (R := Wk p P α) (S := kpAdic p P) w
  -- htr : (Algebra.trace (Wk p P α) (kpAdic p P))
  --         (algebraMap (Wk p P α) (kpAdic p P) w)
  --       = Module.finrank (Wk p P α) (kpAdic p P) • w
  rw [finrank_kpAdic_over_Wk_eq_ramIdx (p := p) (P := P) (α := α) hα hgen] at htr
  exact htr


/-- **`W` is finite-dimensional over `QpAdic p`**: the Teichmüller subfield
`W = ℚ_p(ζ)` is generated by the integral element `ζ` (root of `X^q − 1`),
so `IntermediateField.adjoin.finiteDimensional` applies. -/
theorem moduleFinite_QpAdic_Wk (p : ℕ) [Fact (Nat.Prime p)]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {α : kap p P} (hα : α ≠ 0) :
    Module.Finite (QpAdic p) (Wk p P α) :=
  IntermediateField.adjoin.finiteDimensional
    (teich_isIntegral_kpAdic (p := p) (P := P) (α := α) hα)

/-- **THE LOCAL TRACE IDENTITY (stone 4)**: for `w ∈ W = ℚ_p(ζ)` the
Teichmüller subfield of `K_P`, the trace of `w` (viewed in `K_P`) from
`K_P` down to `ℚ_p` equals `e_P` times the trace of `w` from `W` down to
`ℚ_p`:

    Tr_{K_P/ℚ_p}(w) = e_P · Tr_{W/ℚ_p}(w)

Proof: trace-transitivity through the tower `QpAdic → W → K_P`
(`Algebra.trace_trace` — Mathlib `RingTheory/Trace/Defs.lean`), the scalar
reduction `Tr_{K_P/W}(w) = e_P·w`
(`trace_kpAdic_of_Wk_eq_smul_ramIdx`), and `ℚ_p`-linearity of
`Tr_{W/ℚ_p}` (`map_nsmul`).  This is the algebraic core the Session-53/54
roadmap calls "stone 4", the `e`-factor feeding the S1 wild-witness
programme (`K_P/W` totally ramified of degree `e` = `P.ramificationIdx ℤ`
by `finrank_kpAdic_over_Wk_eq_ramIdx`). -/
theorem localTraceIdentity (p : ℕ) [Fact (Nat.Prime p)]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {α : kap p P} (hα : α ≠ 0)
    (hgen : orderOf (Units.mk0 α hα) = p ^ P.inertiaDeg ℤ - 1)
    (w : Wk p P α) :
    (Algebra.trace (QpAdic p) (kpAdic p P))
        (algebraMap (Wk p P α) (kpAdic p P) w)
      = P.ramificationIdx ℤ •
          (Algebra.trace (QpAdic p) (Wk p P α) w) := by
  classical
  haveI : Module.Finite (QpAdic p) (Wk p P α) :=
    moduleFinite_QpAdic_Wk (p := p) (P := P) (α := α) hα
  have hsc := trace_kpAdic_of_Wk_eq_smul_ramIdx (p := p) (P := P) (α := α) hα hgen w
  have htt := Algebra.trace_trace (R := QpAdic p) (S := Wk p P α) (T := kpAdic p P)
    (x := algebraMap (Wk p P α) (kpAdic p P) w)
  -- htt : trace (QpAdic p) (Wk p P α) (trace (Wk p P α) (kpAdic p P) x)
  --         = trace (QpAdic p) (kpAdic p P) x   (trace-transitivity, Mathlib)
  rw [← htt]
  rw [hsc]
  exact map_nsmul (Algebra.trace (QpAdic p) (Wk p P α)) (P.ramificationIdx ℤ) w

end
end Submission.Vdw.LocalField
