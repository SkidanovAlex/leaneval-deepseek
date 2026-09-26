import Mathlib
import Submission.Work.Asymptotics.KhatE1Core.ClearedCombos

/-!
# The exact `E(z)`-expansion of `br8ref` (the `K₋`-reference bracket)

`br8ref ℓ τ z` is a **polynomial of degree `≤ 4` in `e = Ept z`** with coefficients that are
`τ`-atoms: the three reference combinations it is built from (`E₁₀ref·𝓛ref`,
`E₈ref·Wref - E₆ref·D2ref`, `(1728-j(τ))E₈ref·Wref + j(τ)E₆ref·D2ref`) are polynomials in `e` of
degree `≤ 4`.  `br8ref_expand` records this expansion exactly (`ring`), and `Tref8_e2_eq` records
as a corollary the `e²`-coefficient of `Tref8 = Sinvref·br8ref + br0 8`, which must agree with
the `e¹`-coefficient `Xc·R8_q1 + R8_p1` of the explicit `R8` — a non-trivial consistency check
that pins the whole read-off down.

These are the `K₋`-side data from which the `e³`/`e⁴` coefficients of the cleared residual
`Δ(τ)Sh(τ,z)·(Kdev8Bracket - 2·KdevE2·E(z)²)` are assembled (`ClearedCombos`,
`Delta_mul_Dev8Raw` supplies the `Dev8Raw` half). -/

namespace Work.Asymptotics.KhatE1Core

open UpperHalfPlane

noncomputable section

open Work.Kernels

/-- **The exact `e = Ept z` expansion of `br8ref`** (a polynomial of degree `≤ 4`). -/
theorem br8ref_expand (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) :
    Work.Asymptotics.Compact.br8ref ℓ τ z
      = (-3456 * Work.Asymptotics.Compact.Xc ℓ z * E4Fun τ + 1728 * psi4 ℓ τ)
        + Work.Residues.Ept z
            * (27648 * E4Fun τ - 13824 * psi4 ℓ τ
              - 24 * (psi2 ℓ τ * E14Fun τ / DeltaFun τ)
              + 24 * (jInvariantFun τ * psi4 ℓ τ))
        + (Work.Residues.Ept z) ^ 2
            * (-41472 * E4Fun τ + 912384 * Work.Asymptotics.Compact.Xc ℓ z * E4Fun τ
              + 870912 * psi4 ℓ τ
              + 1152 * (psi2 ℓ τ * E14Fun τ / DeltaFun τ)
              - 1152 * (jInvariantFun τ * psi4 ℓ τ))
        + (Work.Residues.Ept z) ^ 3
            * (-7299072 * E4Fun τ - 6635520 * psi4 ℓ τ
              + 4224 * (psi2 ℓ τ * E14Fun τ / DeltaFun τ)
              - 4224 * (jInvariantFun τ * psi4 ℓ τ))
        + (Work.Residues.Ept z) ^ 4
            * (10948608 * E4Fun τ + 19906560 * psi4 ℓ τ
              + 61056 * (jInvariantFun τ * psi4 ℓ τ)
              - 61056 * (psi2 ℓ τ * E14Fun τ / DeltaFun τ)) := by
  rw [Work.Asymptotics.Compact.br8ref, Work.Asymptotics.Compact.E10ref,
    Work.Asymptotics.Compact.Lref, Work.Asymptotics.Compact.E8ref,
    Work.Asymptotics.Compact.Wref, Work.Asymptotics.Compact.E6ref,
    Work.Asymptotics.Compact.D2ref, Work.Asymptotics.Compact.Xc]
  ring

/-- **Consistency of the read-off.**  The `e²`-coefficient of `Tref8 = Sinvref·br8ref + br0 8`,
computed from `br8ref_expand` and `Sinvref = 1 + (j(τ)-720)e²`, agrees with the `e¹`-coefficient
`Xc·R8_q1 + R8_p1` of the explicit `R8`.  This is the non-trivial check that pins the whole
`K₋`-read-off (it is *not* a formal consequence of either side alone; both sides are the
`τ`-atoms `E₄(τ), ψ₄, ψ₂E₁₄/Δ(τ), j(τ)ψ₄` in a specific combination). -/
theorem Tref8_e2_eq (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) :
    Work.Asymptotics.Compact.R8_q1 ℓ τ * Work.Asymptotics.Compact.Xc ℓ z
        + Work.Asymptotics.Compact.R8_p1 ℓ τ
      = (-41472 * E4Fun τ + 912384 * Work.Asymptotics.Compact.Xc ℓ z * E4Fun τ
            + 870912 * psi4 ℓ τ
            + 1152 * (psi2 ℓ τ * E14Fun τ / DeltaFun τ)
            - 1152 * (jInvariantFun τ * psi4 ℓ τ))
        + (jInvariantFun τ - 720)
            * (-3456 * Work.Asymptotics.Compact.Xc ℓ z * E4Fun τ + 1728 * psi4 ℓ τ) := by
  have hΔ : DeltaFun τ ≠ 0 := ClassicalFacts.DeltaFun_ne_zero τ
  rw [Work.Asymptotics.Compact.R8_q1, Work.Asymptotics.Compact.R8_p1]
  field_simp
  ring

end

end Work.Asymptotics.KhatE1Core
