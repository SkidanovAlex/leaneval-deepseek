import Submission.ZagierHoffmanProof.ATSecondBlock
import Submission.ZagierHoffmanProof.ABPPoly
import Submission.ZagierHoffmanProof.AmbientRing

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
open Polynomial PowerSeries
open scoped WithZero Topology

/-!
# The Anderson–Thakur `H_n` of the `t`-motive, in the range `n ≤ 2q - 2`

Ngo Dac's §4.2/§6 uses the Anderson–Thakur polynomials `H_n ∈ A[t]` (`A = F_q[θ]`), which are the
`α_n` of `CarlitzAT.lean` **with the two variables exchanged**; `H_n = 1` for `n ≤ q`
(`α_n = 1`, `atAlpha_eq_one_of_le`) and, in the second block `q < n ≤ 2q - 2` (proved in
`ATSecondBlock.lean`),

  `H_{q+k-1} = (t^q - t) + (k - 1)·(t^q - θ^q)`,   `1 ≤ k ≤ q - 1`.

This file provides these polynomials as elements of `Polynomial (Ambient F)` (`ambH`), together with
the evaluation of their Frobenius twists at `θ`:

  `(H_n)^{(d)}(θ) = (n - q + 1)·θ^q - θ - (n - q)·θ^(q^(d+1))`   (`q < n`),

which is exactly `α_n(θ, θ^(q^d))` — the value of the Anderson–Thakur interpolation in the
Frobenius orbit, as needed for the bridge (4.2) `L(𝔰;Q)(θ) = Γ_𝔰·ζ_A(𝔰)·π̃^{-w}`.

The remaining input is the arithmetic identity (`Commons.NumberTheory.PowerSum.second_block`):
`P_d(n)·ambEll(d)^n = α_n(θ,θ^(q^d))/Γ_n` for `q ≤ n ≤ 2q - 2`, which turns the evaluation above
into the interpolation `(H_n)^{(d)}(θ) = Γ_n·ambEll(d)^n·P_d(n)`.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F]

/-- Natural numbers are fixed by the `q ^ d`-th power map in the characteristic-`p` field
`Ambient F`. -/
lemma natCast_ambient_pow_card_pow (m d : ℕ) :
    ((m : Ambient F)) ^ (Nat.card F ^ d) = (m : Ambient F) := by
  haveI : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = Nat.card F := Fintype.card_eq_nat_card
  have h1 : ((m : Ambient F)) ^ Nat.card F = (m : Ambient F) := by
    rw [show ((m : Ambient F)) = algebraMap F (Ambient F) ((m : F)) from (map_natCast _ m).symm,
      ← map_pow, ← hcard, FiniteField.pow_card]
  induction d with
  | zero => rw [pow_zero, pow_one]
  | succ d ih => rw [pow_succ, pow_mul, ih, h1]

/-- The Anderson–Thakur `H_n` of Dac §4.2, in the range `n ≤ 2q - 2` (the `t`-motive datum of
`theorem_D`): `H_n = 1` for `n ≤ q` and `H_{q+k-1} = (t^q-t)+(k-1)(t^q-θ^q)`. -/
noncomputable def ambH (n : ℕ) : Polynomial (Ambient F) :=
  if n ≤ Nat.card F then 1
  else Polynomial.X ^ Nat.card F - Polynomial.X
    + Polynomial.C ((n - Nat.card F : ℕ) : Ambient F)
      * (Polynomial.X ^ Nat.card F - Polynomial.C ((ambTheta F) ^ Nat.card F))

lemma ambH_of_le {n : ℕ} (hn : n ≤ Nat.card F) : ambH F n = 1 := by
  rw [ambH, if_pos hn]

lemma ambH_of_gt {n : ℕ} (hn : Nat.card F < n) : ambH F n =
    Polynomial.X ^ Nat.card F - Polynomial.X
      + Polynomial.C ((n - Nat.card F : ℕ) : Ambient F)
        * (Polynomial.X ^ Nat.card F - Polynomial.C ((ambTheta F) ^ Nat.card F)) := by
  rw [ambH, if_neg (by omega)]

/-- The Frobenius twist of `H_n` (`q < n`): the coefficient `θ^q` becomes `θ^(q^(d+1))`. -/
lemma polyTwist_ambH {n d : ℕ} (hn : Nat.card F < n) :
    polyTwist (q := Nat.card F) d (ambH F n)
      = Polynomial.X ^ Nat.card F - Polynomial.X
        + Polynomial.C ((n - Nat.card F : ℕ) : Ambient F)
          * (Polynomial.X ^ Nat.card F
              - Polynomial.C ((ambTheta F) ^ (Nat.card F ^ (d + 1)))) := by
  simp only [ambH_of_gt F hn, polyTwist, polyTwistHom_apply, Polynomial.map_add,
    Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_C, Polynomial.C_pow, frobPowHom_apply, natCast_ambient_pow_card_pow, pow_succ]
  ring

/-- ★★ **The `H_n`-polynomial evaluated along the Frobenius orbit**: for `q < n` and all `d`,
`(H_n)^{(d)}(θ) = (n-q+1)·θ^q - θ - (n-q)·θ^(q^(d+1))` (= `α_n(θ, θ^(q^d))`). -/
theorem evalSeriesGen_frobTwist_ambH {n d : ℕ} (hn1 : Nat.card F < n) :
    evalSeriesGen (frobTwist (R := Ambient F) (p := Nat.card F) d
        ((ambH F n : Polynomial (Ambient F)) : PowerSeries (Ambient F))) (ambTheta F)
      = (((n - Nat.card F + 1 : ℕ) : Ambient F) * (ambTheta F) ^ Nat.card F - (ambTheta F)
          - ((n - Nat.card F : ℕ) : Ambient F)
            * (ambTheta F) ^ (Nat.card F ^ (d + 1))) := by
  rw [show ((ambH F n : Polynomial (Ambient F)) : PowerSeries (Ambient F))
      = coeHom (K := Ambient F) (ambH F n) from rfl]
  rw [← coe_polyTwist (q := Nat.card F) d (ambH F n), coeHom_apply, evalSeriesGen_polynomial,
    polyTwist_ambH F hn1]
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C]
  push_cast
  ring

end ZagierHoffmanPositiveChar
