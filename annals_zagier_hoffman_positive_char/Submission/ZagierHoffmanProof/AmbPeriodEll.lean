import Submission.ZagierHoffmanProof.EllFrob
import Submission.ZagierHoffmanProof.AmbPeriod

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Polynomial PowerSeries Finset
open scoped WithZero Topology

/-!
# The iterated functional equation for the Anderson–Thakur period `Ω`

`AmbPeriod.ambOmega_functional` is `(t-θ^q)·Ω^{(1)} = Ω`; iterating it (`EllFrob`) gives
`(∏_{i=1}^{d}(t-θ^{q^i}))·Ω^{(d)} = Ω` and, after evaluation at `t = θ`,

    `(∏_{i=1}^{d}(θ-θ^{q^i}))·(Ω^{(d)})(θ) = Ω(θ)`,

i.e. `(Ω^{(d)})(θ) = Ω(θ)/ℓ_d` with `ℓ_d = ∏_{i=1}^{d}(θ-θ^{q^i})` (the paper's `ℓ_d`).
Since the "so-called period" of the workspace is `π := 1/Ω(θ)`, this is exactly the relation
`(Ω^{(d)})(θ) = π^{-1}ℓ_d^{-1}` that the ζ_A ↔ CMPL bridge (Dac (4.2) / AT09 (2.4.1)) uses in the
per-degree identity `(Ω^{s}H_{s-1})^{(d)}(θ) = Γ_sS_d(s)/π^s`.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F]

/-- **The iterated functional equation for `Ω`, evaluated at `θ`** (cleared form). -/
theorem ambOmega_iter_eval (d : ℕ) :
    (∏ i ∈ Finset.range d,
        ((ambTheta F) - (ambTheta F) ^ ((Nat.card F) ^ (i + 1)))) *
      evalSeriesGen
        (frobTwist (R := Ambient F) (p := Nat.card F) d (ambOmega F)) (ambTheta F)
      = evalSeriesGen (ambOmega F) (ambTheta F) :=
  ellSh_eval_mul (K := Ambient F) (q := Nat.card F) (θ := ambTheta F) (γ := ambGamma)
    (ambGamma_lt_one) (gammaArchimedean_rat) (ambGamma_pos) d
    (gSuperEntire_ambOmega F) (ambOmega_functional F)

/-- **The iterated functional equation for `Ω` at `θ`**, division form:
`(Ω^{(d)})(θ) = Ω(θ)/ℓ_d` (with `ℓ_d = ∏_{i<d}(θ-θ^{q^{i+1}}) ≠ 0`, so that the division is
legitimate). -/
theorem ambOmega_twist_eval (d : ℕ)
    (hℓ : (∏ i ∈ Finset.range d,
        ((ambTheta F) - (ambTheta F) ^ ((Nat.card F) ^ (i + 1)))) ≠ 0) :
    evalSeriesGen
        (frobTwist (R := Ambient F) (p := Nat.card F) d (ambOmega F)) (ambTheta F)
      = evalSeriesGen (ambOmega F) (ambTheta F) /
        ∏ i ∈ Finset.range d, ((ambTheta F) - (ambTheta F) ^ ((Nat.card F) ^ (i + 1))) := by
  rw [eq_div_iff hℓ, mul_comm]
  exact ambOmega_iter_eval F d

/-- **The per-degree factor of the ζ_A ↔ CMPL bridge** (cleared form):
`ℓ_d^s · ((Ω^{(d)})^s)(θ) = (Ω(θ))^s`.  In the notation of Dac (4.2) / AT09 (2.4.1) this is
`(Ω^{s})^{(d)}(θ) = π^{-s}ℓ_d^{-s}` with `π := 1/Ω(θ)`. -/
theorem ambOmega_iter_eval_pow (d s : ℕ) :
    (∏ i ∈ Finset.range d,
        ((ambTheta F) - (ambTheta F) ^ ((Nat.card F) ^ (i + 1)))) ^ s *
      (evalSeriesGen
        (frobTwist (R := Ambient F) (p := Nat.card F) d (ambOmega F)) (ambTheta F)) ^ s
      = (evalSeriesGen (ambOmega F) (ambTheta F)) ^ s := by
  rw [← mul_pow, ambOmega_iter_eval]

end ZagierHoffmanPositiveChar
