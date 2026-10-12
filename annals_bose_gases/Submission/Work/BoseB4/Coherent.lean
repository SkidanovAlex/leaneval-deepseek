import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseB4.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.Coherent` — coherent states and the `c`-number substitution

FS §8.3 (`thm:Kafz`) replaces the condensate operators `a₀`, `a₀†` by the
complex numbers `z`, `z̄` by resolving the identity in coherent states
`|z⟩ = e^{z a₀†}Ω`:

    `1 = ∫_ℂ |z⟩⟨z| dν(z)`,  `dν(z) = e^{-|z|²} d²z/π`,  `a₀|z⟩ = z|z⟩`.

On the Fock space presented as `Fock E = ⨁_n E` with the condensate quantum
number as grading, the *coherent-state transform* of a core vector `Ψ` is

    `Phi Ψ z = ⟨z|Ψ⟩ = ∑_n (z̄^n/√(n!)) • Ψ n ∈ E`,

where `Ψ n = (level n)^* Ψ` is the `n`-condensate-quanta component
(`Defs.Embed_apply`).  The two structural facts used by FS are

* `Phi (a0d Ψ) z = z̄ * Phi Ψ z` (`Phi_a0d`) — creation is multiplication;
* `Phi (lift B Ψ) z = B (Phi Ψ z)` (`Phi_lift`) — spectator operators act
  levelwise;

and the two analytic facts are the **Bargmann isometry**

    `⟪Ψ, Ψ'⟫ = ∫_ℂ ⟪Phi Ψ z, Phi Ψ' z⟫ dν(z)`

(the resolution of the identity) and the **anti-Wick substitution theorem**

    `⟪Ψ, (a₀†)^q (a₀)^p Ψ'⟫ = ∫_ℂ z^p z̄^q ⟪Phi Ψ z, Phi Ψ' z⟫ dν(z)`,

equivalently (FS `eq:subst-z`) `a₀†a₀ = a₀a₀† − 1`, `a₀†a₀†a₀a₀ = |z|⁴ − 4|z|² + 2`
etc. — i.e. the *anti-normal* ordering of the monomial in `a₀, a₀†`.  Those two
facts live in `Submission/Work/BoseB4/Bargmann.lean` and
`Submission/Work/BoseB4/Kafz.lean`.

**Note on a typo in the source.**  FS `lem:2ndQuand` prints
`n₀² = (a₀†)²a₀² − a₀†a₀`; the correct identity, and the one compatible with
FS's own substitution rules, is `n₀² = (a₀†)²a₀² + a₀†a₀` (see
`Work.BoseB4.Alg.numOp_sq`).  Everything below is consistent with the `+` sign.
-/

noncomputable section

open scoped lp NNReal ENNReal
open MeasureTheory

namespace Work.BoseB4

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-! ## 1. The Gaussian measure `dν(z) = e^{-|z|²} d²z/π` on `ℂ` -/

/-- The Gaussian density `e^{-|z|²}/π` as a nonnegative real. -/
noncomputable def gaussWeight (z : ℂ) : ℝ≥0 :=
  ⟨Real.exp (-(‖z‖ ^ 2)) / Real.pi, by positivity⟩

/-- **The Gaussian measure** `dν(z) = e^{-|z|²} d²z/π` on `ℂ`. -/
noncomputable def gauss : Measure ℂ :=
  volume.withDensity fun z => (gaussWeight z : ℝ≥0∞)

lemma measurable_gaussWeight : Measurable gaussWeight := by
  unfold gaussWeight
  fun_prop

/-- Unfolding the Gaussian measure: the integral against `gauss` is the integral
against Lebesgue measure of the density times the integrand. -/
lemma integral_gauss {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] (f : ℂ → E') :
    ∫ z, f z ∂gauss = ∫ z, (gaussWeight z : ℝ) • f z ∂volume :=
  integral_withDensity_eq_integral_smul measurable_gaussWeight f

/-! ## 2. The coherent-state transform `Φ(z) = ⟨z|Ψ⟩` -/

/-- The weight `z̄^n/√(n!)` of the `n`-th condensate level in the coherent state
`|z⟩ = ∑_n (z^n/√(n!)) e_n`. -/
noncomputable def cohWeight (n : ℕ) (z : ℂ) : ℂ :=
  (starRingEnd ℂ z) ^ n / ((Real.sqrt ((n.factorial : ℝ)) : ℝ) : ℂ)

/-- The coherent-state transform, as a linear map in the state. -/
noncomputable def PhiLin (z : ℂ) : FockCore E →ₗ[ℂ] E :=
  Finsupp.lsum ℂ fun n : ℕ => cohWeight n z • (1 : E →ₗ[ℂ] E)

/-- **The coherent-state transform** `Φ(z) = ⟨z|Ψ⟩ = ∑_n (z̄^n/√(n!)) • Ψ n`. -/
noncomputable def Phi (Ψ : FockCore E) (z : ℂ) : E := PhiLin (E := E) z Ψ

@[simp]
lemma Phi_single (n : ℕ) (v : E) (z : ℂ) :
    Phi (Finsupp.single n v) z = cohWeight n z • v := by
  rw [Phi, PhiLin, Finsupp.lsum_single]
  rfl

lemma Phi_add (Ψ Ψ' : FockCore E) (z : ℂ) :
    Phi (Ψ + Ψ') z = Phi Ψ z + Phi Ψ' z :=
  map_add (PhiLin (E := E) z) Ψ Ψ'

lemma Phi_smul (c : ℂ) (Ψ : FockCore E) (z : ℂ) :
    Phi (c • Ψ) z = c • Phi Ψ z :=
  map_smul (PhiLin (E := E) z) c Ψ

/-- The scalar recursion behind `Phi (a0d Ψ) z = z̄ • Phi Ψ z`:
`(z̄^{n+1}/√((n+1)!))·√(n+1) = z̄·(z̄^n/√(n!))`. -/
lemma cohWeight_succ (n : ℕ) (z : ℂ) :
    cohWeight (n + 1) z * sq (n + 1) = (starRingEnd ℂ z) * cohWeight n z := by
  have hfac : ((n + 1).factorial : ℝ) = ((n : ℝ) + 1) * (n.factorial : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have hsqrt : ((Real.sqrt (((n + 1).factorial : ℝ)) : ℝ) : ℂ)
      = ((Real.sqrt ((n : ℝ) + 1) : ℝ) : ℂ) * ((Real.sqrt ((n.factorial : ℝ)) : ℝ) : ℂ) := by
    rw [hfac, Real.sqrt_mul (by positivity)]
    push_cast
    ring
  have hne : ((Real.sqrt ((n.factorial : ℝ)) : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt ((n.factorial : ℝ)) := by
      rw [Real.sqrt_pos]
      exact_mod_cast Nat.factorial_pos n
    exact_mod_cast this.ne'
  rw [cohWeight, cohWeight, sq, hsqrt]
  field_simp
  push_cast
  ring_nf

end Work.BoseB4
