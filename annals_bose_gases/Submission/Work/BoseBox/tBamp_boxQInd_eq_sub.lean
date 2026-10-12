import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.UBBInputs9.A.tBdiagFormInd_eq_tBdiagForm
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBox.tBamp_boxQInd_eq_sub`

The windowed `p`-mode amplitude

    `tBamp χ p Ψ i x = ∫_z (χ z)e^{−i⟪p,z⟫}·Ψ(x_{i←z}) dz`

is a **linear** functional of its state argument `Ψ`.  The FS-faithful box projection of round 8,
`Q_{B,i} = 1_B − P_{B,i}` (`Work.UBBInputs8.boxQInd`), is the indicator times the mean-free state,

    `Q_{B,i}Ψ = 1_A(x_i)·(Ψ − ⨍_A Ψ)`,

so when the window `χ` is supported in the box `A` its amplitude decomposes as the *sharp*
subtraction identity

    `tBamp χ p (Q_{B,i}Ψ) i x
       = tBamp χ p Ψ i x
         − (P_{B,i}Ψ)(x_{i←z₀}) · tBamp χ p 1 i x`.

Two remarks on the shape of the statement.

* The box mean `P_{B,i}Ψ` is **constant along the slot-`i` coordinate** inside the amplitude
  (`Function.update_idem`): `P_{B,i}Ψ(x_{i←z}) = |A|⁻¹∫_A Ψ(x_{i←z'})dz'` for *every* `z`, so the
  `z₀` of the statement is invisible — as it must be, since `tBamp` integrates over precisely the
  slot-`i` variable.
* Nothing is assumed about the set `A` (not even measurability) and nothing about `volA`
  (in particular `volA` need not be nonzero): the identity is an identity of the *pointwise*
  algebra of the definitions plus the linearity of the Bochner integral.  The only analytic input
  is the integrability of the two amplitude integrands, which follows from
  `χ` continuous with compact support and `Ψ` continuous.

Compared with the sibling identity `Work.BoseBox.tBamp_boxQInd_eq` (which is stated for the
indicator-free `boxQ` and needs `volA ≠ 0`, `Integrable χ` and a *compactly supported* state), the
statement here is for the FS-faithful `boxQInd`, for an arbitrary `A`, and only needs `Ψ` to be
continuous.
-/

namespace Work.BoseBox

open MeasureTheory

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1  The factorisation of the FS box projection -/

/-- `Q_{B,i}` is the box indicator times the mean-free state:
`boxQInd volA A i Φ = 1_A(·_i)·(Φ − |A|⁻¹∫_A Φ(·_{i←z})dz)`.  This is a pure `ring` identity
between the two definitions (`boxPInd` is `|A|⁻¹∫_A Φ(·_{i←z})dz` times the same indicator). -/
lemma boxQInd_eq_indicator_mul_sub {volA : ℝ} {A : Set ℝ³} {N : ℕ}
    (i : Fin N) (Φ : Submission.BoseGases.X N → ℝ) :
    Work.UBBInputs8.boxQInd volA A i Φ
      = fun y : Submission.BoseGases.X N => A.indicator (fun _ => (1 : ℝ)) (y i)
          * (Φ y - (1 / volA) * ∫ z in A, Φ (Function.update y i z)) := by
  funext y
  simp only [Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxPInd]
  ring

/-! ## 2  Integrability of the amplitude integrand -/

/-- The integrand of `tBamp` is integrable as soon as the window is continuous with compact
support and the state is continuous: `z ↦ (χ z)e^{−i⟪p,z⟫}(Ψ(x_{i←z}))` is continuous (the
exponential factor is continuous, the slot insertion is `continuous_update`) and its support is
contained in `tsupport χ`, hence compact. -/
lemma integrable_tBamp_integrand {χ : ℝ³ → ℝ} (hχc : Continuous χ) (hχcs : HasCompactSupport χ)
    {N : ℕ} (Ψ : Submission.BoseGases.X N → ℝ) (hΨc : Continuous Ψ) (p : ℝ³) (i : Fin N)
    (x : Submission.BoseGases.X N) :
    Integrable (fun z : ℝ³ => (χ z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))
      * (Ψ (Function.update x i z) : ℂ)) := by
  have hcont : Continuous (fun z : ℝ³ => (χ z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))
      * (Ψ (Function.update x i z) : ℂ)) := by
    fun_prop
  have hcs : HasCompactSupport (fun z : ℝ³ => (χ z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))
      * (Ψ (Function.update x i z) : ℂ)) := by
    have h1 : HasCompactSupport (fun z : ℝ³ => (χ z : ℂ)) := hχcs.comp_left Complex.ofReal_zero
    have h2 : (fun z : ℝ³ => (χ z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))
        * (Ψ (Function.update x i z) : ℂ))
        = (fun z : ℝ³ => (χ z : ℂ)) * (fun z : ℝ³ => Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))
            * (Ψ (Function.update x i z) : ℂ)) := by
      funext z; simp only [Pi.mul_apply]; ring
    rw [h2]
    exact h1.mul_right
  exact hcont.integrable_of_hasCompactSupport hcs

/-! ## 3  The three linearity steps for `tBamp` -/

/-- `tBamp` only sees the values of its argument on the slot-`i` fibre through `x`: two states
that agree on `{x_{i←z} | z}` have the same amplitude. -/
lemma tBamp_congr_slot {N : ℕ} (χ : ℝ³ → ℝ) (p : ℝ³) {f g : Submission.BoseGases.X N → ℝ}
    (i : Fin N) (x : Submission.BoseGases.X N)
    (h : ∀ z : ℝ³, f (Function.update x i z) = g (Function.update x i z)) :
    Work.SmallBoxTBWord.tBamp χ p f i x = Work.SmallBoxTBWord.tBamp χ p g i x := by
  simp only [Work.SmallBoxTBWord.tBamp]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with z
  rw [h z]

/-- The amplitude is additive: `tBamp χ p (f − g) = tBamp χ p f − tBamp χ p g`.  This is the
Bochner-integral linearity `integral_sub` (which needs both integrands integrable, supplied here
as hypotheses) after the pointwise rewrite `↑(f − g) = ↑f − ↑g`. -/
lemma tBamp_sub {N : ℕ} (χ : ℝ³ → ℝ) (p : ℝ³) (f g : Submission.BoseGases.X N → ℝ)
    (i : Fin N) (x : Submission.BoseGases.X N)
    (hf : Integrable (fun z : ℝ³ => (χ z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))
      * (f (Function.update x i z) : ℂ)))
    (hg : Integrable (fun z : ℝ³ => (χ z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))
      * (g (Function.update x i z) : ℂ))) :
    Work.SmallBoxTBWord.tBamp χ p (fun y => f y - g y) i x
      = Work.SmallBoxTBWord.tBamp χ p f i x - Work.SmallBoxTBWord.tBamp χ p g i x := by
  simp only [Work.SmallBoxTBWord.tBamp]
  rw [show (fun z : ℝ³ => (χ z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))
        * (((f (Function.update x i z) - g (Function.update x i z)) : ℝ) : ℂ))
      = (fun z : ℝ³ => (χ z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))
          * (f (Function.update x i z) : ℂ))
        - (fun z : ℝ³ => (χ z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))
          * (g (Function.update x i z) : ℂ)) from by
      funext z
      simp only [Pi.sub_apply, Complex.ofReal_sub]
      ring]
  exact MeasureTheory.integral_sub hf hg

/-- A state which is constant along the slot-`i` fibre has amplitude equal to that constant times
the amplitude of the constant state `1` (`integral_const_mul`, no integrability needed). -/
lemma tBamp_const {N : ℕ} (χ : ℝ³ → ℝ) (p : ℝ³) (K : ℝ) (i : Fin N)
    (x : Submission.BoseGases.X N) :
    Work.SmallBoxTBWord.tBamp χ p (fun _ : Submission.BoseGases.X N => K) i x
      = (K : ℂ) * Work.SmallBoxTBWord.tBamp χ p (fun _ : Submission.BoseGases.X N => (1 : ℝ)) i x := by
  simp only [Work.SmallBoxTBWord.tBamp]
  rw [← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with z
  simp only [Complex.ofReal_one]
  ring

/-! ## 4  The subtraction identity -/

/-- **`tBamp` of the FS box projection.**  With the window supported in the box, the amplitude of
`Q_{B,i}Ψ` splits off the box mean:

    `tBamp χ p (Q_{B,i}Ψ) i x = tBamp χ p Ψ i x − (P_{B,i}Ψ)(x_{i←z₀})·tBamp χ p 1 i x`.

The proof is the factorisation `boxQInd_eq_indicator_mul_sub`, the invisibility of the box
indicator to the amplitude (`Work.UBBInputs9.A.tBamp_indicator_mul`), the constancy of the box mean
along the fibre (`Function.update_idem`) and the three linearity steps above. -/
theorem tBamp_boxQInd_eq_sub {volA : ℝ} {A : Set (EuclideanSpace ℝ (Fin 3))}
    {χ : EuclideanSpace ℝ (Fin 3) → ℝ} {N : ℕ} (Ψ : Submission.BoseGases.X N → ℝ)
    (i : Fin N) (p : EuclideanSpace ℝ (Fin 3)) (x : Submission.BoseGases.X N)
    (z₀ : EuclideanSpace ℝ (Fin 3))
    (hχzero : ∀ z : EuclideanSpace ℝ (Fin 3), z ∉ A → χ z = 0)
    (hχc : Continuous χ) (hχcs : HasCompactSupport χ) (hΨc : Continuous Ψ) :
    Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i Ψ) i x
      = Work.SmallBoxTBWord.tBamp χ p Ψ i x
        - ((Work.SmallBoxTBWord.boxP volA A i Ψ (Function.update x i z₀) : ℝ) : ℂ)
          * Work.SmallBoxTBWord.tBamp χ p (fun _ : Submission.BoseGases.X N => (1 : ℝ)) i x := by
  have hfac : Work.UBBInputs8.boxQInd volA A i Ψ
      = fun y : Submission.BoseGases.X N => A.indicator (fun _ => (1 : ℝ)) (y i)
          * (Ψ y - (1 / volA) * ∫ z in A, Ψ (Function.update y i z)) :=
    boxQInd_eq_indicator_mul_sub i Ψ
  rw [hfac, Work.UBBInputs9.A.tBamp_indicator_mul hχzero p _ i x]
  -- the box mean is the constant `K` of the fibre through `x`
  set K : ℝ := (1 / volA) * ∫ z in A, Ψ (Function.update x i z) with hK
  have hboxP : Work.SmallBoxTBWord.boxP volA A i Ψ (Function.update x i z₀) = K := by
    rw [hK, Work.SmallBoxTBWord.boxP]
    congr 1
    apply MeasureTheory.integral_congr_ae
    filter_upwards with z
    rw [Function.update_idem]
  rw [hboxP]
  -- on the fibre the mean-free state is `Ψ − K`
  have hslot : ∀ z : ℝ³,
      (fun y : Submission.BoseGases.X N => Ψ y - (1 / volA) * ∫ z' in A, Ψ (Function.update y i z'))
          (Function.update x i z)
        = (fun y : Submission.BoseGases.X N => Ψ y - K) (Function.update x i z) := by
    intro z
    show Ψ (Function.update x i z) - (1 / volA) * ∫ z' in A, Ψ (Function.update (Function.update x i z) i z')
      = Ψ (Function.update x i z) - K
    rw [hK]
    congr 2
    apply MeasureTheory.integral_congr_ae
    filter_upwards with z'
    rw [Function.update_idem]
  rw [tBamp_congr_slot (f := fun y : Submission.BoseGases.X N =>
        Ψ y - (1 / volA) * ∫ z' in A, Ψ (Function.update y i z'))
      (g := fun y : Submission.BoseGases.X N => Ψ y - K) χ p i x hslot]
  rw [tBamp_sub χ p Ψ (fun _ : Submission.BoseGases.X N => K) i x
      (integrable_tBamp_integrand hχc hχcs Ψ hΨc p i x)
      (integrable_tBamp_integrand hχc hχcs (fun _ : Submission.BoseGases.X N => K) continuous_const p i x)]
  rw [tBamp_const χ p K i x]

end Work.BoseBox
