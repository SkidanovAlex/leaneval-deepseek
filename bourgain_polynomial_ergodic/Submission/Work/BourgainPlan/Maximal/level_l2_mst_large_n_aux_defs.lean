import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_scalar_defs
import Submission.Work.BourgainPlan.Maximal.mst_level_defs
import Submission.Work.BourgainPlan.Maximal.polyProfile_decay_sharp
import Submission.Work.BourgainPlan.Maximal.sigmaN_denom_le
import Submission.Work.BourgainPlan.Maximal.sigmaN_separated
import Submission.Work.BourgainPlan.Maximal.sigmaN_card_le
import Submission.Work.BourgainPlan.Maximal.mstEta_support
import Submission.Work.BourgainPlan.Maximal.level_l2_mst_large_n_defs

/-!
# The vocabulary of the large-`n` half of MST Theorem 2, second layer

MST §4.3, the estimate for `sup_{n ≥ 2^{κ_s}}`.  The model operator at scale `2^n` is the
`ℓ²(ℤ)`-multiplier with the level-`s` symbol

`ν_n = Σ_{β ∈ 𝒰((s+1)^l)∖𝒰(s^l)} G β · Φ_{2^n}(· − β) ψ_s(· − β)`,

where `Φ_N = mstProf P N` is the profile and `ψ_s = mstEta d χ η s` is the level bump.  The two
objects introduced here are the ones in which the freezing / averaging argument of MST is carried:

* `mstArc G E t = Σ_{β∈E} G β · e^{2πi t β}` — the arc comb, evaluated at the integer `t`
  (it is `Q_s`-periodic when every `β ∈ E` is a `Q_s`-torsion point of the circle);
* `mstModSeq G E f x = fun k => mstArc G E (k − x) * f k` — the modulation of `f` whose role is
  that the *model operator is a single multiplier applied to it*: MST's identity

  `(the model at scale 2^n applied to f)(y) = Op_{Φ_{2^n} ψ_s} (mstModSeq G E f y) (y)`

  (`opMul_mstModelFn_eq_modSeq` below), which is what makes the `u`-averaging of the paper work.
-/

open MeasureTheory Finset
open scoped BigOperators ENNReal

set_option autoImplicit false

namespace Work.BourgainPlan.Maximal

open Work.BourgainPlan.IonescuWainger

noncomputable section

local notation "Circ" => Work.BourgainPlan.IonescuWainger.Circle
local notation "haarT" => (AddCircle.haarAddCircle (T := 1))

/-- The **arc comb** of a level: `t ↦ Σ_{β∈E} G β · e^{2πi t β}`, an integer-indexed function. -/
def mstArc (G : Circ → ℂ) (E : Finset Circ) (t : ℤ) : ℂ :=
  ∑ β ∈ E, G β * fourier t β

/-- The **modulated input** of the level: `k ↦ mstArc G E (k − x) · f k`.  MST's identity
`ν_n * f = Op_{Φ_{2^n}ψ_s}(mstModSeq G E f y)` at `y` makes this the input whose multiplier is a
single `Φ_{2^n}ψ_s` (instead of the shifted bump over the arcs). -/
def mstModSeq (G : Circ → ℂ) (E : Finset Circ) (f : ℤ → ℂ) (x : ℤ) : ℤ → ℂ :=
  fun k => mstArc G E (k - x) * f k

@[simp] theorem mstArc_apply (G : Circ → ℂ) (E : Finset Circ) (t : ℤ) :
    mstArc G E t = ∑ β ∈ E, G β * fourier t β := rfl

@[simp] theorem mstModSeq_apply (G : Circ → ℂ) (E : Finset Circ) (f : ℤ → ℂ) (x k : ℤ) :
    mstModSeq G E f x k = mstArc G E (k - x) * f k := rfl

/-- A square-summable function modulated by the arc comb stays square-summable. -/
theorem memℒp_mstModSeq {G : Circ → ℂ} {E : Finset Circ} {f : ℤ → ℂ} (hf : Memℓp f 2) (x : ℤ) :
    Memℓp (mstModSeq G E f x) 2 := by
  have hf' : Summable (fun m : ℤ => ‖f m‖ ^ (2 : ℝ)) := by simpa [Memℓp] using hf
  have hB : 0 ≤ ∑ β ∈ E, ‖G β‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine memℓp_gen ?_
  rw [show (2 : ℝ≥0∞).toReal = (2 : ℝ) from ENNReal.toReal_ofNat 2]
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    (hf'.mul_left ((∑ β ∈ E, ‖G β‖) ^ 2))
  have h1 : ‖mstModSeq G E f x k‖ ≤ (∑ β ∈ E, ‖G β‖) * ‖f k‖ := by
    rw [mstModSeq_apply, norm_mul, mstArc]
    exact mul_le_mul_of_nonneg_right (le_trans (norm_sum_le _ _)
      (Finset.sum_le_sum fun β _ => by rw [norm_mul, norm_fourier_apply', mul_one]))
      (norm_nonneg _)
  calc ‖mstModSeq G E f x k‖ ^ (2 : ℝ) ≤ ((∑ β ∈ E, ‖G β‖) * ‖f k‖) ^ (2 : ℝ) :=
        Real.rpow_le_rpow (norm_nonneg _) h1 (by norm_num)
    _ = (∑ β ∈ E, ‖G β‖) ^ 2 * ‖f k‖ ^ (2 : ℝ) := by
        rw [Real.mul_rpow hB (norm_nonneg _), Real.rpow_two, Real.rpow_two]

/-! ## Abbreviations shortening the statements of the companion lemmas -/

/-- The circle `𝕋 = ℝ/ℤ` (abbreviation). -/
abbrev mstCirc : Type := Work.BourgainPlan.IonescuWainger.Circle

/-- The Haar probability measure of the circle (abbreviation). -/
abbrev mstHaar : Measure mstCirc := AddCircle.haarAddCircle (T := 1)

/-- **The model hypothesis at level `s`**: the `L^∞`-class `A n` is the level-`s` model symbol
`Φ_{2^n}·ψ_s` at the dyadic scale `2^n`. -/
def HasModel (P : Polynomial ℤ) (d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (s : ℕ)
    (A : ∀ n : ℕ, Lp ℂ ⊤ mstHaar) : Prop :=
  ∀ n : ℕ, ∀ᵐ ξ ∂mstHaar,
    (A n : mstCirc → ℂ) ξ = mstProf P (2 ^ n) ξ * mstEta d χ η s ξ

/-- **The bump hypothesis at level `s`**: the `L^∞`-class `B` is the level bump `ψ_s`. -/
def HasBump (d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (s : ℕ) (B : Lp ℂ ⊤ mstHaar) : Prop :=
  ∀ᵐ ξ ∂mstHaar, (B : mstCirc → ℂ) ξ = mstEta d χ η s ξ

/-- **The Gauss-sum decay hypothesis on the level `s`** (the only hypothesis MST impose on the
weights `G` of the level). -/
def HasDecay (G : mstCirc → ℂ) (G0 : ℝ) (l s : ℕ) (δ : ℝ) : Prop :=
  ∀ β ∈ mstLvl l s, ‖G β‖ ≤ G0 * ((s : ℝ) + 1) ^ (-(δ * l))

/-! ## The level parameters, with the **real** exponent `1/10`

WARNING.  The sibling module `level_l2_mst_large_n_defs.lean` defines `mstQ s` and `mstN₀ P s` with
an unannotated exponent `1 / 10`, which Lean elaborates as `ℕ`-division `1 / 10 = 0`; both
definitions are therefore *constant* (`mstQ s = (⌈e⌉)! = 6` and `mstN₀ P s = 2^{40·d}` for every
`s`), which contradicts their doc strings.  The two definitions below carry the real exponent
`(1 / 10 : ℝ)` and are the ones used by the large-`n` estimates (and they agree definitionally with
the inlined expression of the target statement `level_l2_mst_large_n`). -/

/-- The common denominator `Q_s = (⌈e^{(s+1)^{1/10}}⌉)!` of the level-`s` arcs. -/
def mstQ' (s : ℕ) : ℕ := Nat.factorial ⌈Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ))⌉₊

/-- The scale `2^{κ_s}`, `κ_s = 20·d·(⌊(s+1)^{1/10}⌋+1)`, where the large-`n` regime starts. -/
def mstN₀' (P : Polynomial ℤ) (s : ℕ) : ℕ :=
  2 ^ (20 * P.natDegree * (⌊((s : ℝ) + 1) ^ (1 / 10 : ℝ)⌋₊ + 1))

theorem mstQ'_pos (s : ℕ) : 0 < mstQ' s := Nat.factorial_pos _

theorem one_le_mstQ' (s : ℕ) : 1 ≤ mstQ' s := Nat.one_le_iff_ne_zero.mpr (mstQ'_pos s).ne'

end
end Work.BourgainPlan.Maximal
