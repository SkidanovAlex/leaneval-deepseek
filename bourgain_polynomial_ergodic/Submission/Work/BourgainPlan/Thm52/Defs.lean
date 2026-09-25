import Mathlib
import Submission.Work.BourgainPlan.Maximal.rhoVarReductions
import Submission.Work.BourgainPlan.Maximal.varRho_tail_glue
import Submission.Work.BourgainPlan.IonescuWainger.mz_square_function
import Submission.Commons.MeasureTheory.Lp.eLpNorm_finset_sum_le_ennreal
import Submission.Commons.MeasureTheory.Lp.eLpNorm_const_mul_ennreal

/-!
# KMSZ Theorem 5.2: the Rademacher–Menshov (`seminorm`) form of the Ionescu–Wainger theorem

Source: D. Kosz, M. Mirek, W. Słomian, J. Zhang, *Remarks on the Ionescu–Wainger multiplier
theorem*, arXiv:2606.12663, §5 (Definition 5.1 and Theorem 5.2).  This chapter of the workspace
formalises §5 in the corpus's `ℓᵖ(ℤ)` language:

* `Work.BourgainPlan.Thm52.SignedDiffBound` — the **uniform-in-signs bound** for the lacunary
  differences of a family of multiplier operators.  This is exactly the shape in which the
  Ionescu–Wainger multiplier theorem (KMSZ Theorem 1.9, i.e. `IWProjectionBound` in this corpus)
  is available: it controls `Σ_m ω_m (T_{n+1} − T_n)` uniformly in the signs `ω`.

* `Work.BourgainPlan.Thm52.LargeScaleBound` — the **sampling-principle half** (KMSZ Definition
  5.1(3) + the factorisation (6.22)): the tail of the family is controlled by the continuous
  analogue of the multipliers.

* `Work.BourgainPlan.Thm52.varRho_small_scales` — KMSZ **(5.4)**: the `2`-variation over the
  dyadic window `[0, 2^κ]` is controlled by `(κ+1)·A` (the `log N` of Theorem 5.2 is the number
  `κ+1` of dyadic levels), via the Rademacher–Menshov inequality (condition (2) of Definition 5.1,
  landed here as `varELpNormLeRho`) and the Marcinkiewicz–Zygmund theorem
  (`mz_square_function`, which is the Khintchine step).

* `Work.BourgainPlan.Thm52.thm52` — KMSZ Theorem 5.2, assembled from the small-scale step, the
  splitting property (condition (1), landed as `varRhoSplitting`/`varRho_tail_glue`) and the
  large-scale input.

The consumer of this chapter is `Work.BourgainPlan.Maximal.KMSZMajorArcStatement` (KMSZ §6.3),
whose inequality (6.20) is "an application of Theorem 5.2", carrying the constants
`A_q, B_q` of (6.21).
-/

open MeasureTheory Finset
open scoped BigOperators ENNReal

set_option autoImplicit false

namespace Work.BourgainPlan.Thm52

noncomputable section

/-- The `ℓᵖ(ℤ)`-norm (`Measure.count`) of a complex-valued sequence, as an `ℝ≥0∞`. -/
def lpNorm (p : ℝ) (f : ℤ → ℂ) : ℝ≥0∞ := eLpNorm f (ENNReal.ofReal p) Measure.count

/-- The `p`-th power of the `ℓᵖ(ℤ)`-norm, in `ℝ≥0∞` form: `∫⁻ |f|^p d#`. -/
def lpPow (p : ℝ) (f : ℤ → ℂ) : ℝ≥0∞ := ∫⁻ y : ℤ, ‖f y‖ₑ ^ p ∂Measure.count

/-- **The level-`l` dyadic block square function of a family** `a : ℕ → ℤ → ℂ` over the dyadic
window `[0, 2^n]`: `(Σ_{m < 2^{n−l}} ‖a ((m+1)2^l) − a (m2^l)‖²)^{1/2}`.  This is the `ℝ≥0∞`-valued
form of `Work.BourgainPlan.Maximal.rmLevel`. -/
def levelSq (n l : ℕ) (a : ℕ → ℤ → ℂ) (y : ℤ) : ℝ≥0∞ :=
  (∑ m ∈ Finset.range (2 ^ (n - l)), ‖a ((m + 1) * 2 ^ l) y - a (m * 2 ^ l) y‖ₑ ^ (2 : ℝ))
    ^ ((1 : ℝ) / 2)

/-- **The uniform-in-signs bound for the lacunary differences of a family of operators** (the
hypothesis produced by the Ionescu–Wainger multiplier theorem, KMSZ Theorem 1.9; here stated for the
`κ`-th dyadic window `[0, 2^κ]`).

At level `l ≤ κ` the differences are `T ((m+1)2^l) − T (m 2^l)`; the hypothesis says that *every*
signed combination of them is bounded on `ℓᵖ(ℤ)` by `A`.  In the Ionescu–Wainger application
`T n = T_ℤ[J|m_n K]` and `Σ_m ω_m (T ((m+1)2^l) − T (m2^l))` is the multiplier with symbol
`Σ_m ω_m (m_{(m+1)2^l} − m_{m 2^l})`, whose continuous multiplier norm is `≤ A_{2r}` (KMSZ (6.21)),
so the bound is exactly "Theorem 1.9 with the constant `A_{2r}`". -/
def SignedDiffBound (p : ℝ) (T : ℕ → (ℤ → ℂ) → (ℤ → ℂ)) (n : ℕ) (A : ℝ) : Prop :=
  ∀ (l : ℕ), l ≤ n → ∀ (ω : Fin (2 ^ (n - l)) → Bool) (f : ℤ → ℂ),
    (∫⁻ y : ℤ, ‖∑ m : Fin (2 ^ (n - l)), (if ω m then (1 : ℂ) else -1)
        * (T (((m : ℕ) + 1) * 2 ^ l) f y - T ((m : ℕ) * 2 ^ l) f y)‖ₑ ^ p ∂Measure.count)
      ≤ ENNReal.ofReal (A ^ p) * lpPow p f

/-- **The large-scale (sampling-principle) bound** (KMSZ Definition 5.1(3) and (5.5)): the tail
variation of the family from the threshold `2^κ` on is bounded by `B` times the `ℓᵖ` norm of the
input.  In KMSZ's proof this is obtained from the factorisation (6.22)
`T_ℤ[J_G|m_nK] = T_ℤ[J_1|m_nK_Q] ∘ T_ℤ[J_G|η_{≤−5rN}K]`, the sampling principle (their
Definition 5.1(3)) for the seminorm `S`, and Theorem 1.9 for the second factor; the constant is
`C₃·B_p` of (5.5). -/
def LargeScaleBound (p : ℝ) (T : ℕ → (ℤ → ℂ) → (ℤ → ℂ)) (κ : ℕ) (B : ℝ) : Prop :=
  ∀ f : ℤ → ℂ,
    eLpNorm (fun y : ℤ => Work.BourgainPlan.Maximal.varRhoFrom 2 κ (fun n => T n f y))
      (ENNReal.ofReal p) Measure.count
      ≤ ENNReal.ofReal B * lpNorm p f

/-- **The single-scale bound** (the base term of the Rademacher–Menshov splitting, i.e. KMSZ (6.11)
itself for the finitely many small scales). -/
def SingleScaleBound (p : ℝ) (T : ℕ → (ℤ → ℂ) → (ℤ → ℂ)) (κ : ℕ) (A : ℝ) : Prop :=
  ∀ (i : ℕ), i ≤ 2 ^ κ → ∀ f : ℤ → ℂ,
    eLpNorm (fun y : ℤ => ‖T i f y‖ₑ) (ENNReal.ofReal p) Measure.count
      ≤ ENNReal.ofReal A * lpNorm p f

end

end Work.BourgainPlan.Thm52
