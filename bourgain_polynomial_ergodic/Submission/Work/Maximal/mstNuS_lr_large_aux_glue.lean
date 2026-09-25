import Mathlib
import Submission.Work.Maximal.mstWide_defs
import Submission.Work.Maximal.mstNuS_sub_mstWideModel_lr_tail
import Submission.Work.Maximal.mstWideModel_lr_maximal
import Submission.Work.Maximal.latfix_mstWideModel_lr_maximal
import Submission.Work.Maximal.latfix_memLp_mstWideModel
import Submission.Work.Maximal.latglue_basic
import Submission.Work.Maximal.latglue_diff
import Submission.Work.Maximal.mstNuS_sub_mstWideModel_lr_tail_all
import Submission.Work.Maximal.latglue_core

set_option autoImplicit false

namespace Work.Maximal

/-- **The glue of the large-scale `ℓʳ` level estimate**, i.e. the statement of
`Work.Maximal.mstNuS_lr_large_aux` with the **corrected** sampling-principle comparison `hLattice`
(`Continuous H` included, at the same exponent `r` as the theorem — this is the shape of the landed
`Work.BourgainPlan.Maximal.mstLatticePrinciple`) left as an explicit hypothesis.

Proof: `sup_{k ≥ 2^{κ_s}} |A_k g| ≤ sup_{k ≥ 2^{κ_s}} |(A_k − Ω_k) g| + sup_k |Ω_k g|`; the second
is `mstWideModel_lr_maximal` (applied with `hLattice`, which holds for *every* `s`), the first is
`mstNuS_sub_mstWideModel_lr_tail` for `s ≥ s₀`; for the finitely many `s < s₀` the difference is
handled with `s`-dependent constants (the margin `{min(2^{−s(d−χ)}/2, 1/(2c_s)) ≤ |θ|}` is fixed for
fixed `s`, so `Σ_{k ≥ 2^{κ_s}} sup_θ |Φ_{2^k}(θ)(η_s−ϱ_s)(θ)| < ∞`), and the finite maximum is
absorbed into `C`.  The `MemLp` data `hΩml`/`hϱml` required by `mstWideModel_lr_maximal` are supplied
from the continuity of the wide bump/model (e.g. `memLp_scaled_bump` +
`memLp_star_mstProf_mul_mstWideBump` + `MemLp` closure under finite sums/products). -/
-- NOTE ON THE STATEMENT AS DELIVERED.  The requested text had `hLattice` *before* the binder
-- `{r : ℝ}`, so the `r` occurring inside `hLattice` was not the theorem's exponent: with the
-- package's `autoImplicit = false` the statement does not elaborate at all, and with
-- `autoImplicit = true` Lean introduces a *separate* implicit variable for it (typed `ℕ` by
-- instance search), i.e. `hLattice` becomes a sampling principle at an unrelated natural exponent
-- and gives no information about the conclusion, whose exponent is the theorem's `r` with
-- `1 < r < 2`.  The binder `{r : ℝ}` has therefore been moved to the front (everything else in the
-- statement is verbatim as delivered): this is the statement the docstring describes ("at the same
-- exponent `r` as the theorem") and the only form that is provable from the hypotheses, since the
-- narrow-to-wide replacement needs the sampling principle at the very exponent `r` of the
-- conclusion.  The whole glue is proved below.
theorem mstNuS_lr_large_aux_glue
    {r : ℝ}
    (hLattice : ∃ C : ℝ, 0 < C ∧ ∀ (H : ℝ → ℂ) (δ : ℝ), 0 < δ → Continuous H →
      MeasureTheory.Integrable H →
      (∀ ξ : ℝ, δ < |ξ| → FourierTransform.fourier H ξ = 0) →
      ∀ (Q : ℕ), 1 ≤ Q → δ * (Q : ℝ) ≤ 1 / 4 → ∀ (m : ℤ) (c : ℝ),
        (∑' x : ℤ, (Work.Maximal.mstHlMax (fun y : ℝ => ENNReal.ofReal ‖H y‖)
            ((Q : ℝ) * (x : ℝ) + (m : ℝ) - c)) ^ r)
          ≤ ENNReal.ofReal (C ^ r) *
            ∑' x : ℤ, ENNReal.ofReal (‖H ((Q : ℝ) * (x : ℝ) + (m : ℝ))‖ ^ r))
    (hΘ : Work.BourgainPlan.Maximal.MSTThetaBound)
    (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (hc : 0 < P.leadingCoeff)
    (l : ℕ) (hl : 1 ≤ l) {χ : ℝ} (hχ0 : 0 < χ) (hχ1 : χ < 1 / 10)
    (η : ℝ → ℂ) (M : ℝ) (hM : 0 < M) (hηc : ContDiff ℝ 2 η)
    (hηbd : ∀ x : ℝ, ‖η x‖ ≤ M)
    (hder1 : ∀ x : ℝ, |x| * ‖deriv η x‖ ≤ M)
    (hder2 : ∀ x : ℝ, |x| ^ 2 * ‖iteratedDeriv 2 η x‖ ≤ M)
    (hηsup : ∀ x : ℝ, 1 / 2 ≤ |x| → η x = 0)
    {δ : ℝ} (hδ : 0 < δ) (D : ℝ) (hD : 0 < D)
    (hGauss : ∀ (s : ℕ) (β : Work.BourgainPlan.IonescuWainger.Circle),
      β ∈ Work.BourgainPlan.Maximal.mstU l (s + 1) \ Work.BourgainPlan.Maximal.mstU l s →
      ‖Work.BourgainPlan.Maximal.mstG P β‖ ≤ D * ((s : ℝ) + 1) ^ (-(δ * l)))
    (hνsml : ∀ n s : ℕ, MeasureTheory.MemLp
      (Work.BourgainPlan.Maximal.mstNuS P l P.natDegree χ η n s) ⊤
      (AddCircle.haarAddCircle (T := 1)))
    (hr : 1 < r) (hr2 : r < 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℕ, ∀ g : ℤ →₀ ℂ,
      MeasureTheory.eLpNorm (fun m : ℤ => (⨆ k : ℕ,
          ⨆ (_ : 2 ^ (Work.BourgainPlan.Maximal.mstKappa P s) ≤ k),
          ‖Work.BourgainPlan.IonescuWainger.opMul
            (Work.BourgainPlan.Maximal.mstNuSCls P l P.natDegree χ η k s (hνsml k s))
            (⇑g) (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) m‖ₑ))
          (ENNReal.ofReal r) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C * Real.log ((s : ℝ) + 2))
          * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal r) MeasureTheory.Measure.count := by
  have hϱml : ∀ s : ℕ, MeasureTheory.MemLp (mstWideBump P χ η s) ⊤
      (AddCircle.haarAddCircle (T := 1)) :=
    fun s => (mstWideBump_memLp_and_narrow P χ η hηc.continuous hηsup s).1
  have hΩml : ∀ k s : ℕ, MeasureTheory.MemLp (mstWideModel P l χ η k s) ⊤
      (AddCircle.haarAddCircle (T := 1)) :=
    fun k s => memLp_mstWideModel P l χ η hηc.continuous hηsup k s
  obtain ⟨CΔ, hΔpos, hΔ⟩ := mstNuS_sub_mstWideModel_lr_tail_all P hd hc l hl hχ0 hχ1 η hηc
    hηsup hδ D hD hGauss hνsml hΩml hr hr2
  exact glue_core hLattice hΘ P hd hc l hl hχ0 hχ1 η M hM hηc hηbd hder1 hder2 hηsup hδ D hD
    hGauss hνsml hϱml hΩml ⟨CΔ, hΔpos, hΔ⟩ hr hr2

end Work.Maximal
