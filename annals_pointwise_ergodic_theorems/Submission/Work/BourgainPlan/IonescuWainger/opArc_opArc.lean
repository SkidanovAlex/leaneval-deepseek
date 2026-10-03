import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.OpArcDefs

namespace Work.BourgainPlan.IonescuWainger

open MeasureTheory
open scoped lp BigOperators ENNReal

noncomputable section

/-- **The pointwise computation behind the insertion of a wider bump.**  If the symbol `m` vanishes
outside the ball of radius `ε`, `φ` vanishes outside the ball of radius `η` and equals `1` on the
ball of radius `ε`, and the arc set `E` is `δ`-separated with `ε + η < δ`, then at *every* point `ξ`

`(Σ_{β∈E} m(·−β))(ξ) · (Σ_{β∈E} φ(·−β))(ξ) = (Σ_{β∈E} m(·−β))(ξ)`.

Indeed, a term `m(ξ−β) ≠ 0` forces `‖ξ−β‖ ≤ ε`; every other translate `φ(ξ−β')`, `β' ≠ β`, must
then vanish, since otherwise `‖β−β'‖ ≤ ‖ξ−β‖ + ‖ξ−β'‖ ≤ ε + η < δ`, contradicting the separation
of the arcs.  So the inner sum `Σ_{β'} φ(ξ−β')` collapses to `φ(ξ−β) = 1`. -/
theorem arcSymbol_mul_eq {m φ : Circle → ℂ} {E : Finset Circle} {ε η δ : ℝ}
    (hmsupp : ∀ ξ, ε < ‖ξ‖ → m ξ = 0)
    (hφsupp : ∀ ξ, η < ‖ξ‖ → φ ξ = 0)
    (hφone : ∀ ξ, ‖ξ‖ ≤ ε → φ ξ = 1)
    (hsep : ∀ β ∈ E, ∀ β' ∈ E, β ≠ β' → δ ≤ ‖β - β'‖) (hδε : ε + η < δ) (ξ : Circle) :
    arcSymbol m E ξ * arcSymbol φ E ξ = arcSymbol m E ξ := by
  have key : ∀ β ∈ E, m (ξ - β) * (∑ β' ∈ E, φ (ξ - β')) = m (ξ - β) := by
    intro β hβ
    by_cases hm0 : m (ξ - β) = 0
    · rw [hm0, zero_mul]
    · have h1 : ‖ξ - β‖ ≤ ε := le_of_not_gt fun hlt => hm0 (hmsupp _ hlt)
      have hφeq : ∀ β' ∈ E, φ (ξ - β') = if β' = β then 1 else 0 := by
        intro β' hβ'
        by_cases h : β' = β
        · rw [if_pos h]; rw [h]; exact hφone _ h1
        · rw [if_neg h]
          apply hφsupp
          by_contra hcon
          push Not at hcon
          have hle : ‖β - β'‖ ≤ ε + η := by
            have hsub : β - β' = (ξ - β') - (ξ - β) := by abel
            rw [hsub]; linarith [norm_sub_le (ξ - β') (ξ - β), hcon]
          linarith [hsep β hβ β' hβ' (Ne.symm h)]
      rw [Finset.sum_congr rfl hφeq, Finset.sum_ite_eq']
      rw [if_pos hβ, mul_one]
  calc arcSymbol m E ξ * arcSymbol φ E ξ
      = (∑ β ∈ E, m (ξ - β)) * (∑ β' ∈ E, φ (ξ - β')) := by
        rw [arcSymbol_apply, arcSymbol_apply]
    _ = ∑ β ∈ E, m (ξ - β) * (∑ β' ∈ E, φ (ξ - β')) := Finset.sum_mul _ _ _
    _ = ∑ β ∈ E, m (ξ - β) := Finset.sum_congr rfl key
    _ = arcSymbol m E ξ := by rw [arcSymbol_apply]

/-- **The `L^∞`-action on `L²` is insensitive to an a.e.-idempotent symbol.**  If
`(Φ·Ψ)(ξ) = Φ(ξ)` for a.e. `ξ`, then `Φ • (Ψ • G) = Φ • G` in `L²`.  This is the associativity
`Φ • (Ψ • G) = (Φ·Ψ) • G` of the pointwise action, combined with the hypothesis. -/
theorem Lp_smul_smul_eq_of_ae (Φ Ψ : Lp ℂ ⊤ (AddCircle.haarAddCircle (T := 1)))
    (G : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1)))
    (h : ∀ᵐ ξ ∂(AddCircle.haarAddCircle (T := 1)),
        (Φ : Circle → ℂ) ξ * (Ψ : Circle → ℂ) ξ = (Φ : Circle → ℂ) ξ) :
    Φ • (Ψ • G) = Φ • G := by
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_lpSMul (p := ⊤) (q := 2) (r := 2) Φ (Ψ • G),
    Lp.coeFn_lpSMul (p := ⊤) (q := 2) (r := 2) Ψ G,
    Lp.coeFn_lpSMul (p := ⊤) (q := 2) (r := 2) Φ G, h] with ξ h1 h2 h3 h4
  simp only [h1, h2, h3, smul_eq_mul, Pi.mul_apply]
  rw [← mul_assoc, h4]

/-- **Multiplicativity of the arc multipliers on the Fourier side.**  If the product of two symbols
`Φ`, `Ψ` agrees a.e. with `Φ`, then inserting the multiplier `opMul Ψ` before `opMul Φ` does
nothing: `opMul Φ (opMul Ψ f) = opMul Φ f`. -/
theorem opMul_opMul (Φ Ψ : Lp ℂ ⊤ (AddCircle.haarAddCircle (T := 1)))
    (f : ℤ → ℂ) (hf : Memℓp f 2)
    (h : ∀ᵐ ξ ∂(AddCircle.haarAddCircle (T := 1)),
        (Φ : Circle → ℂ) ξ * (Ψ : Circle → ℂ) ξ = (Φ : Circle → ℂ) ξ) :
    opMul Φ (opMul Ψ f hf) (opMul_memℓp Ψ f hf) = opMul Φ f hf := by
  funext n
  rw [opMul_apply, opMul_apply]
  congr 1
  show Φ • ftLp (opMul Ψ f hf) (opMul_memℓp Ψ f hf) = Φ • ftLp f hf
  rw [ftLp_opMul Ψ f hf]
  exact Lp_smul_smul_eq_of_ae Φ Ψ (ftLp f hf) h

/-- **The insertion of a wider bump into an arc multiplier** (Tao, arXiv:2008.05066, proof of
`main`: "we may use the disjointness of the arcs to factor
`Op_{m;α+Σ_{A₀}}f = Op_{m;α+Σ_{A₀}} Op_{φ;α+Σ_{A₀}}f`"): if the arc set `E` is `δ`-separated, the
symbol `m` vanishes outside the ball of radius `ε`, and the symbol `φ` equals `1` on the ball of
radius `ε` while vanishing outside the ball of radius `η`, with `ε + η < δ`, then

`Op_{m;E} (Op_{φ;E} f) = Op_{m;E} f`   (`opArc m E ∘ opArc φ E = opArc m E`).

Indeed, for a nonzero term of `(Σ_{β∈E}m(·−β))·(Σ_{β∈E}φ(·−β))` at `ξ` one needs `‖ξ−β‖ ≤ ε` and
`‖ξ−β'‖ ≤ η`, hence `‖β−β'‖ ≤ ε+η < δ` and `β = β'`; and `m(ξ−β) ≠ 0` forces `‖ξ−β‖ ≤ ε`, where
`φ ≡ 1`.  So the product of the two symbols is `Σ_{β∈E}m(·−β)` itself.

This is the step that lets the `opArc_l2_endpoint` estimate (for the wide bump `φ`) be combined with
the `msw` sampling principle and the Marcinkiewicz–Zygmund step (for the narrow symbol `m`) in the
proof of the Ionescu–Wainger multiplier result.  Proof route: the general multiplicativity
`opArc ψ (opArc φ f) = opMul (arcSymbolLp (ψ·φ) …) f` on the Fourier side (via `ftLp_opMul` and the
associativity of the `Lp ℂ ⊤`-action on `Lp ℂ 2`), together with the pointwise-support computation
`arcSymbol m E · arcSymbol φ E = arcSymbol m E` (hence the `a.e.` equality of the symbols in
`Lp ℂ ⊤`). -/
theorem opArc_opArc {m φ : Work.BourgainPlan.IonescuWainger.Circle → ℂ}
    {hm : MeasureTheory.MemLp m ⊤ (AddCircle.haarAddCircle (T := 1))}
    {hφ : MeasureTheory.MemLp φ ⊤ (AddCircle.haarAddCircle (T := 1))}
    {E : Finset Work.BourgainPlan.IonescuWainger.Circle} {ε η δ : ℝ}
    (hmsupp : ∀ ξ, ε < ‖ξ‖ → m ξ = 0)
    (hφsupp : ∀ ξ, η < ‖ξ‖ → φ ξ = 0)
    (hφone : ∀ ξ, ‖ξ‖ ≤ ε → φ ξ = 1)
    (hsep : ∀ β ∈ E, ∀ β' ∈ E, β ≠ β' → δ ≤ ‖β - β'‖) (hδε : ε + η < δ)
    (f : ℤ → ℂ) (hf : Memℓp f 2) :
    Work.BourgainPlan.IonescuWainger.opArc m hm E
        (Work.BourgainPlan.IonescuWainger.opArc φ hφ E f hf)
        (Work.BourgainPlan.IonescuWainger.opMul_memℓp
          (Work.BourgainPlan.IonescuWainger.arcSymbolLp φ hφ E) f hf)
      = Work.BourgainPlan.IonescuWainger.opArc m hm E f hf := by
  have hae : ∀ᵐ ξ ∂(AddCircle.haarAddCircle (T := 1)),
      (arcSymbolLp m hm E : Circle → ℂ) ξ * (arcSymbolLp φ hφ E : Circle → ℂ) ξ
        = (arcSymbolLp m hm E : Circle → ℂ) ξ := by
    filter_upwards [arcSymbolLp_coeFn m hm E, arcSymbolLp_coeFn φ hφ E] with ξ hm' hφ'
    rw [hm', hφ', arcSymbol_mul_eq hmsupp hφsupp hφone hsep hδε ξ]
  exact opMul_opMul (arcSymbolLp m hm E) (arcSymbolLp φ hφ E) f hf hae

end

end Work.BourgainPlan.IonescuWainger
