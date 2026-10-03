/-
# The exact-height single-scale model approximation of the low case of area A6

Target: `Work.KMTPlan.A6.ModApproxErrCoreExact`: the *single-scale* estimate for the
model-approximation error `modApproxErr = mainPartTuple − mdlPart` of the low case
(`k₁ = 0 ∨ k₂ = 0`),

  `‖ modApproxErr ρ P C₀ a f g l₁ l₂ k₁ k₂ n ‖_{ℓ¹(ℤ)}
     ≤ C(Λ) · modelWeight A ρ l₁ l₂ k₁ k₂ · ⌊a n⌋⁻¹ · ‖f‖₂ ‖g‖₂`,

for every `Λ`-lacunary `a` with `a n ≥ 1` and all `f g : ℤ → ℂ` in `ℓ²(ℤ)` (Krause--Mirek--Tao,
Proposition `mod-approx`, composed with the functional calculus `bn-ident` and the
integration-by-parts identity `integ-ident`).

## The route (see also `NOTES_ModApproxErrCoreExact_ROUTE.md`)

Off the condition

  `CoreCond = inIndexSet C₀ (max l₁ l₂) k₁ k₂ ⌊a n⌋ ∧ splitCut ρ L < ⌊a n⌋ ∧ mainRegime ρ k₁ k₂ ⌊a n⌋`

both `mainPartTuple` and `mdlPart` vanish (they are defined by the *same* `if`-test), so the
estimate is trivial there; this file records that (`modApproxErr_eq_zero_of_not_core`).

The whole content is on `CoreCond`, where the error is a *bilinear convolution*
`bilinOp (K₁ - K₂) f g` with explicit kernels `K₁` (the concrete halved average
`Ã_N(F_N f, G_N g)` of the §5 pieces) and `K₂` (the §6 model operator
`∫_{1/2}^1 B^{l₁,l₂,m_Ẑ}_{m_*}(T^{l₁}_{φ_{N,t}} F, T^{l₂}_{φ̃_{N,t}} G) dt`), and the two kernels are
compared by decomposing both in the *arithmetic fibres* `α ∈ (ℚ/ℤ)_{≤l}`: on the fibre
`(α₁,α₂)`, `K₁` is the discrete average of the smooth factors times the periodic phase
`n ↦ e(α₁n+α₂P(n))`, and `K₂` is `m_Ẑ(α₁,α₂)` times the *continuous* average of the same smooth
factors.  The difference of the two symbols is exactly the symbol difference

  `M₀ = E_{n ∈ [N]} e(α₁n+α₂P(n)) e(ξ₁n+ξ₂P(n)) 1_{n>N/2} - m_Ẑ(α₁,α₂) m̃_{N,ℝ}(ξ₁,ξ₂)`

of `Work.KMTAreas.A7.M0`, whose size and `ξ`-derivatives are estimated by
`Work.A7.M0SharpBound` (`j = 0`) and `Work.A7.ModelApproxCore_M0_deriv_bound` (`j₁,j₂ ≤ 2`); the
conversion of those symbol bounds into the `ℓ¹(ℤ²)`-mass bound of `K₁ - K₂` is the paper's Lemma
`crude-mult`(ii) with `r₁ = ⌊a n⌋⁻¹`, `r₂ = ⌊a n⌋^{-d}`, together with the fibre decompositions
(`iwKernel_iwSymbolSet`), the de Leeuw unfolding `MSW_periodize_integral`, the non-aliasing of the
arithmetic frequencies (killing the cross fibres and reducing the `≤ l` arithmetic kernel to the
exact-height one), the `m_*`-sliver estimate and the flatness of the cutoff `η` (which makes the
`periodize η_{≤0}` factor of `mdlF` equal to `1` on the frequency window).  Finally the weight
arithmetic absorbs the factors `2^{O(2^{ρl})}`, `q²` and `2^{O(L)}` into
`modelWeight A ρ l₁ l₂ k₁ k₂`, because here the exponent `A` is allowed to depend on `ρ`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.ModelApproxDefs
import Submission.Work.KMTPlan.A6.MaeKernels

namespace Work.KMTPlan.A6

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.EndVar
open Work.KMTContract
open Work.KMTAreas.A7

noncomputable section

/-- **The core condition of the single-scale model approximation**: the same conjunction that
appears as the `if`-test of both `mainPartTuple` and `mdlPart` (`Work.KMTAreas.A7.Large.Defs`):
the scale `N = ⌊a n⌋` lies in the index set `I^{max l₁ l₂, k₁, k₂}`, is large
(`N > splitCut ρ (max (max l₁ l₂) (max k₁ k₂))`) and lies in the main regime `k + 2u ≤ Log N`.
(This was `Work.KMTAreas.A7.CoreCond` before the A7 area was restructured.) -/
def coreCond (ρ : ℝ) (C₀ : ℕ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ) (n : ℕ) : Prop :=
  inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ) (Nat.floor (a n)) ∧
    splitCut ρ (max (max l₁ l₂) (max k₁ k₂)) < Nat.floor (a n) ∧
    mainRegime ρ k₁ k₂ (Nat.floor (a n))

/-- Unfolding of `mainPartTuple` on the core condition. -/
theorem mainPartTuple_apply_of_core (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → NNReal)
    (f g : ℤ → ℂ) (l₁ l₂ k₁ k₂ n : ℕ) (x : ℤ)
    (h : coreCond ρ C₀ a l₁ l₂ k₁ k₂ n) :
    mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
      = varpPiece (kmtPj ρ) P P.natDegree (a n) f g l₁ l₂ k₁ k₂ x := by
  rw [mainPartTuple]
  exact if_pos h

/-- **Off the core condition the model-approximation error vanishes.**  `mainPartTuple` and
`mdlPart` are defined by the *same* `if`-test (the conjunction `coreCond`), so the error
`mainPartTuple − mdlPart` is identically zero wherever the condition fails. -/
theorem modApproxErr_eq_zero_of_not_core (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → NNReal)
    (f g : ℤ → ℂ) (l₁ l₂ k₁ k₂ n : ℕ)
    (h : ¬ coreCond ρ C₀ a l₁ l₂ k₁ k₂ n) :
    modApproxErr ρ P C₀ a f g l₁ l₂ k₁ k₂ n = 0 := by
  funext x
  have h₁ : mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x = 0 := by
    rw [mainPartTuple]; exact if_neg h
  have h₂ : mdlPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x = 0 := by
    rw [mdlPart]; exact if_neg h
  simp only [modApproxErr, Pi.sub_apply, h₁, h₂, sub_zero]
  rfl

/-- **The single-scale model-approximation estimate of the low case (the §6 crux).**

There are `ρ₀ > 0` and, for every `ρ ∈ (0,ρ₀]`, an exponent `A ≥ 0` and a constant
`C : ℝ≥0 → ℝ≥0` such that for every `Λ`-lacunary scale sequence `a` with `a n ≥ 1`, every
quadruple `(l₁,l₂,k₁,k₂)` with `k₁ = 0` or `k₂ = 0`, every `f, g ∈ ℓ²(ℤ)` and every `n`,

  `‖ modApproxErr ρ P C₀ a f g l₁ l₂ k₁ k₂ n ‖_{ℓ¹(ℤ)}
     ≤ C(Λ) · modelWeight A ρ l₁ l₂ k₁ k₂ · ⌊a n⌋⁻¹ · ‖f‖₂ ‖g‖₂`.

Off the core condition both tuples vanish (`modApproxErr_eq_zero_of_not_core`), so the whole
content is the model approximation on the core scales; see
`NOTES_ModApproxErrCoreExact_ROUTE.md` for the route. -/
theorem ModApproxErrCoreExact (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (C₀ : ℕ) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ A : ℝ, 0 ≤ A ∧ ∃ C : NNReal → NNReal,
      ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
        1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
        (k₁ = 0 ∨ k₂ = 0) →
        MeasureTheory.MemLp f 2 MeasureTheory.Measure.count →
        MeasureTheory.MemLp g 2 MeasureTheory.Measure.count → ∀ n : ℕ,
        MeasureTheory.eLpNorm (fun x : ℤ =>
            Work.KMTPlan.A6.modApproxErr ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
          1 MeasureTheory.Measure.count
          ≤ (C Λ : ENNReal) * ENNReal.ofReal (Work.KMTAreas.A7.modelWeight A ρ l₁ l₂ k₁ k₂)
              * ENNReal.ofReal (((Nat.floor (a n) : ℕ) : ℝ)⁻¹)
              * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
              * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by sorry

end

end Work.KMTPlan.A6
