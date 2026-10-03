/-
# The `ℓ¹(ℤ²)`-mass bound for the §6 model-approximation error of the small scales (Area A7)

Target: `Work.KMTAreas.A7.smallKernelMass_le`: the `ℓ¹(ℤ²)` mass of the kernel of the §6
model-approximation error of the small scales,

`smallKconc ρ P l₁ l₂ k₁ k₂ N − smallKmod ρ P l₁ l₂ k₁ k₂ N`,
is `≤ K(Λ) · 2^{C·max(2^{ρL},L)} · N⁻¹` on the small-scale condition `smallCond`
(`N = ⌊a n⌋`, `L = smallL l₁ l₂ k₁ k₂`).

This is Krause--Mirek--Tao, *Pointwise ergodic theorems for non-conventional bilinear polynomial
averages*, Ann. of Math. 195 (3) 2022, Proposition `mod-approx` (§6) composed with the functional
calculus `bn-ident`, in the *kernel-mass* form.  The kernel-mass form is what the surrounding
chain needs: `smallDiff_eq_bilinOp` identifies `smallMainPart − smallModelTuple` with
`bilinOp (smallKconc − smallKmod) f g`, and `Work.KMTAreas.A7.BilinOpLp` turns the mass bound into
the `ℓ^p` bound of `SmallSingleScaleB`.

## The objects (`Submission/Work/KMTAreas/A7/{SmallDefs,SmallModApprox,ModelOps}.lean`)

`N := Nat.floor (a n)`, `d := P.natDegree`, `L := smallL l₁ l₂ k₁ k₂`, `u := uScale ρ L`,
`A_i := diffFreqs ρ l_i` (the *exact* IW heights `(ℚ/ℤ)_{l_i} = (ℚ/ℤ)_{≤l_i} \ (ℚ/ℤ)_{≤l_i-1}`),
`φ_i = varphiN N k₁`, `φ̃_i = varphitildeN d N k₂`, `φ^t := varphiNt N k₁ t`, `φ̃^t` similarly,
`m_* := mStarF u`, `m̃_* := mStargF d u`, and

* `tmKernel ρ l ψ = iwKernel (iwSymbolSet A_l (periodize ψ))`
  (`= (∑_{α ∈ A_l} e(-jα))·cw ψ j`, `Work.KMTPlan.A6.IwKernelArithChar`);
* `smallKconc = kernComp (khalf N P) (tmKernel ρ l₁ φ) (tmKernel ρ l₂ φ̃)`;
* `smallKmod = ∫_{1/2}^1 kernComp (smallArithKernel ⊗ cw m_* ⊗ cw m̃_*) (tmKernel ρ l₁ φ^t)
  (tmKernel ρ l₂ φ̃^t) dt`;
* `smKernMass K = ∑'_{p : ℤ×ℤ} ‖K p.1 p.2‖ₑ`.

## The route (this is the §6 crux; the pieces below are the ones still to be built)

Write `𝕋 := ℝ/ℤ` (`Work.Analysis.IonescuWainger.Circle`, measure `AddCircle.haarAddCircle`) and let
`coeff F a b := ∫_{θ₁}∫_{θ₂} F θ₁ θ₂ · fourier(-a) θ₁ · fourier(-b) θ₂` be the double Fourier
coefficient of `F : 𝕋² → ℂ` (so that `iwKernel m j = ∫_θ (fourier (-j) θ)·m θ` *is* this transform
in one variable).

**(K1) The two kernels are double Fourier coefficients of explicit symbols.**
Setting `Ψ_i := iwSymbolSet A_i (periodize φ_i)`, `Φ_i := periodize φ_i`,
`avg(θ) := N⁻¹ ∑_{m ∈ Ioc (N/2) N} fourier(m) θ₁ · fourier(P(m)) θ₂`,
`m̃(ξ₁,ξ₂) := mTilde P N ξ₁ ξ₂` (evaluated at canonical representatives, via the
`varphiNt`-modulation identity `periodize (varphiNt N k t) ξ = ee (N t ξ₀) · periodize (varphiN N k) ξ`), and
`Arith(θ) := ∑_{α₁∈A₁}∑_{α₂∈A₂} mZ P (arithQ ρ (max l₁ l₂)) α₁ α₂ ·
  periodize (mStarF u) (θ₁-α₁) · periodize (mStargF d u) (θ₂-α₂)`
(the Poisson/fibre collapse `∑_j cw m_* j · e(j·) = periodize m_*` of `type-B`,
`Work.KMTPlan.A6.PoissonModulatedZero`, `MdlCwIntegIdent`), one has

  `smallKconc ρ P l₁ l₂ k₁ k₂ N = coeff (fun θ₁ θ₂ => Ψ₁ θ₁ * Ψ₂ θ₂ * avg θ₁ θ₂)`
  `smallKmod  ρ P l₁ l₂ k₁ k₂ N
     = coeff (fun θ₁ θ₂ => (∑_{β} Φ₁(θ₁-β₁)·Φ₂(θ₂-β₂)·m̃(θ₁-β₁,θ₂-β₂)) · Arith θ₁ θ₂)`

(the `m̃`-factor sits *inside* the sum over the arithmetic frequencies, because
`∫_t Ψ₁^t(θ₁)Ψ₂^t(θ₂) dt = ∑_β Φ₁(θ₁-β₁)Φ₂(θ₂-β₂)m̃(θ₁-β₁,θ₂-β₂)`; only
`Φ₁⊗Φ₂` — not `Ψ₁⊗Ψ₂` — factors out of the `t`-integral; see the definition `modSymb` below).
The Poisson/fibre collapse `∑_j cw m_* j · e(j·) = periodize m_*` is used for `Arith`.

**CORRECTION (found by a sub-agent attacking `smallKmod_eq_coeff`, 2026-09):** the symbol
`modSymb` *as defined below* is NOT the model symbol, and `smallKmod_eq_coeff` is FALSE with it.
`periodize (varphiNt N k t) γ = ∑_{m∈ℤ} φ_N(γ₀+m)·ee (N t (γ₀+m))` and `ee (N t m) ≠ 1` for
non-integer `N t`, so the `t`-integral of the symbol of the modulated piece sums `mTilde` over the
whole *lift*:
  `∫_{1/2}^1 Ψ₁^t(θ₁)Ψ₂^t(θ₂) dt = ∑_{β}∑_{m₁,m₂} φ_N((θ₁-β₁)₀+m₁)φ̃_N((θ₂-β₂)₀+m₂)
      · mTilde P N ((θ₁-β₁)₀+m₁) ((θ₂-β₂)₀+m₂)`
(the `m`-sum is finite: the bumps are supported in `|ξ| ≤ 2^{k_i+1}/N`).  `modSymb` below keeps
only the `m = 0` term (`mTilde (fract (θ-β))`), which is wrong because `mTilde` is not
1-periodic (unit test: `P = 0`, `N = 1`: `mTilde 0 1 0 0 = 1/2` but `mTilde 0 1 1 0 = -i/π`).
**A correct `modSymb` must carry this lift-sum**, and (K2)/(K4) must be re-derived with it.  The
`M0` identity itself is untouched: when `2^{k_i+1}/N < 1/2` only `m = 0` survives on the support of
the bump, so the `M0`-analysis applies; in the complementary regime the surviving `m ≠ 0` terms
must be estimated separately (they are supported where the bump wraps around the circle, and there
`|mTilde|` is controlled by the oscillation of `ξ ↦ e(ξ N t)`).

**(K2) The algebraic collapse.** With `Σ₁ := Ψ₁·Ψ₂·avg`, `Σ₂ := Φ₁·Φ₂·m̃·Arith` and
`G_β(θ) := avg(θ) − Arith(θ)·m̃(θ-β)` (`β ∈ A₁×A₂`), the *identity*

  `Σ₁ − Σ₂ = ∑_{β₁∈A₁}∑_{β₂∈A₂} Φ₁(θ₁-β₁)·Φ₂(θ₂-β₂)·G_β(θ)`

holds (only the definitions of `Ψ_i`, `Σ_i` are used).  Key rewriting: with `m̃(β) := mZ(β)`,

  `G_β(θ) = (avg(θ) − mZ(β)·m̃(θ-β)) + (mZ(β) − Arith(θ))·m̃(θ-β)`,
  `avg(α+ξ) − mZ(α)·m̃(ξ) = M0 P N (arithQ ρ (max l₁ l₂)) α₁ α₂ ξ₁ ξ₂`  (definition of `M0`),

so on the part of the bump window where `Arith(θ) = mZ(β)` (`periodize (mStarF u) (θ-β) = 1`) the
bracket is exactly the `M0` of `Work.A7.M0SharpBound`.

**(K3) The mass bound.** For a `C²` symbol `F` and kernels `κ₁,κ₂ ∈ ℓ¹` with coefficient masses
`≍ 1` (here `κ_i = cw φ_i`, the Fourier transforms of the bumps), the coefficient
transform of a product is the convolution of the coefficient transforms, so
`smKernMass (coeff ((κ̂₁⊗κ̂₂) * K_G-shape))`-type estimates give, with the paper's `crude-mult`(ii)
(integration by parts in the two θ-variables, `r₁ = N⁻¹`, `r₂ = N^{-d}`),

  `smKernMass (fun a b => coeff Σ a b) ≤ C · sup_{j₁,j₂≤2} ∫∫ r₁^{j₁-1} r₂^{j₂-1} |∂^{j₁}_{θ₁}∂^{j₂}_{θ₂} Σ|`.

**(K4) The single-scale estimate.** `M0SharpBound` and `ModelApproxCore_M0_deriv_bound`
(`Submission/Work/A7/`) give
`|∂^{j₁}_{ξ₁}∂^{j₂}_{ξ₂} M0| ≤ C q² (1 + (2^{k₁}+2^{dk₂})²/N) N^{j₁+dj₂-1}` (`j₁,j₂ ≤ 2`,
`q = arithQ ρ (max l₁ l₂)`), and the bump derivative bounds
`∫ |(periodize φ_i)^{(i)}| ≍ (2^{k_i}/N)^{1-i}` turn (K3) into

  `smKernMass (Kconc − Kmod) ≤ C · #A₁ · #A₂ · q² · 2^{O(L)} · N⁻¹`

on the *good part* (where `Arith = mZ(β)` on the bump windows: this is the collapse step, and
`iw_height_separated` — the frequencies of `A_i` are `≳ 2^{-C_ρ2^{ρl_i}}` apart — together with
`2^{k}/N ≤ 2^{-2u}` and `periodize (mStarF u) = 1` on `|·| ≤ 2^{-2u}/2` (`ContDiffBump` axioms
`kmtEta_one`/`kmtEta_zero`) gives it).

**(K5) Summation and weight arithmetic.** `iw_height_card_le` gives
`#A_i ≲_ρ 2^{2^{ρ l_i}}` (`mag-lem`(iii)) and the period is `q ≲_ρ 2^{2^{ρL}}`
(`mag-lem`(ii)), so every factor is absorbed by `smallScaleWeight C ρ l₁ l₂ k₁ k₂`;
`1/N` is the *only* place where `N` appears and it is what makes the estimate possible.

**(K6) The complementary regime.** If `k₁ + 2·uScale ρ L > logN N` then (using `smallCond`'s
`inIndexSet`, i.e. `L ≤ C₀·logLogN N`, and `ρ ≤ 1/(4C₀)`) the integer `L` — and hence `N` — is
bounded in terms of `C₀, ρ` only (`Work.KMTAreas.A7.bound_of_not_narrow`), and the crude bound
`Work.KMTAreas.A7.smallKernMass_le_of_bounded` applies with a constant absorbed by `C`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.smallKconc_coeff
import Submission.Work.KMTAreas.A7.smallKmod_coeff

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger

/-! ## An elementary structural lemma about `smKernMass` -/

/-- The `ℓ¹(ℤ²)`-mass is subadditive. -/
theorem smKernMass_sub_le {K L : ℤ → ℤ → ℂ} :
    smKernMass (fun a b => K a b - L a b) ≤ smKernMass K + smKernMass L := by
  rw [smKernMass, smKernMass, smKernMass]
  calc ∑' p : ℤ × ℤ, ‖K p.1 p.2 - L p.1 p.2‖ₑ
      ≤ ∑' p : ℤ × ℤ, (‖K p.1 p.2‖ₑ + ‖L p.1 p.2‖ₑ) :=
        ENNReal.tsum_le_tsum fun p => by
          simpa only [enorm_eq_nnnorm, ← ENNReal.coe_add] using
            ENNReal.coe_le_coe.mpr (nnnorm_sub_le (K p.1 p.2) (L p.1 p.2))
    _ = (∑' p : ℤ × ℤ, ‖K p.1 p.2‖ₑ) + (∑' p : ℤ × ℤ, ‖L p.1 p.2‖ₑ) :=
        ENNReal.tsum_add

end

end Work.KMTAreas.A7

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger Work.Analysis.EndVar

/-! ## Elementary reductions used by the regime split -/

/-- **A period of an exact-height arithmetic frequency.**  Every frequency `β` of exact height
`≤ 2^l` is killed by some `q` in the Ionescu--Wainger denominator set `P_{≤l}`, and every such `q`
is at most `2^{C·2^{ρl}}` (`iwP_element_le`). -/
theorem exists_period_diffFreqs (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (l : ℕ) (β : Work.Analysis.IonescuWainger.Circle),
      β ∈ diffFreqs ρ l →
      ∃ q : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ (2 : ℝ) ^ (C * (2 : ℝ) ^ (ρ * (l : ℝ))) ∧ q • β = 0 := by
  obtain ⟨C, hC, hCb⟩ := iwP_element_le hρ
  refine ⟨C, hC, fun l β hβ => ?_⟩
  have hβ' : β ∈ iwArithFreqs ρ l := diffFreqs_subset_iwArithFreqs_le hρ hρ1 (le_refl l) hβ
  obtain ⟨q, hq, hqβ⟩ := mem_iwArithFreqs.mp hβ'
  exact ⟨q, Nat.one_le_iff_ne_zero.mpr (ne_zero_of_mem_iwP hq), hCb l q hq, hqβ⟩

/-- The auxiliary scale `uScale ρ L = ⌊2^{2ρL}⌋` is at least `1`. -/
theorem one_le_uScale (ρ : ℝ) (hρ : 0 ≤ ρ) (L : ℕ) : 1 ≤ uScale ρ L := by
  have h : ((1 : ℤ) : ℝ) ≤ (1 : ℝ) * (2 : ℝ) ^ (2 * ρ * (L : ℝ)) := by
    push_cast
    rw [one_mul]
    exact Real.one_le_rpow (by norm_num) (by positivity)
  have h2 : (1 : ℤ) ≤ ⌊(1 : ℝ) * (2 : ℝ) ^ (2 * ρ * (L : ℝ))⌋ := Int.le_floor.mpr h
  have h3 : (0 : ℤ) ≤ ⌊(1 : ℝ) * (2 : ℝ) ^ (2 * ρ * (L : ℝ))⌋ := le_trans (by norm_num) h2
  have h4 : (1 : ℤ) ≤ (⌊(1 : ℝ) * (2 : ℝ) ^ (2 * ρ * (L : ℝ))⌋.toNat : ℤ) := by
    rw [Int.toNat_of_nonneg h3]; exact h2
  have h5 : uScale ρ L = ⌊(1 : ℝ) * (2 : ℝ) ^ (2 * ρ * (L : ℝ))⌋.toNat := by
    unfold uScale scaleCount
    norm_num
  rw [h5]
  exact_mod_cast h4

/-- `smallCond` is monotone in the constant `C₀` of the index set. -/
theorem smallCond_mono_C₀ {ρ : ℝ} {C₀ C₀' : ℕ} {a : ℕ → NNReal} {l₁ l₂ k₁ k₂ n : ℕ}
    (h : C₀ ≤ C₀') (hc : smallCond ρ C₀ a l₁ l₂ k₁ k₂ n) :
    smallCond ρ C₀' a l₁ l₂ k₁ k₂ n := by
  obtain ⟨h1, h2, h3⟩ := hc
  obtain ⟨h4, h5, h6⟩ := h1
  have hhs : (heightScale C₀ (Nat.floor (a n)) : ℤ)
      ≤ (heightScale C₀' (Nat.floor (a n)) : ℤ) := by
    have : heightScale C₀ (Nat.floor (a n)) ≤ heightScale C₀' (Nat.floor (a n)) := by
      unfold heightScale
      exact Nat.mul_le_mul_right _ h
    exact_mod_cast this
  exact ⟨⟨le_trans h4 hhs, le_trans h5 hhs, le_trans h6 hhs⟩, h2, h3⟩

/-- The integer logarithm `logN N` agrees with its `toNat` as a real number. -/
theorem logN_toNat_cast (N : ℕ) :
    ((logN N : ℤ) : ℝ) = (((logN N).toNat : ℕ) : ℝ) := by
  have h1 : (((logN N : ℤ)) : ℝ) = (((logN N).toNat : ℤ) : ℝ) := by
    rw [Int.toNat_of_nonneg (logN_nonneg N)]
  have h2 : (((logN N).toNat : ℤ) : ℝ) = (((logN N).toNat : ℕ) : ℝ) := by push_cast; ring
  rw [h1, h2]

end

end Work.KMTAreas.A7

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger Work.Analysis.EndVar

/-- The maximum height of the small-scale parameters is `smallL`, as a real. -/
lemma lmaxR_eq_smallL (l₁ l₂ k₁ k₂ : ℕ) :
    lmaxR l₁ l₂ k₁ k₂ = ((smallL l₁ l₂ k₁ k₂ : ℕ) : ℝ) := by
  simp only [lmaxR, smallL, Work.Analysis.EndVar.lmax]
  push_cast
  rfl

end

end Work.KMTAreas.A7
