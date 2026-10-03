/-
# The model-operator sub-contract of Area A6 (`VarpL2KMT`)

Area **A6** of the KMT contract (`Submission/Work/KMTContract/Areas.lean`) is the paper's
Theorem `varp` at `(p₁,p₂,p) = (2,2,1)` with the exponential gain
`2^{-c max(max l₁ l₂)(max s₁ s₂)}`, from the Ionescu--Wainger multiplier theorem (A1) and the
single-scale minor arc estimate `improv` (`ImprovKMT`).  Its proof is the paper's §6--§9:

* §6 "Approximation by model operators": the paraproduct pieces `F^{u,l₁,s₁}_N f` are written as
  `T^{l₁}_{φ_N}F` with `F = Π_{l₁,≤-u}f`, the halved average `Ã_N` is replaced by the twisted
  bilinear multiplier `B^{l₁,l₂,m_Ẑ}_{(φ_N⊗φ̃_N)m̃_{N,ℝ}}`, the symbol is factorised through
  `m_* = η_{≤-2u}⊗η_{≤-2du}` (functional calculus), and the scale set is split into
  `I_sml = {N ≤ 2^{2^u}}` and `I_lrg = {N > 2^{2^u}}`;
* §7 "The small-scale estimate": the two-parameter Rademacher--Menshov inequality `rm-bil`
  (workspace: `Work.Analysis.Paraproduct.SmallScale.smallScale_variational_le_Vr`) plus a single
  scale estimate `SSU` (itself an application of `improv`);
* §8 "The large-scale estimate": the quantitative Shannon sampling theorem, the arithmetic
  bilinear estimate `bile` (App. C + §10), vector-valued Lépingle, and the shifted
  Calderón--Zygmund square function estimates;
* §6 (cont.) the integration-by-parts identity `integ-ident` producing the decay in
  `max(s₁,s₂) - l`, together with the `V^r` bounds `weight-bound` of the weights
  `P'(Nt)/N^{d-1}`, `N^{d-1}/P'(Nt)`, `N^dP''(Nt)/P'(Nt)²`;
* Proposition `high-high-l2`: the case `s₁,s₂ > -u`, `p₁ = p₂ = 2`, which follows from `improv`
  applied twice, Cauchy--Schwarz and the Bessel inequality `∑_{N∈I}‖F_N‖₂² ≲ ‖f‖₂²`.

At the bottom scale `u = 0` of the contract's pieces `varpPiece`/`varpCol` the four cases are

* `CaseHH`   (`s₁,s₂ > -u`):      `k₁ ≥ 1 ∧ k₂ ≥ 1`;
* `CaseLowLow` (`s₁ = s₂ = -u`):  `k₁ = 0 ∧ k₂ = 0`;
* `CaseLowHigh` (`s₂ > s₁ = -u`): `k₁ = 0 ∧ k₂ ≥ 1`;
* `CaseHighLow` (`s₁ > s₂ = -u`): `k₁ ≥ 1 ∧ k₂ = 0`.

This module fixes the vocabulary of the sub-contract:

* `PieceBoundOn ρ P C₀ p₁ p₂ p r w Q` — the case-restricted form of `PieceBound`;
* `pieceBound_of_cases` — the (proved) assembly: two case-restricted bounds whose cases cover all
  quadruples give `PieceBound`;
* `highHigh_of_inputs` — the (proved) reduction of the high–high case to the two inputs
  `pieceProjVanishing`({\ref{FN-def}}) and `pieceBessel`, plus `improv` (`ImprovKMT`) and the
  domination of the logarithmic error term by the gain;
* `pieceProjVanishing*`, `pieceBessel*` — the two inputs, stated in the vocabulary of
  `Submission/Work/KMTContract/Defs.lean` (delegated);
* `pieceBoundOn_mono_weight`, `pieceBoundOn_mono_case` — the elementary monotonicities.

Nothing here is postulated as an axiom; the only hypothesis of `highHigh_of_inputs` are the
explicit ones listed.
-/
import Submission.Work.KMTContract.Defs

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace Work.KMTPlan

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal PNat BigOperators
open PointwiseErgodicTheorems
open Submission.PointwiseErgodicTheorems
open Work.Analysis.EndVar
open Work.KMTContract

/-! ## The four cases of the §6 decomposition -/

/-- **The high–high case** `s₁,s₂ > -u` of §6 at the bottom scale `u = 0` of the contract's
pieces: both `k₁` and `k₂` are at least `1`.  This is the case covered by the paper's
Proposition `high-high-l2`. -/
def CaseHH (l₁ l₂ k₁ k₂ : ℕ) : Prop := 1 ≤ k₁ ∧ 1 ≤ k₂

/-- **The low–low case** `s₁ = s₂ = -u` at `u = 0`: `k₁ = k₂ = 0`. -/
def CaseLowLow (l₁ l₂ k₁ k₂ : ℕ) : Prop := k₁ = 0 ∧ k₂ = 0

/-- **The low–high case** `s₂ > s₁ = -u` at `u = 0`: `k₁ = 0` and `k₂ ≥ 1`. -/
def CaseLowHigh (l₁ l₂ k₁ k₂ : ℕ) : Prop := k₁ = 0 ∧ 1 ≤ k₂

/-- **The high–low case** `s₁ > s₂ = -u` at `u = 0`: `k₁ ≥ 1` and `k₂ = 0`. -/
def CaseHighLow (l₁ l₂ k₁ k₂ : ℕ) : Prop := 1 ≤ k₁ ∧ k₂ = 0

/-- The complement of the high–high case: at least one of `k₁`, `k₂` vanishes.  The cases
`CaseLowLow`, `CaseLowHigh`, `CaseHighLow` all imply it; it is the case in which the paper's §6
reduction to the model operator (Theorem `model-est`) is applied. -/
def CaseRest (l₁ l₂ k₁ k₂ : ℕ) : Prop := k₁ = 0 ∨ k₂ = 0

theorem caseHH_or_caseRest (l₁ l₂ k₁ k₂ : ℕ) :
    CaseHH l₁ l₂ k₁ k₂ ∨ CaseRest l₁ l₂ k₁ k₂ := by
  by_cases h₁ : k₁ = 0
  · exact Or.inr (Or.inl h₁)
  · by_cases h₂ : k₂ = 0
    · exact Or.inr (Or.inr h₂)
    · exact Or.inl ⟨Nat.one_le_iff_ne_zero.mpr h₁, Nat.one_le_iff_ne_zero.mpr h₂⟩

/-! ## Case-restricted paraproduct bounds -/

/-- **The case-restricted form of `PieceBound`.**  As `PieceBound ρ P C₀ p₁ p₂ p r w`, but with
the additional hypothesis `Q l₁ l₂ k₁ k₂` on the quadruple of indices.  This is the form in which
the four cases of §6/§7/§8 are proved separately. -/
def PieceBoundOn (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (p₁ p₂ p : ℝ≥0∞) (r : ℝ≥0)
    (w : ℕ → ℕ → ℕ → ℕ → ℝ) (Q : ℕ → ℕ → ℕ → ℕ → Prop) : Prop :=
  ∃ C : ℝ≥0 → ℝ≥0,
    ∀ (a : ℕ → ℝ≥0) (Λ : ℝ≥0) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
      1 < Λ → Lacunary Λ a → (∀ n, 1 ≤ a n) → Q l₁ l₂ k₁ k₂ →
      eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ =>
          varpCol (kmtPj ρ) P P.natDegree C₀ a f g l₁ l₂ k₁ k₂ n x))
        p Measure.count
      ≤ (C Λ : ℝ≥0∞) * ENNReal.ofReal (w l₁ l₂ k₁ k₂) *
          eLpNorm f p₁ Measure.count * eLpNorm g p₂ Measure.count

/-- The case-restricted bound is monotone in the weight. -/
theorem pieceBoundOn_mono_weight {ρ : ℝ} {P : ℤ[X]} {C₀ : ℕ} {p₁ p₂ p : ℝ≥0∞} {r : ℝ≥0}
    {w w' : ℕ → ℕ → ℕ → ℕ → ℝ} {Q : ℕ → ℕ → ℕ → ℕ → Prop}
    (hw : ∀ l₁ l₂ k₁ k₂, w' l₁ l₂ k₁ k₂ ≤ w l₁ l₂ k₁ k₂)
    (h : PieceBoundOn ρ P C₀ p₁ p₂ p r w' Q) : PieceBoundOn ρ P C₀ p₁ p₂ p r w Q := by
  obtain ⟨C, hC⟩ := h
  refine ⟨C, fun a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 hQ => ?_⟩
  refine (hC a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 hQ).trans ?_
  gcongr
  exact hw l₁ l₂ k₁ k₂

/-- The case-restricted bound is monotone in the case predicate. -/
theorem pieceBoundOn_mono_case {ρ : ℝ} {P : ℤ[X]} {C₀ : ℕ} {p₁ p₂ p : ℝ≥0∞} {r : ℝ≥0}
    {w : ℕ → ℕ → ℕ → ℕ → ℝ} {Q Q' : ℕ → ℕ → ℕ → ℕ → Prop} (hQ : ∀ l₁ l₂ k₁ k₂, Q' l₁ l₂ k₁ k₂ → Q l₁ l₂ k₁ k₂)
    (h : PieceBoundOn ρ P C₀ p₁ p₂ p r w Q) : PieceBoundOn ρ P C₀ p₁ p₂ p r w Q' := by
  obtain ⟨C, hC⟩ := h
  exact ⟨C, fun a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 hQ' => hC a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 (hQ _ _ _ _ hQ')⟩

/-- **The assembly of the case split.**  If the paraproduct bound holds for two case predicates
which cover every quadruple of indices, then it holds unconditionally (the constants being
combined by `max`). -/
theorem pieceBound_of_cases {ρ : ℝ} {P : ℤ[X]} {C₀ : ℕ} {p₁ p₂ p : ℝ≥0∞} {r : ℝ≥0}
    {w : ℕ → ℕ → ℕ → ℕ → ℝ} {Q₁ Q₂ : ℕ → ℕ → ℕ → ℕ → Prop}
    (hcover : ∀ l₁ l₂ k₁ k₂, Q₁ l₁ l₂ k₁ k₂ ∨ Q₂ l₁ l₂ k₁ k₂)
    (h₁ : PieceBoundOn ρ P C₀ p₁ p₂ p r w Q₁) (h₂ : PieceBoundOn ρ P C₀ p₁ p₂ p r w Q₂) :
    PieceBound ρ P C₀ p₁ p₂ p r w := by
  obtain ⟨C₁, hC₁⟩ := h₁
  obtain ⟨C₂, hC₂⟩ := h₂
  rw [PieceBound, VarpStatementΛWith]
  refine ⟨fun Λ => max (C₁ Λ) (C₂ Λ), fun a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 => ?_⟩
  rcases hcover l₁ l₂ k₁ k₂ with h | h
  · refine (hC₁ a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 h).trans ?_
    gcongr
    exact le_max_left _ _
  · refine (hC₂ a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 h).trans ?_
    gcongr
    exact le_max_right _ _

/-- The high–high case and its complement together give `PieceBound` (the shape in which §6 and
§7--§9 are proved). -/
theorem pieceBound_of_hh_and_rest {ρ : ℝ} {P : ℤ[X]} {C₀ : ℕ} {p₁ p₂ p : ℝ≥0∞} {r : ℝ≥0}
    {w : ℕ → ℕ → ℕ → ℕ → ℝ}
    (hh : PieceBoundOn ρ P C₀ p₁ p₂ p r w CaseHH)
    (hr : PieceBoundOn ρ P C₀ p₁ p₂ p r w CaseRest) :
    PieceBound ρ P C₀ p₁ p₂ p r w :=
  pieceBound_of_cases caseHH_or_caseRest hh hr

/-! ## The sub-contract of the high–high case

/-! ## The sub-contract of the high–high case

The high–high case `CaseHH` of `PieceBoundOn` is proved from the following named inputs (each of
which is proved in its own module under `Submission/Work/KMTPlan/A6/`):

* `VanishingF`, `VanishingG` — the vanishing of the `F`-/`G`-piece under the IW projection at the
  coupled height `(L, -LogN + L)` (the hypothesis of `ImprovKMT`);
* `BesselF`, `BesselG` — the Bessel/Plancherel inequality `∑_{n∈s}‖F_n‖₂² ≲ ‖f‖₂²` for the
  pieces in the good-major-arc regime;
* `NonAliasingSize` — the IW non-aliasing of `(ℚ/ℤ)_{≤l}` beyond the explicit scale;
* `LogGain` — the domination of the logarithmic error term of `ImprovKMT` by the gain;
* `GoodScaleArith` — for large height parameters every scale of the index set is in the
  good-major-arc regime. -/
namespace Sub

open Work.Analysis.IonescuWainger

/-- **Vanishing input, `F`-side.**  Under the good-major-arc hypothesis (non-aliasing at the
scale `max(k₁,L) - LogN + 1`) and the disjunction `L < l₁ ∨ L + 2 ≤ k₁`, the IW projection at
`(L, -LogN + L)` kills the difference piece `F^{0,l₁,k₁}_N f`. -/
def VanishingF : Prop :=
  ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∀ (l₁ k₁ L N : ℕ) (f : ℤ → ℂ), 1 ≤ k₁ →
    (L < l₁ ∨ L + 2 ≤ k₁) →
    max (k₁ : ℤ) (L : ℤ) + 2 ≤ Work.Analysis.EndVar.logN N →
    NonAliasing (max (k₁ : ℤ) (L : ℤ) - Work.Analysis.EndVar.logN N + 1)
      (iwArithFreqs ρ l₁ ∪ iwArithFreqs ρ L) →
    MemLp f 2 Measure.count →
    kmtProj ρ L (-(Work.Analysis.EndVar.logN N) + (L : ℤ))
      (Work.Analysis.EndVar.Fpiece (kmtPj ρ) 0 l₁ (k₁ : ℤ) N f) = 0

/-- **Vanishing input, `G`-side.**  The rescaled analogue of `VanishingF` for the piece
`G^{0,l₂,k₂}_N g` (heights `d(-LogN + s)`, `d = P.natDegree`). -/
def VanishingG : Prop :=
  ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∀ (P : ℤ[X]) (l₂ k₂ L N : ℕ) (g : ℤ → ℂ), 1 ≤ k₂ →
    (L < l₂ ∨ L + 2 ≤ k₂) →
    max (k₂ : ℤ) (L : ℤ) + 2 ≤ Work.Analysis.EndVar.logN N →
    NonAliasing ((P.natDegree : ℤ) * (-(Work.Analysis.EndVar.logN N) + (max k₂ L : ℤ)) + 1)
      (iwArithFreqs ρ l₂ ∪ iwArithFreqs ρ L) →
    MemLp g 2 Measure.count →
    kmtProj ρ L ((P.natDegree : ℤ) * (-(Work.Analysis.EndVar.logN N) + (L : ℤ)))
      (Work.Analysis.EndVar.Gpiece (kmtPj ρ) (P.natDegree : ℤ) 0 l₂ (k₂ : ℤ) N g) = 0

/-- **Bessel input, `F`-side** (paper's *Bessel-type inequalities*): in the good-major-arc regime
the pieces `F^{0,l₁,k₁}_{N_n} f` along a lacunary family of scales are almost orthogonal. -/
def BesselF (ρ : ℝ) : Prop :=
  ∃ (B : ℝ≥0 → ℝ≥0) (C : ℝ), 0 < C ∧
    ∀ (l₁ k₁ : ℕ), 1 ≤ k₁ → ∀ (a : ℕ → ℝ≥0) (Λ : ℝ≥0), 1 < Λ → Lacunary Λ a →
      (∀ n, 1 ≤ a n) → ∀ (s : Finset ℕ) (f : ℤ → ℂ), MemLp f 2 Measure.count →
      (∀ n ∈ s, ((max l₁ k₁ : ℕ) : ℝ) + C * (2 : ℝ) ^ (ρ * (l₁ : ℝ))
          ≤ ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ)) →
      ∑ n ∈ s, (eLpNorm (Work.Analysis.EndVar.Fpiece (kmtPj ρ) 0 l₁ (k₁ : ℤ)
            (Nat.floor (a n)) f) 2 Measure.count) ^ (2 : ℕ)
        ≤ ((B Λ : ℝ≥0) : ℝ≥0∞) ^ (2 : ℕ) * (eLpNorm f 2 Measure.count) ^ (2 : ℕ)

/-- **Bessel input, `G`-side.** -/
def BesselG (ρ : ℝ) (P : ℤ[X]) : Prop :=
  ∃ (B : ℝ≥0 → ℝ≥0) (C : ℝ), 0 < C ∧
    ∀ (l₂ k₂ : ℕ), 1 ≤ k₂ → ∀ (a : ℕ → ℝ≥0) (Λ : ℝ≥0), 1 < Λ → Lacunary Λ a →
      (∀ n, 1 ≤ a n) → ∀ (s : Finset ℕ) (g : ℤ → ℂ), MemLp g 2 Measure.count →
      (∀ n ∈ s, ((max l₂ k₂ : ℕ) : ℝ) + C * (2 : ℝ) ^ (ρ * (l₂ : ℝ))
          ≤ ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ)) →
      ∑ n ∈ s, (eLpNorm (Work.Analysis.EndVar.Gpiece (kmtPj ρ) (P.natDegree : ℤ) 0 l₂ (k₂ : ℤ)
            (Nat.floor (a n)) g) 2 Measure.count) ^ (2 : ℕ)
        ≤ ((B Λ : ℝ≥0) : ℝ≥0∞) ^ (2 : ℕ) * (eLpNorm g 2 Measure.count) ^ (2 : ℕ)

/-- **Non-aliasing input.**  Beyond the explicit scale `-C·2^{ρ·max(l₁,L)}` the arithmetic
frequency set `(ℚ/ℤ)_{≤l₁} ∪ (ℚ/ℤ)_{≤L}` is non-aliasing. -/
def NonAliasingSize (ρ : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (l₁ L : ℕ) (K : ℤ),
    (K : ℝ) + C * (2 : ℝ) ^ (ρ * (max l₁ L : ℝ)) < 0 →
    NonAliasing K (iwArithFreqs ρ l₁ ∪ iwArithFreqs ρ L)

/-- **Log-domination input.**  In the good-major-arc regime the secondary (logarithmic) term of
`ImprovKMT` is dominated by the exponential gain `2^{-(c/2)·lmax}`. -/
def LogGain (ρ c R : ℝ) : Prop :=
  ∀ (lmax : ℕ) (X : ℝ), 1 ≤ X →
    (lmax : ℝ) + R * (2 : ℝ) ^ (ρ * (lmax : ℝ)) + 2 ≤ X →
    X ^ (-(c / ρ)) ≤ (2 : ℝ) ^ (-(c / 2 * (lmax : ℝ)))

/-- **Good-scale input.**  For all sufficiently large height parameters, every scale of the index
set `I^{l,s₁,s₂}` (i.e. every `N` with `lmax ≤ l_(N)`) is in the good-major-arc regime. -/
def GoodScaleArith (C₀ : ℕ) (ρ R : ℝ) : Prop :=
  ∃ B₀ : ℕ, ∀ (lmax N : ℕ), B₀ ≤ lmax → lmax ≤ Work.Analysis.EndVar.heightScale C₀ N →
    (lmax : ℝ) + R * (2 : ℝ) ^ (ρ * (lmax : ℝ)) + 2
      ≤ ((Work.Analysis.EndVar.logN N : ℤ) : ℝ)

end Sub

end

end Work.KMTPlan
