/-
# The window-parameterised §5.1 chain of Krause--Mirek--Tao's Theorem `improv`(i)

This module fixes the *interfaces* of the proof of Theorem `improv`(i) (Krause--Mirek--Tao,
Ann. of Math. 195 (2022), §5.1) in the form in which the target `Work.KMTAreas.A4.improvOneZ`
uses them, i.e. with the support-window constant `A` kept free.

## Why the window must be free (read this before changing the statements)

The paper's `lip`, Corollary `struct` and Corollary `struct-iii` are stated for `f, g, h`
supported in `[-N₀, N₀]` with `N₀ ~ N^d` (`d = deg P`), the implied constant being allowed to
depend on the polynomial `P`.  That `P`-dependent constant is *not* cosmetic.  In the proof of
Corollary `siv`, `g` is partitioned into intervals `I` of length `N^d`; the summands of
`Ã*_N(h, g·1_I)` are `h(x-n) g(x+P(n)-n)`, so the average only sees `h` restricted to

  `W_I = I - P((N/2, N])`,

an interval of the same length `O(N^d)` but at distance `~ |P(N)| ~ |a_d| N^d` from `I`.  The pair
`(h·1_{W_I}, g·1_I)` therefore inhabits a ball of radius `~ (1 + |a_d|) N^d`, which for
`|a_d| > 1` does **not** fit into the ball of radius `2 N^d` of the pinned statements
(`Work.KMTAreas.A4.LipOutputTail` and friends): for `P = 100 X^2` those pinned hypotheses are
even *vacuous* (`Submission/Work/KMTAreas/A4/lipOutputTail_vacuous_100sq.lean`, and
`NOTES_A4_window_pin_GAP.md`).  Since the target `improvOneZ` has no support hypotheses at all,
no argument can replace the free window by a vacuous pinned statement.

So every statement below carries the parameter `A ≥ 1`, and the hypothesis `A` is instantiated
only once, in the proof of `siv`, with a constant depending on the coefficients of `P` — which is
exactly what the paper's `N₀ ~ N^d` means.

## The chain

* `LipOutA P A`            — Proposition `lip` at the window `A` (from `PeluseInverseKIMT P`);
* `StructAClaim P A`       — Corollary `struct` at the window `A` (LIP + Hahn--Banach);
* `PropdualAClaim P A`     — Proposition `propdual` at the window `A` (struct + `AreaA1`);
* `StructiiiAClaim P A`    — Corollary `struct-iii` at the window `A` (+ `PolyImproving (X-P)`);
* `OffDecayClaim ρ`        — Lemma `iw-prop`(i) off-diagonal decay (from `AreaA1`), window-free;
* `SivClaimZ P`            — Corollary `siv` (window-free), from `StructiiiAClaim` + `OffDecayClaim`;
* the target `improvOneZ` follows from `SivClaimZ P` by the final duality (transposition
  `⟨Ã_N(f,g),h⟩ = ⟨Ã*_N(h,g),f⟩` + `ℓ¹`--`ℓ^∞` duality), as in
  `Work.KMTAreas.A4Z.improvTwoZ_of_sivSecond` for part (ii).
-/
import Mathlib
import Submission.Work.KMTAreas.A4.ImprovOneClaims
import Submission.Work.KMTAreas.A4.LipOutputTailA

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators

namespace Work.KMTAreas.A4

open Work.Analysis.InverseTheory (SupportIn AhalfZ AhalfTranspose bilinPair FourierSupportIn majorArc FinSupp)
open Work.Analysis.IonescuWainger (L2Z)

/-- **Proposition `lip` (alternate inverse theorem for `f`) with a free support-window constant
`A ≥ 1`**, from Peluse's inverse theorem.

For `1`-bounded `f, g, h` supported in `[-M, M]` with `N^d/A ≤ M ≤ A N^d` and a large trilinear
form there is `F` — bounded by `C·A·δ^{-K}`, summable with `ℓ¹`-norm at most `C·A·δ^{-K}N^d`,
concentrated in `[-M, M]` up to mass `δ^K N^d/2`, with Fourier transform supported in
`majorArc ρ l k`, `2^l ≤ C·A·δ^{-K}`, `2^k ≤ C·A·δ^{-K}/N`, and correlating with `f`:
`δ^K N^d ≤ |⟨f, F⟩|`.

The concentration clause is at `M` itself (the support radius of the inputs): this is exactly
what the Hahn--Banach step of Corollary `struct` needs, where the test function is truncated to
the window `[-M, M]` and the dual function `Ã*_N(h,g)` is supported in `[-(N₀+N), N₀+N]` with
`N₀ + N ≤ M`. -/
def LipOutA (P : Polynomial ℤ) (A : ℝ) : Prop :=
  ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
  ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∀ (N M : ℕ) (δ : ℝ) (f g h : ℤ → ℂ), 1 ≤ N → 0 < δ → δ ≤ 1 →
    (N : ℝ) ^ P.natDegree / A ≤ (M : ℝ) → (M : ℝ) ≤ A * (N : ℝ) ^ P.natDegree →
    SupportIn f M → SupportIn g M → SupportIn h M →
    (∀ x : ℤ, ‖f x‖ ≤ 1) → (∀ x : ℤ, ‖g x‖ ≤ 1) → (∀ x : ℤ, ‖h x‖ ≤ 1) →
    δ * (N : ℝ) ^ P.natDegree ≤ ‖bilinPair (AhalfZ N P f g) h‖ →
    ∃ (F : ℤ → ℂ) (l : ℕ) (k : ℤ),
      (∀ x : ℤ, ‖F x‖ ≤ C * A * δ⁻¹ ^ K) ∧
      Summable (fun x : ℤ => ‖F x‖) ∧
      (∑' x : ℤ, ‖F x‖ ≤ C * A * δ⁻¹ ^ K * (N : ℝ) ^ P.natDegree) ∧
      (∑' x : ℤ, (if (M : ℝ) < |(x : ℝ)| then ‖F x‖ else 0)
        ≤ δ ^ K * (N : ℝ) ^ P.natDegree / 2) ∧
      FourierSupportIn F (majorArc ρ l k) ∧
      (2 : ℝ) ^ l ≤ C * A * δ⁻¹ ^ K ∧
      (2 : ℝ) ^ k ≤ C * A * δ⁻¹ ^ K / (N : ℝ) ∧
      δ ^ K * (N : ℝ) ^ P.natDegree ≤ ‖bilinPair f F‖

/-- **The family `Φ` of Corollary `struct` at the window `A`**: the functions that `LipOutA` may
return — pointwise bounded by `C·A·δ^{-K}`, `ℓ¹`-norm at most `C·A·δ^{-K}N^d`, and Fourier
supported in `majorArc ρ l k` with `2^l ≤ C·A·δ^{-K}`, `2^k ≤ C·A·δ^{-K}/N`. -/
def StructPhiA (P : Polynomial ℤ) (ρ A C K δ : ℝ) (N : ℕ) : Set L2Z :=
  {ψ | (∀ x : ℤ, ‖ψ x‖ ≤ C * A * δ⁻¹ ^ K) ∧
       Summable (fun x : ℤ => ‖ψ x‖) ∧
       (∑' x : ℤ, ‖ψ x‖ ≤ C * A * δ⁻¹ ^ K * (N : ℝ) ^ P.natDegree) ∧
       (∃ l : ℕ, ∃ k : ℤ, FourierSupportIn (fun x : ℤ => ψ x) (majorArc ρ l k) ∧
         (2 : ℝ) ^ l ≤ C * A * δ⁻¹ ^ K ∧ (2 : ℝ) ^ k ≤ C * A * δ⁻¹ ^ K / (N : ℝ))}

/-- **Corollary `struct`** (structure of the dual function, I) at the window `A`: the dual
function `Ã*_N(h,g)` is a finite non-negative combination of dilates of elements of `StructPhiA`,
plus an `ℓ¹`-error `E₁` of norm at most `δN^d` and an `ℓ²`-error `E₂` of norm at most `δ`; the
dilating coefficients are bounded by `4δ^{1-K}` (the Hahn--Banach balance `A/B` with
`A = δN^d`, `B = δ^K N^d/4`). -/
def StructDecompA (P : Polynomial ℤ) (ρ A C K δ : ℝ) (N : ℕ) (g h : ℤ → ℂ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (s : Finset ι) (φ : ι → L2Z) (lam : ι → ℂ) (w : ι → ℝ)
    (E₁ E₂ : L2Z),
    (∀ i ∈ s, φ i ∈ StructPhiA P ρ A C K δ N) ∧
    (∀ i ∈ s, ‖lam i‖ ≤ 4 * δ⁻¹ ^ (K - 1)) ∧
    (∀ i, 0 ≤ w i) ∧ (∑ i, w i ≤ 1) ∧
    MemL1Ball (δ * (N : ℝ) ^ P.natDegree) E₁ ∧
    ‖E₂‖ ≤ δ ∧
    (∀ x : ℤ, AhalfTranspose N P h g x
      = (∑ i ∈ s, w i • (lam i • φ i)) x + E₁ x + E₂ x)

/-- **Corollary `struct` at the window `A`, as a self-contained claim**: there are constants
`C, K > 0` (those of `LipOutA P A`; in particular independent of `ρ`) such that for every
`ρ ∈ (0,1]`, every `δ ∈ (0,1]`, every `N ≥ 1`, every support radius `N₀` and every truncation
radius `M` with `N₀ + N ≤ M` and `N^d/A ≤ M ≤ A N^d`, and every pair of `1`-bounded `g, h`
supported in `[-N₀,N₀]`, the dual function `Ã*_N(h,g)` decomposes as in `StructDecompA`.

The constants are quantified *existentially* and before `ρ` — as in `LipOutA P A`, whose constants
they are.  (Quantifying them universally would be false: `StructPhiA` is empty when
`C·A·δ^{-K} < 1`, and the decomposition would then have to approximate `Ã*_N(h,g)` by `E₁ + E₂`
alone, which fails for e.g. `g = h = 1` on `[-N₀,N₀]`.) -/
def StructAClaim (P : Polynomial ℤ) (A : ℝ) : Prop :=
  ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
  ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∀ (δ : ℝ) (N N₀ M : ℕ) (g h : ℤ → ℂ), 1 ≤ N → 0 < δ → δ ≤ 1 →
    (N : ℝ) ^ P.natDegree / A ≤ (M : ℝ) → (M : ℝ) ≤ A * (N : ℝ) ^ P.natDegree →
    (N₀ : ℝ) + (N : ℝ) ≤ (M : ℝ) →
    SupportIn g N₀ → SupportIn h N₀ →
    (∀ x : ℤ, ‖g x‖ ≤ 1) → (∀ x : ℤ, ‖h x‖ ≤ 1) →
    StructDecompA P ρ A C K δ N g h

/-- **Proposition `propdual` at the window `A` and rate `c`**: on good major arcs,

`‖(1 - Π_{≤l,≤-Log N+l}) Ã*_N(h,g)‖_{ℓ²} ≤ C · 2^{-cl} · N^{d/2}`

for `g, h` supported in `[-N₀,N₀]` with `N^d/A ≤ N₀` and `N₀ + N ≤ A N^d`. -/
def PropdualAHyp (P : Polynomial ℤ) (A c : ℝ) (ρ Cρ : ℝ) (C : ℝ≥0) : Prop :=
  ∀ (N N₀ l : ℕ) (g h : ℤ → ℂ), 1 ≤ N →
    (N : ℝ) ^ P.natDegree / A ≤ (N₀ : ℝ) → (N₀ : ℝ) + (N : ℝ) ≤ A * (N : ℝ) ^ P.natDegree →
    SupportIn g N₀ → SupportIn h N₀ → (∀ x : ℤ, ‖g x‖ ≤ 1) → (∀ x : ℤ, ‖h x‖ ≤ 1) →
    Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l ((l : ℤ) - Work.Analysis.EndVar.logN N) →
    MeasureTheory.eLpNorm (fun x : ℤ => AhalfTranspose N P h g x
        - Work.KMTContract.kmtProj ρ l ((l : ℤ) - Work.Analysis.EndVar.logN N)
            (AhalfTranspose N P h g) x) 2 (MeasureTheory.Measure.count : Measure ℤ)
      ≤ (C : ENNReal) * ENNReal.ofReal ((2 : ℝ) ^ (-(c * (l : ℝ))) *
          ((N : ℝ) ^ P.natDegree) ^ (1 / 2 : ℝ))

/-- **Proposition `propdual` at the window `A`**, as a claim. -/
def PropdualAClaim (P : Polynomial ℤ) (A : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : NNReal, 0 < C ∧
    PropdualAHyp P A c ρ Cρ C

/-- **Corollary `struct-iii` at the window `A` and rate `c`**: as `PropdualAHyp`, but with `g`
only assumed to be in `ℓ²` (and still supported), and with the bound `C·2^{-cl}‖g‖_{ℓ²}`. -/
def StructiiiAHyp (P : Polynomial ℤ) (A c : ℝ) (ρ Cρ : ℝ) (C : ℝ≥0) : Prop :=
  ∀ (N N₀ l : ℕ) (g h : ℤ → ℂ), 1 ≤ N →
    (N : ℝ) ^ P.natDegree / A ≤ (N₀ : ℝ) → (N₀ : ℝ) + (N : ℝ) ≤ A * (N : ℝ) ^ P.natDegree →
    SupportIn g N₀ → SupportIn h N₀ → MeasureTheory.MemLp g 2 MeasureTheory.Measure.count →
    (∀ x : ℤ, ‖h x‖ ≤ 1) →
    Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l ((l : ℤ) - Work.Analysis.EndVar.logN N) →
    MeasureTheory.eLpNorm (fun x : ℤ => AhalfTranspose N P h g x
        - Work.KMTContract.kmtProj ρ l ((l : ℤ) - Work.Analysis.EndVar.logN N)
            (AhalfTranspose N P h g) x) 2 (MeasureTheory.Measure.count : Measure ℤ)
      ≤ (C : ENNReal) * ENNReal.ofReal ((2 : ℝ) ^ (-(c * (l : ℝ))))
          * MeasureTheory.eLpNorm g 2 (MeasureTheory.Measure.count : Measure ℤ)

/-- **Corollary `struct-iii` at the window `A`**, as a claim. -/
def StructiiiAClaim (P : Polynomial ℤ) (A : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : NNReal, 0 < C ∧
    StructiiiAHyp P A c ρ Cρ C

/-- **Corollary `siv`** (structure of the dual function, IV), window-free: the `ℓ²` bound for
`(1 - Π_{≤l,≤-Log N+l}) Ã*_N(h,g)` without any support hypothesis on `g`. -/
def SivHyp (P : Polynomial ℤ) (c : ℝ) (ρ Cρ : ℝ) (C : ℝ≥0) : Prop :=
  ∀ (N l : ℕ) (g h : ℤ → ℂ), 1 ≤ N →
    MeasureTheory.MemLp g 2 (MeasureTheory.Measure.count : Measure ℤ) →
    (∀ x : ℤ, ‖h x‖ ≤ 1) →
    Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l ((l : ℤ) - Work.Analysis.EndVar.logN N) →
    MeasureTheory.eLpNorm (fun x : ℤ => AhalfTranspose N P h g x
        - Work.KMTContract.kmtProj ρ l ((l : ℤ) - Work.Analysis.EndVar.logN N)
            (AhalfTranspose N P h g) x) 2 (MeasureTheory.Measure.count : Measure ℤ)
      ≤ (C : ENNReal) * ENNReal.ofReal ((2 : ℝ) ^ (-(c * (l : ℝ))))
          * MeasureTheory.eLpNorm g 2 (MeasureTheory.Measure.count : Measure ℤ)

/-- **Corollary `siv`** as a claim. -/
def SivClaimZ (P : Polynomial ℤ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : NNReal, 0 < C ∧
    SivHyp P c ρ Cρ C

/-! ## The interface actually used by the chain: the tail at `A N^d`

The LIP input available in this workspace (`A4/peluseLipL1TailA`, `A4/LipOutputTailA`) measures the
spatial tail of the returned `F` outside the ball of radius `A N^d` (the *window*), not outside the
support radius `N₀` of the inputs.  The §5.1 chain is therefore formulated with the Hahn--Banach
test function truncated at radius `⌊A N^d⌋`:  the truncation error is invisible on the support of
the dual function `Ã*_N(h,g)` (which sits in `[-(N₀+N), N₀+N] ⊆ [-A N^d, A N^d]`), and it is
bounded by the tail clause because `x.natAbs > ⌊A N^d⌋` implies `|x| > A N^d`.

`LipWinA P A` is the statement of `LipOutputTailA` with the constants quantified once and for all
for the window `A` — the form produced by `A4.lipOutputTailA_of_lipL1A` from
`A4.peluseLipL1TailA`. -/

/-- **Proposition `lip` at the window `A`**, as a claim: the constants of `LipOutputTailA` at the
fixed window `A`, quantified before `ρ` (so that the §5.1 chain has a rate independent of `ρ`). -/
def LipWinA (P : Polynomial ℤ) (A : ℝ) : Prop :=
  ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
    ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → LipOutputTailA P ρ A C K

/-- **Corollary `struct` at the window `A`**, in the form matching `LipWinA`: the dual function of
a pair `g, h` supported in `[-N₀,N₀]` with `N₀ ∈ [N^d/A, A N^d]` and `N₀ + N ≤ A N^d` decomposes
into major-arc pieces plus `ℓ¹`- and `ℓ²`-errors (the Hahn--Banach test function is truncated at
the window `⌊A N^d⌋`). -/
def StructWinA (P : Polynomial ℤ) (A : ℝ) : Prop :=
  ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
  ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∀ (δ : ℝ) (N N₀ : ℕ) (g h : ℤ → ℂ), 1 ≤ N → 0 < δ → δ ≤ 1 →
    (N : ℝ) ^ P.natDegree / A ≤ (N₀ : ℝ) →
    (N₀ : ℝ) + (N : ℝ) ≤ A * (N : ℝ) ^ P.natDegree →
    SupportIn g N₀ → SupportIn h N₀ →
    (∀ x : ℤ, ‖g x‖ ≤ 1) → (∀ x : ℤ, ‖h x‖ ≤ 1) →
    StructDecompA P ρ A C K δ N g h

end Work.KMTAreas.A4
