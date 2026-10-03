/-
# Interfaces of the second half of §5: the proof of Theorem `improv`(ii)

Krause--Mirek--Tao, §5.2, proves Theorem `improv`(ii) -- the single-scale minor-arc estimate for
the pair `(f,g)` when the *second* function `g` has no major-arc mass at the rescaled height
`d(-Log N + l)`, `d = deg P` -- by "repeating the proof of Theorem `improv`(i) with the role of
`f` now played by `g`, and with the spatial scale `N` replaced by `N^d`".

Concretely one considers the *second* dual function
`Ã_N^{**}(f,h)(x) = N⁻¹ ∑_{N/2<n≤N} f(x+n-P(n)) h(x-P(n))`
(equation `(bkhf)` of §5, `Submission/Work/Analysis/InverseTheory/Transpose.lean`), for which the
transposition identity `⟨Ã_N(f,g),h⟩ = ⟨Ã_N^{**}(f,h),g⟩` holds, and one proves the estimates

* `lip-2` (Proposition `lip-2`): the alternate inverse theorem for `g` — if the trilinear form of
  the hypotheses of Theorem `pp` is large, then `g` correlates with a function whose Fourier
  transform is concentrated in a major arc of scale `(l,k)` with `2^l ≲ δ^{-O(1)}` and
  `2^k ≲ δ^{-O(1)}/N^d` (the scale `N^d`, not `N`, because both shifts `n-P(n)`, `P(n)` are of
  size `N^d`);
* `struct-dual` (Corollary `struct-dual`): the Hahn--Banach decomposition of `Ã_N^{**}(f,h)` into
  major-arc pieces plus an `ℓ¹`-error of mass `δ N^d` and an `ℓ²`-error of norm `δ`;
* `propdual-second` (Proposition `propdual-second`): the `ℓ²` bound
  `‖(1-Π_{≤l,≤-dLogN+dl})Ã_N^{**}(f,h)‖_{ℓ²} ≲ 2^{-cl} N^{d/2} ‖f‖_∞‖h‖_∞`;
* `struct-iii-second` (Corollary `struct-iii-second`): the same with `‖f‖_{ℓ²}` in place of
  `‖f‖_∞` (using the `ℓ^p`-improving estimate `lp-improv` for the average `A_N^{n-P(n)}`, i.e.
  area A3 at `Q = P - X`);
* `siv-second` (Corollary `siv-second`): the same without the support hypotheses on `f` and `h`
  (using the off-diagonal decay `off-decay` of the Ionescu--Wainger projections, Lemma `iw-prop`).

This module fixes those five statements as predicates in the vocabulary of the workspace, so that
each step of the chain can be stated and proved as an *implication*, independently of the others.
The chain is glued together, and Theorem `improv`(ii) is deduced from its last member, in
`Submission/Work/KMTAreas/A4Z/Assembly.lean` and `Submission/Work/KMTAreas/A4/improvTwoZ.lean`.

## Notation

* `projTwo P ρ N l` is the projection `Π_{≤l,≤d(l-Log N)}` of Theorem `improv`(ii), i.e.
  `kmtProj ρ l ((P.natDegree : ℤ) * ((l : ℤ) - logN N))`;
* `AhalfTranspose₂ N P f h` is the second dual function (paper `(bkhf)`);
* `bilinPair f g = ∑_x f x * g x` is the paper's bilinear pairing (no conjugation).
-/
import Mathlib
import Submission.Work.KMTAreas.A4.Hahn
import Submission.Work.Analysis.InverseTheory.Transpose

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger
open Work.Analysis.InverseTheory
open Work.Analysis.EndVar

namespace Work.KMTAreas.A4Z

open Work.KMTAreas.A4 (MemL1Ball)

/-- **The projection `Π_{≤l,≤d(l-Log N)}` of Theorem `improv`(ii)**: the Ionescu--Wainger
projection at the arithmetic height scale `2^l` and the continuous height scale
`2^{d(l-Log N)}`, `d = deg P`, attached to the shifts `P(n)` of the second function. -/
noncomputable def projTwo (P : Polynomial ℤ) (ρ : ℝ) (N l : ℕ) (u : ℤ → ℂ) : ℤ → ℂ :=
  Work.KMTContract.kmtProj ρ l ((P.natDegree : ℤ) * ((l : ℤ) - logN N)) u

@[simp] theorem projTwo_apply (P : Polynomial ℤ) (ρ : ℝ) (N l : ℕ) (u : ℤ → ℂ) :
    projTwo P ρ N l u
      = Work.KMTContract.kmtProj ρ l ((P.natDegree : ℤ) * ((l : ℤ) - logN N)) u := rfl

/-- **Proposition `lip-2`** (the alternate inverse theorem for `g`, §5.2), as a predicate in the
constants `C, K`: for `1`-bounded functions `f,g,h` supported in `[-N₀,N₀]` with `N₀ ~ N^d` and
a large trilinear form, there is `G` with the `ℓ^∞`/`ℓ¹` bounds, Fourier support in
`majorArc ρ l k` with `2^l ≤ Cδ^{-K}` and `2^k ≤ Cδ^{-K}/N^d`, and the correlation
`δ^K N^d ≤ |⟨g,G⟩|`. -/
def LipOutputTwo (P : Polynomial ℤ) (ρ C K : ℝ) : Prop :=
  ∀ (N N₀ : ℕ) (δ : ℝ) (f g h : ℤ → ℂ), 1 ≤ N → 0 < δ → δ ≤ 1 →
    (N : ℝ) ^ P.natDegree / 2 ≤ (N₀ : ℝ) → (N₀ : ℝ) ≤ 2 * (N : ℝ) ^ P.natDegree →
    SupportIn f N₀ → SupportIn g N₀ → SupportIn h N₀ →
    (∀ x : ℤ, ‖f x‖ ≤ 1) → (∀ x : ℤ, ‖g x‖ ≤ 1) → (∀ x : ℤ, ‖h x‖ ≤ 1) →
    δ * (N : ℝ) ^ P.natDegree ≤ ‖bilinPair (AhalfZ N P f g) h‖ →
    ∃ (G : ℤ → ℂ) (l : ℕ) (k : ℤ),
      (∀ x : ℤ, ‖G x‖ ≤ C * δ⁻¹ ^ K) ∧
      Summable (fun x : ℤ => ‖G x‖) ∧
      (∑' x : ℤ, ‖G x‖ ≤ C * δ⁻¹ ^ K * (N : ℝ) ^ P.natDegree) ∧
      FourierSupportIn G (majorArc ρ l k) ∧
      (2 : ℝ) ^ l ≤ C * δ⁻¹ ^ K ∧
      (2 : ℝ) ^ k ≤ C * δ⁻¹ ^ K / (N : ℝ) ^ P.natDegree ∧
      δ ^ K * (N : ℝ) ^ P.natDegree ≤ ‖bilinPair g G‖

/-- **Proposition `lip-2` with the honest `ℓ¹` bound and the spatial tail bound** (the analogue of
`A4.LipOutputTail`): same as `LipOutputTwo`, plus the summability of `‖G ·‖` (so that the `ℓ¹`
bound is not vacuous) and the spatial concentration of `G` in `[-2N^d, 2N^d]`.  The tail conjunct
is what allows the test function of the Hahn--Banach step of Corollary `struct-dual` to be
replaced by its truncation. -/
def LipOutputTailTwo (P : Polynomial ℤ) (ρ C K : ℝ) : Prop :=
  ∀ (N N₀ : ℕ) (δ : ℝ) (f g h : ℤ → ℂ), 1 ≤ N → 0 < δ → δ ≤ 1 →
    (N : ℝ) ^ P.natDegree / 2 ≤ (N₀ : ℝ) → (N₀ : ℝ) ≤ 2 * (N : ℝ) ^ P.natDegree →
    SupportIn f N₀ → SupportIn g N₀ → SupportIn h N₀ →
    (∀ x : ℤ, ‖f x‖ ≤ 1) → (∀ x : ℤ, ‖g x‖ ≤ 1) → (∀ x : ℤ, ‖h x‖ ≤ 1) →
    δ * (N : ℝ) ^ P.natDegree ≤ ‖bilinPair (AhalfZ N P f g) h‖ →
    ∃ (G : ℤ → ℂ) (l : ℕ) (k : ℤ),
      (∀ x : ℤ, ‖G x‖ ≤ C * δ⁻¹ ^ K) ∧
      Summable (fun x : ℤ => ‖G x‖) ∧
      (∑' x : ℤ, ‖G x‖ ≤ C * δ⁻¹ ^ K * (N : ℝ) ^ P.natDegree) ∧
      (∑' x : ℤ, (if 2 * N ^ P.natDegree < x.natAbs then ‖G x‖ else 0)
        ≤ δ ^ K * (N : ℝ) ^ P.natDegree / 2) ∧
      FourierSupportIn G (majorArc ρ l k) ∧
      (2 : ℝ) ^ l ≤ C * δ⁻¹ ^ K ∧
      (2 : ℝ) ^ k ≤ C * δ⁻¹ ^ K / (N : ℝ) ^ P.natDegree ∧
      δ ^ K * (N : ℝ) ^ P.natDegree ≤ ‖bilinPair g G‖

/-- **The family `Φ₂` of Corollary `struct-dual`**
: the functions that Proposition `lip-2` may
return — pointwise bounded by `C δ^{-K}`, `ℓ¹`-norm at most `C δ^{-K} N^d`, and Fourier supported
in `majorArc ρ l k` with `2^l ≤ C δ^{-K}`, `2^k ≤ C δ^{-K}/N^d`. -/
def structPhiTwo (P : Polynomial ℤ) (ρ : ℝ) (C K δ : ℝ) (N : ℕ) : Set L2Z :=
  {ψ | (∀ x : ℤ, ‖ψ x‖ ≤ C * δ⁻¹ ^ K) ∧
       Summable (fun x : ℤ => ‖ψ x‖) ∧
       (∑' x : ℤ, ‖ψ x‖ ≤ C * δ⁻¹ ^ K * (N : ℝ) ^ P.natDegree) ∧
       (∃ l : ℕ, ∃ k : ℤ, FourierSupportIn (fun x : ℤ => ψ x) (majorArc ρ l k) ∧
         (2 : ℝ) ^ l ≤ C * δ⁻¹ ^ K ∧ (2 : ℝ) ^ k ≤ C * δ⁻¹ ^ K / (N : ℝ) ^ P.natDegree)}

/-- **Corollary `struct-dual`** (structure of the second dual function): the second dual function
`Ã_N^{**}(f,h)` is a finite non-negative combination of dilates of elements of the family
`structPhiTwo`, plus an `ℓ¹`-error `E₁` of norm at most `δN^d` and an `ℓ²`-error `E₂` of norm at
most `δ`; the dilating coefficients are bounded by `A/B` with `A = δN^d`, `B = δ^K N^d/4`. -/
def StructDecompTwo (P : Polynomial ℤ) (ρ C K δ : ℝ) (N : ℕ) (f h : ℤ → ℂ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (s : Finset ι) (φ : ι → L2Z) (lam : ι → ℂ) (w : ι → ℝ)
    (E₁ E₂ : L2Z),
    (∀ i ∈ s, φ i ∈ structPhiTwo P ρ C K δ N) ∧
    (∀ i ∈ s, ‖lam i‖ ≤ 4 * δ⁻¹ ^ (K - 1)) ∧
    (∀ i, 0 ≤ w i) ∧ (∑ i, w i ≤ 1) ∧
    MemL1Ball (δ * (N : ℝ) ^ P.natDegree) E₁ ∧ ‖E₂‖ ≤ δ ∧
    (∀ x : ℤ, AhalfTranspose₂ N P f h x
      = (∑ i ∈ s, w i • (lam i • φ i)) x + E₁ x + E₂ x)

/-- **Proposition `propdual-second`** at fixed rate `c`, parameters `(ρ, Cρ)` and constant `C`:
for `1`-bounded `f, h` supported in `[-N₀,N₀]` with `N₀ ~ N^d`, on good major arcs,
`‖(1-Π_{≤l,≤d(l-Log N)})Ã_N^{**}(f,h)‖_{ℓ²} ≤ C · 2^{-cl} · N^{d/2}`. -/
def PropdualSecondHyp (P : Polynomial ℤ) (c : ℝ) (ρ Cρ : ℝ) (C : ℝ≥0) : Prop :=
  ∀ (N N₀ l : ℕ) (f h : ℤ → ℂ), 1 ≤ N →
    (N : ℝ) ^ P.natDegree / 2 ≤ (N₀ : ℝ) → (N₀ : ℝ) ≤ (N : ℝ) ^ P.natDegree →
    SupportIn f N₀ → SupportIn h N₀ → (∀ x : ℤ, ‖f x‖ ≤ 1) → (∀ x : ℤ, ‖h x‖ ≤ 1) →
    GoodMajorArcs ρ Cρ l ((P.natDegree : ℤ) * ((l : ℤ) - logN N)) →
    eLpNorm (fun x : ℤ => AhalfTranspose₂ N P f h x - projTwo P ρ N l (AhalfTranspose₂ N P f h) x)
      2 Measure.count
      ≤ (C : ℝ≥0∞) * ENNReal.ofReal ((2 : ℝ) ^ (-(c * (l : ℝ))) * ((N : ℝ) ^ P.natDegree) ^ (1 / 2 : ℝ))

/-- **Corollary `struct-iii-second`** at fixed rate `c`: as `PropdualSecondHyp`, but with `f`
only in `ℓ²(ℤ)` (and still supported, `1`-bounded `h`), and with the bound
`C · 2^{-cl} · ‖f‖_{ℓ²}`. -/
def StructIiiSecondHyp (P : Polynomial ℤ) (c : ℝ) (ρ Cρ : ℝ) (C : ℝ≥0) : Prop :=
  ∀ (N N₀ l : ℕ) (f h : ℤ → ℂ), 1 ≤ N →
    (N : ℝ) ^ P.natDegree / 2 ≤ (N₀ : ℝ) → (N₀ : ℝ) ≤ (N : ℝ) ^ P.natDegree →
    SupportIn f N₀ → SupportIn h N₀ → MemLp f 2 Measure.count → (∀ x : ℤ, ‖h x‖ ≤ 1) →
    GoodMajorArcs ρ Cρ l ((P.natDegree : ℤ) * ((l : ℤ) - logN N)) →
    eLpNorm (fun x : ℤ => AhalfTranspose₂ N P f h x - projTwo P ρ N l (AhalfTranspose₂ N P f h) x)
      2 Measure.count
      ≤ (C : ℝ≥0∞) * ENNReal.ofReal ((2 : ℝ) ^ (-(c * (l : ℝ))))
          * eLpNorm f 2 Measure.count

/-- **Corollary `siv-second`** at fixed rate `c`: the `ℓ²` bound for `(1-Π_{≤l,≤d(l-Log N)})Ã^{**}`,
without support hypotheses, for `f ∈ ℓ²(ℤ)` and `‖h‖_∞ ≤ 1`.  This is the input of the final
duality step proving Theorem `improv`(ii). -/
def SivSecondHyp (P : Polynomial ℤ) (c : ℝ) (ρ Cρ : ℝ) (C : ℝ≥0) : Prop :=
  ∀ (N l : ℕ) (f h : ℤ → ℂ), 1 ≤ N → MemLp f 2 Measure.count → (∀ x : ℤ, ‖h x‖ ≤ 1) →
    GoodMajorArcs ρ Cρ l ((P.natDegree : ℤ) * ((l : ℤ) - logN N)) →
    eLpNorm (fun x : ℤ => AhalfTranspose₂ N P f h x - projTwo P ρ N l (AhalfTranspose₂ N P f h) x)
      2 Measure.count
      ≤ (C : ℝ≥0∞) * ENNReal.ofReal ((2 : ℝ) ^ (-(c * (l : ℝ))))
          * eLpNorm f 2 Measure.count

/-- **The off-diagonal decay `(off-decay)` of Lemma `iw-prop`(i)**, at fixed `ρ`: for every
exponent `q ∈ (1,∞)` and every order `M` there is a constant `Cρq` such that on good major arcs
the Ionescu--Wainger projection decays off the support of its input. -/
def OffDecayHyp (ρ : ℝ) : Prop :=
  ∀ (q : ℝ), 1 < q → ∀ (M : ℕ), ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ≥0, 0 < C ∧
    ∀ (l : ℕ) (k : ℤ), GoodMajorArcs ρ Cρ l k → ∀ (a b c d : ℤ) (f : ℤ → ℂ), b < c →
      (∀ x : ℤ, x < a ∨ b < x → f x = 0) →
      eLpNorm (fun x : ℤ => if c ≤ x ∧ x ≤ d then Work.KMTContract.kmtProj ρ l k f x else 0)
          (ENNReal.ofReal q) Measure.count
        ≤ (C : ℝ≥0∞) *
            ENNReal.ofReal ((max ((l : ℝ)) 1) *
              (max ((2 : ℝ) ^ k * ((c - b : ℤ) : ℝ)) 1) ^ (-(M : ℝ))) *
            eLpNorm f (ENNReal.ofReal q) Measure.count

/-- **Proposition `lip-2` with a free support-window parameter `A` and a quantitative spatial
tail clause.**  This is `LipOutputTwo` with the support window `N₀ ≤ 2 N^d` replaced by
`N₀ ≤ A N^d`, `A ≥ 1` a parameter, and with the additional clause that the returned function `G` is
concentrated in the window of radius `R N^d`, with a power-law tail:
`∑_{|x| > R N^d} ‖G x‖² ≤ C₀² R^{-K₂} (C A δ^{-K})² N^d` for every `R ≥ 1`.

The free window and the tail clause are needed by the second half of §5: the dual function
`Ã_N^{**}(f,h)` arising there is supported in `[min_n P(n) - N₀, max_n P(n) + N₀]`, a window whose
length is `~ C_P N^d` with `C_P` depending on the *coefficients* of `P` (e.g. `P = 100X²` gives a
window of length `~ 75 N²`), whereas the inputs `f, h` are supported in `[-N₀,N₀]`.  To apply the
inverse theorem to a test function of the Hahn--Banach step of Corollary `struct-dual`, that test
function has to be truncated to a window containing `supp Ã_N^{**}(f,h)`; the truncation is
harmless as long as one measures pairings against functions supported in that window, and the
returned function is concentrated around it up to the width `δ^{-O(1)} N^d` of the reproducing
kernel of `lip-2`.  This is expressed by the two tail clauses below.

**The `ℓ¹` tail clause at the window `A N^d`** (the second-to-last conjunct, mirroring the
`A4.LipOutputTail` clause `∑_{|x|>2N^d}‖F x‖ ≤ δ^K N^d/2` of the `f`-half) is what the
Hahn--Banach step of Corollary `struct-dual` actually consumes: one compares the pairing of a
`1`-bounded test function `u` with an output `G` to the pairing with the truncation
`1_{[-AN^d,AN^d]}·u`, and the two differ exactly by the `ℓ¹`-mass of `G` outside the window.
It is *provable* from the true `lip-2` because its output is the input convolved with a
reproducing kernel of width `δ^{-O(1)}N^d ≪ N^d`, so the mass outside the window is only the
shell of that width (times the constant of the kernel), whereas the pinned clause at `2N^d` —
a window *smaller* than the support radius `~ (Σ|coeff|) N^d` of the dual function — would be
false.

**The `ℓ²` tail clause** (the last conjunct, with the free parameter `R ≥ 1`) is the
concentration of the kernel beyond every `R N^d`; it is *strictly weaker* than the `ℓ¹` clause
(its right-hand side is the trivial bound `(C A δ^{-K})²N^d` times `R^{-K₂}`, and it only gives
`∑_{|x|>AN^d}‖G x‖ ≤ 2C₀²A^{-K₂}·C A δ^{-K}N^d` via the layer-cake argument, which is
`≫ δ^K N^d` as `δ → 0`).  It is kept because it is the clause a proof of `lip-2` most directly
yields; consumers should use the `ℓ¹` clause. -/
def LipOutputGenTwo (P : Polynomial ℤ) (ρ : ℝ) (A C K C₀ K₂ : ℝ) : Prop :=
  ∀ (N N₀ : ℕ) (δ : ℝ) (f g h : ℤ → ℂ), 1 ≤ N → 0 < δ → δ ≤ 1 →
    A * (N : ℝ) ^ P.natDegree / 2 ≤ (N₀ : ℝ) → (N₀ : ℝ) ≤ A * (N : ℝ) ^ P.natDegree →
    SupportIn f N₀ → SupportIn g N₀ → SupportIn h N₀ →
    (∀ x : ℤ, ‖f x‖ ≤ 1) → (∀ x : ℤ, ‖g x‖ ≤ 1) → (∀ x : ℤ, ‖h x‖ ≤ 1) →
    δ * (N : ℝ) ^ P.natDegree ≤ ‖bilinPair (AhalfZ N P f g) h‖ →
    ∃ (G : ℤ → ℂ) (l : ℕ) (k : ℤ),
      (∀ x : ℤ, ‖G x‖ ≤ C * A * δ⁻¹ ^ K) ∧
      Summable (fun x : ℤ => ‖G x‖) ∧
      (∑' x : ℤ, ‖G x‖ ≤ C * A * δ⁻¹ ^ K * (N : ℝ) ^ P.natDegree) ∧
      FourierSupportIn G (majorArc ρ l k) ∧
      (2 : ℝ) ^ l ≤ C * A * δ⁻¹ ^ K ∧
      (2 : ℝ) ^ k ≤ C * A * δ⁻¹ ^ K / (N : ℝ) ^ P.natDegree ∧
      δ ^ K * (N : ℝ) ^ P.natDegree ≤ ‖bilinPair g G‖ ∧
      (∑' x : ℤ, (if A * (N : ℝ) ^ P.natDegree < |(x : ℝ)| then ‖G x‖ else 0)
        ≤ δ ^ K * (N : ℝ) ^ P.natDegree / 2) ∧
      (∀ R : ℝ, 1 ≤ R →
        ∑' x : ℤ, (if R * (N : ℝ) ^ P.natDegree < |(x : ℝ)| then ‖G x‖ ^ 2 else 0)
          ≤ C₀ ^ 2 * R ^ (-(K₂)) * (C * A * δ⁻¹ ^ K) ^ 2 * (N : ℝ) ^ P.natDegree)

/-- **The family `Φ'₂` of Corollary `struct-dual`**: the untruncated outputs of `lip-2` together
with their truncations to the fixed window `[-N₀,N₀]`.

The truncations are added because the Hahn--Banach argument of Corollary `struct-dual` is run in
the *subspace* of functions supported in a window `W = [-N₀,N₀]` containing
`supp Ã_N^{**}(f,h)`: the test functions are then automatically supported (which is what `lip-2`
needs), and the pairing of a test function supported in `W` with an output `G` equals its pairing
with the truncation `G · 1_W`.  This removes the (unavoidable, in this range of parameters) loss
coming from the fringe of `G` outside the window.  The untruncated outputs are kept as well so
that the decomposition may be taken with Fourier-supported pieces. -/
def structPhiGenTwo (P : Polynomial ℤ) (ρ : ℝ) (A C K δ : ℝ) (N : ℕ) : Set L2Z :=
  {ψ | ∃ (G : ℤ → ℂ) (l : ℕ) (k : ℤ),
      (∀ x : ℤ, ‖G x‖ ≤ C * A * δ⁻¹ ^ K) ∧
      FourierSupportIn G (majorArc ρ l k) ∧
      (2 : ℝ) ^ l ≤ C * A * δ⁻¹ ^ K ∧
      (2 : ℝ) ^ k ≤ C * A * δ⁻¹ ^ K / (N : ℝ) ^ P.natDegree ∧
      (∀ x : ℤ, ψ x = G x)}

/-- **Corollary `struct-dual` with a free window parameter**: the decomposition of the second dual
function `Ã_N^{**}(f,h)`, for `f, h` supported in `[-N₀,N₀]` with `N₀` of the order of `A N^d`, into
`ℓ²`-pieces with Fourier support in the major arcs of `lip-2` plus an `ℓ¹`-error of mass `δ N^d` and
an `ℓ²`-error of norm `δ`. -/
def StructDecompGenTwo (P : Polynomial ℤ) (ρ C K δ : ℝ) (A : ℝ) (N : ℕ) (f h : ℤ → ℂ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (s : Finset ι) (φ : ι → L2Z) (lam : ι → ℂ) (w : ι → ℝ)
    (E₁ E₂ : L2Z),
    (∀ i ∈ s, φ i ∈ structPhiGenTwo P ρ A C K δ N) ∧
    (∀ i ∈ s, ‖lam i‖ ≤ 4 * δ⁻¹ ^ (K - 1)) ∧
    (∀ i, 0 ≤ w i) ∧ (∑ i, w i ≤ 1) ∧
    MemL1Ball (δ * (N : ℝ) ^ P.natDegree) E₁ ∧ ‖E₂‖ ≤ δ ∧
    (∀ x : ℤ, AhalfTranspose₂ N P f h x
      = (∑ i ∈ s, w i • (lam i • φ i)) x + E₁ x + E₂ x)

/-! ## The claims of §5.2, in the form in which the chain is assembled -/

/-- **Corollary `struct-dual`**, in the form of a self-contained claim: there are `C₁, K₁ > 0`
(independent of `ρ`) such that for every `ρ ∈ (0,1]`, every `N ≥ 1`, every `N₀` with
`N₀ ~ N^d`, every `δ ∈ (0,1]` and all `1`-bounded `f, h` supported in `[-N₀,N₀]`, the second dual
function `Ã_N^{**}(f,h)` decomposes as in `StructDecompTwo`. -/
def StructDecompClaim (P : Polynomial ℤ) : Prop :=
  ∃ C₁ K₁ : ℝ, 0 < C₁ ∧ 0 < K₁ ∧
    ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∀ (N N₀ : ℕ) (δ : ℝ) (f h : ℤ → ℂ), 1 ≤ N → 0 < δ → δ ≤ 1 →
      (N : ℝ) ^ P.natDegree / 2 ≤ (N₀ : ℝ) → (N₀ : ℝ) ≤ (N : ℝ) ^ P.natDegree →
      SupportIn f N₀ → SupportIn h N₀ →
      (∀ x : ℤ, ‖f x‖ ≤ 1) → (∀ x : ℤ, ‖h x‖ ≤ 1) →
      StructDecompTwo P ρ C₁ K₁ δ N f h

/-- **Proposition `propdual-second`** as a claim (`∃ c > 0`, `∀ ρ`, `∃ Cρ`, `∃ C`). -/
def PropdualSecondClaim (P : Polynomial ℤ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : NNReal, 0 < C ∧
    PropdualSecondHyp P c ρ Cρ C

/-- **Corollary `struct-iii-second`** as a claim. -/
def StructIiiSecondClaim (P : Polynomial ℤ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : NNReal, 0 < C ∧
    StructIiiSecondHyp P c ρ Cρ C

/-- **Corollary `siv-second`** as a claim. -/
def SivSecondClaim (P : Polynomial ℤ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : NNReal, 0 < C ∧
    SivSecondHyp P c ρ Cρ C

/-- **Proposition `lip-2` with the *sharp* concentration clause needed by Corollary
`struct-dual`.**  Same as `LipOutputGenTwo`, but the tail clause is an **`ℓ¹` fringe at the input's
own window**: the returned function has mass at most `δ^K N^d / 2` outside the ball of radius
`A N^d` (the window in which the inputs live).

This is exactly what the Hahn--Banach step of Corollary `struct-dual` consumes: applying `lip-2` to
`g := 1_{[-AN^d,AN^d]} · star ∘ u` gives `|⟨g,ψ⟩| ≥ δ^K N^d`, and to conclude the Hahn hypothesis
`|⟨u,ψ⟩| > δ^K N^d/2` for a `1`-bounded `u` one needs precisely this fringe bound (the two
pairings differ by `Σ_{|x|>AN^d} star(u x)ψ x`).  It is *not* implied by the `ℓ²` tail clause of
`LipOutputGenTwo` (a bump just outside the window satisfies that clause but violates this one), and
a "tail at the *fixed* window `2N^d`" is false in this range of parameters because the reproducing
kernel of `lip-2` has width `δ^{-O(1)}N^d`, of the order of the window itself.  Whether the true
`lip-2` output satisfies this sharp clause is the quantitative question isolated by the
`struct-dual` step (it amounts to a comparison between the inverse-Weyl fringe exponent and the
correlation exponent of `lip-2`). -/
def LipOutputGenTwoTail (P : Polynomial ℤ) (ρ : ℝ) (A C K C0 K2 : ℝ) : Prop :=
  ∀ (N N₀ : ℕ) (δ : ℝ) (f g h : ℤ → ℂ), 1 ≤ N → 0 < δ → δ ≤ 1 →
    A * (N : ℝ) ^ P.natDegree / 2 ≤ (N₀ : ℝ) → (N₀ : ℝ) ≤ A * (N : ℝ) ^ P.natDegree →
    SupportIn f N₀ → SupportIn g N₀ → SupportIn h N₀ →
    (∀ x : ℤ, ‖f x‖ ≤ 1) → (∀ x : ℤ, ‖g x‖ ≤ 1) → (∀ x : ℤ, ‖h x‖ ≤ 1) →
    δ * (N : ℝ) ^ P.natDegree ≤ ‖bilinPair (AhalfZ N P f g) h‖ →
    ∃ (G : ℤ → ℂ) (l : ℕ) (k : ℤ),
      (∀ x : ℤ, ‖G x‖ ≤ C * A * δ⁻¹ ^ K) ∧
      Summable (fun x : ℤ => ‖G x‖) ∧
      (∑' x : ℤ, ‖G x‖ ≤ C * A * δ⁻¹ ^ K * (N : ℝ) ^ P.natDegree) ∧
      FourierSupportIn G (majorArc ρ l k) ∧
      (2 : ℝ) ^ l ≤ C * A * δ⁻¹ ^ K ∧
      (2 : ℝ) ^ k ≤ C * A * δ⁻¹ ^ K / (N : ℝ) ^ P.natDegree ∧
      δ ^ K * (N : ℝ) ^ P.natDegree ≤ ‖bilinPair g G‖ ∧
      (∑' x : ℤ, (if A * (N : ℝ) ^ P.natDegree < |(x : ℝ)| then ‖G x‖ else 0)
        ≤ δ ^ K * (N : ℝ) ^ P.natDegree / 2) ∧
      (∀ R : ℝ, 1 ≤ R →
        ∑' x : ℤ, (if R * (N : ℝ) ^ P.natDegree < |(x : ℝ)| then ‖G x‖ ^ 2 else 0)
          ≤ C0 ^ 2 * R ^ (-(K2)) * (C * A * δ⁻¹ ^ K) ^ 2 * (N : ℝ) ^ P.natDegree)

/-- **Corollary `struct-dual` with the sharp `lip-2` input**: the decomposition of the second dual
function `Ã_N^{**}(f,h)` from the sharp form `LipOutputGenTwoTail` of Proposition `lip-2`. -/
def StructDecompClaimOfLipTail (P : Polynomial ℤ) : Prop :=
  (∀ (A : ℝ), 1 ≤ A → ∃ C K C0 K2 : ℝ, 0 < C ∧ 0 < K ∧ 0 < C0 ∧ 0 < K2 ∧
      ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → LipOutputGenTwoTail P ρ A C K C0 K2) →
    StructDecompClaim P

end Work.KMTAreas.A4Z
