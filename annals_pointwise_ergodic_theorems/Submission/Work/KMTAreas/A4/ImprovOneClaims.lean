/-
# The interfaces of the §5.1 chain of Krause--Mirek--Tao's Theorem `improv`(i)

This module fixes, as `Prop`-valued definitions, the four statements into which the proof of
Theorem `improv`(i) (the case in which the *first* function `f` has no major-arc content) is
decomposed by §5.1 and its Appendix A:

* `OffDecayClaim ρ` — Lemma `iw-prop`(i)'s off-diagonal decay of the Ionescu--Wainger
  projections `Π_{≤l,≤k} = kmtProj ρ l k` (proved in Appendix A from the even-exponent
  Ionescu--Wainger multiplier theorem, area A1);
* `PropdualClaim P` — Proposition `propdual` of §5.1: the `ℓ²` bound
  `‖(1 - Π_{≤l,≤-Log N+l}) Ã*_N(h,g)‖₂ ≲ 2^{-cl} N^{d/2}` for `1`-bounded `g,h` supported in
  `[-N₀,N₀]`, `N₀ ~ N^d`, on good major arcs;
* `StructIIIClaim P` — Corollary `struct-iii`: the same with `‖g‖_{ℓ²}` in place of `‖g‖_∞`
  (using the `ℓ^p`-improving estimate, area A3);
* `SIVClaim P` — Corollary `siv`: the same without the support hypothesis on `g`.

`SIVClaim P` is the final input of the duality argument that proves Theorem `improv`(i):
for `f ∈ ℓ²(ℤ)` with `Π_{≤l,≤-LogN+l} f = 0`, `g ∈ ℓ²(ℤ)` and `h ∈ ℓ^∞(ℤ)`,
`‖(1 - Π_{≤l,≤-LogN+l}) Ã*_N(h,g)‖_{ℓ²} ≲ 2^{-cl}‖h‖_∞‖g‖_{ℓ²}`.

The three trivial implications `PropdualClaim → PropdualClaim`-style wrappers are not needed:
the definitions are used directly as the statements of the corresponding lemmas
(`A4/propdualKMT`, `A4/structiiiKMT`, `A4/sivKMT`, `A4/offDecayKMT`).
-/
import Mathlib
import Submission.Work.KMTAreas.A4.Struct

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators

namespace Work.KMTAreas.A4

open Work.Analysis.InverseTheory

/-- **Lemma `iw-prop`(i), off-diagonal decay** (Appendix A) at a fixed `ρ`: for every exponent
`q ∈ (1,∞)` and every order `M` there are `Cρ > 0` and `C > 0` such that for every pair `(l,k)` of
good major arcs and every `f` supported in `(-∞,b]` with `b < c`,

`‖Π_{≤l,≤k} f‖_{ℓ^q[c,d]} ≤ C ⟨l⟩ ⟨2^k (c-b)⟩^{-M} ‖f‖_{ℓ^q}`. -/
def OffDecayClaim (ρ : ℝ) : Prop :=
  ∀ (q : ℝ), 1 < q → ∀ (M : ℕ),
    ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : NNReal, 0 < C ∧
      ∀ (l : ℕ) (k : ℤ), Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l k →
      ∀ (a b c d : ℤ) (f : ℤ → ℂ), b < c →
        (∀ x : ℤ, x < a ∨ b < x → f x = 0) →
        MeasureTheory.eLpNorm
            (fun x : ℤ => if c ≤ x ∧ x ≤ d then Work.KMTContract.kmtProj ρ l k f x else 0)
            (ENNReal.ofReal q) (MeasureTheory.Measure.count : Measure ℤ)
          ≤ (C : ENNReal) *
              ENNReal.ofReal ((max ((l : ℝ)) 1) *
                (max ((2 : ℝ) ^ k * ((c - b : ℤ) : ℝ)) 1) ^ (-(M : ℝ))) *
              MeasureTheory.eLpNorm f (ENNReal.ofReal q) (MeasureTheory.Measure.count : Measure ℤ)

/-- **Proposition `propdual`** of §5.1 (structure of the dual function, II). -/
def PropdualClaim (P : Polynomial ℤ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 →
    ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : NNReal, 0 < C ∧
      ∀ (N N₀ l : ℕ) (g h : ℤ → ℂ), 1 ≤ N →
        (N : ℝ) ^ P.natDegree / 2 ≤ (N₀ : ℝ) → (N₀ : ℝ) ≤ (N : ℝ) ^ P.natDegree →
        SupportIn g N₀ → SupportIn h N₀ → (∀ x : ℤ, ‖g x‖ ≤ 1) → (∀ x : ℤ, ‖h x‖ ≤ 1) →
        Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l
            ((l : ℤ) - Work.Analysis.EndVar.logN N) →
        MeasureTheory.eLpNorm (fun x : ℤ => AhalfTranspose N P h g x
            - Work.KMTContract.kmtProj ρ l ((l : ℤ) - Work.Analysis.EndVar.logN N)
                (AhalfTranspose N P h g) x) 2 (MeasureTheory.Measure.count : Measure ℤ)
          ≤ (C : ENNReal) * ENNReal.ofReal ((2 : ℝ) ^ (-(c * (l : ℝ))) *
              ((N : ℝ) ^ P.natDegree) ^ (1 / 2 : ℝ))

/-- **Corollary `struct-iii`** of §5.1 (structure of the dual function, III). -/
def StructIIIClaim (P : Polynomial ℤ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 →
    ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : NNReal, 0 < C ∧
      ∀ (N N₀ l : ℕ) (g h : ℤ → ℂ), 1 ≤ N →
        (N : ℝ) ^ P.natDegree / 2 ≤ (N₀ : ℝ) → (N₀ : ℝ) ≤ (N : ℝ) ^ P.natDegree →
        SupportIn g N₀ → SupportIn h N₀ → (∀ x : ℤ, ‖h x‖ ≤ 1) →
        Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l
            ((l : ℤ) - Work.Analysis.EndVar.logN N) →
        MeasureTheory.eLpNorm (fun x : ℤ => AhalfTranspose N P h g x
            - Work.KMTContract.kmtProj ρ l ((l : ℤ) - Work.Analysis.EndVar.logN N)
                (AhalfTranspose N P h g) x) 2 (MeasureTheory.Measure.count : Measure ℤ)
          ≤ (C : ENNReal) * ENNReal.ofReal ((2 : ℝ) ^ (-(c * (l : ℝ)))) *
              MeasureTheory.eLpNorm g 2 (MeasureTheory.Measure.count : Measure ℤ)

/-- **Corollary `siv`** of §5.1 (structure of the dual function, IV): the `ℓ²` bound for
`(1 - Π_{≤l,≤-LogN+l}) Ã*_N(h,g)` without any support hypothesis on `g` or `h`. -/
def SIVClaim (P : Polynomial ℤ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 →
    ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : NNReal, 0 < C ∧
      ∀ (N l : ℕ) (g h : ℤ → ℂ), 1 ≤ N →
        MeasureTheory.MemLp g 2 (MeasureTheory.Measure.count : Measure ℤ) →
        (∀ x : ℤ, ‖h x‖ ≤ 1) →
        Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l
            ((l : ℤ) - Work.Analysis.EndVar.logN N) →
        MeasureTheory.eLpNorm (fun x : ℤ => AhalfTranspose N P h g x
            - Work.KMTContract.kmtProj ρ l ((l : ℤ) - Work.Analysis.EndVar.logN N)
                (AhalfTranspose N P h g) x) 2 (MeasureTheory.Measure.count : Measure ℤ)
          ≤ (C : ENNReal) * ENNReal.ofReal ((2 : ℝ) ^ (-(c * (l : ℝ)))) *
              MeasureTheory.eLpNorm g 2 (MeasureTheory.Measure.count : Measure ℤ)

end Work.KMTAreas.A4
