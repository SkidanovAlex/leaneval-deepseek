/-
The **small-scale half** of the Ionescu–Wainger multiplier theorem for the concrete sets
`iwArithFreqs ρ l`, assembled from the fleet's lemmas.

Why this is the half that does not need the deep super-orthogonality input: the MSZ3/Tao proof of
the multiplier bound needs the arithmetic gap of `2r`-fold products of denominators to dominate
`2rε` (MSZ3: `Q₀N^{4rD} ≲ e^{N^ρ}/r`; Tao: the `(r,c)`-goodness `ε < c/(2r q_max^{2rk})`), i.e. it
applies only for scales `l` above a threshold `l₀(r,ρ)`.  Below that threshold the scale is
*finite* and the bound is elementary: the IW arcs `α + ℝ_{≤k}`, `α ∈ (ℚ/ℤ)_{≤l}`, are pairwise
disjoint (proved in the workspace, `exists_goodMajorArcs_nonAliasing`), and each single arc is a
Magyar–Stein–Wainger multiplier (a modulation of the `T[1]`-case), so

`‖T^{≤l}_φ‖_{ℓ^q} ≤ ∑_{α} ‖Op_{φ;α}‖_{ℓ^q} ≤ |(ℚ/ℤ)_{≤l}| · C · M`,

with a constant depending only on `(ρ,q)` and on the threshold.

## Contents

* `MSWSingleTorsion` — the Magyar–Stein–Wainger sampling principle for a single torsion subgroup
  `T[Q]` (the statement proved by `Work.KMTAreas.MSW_single_torsion`, recorded here as a `Prop` so
  that the assembly below can be written and checked independently of that proof);
* `IWLqBound_singleton_of_MSW` — consequently every *single* arc `{α}` is bounded by `(C M)`;
* `IWLqBound_of_singleton_bounds` — the finite sum over the arcs, with the loss `A.card`
  (the corrected union lemma `IWLqBound_biUnion_of_integrable`).

See `Submission/Work/KMTAreas/A1_STATUS.md` §8 for how these reduce A1 to the deep input *only for
large* `l`.
-/
import Mathlib
import Submission.Work.KMTAreas.IWLqBound_of_scalar
import Submission.Work.KMTAreas.IWLqBound_singleton
import Submission.Work.KMTAreas.IWLqBound_biUnion_of_integrable

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators ENNReal NNReal
open MeasureTheory

namespace Work.KMTAreas

open Work.Analysis.IWMultiplier
open Work.Analysis.IonescuWainger

/-- **The Magyar–Stein–Wainger sampling principle for a single torsion subgroup** — the statement
proved by `Work.KMTAreas.MSW_single_torsion`, recorded as a `Prop`. -/
def MSWSingleTorsion : Prop :=
  ∀ (Q : ℕ), 1 ≤ Q → ∀ (p : ENNReal), 1 ≤ p → p < ⊤ →
    ∃ C : NNReal, 0 < C ∧ ∀ {k : ℤ}, (2 : ℝ) ^ k * (2 * (Q : ℝ)) ≤ 1 →
      ∀ {φ : SchwartzMap ℝ ℂ}, (∀ x, φ x ≠ 0 → x ∈ realArc k) →
      ∀ {M : NNReal}, IsLqMultiplierBound p (φ : ℝ → ℂ) M →
        IWLqBoundScalar (iwDenomFreqs {Q}) (periodize (φ : ℝ → ℂ)) p (C * M)

/-- `iwDenomFreqs {1}` is the singleton `{0}`: the `Q = 1` case of the sampling principle is the
single-arc multiplier `Op_{φ;0}`. -/
theorem iwDenomFreqs_one : iwDenomFreqs {1} = ({0} : Finset Work.Analysis.IonescuWainger.Circle) := by
  ext α
  rw [mem_iwDenomFreqs, Finset.mem_singleton]
  constructor
  · rintro ⟨q, hq, -, hqα⟩
    rw [Finset.mem_singleton] at hq
    subst hq
    simpa using hqα
  · intro h
    subst h
    exact ⟨1, by simp, le_refl 1, by simp⟩

/-- **Every single arc is bounded, quantitatively.**  This is the step that turns the
Magyar–Stein–Wainger sampling principle at `Q = 1` into a bound for every singleton frequency set
`{α}`; it needs (i) the modulation invariance `IWLqBound_singleton` (which preserves the constant)
and (ii) the quantitative form of `IWLqBound_of_scalar` (the Hilbert-valued conclusion from the
scalar one, with a constant depending only on `q`).  The statement is recorded here for the
assembly; it is *not* used by anything else yet.

`∃ C, 0 < C ∧ ∀ (k : ℤ), (2:ℝ)^k * 2 ≤ 1 → ∀ (φ : SchwartzMap ℝ ℂ),
  (∀ x, φ x ≠ 0 → x ∈ realArc k) → ∀ (M : NNReal), IsLqMultiplierBound q (φ : ℝ → ℂ) M →
  ∀ α, IWLqBound ({α} : Finset Circle) (periodize (φ : ℝ → ℂ)) q (C * M)`. -/
def IWLqBound_singleton_of_MSW_statement (hMSW : MSWSingleTorsion) (q : ENNReal) : Prop :=
  ∃ C : NNReal, 0 < C ∧ ∀ (k : ℤ), (2 : ℝ) ^ k * 2 ≤ 1 →
    ∀ (φ : SchwartzMap ℝ ℂ), (∀ x, φ x ≠ 0 → x ∈ Work.Analysis.IonescuWainger.realArc k) →
    ∀ (M : NNReal), Work.Analysis.IWMultiplier.IsLqMultiplierBound q (φ : ℝ → ℂ) M →
    ∀ α : Work.Analysis.IonescuWainger.Circle,
      Work.Analysis.IWMultiplier.IWLqBound ({α} : Finset Work.Analysis.IonescuWainger.Circle)
        (periodize (φ : ℝ → ℂ)) q (C * M)

/-- **The finite sum over the arcs.**  If every single arc is bounded by `C`, then a finite set `A`
of frequencies with pairwise disjoint arcs is bounded by `C · A.card`. -/
theorem IWLqBound_of_singleton_bounds {A : Finset Work.Analysis.IonescuWainger.Circle} {Φ : Work.Analysis.IonescuWainger.Circle → ℂ}
    (hint : ∀ α ∈ A, Integrable (iwSymbolSet ({α} : Finset Work.Analysis.IonescuWainger.Circle) Φ) circleMeasure)
    {q : ENNReal} (hq : 1 ≤ q) {C : NNReal}
    (h : ∀ α ∈ A, IWLqBound ({α} : Finset Work.Analysis.IonescuWainger.Circle) Φ q C) :
    IWLqBound A Φ q (C * A.card) := by
  classical
  have hdisj : ∀ α ∈ A, ∀ β ∈ A, α ≠ β →
      Disjoint ({α} : Finset Work.Analysis.IonescuWainger.Circle) ({β} : Finset Work.Analysis.IonescuWainger.Circle) := by
    intro α _ β _ hne
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [Finset.mem_singleton] at hx hx'
    exact hne (hx.symm.trans hx')
  have hbi : A.biUnion (fun α : Work.Analysis.IonescuWainger.Circle => ({α} : Finset Work.Analysis.IonescuWainger.Circle)) = A := by
    ext x
    simp
  simpa [hbi] using IWLqBound_biUnion_of_integrable A (fun α : Work.Analysis.IonescuWainger.Circle => ({α} : Finset Work.Analysis.IonescuWainger.Circle))
    hdisj hint hq h

end Work.KMTAreas
