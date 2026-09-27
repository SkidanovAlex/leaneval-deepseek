import Mathlib
import Submission.Work.EKLContract.All
import Submission.Work.EKLRelCross.Instances
import Submission.Work.EKLRelCross.LeafBasic
import Submission.Work.EKLRelCross.LeafExistDefs
import Submission.Work.EKLComp.LeafDefs
import Submission.Work.EKLComp.condExpKernel_atom
import Submission.Work.EKLComp.joinAtoms

/-!
# Leafwise measures: the construction of `ν`

Vocabulary for the construction of the leafwise measures `ν x` of a horospherical subgroup
`U ≤ SL₃(ℝ)` on `X₃`, from a family of "flowers" (plaque algebras with a measurable base on
which the atoms contain a large plaque), Pisa §5–6.

* `pushOrbit U x κ` — transport of a measure `κ` on `X₃` carried by the `U`-orbit of `x` to a
  measure on `SL₃(ℝ)` carried by `U` (via the inverse of `u ↦ u • x`);
* `piece U k` — the annulus `Ucl U (k+1) \ Ucl U k`; the `piece U k` (`k ∈ ℕ`) partition `U`;
* `FlowerFamily U μ` — the flower input: for every `R > 1` countably many plaque algebras
  `(Z k, m k)` with measurable base `G k` on which `V R ∩ U ⊆ shape (m k) U x`, covering a.e.;
* `sel G x` — the least index whose base contains `x`;
* `refPush`, `nuLevel`, `nuFull` — the conditional measure pushed to `U`, its normalisation by
  `Box1 U`, and the patched family `ν`.
-/

open MeasureTheory Topology Filter
open scoped ENNReal

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLRelCross

open Work.EKLContract Work.EKLComp

/-! ## Transport of a measure on `X₃` to the group -/

/-- Transport of a measure `ν` on `X₃` (carried by the `U`-orbit through `x`) to a measure on
`SL₃(ℝ)` carried by `U`: the pushforward under the inverse of `u ↦ u • x`, restricted to `U`.
If `u ↦ u • x` is injective on `U`, then for Borel `A ⊆ SL₃(ℝ)` this is `ν ((A ∩ U) • x)`. -/
def pushOrbit (U : Subgroup SL3) (x : X3) (ν : Measure X3) : Measure SL3 :=
  (Measure.comap (fun u : U => (u : SL3) • x) ν).map (Subtype.val)

/-! ## The annuli `piece U k` -/

/-- The `k`-th annulus of the closed `U`-balls: `piece U 0 = Ucl U 1` (so that the identity,
which lies in `Ucl U 0 = {1}`, is included) and `piece U (k+1) = Ucl U (k+2) \ Ucl U (k+1)`.
The sets `piece U k`, `k ∈ ℕ`, are pairwise disjoint and cover `U`, and
`Box1 U = Ucl U 1 = piece U 0`. -/
def piece (U : Subgroup SL3) : ℕ → Set SL3
  | 0 => Ucl U 1
  | (k + 1) => Ucl U ((k : ℝ) + 2) \ Ucl U ((k : ℝ) + 1)

/-! ## The flower input -/

/-- **The flower family** (Pisa Def. 6.14 / Cor. 6.15): for every radius `R > 1` there are
countably many plaque algebras `(Z k, m k)`, with measurable bases `G k ⊆ Z k` of positive-measure
domains, on which the shape contains `V R ∩ U`, and the bases cover almost every point. -/
def FlowerFamily (U : Subgroup SL3) (μ : Measure X3) : Prop :=
  ∀ R : ℝ, 1 < R → ∃ (Z : ℕ → Set X3) (m : ℕ → MeasurableSpace X3) (G : ℕ → Set X3),
    (∀ k, IsPlaqueAlgebra U (Z k) (m k)) ∧
    (∀ k, MeasurableSet (G k)) ∧
    (∀ k, μ (Z k) ≠ 0) ∧
    (∀ k, ∀ x ∈ G k, V R ∩ (U : Set SL3) ⊆ shape (m k) U x) ∧
    μ (⋃ k, G k)ᶜ = 0

/-! ## The flower data, bundled -/

/-- Bundled flower data (Pisa Def. 6.14 / Cor. 6.15) for a fixed subgroup `U` and measure `μ`:
for every level `k` countably many plaque algebras `(Z k i, m k i)` with measurable bases
`G k i` of positive-measure domains, on which `V (k+2) ∩ U ⊆ shape (m k i) U x`. -/
structure FlowerData (U : Subgroup SL3) (μ : Measure X3) where
  Z : ℕ → ℕ → Set X3
  m : ℕ → ℕ → MeasurableSpace X3
  G : ℕ → ℕ → Set X3
  isPlaque : ∀ k i, IsPlaqueAlgebra U (Z k i) (m k i)
  measG : ∀ k i, MeasurableSet (G k i)
  sub : ∀ k i, G k i ⊆ Z k i
  neZero : ∀ k i, μ (Z k i) ≠ 0
  shape_sub : ∀ k i, ∀ x ∈ G k i,
    V ((k : ℝ) + 3) ∩ (U : Set SL3) ⊆ shape (m k i) U x
  cover : ∀ k, μ (⋃ i, G k i)ᶜ = 0

/-! ## The reference index and the reference conditional measure -/

/-- The least index `k` with `x ∈ G k` (junk `0` if there is none). -/
def sel (G : ℕ → Set X3) (x : X3) : ℕ := by
  classical
  exact if h : ∃ k, x ∈ G k then Nat.find h else 0

/-- The conditional measure of `μ` restricted to `Z (sel G x)` with respect to the σ-algebra
`m (sel G x)`, at `x`. -/
def refKernel [StandardBorelSpace X3] (μ : Measure X3) [IsFiniteMeasure μ]
    (Z : ℕ → Set X3) (m : ℕ → MeasurableSpace X3)
    (G : ℕ → Set X3) (x : X3) : Measure X3 :=
  ProbabilityTheory.condExpKernel (μ.restrict (Z (sel G x))) (m (sel G x)) x

/-- The pushed conditional measure: a measure on `SL₃(ℝ)` carried by `U`. -/
def refPush [StandardBorelSpace X3] (U : Subgroup SL3) (μ : Measure X3) [IsFiniteMeasure μ]
    (Z : ℕ → Set X3) (m : ℕ → MeasurableSpace X3) (G : ℕ → Set X3) (x : X3) : Measure SL3 :=
  pushOrbit U x (refKernel μ Z m G x)

/-- The normalised pushed conditional measure: `ν_ref x (Box1 U) = 1`. -/
def nuLevel [StandardBorelSpace X3] (U : Subgroup SL3) (μ : Measure X3) [IsFiniteMeasure μ]
    (Z : ℕ → Set X3) (m : ℕ → MeasurableSpace X3) (G : ℕ → Set X3) (x : X3) : Measure SL3 :=
  (refPush U μ Z m G x (Box1 U))⁻¹ • refPush U μ Z m G x

/-! ## Patching -/

/-- The patched family: `ν x` agrees with the `k`-th reference measure on the annulus
`piece U k`. -/
def nuFull [StandardBorelSpace X3] (U : Subgroup SL3) (μ : Measure X3) [IsFiniteMeasure μ]
    (Z : ℕ → ℕ → Set X3) (m : ℕ → ℕ → MeasurableSpace X3) (G : ℕ → ℕ → Set X3)
    (x : X3) : Measure SL3 :=
  Measure.sum (fun k => (nuLevel U μ (Z k) (m k) (G k) x).restrict (piece U k))

end Work.EKLRelCross


namespace Work.EKLRelCross

open Work.EKLContract Work.EKLComp

/-! ## The two measure-theoretic inputs -/

/-- **Proportionality of conditional measures of two plaque algebras** (Pisa 5.17 + 6.17):
for two plaque algebras `(Z₁, 𝔪₁)`, `(Z₂, 𝔪₂)` the conditional measures of `μ` restricted to the
domains are proportional on the intersection of the atoms, a.e. on `Z₁ ∩ Z₂`. -/
def ProporPiece (U : Subgroup SL3) (μ : Measure X3) [StandardBorelSpace X3]
    [IsFiniteMeasure μ] : Prop :=
  ∀ (Z₁ Z₂ : Set X3) (𝔪₁ 𝔪₂ : SigAlg),
    IsPlaqueAlgebra U Z₁ 𝔪₁.m → IsPlaqueAlgebra U Z₂ 𝔪₂.m →
    ∀ᵐ x ∂μ, x ∈ Z₁ ∩ Z₂ →
      ProporOn (ProbabilityTheory.condExpKernel (mΩ := instMeasurableSpaceX3) (μ.restrict Z₁) 𝔪₁.m x)
        (ProbabilityTheory.condExpKernel (mΩ := instMeasurableSpaceX3) (μ.restrict Z₂) 𝔪₂.m x)
        (atom 𝔪₁.m x ∩ atom 𝔪₂.m x)

/-- **Positivity of the conditional measure of a plaque algebra on plaques** (Pisa 6.20). -/
def PosPiece (U : Subgroup SL3) (μ : Measure X3) [StandardBorelSpace X3]
    [IsFiniteMeasure μ] : Prop :=
  ∀ (Z : Set X3) (𝔪 : SigAlg), IsPlaqueAlgebra U Z 𝔪.m →
    ∀ (O : Set SL3), IsOpen O → (1 : SL3) ∈ O →
    ∀ᵐ x ∂(μ.restrict Z),
      0 < ProbabilityTheory.condExpKernel (mΩ := instMeasurableSpaceX3) (μ.restrict Z) 𝔪.m x
            ((fun g : SL3 => g • x) '' (O ∩ (U : Set SL3)))

end Work.EKLRelCross

namespace Work.EKLRelCross

open Work.EKLContract Work.EKLComp

/-- The conditional expectation of the bounded Borel function `f` on the domain `Z` with respect
to the plaque algebra `S`, evaluated at `x`. -/
noncomputable def condExpAt (S : SigAlg) (μ : Measure X3) (Z : Set X3) (f : X3 → ℝ)
    (x : X3) : ℝ :=
  MeasureTheory.condExp S.m (μ.restrict Z) f x

/-- The average of `f (· • x)` over the shape of `x`, with respect to the leafwise measure `W`. -/
noncomputable def shapeAvg (U : Subgroup SL3) (W : Measure SL3) (S : SigAlg) (x : X3)
    (f : X3 → ℝ) : ℝ :=
  (MeasureTheory.integral (W.restrict (shape S.m U x)) (fun u : SL3 => f (u • x))) /
    ((W (shape S.m U x)).toReal)

end Work.EKLRelCross

namespace Work.EKLRelCross

open Work.EKLContract Work.EKLComp

/-! ## The local-flower input, and the `condexp` field, as named `Prop`s

Both are stated as `def`s so that statements about them involve no delicate notation: this file
owns all the fragile elaboration (`condExp`, the `∫ u in s, · ∂μ` notation, the `Measure`/`Kernel`
instances bound by a local `MeasurableSpace X₃`). -/

/-- **The local flower input** (Pisa 6.7 + 6.9–6.15): at every point with free `U`-orbit and for
every radius `R > 0` there is a plaque algebra whose atoms contain the `R`-plaque of every point
of an open neighbourhood's free part.  This is the exact shape of
`Work.EKLRelCross.W.W_flower_local`. -/
def LocalFlowerInput (U : Subgroup SL3) : Prop :=
  ∀ x₀ : X3, (∀ u₁ ∈ U, ∀ u₂ ∈ U, u₁ • x₀ = u₂ • x₀ → u₁ = u₂) → ∀ R : ℝ, 0 < R →
    ∃ (Z : Set X3) (m : MeasurableSpace X3) (G O : Set X3),
      IsOpen O ∧ x₀ ∈ O ∧
      @MeasurableSet X3 Work.EKLContract.instMeasurableSpaceX3 G ∧ G ⊆ Z ∧
      IsPlaqueAlgebra U Z m ∧ x₀ ∈ G ∧
      (O ∩ {x : X3 | ∀ u ∈ U, u • x = x → u = 1} ⊆ G) ∧
      (∀ x ∈ G, V R ∩ (U : Set SL3) ⊆ shape m U x)

/-- **The `condexp` axiom of `IsLeafwise` for the patched family `nuFull`** (Pisa 6.3 (iv)), for a
single plaque algebra `(Z', m')` and one test function `f`. -/
def CondExpFieldAt (U : Subgroup SL3) (μ : Measure X3) [StandardBorelSpace X3]
    [IsFiniteMeasure μ] (Z : ℕ → ℕ → Set X3) (m : ℕ → ℕ → MeasurableSpace X3)
    (G : ℕ → ℕ → Set X3) (Z' : Set X3) (m' : MeasurableSpace X3) : Prop :=
  IsPlaqueAlgebra U Z' m' →
    ∀ f : X3 → ℝ, Measurable[Work.EKLContract.instMeasurableSpaceX3] f →
      (∃ C : ℝ, ∀ y : X3, |f y| ≤ C) →
      ∀ᵐ x ∂(μ.restrict Z'), MeasureTheory.condExp m' (μ.restrict Z') f x =
        (∫ u in shape m' U x, f (u • x) ∂(nuFull U μ Z m G x)) /
          ((nuFull U μ Z m G x) (shape m' U x)).toReal

/-- **The `condexp` axiom for all plaque algebras** — the eighth field of `IsLeafwise`. -/
def CondExpField (U : Subgroup SL3) (μ : Measure X3) [StandardBorelSpace X3]
    [IsFiniteMeasure μ] (Z : ℕ → ℕ → Set X3) (m : ℕ → ℕ → MeasurableSpace X3)
    (G : ℕ → ℕ → Set X3) : Prop :=
  ∀ (Z' : Set X3) (m' : MeasurableSpace X3), CondExpFieldAt U μ Z m G Z' m'

end Work.EKLRelCross
