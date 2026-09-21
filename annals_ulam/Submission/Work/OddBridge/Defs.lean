import Mathlib
import Submission.Work.OddBridge.KernelDefs
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.Assembly
import Submission.Work.OddVolterra.Bridge.momentEqs_of_volterra_tail
import Submission.Work.OddEnvelope.Main

/-!
# The bridge `OddBridge`: the three hypotheses of the tail bridge, as predicates

`Work.OddVolterra.Bridge.momentEqs_of_volterra_tail` turns three inputs -- the Abel inversion
`(arik)`, the two row identities `(t1)`, `(t2)`, and the smoothness of the two moment expressions
-- together with the support of the perturbation `h` into the two moment equations of Ryabogin's
odd case.  This file gives those three inputs names, so that the lemmas producing them can be
stated and delegated.
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

namespace Work.OddBridge

open Work.OddVolterra

noncomputable section

/-- The paper's `(arik)`: the Abel transform of the kernel `Kvec` is the right-hand side `Q`.
Stated on every compact `[a,c] ⊂ (0,1)`, which is the form consumed by the tail bridge. -/
def Harik (n : ℕ) (h x y : ℝ → ℝ) : Prop :=
  ∀ a c : ℝ, 0 < a → a ≤ c → c < 1 → ∀ s ∈ Set.Icc a c,
    (∫ σ in s..1,
        (Kvec n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ)) 0 / Real.sqrt (σ - s)) =
        (Q n h s) 0 ∧
    (∫ σ in s..1,
        (Kvec n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ)) 1 / Real.sqrt (σ - s)) =
        (Q n h s) 1

/-- The paper's `(t1)`: the `(n+1)`-st derivative of the first moment integral is the
inhomogeneity `E₁` plus the Abel transform of the first row of the kernel. -/
def RowF (n : ℕ) (h x y : ℝ → ℝ) : Prop :=
  ∀ a c : ℝ, 0 < a → a ≤ c → c < 1 → ∀ s ∈ Set.Icc a c,
    iteratedDeriv (n + 1)
        (fun u : ℝ => momentF n h x y (Work.OddEnvelope.envelopeProfile h x y) u) s =
      E1 n h s + ∫ σ in s..1,
        (Kvec n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ)) 0 / Real.sqrt (σ - s)

/-- The paper's `(t2)`: the `n`-th derivative of the centroid moment integral is the
inhomogeneity `E₂` plus the Abel transform of the second row of the kernel. -/
def RowH (n : ℕ) (h x y : ℝ → ℝ) : Prop :=
  ∀ a c : ℝ, 0 < a → a ≤ c → c < 1 → ∀ s ∈ Set.Icc a c,
    iteratedDeriv n
        (fun u : ℝ => momentH n h x y (Work.OddEnvelope.envelopeProfile h x y) u) s =
      E2 n h s + ∫ σ in s..1,
        (Kvec n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ)) 1 / Real.sqrt (σ - s)

/-- Smoothness of the first moment expression on `(0,1)`. -/
def ContF (n : ℕ) (h x y : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ (⊤ : ℕ∞)
    (fun u : ℝ =>
      momentF n h x y (Work.OddEnvelope.envelopeProfile h x y) u - momentRHS n u)
    (Set.Ioo 0 1)

/-- Smoothness of the centroid moment expression on `(0,1)`. -/
def ContH (n : ℕ) (h x y : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ (⊤ : ℕ∞)
    (fun u : ℝ => momentH n h x y (Work.OddEnvelope.envelopeProfile h x y) u)
    (Set.Ioo 0 1)

lemma harik_iff (n : ℕ) (h x y : ℝ → ℝ) : Harik n h x y ↔
    ∀ a c : ℝ, 0 < a → a ≤ c → c < 1 → ∀ s ∈ Set.Icc a c,
      (∫ σ in s..1,
          (Kvec n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ)) 0 / Real.sqrt (σ - s)) =
          (Q n h s) 0 ∧
      (∫ σ in s..1,
          (Kvec n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ)) 1 / Real.sqrt (σ - s)) =
          (Q n h s) 1 := Iff.rfl

lemma rowF_iff (n : ℕ) (h x y : ℝ → ℝ) : RowF n h x y ↔
    ∀ a c : ℝ, 0 < a → a ≤ c → c < 1 → ∀ s ∈ Set.Icc a c,
      iteratedDeriv (n + 1)
          (fun u : ℝ => momentF n h x y (Work.OddEnvelope.envelopeProfile h x y) u) s =
        E1 n h s + ∫ σ in s..1,
          (Kvec n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ)) 0 / Real.sqrt (σ - s) :=
  Iff.rfl

lemma rowH_iff (n : ℕ) (h x y : ℝ → ℝ) : RowH n h x y ↔
    ∀ a c : ℝ, 0 < a → a ≤ c → c < 1 → ∀ s ∈ Set.Icc a c,
      iteratedDeriv n
          (fun u : ℝ => momentH n h x y (Work.OddEnvelope.envelopeProfile h x y) u) s =
        E2 n h s + ∫ σ in s..1,
          (Kvec n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ)) 1 / Real.sqrt (σ - s) :=
  Iff.rfl

end

end Work.OddBridge
