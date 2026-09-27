import Mathlib
import ChallengeDeps
import Submission.Work.Measurable
import Submission.Commons.Measure.AddCircle.exists_add_add_eq_zero_of_third_lt

open InscribedRectangles
open Manifold Real MeasureTheory
open scoped ContDiff ENNReal Pointwise

set_option autoImplicit false
noncomputable section

namespace Submission.Configuration

/-- **The Kemperman endgame of Theorem 3.**  If the complement `Z` of the "good" set of angles
can be split as `Z = X ⊔ (-X)` with `X` open and no three elements of `X` summing to `0`, then `Z`
has measure at most `2/3` (equivalently the good set has measure at least `1/3`).

This is exactly the argument of Hugelmeyer's Theorem 3: an order relation `≺` on the translates of
a Möbius strip produces such an `X = {u : M ∩ u·M = ∅, M ≺ u·M}`; antisymmetry gives
`X ∩ (-X) = ∅`, totality gives `Z = X ∪ (-X)`, and transitivity gives the triple-product-free
condition. -/
theorem measureReal_le_two_thirds_of_split {Z X : Set UnitAddCircle}
    (hZmeas : MeasurableSet Z) (hXopen : IsOpen X)
    (hXsub : X ⊆ Z) (hZeq : Z = X ∪ (-X)) (hdisj : Disjoint X (-X))
    (htriple : ∀ a ∈ X, ∀ b ∈ X, ∀ c ∈ X, a + b + c ≠ 0) :
    volume.real Z ≤ 2 / 3 := by
  by_contra hcon
  push_neg at hcon
  have hXmeas : MeasurableSet X := hXopen.measurableSet
  have hnegmeas : MeasurableSet (-X) := hXmeas.neg
  have hXne : X.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne] at hZeq
    simp only [Set.neg_empty, Set.union_empty] at hZeq
    rw [hZeq] at hcon
    norm_num at hcon
  have hnegvol : volume.real (-X) = volume.real X := by
    rw [measureReal_def, measureReal_def, Measure.measure_neg]
  have hZvol : volume.real Z = volume.real X + volume.real (-X) := by
    rw [hZeq, measureReal_union hdisj hnegmeas (by finiteness) (by finiteness)]
  have hXgt : (1 / 3 : ℝ) < volume.real X := by
    rw [hnegvol] at hZvol
    linarith
  obtain ⟨a, ha, b, hb, c, hc, habc⟩ :=
    Commons.Measure.AddCircle.exists_add_add_eq_zero_of_third_lt hXopen hXne hXgt
  exact htriple a ha b hb c hc habc

/-- The complement of `GoodC γ` has measure at most `2/3` once it admits a "left half" `X` as
above. -/
theorem measureReal_compl_GoodC_le (γ : Circle → ℝ × ℝ)
    (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ∞ γ) {X : Set UnitAddCircle}
    (hXopen : IsOpen X) (hXsub : X ⊆ (GoodC γ)ᶜ)
    (hZeq : (GoodC γ)ᶜ = X ∪ (-X)) (hdisj : Disjoint X (-X))
    (htriple : ∀ a ∈ X, ∀ b ∈ X, ∀ c ∈ X, a + b + c ≠ 0) :
    volume.real ((GoodC γ)ᶜ) ≤ 2 / 3 :=
  measureReal_le_two_thirds_of_split (measurableSet_GoodC γ hγ).compl hXopen hXsub hZeq hdisj htriple

/-- **Theorem 1 from the order structure on the translates of the configuration Möbius strip.**

If the set of "non-intersecting" angles of `γ` admits an open half `X` such that
(i) `X ⊆ (GoodC γ)ᶜ`, (ii) `(GoodC γ)ᶜ = X ∪ (-X)`, (iii) `X ∩ (-X) = ∅`, and
(iv) `X` is free of triples summing to `0`, then `volume (X γ) ≥ 1/3`.

Property (i)–(iv) are exactly what the paper's total order `≺` on the configuration Möbius strips
provides, with `X = {u : M ∩ u·M = ∅, M ≺ u·M}`. -/
theorem theorem_1_of_order_split (γ : Circle → ℝ × ℝ)
    (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ∞ γ) {W : Set UnitAddCircle}
    (hXopen : IsOpen W) (hXsub : W ⊆ (GoodC γ)ᶜ)
    (hZeq : (GoodC γ)ᶜ = W ∪ (-W)) (hdisj : Disjoint W (-W))
    (htriple : ∀ a ∈ W, ∀ b ∈ W, ∀ c ∈ W, a + b + c ≠ 0) :
    volume (X γ) ≥ 1 / 3 := by
  have hGmeas : MeasurableSet (GoodC γ) := measurableSet_GoodC γ hγ
  have hle := measureReal_compl_GoodC_le γ hγ hXopen hXsub hZeq hdisj htriple
  have hsum : volume.real (GoodC γ) + volume.real ((GoodC γ)ᶜ) = 1 := by
    have h := measureReal_union (μ := (volume : Measure UnitAddCircle))
      (disjoint_compl_right (a := GoodC γ)) hGmeas.compl (by finiteness) (by finiteness)
    rw [Set.union_compl_self] at h
    have h1 : volume.real (Set.univ : Set UnitAddCircle) = 1 := by
      rw [measureReal_def, AddCircle.measure_univ]; simp
    rw [h1] at h
    exact h.symm
  refine theorem_1_of_GoodC_measure γ hγ ?_
  linarith

/-- **The precise residual topological input** (Hugelmeyer's Theorem 3 + the order of Theorem 2),
stated purely in terms of the curve `γ`: the set of angles `u` at which the configuration Möbius
strip `M` of `γ` is *disjoint* from its rotation `u·M` admits an open half `W` which is closed under
addition as long as the sum stays in `Z`, i.e. contains no `a, b, c` with `a + b + c = 0`.

Concretely `W = {u : M ∩ u·M = ∅, M ≺ u·M}` where `≺` is the total order on translates of `M`
coming from the total order on disjoint homologically nontrivial projective planes in `ℝ × ℝP³`. -/
def OrderSplitHolds (γ : Circle → ℝ × ℝ) : Prop :=
  ∃ W : Set UnitAddCircle, IsOpen W ∧ W ⊆ (GoodC γ)ᶜ ∧
    (GoodC γ)ᶜ = W ∪ (-W) ∧ Disjoint W (-W) ∧
    ∀ a ∈ W, ∀ b ∈ W, ∀ c ∈ W, a + b + c ≠ 0

/-- **Theorem 1 from the residual input.**  Under `OrderSplitHolds γ` (and smoothness of `γ`),
at least one third of all aspect ratios occur. -/
theorem theorem_1_of_OrderSplitHolds (γ : Circle → ℝ × ℝ)
    (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ∞ γ) (h : OrderSplitHolds γ) :
    volume (X γ) ≥ 1 / 3 := by
  obtain ⟨W, hWopen, hWsub, hZeq, hdisj, htriple⟩ := h
  exact theorem_1_of_order_split γ hγ hWopen hWsub hZeq hdisj htriple

end Submission.Configuration
