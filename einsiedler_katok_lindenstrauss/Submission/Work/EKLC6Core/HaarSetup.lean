import Mathlib
import Submission.Work.EKLContract.Defs

/-!
# Haar-measure infrastructure for closed subgroups of `SL₃(ℝ)`

This module collects the (mostly topological) infrastructure needed to put a Haar measure on a
closed subgroup `H ≤ SL₃(ℝ)` and to compare it with its conjugates by an element `a` normalising
`H`.  Nothing here mentions any particular subgroup: every statement is about an arbitrary
`H : Subgroup SL3`.

Contents

* `SL3_locallyCompactSpace`, `SL3_secondCountableTopology` (both inherited from the ambient
  matrix space, which is a finite product of copies of `ℝ`);
* `subgroup_locallyCompactSpace`, `subgroup_secondCountableTopology` for a closed subgroup;
* `conjMulEquiv H a hn hn'` — conjugation by `a` as a group isomorphism `H ≃* H`, and its
  continuous version `conjContinuousMulEquiv H a hn hn' : H ≃ₜ* H`;
* the measure-theoretic bookkeeping lemmas
  `subtype_preimage_conj_image`, `subtype_preimage_mul_left_image`, `subtype_preimage_compl`,
  `measurableSet_conjImage`.
-/

noncomputable section

open MeasureTheory Topology

set_option linter.unusedVariables false

namespace Work.EKLC6Core

open Work.EKLContract

/-! ## Local compactness and second countability -/

/-- `SL₃(ℝ)` is locally compact: it is a closed subspace of the finite-dimensional real vector
space `Matrix (Fin 3) (Fin 3) ℝ ≅ ℝ⁹`. -/
theorem SL3_locallyCompactSpace : LocallyCompactSpace SL3 := by
  have : LocallyCompactSpace (Matrix (Fin 3) (Fin 3) ℝ) :=
    inferInstanceAs (LocallyCompactSpace (Fin 3 → Fin 3 → ℝ))
  exact (Matrix.SpecialLinearGroup.isClosedEmbedding_val (n := Fin 3) (R := ℝ)).locallyCompactSpace

/-- `SL₃(ℝ)` is second countable. -/
theorem SL3_secondCountableTopology : SecondCountableTopology SL3 := by
  have : SecondCountableTopology (Matrix (Fin 3) (Fin 3) ℝ) :=
    inferInstanceAs (SecondCountableTopology (Fin 3 → Fin 3 → ℝ))
  exact (Matrix.SpecialLinearGroup.isClosedEmbedding_val (n := Fin 3) (R := ℝ)).isInducing.secondCountableTopology

/-- A closed subgroup of `SL₃(ℝ)` is locally compact. -/
theorem subgroup_locallyCompactSpace {H : Subgroup SL3} (hH : IsClosed (H : Set SL3)) :
    LocallyCompactSpace H := by
  have : LocallyCompactSpace SL3 := SL3_locallyCompactSpace
  exact hH.locallyCompactSpace

/-- A closed subgroup of `SL₃(ℝ)` is second countable. -/
theorem subgroup_secondCountableTopology {H : Subgroup SL3} (hH : IsClosed (H : Set SL3)) :
    SecondCountableTopology H := by
  have : SecondCountableTopology SL3 := SL3_secondCountableTopology
  exact hH.isClosedEmbedding_subtypeVal.isInducing.secondCountableTopology

/-! ## Conjugation by a normalising element -/

/-- Conjugation by an element `a` which normalises `H`, as a group isomorphism `H ≃* H`.
The hypothesis `hn` witnesses `a H a⁻¹ ⊆ H` and `hn'` witnesses `a⁻¹ H a ⊆ H`. -/
def conjMulEquiv (H : Subgroup SL3) (a : SL3)
    (hn : ∀ u ∈ H, a * u * a⁻¹ ∈ H) (hn' : ∀ u ∈ H, a⁻¹ * u * a ∈ H) : H ≃* H where
  toFun h := ⟨a * (h : SL3) * a⁻¹, hn h h.2⟩
  invFun h := ⟨a⁻¹ * (h : SL3) * a, hn' h h.2⟩
  left_inv h := by ext; simp only [Subgroup.coe_mul]; group
  right_inv h := by ext; simp only [Subgroup.coe_mul]; group
  map_mul' x y := by ext; simp only [Subgroup.coe_mul]; group

/-- The underlying element of `conjMulEquiv H a hn hn' h` is `a * h * a⁻¹`. -/
lemma conjMulEquiv_apply (H : Subgroup SL3) (a : SL3)
    (hn : ∀ u ∈ H, a * u * a⁻¹ ∈ H) (hn' : ∀ u ∈ H, a⁻¹ * u * a ∈ H) (h : H) :
    (conjMulEquiv H a hn hn' h : SL3) = a * (h : SL3) * a⁻¹ := rfl

lemma continuous_conjMulEquiv (H : Subgroup SL3) (a : SL3)
    (hn : ∀ u ∈ H, a * u * a⁻¹ ∈ H) (hn' : ∀ u ∈ H, a⁻¹ * u * a ∈ H) :
    Continuous (conjMulEquiv H a hn hn') := by
  apply Continuous.subtype_mk
  fun_prop

lemma continuous_conjMulEquiv_symm (H : Subgroup SL3) (a : SL3)
    (hn : ∀ u ∈ H, a * u * a⁻¹ ∈ H) (hn' : ∀ u ∈ H, a⁻¹ * u * a ∈ H) :
    Continuous (conjMulEquiv H a hn hn').symm := by
  apply Continuous.subtype_mk
  fun_prop

/-- Conjugation by a normalising element, as a topological group isomorphism. -/
def conjContinuousMulEquiv (H : Subgroup SL3) (a : SL3)
    (hn : ∀ u ∈ H, a * u * a⁻¹ ∈ H) (hn' : ∀ u ∈ H, a⁻¹ * u * a ∈ H) : H ≃ₜ* H :=
  ContinuousMulEquiv.mk (conjMulEquiv H a hn hn')
    (continuous_conjMulEquiv H a hn hn') (continuous_conjMulEquiv_symm H a hn hn')

/-! ## Preimages of the basic sets -/

/-- `Subtype.val ⁻¹' (a · a⁻¹) '' s` is the preimage of `Subtype.val ⁻¹' s` under the *inverse*
conjugation `h ↦ a⁻¹ h a`.  (The inverse appears because `H ∋ h ↦ h` is inside the image, so the
membership `h ∈ (a · a⁻¹) '' s` is `a⁻¹ h a ∈ s`.) -/
lemma subtype_preimage_conj_image (H : Subgroup SL3) (a : SL3)
    (hn : ∀ u ∈ H, a * u * a⁻¹ ∈ H) (hn' : ∀ u ∈ H, a⁻¹ * u * a ∈ H) (s : Set SL3) :
    (Subtype.val ⁻¹' ((fun g : SL3 => a * g * a⁻¹) '' s))
      = (fun h : H => (⟨a⁻¹ * (h : SL3) * a, hn' h h.2⟩ : H)) ⁻¹' (Subtype.val ⁻¹' s) := by
  ext h
  constructor
  · rintro ⟨k, hk, hk'⟩
    show a⁻¹ * (h : SL3) * a ∈ s
    rw [← hk']
    have : a⁻¹ * (a * k * a⁻¹) * a = k := by group
    rwa [this]
  · intro hh
    exact ⟨a⁻¹ * (h : SL3) * a, hh, by group⟩

/-- `Subtype.val ⁻¹' (u ·) '' s` is the preimage of `Subtype.val ⁻¹' s` under left multiplication
by `u⁻¹` in `H`. -/
lemma subtype_preimage_mul_left_image {H : Subgroup SL3} {u : SL3} (hu : u ∈ H) (s : Set SL3) :
    (Subtype.val ⁻¹' ((fun g : SL3 => u * g) '' s))
      = (fun h : H => (⟨u, hu⟩ : H)⁻¹ * h) ⁻¹' (Subtype.val ⁻¹' s) := by
  ext h
  constructor
  · rintro ⟨k, hk, hk'⟩
    show ((⟨u, hu⟩ : H)⁻¹ * h : SL3) ∈ s
    have hcoe : ((⟨u, hu⟩ : H)⁻¹ * h : SL3) = u⁻¹ * (h : SL3) := by simp
    rw [hcoe, ← hk']
    have : u⁻¹ * (u * k) = k := by group
    rwa [this]
  · intro hh
    show ∃ k : SL3, k ∈ s ∧ u * k = (h : SL3)
    have hh' : ((⟨u, hu⟩ : H)⁻¹ * h : SL3) ∈ s := hh
    have hcoe : ((⟨u, hu⟩ : H)⁻¹ * h : SL3) = u⁻¹ * (h : SL3) := by simp
    rw [hcoe] at hh'
    exact ⟨u⁻¹ * (h : SL3), hh', by group⟩

/-- The preimage of the complement of `H` is empty. -/
lemma subtype_preimage_compl (H : Subgroup SL3) :
    (Subtype.val : H → SL3) ⁻¹' ((H : Set SL3))ᶜ = ∅ := by
  ext h
  simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false, not_not]
  exact h.2

/-- The image of a measurable set under conjugation by a fixed element is measurable. -/
lemma measurableSet_conjImage (a : SL3) {s : Set SL3} (hs : MeasurableSet s) :
    MeasurableSet ((fun g : SL3 => a * g * a⁻¹) '' s) := by
  have hset : (fun g : SL3 => a * g * a⁻¹) '' s = (fun g : SL3 => a⁻¹ * g * a) ⁻¹' s := by
    ext g
    constructor
    · rintro ⟨h, hh, rfl⟩
      show a⁻¹ * (a * h * a⁻¹) * a ∈ s
      have : a⁻¹ * (a * h * a⁻¹) * a = h := by group
      rwa [this]
    · intro hg
      refine ⟨a⁻¹ * g * a, hg, ?_⟩
      show a * (a⁻¹ * g * a) * a⁻¹ = g
      group
  rw [hset]
  exact hs.preimage (by fun_prop)

/-- The image of a measurable set under left translation by a fixed element is measurable. -/
lemma measurableSet_mul_left_image (u : SL3) {s : Set SL3} (hs : MeasurableSet s) :
    MeasurableSet ((fun g : SL3 => u * g) '' s) := by
  have hset : (fun g : SL3 => u * g) '' s = (fun g : SL3 => u⁻¹ * g) ⁻¹' s := by
    ext g
    constructor
    · rintro ⟨h, hh, rfl⟩
      show u⁻¹ * (u * h) ∈ s
      have : u⁻¹ * (u * h) = h := by group
      rwa [this]
    · intro hg
      exact ⟨u⁻¹ * g, hg, by group⟩
  rw [hset]
  exact hs.preimage (by fun_prop)

end Work.EKLC6Core
