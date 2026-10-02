import Mathlib
import Submission.Work.ThomBordism.Transversality.Basic
import Submission.Work.ThomBordism.Transversality.TransversalApproximation.chi

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The cut-off `χt = χ * (β ∘ F)` of the transversality homotopy theorem

Step 1 of the proof of `TransversalApproximation`: given a smooth `χ : M → [0,1]` vanishing near
`∂M`, we shrink it (by multiplying by a bump of `Φ ∘ F` supported in the region where `Φ` is a
submersion) so that the perturbation constructed in `perturbation.lean` only uses vertical
families attached to points where `Φ` *is* a submersion.

The construction uses that `F '' tsupport χ` is compact and meets the closed set where `Φ` fails to
be a submersion only away from the core, hence with `‖Φ‖` bounded below by some `δ₀ > 0` there.
-/

open scoped Manifold ContDiff Topology MeasureTheory
open Function Set Topology Manifold Filter

set_option autoImplicit false

namespace Work.ThomBordism.Transversality.TransversalApproximation

noncomputable section

open Work.ThomBordism.Transversality (CoreTarget)

variable {n k : ℕ}

/-- **The cut-off `χt`.**  For `F : M → X.E` smooth and `χ : M → [0,1]` smooth vanishing near `∂M`,
there is a smooth `χt : M → [0,1]`, vanishing near `∂M`, with

* `χt x = χ x` whenever `Φ (F x) = 0`, and
* `Φ` is a submersion at `F x` for every `x ∈ tsupport χt`. -/
theorem exists_chiTilde
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E' H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M] [CompactSpace M] [T2Space M]
    (X : CoreTarget n k) (F : M → X.E)
    (hF : ContMDiff I (𝓡 n) ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (χ : M → ℝ) (hχ : ContMDiff I (𝓘(ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1)
    (hχbd : ∃ V : Set M, IsOpen V ∧ I.boundary M ⊆ V ∧ ∀ x ∈ V, χ x = 0) :
    ∃ χt : M → ℝ, ContMDiff I (𝓘(ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) χt ∧ (∀ x, 0 ≤ χt x) ∧
      (∀ x, χt x ≤ 1) ∧
      (∃ V : Set M, IsOpen V ∧ I.boundary M ⊆ V ∧ ∀ x ∈ V, χt x = 0) ∧
      (∀ x, X.Φ (F x) = 0 → χt x = χ x) ∧
      (∀ x ∈ tsupport χt, IsSubmersionAt (𝓡 n) (𝓡 k) ((⊤ : ℕ∞) : WithTop ℕ∞) X.Φ (F x)) := by
  classical
  have hV0open : IsOpen {y : X.E | IsSubmersionAt (𝓡 n) (𝓡 k) ((⊤ : ℕ∞) : WithTop ℕ∞) X.Φ y} :=
    isOpen_isSubmersionAt
  have hC : IsCompact (F '' tsupport χ ∩ {y : X.E | ¬ IsSubmersionAt (𝓡 n) (𝓡 k)
      ((⊤ : ℕ∞) : WithTop ℕ∞) X.Φ y}) :=
    ((isClosed_tsupport χ).isCompact.image hF.continuous).inter_right hV0open.isClosed_compl
  have hpos : ∀ y ∈ F '' tsupport χ ∩ {y : X.E | ¬ IsSubmersionAt (𝓡 n) (𝓡 k)
      ((⊤ : ℕ∞) : WithTop ℕ∞) X.Φ y}, (0 : ℝ) < ‖X.Φ y‖ := by
    rintro y ⟨-, hy⟩
    exact norm_pos_iff.mpr fun h0 => hy (X.isSubmersionAt_Φ y h0)
  obtain ⟨δ0, hδ0pos, hδ0le⟩ := hC.exists_forall_le'
    ((continuous_norm.comp X.contMDiff_Φ.continuous).continuousOn) hpos
  obtain ⟨β, hβ, hβ0, hβ1, hβone, hβzero⟩ := exists_beta X hδ0pos
  refine ⟨fun x => χ x * β (F x), hχ.mul (hβ.comp hF), ?_, ?_, ?_, ?_, ?_⟩
  · intro x; exact mul_nonneg (hχ0 x) (hβ0 (F x))
  · intro x
    have := mul_le_mul (hχ1 x) (hβ1 (F x)) (hβ0 (F x)) (by norm_num : (0:ℝ) ≤ 1)
    simpa using this
  · obtain ⟨V, hVopen, hVbd, hV0⟩ := hχbd
    exact ⟨V, hVopen, hVbd, fun x hx => by
      show χ x * β (F x) = 0
      rw [hV0 x hx, zero_mul]⟩
  · intro x hx
    have hb1 : β (F x) = 1 := hβone (F x) (by rw [hx, norm_zero]; positivity)
    show χ x * β (F x) = χ x
    rw [hb1, mul_one]
  · intro x hx
    have hclosed : IsClosed {y : M | ‖X.Φ (F y)‖ ≤ δ0 / 3} :=
      isClosed_le (continuous_norm.comp (X.contMDiff_Φ.continuous.comp hF.continuous))
        continuous_const
    have hsub : {y : M | (fun z => χ z * β (F z)) y ≠ 0} ⊆ {y : M | ‖X.Φ (F y)‖ ≤ δ0 / 3} := by
      intro y hy
      have hbne : β (F y) ≠ 0 := by
        intro h0
        exact hy (by show χ y * β (F y) = 0; rw [h0, mul_zero])
      have hlt : ‖X.Φ (F y)‖ < δ0 / 3 := by
        by_contra hcon
        exact hbne (hβzero (F y) (not_lt.mp hcon))
      exact le_of_lt hlt
    have htsupp : tsupport (fun z => χ z * β (F z)) ⊆ {y : M | ‖X.Φ (F y)‖ ≤ δ0 / 3} :=
      closure_minimal hsub hclosed
    have hxsub : x ∈ tsupport χ := tsupport_mul_subset_left hx
    have hle : ‖X.Φ (F x)‖ ≤ δ0 / 3 := htsupp hx
    by_contra hnot
    exact absurd (hδ0le (F x) ⟨mem_image_of_mem F hxsub, hnot⟩)
      (not_le.mpr (lt_of_le_of_lt hle (by linarith)))

end

end Work.ThomBordism.Transversality.TransversalApproximation
