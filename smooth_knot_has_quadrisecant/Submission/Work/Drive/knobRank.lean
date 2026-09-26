import Mathlib
import Submission.Work.Drive.rankPatchDefs

open scoped Matrix

/-!
# The "two knob" rank lemma

The rank computations for the patches of the bad locus all have the following shape: the
differential of a patch map `D : E →ₗ[ℝ] Space × Space` (or `Space × Space × Space`) contains,
in each of its two (resp. three) factors, the image of a common linear map `f : Space →ₗ[ℝ] Space`,
realised by explicit "knob" directions `dir i : Space → E`.  Since the factors are independent,
the rank of `D` is at least the sum of the ranks contributed by the knobs.

This file proves the two-factor version (used for the patches `P_a`, `P_b`, `P_m`).
-/

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

noncomputable section

/-- **Two independent knobs contribute additively to the rank.**  If `D` is a linear map into
`Space × Space` and `dir₁`, `dir₂` are directions realising, respectively, the second-factor-zero
part `(f u, 0)` and the first-factor-zero part `(0, f u)` of the image, then the rank of `D` is at
least twice the rank of `f`. -/
lemma two_knob_rank {E : Type*} [AddCommGroup E] [Module ℝ E]
    {D : E →ₗ[ℝ] Space × Space} {f : Space →ₗ[ℝ] Space} (dir₁ dir₂ : Space → E)
    (h₁ : ∀ u : Space, D (dir₁ u) = (f u, 0))
    (h₂ : ∀ u : Space, D (dir₂ u) = (0, f u)) :
    2 * Module.finrank ℝ (LinearMap.range f) ≤ Module.finrank ℝ (LinearMap.range D) := by
  let Ψ : ((LinearMap.range f) × (LinearMap.range f)) →ₗ[ℝ] (LinearMap.range D) :=
    { toFun := fun p =>
        ⟨(p.1.1, p.2.1), by
          obtain ⟨u, hu⟩ := p.1.2
          obtain ⟨v, hv⟩ := p.2.2
          refine ⟨dir₁ u + dir₂ v, ?_⟩
          rw [map_add, h₁ u, h₂ v, hu, hv]
          simp⟩
      map_add' := fun p q => by
        apply Subtype.ext
        simp
      map_smul' := fun c p => by
        apply Subtype.ext
        simp }
  have hΨ : Function.Injective Ψ := by
    intro p q hpq
    have h1 : (p.1.1, p.2.1) = (q.1.1, q.2.1) := by
      have := congrArg Subtype.val hpq
      simpa [Ψ] using this
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h1))
      (Subtype.ext (congrArg Prod.snd h1))
  have hle := LinearMap.finrank_le_finrank_of_injective (f := Ψ) hΨ
  rw [Module.finrank_prod] at hle
  linarith


section ThreeKnob

/-- **Three independent knobs contribute additively to the rank.**  If `D` is a linear map into
`Space × Space × Space` and `dirᵢ` are directions realising the three "one-factor" variations
`(fᵢ u, 0, 0)`, `(0, fᵢ u, 0)`, `(0, 0, fᵢ u)`, then the rank of `D` is at least the sum of the
ranks of the `fᵢ`. -/
lemma three_knob_rank {E : Type*} [AddCommGroup E] [Module ℝ E]
    {D : E →ₗ[ℝ] Space × Space × Space} {f₁ f₂ f₃ : Space →ₗ[ℝ] Space}
    (dir₁ dir₂ dir₃ : Space → E)
    (h₁ : ∀ u : Space, D (dir₁ u) = (f₁ u, 0, 0))
    (h₂ : ∀ u : Space, D (dir₂ u) = (0, f₂ u, 0))
    (h₃ : ∀ u : Space, D (dir₃ u) = (0, 0, f₃ u)) :
    Module.finrank ℝ (LinearMap.range f₁) + Module.finrank ℝ (LinearMap.range f₂) +
      Module.finrank ℝ (LinearMap.range f₃) ≤ Module.finrank ℝ (LinearMap.range D) := by
  let Ψ : ((LinearMap.range f₁) × (LinearMap.range f₂) × (LinearMap.range f₃)) →ₗ[ℝ]
      (LinearMap.range D) :=
    { toFun := fun p =>
        ⟨(p.1.1, p.2.1.1, p.2.2.1), by
          obtain ⟨u, hu⟩ := p.1.2
          obtain ⟨v, hv⟩ := p.2.1.2
          obtain ⟨w, hw⟩ := p.2.2.2
          refine ⟨dir₁ u + dir₂ v + dir₃ w, ?_⟩
          rw [map_add, map_add, h₁ u, h₂ v, h₃ w, hu, hv, hw]
          simp⟩
      map_add' := fun p q => by
        apply Subtype.ext
        simp
      map_smul' := fun c p => by
        apply Subtype.ext
        simp }
  have hΨ : Function.Injective Ψ := by
    intro p q hpq
    have h1 : (p.1.1, p.2.1.1, p.2.2.1) = (q.1.1, q.2.1.1, q.2.2.1) := by
      have := congrArg Subtype.val hpq
      simpa [Ψ] using this
    have e1 : p.1.1 = q.1.1 := by simpa using congrArg Prod.fst h1
    have e2 : p.2.1.1 = q.2.1.1 := by simpa using congrArg (fun z => z.2.1) h1
    have e3 : p.2.2.1 = q.2.2.1 := by simpa using congrArg (fun z => z.2.2) h1
    exact Prod.ext (Subtype.ext e1) (Prod.ext (Subtype.ext e2) (Subtype.ext e3))
  have hle := LinearMap.finrank_le_finrank_of_injective (f := Ψ) hΨ
  rw [Module.finrank_prod, Module.finrank_prod] at hle
  linarith

/-- The vector triple product expansion for `cross3`. -/
lemma cross3_cross3_eq (u v w : Space) :
    cross3 u (cross3 v w) = (inner ℝ u w) • v - (inner ℝ v u) • w := by
  have hinner1 : inner ℝ u w = WithLp.ofLp u ⬝ᵥ WithLp.ofLp w := by
    have h := EuclideanSpace.inner_toLp_toLp (𝕜 := ℝ) (WithLp.ofLp u) (WithLp.ofLp w)
    simp only [WithLp.toLp_ofLp, star_trivial] at h
    rw [h, dotProduct_comm]
  have hinner2 : inner ℝ v u = WithLp.ofLp v ⬝ᵥ WithLp.ofLp u := by
    have h := EuclideanSpace.inner_toLp_toLp (𝕜 := ℝ) (WithLp.ofLp v) (WithLp.ofLp u)
    simp only [WithLp.toLp_ofLp, star_trivial] at h
    rw [h, dotProduct_comm]
  apply WithLp.ofLp_injective 2
  simp only [cross3, WithLp.ofLp_toLp, WithLp.ofLp_sub, WithLp.ofLp_smul]
  rw [cross_cross_eq_smul_sub_smul', hinner1, hinner2]

/-- The cross product `u × w` is orthogonal to its second argument. -/
lemma inner_cross3_right (u w : Space) : inner ℝ (cross3 u w) w = 0 := by
  rw [cross3_anticomm, inner_neg_left, neg_eq_zero, cross3]
  exact Commons.Analysis.CrossProduct.inner_cross3_self_left (u := w) (v := u)

/-- The linear map `u ↦ w × (u × d)`. -/
def crossCross (w d : Space) : Space →ₗ[ℝ] Space where
  toFun := fun u => cross3 w (cross3 u d)
  map_add' := fun u v => by
    rw [cross3_add_left, cross3_add_right]
  map_smul' := fun c u => by
    rw [cross3_smul_left, cross3_smul_right]
    rfl

@[simp] lemma crossCross_apply (w d u : Space) :
    crossCross w d u = cross3 w (cross3 u d) := rfl

lemma crossCross_eq {w d : Space} (hwd : inner ℝ w d = 0) (u : Space) :
    crossCross w d u = -(inner ℝ u w) • d := by
  rw [crossCross_apply, cross3_cross3_eq, hwd, zero_smul, zero_sub, neg_smul]

/-- For nonzero `w` orthogonal to `d ≠ 0`, the map `u ↦ w × (u × d)` has rank one: its image is
the line spanned by `d`. -/
lemma finrank_range_crossCross {w d : Space} (hw : w ≠ 0) (hd : d ≠ 0)
    (hwd : inner ℝ w d = 0) :
    Module.finrank ℝ (LinearMap.range (crossCross w d)) = 1 := by
  have hwne : inner ℝ w w ≠ 0 := inner_self_ne_zero.mpr hw
  have hle : LinearMap.range (crossCross w d) ≤ ℝ ∙ d := by
    rintro _ ⟨u, rfl⟩
    rw [crossCross_eq hwd, Submodule.mem_span_singleton]
    exact ⟨-(inner ℝ u w), by rw [neg_smul]⟩
  have hmem : d ∈ LinearMap.range (crossCross w d) := by
    refine ⟨(-(inner ℝ w w)⁻¹) • w, ?_⟩
    rw [crossCross_eq hwd, real_inner_smul_left,
      show -((- (inner ℝ w w)⁻¹) * inner ℝ w w) = (1 : ℝ) by
        rw [neg_mul, neg_neg, inv_mul_cancel₀ hwne]]
    exact one_smul ℝ d
  have heq : LinearMap.range (crossCross w d) = ℝ ∙ d :=
    le_antisymm hle ((Submodule.span_singleton_le_iff_mem d _).mpr hmem)
  rw [heq, finrank_span_singleton hd]

end ThreeKnob

end

end Work.Drive
