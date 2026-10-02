import Mathlib
import Submission.Work.Tubular.Defs
import Submission.Work.Tubular.Compact

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# The Thom space of the normal bundle is independent of the radius

For an embedding `E : V ↪ ℝ^N` of a compact smooth `8`-manifold, the Thom space of the normal
bundle is defined (`Work.Tubular.NormalThomSpace`) as the quotient `D_ε(ν)/S_ε(ν)` of the closed
`ε`-disc bundle by the `ε`-sphere bundle.  The *radius* `ε` is a choice, and the Thom space does not
depend on it: for `0 < a, b` the two quotients `D_a(ν)/S_a(ν)` and `D_b(ν)/S_b(ν)` are homeomorphic.

The homeomorphism is the obvious one: scale every normal vector by the positive constant `b / a`.
This scales the fibrewise norm by the same factor, so it carries the closed `a`-disc bundle onto the
closed `b`-disc bundle and the `a`-sphere bundle onto the `b`-sphere bundle (that is exactly what the
two positivity hypotheses `0 < a`, `0 < b` are needed for); being a homeomorphism of the normal
total space it descends to a homeomorphism of the quotients.

Contents:

* `Work.Tubular.normalScaleMap`, `..._proj`, `..._vec` — scaling the normal vector;
* `Work.Tubular.continuous_normalScaleMap`;
* `Work.Tubular.normalNorm_normalScaleMap` — the effect on the fibrewise norm;
* `Work.Tubular.normalTotalScaleHomeomorph` — the induced homeomorphism of `ν`;
* `Work.Tubular.normalDiscScaleHomeomorph` — its restriction to the disc bundles;
* `Work.Tubular.normalDiscScaleHomeomorph_mem_sphere` — and to the sphere bundles;
* `Work.Tubular.normalThomSpace_scale` — the homeomorphism of Thom spaces.
-/

open Set

open Work.ThomBordism.PontryaginThom (EmbeddingData)

namespace Work.Tubular

noncomputable section

variable {V : Work.ThomBordism.Man8} {N : ℕ}

/-! ## Scaling the normal bundle -/

/-- **Scaling a point of the normal total space by a real number `r`**: the base point is unchanged
and the normal vector is multiplied by `r`.  This is well defined because the normal space is a
subspace. -/
def normalScaleMap (E : EmbeddingData V N) (r : ℝ) (p : NormalTotal E) : NormalTotal E :=
  ⟨(p.1.1, r • p.1.2), Submodule.smul_mem (normalSpace E p.1.1) r p.2⟩

@[simp] theorem normalScaleMap_proj (E : EmbeddingData V N) (r : ℝ) (p : NormalTotal E) :
    (normalScaleMap E r p).proj = p.proj := rfl

@[simp] theorem normalScaleMap_vec (E : EmbeddingData V N) (r : ℝ) (p : NormalTotal E) :
    (normalScaleMap E r p).vec = r • p.vec := rfl

/-- Scaling the normal vector is continuous. -/
theorem continuous_normalScaleMap (E : EmbeddingData V N) (r : ℝ) :
    Continuous (normalScaleMap E r) := by
  apply Continuous.subtype_mk
  exact (continuous_subtype_val.fst).prodMk ((continuous_subtype_val.snd).const_smul r)

/-- **The fibrewise norm is multiplied by `r`** under the scaling `normalScaleMap E r`, for `r ≥ 0`.
This is the computation on which everything else rests: it is what makes the scaling carry the
`a`-disc bundle to the `r * a`-disc bundle and the `a`-sphere bundle to the `r * a`-sphere bundle. -/
theorem normalNorm_normalScaleMap (E : EmbeddingData V N) (r : ℝ) (hr : 0 ≤ r)
    (p : NormalTotal E) :
    normalNorm E (normalScaleMap E r p) = r * normalNorm E p := by
  simp only [normalScaleMap, normalNorm, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]

/-! ## Two elementary facts about `(b/a) * x` -/

/-- For `0 < r` and `r * a = b`, the inequality `r * x ≤ b` is equivalent to `x ≤ a`. -/
theorem mul_le_iff_of_pos_mul_eq {r a b x : ℝ} (hr : 0 < r) (hab : r * a = b) :
    r * x ≤ b ↔ x ≤ a := by
  rw [← hab]
  exact mul_le_mul_iff_of_pos_left hr

/-- For `0 < r` and `r * a = b`, the equation `r * x = b` is equivalent to `x = a`. -/
theorem mul_eq_iff_of_pos_mul_eq {r a b x : ℝ} (hr : 0 < r) (hab : r * a = b) :
    r * x = b ↔ x = a := by
  rw [← hab]
  exact ⟨fun h => mul_left_cancel₀ (ne_of_gt hr) h, fun h => by rw [h]⟩

/-! ## The scaling homeomorphism of the normal bundle -/

/-- **The normal total space is self-homeomorphic by scaling the normal vectors** by a nonzero
constant `r`; the normal space is a subspace, so the scaling is invertible with inverse the scaling
by `r⁻¹`. -/
def normalTotalScaleHomeomorph (E : EmbeddingData V N) (r : ℝ) (hr : r ≠ 0) :
    NormalTotal E ≃ₜ NormalTotal E where
  toFun := normalScaleMap E r
  invFun := normalScaleMap E r⁻¹
  left_inv := by
    intro p
    apply NormalTotal.ext
    simp [normalScaleMap, inv_smul_smul₀ hr]
  right_inv := by
    intro p
    apply NormalTotal.ext
    simp [normalScaleMap, smul_inv_smul₀ hr]
  continuous_toFun := continuous_normalScaleMap E r
  continuous_invFun := continuous_normalScaleMap E r⁻¹

/-- **The scaling by `b / a` carries the closed `a`-disc bundle onto the closed `b`-disc bundle**,
for `0 < a`, `0 < b`.  Hence the disc bundles of any two positive radii are homeomorphic. -/
def normalDiscScaleHomeomorph (E : EmbeddingData V N) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    NormalDiscSub E a ≃ₜ NormalDiscSub E b :=
  (normalTotalScaleHomeomorph E (b / a) (div_ne_zero (ne_of_gt hb) (ne_of_gt ha))).subtype
    (fun p => by
      show p ∈ normalClosedDiscSet E a ↔
        (normalTotalScaleHomeomorph E (b / a) _ p) ∈ normalClosedDiscSet E b
      rw [mem_normalClosedDiscSet, mem_normalClosedDiscSet]
      change normalNorm E p ≤ a ↔ normalNorm E (normalScaleMap E (b / a) p) ≤ b
      rw [normalNorm_normalScaleMap E (b / a) (le_of_lt (div_pos hb ha))]
      exact (mul_le_iff_of_pos_mul_eq (div_pos hb ha) (div_mul_cancel₀ b (ne_of_gt ha))).symm)

/-- The homeomorphism `normalDiscScaleHomeomorph` applied to a point of the disc bundle. -/
@[simp] theorem normalDiscScaleHomeomorph_apply (E : EmbeddingData V N) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (q : NormalDiscSub E a) :
    ((normalDiscScaleHomeomorph E ha hb q : NormalDiscSub E b) : NormalTotal E) =
      normalScaleMap E (b / a) q.1 := rfl

/-- **The scaling by `b / a` carries the `a`-sphere bundle onto the `b`-sphere bundle.**  On the
disc bundle, this says exactly that the `normalSphereInDisc` condition corresponds under
`normalDiscScaleHomeomorph`. -/
theorem normalDiscScaleHomeomorph_mem_sphere (E : EmbeddingData V N) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (q : NormalDiscSub E a) :
    normalDiscScaleHomeomorph E ha hb q ∈ normalSphereInDisc E b ↔
      q ∈ normalSphereInDisc E a := by
  rw [mem_normalSphereInDisc, mem_normalSphereInDisc]
  change normalNorm E (normalScaleMap E (b / a) q.1) = b ↔ normalNorm E q.1 = a
  rw [normalNorm_normalScaleMap E (b / a) (le_of_lt (div_pos hb ha))]
  exact mul_eq_iff_of_pos_mul_eq (div_pos hb ha) (div_mul_cancel₀ b (ne_of_gt ha))

/-! ## The induced homeomorphism of the Thom spaces -/

theorem normalThomSpace_scale {V : Work.ThomBordism.Man8} {N : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V N) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Nonempty (Work.Tubular.NormalThomSpace E a ≃ₜ Work.Tubular.NormalThomSpace E b) := by
  refine ⟨Homeomorph.Quotient.congr (normalDiscScaleHomeomorph E ha hb) ?_⟩
  intro x y
  show (x = y ∨ (x ∈ normalSphereInDisc E a ∧ y ∈ normalSphereInDisc E a)) ↔
    ((normalDiscScaleHomeomorph E ha hb) x = (normalDiscScaleHomeomorph E ha hb) y ∨
      ((normalDiscScaleHomeomorph E ha hb) x ∈ normalSphereInDisc E b ∧
       (normalDiscScaleHomeomorph E ha hb) y ∈ normalSphereInDisc E b))
  rw [normalDiscScaleHomeomorph_mem_sphere, normalDiscScaleHomeomorph_mem_sphere]
  constructor
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inl (by rw [h])
    · exact Or.inr ⟨h1, h2⟩
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inl ((normalDiscScaleHomeomorph E ha hb).injective h)
    · exact Or.inr ⟨h1, h2⟩

end

end Work.Tubular
