import Mathlib
import Submission.Work.ThomBordism.ambientClassDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# Vocabulary for the ambient localisation of the collapse class

This file supplies, for the target `Work.ThomBordism.collapseLocalisation_ambient`, the small
vocabulary used by its proof and by the delegated geometric pieces:

* `Work.ThomBordism.radialRescale E φ` — the **positive fibrewise radial rescaling** of the normal
  bundle determined by a function `φ` of the norm, `p ↦ ⟨proj p, φ (‖vec p‖) • vec p⟩`.  Both the
  Pontryagin–Thom blow-up `Work.Tubular.normalBlowUp E ε` and the radial retraction of `ν` onto a
  disc bundle are of this form (up to the domain), and *all* of them are homotopic to the identity
  through such rescalings as soon as `φ > 0`;
* `Work.ThomBordism.chartAffine E x` — the **ambient chart map** `p ↦ E.e p.1 + vec p - E.e x`
  (the affine "identity" of the tubular neighbourhood), together with the pointwise identity
  `chartAffine E x (C.inv y) = y - E.e x` on the tube (`chartAffine_inv`), which is the definitional
  content of `ambientStandardClass`.
-/

open CategoryTheory

namespace Work.ThomBordism

noncomputable section

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-- **The positive fibrewise radial rescaling of the normal bundle determined by `φ`**:
`p ↦ ⟨proj p, φ (‖vec p‖) • vec p⟩`.  It fixes the base point of every fibre, so it preserves the
zero section, and it preserves `ν∖0` whenever `φ > 0`. -/
noncomputable def radialRescale (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (φ : ℝ → ℝ) (p : Work.Tubular.NormalTotal E) : Work.Tubular.NormalTotal E :=
  ⟨((p : V.pt × Work.Tubular.Euc (8 + k)).1,
    φ (Work.Tubular.normalNorm E p) • (p : V.pt × Work.Tubular.Euc (8 + k)).2),
   Submodule.smul_mem (Work.Tubular.normalSpace E _) _ p.2⟩

@[simp] theorem radialRescale_coe (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (φ : ℝ → ℝ) (p : Work.Tubular.NormalTotal E) :
    ((radialRescale E φ p : Work.Tubular.NormalTotal E) : V.pt × Work.Tubular.Euc (8 + k))
      = ((p : V.pt × Work.Tubular.Euc (8 + k)).1,
          φ (Work.Tubular.normalNorm E p) • (p : V.pt × Work.Tubular.Euc (8 + k)).2) := rfl

theorem radialRescale_proj (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (φ : ℝ → ℝ) (p : Work.Tubular.NormalTotal E) :
    ((radialRescale E φ p : Work.Tubular.NormalTotal E) : V.pt × Work.Tubular.Euc (8 + k)).1
      = ((p : Work.Tubular.NormalTotal E) : V.pt × Work.Tubular.Euc (8 + k)).1 := rfl

/-- The norm of a radial rescaling. -/
theorem normalNorm_radialRescale (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (φ : ℝ → ℝ) (p : Work.Tubular.NormalTotal E) :
    Work.Tubular.normalNorm E (radialRescale E φ p)
      = |φ (Work.Tubular.normalNorm E p)| * Work.Tubular.normalNorm E p := by
  rw [Work.Tubular.normalNorm, radialRescale_coe, norm_smul, Real.norm_eq_abs]
  simp only [Work.Tubular.normalNorm]

/-- A radial rescaling with a positive coefficient preserves the punctured total space. -/
theorem radialRescale_mem_normalNonzero (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (φ : ℝ → ℝ) (hφpos : ∀ r, 0 ≤ r → 0 < φ r) {p : Work.Tubular.NormalTotal E}
    (hp : p ∈ Work.Tubular.normalNonzero E) : radialRescale E φ p ∈ Work.Tubular.normalNonzero E := by
  rw [Work.Tubular.mem_normalNonzero] at hp ⊢
  rw [normalNorm_radialRescale]
  exact mul_ne_zero (abs_ne_zero.mpr (ne_of_gt (hφpos _ (Work.Tubular.normalNorm_nonneg E p)))) hp

/-- The identity rescaling. -/
theorem radialRescale_one (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (p : Work.Tubular.NormalTotal E) : radialRescale E (fun _ => 1) p = p := by
  apply Subtype.ext
  rw [radialRescale_coe]
  simp

/-- **The ambient chart map** based at `E.e x`: the affine "identity" of the tubular neighbourhood,
`p ↦ E.e p.1 + vec p - E.e x`.  On the tube it is the translation `y ↦ y - E.e x`, which is the
definitional content of `ambientStandardClass`. -/
noncomputable def chartAffine (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (x : V.pt) (p : Work.Tubular.NormalTotal E) : Work.Tubular.Euc (8 + k) :=
  E.e ((p : V.pt × Work.Tubular.Euc (8 + k)).1) + (p : V.pt × Work.Tubular.Euc (8 + k)).2 - E.e x

@[simp] theorem chartAffine_apply (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (x : V.pt) (p : Work.Tubular.NormalTotal E) :
    chartAffine E x p
      = E.e ((p : V.pt × Work.Tubular.Euc (8 + k)).1)
        + (p : V.pt × Work.Tubular.Euc (8 + k)).2 - E.e x := rfl

/-- **The tube inverse identifies the chart map with the translation**: on the tube,
`chartAffine E x (C.inv y) = y - E.e x`. -/
theorem chartAffine_inv (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (x : V.pt) {y : Work.Tubular.Euc (8 + k)} (hy : y ∈ C.U) :
    chartAffine E x (C.inv y) = y - E.e x := by
  rw [chartAffine_apply, ← Work.Tubular.tubeMap, C.tubeMap_inv y hy]

/-- The chart map of the zero-section point over `x` is `0`. -/
theorem chartAffine_zeroSection (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (x : V.pt) : chartAffine E x (Work.Tubular.zeroSectionNormal E x) = 0 := by
  rw [chartAffine_apply, Work.Tubular.zeroSectionNormal]
  simp

end

end Work.ThomBordism
