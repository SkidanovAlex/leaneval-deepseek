import Mathlib
import Submission.Work.ThomBordism.Transversality.BoxFamily.Defs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The box point: `box hF y s` has vertical coordinate `Φ y + s`

This file proves the two elementary facts about `BoxFamily.box`:

* `box_Phi` (on `boxSet`): `Φ (box hF y s) = Φ y + s`;
* `box_zero`: `box hF y 0 = y`.

Both are read off from `IsSubmersionAtOfComplement.writtenInCharts`.
-/

open scoped Manifold ContDiff
open Function Set Topology Manifold Filter

set_option autoImplicit false

namespace Work.ThomBordism.Transversality.BoxFamily

noncomputable section

open Work.ThomBordism.Transversality (CoreTarget)

variable {n k : ℕ} {X : CoreTarget n k} {y₀ : X.E} {F : Type*} [NormedAddCommGroup F]
  [NormedSpace ℝ F] {y : X.E} {s : EuclideanSpace ℝ (Fin k)}

/-- The value of the domain chart at a point of its source lies in the target of the extended
chart. -/
theorem domChart_mem_extend_target
    (hF : IsSubmersionAtOfComplement F (𝓡 n) (𝓡 k) ((⊤ : ℕ∞) : WithTop ℕ∞) X.Φ y₀)
    (hy : y ∈ hF.domChart.source) :
    hF.domChart y ∈ (hF.domChart.extend (𝓡 n)).target := by
  have h := (hF.domChart.extend (𝓡 n)).map_source (by rwa [extend_domChart_source])
  rwa [extend_domChart_coe] at h

/-- **The identity of `writtenInCharts` in the plain charts of `hF`**: for `y` in the source of the
domain chart, `codChart (Φ y) = (equiv (domChart y)).1`. -/
theorem codChart_Phi_eq
    (hF : IsSubmersionAtOfComplement F (𝓡 n) (𝓡 k) ((⊤ : ℕ∞) : WithTop ℕ∞) X.Φ y₀)
    (hy : y ∈ hF.domChart.source) :
    hF.codChart (X.Φ y) = (hF.equiv (hF.domChart y)).1 := by
  have h := hF.writtenInCharts (domChart_mem_extend_target hF hy)
  rw [extend_codChart_coe] at h
  simp only [Function.comp_apply] at h
  have hleft : (hF.domChart.extend (𝓡 n)).symm (hF.domChart y) = y := by
    have := (hF.domChart.extend (𝓡 n)).left_inv (by rwa [extend_domChart_source])
    rwa [extend_domChart_coe] at this
  rw [hleft] at h
  exact h

/-- `boxCoord` at `s = 0` is the image of `y` under the domain chart. -/
theorem boxCoord_zero
    (hF : IsSubmersionAtOfComplement F (𝓡 n) (𝓡 k) ((⊤ : ℕ∞) : WithTop ℕ∞) X.Φ y₀)
    (hy : y ∈ hF.domChart.source) :
    boxCoord hF y 0 = hF.domChart y := by
  rw [boxCoord, add_zero, codChart_Phi_eq hF hy]
  exact hF.equiv.symm_apply_apply (hF.domChart y)

/-- The base point of the construction belongs to `boxSet`. -/
theorem boxSet_self
    (hF : IsSubmersionAtOfComplement F (𝓡 n) (𝓡 k) ((⊤ : ℕ∞) : WithTop ℕ∞) X.Φ y₀) :
    (y₀, (0 : EuclideanSpace ℝ (Fin k))) ∈ boxSet hF := by
  refine ⟨hF.mem_domChart_source, ?_, ?_⟩
  · simpa using hF.mem_codChart_source
  · rw [boxCoord_zero hF hF.mem_domChart_source]
    exact domChart_mem_extend_target hF hF.mem_domChart_source

/-- **The exact vertical translate identity**: on `boxSet`, the point `box hF y s` has vertical
coordinate `Φ y + s`. -/
theorem box_Phi
    (hF : IsSubmersionAtOfComplement F (𝓡 n) (𝓡 k) ((⊤ : ℕ∞) : WithTop ℕ∞) X.Φ y₀)
    (hy : (y, s) ∈ boxSet hF) :
    X.Φ (box hF y s) = X.Φ y + s := by
  have h2 : X.Φ y + s ∈ hF.codChart.source := hy.2.1
  have h3 : boxCoord hF y s ∈ (hF.domChart.extend (𝓡 n)).target := hy.2.2
  have hkey : hF.codChart (X.Φ (box hF y s)) = hF.codChart (X.Φ y + s) := by
    change hF.codChart (X.Φ ((hF.domChart.extend (𝓡 n)).symm (boxCoord hF y s))) =
      hF.codChart (X.Φ y + s)
    have hwr := hF.writtenInCharts h3
    rw [extend_codChart_coe] at hwr
    simp only [Function.comp_apply] at hwr
    have hcoord : hF.equiv (boxCoord hF y s) =
        (hF.codChart (X.Φ y + s), (hF.equiv (hF.domChart y)).2) := by
      rw [boxCoord]
      exact hF.equiv.apply_symm_apply _
    rw [hcoord] at hwr
    simpa using hwr
  have hmem : box hF y s ∈ hF.domChart.source := by
    have := (hF.domChart.extend (𝓡 n)).map_target h3
    rwa [extend_domChart_source] at this
  exact hF.codChart.injOn (hF.source_subset_preimage_source hmem) h2 hkey

/-- **`box hF y 0 = y`** on the source of the domain chart. -/
theorem box_zero
    (hF : IsSubmersionAtOfComplement F (𝓡 n) (𝓡 k) ((⊤ : ℕ∞) : WithTop ℕ∞) X.Φ y₀)
    (hy : y ∈ hF.domChart.source) : box hF y 0 = y := by
  rw [box, boxCoord_zero hF hy]
  have := (hF.domChart.extend (𝓡 n)).left_inv (by rwa [extend_domChart_source])
  rwa [extend_domChart_coe] at this

end

end Work.ThomBordism.Transversality.BoxFamily
