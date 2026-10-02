import Mathlib
import Submission.Work.ThomBordism.Transversality.BoxFamily.Validity

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Smoothness of the box family

`contMDiffOn_boxCoord`: `boxCoord hF` is `C^∞` on `boxSet hF` — it is the composite
`(domChart.extend 𝓡n).symm ∘ (codChart ∘ (Φ + ·), (equiv ∘ domChart)₂)`, and each factor is smooth
on the region where `boxSet` says its arguments live (`contMDiffOn_extend_symm` for the inverse of
the chart, `contMDiffOn_of_mem_maximalAtlas` for `codChart`, `ContinuousLinearMap.contMDiff` for
`equiv`).

`contMDiffOn_box`: hence `(y, s) ↦ box hF y s` is `C^∞` on `boxSet hF`.  This is the smoothness
input of step 2 of the transversality homotopy theorem; the gluing with the identity (which makes
the family global) happens in the assembly, where only the smoothness of `box` on the *open* set
`boxSet hF` is used.
-/

open scoped Manifold ContDiff
open Function Set Topology Manifold Filter

set_option autoImplicit false

namespace Work.ThomBordism.Transversality.BoxFamily

noncomputable section

open Work.ThomBordism.Transversality (CoreTarget)

variable {n k : ℕ} {X : CoreTarget n k} {y₀ : X.E} {F : Type*} [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- `boxCoord` is smooth on `boxSet`. -/
theorem contMDiffOn_boxCoord
    (hF : IsSubmersionAtOfComplement F (𝓡 n) (𝓡 k) ((⊤ : ℕ∞) : WithTop ℕ∞) X.Φ y₀) :
    ContMDiffOn ((𝓡 n).prod (𝓡 k)) (𝓡 n) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : X.E × EuclideanSpace ℝ (Fin k) => boxCoord hF p.1 p.2) (boxSet hF) := by
  have hT : ContMDiff ((𝓡 n).prod (𝓡 k)) (𝓡 k) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : X.E × EuclideanSpace ℝ (Fin k) => X.Φ p.1 + p.2) :=
    (X.contMDiff_Φ.comp contMDiff_fst).add contMDiff_snd
  have h1 : ContMDiffOn ((𝓡 n).prod (𝓡 k)) (𝓡 k) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : X.E × EuclideanSpace ℝ (Fin k) => hF.codChart (X.Φ p.1 + p.2))
      (boxSet hF) :=
    (contMDiffOn_of_mem_maximalAtlas hF.codChart_mem_maximalAtlas).comp
      (hT.contMDiffOn.mono (Set.subset_univ _)) (fun p hp => hp.2.1)
  have hφ : ContMDiffOn ((𝓡 n).prod (𝓡 k)) (𝓡 n) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : X.E × EuclideanSpace ℝ (Fin k) => hF.domChart p.1) (boxSet hF) :=
    (contMDiffOn_of_mem_maximalAtlas hF.domChart_mem_maximalAtlas).comp
      (contMDiff_fst.contMDiffOn.mono (Set.subset_univ _)) (fun p hp => hp.1)
  have h2 : ContMDiffOn ((𝓡 n).prod (𝓡 k))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin k) × F)) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : X.E × EuclideanSpace ℝ (Fin k) => hF.equiv (hF.domChart p.1)) (boxSet hF) :=
    (hF.equiv : EuclideanSpace ℝ (Fin n) →L[ℝ] (EuclideanSpace ℝ (Fin k) × F)).contMDiff.comp_contMDiffOn hφ
  have h2b : ContMDiffOn ((𝓡 n).prod (𝓡 k)) (𝓘(ℝ, F)) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : X.E × EuclideanSpace ℝ (Fin k) => (hF.equiv (hF.domChart p.1)).2)
      (boxSet hF) :=
    (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin k)) F).contMDiff.comp_contMDiffOn h2
  have hpair := h1.prodMk_space h2b
  exact (hF.equiv.symm : (EuclideanSpace ℝ (Fin k) × F) →L[ℝ] EuclideanSpace ℝ (Fin n)).contMDiff.comp_contMDiffOn hpair

/-- `(y, s) ↦ box hF y s` is smooth on `boxSet`. -/
theorem contMDiffOn_box
    (hF : IsSubmersionAtOfComplement F (𝓡 n) (𝓡 k) ((⊤ : ℕ∞) : WithTop ℕ∞) X.Φ y₀) :
    ContMDiffOn ((𝓡 n).prod (𝓡 k)) (𝓡 n) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : X.E × EuclideanSpace ℝ (Fin k) => box hF p.1 p.2) (boxSet hF) := by
  have h := (contMDiffOn_extend_symm hF.domChart_mem_maximalAtlas).comp
    (contMDiffOn_boxCoord hF) ?_
  · simpa only [box, Function.comp_def] using h
  · intro p hp
    rw [← OpenPartialHomeomorph.extend_target']
    exact hp.2.2

end

end Work.ThomBordism.Transversality.BoxFamily
