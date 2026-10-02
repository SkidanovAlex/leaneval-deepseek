import Mathlib
import Submission.Work.PTGeometric.TubeAmbient

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.PTGeometric

/-- The `j`-th coordinate of the cube parametrisation `cubeToEuc N R`. -/
theorem cubeToEuc_apply_coord (N : ℕ) (R : ℝ) (t : Fin N → Set.Icc (0 : ℝ) 1) (j : Fin N) :
    (Work.Tubular.cubeToEuc N R t).ofLp j = 2 * R * ((t j : ℝ) - 1 / 2) :=
  congrFun (Work.Tubular.funToEuc_symm_cubeToEuc N R t) j

/-- A point of the open tube of a tube chart whose closed tube is contained in the box of radius `R`
has all its cube coordinates in the **interior** of `[0,1]`: if the `j`-th coordinate were `0` or `1`,
the corresponding ambient coordinate would be `±R`, contradicting the box bound. -/
theorem cubeToEuc_mem_openCube {N : ℕ} {V : Work.ThomBordism.Man8}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V N) {ε R : ℝ}
    (C : Work.Tubular.TubeChart E ε) (hR : 0 < R)
    (hbox : ∀ y ∈ C.U, ∀ j : Fin N, |y.ofLp j| < R)
    {t : Fin N → Set.Icc (0 : ℝ) 1} (h : Work.Tubular.cubeToEuc N R t ∈ C.openTube) :
    ∀ j : Fin N, 0 < (t j : ℝ) ∧ (t j : ℝ) < 1 := by
  have hmem : Work.Tubular.cubeToEuc N R t ∈ C.U := C.openTube_subset_U h
  intro j
  constructor
  · by_contra hle
    have h0 : (t j : ℝ) = 0 := le_antisymm (not_lt.mp hle) (t j).2.1
    have hb := hbox _ hmem j
    rw [cubeToEuc_apply_coord N R t j, h0] at hb
    have hval : |2 * R * ((0 : ℝ) - 1 / 2)| = R := by
      rw [show 2 * R * ((0 : ℝ) - 1 / 2) = -R by ring, abs_neg, abs_of_pos hR]
    rw [hval] at hb
    exact absurd hb (lt_irrefl R)
  · by_contra hle
    have h1 : (t j : ℝ) = 1 := le_antisymm (t j).2.2 (not_lt.mp hle)
    have hb := hbox _ hmem j
    rw [cubeToEuc_apply_coord N R t j, h1] at hb
    have hval : |2 * R * ((1 : ℝ) - 1 / 2)| = R := by
      rw [show 2 * R * ((1 : ℝ) - 1 / 2) = R by ring, abs_of_pos hR]
    rw [hval] at hb
    exact absurd hb (lt_irrefl R)

end Work.PTGeometric
