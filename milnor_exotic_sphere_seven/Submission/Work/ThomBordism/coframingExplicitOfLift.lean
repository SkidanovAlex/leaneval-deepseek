import Mathlib
import Submission.Work.ThomBordism.Grassmann.coframingDefs
import Submission.Work.ThomBordism.Grassmann.exists_coframing_of_orientedLift

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-!
# The explicit coframing of a continuous family of oriented planes, with its orientation

`Work.ThomBordism.Grassmann.exists_coframing_of_orientedLift` produces a finite
orientation-consistent coframing of a continuous family of oriented `k`-planes in `ℝ^{k+m}` given
through an oriented lift `Γ : M → G̃r_k(ℝ^{k+m})`, but only as an *existential* statement: the
witnesses `U`, `ℓ`, `e` are not named, so a consumer cannot compute with them.

This module provides the same construction **explicitly**: the cover is
`U (S,b) = cfGoodSet Γ (S,b)` (the points whose plane lies in the chart `S` with sign `b`), the
fixed left inverse is `ellOf (S,b)` and the varying parametrisation is `eOf Γ (S,b) y`, indexed by
`Fin (Fintype.card (ChartIdx k m × Bool))` through any enumeration of the (finite) index set.  On
top of the five clauses of `exists_coframing_of_orientedLift` this records two further facts that
make the witness usable:

* the **naming clause** — every member of the cover, together with its left inverse and its
  parametrisation, is *literally* one of the `cfGoodSet Γ i`, `ellOf i`, `eOf Γ i`; and
* the **orientation clause** — on `cfGoodSet Γ i` the frame matrix of the coframing `eOf Γ i y`,
  written in the orthonormal frame `Quotient.out (Γ y)` of the plane, has positive determinant,
  i.e. the coframing is positively oriented for `Γ`.

The mathematical content of the second clause: `frameMatrix_det_eq_sign` gives
`det A = frameSign i.1 (Γ y) · |det A|` with `A = frameMatrix i.1 (out (Γ y)).1`, and
`frameSign_eq_of_mem_goodSet` gives `frameSign i.1 (Γ y) = cfSignOf i.2`, while
`signMat_eq_orientMat` + `orientMat_det` identify `det (cfSignMat (cfSignOf i.2))` with
`cfSignOf i.2`; hence `det (A⁻¹ · cfSignMat (cfSignOf i.2)) = 1/|det A| > 0`.
-/

namespace Work.ThomBordism.Grassmann

open scoped Topology

noncomputable section

variable {k m : ℕ}

/-- A tiny arithmetic lemma: if `e² = 1` and `a > 0` then `(e a)⁻¹ e = a⁻¹ > 0`. -/
theorem inv_mul_self_mul_inv_pos {a e : ℝ} (he : e * e = 1) (ha : 0 < a) :
    0 < (e * a)⁻¹ * e := by
  have hene : e ≠ 0 := by intro h; rw [h, zero_mul] at he; exact one_ne_zero he.symm
  have hane : a ≠ 0 := ne_of_gt ha
  have hkey : (e * a)⁻¹ * e = a⁻¹ := by
    rw [inv_mul_eq_div, ← one_div]
    rw [div_eq_div_iff (mul_ne_zero hene hane) hane, one_mul]
  rw [hkey]
  exact inv_pos.mpr ha

/-- **The explicit coframing is positively oriented for the lift `Γ`.**  On `cfGoodSet Γ i` the
matrix of the coframing `eOf Γ i y` in the orthonormal frame `Quotient.out (Γ y)` of the plane is
`(frameMatrix i.1 (out (Γ y)).1)⁻¹ * cfSignMat (cfSignOf i.2)`, and its determinant is
`+|det|⁻¹ > 0`. -/
theorem frameMatrix_inv_cfSignMat_det_pos {M : Type} [TopologicalSpace M]
    {Γ : M → OG k m} {i : ChartIdx k m × Bool} {y : M} (hy : y ∈ cfGoodSet Γ i) :
    0 < Matrix.det ((frameMatrix i.1 (Quotient.out (Γ y)).1)⁻¹ * cfSignMat (cfSignOf i.2)) := by
  have hout : Quotient.mk'' (Quotient.out (Γ y)) = Γ y := Quotient.out_eq' _
  have hS : Quotient.out (Γ y) ∈ chartSet i.1 :=
    (mem_baseSet_iff i.1 (Quotient.out (Γ y))).mp (by rw [hout]; exact hy.1)
  have hd : (frameMatrix i.1 (Quotient.out (Γ y)).1).det
      = cfSignOf i.2 * |(frameMatrix i.1 (Quotient.out (Γ y)).1).det| := by
    have h := frameMatrix_det_eq_sign i.1 (Quotient.out (Γ y)) hS
    rw [hout, frameSign_eq_of_mem_goodSet hy] at h
    exact h
  have hD : (cfSignMat (cfSignOf i.2) : Matrix (Fin k) (Fin k) ℝ).det = cfSignOf i.2 := by
    rw [signMat_eq_orientMat (S := i.1) (x := Γ y) (ε := cfSignOf i.2)
      (frameSign_eq_of_mem_goodSet hy), orientMat_det, frameSign_eq_of_mem_goodSet hy]
  have h1 : Matrix.det ((frameMatrix i.1 (Quotient.out (Γ y)).1)⁻¹ * cfSignMat (cfSignOf i.2))
      = ((frameMatrix i.1 (Quotient.out (Γ y)).1).det)⁻¹ * cfSignOf i.2 := by
    rw [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv, hD]
  rw [h1]
  rw [show ((frameMatrix i.1 (Quotient.out (Γ y)).1).det)⁻¹ * cfSignOf i.2
      = (cfSignOf i.2 * |(frameMatrix i.1 (Quotient.out (Γ y)).1).det|)⁻¹ * cfSignOf i.2
      from by rw [← hd]]
  exact inv_mul_self_mul_inv_pos (signOf_mul_self i.2) (abs_pos.mpr hS)

end

end Work.ThomBordism.Grassmann

namespace Work.ThomBordism

theorem coframingExplicitOfLift {k m : ℕ} {M : Type} [TopologicalSpace M]
    {P : M → Work.PTGeometric.EndOp (k + m)}
    (hPc : Continuous P) (hPgr : ∀ x, P x ∈ Work.PTGeometric.Gr (k + m) k)
    (Γ : M → Work.ThomBordism.Grassmann.OG k m) (hΓc : Continuous Γ)
    (hΓ : ∀ x, Work.PTGeometric.projOfPlane k m (Γ x) = P x) (W : Set M) :
    ∃ (mE : ℕ) (U : Fin mE → Set M)
      (ℓ : Fin mE → Work.PTGeometric.Amb (k + m) →L[ℝ] Work.PTGeometric.Amb k)
      (e : Fin mE → M → Work.PTGeometric.Amb k →L[ℝ] Work.PTGeometric.Amb (k + m)),
      (∀ j, IsOpen (U j)) ∧
      (∀ x ∈ W, ∃ j, x ∈ U j) ∧
      (∀ j y, y ∈ U j → ∀ c : Work.PTGeometric.Amb k,
        ℓ j (e j y c) = c ∧ P y (e j y c) = e j y c) ∧
      (∀ j y, y ∈ U j → Function.Injective (e j y)) ∧
      (∀ j j' y, y ∈ U j → y ∈ U j' →
        0 < LinearMap.det ((ℓ j').comp (e j y) :
          Work.PTGeometric.Amb k →ₗ[ℝ] Work.PTGeometric.Amb k)) ∧
      (∀ j, ∃ i : Work.ThomBordism.Grassmann.ChartIdx k m × Bool,
        U j = Work.ThomBordism.Grassmann.cfGoodSet Γ i ∧
        ℓ j = Work.ThomBordism.Grassmann.ellOf i ∧
        ∀ y, e j y = Work.ThomBordism.Grassmann.eOf Γ i y) ∧
      (∀ j (i : Work.ThomBordism.Grassmann.ChartIdx k m × Bool),
        U j = Work.ThomBordism.Grassmann.cfGoodSet Γ i → ∀ y (hy : y ∈ U j),
          0 < Matrix.det ((Work.ThomBordism.Grassmann.frameMatrix i.1
              (Quotient.out (Γ y)).1)⁻¹
            * Work.ThomBordism.Grassmann.cfSignMat (Work.ThomBordism.Grassmann.cfSignOf i.2))) := by
  classical
  -- Enumerate the (finite) index set `ChartIdx k m × Bool` of the chart-by-chart coframing.
  let eι : Work.ThomBordism.Grassmann.ChartIdx k m × Bool ≃
      Fin (Fintype.card (Work.ThomBordism.Grassmann.ChartIdx k m × Bool)) := Fintype.equivFin _
  refine ⟨_, fun j => Work.ThomBordism.Grassmann.cfGoodSet Γ (eι.symm j),
    fun j => Work.ThomBordism.Grassmann.ellOf (eι.symm j),
    fun j => Work.ThomBordism.Grassmann.eOf Γ (eι.symm j), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- openness of the members of the cover
    intro j
    exact Work.ThomBordism.Grassmann.isOpen_goodSet hΓc (eι.symm j)
  · -- the members cover `W`
    intro x _
    obtain ⟨i, hi⟩ := Work.ThomBordism.Grassmann.exists_goodSet Γ x
    exact ⟨eι i, by simpa using hi⟩
  · -- the left inverse and the plane condition
    intro j y hy c
    exact ⟨Work.ThomBordism.Grassmann.ellOf_eOf_of_mem hy c,
      Work.ThomBordism.Grassmann.projOfPlane_eOf_of_mem hΓ hy c⟩
  · -- injectivity
    intro j y hy
    exact Work.ThomBordism.Grassmann.injective_eOf_of_mem hy
  · -- orientation consistency of overlapping members
    intro j j' y hy hy'
    exact Work.ThomBordism.Grassmann.det_eOf_pos hy hy'
  · -- the naming clause
    intro j
    exact ⟨eι.symm j, rfl, rfl, fun y => rfl⟩
  · -- the orientation clause
    intro j i hU y hy
    exact Work.ThomBordism.Grassmann.frameMatrix_inv_cfSignMat_det_pos (i := i) (y := y)
      (by rw [← hU]; exact hy)

end Work.ThomBordism
