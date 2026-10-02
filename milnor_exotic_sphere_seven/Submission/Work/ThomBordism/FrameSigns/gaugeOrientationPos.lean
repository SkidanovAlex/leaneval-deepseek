import Mathlib
import Submission.Work.Thom.isOrientedOver_of_det_pos

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# An orientation preserving gauge acts as the identity on the top relative cohomology

Let `D : Y → Gauge n` be a continuous family of invertible linear endomorphisms of `ℝⁿ` with
`det (D y) > 0` for all `y`, and let `gaugeEnd D` be the induced automorphism
`(y, v) ↦ (y, D y v)` of the trivial bundle `Y × ℝⁿ → Y`.  Then `gaugeEnd D` acts as the identity
on the relative cohomology `Hⁿ(Y × ℝⁿ, Y × (ℝⁿ ∖ 0); ℤ)`.

This is the "glueing of local Thom data along an orientation preserving change of trivialisation"
statement: `Work.Thom.Mpun_gaugeEnd_invariant` proves that the gauge fixes the *model class* `Mpun`,
and since `Mpun` is a model class (`Work.Thom.Mpun_isModel`), every class of the pair is a
`H⁰`-multiple of it, so the whole cohomology is fixed.

The only wrinkle is the degree bookkeeping: `Mpun` sits in degree `n` while the model property of
`Mpun_isModel` at `k = 0` produces degree `0 + n`, which is not definitionally `n`; the transport
along `Nat.zero_add n` is handled with `Work.Thom.relCohMap_cast` and `Work.Thom.eq_of_cast_eq`.
-/

open CategoryTheory

namespace Work.ThomBordism.FrameSigns

theorem gaugeOrientationPos {n : ℕ} (hn : 1 ≤ n) {Y : Type} [TopologicalSpace Y]
    (D : Y → Work.Thom.Gauge n) (hD : Continuous D)
    (hdet : ∀ y, 0 < LinearMap.det (D y).toLinearMap) :
    ∀ ξ : Work.Thom.RelCoh ℤ n (Y × EuclideanSpace ℝ (Fin n)) (Work.Thom.Punct Y n),
      (Work.Thom.relCohMap (Work.Thom.gaugeEnd D hD) (Work.Thom.Punct Y n) (Work.Thom.Punct Y n)
        (Work.Thom.gaugeEnd_mem D hD (fun y => Work.Thom.gaugeEnd_bijective_of_det_ne_zero (D y)
          (ne_of_gt (hdet y)))) ℤ n).hom ξ = ξ := by
  intro ξ
  classical
  have hB : ∀ y, Function.Bijective (D y) :=
    fun y => Work.Thom.gaugeEnd_bijective_of_det_ne_zero (D y) (ne_of_gt (hdet y))
  have hf : ∀ p ∈ Work.Thom.Punct Y n, Work.Thom.gaugeEnd D hD p ∈ Work.Thom.Punct Y n :=
    Work.Thom.gaugeEnd_mem D hD hB
  have h : 0 + n = n := Nat.zero_add n
  -- `Mpun` is a model class, so `ξ` is an `H⁰`-multiple of it.
  obtain ⟨a, ha⟩ := (Work.Thom.Mpun_isModel n Y 0).2 (h.symm ▸ ξ)
  -- The gauge fixes the `H⁰`-multiples of `Mpun`.
  have hkey : (Work.Thom.relCohMap (Work.Thom.gaugeEnd D hD) (Work.Thom.Punct Y n)
      (Work.Thom.Punct Y n) hf ℤ (0 + n)).hom
      ((Work.Thom.mixedCupC ℤ (Work.Thom.Punct Y n) 0 n)
        ((Work.Thom.CohMap (Work.Thom.projFstA Y n) ℤ 0).hom a) (Work.Thom.Mpun n Y))
      = (Work.Thom.mixedCupC ℤ (Work.Thom.Punct Y n) 0 n)
        ((Work.Thom.CohMap (Work.Thom.projFstA Y n) ℤ 0).hom a) (Work.Thom.Mpun n Y) := by
    rw [Work.Thom.mixedCupC_pairNatural (Work.Thom.gaugeEnd D hD) (Work.Thom.Punct Y n)
      (Work.Thom.Punct Y n) hf 0 n ((Work.Thom.CohMap (Work.Thom.projFstA Y n) ℤ 0).hom a)
      (Work.Thom.Mpun n Y)]
    rw [Work.Thom.Mpun_gaugeEnd_invariant n hn D hD hdet]
    -- the gauge does not move the base projection
    have hcomp : (Work.Thom.projFstA Y n).comp (Work.Thom.gaugeEnd D hD) = Work.Thom.projFstA Y n := by
      apply ContinuousMap.ext
      intro p
      simp only [ContinuousMap.comp_apply, Work.Thom.gaugeEnd_apply, Work.Thom.projFstA]
      rfl
    rw [Work.Thom.CohMap_comp_apply (Work.Thom.gaugeEnd D hD) (Work.Thom.projFstA Y n) ℤ 0 a,
      Work.Thom.CohMap_congr hcomp ℤ 0]
  -- transport the identity along `0 + n = n`
  have hcast : (h.symm ▸ (Work.Thom.relCohMap (Work.Thom.gaugeEnd D hD) (Work.Thom.Punct Y n)
      (Work.Thom.Punct Y n) hf ℤ n).hom ξ :
        Work.Thom.RelCoh ℤ (0 + n) (Y × EuclideanSpace ℝ (Fin n)) (Work.Thom.Punct Y n))
      = (h.symm ▸ ξ :
        Work.Thom.RelCoh ℤ (0 + n) (Y × EuclideanSpace ℝ (Fin n)) (Work.Thom.Punct Y n)) := by
    have hc := Work.Thom.relCohMap_cast (Work.Thom.gaugeEnd D hD) (Work.Thom.Punct Y n)
      (Work.Thom.Punct Y n) hf (h := h.symm) ξ
    rw [← hc, ← ha]
    exact hkey
  exact Work.Thom.eq_of_cast_eq (α := fun k => Work.Thom.RelCoh ℤ k
      (Y × EuclideanSpace ℝ (Fin n)) (Work.Thom.Punct Y n)) (h := h.symm) hcast

end Work.ThomBordism.FrameSigns
