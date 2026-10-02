import Mathlib
import Submission.Work.ThomBordism.Grassmann.NuRadialDefs
import Submission.Work.ThomBordism.Grassmann.NuRadialInvCont

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.ThomBordism.Grassmann

open scoped Topology

/-- **The disc bundle of a fibrewise norm is trivial.**  For a continuous fibrewise norm `ν` on the
trivial bundle `X × ℝ^k` (non-negative, positively homogeneous in the fibre, vanishing exactly on
the zero section), the `ν`-unit disc `{z | ν z ≤ 1}` is homeomorphic to `X × {v | ‖v‖ ≤ 1}`, and
the homeomorphism matches the two boundaries: `ν z = 1` exactly when the euclidean norm of the
image fibre coordinate is `1`. -/
theorem exists_homeo_nuDisc (X : Type*) [TopologicalSpace X] (k : ℕ)
    (ν : X × EuclideanSpace ℝ (Fin k) → ℝ) (hcont : Continuous ν)
    (hnonneg : ∀ z, 0 ≤ ν z)
    (hhom : ∀ (c : ℝ) (x : X) (v : EuclideanSpace ℝ (Fin k)), 0 ≤ c → ν (x, c • v) = c * ν (x, v))
    (hzero : ∀ (x : X) (v : EuclideanSpace ℝ (Fin k)), ν (x, v) = 0 ↔ v = 0) :
    ∃ e : ↥{z : X × EuclideanSpace ℝ (Fin k) | ν z ≤ 1} ≃ₜ
        X × {v : EuclideanSpace ℝ (Fin k) // ‖v‖ ≤ 1},
      ∀ z : ↥{z : X × EuclideanSpace ℝ (Fin k) | ν z ≤ 1},
        ν (z : X × EuclideanSpace ℝ (Fin k)) = 1 ↔
          ‖((e z).2 : EuclideanSpace ℝ (Fin k))‖ = 1 := by
  have hφ : Continuous (nuRadial k ν) := continuous_nuRadial k ν hcont hnonneg hhom
  have hψ : Continuous (nuRadialInv k ν) := continuous_nuRadialInv X k ν hcont hnonneg hzero
  let efun : ↥{z : X × EuclideanSpace ℝ (Fin k) | ν z ≤ 1} →
      X × {v : EuclideanSpace ℝ (Fin k) // ‖v‖ ≤ 1} :=
    fun z => (z.1.1,
      ⟨nuRadial k ν z.1, by rw [norm_nuRadial k ν hnonneg hhom z.1]; exact z.2⟩)
  let einv : X × {v : EuclideanSpace ℝ (Fin k) // ‖v‖ ≤ 1} →
      ↥{z : X × EuclideanSpace ℝ (Fin k) | ν z ≤ 1} :=
    fun y => ⟨(y.1, nuRadialInv k ν (y.1, (y.2 : EuclideanSpace ℝ (Fin k)))), by
      change ν (y.1, nuRadialInv k ν (y.1, (y.2 : EuclideanSpace ℝ (Fin k)))) ≤ 1
      rw [nu_nuRadialInv k ν hhom hnonneg hzero y.1 (y.2 : EuclideanSpace ℝ (Fin k))]
      exact y.2.2⟩
  have hleft : Function.LeftInverse einv efun := by
    intro z
    refine Subtype.ext (Prod.ext rfl ?_)
    exact nuRadialInv_nuRadial k ν hhom hnonneg hzero z.1.1 z.1.2
  have hright : Function.RightInverse einv efun := by
    intro y
    refine Prod.ext rfl (Subtype.ext ?_)
    exact nuRadial_nuRadialInv k ν hhom hnonneg hzero y.1 y.2.1
  have hcont_efun : Continuous efun := by
    refine Continuous.prodMk (continuous_fst.comp continuous_subtype_val) ?_
    exact Continuous.subtype_mk
      (f := fun z : ↥{z : X × EuclideanSpace ℝ (Fin k) | ν z ≤ 1} =>
        nuRadial k ν (z : X × EuclideanSpace ℝ (Fin k))) (hφ.comp continuous_subtype_val)
      (fun z => by rw [norm_nuRadial k ν hnonneg hhom]; exact z.2)
  have hcont_einv : Continuous einv := by
    exact Continuous.subtype_mk
      (f := fun y : X × {v : EuclideanSpace ℝ (Fin k) // ‖v‖ ≤ 1} =>
        (y.1, nuRadialInv k ν (y.1, (y.2 : EuclideanSpace ℝ (Fin k)))))
      (Continuous.prodMk continuous_fst (hψ.comp (Continuous.prodMk continuous_fst
        (continuous_subtype_val.comp continuous_snd))))
      (fun y => by
        change ν (y.1, nuRadialInv k ν (y.1, (y.2 : EuclideanSpace ℝ (Fin k)))) ≤ 1
        rw [nu_nuRadialInv k ν hhom hnonneg hzero y.1 (y.2 : EuclideanSpace ℝ (Fin k))]
        exact y.2.2)
  refine ⟨Homeomorph.mk (Equiv.mk efun einv hleft hright) hcont_efun hcont_einv, ?_⟩
  intro z
  show ν (z : X × EuclideanSpace ℝ (Fin k)) = 1 ↔
    ‖(nuRadial k ν (z : X × EuclideanSpace ℝ (Fin k)))‖ = 1
  rw [norm_nuRadial k ν hnonneg hhom]

end Work.ThomBordism.Grassmann
