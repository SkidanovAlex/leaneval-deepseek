import Submission.Work.ThomBordism._gtd.P1
import Submission.Work.ThomBordism.gaussClassifying
import Submission.Work.Tubular.exists_euclidean_normalBundle
import Submission.Work.PTGeometric.PadAmb

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open scoped Topology

namespace Work.ThomBordism.Grassmann

open Work.PTGeometric
open Work.ThomBordism.PontryaginThom

noncomputable section

variable {V : Work.ThomBordism.Man8} {k : ℕ}

theorem span_gframe (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) {x : V.pt} (hx : x ∈ ND.D.baseSet i) :
    Submodule.span ℝ (Set.range (Work.ThomBordism.Gauss.gframe E ND i x))
      = Work.Tubular.normalSpace E x := by
  have hcoe : ∀ a, Work.ThomBordism.Gauss.gframe E ND i x a
      = (if (a : ℕ) = 0 then Work.ThomBordism.Gauss.sigma E ND i x else 1)
          • Work.Tubular.orthFrame E ND i x a :=
    fun a => Work.ThomBordism.Gauss.gframe_apply E ND i x a
  have hne : ∀ a, (if (a : ℕ) = 0 then Work.ThomBordism.Gauss.sigma E ND i x else 1) ≠ 0 := by
    intro a
    by_cases ha : (a : ℕ) = 0
    · rw [if_pos ha]
      rcases Work.ThomBordism.Gauss.sigma_eq_one_or E ND i x with h | h <;> rw [h] <;> norm_num
    · rw [if_neg ha]; norm_num
  rw [show Submodule.span ℝ (Set.range (Work.ThomBordism.Gauss.gframe E ND i x))
      = Submodule.span ℝ (Set.range (Work.Tubular.orthFrame E ND i x)) from ?_]
  · exact Work.Tubular.span_orthFrame E ND i hx
  · refine le_antisymm ?_ ?_
    · refine Submodule.span_le.mpr ?_
      rintro - ⟨a, rfl⟩
      rw [hcoe a]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
    · refine Submodule.span_le.mpr ?_
      rintro - ⟨a, rfl⟩
      have h2 : Work.Tubular.orthFrame E ND i x a
          = ((if (a : ℕ) = 0 then Work.ThomBordism.Gauss.sigma E ND i x else 1))⁻¹
              • Work.ThomBordism.Gauss.gframe E ND i x a := by
        rw [hcoe a, smul_smul, inv_mul_cancel₀ (hne a), one_smul]
      rw [h2]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

end

end Work.ThomBordism.Grassmann
