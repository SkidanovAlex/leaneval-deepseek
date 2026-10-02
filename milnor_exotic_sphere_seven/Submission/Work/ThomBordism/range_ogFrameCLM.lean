import Mathlib
import Submission.Work.ThomBordism.LeadChapter.Defs
import Submission.Work.PTGeometric.exists_projOfPlane
import Submission.Work.PTGeometric.ConcreteCollapse

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The range of the orthonormal frame map of an oriented plane

`Work.ThomBordism.LeadChapter.ogFrameCLM Γ` is the frame map `ℝ^k → ℝ^{k+m}` of the orthonormal frame
`Quotient.out Γ` of the oriented plane `Γ : G̃r_k(ℝ^{k+m})`.  Its range is exactly the plane, i.e. the
set of vectors fixed by `Work.PTGeometric.projOfPlane k m Γ`:

* `Work.ThomBordism.memPlane_iff_mem_span_out` — `memPlane` is the span of the representative frame;
* `Work.ThomBordism.range_ogFrameCLM` — `Set.range (ogFrameCLM Γ) = {w | memPlane Γ w}`.

This is the range identification of `G3` of `LeadChapter/ASSEMBLY.md`: combined with
`Work.PTGeometric.projOfPlane_fixed_iff` and the tie `Γ₂ x = G.gauss ⟨Hf x, _⟩` it identifies the Gauss
plane with the range of the level function's derivative, which is the hypothesis of
`Work.ThomBordism.exists_comp_eq_of_range_le` producing the normal-frame datum `N` of the tube
determinant.

No `sorry`, no new axioms.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open scoped Topology

namespace Work.ThomBordism

noncomputable section

open Work.PTGeometric

/-- **`memPlane` is the span of any representative frame.** -/
theorem memPlane_iff_mem_span_out (k m : ℕ) (Γ : Work.ThomBordism.Grassmann.OG k m)
    (w : Amb (k + m)) :
    Work.ThomBordism.Grassmann.memPlane Γ w ↔
      w ∈ Submodule.span ℝ (Set.range (Quotient.out Γ).1) := by
  conv_lhs => rw [← Quotient.out_eq' Γ]
  exact Work.PTGeometric.memPlane_mk_iff (Quotient.out Γ) w

/-- **The frame map of an oriented plane has the plane as its range.** -/
theorem range_ogFrameCLM (k m : ℕ) (Γ : Work.ThomBordism.Grassmann.OG k m) :
    Set.range (Work.ThomBordism.LeadChapter.ogFrameCLM Γ) =
      {w : Amb (k + m) | Work.ThomBordism.Grassmann.memPlane Γ w} := by
  classical
  -- the value of the frame map on the standard basis
  have hsingle : ∀ a : Fin k,
      Work.ThomBordism.LeadChapter.ogFrameCLM Γ (EuclideanSpace.single a 1) =
        (Quotient.out Γ).1 a := by
    intro a
    rw [Work.ThomBordism.LeadChapter.ogFrameCLM, ContinuousLinearMap.sum_apply]
    rw [Finset.sum_eq_single a]
    · simp [PiLp.proj_apply, PiLp.single_apply]
    · intro b _ hb
      have h : (EuclideanSpace.proj b)
          (EuclideanSpace.single a 1 : EuclideanSpace ℝ (Fin k)) = 0 := by
        rw [PiLp.proj_apply, PiLp.single_apply, if_neg hb]
      rw [ContinuousLinearMap.smulRight_apply, h, zero_smul]
    · intro ha
      exact absurd (Finset.mem_univ a) ha
  -- the frame map is the linear expansion in the frame
  have hval : ∀ x : EuclideanSpace ℝ (Fin k),
      Work.ThomBordism.LeadChapter.ogFrameCLM Γ x =
        ∑ a : Fin k, x a • (Quotient.out Γ).1 a := by
    intro x
    have hx : x = ∑ a : Fin k, x a • EuclideanSpace.single a 1 := by
      conv_lhs => rw [← (EuclideanSpace.basisFun (Fin k) ℝ).sum_repr x]
      exact Finset.sum_congr rfl (fun a _ => by
        rw [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply])
    calc Work.ThomBordism.LeadChapter.ogFrameCLM Γ x
        = Work.ThomBordism.LeadChapter.ogFrameCLM Γ
            (∑ a : Fin k, x a • EuclideanSpace.single a 1) := congrArg _ hx
      _ = ∑ a : Fin k, Work.ThomBordism.LeadChapter.ogFrameCLM Γ
            (x a • EuclideanSpace.single a 1) := by rw [map_sum]
      _ = ∑ a : Fin k, x a • Work.ThomBordism.LeadChapter.ogFrameCLM Γ
            (EuclideanSpace.single a 1) :=
            Finset.sum_congr rfl (fun a _ => map_smul _ _ _)
      _ = ∑ a : Fin k, x a • (Quotient.out Γ).1 a :=
            Finset.sum_congr rfl (fun a _ => by rw [hsingle a])
  ext w
  constructor
  · rintro ⟨x, rfl⟩
    rw [Set.mem_setOf_eq, memPlane_iff_mem_span_out, hval x]
    refine Submodule.sum_mem _ (fun a _ => Submodule.smul_mem _ _ ?_)
    exact Submodule.subset_span ⟨a, rfl⟩
  · intro hw
    rw [Set.mem_setOf_eq, memPlane_iff_mem_span_out] at hw
    have hle : Submodule.span ℝ (Set.range (Quotient.out Γ).1) ≤
        LinearMap.range (Work.ThomBordism.LeadChapter.ogFrameCLM Γ).toLinearMap := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨a, rfl⟩
      exact ⟨EuclideanSpace.single a 1, hsingle a⟩
    exact hle hw

/-- **The range of the frame map of the Gauss plane of a tube point is the tube's plane.** -/
theorem range_ogFrameCLM_gauss {k : ℕ} {D : Work.ThomBordism.PontryaginThom.ThomTarget k}
    {ι : Type} [Fintype ι] {Fam : ι → Work.ThomBordism.Man8}
    (G : GenuineTubeGeometry k D ι Fam) (p : {y : D.T // y ≠ D.t₀}) :
    Set.range (Work.ThomBordism.LeadChapter.ogFrameCLM (G.gauss p)) =
      {z : Amb (k + G.mU) | (G.coord p).1 z = z} := by
  rw [range_ogFrameCLM]
  ext z
  rw [Set.mem_setOf_eq, Set.mem_setOf_eq, ← G.gauss_proj p,
    Work.PTGeometric.projOfPlane_fixed_iff]

end

#print axioms Work.ThomBordism.range_ogFrameCLM
#print axioms Work.ThomBordism.range_ogFrameCLM_gauss

end Work.ThomBordism
