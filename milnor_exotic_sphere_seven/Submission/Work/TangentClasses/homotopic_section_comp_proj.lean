import Mathlib
import Submission.Work.TangentClasses.DiscProj
import Submission.Work.Milnor.VBundle
import Submission.Work.Milnor.ScaleDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.TangentClasses

open scoped unitInterval

noncomputable section

/-- **Fibrewise scaling by `0` is the zero section composed with the bundle projection.**
This is the "retraction" end of the deformation retraction of the total space of `ξ` onto the
zero section: scaling the fibre coordinate to `0` in either chart is exactly evaluating the zero
section at the base point. -/
theorem vScale_zero_eq_zeroSection (k : ℤ) (z : Submission.Milnor.Vk k) :
    Work.Milnor.vScale k 0 z
      = Work.Milnor.zeroSection k (Work.Milnor.vBaseMap k z) := by
  refine Quotient.inductionOn z ?_
  intro s
  rcases s with p | p
  · show Work.Milnor.vScale k 0 ((Submission.Milnor.vData k).ιX p)
        = Work.Milnor.zeroSection k (Work.Milnor.vBaseMap k ((Submission.Milnor.vData k).ιX p))
    rw [Work.Milnor.vScale_ιX, Work.Milnor.vBaseMap_ιX, Work.Milnor.zeroSection_apply_coe]
    simp
  · rcases p with ⟨x, y⟩
    by_cases hx : x = 0
    · show Work.Milnor.vScale k 0 ((Submission.Milnor.vData k).ιY (x, y))
          = Work.Milnor.zeroSection k
              (Work.Milnor.vBaseMap k ((Submission.Milnor.vData k).ιY (x, y)))
      rw [Work.Milnor.vScale_ιY, zero_smul, Work.Milnor.vBaseMap_ιY, Submission.Milnor.baseChart2,
        if_pos hx, Work.Milnor.zeroSection_apply_infty, hx]
    · show Work.Milnor.vScale k 0 ((Submission.Milnor.vData k).ιY (x, y))
          = Work.Milnor.zeroSection k
              (Work.Milnor.vBaseMap k ((Submission.Milnor.vData k).ιY (x, y)))
      rw [Work.Milnor.vScale_ιY, zero_smul, Work.Milnor.vBaseMap_ιY, Submission.Milnor.baseChart2,
        if_neg hx, Work.Milnor.zeroSection_apply_coe]
      rw [(Submission.Milnor.vData k).ιY_eq_ιX_iff]
      refine ⟨Submission.Milnor.mem_vOpens.mpr (Submission.Milnor.invBase_ne_zero hx), ?_⟩
      rw [Work.Milnor.vData_φ_apply, Submission.Milnor.vMap,
        Submission.Milnor.invBase_invBase hx]
      simp [Submission.Milnor.vTwist]

/-- **The disc bundle `D(ξ) → S⁴` deformation retracts onto its zero section.**  Explicitly, the
fibrewise scaling `vScale (-2) t` interpolates between the retraction `s ∘ π` (at `t = 0`) and the
identity (at `t = 1`). -/
theorem homotopic_section_comp_proj :
    Nonempty (ContinuousMap.Homotopy (Work.TangentClasses.discSection.comp Work.TangentClasses.discProj) (ContinuousMap.id Work.TangentClasses.DiscSpace)) := by
  refine ⟨ContinuousMap.Homotopy.mk
    ⟨fun w : I × DiscSpace => Work.Milnor.vScale (-2) (w.1 : ℝ) w.2, ?_⟩ ?_ ?_⟩
  · exact (Work.Milnor.continuous_vScale_uncurry (-2)).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  · intro z
    show Work.Milnor.vScale (-2) ((0 : I) : ℝ) z
      = Work.TangentClasses.discSection (Work.TangentClasses.discProj z)
    rw [show ((0 : I) : ℝ) = 0 from rfl]
    exact vScale_zero_eq_zeroSection (-2) z
  · intro z
    show Work.Milnor.vScale (-2) ((1 : I) : ℝ) z = z
    rw [show ((1 : I) : ℝ) = 1 from rfl, Work.Milnor.vScale_one]
    rfl

end

end Work.TangentClasses
