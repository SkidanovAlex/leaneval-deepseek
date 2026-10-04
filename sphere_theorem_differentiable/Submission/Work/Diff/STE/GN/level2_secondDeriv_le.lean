import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.GN.tools
import Submission.Work.Diff.STE.ENormSq_succ_eq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.GN

theorem level2_secondDeriv_le {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ℕ) (hm : 2 ≤ m)
    (f : (ι → ℝ) → ℂ) (i : ι) :
    (∫ x in Work.Diff.STE.unitCube (ι := ι),
        ‖Work.Diff.STE.pd i (Work.Diff.STE.pd i f) x‖ ^ (m : ℝ)) ^ (1 / (m : ℝ))
      ≤ Work.Diff.STE.gnLev (ι := ι) m f 2 := by
  -- The pure second derivative `∂ᵢ∂ᵢ f` is one of the level-`2` derivative directions
  -- (`pdVec 2 l f = ∂^{l 0} ∂^{l 1} f`, and `l := fun _ => i` gives `∂ᵢ∂ᵢ`), so its `L^m`
  -- norm is at most the `ℓ¹`-in-`l` sum defining `gnLev m f 2`.
  have hpd : Work.Diff.STE.pd i (Work.Diff.STE.pd i f)
      = Work.Diff.STE.pdVec 2 (fun _ : Fin 2 => i) f := rfl
  have hgnP : Work.Diff.STE.gnP m 2 = (m : ℝ) := by rw [Work.Diff.STE.gnP]; norm_num
  have hnn : ∀ l : Fin 2 → ι, 0 ≤ ∫ x in Work.Diff.STE.unitCube (ι := ι),
      ‖Work.Diff.STE.pdVec 2 l f x‖ ^ (m : ℝ) :=
    fun l => MeasureTheory.integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
  rw [hpd, Work.Diff.STE.gnLev, hgnP]
  refine Real.rpow_le_rpow (hnn _) ?_ (by positivity)
  exact Finset.single_le_sum (fun l _ => hnn l) (Finset.mem_univ _)

end Work.Diff.STE.GN
