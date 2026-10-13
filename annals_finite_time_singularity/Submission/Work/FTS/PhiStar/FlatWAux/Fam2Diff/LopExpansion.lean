import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.Spaces.DthIter_mul
import Submission.Work.FTS.EllipticEst.remov.high_chain_sum_self

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.FlatWAux.Fam2Diff

theorem LopExpansion (i : ℕ) {g : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hg : ContDiffOn ℝ (i + 1) g U) :
    ∀ θ ∈ U, (Work.Spaces.Lop^[i]) g θ
      = ∑ r ∈ Finset.range (i + 1),
          Work.FTS.EllipticEst.remov.selfdth.dthCoef i r θ * iteratedDeriv r g θ := by
  intro θ hθ
  -- view `g` as a function of two variables independent of the first
  have hsm : ContDiffOn ℝ (((i + 1 : ℕ)) : WithTop ℕ∞)
      (Function.uncurry (fun (_ : ℝ) (θ' : ℝ) => g θ')) (Set.univ ×ˢ U) := by
    change ContDiffOn ℝ (((i + 1 : ℕ)) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => g p.2) (Set.univ ×ˢ U)
    have hsnd : ContDiffOn ℝ (((i + 1 : ℕ)) : WithTop ℕ∞) (Prod.snd : ℝ × ℝ → ℝ)
        (Set.univ ×ˢ U) :=
      (contDiff_snd (𝕜 := ℝ) (E := ℝ) (F := ℝ) (n := (((i + 1 : ℕ)) : WithTop ℕ∞))).contDiffOn
    have hc := hg.comp hsnd (fun p hp => hp.2)
    simpa [Function.comp_def] using hc
  have hexp := Work.FTS.EllipticEst.remov.selfdth.DthIter_expansion_of_contDiffOn
    i (fun (_ : ℝ) (θ' : ℝ) => g θ') (Set.univ ×ˢ U)
    (isOpen_univ.prod hU) hsm 0 θ ⟨trivial, hθ⟩
  have hslice : (fun θ : ℝ => (fun (_ : ℝ) (θ' : ℝ) => g θ') 0 θ) = g := by
    funext θ'; rfl
  have hL : Work.Spaces.DthIter i (fun (_ : ℝ) (θ' : ℝ) => g θ') 0 θ
      = (Work.Spaces.Lop^[i]) g θ := by
    rw [Work.Spaces.DthIter_eq_iterate_Lop, hslice]
  rw [← hL, hexp]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hpt : Work.Spaces.pthIter r (fun (_ : ℝ) (θ' : ℝ) => g θ') 0 θ
      = iteratedDeriv r g θ := by
    rw [Work.FTS.EllipticEst.remov.selfdth.pthIter_eq_iteratedDeriv_slice, hslice]
  rw [hpt]

end Work.FTS.PhiStar.FlatWAux.Fam2Diff
