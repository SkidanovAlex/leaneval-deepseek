import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Repel.liftSel_def
import Submission.Work.Repel.iterate_diffAt
import Submission.Work.Repel.invFunOn_differentiableOn

namespace Work.Repel

/-- `π = piExp` is entire. -/
theorem differentiable_piExp : Differentiable ℂ MandelDim.piExp := by
  unfold MandelDim.piExp
  fun_prop

theorem liftSel_differentiableOn {f₀ : ℂ → ℂ} {D₀ : Set ℂ} {d : MandelDim.ParabData f₀ D₀}
    {f : ℂ → ℂ} {Df : Set ℂ} {η y₁ : ℝ} {K K' : Set ℂ} {δ : ℝ}
    (P : MandelDim.PertData d f Df η y₁ K K' δ)
    {U U' : Set ℂ} (hUo : IsOpen U) (hU'o : IsOpen U') (hinj : Set.InjOn MandelDim.piExp U')
    {m : ℕ} (hm : 1 ≤ m) (hwalk : ∀ w ∈ U, ∀ j < m, P.R^[j] w ∈ P.DR)
    (hmaps : ∀ w ∈ U, MandelDim.piExp (P.R^[m] w) ∈ MandelDim.piExp '' U') :
    DifferentiableOn ℂ (liftSel P.R m U') U := by
  -- `π` is entire, so the inverse branch of `π` on the injective set `U'` is holomorphic.
  have hinv : DifferentiableOn ℂ (Function.invFunOn MandelDim.piExp U')
      (MandelDim.piExp '' U') :=
    invFunOn_differentiableOn hU'o hinj
      (differentiable_piExp.differentiableOn.mono (Set.subset_univ _))
  -- the `m`-th iterate of `R` is holomorphic on `U` (its orbit up to `m - 1` stays in `DR`)
  have hRm : DifferentiableOn ℂ (P.R^[m]) U := by
    intro w hw
    exact (differentiableAt_iterate m (fun i hi =>
      P.R_holo.differentiableAt
        (P.DR_open.mem_nhds (hwalk w hw i hi)))).differentiableWithinAt
  -- compose with `π` and the inverse branch; the image lands in `π '' U'` by `hmaps`
  have hcomp : DifferentiableOn ℂ (fun w => MandelDim.piExp (P.R^[m] w)) U :=
    differentiable_piExp.differentiableOn.comp hRm (fun w _ => Set.mem_univ _)
  have hmain : DifferentiableOn ℂ
      (fun w => Function.invFunOn MandelDim.piExp U' (MandelDim.piExp (P.R^[m] w))) U :=
    hinv.comp hcomp hmaps
  -- on `U` the chosen lift agrees with that inverse branch
  refine hmain.congr ?_
  intro w hw
  obtain ⟨w₀, hw₀U', hw₀eq⟩ := hmaps w hw
  have hex : ∃ w' ∈ U', MandelDim.piExp w' = MandelDim.piExp (P.R^[m] w) :=
    ⟨w₀, hw₀U', hw₀eq⟩
  obtain ⟨hmem', hπ'⟩ := liftSel_spec (R := P.R) (m := m) (U' := U') hex
  exact (hinj (Function.invFunOn_mem hex) hmem'
    (by rw [Function.invFunOn_eq hex, hπ'])).symm

end Work.Repel
