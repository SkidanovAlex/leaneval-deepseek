import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC6Core.Covariant
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLC6Core.ent_ge_growth_assembly
import Submission.Work.EKLC6Core.exists_gen_plaque
import Submission.Work.EKLC6Core.exists_good_set_plaque
import Submission.Work.EKLC6Core.uminus_isHoro

/-!
# `Work.EKLC6Core.ent_ge_growth_uminus` — Pisa 7.6(ii) for the full stable horospherical subgroup

For an `A`-ergodic probability `μ` on `X₃`, the leaf-wise system `ν = μ_x^{U}` of the full
contracted horospherical subgroup `U = Uminus t`, and the growth function
`growthFun (Uminus t) ν t x = -log ν x (conjBox (Uminus t) t)`,

`ofReal (∫ growthFun (Uminus t) ν t) ≤ ent μ (aDiag t ·)`.

This is the `U = G⁻(t)` case of Pisa 7.6(ii).  The inputs are

* `exists_plaque_family_conull` (Pisa 7.37/7.38): a conull, countably generated,
  `aDiag t`-descending plaque algebra `(Z, A)` for `Uminus t`;
* `comap_pastSigA_le`: its past σ-algebra is `aDiag t`-descending;
* `exists_good_set_plaque` (Pisa 7.34/7.35: the sandwich stratification and recurrence);
* `ent_ge_growth_of_goodset` (the Birkhoff/a.e. bookkeeping, L3 + `growth_le_HcondSig`).
-/

open MeasureTheory Filter Topology
open scoped ENNReal

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-- In the degenerate case `Uminus t = ⊥` the contracted box is `{1}`, whence the growth
function vanishes identically and the inequality is trivial. -/
theorem ent_ge_growth_bot {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ]
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' : Set Work.EKLContract.X3}
    (hL : Work.EKLContract.IsLeafwise μ (⊥ : Subgroup Work.EKLContract.SL3) ν X')
    (t : Fin 3 → ℝ) (hbot : Work.EKLC6Core.Uminus t = ⊥) :
    ENNReal.ofReal (∫ x, Work.EKLC6Core.growthFun (⊥ : Subgroup Work.EKLContract.SL3) ν t x ∂μ) ≤
      Work.EKLContract.ent μ (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) := by
  have hbox : Box1 (⊥ : Subgroup Work.EKLContract.SL3) = {1} := by
    ext g
    constructor
    · intro hg
      exact Subgroup.mem_bot.mp hg.1
    · intro hg
      rw [Set.mem_singleton_iff] at hg
      subst hg
      refine ⟨Subgroup.mem_bot.mpr rfl, ?_⟩
      intro i j
      simp
  have hconj : Work.EKLC6Core.conjBox (⊥ : Subgroup Work.EKLContract.SL3) t = {1} := by
    rw [Work.EKLC6Core.conjBox, hbox]
    ext g
    simp [Work.EKLC6Core.conjBy]
  have hzero : ∫ x, Work.EKLC6Core.growthFun (⊥ : Subgroup Work.EKLContract.SL3) ν t x ∂μ = 0 := by
    have hae : Work.EKLC6Core.growthFun (⊥ : Subgroup Work.EKLContract.SL3) ν t
        =ᵐ[μ] fun _ : Work.EKLContract.X3 => (0 : ℝ) := by
      filter_upwards [MeasureTheory.ae_iff.mpr hL.conull] with x hx
      rw [Work.EKLC6Core.growthFun, hconj]
      have h1x : ν x ({1} : Set Work.EKLContract.SL3) = 1 := by
        rw [← hbox]
        exact hL.normalised x hx
      rw [h1x]
      simp
    rw [MeasureTheory.integral_congr_ae hae]
    simp
  rw [hzero]
  simp

/-- **Pisa 7.6(ii) for the full contracted horospherical subgroup.** -/
theorem ent_ge_growth_uminus {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ]
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' X'' : Set Work.EKLContract.X3} (t : Fin 3 → ℝ)
    (hErg : Work.EKLContract.IsAErgodic μ)
    (hL : Work.EKLContract.IsLeafwise μ (Work.EKLC6Core.Uminus t) ν X')
    (hcov : Work.EKLC6Core.ACovariant ν X'') (hX'' : μ (X''ᶜ) = 0)
    (hint : MeasureTheory.Integrable (Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t) μ) :
    ENNReal.ofReal (∫ x, Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t x ∂μ) ≤
      Work.EKLContract.ent μ (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) := by
  have hAinv : Work.EKLContract.IsAInvariant μ := hErg.1
  have hmp : MeasureTheory.MeasurePreserving
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) μ μ := hAinv t
  have hU : Work.EKLContract.IsHoro (Work.EKLC6Core.Uminus t) :=
    (Work.EKLC6Core.uminus_isHoro t).1
  have hcontr : ∀ u ∈ Work.EKLC6Core.Uminus t, Filter.Tendsto
      (fun n : ℕ => Work.EKLContract.aDiag t ^ n * u * (Work.EKLContract.aDiag t ^ n)⁻¹)
      Filter.atTop (nhds 1) :=
    Work.EKLC6Core.tendsto_conj_mem_uminus t
  by_cases hne : Work.EKLC6Core.Uminus t = (⊥ : Subgroup Work.EKLContract.SL3)
  · rw [hne] at hL ⊢
    exact Work.EKLC6Core.ent_ge_growth_bot hL t hne
  · -- The conull plaque algebra and its `aDiag t`-descent come from `exists_gen_plaque`
    -- (Pisa 7.37/7.38 with the ergodicity of `aDiag t` supplied by `IsAErgodic μ`).
    obtain ⟨A, Z, hplaq, hZ, hdec, -⟩ :=
      Work.EKLC6Core.exists_gen_plaque (μ := μ) t hErg
    obtain ⟨Y, δ, R, hYmeas, hδ, hR, hY, hvisit⟩ :=
      Work.EKLC6Core.exists_good_set_plaque t hmp hplaq hZ
    exact Work.EKLC6Core.ent_ge_growth_of_goodset hL hU hcov hX'' t hcontr hAinv hint
      hplaq hdec hZ hYmeas hδ hR hY hvisit

end Work.EKLC6Core

end
