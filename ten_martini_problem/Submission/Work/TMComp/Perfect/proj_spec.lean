import Mathlib
import Submission.Work.TMComp.PerfectDefs

open LeanEval.Analysis.TenMartini
open Work.TMContract

noncomputable section

namespace Work.TMComp.Perfect

/-- General form of `proj_spec` for an arbitrary self-adjoint operator `H`: the functional
calculus of the tent function `projFun E δ` is a self-adjoint idempotent which kills `H - E`
and is nonzero whenever `E` lies in the spectrum. -/
private theorem cfc_projFun_spec
    (H : EllTwo →L[ℂ] EllTwo) (E δ : ℝ) (hδ : 0 < δ) (hsa : IsSelfAdjoint H)
    (hE : (E : ℂ) ∈ spectrum ℂ H)
    (hiso : ∀ x ∈ spectrum ℂ H, ‖x - (E : ℂ)‖ < δ → x = (E : ℂ)) :
    cfc (projFun E δ) H * cfc (projFun E δ) H = cfc (projFun E δ) H ∧
      star (cfc (projFun E δ) H) = cfc (projFun E δ) H ∧
      cfc (projFun E δ) H ≠ 0 ∧
      (H - (E : ℂ) • 1) * cfc (projFun E δ) H = 0 := by
  have hnormal : IsStarNormal H := hsa.isStarNormal
  have hcont : ContinuousOn (projFun E δ) (spectrum ℂ H) :=
    (projFun_continuous E δ).continuousOn
  -- On the spectrum, `projFun E δ` can only be nonzero at `E`.
  have hkey : ∀ z ∈ spectrum ℂ H, projFun E δ z ≠ 0 → z = (E : ℂ) := by
    intro z hz hzne
    have hne_real : (max 0 (1 - ‖z - (E : ℂ)‖ / δ) : ℝ) ≠ 0 :=
      fun h => hzne (by simp [projFun, h])
    have hpos : 0 < max 0 (1 - ‖z - (E : ℂ)‖ / δ) :=
      lt_of_le_of_ne (le_max_left 0 _) (Ne.symm hne_real)
    have hx : 0 < 1 - ‖z - (E : ℂ)‖ / δ := by
      by_contra hle
      rw [not_lt] at hle
      rw [max_eq_left hle] at hpos
      exact lt_irrefl 0 hpos
    rw [sub_pos, div_lt_one hδ] at hx
    exact hiso z hz hx
  -- `projFun E δ` is idempotent on the spectrum.
  have hsq : Set.EqOn (fun z => projFun E δ z * projFun E δ z) (projFun E δ) (spectrum ℂ H) := by
    intro z hz
    by_cases h : projFun E δ z = 0
    · simp [h]
    · have hzE : z = (E : ℂ) := hkey z hz h
      simp [hzE, projFun_apply_self]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← cfc_mul (projFun E δ) (projFun E δ) H hcont hcont]
    exact cfc_congr hsq
  · rw [← cfc_star (projFun E δ) H]
    exact cfc_congr (fun z _ => projFun_star E δ z)
  · intro hzero
    have heq : Set.EqOn (projFun E δ) (0 : ℂ → ℂ) (spectrum ℂ H) :=
      eqOn_of_cfc_eq_cfc (f := projFun E δ) (g := (0 : ℂ → ℂ)) (a := H)
        (by rw [hzero, cfc_zero ℂ H]) hcont continuousOn_const hnormal
    have h0 := heq hE
    simp only [projFun_apply_self, Pi.zero_apply] at h0
    exact one_ne_zero h0
  · have hcontz : ContinuousOn (fun z : ℂ => z - (E : ℂ)) (spectrum ℂ H) :=
      continuousOn_id.sub continuousOn_const
    have hsub : cfc (fun z : ℂ => z - (E : ℂ)) H = H - (E : ℂ) • 1 := by
      rw [cfc_sub (fun z : ℂ => z) (fun _ => (E : ℂ)) H continuousOn_id continuousOn_const,
        cfc_id' ℂ H hnormal, cfc_const (E : ℂ) H hnormal, Algebra.algebraMap_eq_smul_one]
    have hzero_fun : Set.EqOn (fun z : ℂ => (z - (E : ℂ)) * projFun E δ z) (0 : ℂ → ℂ)
        (spectrum ℂ H) := by
      intro z hz
      by_cases h : projFun E δ z = 0
      · simp [h]
      · have hzE : z = (E : ℂ) := hkey z hz h
        simp [hzE]
    rw [← hsub, ← cfc_mul (fun z : ℂ => z - (E : ℂ)) (projFun E δ) H hcontz hcont,
      cfc_congr hzero_fun, cfc_zero ℂ H]

/-- The canonical spectral projection `proj α lam θ E δ` at an energy `E` isolated in the
spectrum by margin `δ` is a nonzero self-adjoint idempotent which kills `amoOp - E`. -/
theorem proj_spec (α lam θ : ℝ) (E δ : ℝ) (hδ : 0 < δ)
    (hE : (E : ℂ) ∈ spectrum ℂ (Work.TMComp.Perfect.amoOp α lam θ))
    (hsa : IsSelfAdjoint (Work.TMComp.Perfect.amoOp α lam θ))
    (hiso : ∀ x ∈ spectrum ℂ (Work.TMComp.Perfect.amoOp α lam θ), ‖x - (E : ℂ)‖ < δ → x = (E : ℂ)) :
    Work.TMComp.Perfect.proj α lam θ E δ * Work.TMComp.Perfect.proj α lam θ E δ
        = Work.TMComp.Perfect.proj α lam θ E δ ∧
      star (Work.TMComp.Perfect.proj α lam θ E δ) = Work.TMComp.Perfect.proj α lam θ E δ ∧
      Work.TMComp.Perfect.proj α lam θ E δ ≠ 0 ∧
      (Work.TMComp.Perfect.amoOp α lam θ - (E : ℂ) • 1) * Work.TMComp.Perfect.proj α lam θ E δ = 0 := by
  exact cfc_projFun_spec (amoOp α lam θ) E δ hδ hsa hE hiso

end Work.TMComp.Perfect
