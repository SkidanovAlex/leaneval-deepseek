/-
  WilG4c / ParamChartsOK.

  Transfer of the per-chart conditions `ChartsOK` along a *parameter* substitution:

  a finite family `Φ` of charts for the pulled-back family `ν ↦ F (θ ν)` over the parameter
  region `{ν | θ ν ∈ Λ}` is turned into a finite family `Φ'` of charts for `F` over `Λ`,
  by composing every chart with `μ`.  The hypothesis `hpre : ∀ l ∈ Λ, θ (μ l) = l` says that
  `μ` is a section of `θ` over `Λ`, so for `l ∈ Λ` the point `μ l` lies in `{ν | θ ν ∈ Λ}` and
  `F (θ (μ l)) = F l`: the cube-into-cube condition and the `C^r`/unit-norm conditions transfer
  verbatim from `hΦ`, while the `Ω`-condition on the chart graphs is supplied by the caller
  (`hΩ`).  No injectivity or surjectivity of `μ` is needed: the new family is the image of `Φ`
  under `χ ↦ (fun j l t => χ j (μ l) t)`, so its cardinality does not increase.
-/
import Mathlib
import Submission.Work.Wilkies.Defs
import Submission.Work.Wilkies.CG.Spec
import Submission.Work.WilG4c.Defs
import Submission.Work.WilG4c.FLemAPI

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkG4c

theorem ParamChartsOK (S : WilkiesDesign.SOMin) {p q n k a Dg r : ℕ}
    (θ : (Fin q → ℝ) → (Fin p → ℝ)) (μ : (Fin p → ℝ) → (Fin q → ℝ))
    (Λ : Set (Fin p → ℝ)) (F : Work.WilkG4c.Family k p n)
    (hpre : ∀ l ∈ Λ, θ (μ l) = l) (Φ : Finset (Work.WilkG4c.ChartTuple q n))
    (hΩ : ∀ χ ∈ Φ, ∀ j : Fin n,
      WilkiesDesign.CG.famGraph (fun (l : Fin p → ℝ) (t : Fin n → ℝ) => χ j (μ l) t)
        ∈ S.Ω a Dg (p + n + 1))
    (hΦ : Work.WilkG4c.ChartsOK S a Dg r {ν : Fin q → ℝ | θ ν ∈ Λ}
      (fun i ν z => F i (θ ν) z) Φ) :
    ∃ Φ' : Finset (Work.WilkG4c.ChartTuple p n),
      Φ'.card ≤ Φ.card ∧ Work.WilkG4c.ChartsOK S a Dg r Λ F Φ' ∧
      (∀ χ ∈ Φ, (fun j l t => χ j (μ l) t) ∈ Φ') := by
  classical
  refine ⟨Φ.image (fun χ j l t => χ j (μ l) t), Finset.card_image_le, ?_, ?_⟩
  · rw [Work.WilkG4c.ChartsOK] at hΦ ⊢
    rintro φ hφ
    rw [Finset.mem_image] at hφ
    obtain ⟨χ, hχ, rfl⟩ := hφ
    refine ⟨hΩ χ hχ, ?_⟩
    intro l hl
    have hμ : μ l ∈ {ν : Fin q → ℝ | θ ν ∈ Λ} := by
      show θ (μ l) ∈ Λ
      rw [hpre l hl]
      exact hl
    simpa only [hpre l hl] using (hΦ χ hχ).2 (μ l) hμ
  · intro χ hχ
    exact Finset.mem_image_of_mem (fun χ j l t => χ j (μ l) t) hχ

end Work.WilkG4c
