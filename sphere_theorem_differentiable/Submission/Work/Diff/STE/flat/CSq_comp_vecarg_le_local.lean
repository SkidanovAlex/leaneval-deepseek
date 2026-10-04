import Mathlib
import Submission.Work.Diff.STE.CSq_comp_vecarg_le
import Submission.Work.Diff.STE.Torus

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.flat

open scoped Topology

/-- **Extension of a smooth function from an open set, agreeing on a compact subset.**

If `Φ` is smooth on an open set `V ⊆ (Fin m → ℂ)` and `Kc` is a compact subset of `V`, then `Φ`
agrees on `Kc` with a globally smooth function.  The construction multiplies `Φ` by a smooth bump
`χ` which equals `1` on `Kc` and whose support lies inside `W` with `closure W ⊆ V`; the product is
smooth at every point (at points of `V` because both factors are, at points outside `V` because
`χ` vanishes in a neighbourhood there). -/
lemma exists_contDiff_extend_of_isCompact {m : ℕ} (Φ : (Fin m → ℂ) → ℂ) (V : Set (Fin m → ℂ))
    (hVopen : IsOpen V) (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ V)
    (Kc : Set (Fin m → ℂ)) (hKcc : IsCompact Kc) (hKcV : Kc ⊆ V) :
    ∃ Ψ : (Fin m → ℂ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Ψ ∧ ∀ z ∈ Kc, Ψ z = Φ z := by
  classical
  -- an open set `W` with `Kc ⊆ W` and `closure W ⊆ V`
  obtain ⟨W, hWopen, hKcW, hWV⟩ := normal_exists_closure_subset hKcc.isClosed hVopen hKcV
  -- a smooth function equal to `1` on `Kc` with support exactly `W`
  obtain ⟨χ, hχdiff, -, hχsupp, hχone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := ⊤) hWopen hKcc.isClosed hKcW
  refine ⟨fun z => χ z • Φ z, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z ∈ V
    · exact ContDiffAt.smul hχdiff.contDiffAt (hΦ.contDiffAt (hVopen.mem_nhds hz))
    · -- `z ∉ V`, hence `χ = 0` on a neighbourhood of `z`
      have hzcl : z ∉ closure W := fun h => hz (hWV h)
      have hz0 : ∀ᶠ w in 𝓝 z, χ w = 0 := by
        filter_upwards [(isClosed_closure.isOpen_compl).mem_nhds hzcl] with w hw
        have hw' : w ∉ Function.support χ := by
          rw [hχsupp]
          exact fun h => hw (subset_closure h)
        simpa [Function.mem_support] using hw'
      have hev : (fun z => χ z • Φ z) =ᶠ[𝓝 z] (fun _ => (0 : ℂ)) := by
        filter_upwards [hz0] with w hw
        simp [hw]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  · intro z hz
    simp [(hχone z).mp hz]

theorem CSq_comp_vecarg_le_local {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
    (s ρ : ℕ) (hρ : Fintype.card ι < 2 * ρ) (hρs : ρ ≤ s)
    (Φ : (Fin m → ℂ) → ℂ) (V : Set (Fin m → ℂ))
    (hVopen : IsOpen V) (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ V)
    (Kc : Set (Fin m → ℂ)) (hKcc : IsCompact Kc) (hKcV : Kc ⊆ V)
    (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (c : (ι → ℤ) → (Fin m → ℂ)),
      (∀ N : ℕ, Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ N * ‖c k‖)) →
      (∑ i : Fin m, Work.Diff.STE.CSq ρ (fun k : ι → ℤ => c k i)) ≤ B ^ 2 →
      (∀ x : ι → ℝ, (fun i : Fin m => Work.Diff.STE.seriesFun (fun k : ι → ℤ => c k i) x) ∈ Kc) →
      Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff
          (fun x : ι → ℝ => Φ (fun i : Fin m => Work.Diff.STE.seriesFun (fun k => c k i) x)))
        ≤ C * (1 + ∑ i : Fin m, Work.Diff.STE.CSq s (fun k : ι → ℤ => c k i)) := by
  classical
  obtain ⟨Ψ, hΨdiff, hΨeq⟩ :=
    exists_contDiff_extend_of_isCompact Φ V hVopen hΦ Kc hKcc hKcV
  obtain ⟨C, hC, hC'⟩ :=
    Work.Diff.STE.CSq_comp_vecarg_le (ι := ι) s ρ hρ hρs Ψ hΨdiff B hB
  refine ⟨C, hC, ?_⟩
  intro c hmom hCSq hKc
  have hfun : (fun x : ι → ℝ =>
        Φ (fun i : Fin m => Work.Diff.STE.seriesFun (fun k : ι → ℤ => c k i) x))
      = (fun x : ι → ℝ =>
        Ψ (fun i : Fin m => Work.Diff.STE.seriesFun (fun k : ι → ℤ => c k i) x)) := by
    funext x
    exact (hΨeq _ (hKc x)).symm
  rw [hfun]
  exact (hC' c hmom hCSq).2

end Work.Diff.STE.flat
