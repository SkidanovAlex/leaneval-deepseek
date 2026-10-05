import Mathlib
import Submission.Work.RPB1a.Defs

/-!
# RPB1a: concatenation of three loop families

Given three loop families `F₁ F₂ F₃` that match end-to-start (`F₁ 1 = F₂ 0`, `F₂ 1 = F₃ 0`),
they can be concatenated into a single loop family `H` running from `F₁ 0` to `F₃ 1`.

The concatenation is *smooth*: a naive piecewise definition is not `C^∞` at the junctions.
Instead we reparametrise each piece with `Real.smoothTransition ψ` (which is `C^∞`, `= 0` on
`(-∞,0]` and `= 1` on `[1,∞)`), so that each family first *ramps* between parameters `0` and `1`
and then *dwells* at the endpoint.  Concretely (with the `s`-axis split at `1/6, 1/3, 1/2, 2/3, 5/6`)

`H s t = if s ≤ 1/3 then F₁ (ψ (6*s    )) t else if s ≤ 2/3 then F₂ (ψ (6*s - 2)) t else F₃ (ψ (6*s - 4)) t`.

The point is that `H` agrees with the *globally smooth* function
`G₂ s t = F₂ (ψ (6*s-2)) t` on `[1/6, 2/3]` and with `G₃ s t = F₃ (ψ (6*s-4)) t` on `[1/2, ∞)`,
because on the overlapping intervals the `ψ` factors are pinned to `0`/`1` and the junction
identities `h₁₂`, `h₂₃` identify the two families.  Hence `H` is locally a smooth function
everywhere, so `ContDiff ℝ ∞`, and the remaining loop-family fields follow from those of the
`Fᵢ` (each point `H s` equals `Fᵢ σ` for some `σ ∈ [0,1]`).
-/

namespace Work.RPB1a

open Complex Set Metric Filter
open scoped ContDiff Real Topology
open Work.RPB1a

noncomputable section

/-- Re-parametrised family `s ↦ (t ↦ F (ψ (6*s - c)) t)`, used for the three concatenation
pieces (`c = 0, 2, 4`). -/
def glue (F : ℝ → ℝ → ℂ) (c : ℝ) : ℝ → ℝ → ℂ := fun s t => F (Real.smoothTransition (6 * s - c)) t

/-- The concatenation of three families, with `s`-junctions at `1/3` and `2/3`. -/
def concatFam (F₁ F₂ F₃ : ℝ → ℝ → ℂ) (s t : ℝ) : ℂ :=
  if s ≤ 1/3 then glue F₁ 0 s t else if s ≤ 2/3 then glue F₂ 2 s t else glue F₃ 4 s t

@[simp] lemma glue_apply (F : ℝ → ℝ → ℂ) (c s t : ℝ) :
    glue F c s t = F (Real.smoothTransition (6 * s - c)) t := rfl

lemma concatFam_eq_left (F₁ F₂ F₃ : ℝ → ℝ → ℂ) {s : ℝ} (h : s ≤ 1/3) :
    concatFam F₁ F₂ F₃ s = glue F₁ 0 s :=
  funext (fun t => by rw [concatFam, ite_eq_left h])

lemma concatFam_eq_mid (F₁ F₂ F₃ : ℝ → ℝ → ℂ) {s : ℝ} (h1 : ¬ s ≤ 1/3) (h2 : s ≤ 2/3) :
    concatFam F₁ F₂ F₃ s = glue F₂ 2 s :=
  funext (fun t => by rw [concatFam, ite_eq_right h1, ite_eq_left h2])

lemma concatFam_eq_right (F₁ F₂ F₃ : ℝ → ℝ → ℂ) {s : ℝ} (h1 : ¬ s ≤ 1/3) (h2 : ¬ s ≤ 2/3) :
    concatFam F₁ F₂ F₃ s = glue F₃ 4 s :=
  funext (fun t => by rw [concatFam, ite_eq_right h1, ite_eq_right h2])

theorem loopFamily_concat3 (F₁ F₂ F₃ : ℝ → ℝ → ℂ) (h₁ : IsLoopFamily F₁) (h₂ : IsLoopFamily F₂)
    (h₃ : IsLoopFamily F₃) (h₁₂ : ∀ t, F₁ 1 t = F₂ 0 t) (h₂₃ : ∀ t, F₂ 1 t = F₃ 0 t) :
    ∃ H : ℝ → ℝ → ℂ, IsLoopFamily H ∧ (∀ t, H 0 t = F₁ 0 t) ∧ ∀ t, H 1 t = F₃ 1 t := by
  obtain ⟨hc₁, hp₁, hi₁, him₁⟩ := h₁
  obtain ⟨hc₂, hp₂, hi₂, him₂⟩ := h₂
  obtain ⟨hc₃, hp₃, hi₃, him₃⟩ := h₃
  -- the three pieces are globally smooth
  have hgl₁ : ContDiff ℝ ∞ (fun y : ℝ × ℝ => glue F₁ 0 y.1 y.2) := by unfold glue; fun_prop
  have hgl₂ : ContDiff ℝ ∞ (fun y : ℝ × ℝ => glue F₂ 2 y.1 y.2) := by unfold glue; fun_prop
  have hgl₃ : ContDiff ℝ ∞ (fun y : ℝ × ℝ => glue F₃ 4 y.1 y.2) := by unfold glue; fun_prop
  -- `concatFam` agrees with `glue F₂ 2` on `[1/6, 2/3]`
  have h2eq : ∀ s t, 1/6 ≤ s → s ≤ 2/3 → concatFam F₁ F₂ F₃ s t = glue F₂ 2 s t := by
    intro s t hs1 hs2
    by_cases h : s ≤ 1/3
    · rw [concatFam_eq_left F₁ F₂ F₃ h]
      simp only [glue_apply]
      rw [Real.smoothTransition.one_of_one_le (show (1 : ℝ) ≤ 6 * s - 0 by linarith),
        Real.smoothTransition.zero_of_nonpos (show 6 * s - 2 ≤ 0 by linarith), h₁₂ t]
    · rw [concatFam_eq_mid F₁ F₂ F₃ h hs2]
  -- `concatFam` agrees with `glue F₃ 4` on `[1/2, ∞)`
  have h3eq : ∀ s t, 1/2 ≤ s → concatFam F₁ F₂ F₃ s t = glue F₃ 4 s t := by
    intro s t hs
    by_cases h : s ≤ 1/3
    · exfalso; linarith
    by_cases h2 : s ≤ 2/3
    · rw [concatFam_eq_mid F₁ F₂ F₃ h h2]
      simp only [glue_apply]
      rw [Real.smoothTransition.one_of_one_le (show (1 : ℝ) ≤ 6 * s - 2 by linarith),
        Real.smoothTransition.zero_of_nonpos (show 6 * s - 4 ≤ 0 by linarith), h₂₃ t]
    · rw [concatFam_eq_right F₁ F₂ F₃ h h2]
  refine ⟨concatFam F₁ F₂ F₃, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · -- jointly C^∞: locally `concatFam` is one of the three smooth pieces
    rw [contDiff_iff_contDiffAt]
    rintro ⟨s, t⟩
    by_cases h1 : s < 1/3
    · have hnhds : {y : ℝ × ℝ | y.1 < 1/3} ∈ 𝓝 (⟨s, t⟩ : ℝ × ℝ) :=
        IsOpen.mem_nhds (isOpen_lt continuous_fst continuous_const) h1
      have heq : (fun y : ℝ × ℝ => concatFam F₁ F₂ F₃ y.1 y.2)
          =ᶠ[𝓝 (⟨s, t⟩ : ℝ × ℝ)] (fun y : ℝ × ℝ => glue F₁ 0 y.1 y.2) := by
        filter_upwards [hnhds] with y (hy : y.1 < 1/3)
        rw [concatFam, ite_eq_left (le_of_lt hy)]
      exact (hgl₁.contDiffAt).congr_of_eventuallyEq heq
    · by_cases h3 : 1/2 < s
      · have hnhds : {y : ℝ × ℝ | 1/2 < y.1} ∈ 𝓝 (⟨s, t⟩ : ℝ × ℝ) :=
          IsOpen.mem_nhds (isOpen_lt continuous_const continuous_fst) h3
        have heq : (fun y : ℝ × ℝ => concatFam F₁ F₂ F₃ y.1 y.2)
            =ᶠ[𝓝 (⟨s, t⟩ : ℝ × ℝ)] (fun y : ℝ × ℝ => glue F₃ 4 y.1 y.2) := by
          filter_upwards [hnhds] with y (hy : 1/2 < y.1)
          exact h3eq y.1 y.2 (le_of_lt hy)
        exact (hgl₃.contDiffAt).congr_of_eventuallyEq heq
      · have hs1 : 1/6 < s := by linarith
        have hs2 : s < 2/3 := by linarith
        have hnhds : {y : ℝ × ℝ | 1/6 < y.1 ∧ y.1 < 2/3} ∈ 𝓝 (⟨s, t⟩ : ℝ × ℝ) :=
          IsOpen.mem_nhds ((isOpen_lt continuous_const continuous_fst).inter
            (isOpen_lt continuous_fst continuous_const)) ⟨hs1, hs2⟩
        have heq : (fun y : ℝ × ℝ => concatFam F₁ F₂ F₃ y.1 y.2)
            =ᶠ[𝓝 (⟨s, t⟩ : ℝ × ℝ)] (fun y : ℝ × ℝ => glue F₂ 2 y.1 y.2) := by
          filter_upwards [hnhds] with y (hy : 1/6 < y.1 ∧ y.1 < 2/3)
          exact h2eq y.1 y.2 (le_of_lt hy.1) (le_of_lt hy.2)
        exact (hgl₂.contDiffAt).congr_of_eventuallyEq heq
  · -- 2π-periodicity in `t`
    intro s t
    by_cases h1 : s ≤ 1/3
    · rw [concatFam_eq_left F₁ F₂ F₃ h1]
      simp only [glue_apply]
      exact hp₁ _ _
    · by_cases h2 : s ≤ 2/3
      · rw [concatFam_eq_mid F₁ F₂ F₃ h1 h2]
        simp only [glue_apply]
        exact hp₂ _ _
      · rw [concatFam_eq_right F₁ F₂ F₃ h1 h2]
        simp only [glue_apply]
        exact hp₃ _ _
  · -- embeddedness on the parameter range
    intro s _ t t' heq
    by_cases h1 : s ≤ 1/3
    · rw [concatFam_eq_left F₁ F₂ F₃ h1] at heq
      simp only [glue_apply] at heq
      exact hi₁ _ ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩ t t' heq
    · by_cases h2 : s ≤ 2/3
      · rw [concatFam_eq_mid F₁ F₂ F₃ h1 h2] at heq
        simp only [glue_apply] at heq
        exact hi₂ _ ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩ t t' heq
      · rw [concatFam_eq_right F₁ F₂ F₃ h1 h2] at heq
        simp only [glue_apply] at heq
        exact hi₃ _ ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩ t t' heq
  · -- immersion on the parameter range
    intro s _ t
    by_cases h1 : s ≤ 1/3
    · rw [concatFam_eq_left F₁ F₂ F₃ h1]
      exact him₁ _ ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩ t
    · by_cases h2 : s ≤ 2/3
      · rw [concatFam_eq_mid F₁ F₂ F₃ h1 h2]
        exact him₂ _ ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩ t
      · rw [concatFam_eq_right F₁ F₂ F₃ h1 h2]
        exact him₃ _ ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩ t
  · -- start point
    intro t
    rw [concatFam, ite_eq_left (show (0 : ℝ) ≤ 1/3 by norm_num)]
    simp only [glue_apply]
    rw [show (6 : ℝ) * 0 - 0 = 0 by norm_num, Real.smoothTransition.zero]
  · -- end point
    intro t
    rw [concatFam, ite_eq_right (show ¬ ((1 : ℝ) ≤ 1/3) by norm_num),
      ite_eq_right (show ¬ ((1 : ℝ) ≤ 2/3) by norm_num)]
    simp only [glue_apply]
    rw [show (6 : ℝ) * 1 - 4 = 2 by norm_num,
      Real.smoothTransition.one_of_one_le (show (1 : ℝ) ≤ 2 by norm_num)]

end

end Work.RPB1a
