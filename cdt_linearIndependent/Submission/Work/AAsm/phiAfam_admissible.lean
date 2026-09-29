import Mathlib
import Submission.Work.AAsm.defs

/-!
# Area AAsm — `phiAfam k` is an admissible map (Theorem A assembly)

`φ_A = h ∘ ψ_A` is continuous on the closed unit disc, holomorphic on the open disc, fixes `0`,
and vanishes only at `0` on the closed disc (`ψ_A` maps the closed disc into the open disc, where
the hauptmodul `h` only vanishes at `0`, and `ψ_A` is injective at `0` there).

Consequently every map of the `l = 2` family `φ_A(z/10⁴)`, `φ_A(283z/500)`, `φ_A(z)` — a rescaling
of `φ_A` by a constant of modulus `≤ 1` which is implemented by
`admissible_const_mul` — is an admissible map.
-/

namespace Work.AAsm

open Complex Metric
open Submission.CDTPlan

/-- `ψ_A` maps the closed unit disc into the open unit disc. -/
lemma psiA_mapsTo_ball (hP : PsiAFacts) :
    Set.MapsTo psiA (closedBall (0 : ℂ) 1) (ball (0 : ℂ) 1) := by
  intro z hz
  have h := hP.2.2.2.1 z hz
  simpa only [mem_ball, dist_zero_right] using h

/-- `φ_A = h ∘ ψ_A` is continuous on the closed unit disc. -/
lemma phiA_continuousOn (hP : PsiAFacts) (hM : HauptFacts) :
    ContinuousOn phiA (closedBall (0 : ℂ) 1) :=
  (hM.1.continuousOn).comp hP.1 (psiA_mapsTo_ball hP)

/-- `φ_A = h ∘ ψ_A` is holomorphic on the open unit disc. -/
lemma phiA_differentiableOn (hP : PsiAFacts) (hM : HauptFacts) :
    DifferentiableOn ℂ phiA (ball (0 : ℂ) 1) :=
  hM.1.comp hP.2.1 (fun _ hz => psiA_mapsTo_ball hP (ball_subset_closedBall hz))

/-- `φ_A(0) = 0`. -/
lemma phiA_zero (hP : PsiAFacts) : phiA 0 = 0 := by
  simp [phiA, hP.2.2.1, hauptH]

/-- `φ_A` vanishes only at the origin on the closed unit disc. -/
lemma phiA_eq_zero_of_norm_le_one (hP : PsiAFacts) (hM : HauptFacts) {z : ℂ}
    (hz : ‖z‖ ≤ 1) (h0 : phiA z = 0) : z = 0 := by
  have hzc : z ∈ closedBall (0 : ℂ) 1 := by
    simpa only [mem_closedBall, dist_zero_right] using hz
  have hψ : psiA z = 0 :=
    hM.2.2.1 (psiA z) (psiA_mapsTo_ball hP hzc) (by simpa only [phiA] using h0)
  exact hP.2.2.2.2 z hzc hψ

/-- If `‖c‖ ≤ 1` and `c ≠ 0` then `z ↦ φ_A (c z)` is admissible: `φ_A` is admissible on the
closed disc and the rescaling by `c` maps the closed disc into itself and fixes `0`. -/
lemma admissible_const_mul (hP : PsiAFacts) (hM : HauptFacts) (c : ℂ)
    (hc : ‖c‖ ≤ 1) (hc0 : c ≠ 0) :
    AdmissibleMap (fun z : ℂ => phiA (c * z)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine (phiA_continuousOn hP hM).comp ?_ ?_
    · exact (continuous_const.mul continuous_id).continuousOn
    · intro z hz
      simp only [mem_closedBall, dist_zero_right] at hz ⊢
      rw [norm_mul]
      calc ‖c‖ * ‖z‖ ≤ 1 * 1 := mul_le_mul hc hz (norm_nonneg _) zero_le_one
        _ = 1 := by norm_num
  · refine (phiA_differentiableOn hP hM).comp ?_ ?_
    · exact differentiable_id.differentiableOn.const_mul c
    · intro z hz
      simp only [mem_ball, dist_zero_right] at hz ⊢
      rw [norm_mul]
      nlinarith [norm_nonneg c, norm_nonneg z]
  · simp [phiA_zero hP]
  · intro z hz h0
    have hcz : c * z = 0 := phiA_eq_zero_of_norm_le_one hP hM ?_ h0
    · have hz0 : z = 0 := by
        rcases mul_eq_zero.mp hcz with h | h
        · exact absurd h hc0
        · exact h
      rw [hz0] at hz
      norm_num at hz
    · rw [norm_mul, hz, mul_one]
      exact hc

theorem phiAfam_admissible (hP : Submission.CDTPlan.PsiAFacts)
    (hM : Submission.CDTPlan.HauptFacts) :
    ∀ k : Fin 3, Submission.CDTPlan.AdmissibleMap (Submission.CDTPlan.phiAfam k) := by
  intro k
  have hk : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
  rcases hk with rfl | rfl | rfl
  · rw [show phiAfam 0 = (fun z : ℂ => phiA ((1 / 10000 : ℂ) * z)) from by
      funext z; simp [phiAfam]; congr 1; ring]
    exact admissible_const_mul hP hM (1 / 10000 : ℂ) (by norm_num) (by norm_num)
  · rw [show phiAfam 1 = (fun z : ℂ => phiA ((283 / 500 : ℂ) * z)) from by
      funext z; simp [phiAfam]; congr 1; ring]
    exact admissible_const_mul hP hM (283 / 500 : ℂ) (by norm_num) (by norm_num)
  · rw [show phiAfam 2 = (fun z : ℂ => phiA ((1 : ℂ) * z)) from by
      funext z; simp [phiAfam]]
    simpa using admissible_const_mul hP hM (1 : ℂ) (by norm_num) (by norm_num)

end Work.AAsm
