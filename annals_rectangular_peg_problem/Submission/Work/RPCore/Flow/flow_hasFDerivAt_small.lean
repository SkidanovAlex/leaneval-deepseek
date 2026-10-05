import Mathlib
import Submission.Work.RPCore.Flow.flow_variational_eq

namespace Work.RPCore.Flow

/-- Reversing time turns a "flow function" of `X` into one of `-X`: if `Φ t y` is reached at time
`t` by an integral curve of `X` starting at `y`, then `Φ (-t) y` is reached at time `t` by an
integral curve of `-X` starting at `y`. -/
lemma flow_neg_reverse {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (X : E → E)
    (Φ : ℝ → E → E)
    (hΦ : ∀ t y, ∃ γ : ℝ → E, γ 0 = y ∧ IsIntegralCurve γ (fun _ z => X z) ∧ γ t = Φ t y) :
    ∀ t y, ∃ γ : ℝ → E, γ 0 = y ∧
      IsIntegralCurve γ (fun _ z => -X z) ∧ γ t = (fun r y => Φ (-r) y) t y := by
  intro t y
  obtain ⟨γ, hγ0, hγint, hγval⟩ := hΦ (-t) y
  refine ⟨fun s => γ (-1 * s), ?_, ?_, ?_⟩
  · simpa using hγ0
  · have hfield : ((-1 : ℝ) • ((fun (_ : ℝ) (z : E) => X z) ∘ (fun x : ℝ => x * -1)))
        = (fun (_ : ℝ) (z : E) => -X z) := by
      funext r z
      simp [Function.comp_def]
    have h := hγint.comp_mul (-1)
    rw [hfield] at h
    simpa [Function.comp_def, mul_comm] using h
  · show γ (-1 * t) = Φ (-t) y
    rw [neg_one_mul]
    exact hγval

theorem flow_hasFDerivAt_small {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] (X : E → E) (hX : ContDiff ℝ 1 X) {K : ℝ}
    (hK : ∀ z, ‖fderiv ℝ X z‖ ≤ K) (Φ : ℝ → E → E)
    (hΦ : ∀ t y, ∃ γ : ℝ → E, γ 0 = y ∧ IsIntegralCurve γ (fun _ z => X z) ∧ γ t = Φ t y)
    {t : ℝ} (ht : |t| * K < 1) (z : E) :
    ∃ M : E →L[ℝ] E, HasFDerivAt (Φ t) M z ∧ ‖M - 1‖ ≤ Real.exp (K * |t|) - 1 := by
  rcases lt_trichotomy t 0 with ht' | ht' | ht'
  · -- negative time: reverse the vector field
    have hnegt : 0 < -t := by linarith
    have hnegtK : (-t) * K < 1 := by rwa [abs_of_neg ht'] at ht
    have hY : ContDiff ℝ 1 (fun z : E => -X z) := hX.neg
    have hKY : ∀ w : E, ‖fderiv ℝ (fun z : E => -X z) w‖ ≤ K := by
      intro w
      have h : fderiv ℝ (fun z : E => -X z) w = -fderiv ℝ X w := by
        simp
      rw [h, norm_neg]
      exact hK w
    obtain ⟨M, -, -, hfd, hbdd⟩ :=
      flow_variational_eq (fun z : E => -X z) hY K hKY (fun r y => Φ (-r) y)
        (flow_neg_reverse X Φ hΦ) hnegt hnegtK z
    refine ⟨M (-t), ?_, ?_⟩
    · simpa [neg_neg] using hfd (-t) ⟨hnegt.le, le_rfl⟩
    · rw [abs_of_neg ht']
      exact hbdd (-t) ⟨hnegt.le, le_rfl⟩
  · -- zero time: `Φ 0` is the identity
    subst ht'
    have hfun : Φ 0 = fun y : E => y := funext fun y => Port.ODE.flow_zero Φ hΦ y
    refine ⟨1, ?_, ?_⟩
    · rw [hfun]
      exact hasFDerivAt_id z
    · simp
  · -- positive time
    have htK : t * K < 1 := by rwa [abs_of_pos ht'] at ht
    obtain ⟨M, -, -, hfd, hbdd⟩ := flow_variational_eq X hX K hK Φ hΦ ht' htK z
    refine ⟨M t, hfd t ⟨ht'.le, le_rfl⟩, ?_⟩
    rw [abs_of_pos ht']
    exact hbdd t ⟨ht'.le, le_rfl⟩

end Work.RPCore.Flow
