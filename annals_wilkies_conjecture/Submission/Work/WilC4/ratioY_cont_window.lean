import Mathlib
import Submission.Work.WilC4.ErealDefs
import Submission.Work.WilC4.ULPMExp
import Submission.Work.WilC4.slot_aux

namespace Work.WilC4

theorem ratioY_cont_window {k : ℕ}
    {Y : Set (Fin (k + 2) → ℝ)} {B : Set (Fin (k + 1) → ℝ)}
    (hgf : Work.WilC4.GoodFibre Y B) {c : Fin k → ℝ} {M x : ℝ} (hM : 2 ≤ M) (hx : 0 < x)
    (hdeep : Work.WilC4.IsDeepR B c M x) :
    ContinuousOn (fun t : ℝ => Work.WilC4.Route.ratioY Y c t)
      (Set.Ioo (x / M) (M * x / 2)) := by
  -- For `t` in the window `(x/M, Mx/2)`, both `t` and `2t` lie in the deep window
  -- `(x/(2M), 2Mx)` that `B` avoids; there `GoodFibre` makes `valY Y c` continuous and
  -- nowhere zero, so the ratio `valY Y c (2t) / valY Y c t` is continuous.
  have hMpos : 0 < M := by linarith
  have hM1 : (1 : ℝ) ≤ M := by linarith
  have h2M : 0 < 2 * M := by linarith
  have hWcont : ContinuousOn (fun t : ℝ => Work.WilC4.Route.valY Y c t)
      (Set.Ioo (x / (2 * M)) (2 * M * x)) :=
    Work.WilC4.deep_cont hgf hM1 hx hdeep
  have hsub : Set.Ioo (x / M) (M * x / 2) ⊆ Set.Ioo (x / (2 * M)) (2 * M * x) := by
    intro t ht
    refine ⟨?_, ?_⟩
    · have h1 : x / (2 * M) < x / M := by
        rw [div_lt_div_iff₀ h2M hMpos]; nlinarith
      linarith [ht.1]
    · have h1 : M * x / 2 < 2 * M * x := by nlinarith [hMpos, hx]
      linarith [ht.2]
  have hne : ∀ t ∈ Set.Ioo (x / M) (M * x / 2), Work.WilC4.Route.valY Y c t ≠ 0 := fun t ht =>
    (Work.WilC4.deep_val hgf hM1 hx hdeep (hsub ht)).2
  have hmap : Set.MapsTo (fun t : ℝ => 2 * t) (Set.Ioo (x / M) (M * x / 2))
      (Set.Ioo (x / (2 * M)) (2 * M * x)) := by
    intro t ht
    refine ⟨?_, ?_⟩
    · rw [div_lt_iff₀ h2M]
      have ht1 : x < t * M := (div_lt_iff₀ hMpos).mp ht.1
      have ht0 : 0 < t := lt_trans (div_pos hx hMpos) ht.1
      nlinarith [ht1, ht0, hMpos]
    · have h1 : 2 * t < M * x := by
        have := mul_lt_mul_of_pos_left ht.2 (by norm_num : (0 : ℝ) < 2)
        linarith [this]
      have h2 : M * x < 2 * M * x := by nlinarith [hMpos, hx]
      linarith [h1, h2]
  change ContinuousOn (fun t : ℝ => Work.WilC4.Route.valY Y c (2 * t) /
    Work.WilC4.Route.valY Y c t) (Set.Ioo (x / M) (M * x / 2))
  have hdouble : ContinuousOn (fun t : ℝ => 2 * t) (Set.Ioo (x / M) (M * x / 2)) :=
    (continuous_const.mul continuous_id).continuousOn
  have hnum : ContinuousOn (fun t : ℝ => Work.WilC4.Route.valY Y c (2 * t))
      (Set.Ioo (x / M) (M * x / 2)) :=
    hWcont.comp' hdouble hmap
  exact ContinuousOn.div hnum (hWcont.mono hsub) hne

end Work.WilC4
