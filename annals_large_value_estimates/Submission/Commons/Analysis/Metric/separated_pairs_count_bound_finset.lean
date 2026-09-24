import Mathlib
import Submission.Commons.Analysis.Metric.separated_pairs_count_bound
import Submission.Commons.Analysis.Metric.one_separated_points_card_le

namespace Commons.Analysis.Metric

theorem separated_pairs_count_bound_finset {ι : Type*} (S : Finset ι) (t : ι → ℝ)
    (hsep : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → 1 ≤ |t a - t b|) (N : ℕ) (c : ι → ℂ) :
    (∑ a ∈ S, ∑ b ∈ S, if |t a - t b| ≤ (N : ℝ) then ‖c a‖ * ‖c b‖ else 0)
      ≤ (2 * (N : ℝ) + 1) * ∑ a ∈ S, ‖c a‖ ^ 2 := by
  classical
  have hinj : Set.InjOn t (↑S : Set ι) := by
    intro x hx y hy hxy
    by_contra hne
    have h := hsep x hx y hy hne
    rw [hxy, sub_self, abs_zero] at h
    norm_num at h
  -- extended coefficient function on ℝ
  let ext : ℝ → ℂ := fun z => if h : ∃ a ∈ S, t a = z then c (Classical.choose h) else 0
  have h_ext : ∀ a ∈ S, ext (t a) = c a := by
    intro a ha
    have hex : ∃ a' ∈ S, t a' = t a := ⟨a, ha, rfl⟩
    have hspec := Classical.choose_spec hex
    have heq : Classical.choose hex = a := hinj hspec.1 ha hspec.2
    simp only [ext, dif_pos hex]
    rw [heq]
  -- separation of the image set
  have hWsep : ∀ x ∈ S.image t, ∀ y ∈ S.image t, x ≠ y → 1 ≤ |x - y| := by
    intro x hx y hy hxy
    rcases Finset.mem_image.mp hx with ⟨a, ha, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨b, hb, rfl⟩
    exact hsep a ha b hb (fun hab => hxy (by rw [hab]))
  -- the reduced double sum
  let H : ℝ → ℝ := fun z => ∑ x ∈ S.image t, (if |z - x| ≤ (N : ℝ) then ‖ext z‖ * ‖ext x‖ else 0)
  have hinner : ∀ a ∈ S,
      (∑ b ∈ S, if |t a - t b| ≤ (N : ℝ) then ‖c a‖ * ‖c b‖ else 0) = H (t a) := by
    intro a ha
    have h1 : H (t a)
        = ∑ b ∈ S, (if |t a - t b| ≤ (N : ℝ) then ‖ext (t a)‖ * ‖ext (t b)‖ else 0) := by
      simp only [H]
      exact Finset.sum_image hinj
    rw [h1]
    apply Finset.sum_congr rfl
    intro b hb
    rw [← h_ext a ha, ← h_ext b hb]
  have hkey : (∑ a ∈ S, ∑ b ∈ S, if |t a - t b| ≤ (N : ℝ) then ‖c a‖ * ‖c b‖ else 0)
      = ∑ z ∈ S.image t, H z := by
    rw [Finset.sum_congr rfl hinner]
    exact (Finset.sum_image (f := H) hinj).symm
  rw [hkey]
  have hsum2 : (∑ z ∈ S.image t, ‖ext z‖ ^ 2) = ∑ a ∈ S, ‖c a‖ ^ 2 := by
    rw [Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro a ha
    rw [h_ext a ha]
  calc ∑ z ∈ S.image t, H z
      ≤ (2 * (N : ℝ) + 1) * ∑ z ∈ S.image t, ‖ext z‖ ^ 2 :=
        separated_pairs_count_bound (S.image t) hWsep N ext
    _ = (2 * (N : ℝ) + 1) * ∑ a ∈ S, ‖c a‖ ^ 2 := by rw [hsum2]

end Commons.Analysis.Metric
