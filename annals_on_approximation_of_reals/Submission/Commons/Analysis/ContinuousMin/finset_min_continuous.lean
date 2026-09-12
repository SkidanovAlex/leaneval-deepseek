import Mathlib.Analysis.Normed.Order.Lattice

noncomputable section

open Filter

namespace Commons.Analysis.ContinuousMin

private lemma min'_image_eq_inf' {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (g : ι → ℝ) :
    (s.image g).min' (Finset.image_nonempty.mpr hs) = s.inf' hs g := by
  classical
  rw [Finset.min'_eq_inf']
  apply le_antisymm
  · -- `(s.image g).inf' _ id` is a lower bound of every `g b`, `b ∈ s`
    refine Finset.le_inf' (s := s) hs g ?_
    intro b hb
    exact Finset.inf'_le (s := s.image g) (f := (fun y : ℝ => y))
      (Finset.mem_image.mpr ⟨b, hb, rfl⟩)
  · -- `s.inf' hs g` is a lower bound of every value occurring in `s.image g`
    refine (Finset.le_inf'_iff (s := s.image g) (Finset.image_nonempty.mpr hs)
      (fun y : ℝ => y)).2 ?_
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨b, hb, rfl⟩
    exact Finset.inf'_le (s := s) (f := g) hb

/-- The minimum over a finite index family of continuous real functions is continuous. -/
theorem finset_min_continuous {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    {f : ι → ℝ → ℝ} (hf : ∀ i ∈ s, Continuous (f i)) :
    Continuous (fun x : ℝ =>
      (s.image (fun i => f i x)).min' (Finset.image_nonempty.mpr hs)) := by
  have hEq : (fun x : ℝ =>
        (s.image (fun i => f i x)).min' (Finset.image_nonempty.mpr hs)) =
      (fun x : ℝ => s.inf' hs (fun i : ι => f i x)) := by
    funext x
    exact min'_image_eq_inf' s hs (fun i => f i x)
  rw [hEq]
  exact Continuous.finset_inf'_apply (L := ℝ) (X := ℝ) (s := s) hs hf

end Commons.Analysis.ContinuousMin