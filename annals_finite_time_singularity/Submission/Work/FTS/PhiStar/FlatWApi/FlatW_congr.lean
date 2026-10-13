import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.VocabO2
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.PhiStar.FlatWApi

/-! ## `FlatW` depends only on the values on the open quadrant

`FlatW l f K` evaluates `f` and its iterated `∂_z`/`∂_θ` derivatives (the `D_θ`-operators are
pointwise multiplications by `sin 2θ` composed with `∂_θ`) only at points of the open quadrant
`Q = {z > 0, 0 < θ < π/2}`.  On the open set `Q` the operators `∂_z`, `∂_θ` are local: two
functions agreeing on `Q` have agreeing iterated derivatives at every point of `Q`.  Hence
`FlatW l f K` and `FlatW l g K` are equivalent whenever `f = g` on `Q`; the constant is `1`. -/

/-- `∂_z` respects agreement on the open quadrant (the slice at fixed `θ ∈ (0, π/2)` agrees
on a whole neighbourhood of any `z > 0`). -/
private lemma agree_pz {f g : ℝ → ℝ → ℝ}
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → f z θ = g z θ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.pz f z θ = Work.Spaces.pz g z θ := by
  intro z θ hz hθ hπ
  simp only [Work.Spaces.pz]
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
  exact h z' θ hz' hθ hπ

/-- `∂_θ` respects agreement on the open quadrant. -/
private lemma agree_pth {f g : ℝ → ℝ → ℝ}
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → f z θ = g z θ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.pth f z θ = Work.Spaces.pth g z θ := by
  intro z θ hz hθ hπ
  simp only [Work.Spaces.pth]
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [isOpen_Ioo.mem_nhds (show θ ∈ Set.Ioo (0:ℝ) (π/2) from ⟨hθ, hπ⟩)] with θ' hθ'
  exact h z θ' hz hθ'.1 hθ'.2

/-- Iterated `∂_z` respects agreement on the open quadrant. -/
private lemma agree_pzIter {f g : ℝ → ℝ → ℝ}
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → f z θ = g z θ) :
    ∀ k : ℕ, ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
        Work.Spaces.pzIter k f z θ = Work.Spaces.pzIter k g z θ := by
  intro k
  induction k with
  | zero => intro z θ hz hθ hπ; exact h z θ hz hθ hπ
  | succ k ih => intro z θ hz hθ hπ; exact agree_pz ih z θ hz hθ hπ

/-- `D_θ^i ∂_θ` respects agreement on the open quadrant (`D_θ` is multiplication by `sin 2θ`
followed by `∂_θ`, and both operations preserve agreement on the quadrant). -/
private lemma agree_DthIter_pth {f g : ℝ → ℝ → ℝ}
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → f z θ = g z θ) :
    ∀ i : ℕ, ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
        Work.Spaces.DthIter i (Work.Spaces.pth f) z θ
          = Work.Spaces.DthIter i (Work.Spaces.pth g) z θ := by
  intro i
  induction i with
  | zero => intro z θ hz hθ hπ; exact agree_pth h z θ hz hθ hπ
  | succ i ih =>
      intro z θ hz hθ hπ
      have hthis := agree_pth (f := Work.Spaces.DthIter i (Work.Spaces.pth f))
        (g := Work.Spaces.DthIter i (Work.Spaces.pth g)) ih z θ hz hθ hπ
      simp only [Work.Spaces.DthIter_succ, Work.Spaces.Dth]
      rw [hthis]

theorem FlatW_congr : ∃ C : ℝ, 0 < C ∧ ∀ (l : ℕ) (f g : ℝ → ℝ → ℝ) (K : ℝ),
    (∀ z θ : ℝ, 0 < z → 0 < θ → θ < π/2 → f z θ = g z θ) →
    Work.FTS.VocabO2.FlatW l f K → Work.FTS.VocabO2.FlatW l g (C * K) := by
  refine ⟨1, one_pos, ?_⟩
  intro l f g K hag hf z θ hz hθ hπ
  obtain ⟨ha, hb⟩ := hf z θ hz hθ hπ
  refine ⟨?_, ?_⟩
  · intro k hk
    have h1 := ha k hk
    rw [agree_pzIter hag k z θ hz hθ hπ] at h1
    simpa using h1
  · intro k i hki
    have h2 := hb k i hki
    have hD := agree_pzIter (f := Work.Spaces.DthIter i (Work.Spaces.pth f))
      (g := Work.Spaces.DthIter i (Work.Spaces.pth g)) (agree_DthIter_pth hag i)
      k z θ hz hθ hπ
    rw [hD] at h2
    simpa using h2

end Work.FTS.PhiStar.FlatWApi
