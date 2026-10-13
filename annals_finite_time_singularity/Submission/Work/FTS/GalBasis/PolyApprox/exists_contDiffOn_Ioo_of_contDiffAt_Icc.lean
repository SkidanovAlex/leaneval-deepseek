import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.GalBasis.PolyApprox

open Filter Topology

/-- If `f` is `C^4` at a point `a`, then it is `C^4` on some open interval `(a - r, a + r)`
around `a`. -/
lemma exists_Ioo_contDiffOn_of_contDiffAt {f : ℝ → ℝ} {a : ℝ} (ha : ContDiffAt ℝ 4 f a) :
    ∃ r > 0, ContDiffOn ℝ 4 f (Set.Ioo (a - r) (a + r)) := by
  rw [← contDiffWithinAt_univ] at ha
  rw [contDiffWithinAt_iff_contDiffOn_nhds (by norm_num)] at ha
  obtain ⟨u, hu, huC⟩ := ha
  have hu' : u ∈ 𝓝 a := by
    rw [show insert a (Set.univ : Set ℝ) = Set.univ from by simp] at hu
    rwa [nhdsWithin_univ] at hu
  obtain ⟨ε, hε, hεu⟩ := Metric.mem_nhds_iff.mp hu'
  exact ⟨ε, hε, huC.mono (by rw [Real.ball_eq_Ioo] at hεu; exact hεu)⟩

/-- A function which is `C^4` at every point of a closed interval `[a, b]` is `C^4` on a
strictly larger open interval `(c, d)`: take `c` slightly below `a` and `d` slightly above
`b` using the local regularity at the two endpoints. -/
theorem exists_contDiffOn_Ioo_of_contDiffAt_Icc {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ x ∈ Set.Icc a b, ContDiffAt ℝ 4 f x) :
    ∃ c d : ℝ, c < a ∧ b < d ∧ Set.Icc a b ⊆ Set.Ioo c d ∧ ContDiffOn ℝ 4 f (Set.Ioo c d) := by
  obtain ⟨ra, hra, hraC⟩ : ∃ r > 0, ContDiffOn ℝ 4 f (Set.Ioo (a - r) (a + r)) :=
    exists_Ioo_contDiffOn_of_contDiffAt (hf a ⟨le_refl a, hab⟩)
  obtain ⟨rb, hrb, hrbC⟩ : ∃ r > 0, ContDiffOn ℝ 4 f (Set.Ioo (b - r) (b + r)) :=
    exists_Ioo_contDiffOn_of_contDiffAt (hf b ⟨hab, le_refl b⟩)
  refine ⟨a - ra / 2, b + rb / 2, by linarith, by linarith, ?_, ?_⟩
  · intro x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  · rw [isOpen_Ioo.contDiffOn_iff]
    intro y hy
    rcases lt_or_ge y a with hya | hya
    · exact (isOpen_Ioo.contDiffOn_iff.mp hraC) ⟨by linarith [hy.1, hra], by linarith [hy.2, hra]⟩
    · by_cases hyb : y ≤ b
      · exact hf y ⟨hya, hyb⟩
      · exact (isOpen_Ioo.contDiffOn_iff.mp hrbC)
          ⟨by linarith [hy.1, not_le.mp hyb], by linarith [hy.2, hrb]⟩

end Work.FTS.GalBasis.PolyApprox
