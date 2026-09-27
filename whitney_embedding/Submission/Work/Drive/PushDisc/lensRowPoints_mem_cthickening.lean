import Mathlib
import Submission.Work.Drive.PushDisc.milnorLens

namespace Work.Drive.PushDisc

open Set Metric

noncomputable section

/-- **Metric formula for the model space.** The distance in `Mdl k = ℝ × ℝ × ℝ^k × ℝ^k`
(products carry the sup metric) is bounded by the maximum of the componentwise distances. -/
lemma dist_mdl_le {k : ℕ} {a b a' b' : ℝ} {u v u' v' : EuclideanSpace ℝ (Fin k)} {δ : ℝ}
    (h1 : |a - a'| ≤ δ) (h2 : |b - b'| ≤ δ) (h3 : ‖u - u'‖ ≤ δ) (h4 : ‖v - v'‖ ≤ δ) :
    dist ((a, b, u, v) : Work.Drive.Whitney.Mdl k) (a', b', u', v') ≤ δ := by
  rw [dist_eq_norm]
  simp only [Prod.mk_sub_mk, Prod.norm_def, Real.norm_eq_abs]
  exact max_le h1 (max_le h2 (max_le h3 h4))

/-- **The `x`-coordinate of the lens.** For `|x| ≤ 1 + δ/4` there is `x₀` with `|x₀| ≤ 1`
(the `x`-range of the lens) and `|x - x₀| ≤ δ/4`. -/
lemma lensBase_exists {x δ : ℝ} (hδ : 0 < δ) (hx : |x| ≤ 1 + δ / 4) :
    ∃ x₀ : ℝ, |x₀| ≤ 1 ∧ |x - x₀| ≤ δ / 4 := by
  have hx2 : x ≤ 1 + δ / 4 := (abs_le.mp hx).2
  have hx3 : -(1 + δ / 4) ≤ x := (abs_le.mp hx).1
  by_cases h1 : 1 ≤ x
  · refine ⟨1, by norm_num, ?_⟩
    rw [abs_of_nonneg (by linarith)]
    linarith
  · by_cases h2 : x ≤ -1
    · refine ⟨-1, by norm_num, ?_⟩
      rw [abs_of_nonpos (by linarith)]
      linarith
    · refine ⟨x, ?_, ?_⟩
      · rw [abs_le]; exact ⟨by linarith, by linarith⟩
      · rw [sub_self, abs_zero]; linarith

/-- **The arch is `δ`-Lipschitz near the lens range.** If `|x| ≤ 1 + δ/4`, `|x₀| ≤ 1` and
`|x - x₀| ≤ δ/4` then `|arch x - arch x₀| ≤ δ`. -/
lemma abs_arch_sub_le {x x₀ δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hx : |x| ≤ 1 + δ / 4) (h0 : |x₀| ≤ 1) (hd : |x - x₀| ≤ δ / 4) :
    |arch x - arch x₀| ≤ δ := by
  have hfac : arch x - arch x₀ = (x₀ - x) * (x₀ + x) := by
    simp only [arch]; ring
  have hsum : |x₀ + x| ≤ 2 + δ / 4 := by
    calc |x₀ + x| ≤ |x₀| + |x| := abs_add_le _ _
      _ ≤ 1 + (1 + δ / 4) := add_le_add h0 hx
      _ = 2 + δ / 4 := by ring
  rw [hfac, abs_mul, abs_sub_comm x₀ x]
  calc |x - x₀| * |x₀ + x| ≤ (δ / 4) * (2 + δ / 4) :=
        mul_le_mul hd hsum (abs_nonneg _) (by linarith)
    _ ≤ δ := by nlinarith [mul_le_mul_of_nonneg_left hδ1 (le_of_lt hδ)]

theorem lensRowPoints_mem_cthickening {k : ℕ} {δ X ε lam : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hX : X ≤ 1 + δ / 4) (hε : 0 ≤ ε) (hεδ : ε ≤ δ)
    (hlam : 0 ≤ lam) (hlamδ : lam ≤ δ / 4) :
    (∀ (x : ℝ) (u : EuclideanSpace ℝ (Fin k)), |x| ≤ X → ‖u‖ ≤ ε →
        ((x, 0, u, 0) : Work.Drive.Whitney.Mdl k) ∈ Metric.cthickening δ
          {ξ : Work.Drive.Whitney.Mdl k |
            (ξ.1, ξ.2.1) ∈ Work.Drive.PushDisc.lensK ∧ ξ.2.2.1 = 0 ∧ ξ.2.2.2 = 0}) ∧
      (∀ (x : ℝ) (w : EuclideanSpace ℝ (Fin k)), |x| ≤ X → ‖w‖ ≤ 1 →
        ((x, Work.Drive.PushDisc.arch x, 0, lam • w) : Work.Drive.Whitney.Mdl k)
          ∈ Metric.cthickening δ
            {ξ : Work.Drive.Whitney.Mdl k |
              (ξ.1, ξ.2.1) ∈ Work.Drive.PushDisc.lensK ∧ ξ.2.2.1 = 0 ∧ ξ.2.2.2 = 0}) := by
  have hδ4 : 0 < δ / 4 := by linarith
  have hδnn : (0 : ℝ) ≤ δ := le_of_lt hδ
  constructor
  · intro x u hx hu
    have hxX : |x| ≤ 1 + δ / 4 := le_trans hx hX
    obtain ⟨x₀, hx₀, hdx⟩ := lensBase_exists hδ hxX
    have hx₀2 : x₀ ^ 2 ≤ 1 := by
      have h := pow_le_pow_left₀ (abs_nonneg x₀) hx₀ 2
      rwa [sq_abs, one_pow] at h
    have hmem : ((x₀, 0, 0, 0) : Work.Drive.Whitney.Mdl k) ∈
        {ξ : Work.Drive.Whitney.Mdl k |
          (ξ.1, ξ.2.1) ∈ Work.Drive.PushDisc.lensK ∧ ξ.2.2.1 = 0 ∧ ξ.2.2.2 = 0} := by
      refine ⟨⟨hx₀, le_refl 0, ?_⟩, rfl, rfl⟩
      simp only [arch]; linarith
    have hdist : dist ((x, 0, u, 0) : Work.Drive.Whitney.Mdl k)
        ((x₀, 0, 0, 0) : Work.Drive.Whitney.Mdl k) ≤ δ := by
      refine dist_mdl_le ?_ ?_ ?_ ?_
      · linarith
      · rw [sub_self, abs_zero]; exact hδnn
      · rw [sub_zero]; exact le_trans hu hεδ
      · rw [sub_self, norm_zero]; exact hδnn
    exact Metric.mem_cthickening_of_dist_le _ _ δ _ hmem hdist
  · intro x w hx hw
    have hxX : |x| ≤ 1 + δ / 4 := le_trans hx hX
    obtain ⟨x₀, hx₀, hdx⟩ := lensBase_exists hδ hxX
    have hx₀2 : x₀ ^ 2 ≤ 1 := by
      have h := pow_le_pow_left₀ (abs_nonneg x₀) hx₀ 2
      rwa [sq_abs, one_pow] at h
    have harch : |arch x - arch x₀| ≤ δ := abs_arch_sub_le hδ hδ1 hxX hx₀ hdx
    have hlamw : ‖lam • w - 0‖ ≤ δ := by
      rw [sub_zero, norm_smul, Real.norm_eq_abs, abs_of_nonneg hlam]
      nlinarith [hw, hlamδ, hδ, hlam]
    have hmem : ((x₀, arch x₀, 0, 0) : Work.Drive.Whitney.Mdl k) ∈
        {ξ : Work.Drive.Whitney.Mdl k |
          (ξ.1, ξ.2.1) ∈ Work.Drive.PushDisc.lensK ∧ ξ.2.2.1 = 0 ∧ ξ.2.2.2 = 0} := by
      refine ⟨⟨hx₀, ?_, le_refl _⟩, rfl, rfl⟩
      simp only [arch]; linarith
    have hdist : dist ((x, arch x, 0, lam • w) : Work.Drive.Whitney.Mdl k)
        ((x₀, arch x₀, 0, 0) : Work.Drive.Whitney.Mdl k) ≤ δ := by
      refine dist_mdl_le ?_ harch ?_ hlamw
      · linarith
      · rw [sub_self, norm_zero]; exact hδnn
    exact Metric.mem_cthickening_of_dist_le _ _ δ _ hmem hdist

end

end Work.Drive.PushDisc
