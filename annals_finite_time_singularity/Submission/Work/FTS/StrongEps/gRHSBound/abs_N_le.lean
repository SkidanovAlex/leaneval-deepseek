import Mathlib.Analysis.Complex.Trigonometric
import Submission.Work.Construction.Defs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.gRHSBound

theorem abs_N_le {α B : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hB : 0 ≤ B)
    {F Φ : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hFb : |F z θ| ≤ B) (hpFb : |Work.Spaces.pth F z θ| ≤ B)
    (hDzFb : |Work.Spaces.Dz F z θ| ≤ B)
    (hRopb : |Work.Construction.Rop α (Work.Construction.PhiTil α F Φ) z θ| ≤ B)
    (hUopb : |Work.Construction.Uop α (Work.Construction.PhiTil α F Φ) z θ| ≤ B)
    (hVopb : |Work.Construction.Vop (Work.Construction.PhiTil α F Φ) z θ| ≤ B)
    (hFKb : |Work.Construction.FK F z| ≤ B) :
    |Work.Construction.N α F Φ z θ| ≤ 8 * B ^ 2 := by
  have hαnn : 0 ≤ α := le_of_lt hα
  -- `N` is a sum of five products; bound each of them by a multiple of `B ^ 2`.
  have ht1 : |2 * Work.Construction.Rop α (Work.Construction.PhiTil α F Φ) z θ * F z θ|
      ≤ 2 * B ^ 2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    have h : |Work.Construction.Rop α (Work.Construction.PhiTil α F Φ) z θ| * |F z θ|
        ≤ B * B :=
      mul_le_mul hRopb hFb (abs_nonneg _) hB
    nlinarith [h]
  have ht2 : |2 * Work.Construction.Uop α (Work.Construction.PhiTil α F Φ) z θ
        * Work.Spaces.pth F z θ| ≤ 2 * B ^ 2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    have h : |Work.Construction.Uop α (Work.Construction.PhiTil α F Φ) z θ|
        * |Work.Spaces.pth F z θ| ≤ B * B :=
      mul_le_mul hUopb hpFb (abs_nonneg _) hB
    nlinarith [h]
  have ht3 : |2 * α * Work.Construction.Vop (Work.Construction.PhiTil α F Φ) z θ
        * Work.Spaces.Dz F z θ| ≤ 2 * B ^ 2 := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),
      abs_of_nonneg hαnn]
    have h1 : α * |Work.Construction.Vop (Work.Construction.PhiTil α F Φ) z θ| ≤ 1 * B :=
      mul_le_mul hα1 hVopb (abs_nonneg _) (by norm_num)
    have h2 : (α * |Work.Construction.Vop (Work.Construction.PhiTil α F Φ) z θ|)
        * |Work.Spaces.Dz F z θ| ≤ (1 * B) * B :=
      mul_le_mul h1 hDzFb (abs_nonneg _) (by linarith)
    nlinarith [h2]
  have ht4 : |(1 / 2) * Work.Construction.s2 θ * Work.Construction.FK F z
        * Work.Spaces.pth F z θ| ≤ (1/2) * B ^ 2 := by
    have hs2 : |Work.Construction.s2 θ| ≤ 1 := by
      simp only [Work.Construction.s2]
      exact Real.abs_sin_le_one (2 * θ)
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ (1/2))]
    have h1 : |Work.Construction.s2 θ| * |Work.Construction.FK F z| ≤ 1 * B :=
      mul_le_mul hs2 hFKb (abs_nonneg _) (by norm_num)
    have h2 : (|Work.Construction.s2 θ| * |Work.Construction.FK F z|)
        * |Work.Spaces.pth F z θ| ≤ (1 * B) * B :=
      mul_le_mul h1 hpFb (abs_nonneg _) (by linarith)
    nlinarith [h2]
  have ht5 : |Real.sin θ ^ 2 * Work.Construction.FK F z * F z θ| ≤ B ^ 2 := by
    have hsin : |Real.sin θ ^ 2| ≤ 1 := by
      rw [abs_pow]
      exact pow_le_one₀ (abs_nonneg _) (Real.abs_sin_le_one θ)
    rw [abs_mul, abs_mul]
    have h1 : |Real.sin θ ^ 2| * |Work.Construction.FK F z| ≤ 1 * B :=
      mul_le_mul hsin hFKb (abs_nonneg _) (by norm_num)
    have h2 : (|Real.sin θ ^ 2| * |Work.Construction.FK F z|) * |F z θ| ≤ (1 * B) * B :=
      mul_le_mul h1 hFb (abs_nonneg _) (by linarith)
    nlinarith [h2]
  change |2 * Work.Construction.Rop α (Work.Construction.PhiTil α F Φ) z θ * F z θ
      - 2 * Work.Construction.Uop α (Work.Construction.PhiTil α F Φ) z θ * Work.Spaces.pth F z θ
      - 2 * α * Work.Construction.Vop (Work.Construction.PhiTil α F Φ) z θ * Work.Spaces.Dz F z θ
      - (1 / 2) * Work.Construction.s2 θ * Work.Construction.FK F z * Work.Spaces.pth F z θ
      - Real.sin θ ^ 2 * Work.Construction.FK F z * F z θ| ≤ 8 * B ^ 2
  refine abs_le.mpr ⟨?_, ?_⟩
  · linarith [(abs_le.mp ht1).1, (abs_le.mp ht1).2, (abs_le.mp ht2).1, (abs_le.mp ht2).2,
      (abs_le.mp ht3).1, (abs_le.mp ht3).2, (abs_le.mp ht4).1, (abs_le.mp ht4).2,
      (abs_le.mp ht5).1, (abs_le.mp ht5).2, sq_nonneg B]
  · linarith [(abs_le.mp ht1).1, (abs_le.mp ht1).2, (abs_le.mp ht2).1, (abs_le.mp ht2).2,
      (abs_le.mp ht3).1, (abs_le.mp ht3).2, (abs_le.mp ht4).1, (abs_le.mp ht4).2,
      (abs_le.mp ht5).1, (abs_le.mp ht5).2, sq_nonneg B]

end Work.FTS.StrongEps.gRHSBound
