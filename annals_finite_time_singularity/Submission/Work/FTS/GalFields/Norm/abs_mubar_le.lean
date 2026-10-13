import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.GalFields.Defs
import Submission.Work.FTS.Nonlinear.Open.Main
import Submission.Work.Construction.MufunS

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.GalFields.Norm

/-- **The envelope of the two zero-mode rows is bounded on the smallness ball.**
For `0 < α ≤ 1` and `0 ≤ X ≤ α^{7/4}` one has
`α² + √α·X + α^{-3/2}X² ≤ 3`.

Indeed `α² ≤ 1` (as `α ≤ 1`), `√α·X ≤ 1·1` (as `√α ≤ 1` and `X ≤ α^{7/4} ≤ 1`), and
`α^{-3/2}X² ≤ α^{-3/2}·α^{7/2} = α² ≤ 1` (as `X² ≤ (α^{7/4})² = α^{7/2}`). -/
private lemma env_le_three {α X : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hX0 : 0 ≤ X)
    (hX : X ≤ α ^ (7 / 4 : ℝ)) :
    α ^ 2 + Real.sqrt α * X + α ^ (-(3 / 2 : ℝ)) * X ^ 2 ≤ 3 := by
  have h1 : α ^ 2 ≤ 1 := by
    have h1r : α ^ (2 : ℝ) ≤ 1 := Real.rpow_le_one hα.le hα1 (by norm_num)
    calc α ^ 2 = α ^ (2 : ℝ) := by norm_num
      _ ≤ 1 := h1r
  have hsqrt1 : Real.sqrt α ≤ 1 := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_one hα.le hα1 (by norm_num)
  have hX1 : X ≤ 1 := le_trans hX (Real.rpow_le_one hα.le hα1 (by norm_num))
  have h2 : Real.sqrt α * X ≤ 1 := by
    calc Real.sqrt α * X ≤ 1 * 1 := mul_le_mul hsqrt1 hX1 hX0 (by norm_num)
      _ = 1 := by ring
  have hsq : (α ^ (7 / 4 : ℝ)) ^ 2 = α ^ (7 / 2 : ℝ) := by
    rw [← Real.rpow_natCast (α ^ (7 / 4 : ℝ)) 2]
    rw [← Real.rpow_mul hα.le]
    congr 1
    norm_num
  have hX2 : X ^ 2 ≤ α ^ (7 / 2 : ℝ) := by
    calc X ^ 2 ≤ (α ^ (7 / 4 : ℝ)) ^ 2 := pow_le_pow_left₀ hX0 hX 2
      _ = α ^ (7 / 2 : ℝ) := hsq
  have hmul : α ^ (-(3 / 2 : ℝ)) * α ^ (7 / 2 : ℝ) = α ^ (2 : ℝ) := by
    rw [← Real.rpow_add hα]
    congr 1
    norm_num
  have h3 : α ^ (-(3 / 2 : ℝ)) * X ^ 2 ≤ 1 := by
    calc α ^ (-(3 / 2 : ℝ)) * X ^ 2 ≤ α ^ (-(3 / 2 : ℝ)) * α ^ (7 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_left hX2 (Real.rpow_nonneg hα.le _)
      _ = α ^ (2 : ℝ) := hmul
      _ ≤ 1 := Real.rpow_le_one hα.le hα1 (by norm_num)
  linarith

theorem abs_mubar_le {α₂ Ci Ct Ce Cs : ℝ} {IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ}
    (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂) (hE : Work.FTS.OpenPkg.N4Extra' IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      0 < α → α ≤ 1 → α ≤ α₂ → Work.FTS.Nonlin.GalClass α g →
      Work.FTS.VocabO2.StarPkgo2 α Cs Φs → Work.FTS.VocabO.EllPkgGo α Ce g Φg →
      Work.FTS.Nonlin.Xn α g ≤ α ^ (7 / 4 : ℝ) →
      |Work.Construction.mubar
          (Work.Construction.N0 α (Work.Construction.Ftot α g) g)
          (Work.Construction.N α (Work.Construction.Ftot α g)
            (fun z θ => Φs z θ + Φg z θ))| ≤ K := by
  -- the two zero-mode rows, each with its own uniform constant
  obtain ⟨K0, hK0pos, hK0⟩ := Work.FTS.Nonlinear.Open.Rl0 IP hN hE
  obtain ⟨K1, hK1pos, hK1⟩ := Work.FTS.Nonlinear.Open.Rl1 IP hN hE
  refine ⟨3 * (K0 + K1) + 1, by linarith, ?_⟩
  intro α g Φs Φg hα hα1 hαα₂ hgal hs hell hX
  have hsp : Work.FTS.VocabO.StarPkgo α Cs Φs := hs.toStarPkgo
  have hb0 := hK0 hα hα1 hαα₂ hgal hsp hell
  have hb1 := hK1 hα hα1 hαα₂ hgal hsp hell
  -- the envelope is at most `3` on the smallness ball
  have hX0 : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have henv : α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α g
      + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2 ≤ 3 :=
    env_le_three hα hα1 hX0 hX
  have hb0' : |Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α g) g) 0|
      ≤ K0 * 3 := le_trans hb0 (mul_le_mul_of_nonneg_left henv hK0pos.le)
  have hb1' : |Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α g)
      (fun z θ => Φs z θ + Φg z θ)) 0| ≤ K1 * 3 :=
    le_trans hb1 (mul_le_mul_of_nonneg_left henv hK1pos.le)
  calc |Work.Construction.mubar
        (Work.Construction.N0 α (Work.Construction.Ftot α g) g)
        (Work.Construction.N α (Work.Construction.Ftot α g)
          (fun z θ => Φs z θ + Φg z θ))|
      = |Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α g) g) 0
          + Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α g)
              (fun z θ => Φs z θ + Φg z θ)) 0| := by rw [Work.Construction.mubar]
    _ ≤ |Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α g) g) 0|
        + |Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α g)
            (fun z θ => Φs z θ + Φg z θ)) 0| := abs_add_le _ _
    _ ≤ K0 * 3 + K1 * 3 := add_le_add hb0' hb1'
    _ ≤ 3 * (K0 + K1) + 1 := by linarith

end Work.FTS.GalFields.Norm
