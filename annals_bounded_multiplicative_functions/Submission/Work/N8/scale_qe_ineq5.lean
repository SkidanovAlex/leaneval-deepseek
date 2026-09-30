import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.adi_const

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.N8

/-- The elementary real-algebra core of `scale_qe_ineq5`: given
`S = δ⁻¹ ≥ 1 + 3K(c(log 2 + ε) + 2)`, `ε ≤ 1/200`, and the bounds
`P ≤ log 2 + εL`, `(1-2ε)L ≤ M ≤ L` with `L ≥ 200(2K(c log 2 + 1) + 1) + 10`,
we get `2K(cP + M + 1) ≤ S M`. -/
private lemma scale_core {Kk c lg2 ε L S M P : ℝ}
    (hKk : 0 ≤ Kk) (hc : 0 ≤ c) (hlg2 : 0 < lg2) (hε : 0 < ε) (hεle : ε ≤ 1/200)
    (hS : 1 + 3*Kk*(c*(lg2+ε)+2) ≤ S)
    (hP : P ≤ lg2 + ε*L) (hMle : M ≤ L) (hMge : (1-2*ε)*L ≤ M)
    (hL : 200*(2*Kk*(c*lg2+1)+1)+10 ≤ L) :
    2*Kk*(c*P + M + 1) ≤ S*M := by
  have h12 : 0 ≤ 1 - 2*ε := by linarith
  have h16 : 0 ≤ 1 - 6*ε := by linarith
  have h412 : 0 ≤ 4 - 12*ε := by linarith
  have t1 : 0 ≤ 3*c*lg2*(1-2*ε) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hc) (le_of_lt hlg2)) h12
  have t2 : 0 ≤ c*ε*(1-6*ε) := mul_nonneg (mul_nonneg hc (le_of_lt hε)) h16
  have hbracket : 0 ≤ 3*(c*(lg2+ε)+2)*(1-2*ε) - 2*(c*ε+1) := by nlinarith [t1, t2, h412]
  have hge : 0 ≤ c*(lg2+ε) := mul_nonneg hc (by linarith)
  have hKge : 0 ≤ Kk*(c*(lg2+ε)+2) := mul_nonneg hKk (by linarith)
  have hSpos : 0 ≤ S := by nlinarith [hS, hKge]
  have hS12 : (1 + 3*Kk*(c*(lg2+ε)+2))*(1-2*ε) ≤ S*(1-2*ε) :=
    mul_le_mul_of_nonneg_right hS h12
  have hKkbracket : 2*Kk*(c*ε+1) ≤ 3*Kk*(c*(lg2+ε)+2)*(1-2*ε) := by nlinarith [hbracket, hKk]
  have hT : 2*Kk*(c*ε+1) + (1-2*ε) ≤ S*(1-2*ε) := by nlinarith [hS12, hKkbracket]
  have hA0 : 0 ≤ 2*Kk*(c*lg2+1) := by
    have h1 : 0 ≤ c*lg2+1 := by nlinarith [mul_nonneg hc (le_of_lt hlg2)]
    nlinarith [hKk, h1]
  have hLnonneg : 0 ≤ L := by nlinarith [hL, hA0]
  have hstepA : 2*Kk*(c*lg2+1) ≤ (99/100)*L := by nlinarith [hL, hA0]
  have h99 : (99/100:ℝ) ≤ 1 - 2*ε := by linarith
  have hAL : (99/100)*L ≤ (1-2*ε)*L := mul_le_mul_of_nonneg_right h99 hLnonneg
  have hA : 2*Kk*(c*lg2+1) ≤ (1-2*ε)*L := le_trans hstepA hAL
  have hTM : S*(1-2*ε)*L ≤ S*M := by
    have := mul_le_mul_of_nonneg_left hMge hSpos
    nlinarith [this]
  have hTL : (2*Kk*(c*ε+1) + (1-2*ε))*L ≤ S*(1-2*ε)*L :=
    mul_le_mul_of_nonneg_right hT hLnonneg
  have hstep1 : 2*Kk*(c*P + M + 1) ≤ 2*Kk*(c*(lg2+ε*L) + L + 1) := by
    have hcP : c*P ≤ c*(lg2+ε*L) := mul_le_mul_of_nonneg_left hP hc
    have hsum : c*P + M + 1 ≤ c*(lg2+ε*L) + L + 1 := by linarith
    exact mul_le_mul_of_nonneg_left hsum (by linarith)
  have hexp : 2*Kk*(c*(lg2+ε*L) + L + 1) = 2*Kk*(c*lg2+1) + 2*Kk*(c*ε+1)*L := by ring
  linarith [hstep1, hTL, hTM, hA, hexp]

theorem scale_qe_ineq5 (k : ℕ) (θ ε : ℝ) (ℓ : ℕ) (δ : ℝ)
    (hθ₀ : 0 < θ) (hθ₁ : θ < 1 / 2) (hε : 0 < ε) (hεθ : ε ≤ θ / 100) (hδ : 0 < δ)
    (hδbig : 1 + 3 * (Work.BMF.K0c k : ℝ) * ((2 * (ℓ : ℝ) + 2) * (Real.log 2 + ε) + 2) ≤ δ⁻¹) :
    ∃ N : ℝ, ∀ X H P₁ P₂ : ℝ, N ≤ X → X ^ θ ≤ H → H ≤ X ^ (1 - θ) →
      X ^ (ε ^ 2 / 2) ≤ P₁ → P₁ ≤ X ^ ε → X ^ (ε ^ 2 / 2) ≤ P₂ → P₂ ≤ X ^ ε →
      2 * (Work.BMF.K0c k : ℝ) *
          ((2 * (ℓ : ℝ) + 2) * Real.log (2 * P₁) + Real.log (X / (P₁ * P₂)) + 1)
        ≤ (1 / δ) * Real.log (X / (P₁ * P₂)) := by
  have hKk : (0:ℝ) ≤ (Work.BMF.K0c k : ℝ) := by positivity
  have hcc : (0:ℝ) ≤ 2*(ℓ:ℝ)+2 := by
    have hℓ : (0:ℝ) ≤ (ℓ:ℝ) := Nat.cast_nonneg ℓ
    linarith
  have hlg2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hεle200 : ε ≤ 1/200 := by linarith [hεθ, hθ₁]
  have hρ : 0 ≤ ε^2/2 := by positivity
  have hδbig1 : 1 + 3*(Work.BMF.K0c k : ℝ)*((2*(ℓ:ℝ)+2)*(Real.log 2+ε)+2) ≤ 1/δ := by
    rw [one_div]; exact hδbig
  refine ⟨Real.exp (200*(2*(Work.BMF.K0c k : ℝ)*((2*(ℓ:ℝ)+2)*Real.log 2+1)+1)+10), ?_⟩
  intro X H P₁ P₂ hNX hH1 hH2 hP1lo hP1hi hP2lo hP2hi
  have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos _) hNX
  have hlogX : 200*(2*(Work.BMF.K0c k : ℝ)*((2*(ℓ:ℝ)+2)*Real.log 2+1)+1)+10 ≤ Real.log X := by
    have := Real.log_le_log
      (Real.exp_pos (200*(2*(Work.BMF.K0c k : ℝ)*((2*(ℓ:ℝ)+2)*Real.log 2+1)+1)+10)) hNX
    rwa [Real.log_exp] at this
  have h1 : 0 ≤ (2*(ℓ:ℝ)+2)*Real.log 2 + 1 := by
    have := mul_nonneg hcc (le_of_lt hlg2); linarith
  have hA0 : 0 ≤ 2*(Work.BMF.K0c k : ℝ)*((2*(ℓ:ℝ)+2)*Real.log 2 + 1) := by
    nlinarith [hKk, h1]
  have hBpos : 0 < 200*(2*(Work.BMF.K0c k : ℝ)*((2*(ℓ:ℝ)+2)*Real.log 2+1)+1)+10 := by linarith
  have hlogXpos : 0 < Real.log X := lt_of_lt_of_le hBpos hlogX
  have hX1 : 1 < X := (Real.log_pos_iff hXpos.le).mp hlogXpos
  have hP1ge1 : 1 ≤ P₁ := le_trans (Real.one_le_rpow hX1.le hρ) hP1lo
  have hP2ge1 : 1 ≤ P₂ := le_trans (Real.one_le_rpow hX1.le hρ) hP2lo
  have hP1pos : 0 < P₁ := lt_of_lt_of_le one_pos hP1ge1
  have hP2pos : 0 < P₂ := lt_of_lt_of_le one_pos hP2ge1
  have hlogP1le : Real.log P₁ ≤ ε * Real.log X := by
    have h := Real.log_le_log hP1pos hP1hi
    rwa [Real.log_rpow hXpos ε] at h
  have hlogP2le : Real.log P₂ ≤ ε * Real.log X := by
    have h := Real.log_le_log hP2pos hP2hi
    rwa [Real.log_rpow hXpos ε] at h
  have hlogP1ge : 0 ≤ Real.log P₁ := Real.log_nonneg hP1ge1
  have hlogP2ge : 0 ≤ Real.log P₂ := Real.log_nonneg hP2ge1
  have hMdef : Real.log (X/(P₁*P₂)) = Real.log X - (Real.log P₁ + Real.log P₂) := by
    rw [Real.log_div (ne_of_gt hXpos) (ne_of_gt (mul_pos hP1pos hP2pos)),
        Real.log_mul (ne_of_gt hP1pos) (ne_of_gt hP2pos)]
  have hMge : (1-2*ε)*Real.log X ≤ Real.log (X/(P₁*P₂)) := by linarith
  have hMle : Real.log (X/(P₁*P₂)) ≤ Real.log X := by linarith
  have hPle : Real.log (2*P₁) ≤ Real.log 2 + ε * Real.log X := by
    have h := Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (ne_of_gt hP1pos)
    linarith
  exact scale_core hKk hcc hlg2 hε hεle200 hδbig1 hPle hMle hMge hlogX

end Work.N8
