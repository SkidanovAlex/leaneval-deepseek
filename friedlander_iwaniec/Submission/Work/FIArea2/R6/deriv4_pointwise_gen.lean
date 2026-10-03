import Mathlib
import Submission.Work.FIArea2.R6.GenRegion
import Submission.Work.FIArea2.lemma_7_1

set_option autoImplicit false
set_option maxHeartbeats 2000000

open scoped ContDiff

namespace Work.FIArea2.R6

noncomputable section

/-! ## Faà di Bruno at order `4` -/

/-- Faà di Bruno's formula at order `4` in the one-dimensional case: the fourth derivative of
`F ∘ u` is the sum over the ordered partitions of `{0,1,2,3}`, grouped into the five shapes
`1+1+1+1`, `2+1+1`, `2+2`, `3+1` and `4`.  (Copy of the private lemma of
`Submission/Work/FIArea2/lemma_7_1_deriv4_bound.lean`.) -/
private lemma iteratedDeriv_comp_four (F u : ℝ → ℝ) (hF : ContDiff ℝ 4 F) (hu : ContDiff ℝ 4 u)
    (x : ℝ) :
    iteratedDeriv 4 (F ∘ u) x =
      iteratedDeriv 4 F (u x) * deriv u x ^ 4 +
      6 * iteratedDeriv 3 F (u x) * deriv u x ^ 2 * iteratedDeriv 2 u x +
      3 * iteratedDeriv 2 F (u x) * iteratedDeriv 2 u x ^ 2 +
      4 * iteratedDeriv 2 F (u x) * deriv u x * iteratedDeriv 3 u x +
      deriv F (u x) * iteratedDeriv 4 u x := by
  have h3 : ∀ y, iteratedDeriv 3 (F ∘ u) y =
      iteratedDeriv 3 F (u y) * deriv u y ^ 3 +
      3 * iteratedDeriv 2 F (u y) * iteratedDeriv 2 u y * deriv u y +
      deriv F (u y) * iteratedDeriv 3 u y := fun y =>
    iteratedDeriv_comp_three ((hF.contDiffAt).of_le (by norm_num))
      ((hu.contDiffAt).of_le (by norm_num))
  have dF3 : Differentiable ℝ (iteratedDeriv 3 F) := hF.differentiable_iteratedDeriv 3 (by norm_num)
  have dF2 : Differentiable ℝ (iteratedDeriv 2 F) := hF.differentiable_iteratedDeriv 2 (by norm_num)
  have dF1 : Differentiable ℝ (iteratedDeriv 1 F) := hF.differentiable_iteratedDeriv 1 (by norm_num)
  have hu1 : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hu1' : Differentiable ℝ (iteratedDeriv 1 u) := hu.differentiable_iteratedDeriv 1 (by norm_num)
  have hu2 : Differentiable ℝ (iteratedDeriv 2 u) := hu.differentiable_iteratedDeriv 2 (by norm_num)
  have hu3 : Differentiable ℝ (iteratedDeriv 3 u) := hu.differentiable_iteratedDeriv 3 (by norm_num)
  have hP : DifferentiableAt ℝ (fun y => iteratedDeriv 3 F (u y)) x :=
    dF3.differentiableAt.comp x hu1.differentiableAt
  have hR : DifferentiableAt ℝ (fun y => iteratedDeriv 2 F (u y)) x :=
    dF2.differentiableAt.comp x hu1.differentiableAt
  have hT : DifferentiableAt ℝ (fun y => deriv F (u y)) x := by
    rw [← iteratedDeriv_one (f := F)]
    exact dF1.differentiableAt.comp x hu1.differentiableAt
  have hQ : DifferentiableAt ℝ (fun y => deriv u y) x := by
    rw [← iteratedDeriv_one (f := u)]
    exact hu1'.differentiableAt
  have hS : DifferentiableAt ℝ (fun y => iteratedDeriv 2 u y) x := hu2.differentiableAt
  have hU : DifferentiableAt ℝ (fun y => iteratedDeriv 3 u y) x := hu3.differentiableAt
  have dP : deriv (fun y => iteratedDeriv 3 F (u y)) x = iteratedDeriv 4 F (u x) * deriv u x := by
    rw [show (fun y => iteratedDeriv 3 F (u y)) = (iteratedDeriv 3 F) ∘ u from rfl]
    rw [deriv_comp x dF3.differentiableAt hu1.differentiableAt,
      show deriv (iteratedDeriv 3 F) (u x) = iteratedDeriv 4 F (u x) from by
        rw [← iteratedDeriv_succ]]
  have dR : deriv (fun y => iteratedDeriv 2 F (u y)) x = iteratedDeriv 3 F (u x) * deriv u x := by
    rw [show (fun y => iteratedDeriv 2 F (u y)) = (iteratedDeriv 2 F) ∘ u from rfl]
    rw [deriv_comp x dF2.differentiableAt hu1.differentiableAt,
      show deriv (iteratedDeriv 2 F) (u x) = iteratedDeriv 3 F (u x) from by
        rw [← iteratedDeriv_succ]]
  have dT : deriv (fun y => deriv F (u y)) x = iteratedDeriv 2 F (u x) * deriv u x := by
    rw [← iteratedDeriv_one (f := F)]
    rw [show (fun y => iteratedDeriv 1 F (u y)) = (iteratedDeriv 1 F) ∘ u from rfl]
    rw [deriv_comp x dF1.differentiableAt hu1.differentiableAt,
      show deriv (iteratedDeriv 1 F) (u x) = iteratedDeriv 2 F (u x) from by
        rw [← iteratedDeriv_succ]]
  have dQ : deriv (fun y => deriv u y) x = iteratedDeriv 2 u x := by
    rw [show (fun y => deriv u y) = deriv u from rfl, ← iteratedDeriv_one (f := u),
      ← iteratedDeriv_succ]
  have dS : deriv (fun y => iteratedDeriv 2 u y) x = iteratedDeriv 3 u x := by
    rw [show (fun y => iteratedDeriv 2 u y) = iteratedDeriv 2 u from rfl, ← iteratedDeriv_succ]
  have dU : deriv (fun y => iteratedDeriv 3 u y) x = iteratedDeriv 4 u x := by
    rw [show (fun y => iteratedDeriv 3 u y) = iteratedDeriv 3 u from rfl, ← iteratedDeriv_succ]
  have dQ3 : deriv ((deriv u) ^ 3) x = 3 * deriv u x ^ 2 * iteratedDeriv 2 u x := by
    rw [deriv_pow hQ 3, show deriv (deriv u) x = iteratedDeriv 2 u x from dQ]
    norm_num
  have t1 : deriv (fun y => iteratedDeriv 3 F (u y) * deriv u y ^ 3) x
      = (iteratedDeriv 4 F (u x) * deriv u x) * deriv u x ^ 3
        + iteratedDeriv 3 F (u x) * (3 * deriv u x ^ 2 * iteratedDeriv 2 u x) := by
    rw [show (fun y => iteratedDeriv 3 F (u y) * deriv u y ^ 3)
        = (fun y => iteratedDeriv 3 F (u y)) * (deriv u) ^ 3 from rfl]
    rw [deriv_mul hP (hQ.pow 3)]
    simp only [Pi.pow_apply]
    rw [dP, dQ3]
  have t2 : deriv (fun y => 3 * iteratedDeriv 2 F (u y) * iteratedDeriv 2 u y * deriv u y) x
      = 3 * (deriv (fun y => iteratedDeriv 2 F (u y)) x * iteratedDeriv 2 u x * deriv u x
             + iteratedDeriv 2 F (u x) * deriv (fun y => iteratedDeriv 2 u y) x * deriv u x
             + iteratedDeriv 2 F (u x) * iteratedDeriv 2 u x * deriv (fun y => deriv u y) x) := by
    rw [show (fun y => 3 * iteratedDeriv 2 F (u y) * iteratedDeriv 2 u y * deriv u y)
        = ((fun y => 3 * iteratedDeriv 2 F (u y)) * (fun y => iteratedDeriv 2 u y))
          * (fun y => deriv u y) from by funext y; rfl]
    rw [deriv_mul ((hR.const_mul 3).mul hS) hQ, deriv_mul (hR.const_mul 3) hS,
      deriv_const_mul (3:ℝ) hR]
    simp only [Pi.mul_apply]
    ring
  have t3 : deriv (fun y => deriv F (u y) * iteratedDeriv 3 u y) x
      = deriv (fun y => deriv F (u y)) x * iteratedDeriv 3 u x
        + deriv F (u x) * deriv (fun y => iteratedDeriv 3 u y) x := by
    rw [show (fun y => deriv F (u y) * iteratedDeriv 3 u y)
        = (fun y => deriv F (u y)) * (fun y => iteratedDeriv 3 u y) from rfl]
    rw [deriv_mul hT hU]
  have t1d : DifferentiableAt ℝ (fun y => iteratedDeriv 3 F (u y) * deriv u y ^ 3) x :=
    hP.mul (hQ.pow 3)
  have t2d : DifferentiableAt ℝ
      (fun y => 3 * iteratedDeriv 2 F (u y) * iteratedDeriv 2 u y * deriv u y) x :=
    ((hR.const_mul 3).mul hS).mul hQ
  have t3d : DifferentiableAt ℝ (fun y => deriv F (u y) * iteratedDeriv 3 u y) x := hT.mul hU
  rw [iteratedDeriv_succ,
    show iteratedDeriv 3 (F ∘ u) = fun y => iteratedDeriv 3 F (u y) * deriv u y ^ 3 +
      3 * iteratedDeriv 2 F (u y) * iteratedDeriv 2 u y * deriv u y +
      deriv F (u y) * iteratedDeriv 3 u y from funext h3,
    show (fun y => iteratedDeriv 3 F (u y) * deriv u y ^ 3 +
      3 * iteratedDeriv 2 F (u y) * iteratedDeriv 2 u y * deriv u y +
      deriv F (u y) * iteratedDeriv 3 u y)
      = (fun y => iteratedDeriv 3 F (u y) * deriv u y ^ 3)
        + (fun y => 3 * iteratedDeriv 2 F (u y) * iteratedDeriv 2 u y * deriv u y)
        + (fun y => deriv F (u y) * iteratedDeriv 3 u y) from by funext y; rfl]
  rw [deriv_add (t1d.add t2d) t3d, deriv_add t1d t2d, t1, t2, t3,
    dR, dS, dQ, dT, dU]
  ring

/-- Triangle inequality for a sum of five real numbers. -/
private lemma abs_add_five_le (a b c d e : ℝ) :
    |a + b + c + d + e| ≤ |a| + |b| + |c| + |d| + |e| := by
  calc |a + b + c + d + e| ≤ |a + b + c + d| + |e| := abs_add_le _ _
    _ ≤ (|a + b + c| + |d|) + |e| := by
        have := abs_add_le (a + b + c) d
        linarith [abs_nonneg e]
    _ ≤ ((|a + b| + |c|) + |d|) + |e| := by
        have := abs_add_le (a + b) c
        linarith [abs_nonneg d, abs_nonneg e]
    _ ≤ (((|a| + |b|) + |c|) + |d|) + |e| := by
        have := abs_add_le a b
        linarith [abs_nonneg c, abs_nonneg d, abs_nonneg e]
    _ = |a| + |b| + |c| + |d| + |e| := by ring

/-- **The general Faà di Bruno bound.**  On *any* region `A ≤ g(t₁,t₂) ≤ B` with `B ≤ 64 M`, the
fourth `t₁`-derivative of `s ↦ F(g(s,t₂))` is bounded by `10^11·Cder·M⁻¹(1−γ²)⁻¹`.

Route: mirror `Work.FIArea2.lemma_7_1_deriv4_bound` (which covers `M/4 ≤ g ≤ 4M`), replacing the
region bounds `region_bounds` by the general ones derived from `gq ≤ B ≤ 64M`: with `δ = 1 − γ²`,
`w = M^{1/4}`, `e = δ^{1/4}` one gets `t₁²+t₂² ≤ 16w²/e²`, `|t₁| ≤ 4w/e`,
`|t₁²−γt₂²| ≤ 8w²`, hence `|g'| ≤ 128w³/e`, `|g''| ≤ 192w²/e²`, `|g'''| ≤ 96w/e`, `|g''''| = 24`.
The five Faà di Bruno terms then contribute `268435456 + 18874368 + 110592 + 49152 + 24 =
287469592 < 10^11` times `Cder·M⁻¹δ⁻¹`. -/
private lemma deriv4_gq_bound (M γ A B Cder : ℝ) (F : ℝ → ℝ)
    (hM : 1 ≤ M) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hB : B ≤ 64 * M) (hCder : 1 ≤ Cder)
    (hF : ContDiff ℝ 4 F)
    (hfd : ∀ j : ℕ, j ≤ 4 → ∀ u : ℝ, |iteratedDeriv j F u| ≤ Cder * M ^ (-(j : ℝ)))
    (t₁ t₂ : ℝ) (hreg : A ≤ Work.FIArea2.gq γ t₁ t₂ ∧ Work.FIArea2.gq γ t₁ t₂ ≤ B) :
    |iteratedDeriv 4 (fun s : ℝ => F (Work.FIArea2.gq γ s t₂)) t₁|
      ≤ 10 ^ 11 * Cder * M⁻¹ * (1 - γ ^ 2)⁻¹ := by
  simp only [Work.FIArea2.gq] at hreg ⊢
  have hMpos : 0 < M := by linarith
  have hd0 : 0 < 1 - γ ^ 2 := Work.FIArea2.one_sub_gamma_sq_pos γ hγ0 hγ1
  have hCd0 : 0 ≤ Cder := by linarith
  set w : ℝ := Real.sqrt (Real.sqrt M) with hwdef
  set e : ℝ := Real.sqrt (Real.sqrt (1 - γ ^ 2)) with hedef
  have hwpos : 0 < w := by rw [hwdef]; exact Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hMpos)
  have hepos : 0 < e := by rw [hedef]; exact Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hd0)
  have hw2 : w ^ 2 = Real.sqrt M := by rw [hwdef]; exact Real.sq_sqrt (Real.sqrt_nonneg M)
  have he2 : e ^ 2 = Real.sqrt (1 - γ ^ 2) := by
    rw [hedef]; exact Real.sq_sqrt (Real.sqrt_nonneg _)
  have hw4 : w ^ 4 = M := by
    have h1 : w ^ 4 = (w ^ 2) ^ 2 := by ring
    rw [h1, hw2, Real.sq_sqrt hMpos.le]
  have he4 : e ^ 4 = 1 - γ ^ 2 := by
    have h1 : e ^ 4 = (e ^ 2) ^ 2 := by ring
    rw [h1, he2, Real.sq_sqrt hd0.le]
  have he_le_one : e ≤ 1 := by
    rw [hedef]
    calc Real.sqrt (Real.sqrt (1 - γ ^ 2)) ≤ Real.sqrt 1 := by
          apply Real.sqrt_le_sqrt
          calc Real.sqrt (1 - γ ^ 2) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (by nlinarith)
            _ = 1 := Real.sqrt_one
      _ = 1 := Real.sqrt_one
  set P1 : ℝ := 4 * t₁ ^ 3 - 4 * γ * t₁ * t₂ ^ 2 with hP1def
  set P2 : ℝ := 12 * t₁ ^ 2 - 4 * γ * t₂ ^ 2 with hP2def
  set P3 : ℝ := 24 * t₁ with hP3def
  set gtt : ℝ := t₁ ^ 4 - 2 * γ * t₁ ^ 2 * t₂ ^ 2 + t₂ ^ 4 with hgttdef
  have hsum : t₁ ^ 2 + t₂ ^ 2 ≤ 16 * w ^ 2 / e ^ 2 := by
    have hq := quarter_sq_le_gq γ hγ0 (le_of_lt hγ1) t₁ t₂
    have hle : (1 - γ ^ 2) / 4 * (t₁ ^ 2 + t₂ ^ 2) ^ 2 ≤ 64 * M :=
      le_trans hq (le_trans hreg.2 hB)
    have h4 : (t₁ ^ 2 + t₂ ^ 2) ^ 2 ≤ 256 * M / (1 - γ ^ 2) := by
      have hpos4 : (0 : ℝ) < (1 - γ ^ 2) / 4 := by positivity
      have hcom : (t₁ ^ 2 + t₂ ^ 2) ^ 2 * ((1 - γ ^ 2) / 4) ≤ 64 * M := by
        rw [mul_comm]; exact hle
      have h := (le_div_iff₀ hpos4).mpr hcom
      have h3 : 64 * M / ((1 - γ ^ 2) / 4) = 256 * M / (1 - γ ^ 2) := by
        rw [div_div_eq_mul_div]; ring
      rwa [h3] at h
    have hsq : (t₁ ^ 2 + t₂ ^ 2) ^ 2 ≤ (16 * w ^ 2 / e ^ 2) ^ 2 := by
      have h2 : (16 * w ^ 2 / e ^ 2) ^ 2 = 256 * M / (1 - γ ^ 2) := by
        rw [div_pow, mul_pow, show (w ^ 2) ^ 2 = w ^ 4 from by ring, hw4,
          show (e ^ 2) ^ 2 = e ^ 4 from by ring, he4]
        norm_num
      rw [h2]; exact h4
    have hnn : 0 ≤ t₁ ^ 2 + t₂ ^ 2 := by positivity
    calc t₁ ^ 2 + t₂ ^ 2 = Real.sqrt ((t₁ ^ 2 + t₂ ^ 2) ^ 2) := (Real.sqrt_sq hnn).symm
      _ ≤ Real.sqrt ((16 * w ^ 2 / e ^ 2) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = 16 * w ^ 2 / e ^ 2 := Real.sqrt_sq (by positivity)
  have ht1 : |t₁| ≤ 4 * w / e := by
    have h1 : t₁ ^ 2 ≤ (4 * w / e) ^ 2 := by
      have h2 : (4 * w / e) ^ 2 = 16 * w ^ 2 / e ^ 2 := by field_simp; ring
      rw [h2]; linarith [hsum, sq_nonneg t₂]
    have h3 : |t₁| ^ 2 ≤ (4 * w / e) ^ 2 := by rw [sq_abs]; exact h1
    have h4 := sq_le_sq.mp h3
    rwa [abs_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ 4 * w / e)] at h4
  have hdiff : |t₁ ^ 2 - γ * t₂ ^ 2| ≤ 8 * w ^ 2 := by
    have h1 : (t₁ ^ 2 - γ * t₂ ^ 2) ^ 2 ≤ (8 * w ^ 2) ^ 2 := by
      have hid : (t₁ ^ 2 - γ * t₂ ^ 2) ^ 2
          = (t₁ ^ 4 - 2 * γ * t₁ ^ 2 * t₂ ^ 2 + t₂ ^ 4) - (1 - γ ^ 2) * t₂ ^ 4 := by ring
      have hnn : 0 ≤ (1 - γ ^ 2) * t₂ ^ 4 := by positivity
      have h2 : (8 * w ^ 2) ^ 2 = 64 * M := by
        rw [mul_pow, show (8:ℝ) ^ 2 = 64 from by norm_num,
          show (w ^ 2) ^ 2 = w ^ 4 from by ring, hw4]
      rw [h2, hid]
      linarith [hnn, hreg.2, hB]
    have h3 := sq_le_sq.mp h1
    rwa [abs_of_nonneg (by positivity : (0:ℝ) ≤ 8 * w ^ 2)] at h3
  have hP1 : |P1| ≤ 128 * w ^ 3 / e := by
    rw [hP1def]
    have hid : 4 * t₁ ^ 3 - 4 * γ * t₁ * t₂ ^ 2 = (4 * t₁) * (t₁ ^ 2 - γ * t₂ ^ 2) := by ring
    rw [hid, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 4)]
    calc 4 * |t₁| * |t₁ ^ 2 - γ * t₂ ^ 2| ≤ (4 * (4 * w / e)) * (8 * w ^ 2) :=
          mul_le_mul (by linarith [ht1]) hdiff (abs_nonneg _) (by positivity)
      _ = 128 * w ^ 3 / e := by field_simp; ring
  have hP2 : |P2| ≤ 192 * w ^ 2 / e ^ 2 := by
    rw [hP2def]
    have hid : 12 * t₁ ^ 2 - 4 * γ * t₂ ^ 2 = 4 * (3 * t₁ ^ 2 - γ * t₂ ^ 2) := by ring
    have hle : |3 * t₁ ^ 2 - γ * t₂ ^ 2| ≤ 3 * (t₁ ^ 2 + t₂ ^ 2) := by
      have h1 : 3 * t₁ ^ 2 - γ * t₂ ^ 2 ≤ 3 * (t₁ ^ 2 + t₂ ^ 2) := by nlinarith [hγ0, hγ1]
      have h2 : -(3 * (t₁ ^ 2 + t₂ ^ 2)) ≤ 3 * t₁ ^ 2 - γ * t₂ ^ 2 := by
        nlinarith [hγ0, hγ1, sq_nonneg t₂, sq_nonneg t₁]
      rw [abs_le]; exact ⟨h2, h1⟩
    rw [hid, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 4)]
    calc 4 * |3 * t₁ ^ 2 - γ * t₂ ^ 2| ≤ 4 * (3 * (t₁ ^ 2 + t₂ ^ 2)) := by linarith
      _ ≤ 4 * (3 * (16 * w ^ 2 / e ^ 2)) := by linarith
      _ = 192 * w ^ 2 / e ^ 2 := by field_simp; ring
  have hP3 : |P3| ≤ 96 * w / e := by
    rw [hP3def, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 24)]
    calc 24 * |t₁| ≤ 24 * (4 * w / e) := by linarith [ht1]
      _ = 96 * w / e := by ring
  have hiter : ∀ j : ℕ, j ≤ 4 → |iteratedDeriv j F gtt| ≤ Cder * (w ^ (4 * j))⁻¹ := by
    intro j hj
    have h := hfd j hj gtt
    have hwj : M ^ (-(j:ℝ)) = (w ^ (4 * j))⁻¹ := by
      rw [← hw4, Real.rpow_neg (by positivity), Real.rpow_natCast, ← pow_mul]
    rwa [hwj] at h
  have hA4 : |iteratedDeriv 4 F gtt| ≤ Cder * (w ^ 16)⁻¹ := hiter 4 le_rfl
  have hA3 : |iteratedDeriv 3 F gtt| ≤ Cder * (w ^ 12)⁻¹ := hiter 3 (by norm_num)
  have hA2 : |iteratedDeriv 2 F gtt| ≤ Cder * (w ^ 8)⁻¹ := hiter 2 (by norm_num)
  have hA1 : |iteratedDeriv 1 F gtt| ≤ Cder * (w ^ 4)⁻¹ := hiter 1 (by norm_num)
  have hCn1 : (0:ℝ) ≤ Cder * (w ^ 12)⁻¹ := mul_nonneg hCd0 (by positivity)
  have hCn2 : (0:ℝ) ≤ Cder * (w ^ 8)⁻¹ := mul_nonneg hCd0 (by positivity)
  have hCn3 : (0:ℝ) ≤ Cder * (w ^ 16)⁻¹ := mul_nonneg hCd0 (by positivity)
  have hCn4 : (0:ℝ) ≤ Cder * (w ^ 4)⁻¹ := mul_nonneg hCd0 (by positivity)
  have hGcd : ContDiff ℝ 4 (fun s : ℝ => s ^ 4 - 2 * γ * s ^ 2 * t₂ ^ 2 + t₂ ^ 4) := by fun_prop
  have hGd1 : deriv (fun s : ℝ => s ^ 4 - 2 * γ * s ^ 2 * t₂ ^ 2 + t₂ ^ 4)
      = fun s => 4 * s ^ 3 - 4 * γ * s * t₂ ^ 2 := by
    funext s
    have h1 : HasDerivAt (fun x : ℝ => x ^ 4) (4 * s ^ 3) s := by
      simpa using hasDerivAt_pow 4 s
    have h2 : HasDerivAt (fun x : ℝ => 2 * γ * x ^ 2 * t₂ ^ 2) (2 * γ * (2 * s) * t₂ ^ 2) s := by
      have h3 : HasDerivAt (fun y : ℝ => 2 * γ * y ^ 2) (2 * γ * (2 * s)) s := by
        simpa using (hasDerivAt_pow 2 s).const_mul (2 * γ)
      simpa using h3.mul_const (t₂ ^ 2)
    have h4 : HasDerivAt (fun x : ℝ => x ^ 4 - (2 * γ * x ^ 2 * t₂ ^ 2) + t₂ ^ 4)
        (4 * s ^ 3 - 2 * γ * (2 * s) * t₂ ^ 2) s := (h1.sub h2).add_const (t₂ ^ 4)
    convert h4.deriv using 1
    ring
  have hGd2raw : deriv (fun s : ℝ => 4 * s ^ 3 - 4 * γ * s * t₂ ^ 2)
      = fun s => 12 * s ^ 2 - 4 * γ * t₂ ^ 2 := by
    funext s
    have h1 : HasDerivAt (fun x : ℝ => 4 * x ^ 3) (4 * (3 * s ^ 2)) s := by
      simpa using (hasDerivAt_pow 3 s).const_mul (4:ℝ)
    have h2 : HasDerivAt (fun x : ℝ => 4 * γ * x * t₂ ^ 2) ((4 * γ * 1) * t₂ ^ 2) s :=
      (hasDerivAt_id s).const_mul (4 * γ) |>.mul_const (t₂ ^ 2)
    have h4 : HasDerivAt (fun x : ℝ => 4 * x ^ 3 - 4 * γ * x * t₂ ^ 2)
        (4 * (3 * s ^ 2) - (4 * γ * 1) * t₂ ^ 2) s := h1.sub h2
    convert h4.deriv using 1
    ring
  have hGd3raw : deriv (fun s : ℝ => 12 * s ^ 2 - 4 * γ * t₂ ^ 2) = fun s => 24 * s := by
    funext s
    have h1 : HasDerivAt (fun x : ℝ => 12 * x ^ 2) (12 * (2 * s)) s := by
      simpa using (hasDerivAt_pow 2 s).const_mul (12:ℝ)
    have h4 : HasDerivAt (fun x : ℝ => 12 * x ^ 2 - 4 * γ * t₂ ^ 2) (12 * (2 * s)) s :=
      h1.sub_const (4 * γ * t₂ ^ 2)
    convert h4.deriv using 1
    ring
  have hGd4raw : deriv (fun s : ℝ => 24 * s) = fun _ => (24:ℝ) := by
    funext s
    have h : HasDerivAt (fun x : ℝ => 24 * x) 24 s := by
      simpa using (hasDerivAt_id s).const_mul (24:ℝ)
    exact h.deriv
  have hGd2 : iteratedDeriv 2 (fun s : ℝ => s ^ 4 - 2 * γ * s ^ 2 * t₂ ^ 2 + t₂ ^ 4)
      = fun s => 12 * s ^ 2 - 4 * γ * t₂ ^ 2 := by
    rw [iteratedDeriv_succ, iteratedDeriv_one, hGd1]
    exact hGd2raw
  have hGd3 : iteratedDeriv 3 (fun s : ℝ => s ^ 4 - 2 * γ * s ^ 2 * t₂ ^ 2 + t₂ ^ 4)
      = fun s => 24 * s := by
    rw [iteratedDeriv_succ, hGd2]
    exact hGd3raw
  have hGd4 : iteratedDeriv 4 (fun s : ℝ => s ^ 4 - 2 * γ * s ^ 2 * t₂ ^ 2 + t₂ ^ 4)
      = fun _ => (24:ℝ) := by
    rw [iteratedDeriv_succ, hGd3]
    exact hGd4raw
  have hmain : iteratedDeriv 4 (fun s : ℝ => F (s ^ 4 - 2 * γ * s ^ 2 * t₂ ^ 2 + t₂ ^ 4)) t₁
      = iteratedDeriv 4 F gtt * P1 ^ 4
        + 6 * iteratedDeriv 3 F gtt * P1 ^ 2 * P2
        + 3 * iteratedDeriv 2 F gtt * P2 ^ 2
        + 4 * iteratedDeriv 2 F gtt * P1 * P3
        + iteratedDeriv 1 F gtt * 24 := by
    have h := iteratedDeriv_comp_four F (fun s : ℝ => s ^ 4 - 2 * γ * s ^ 2 * t₂ ^ 2 + t₂ ^ 4)
      hF hGcd t₁
    simp only [hGd1, hGd2, hGd3, hGd4, ← iteratedDeriv_one, ← hP1def, ← hP2def, ← hP3def,
      ← hgttdef] at h
    exact h
  have hT1 : |iteratedDeriv 4 F gtt * P1 ^ 4|
      ≤ 268435456 * (Cder * (M⁻¹ * (1 - γ ^ 2)⁻¹)) := by
    have h4 : |P1| ^ 4 ≤ (128 * w ^ 3 / e) ^ 4 := pow_le_pow_left₀ (abs_nonneg P1) hP1 4
    calc |iteratedDeriv 4 F gtt * P1 ^ 4| = |iteratedDeriv 4 F gtt| * |P1| ^ 4 := by
          rw [abs_mul, abs_pow]
      _ ≤ (Cder * (w ^ 16)⁻¹) * (128 * w ^ 3 / e) ^ 4 :=
          mul_le_mul hA4 h4 (by positivity) hCn3
      _ = 268435456 * (Cder * (M⁻¹ * (1 - γ ^ 2)⁻¹)) := by
          rw [← hw4, show (1:ℝ) - γ ^ 2 = e ^ 4 from he4.symm]
          field_simp; ring
  have hT2 : |6 * iteratedDeriv 3 F gtt * P1 ^ 2 * P2|
      ≤ 18874368 * (Cder * (M⁻¹ * (1 - γ ^ 2)⁻¹)) := by
    have h4 : |P1| ^ 2 ≤ (128 * w ^ 3 / e) ^ 2 := pow_le_pow_left₀ (abs_nonneg P1) hP1 2
    have hstep : 6 * |iteratedDeriv 3 F gtt| * |P1| ^ 2 * |P2| ≤
        6 * (Cder * (w ^ 12)⁻¹) * (128 * w ^ 3 / e) ^ 2 * (192 * w ^ 2 / e ^ 2) :=
      mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hA3 (by norm_num : (0:ℝ) ≤ 6)) h4
        (by positivity) (mul_nonneg (by norm_num) hCn1)) hP2 (abs_nonneg _)
        (mul_nonneg (mul_nonneg (by norm_num) hCn1) (by positivity))
    calc |6 * iteratedDeriv 3 F gtt * P1 ^ 2 * P2|
        = 6 * |iteratedDeriv 3 F gtt| * |P1| ^ 2 * |P2| := by
          simp only [abs_mul, abs_pow, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 6)]
      _ ≤ 6 * (Cder * (w ^ 12)⁻¹) * (128 * w ^ 3 / e) ^ 2 * (192 * w ^ 2 / e ^ 2) := hstep
      _ = 18874368 * (Cder * (M⁻¹ * (1 - γ ^ 2)⁻¹)) := by
          rw [← hw4, show (1:ℝ) - γ ^ 2 = e ^ 4 from he4.symm]
          field_simp; ring
  have hT3 : |3 * iteratedDeriv 2 F gtt * P2 ^ 2|
      ≤ 110592 * (Cder * (M⁻¹ * (1 - γ ^ 2)⁻¹)) := by
    have h4 : |P2| ^ 2 ≤ (192 * w ^ 2 / e ^ 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg P2) hP2 2
    have hstep : 3 * |iteratedDeriv 2 F gtt| * |P2| ^ 2 ≤
        3 * (Cder * (w ^ 8)⁻¹) * (192 * w ^ 2 / e ^ 2) ^ 2 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hA2 (by norm_num : (0:ℝ) ≤ 3)) h4
        (by positivity) (mul_nonneg (by norm_num) hCn2)
    calc |3 * iteratedDeriv 2 F gtt * P2 ^ 2| = 3 * |iteratedDeriv 2 F gtt| * |P2| ^ 2 := by
          simp only [abs_mul, abs_pow, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 3)]
      _ ≤ 3 * (Cder * (w ^ 8)⁻¹) * (192 * w ^ 2 / e ^ 2) ^ 2 := hstep
      _ = 110592 * (Cder * (M⁻¹ * (1 - γ ^ 2)⁻¹)) := by
          rw [← hw4, show (1:ℝ) - γ ^ 2 = e ^ 4 from he4.symm]
          field_simp; ring
  have hT4 : |4 * iteratedDeriv 2 F gtt * P1 * P3|
      ≤ 49152 * (Cder * (M⁻¹ * (1 - γ ^ 2)⁻¹)) := by
    have h45 : |P1| * |P3| ≤ (128 * w ^ 3 / e) * (96 * w / e) :=
      mul_le_mul hP1 hP3 (abs_nonneg P3) (by positivity)
    have h42 : e ^ 4 ≤ e ^ 2 := by
      have h2 : e ^ 2 ≤ 1 := pow_le_one₀ hepos.le he_le_one
      nlinarith [hepos, sq_nonneg (e ^ 2)]
    have hstep : 4 * |iteratedDeriv 2 F gtt| * (|P1| * |P3|) ≤
        4 * (Cder * (w ^ 8)⁻¹) * ((128 * w ^ 3 / e) * (96 * w / e)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hA2 (by norm_num : (0:ℝ) ≤ 4)) h45
        (by positivity) (mul_nonneg (by norm_num) hCn2)
    calc |4 * iteratedDeriv 2 F gtt * P1 * P3|
        = 4 * |iteratedDeriv 2 F gtt| * (|P1| * |P3|) := by
          simp only [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 4)]; ring
      _ ≤ 4 * (Cder * (w ^ 8)⁻¹) * ((128 * w ^ 3 / e) * (96 * w / e)) := hstep
      _ = 49152 * (Cder * ((w ^ 4)⁻¹ * (e ^ 2)⁻¹)) := by field_simp; ring
      _ ≤ 49152 * (Cder * ((w ^ 4)⁻¹ * (e ^ 4)⁻¹)) := by
          have hinv : (e ^ 2)⁻¹ ≤ (e ^ 4)⁻¹ := (inv_le_inv₀ (by positivity) (by positivity)).mpr h42
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hinv (by positivity)) hCd0)
            (by norm_num)
      _ = 49152 * (Cder * (M⁻¹ * (1 - γ ^ 2)⁻¹)) := by rw [← hw4, ← he4]
  have hT5 : |iteratedDeriv 1 F gtt * 24| ≤ 24 * (Cder * (M⁻¹ * (1 - γ ^ 2)⁻¹)) := by
    have h64 : e ^ 4 ≤ 1 := pow_le_one₀ hepos.le he_le_one
    calc |iteratedDeriv 1 F gtt * 24| = |iteratedDeriv 1 F gtt| * 24 := by
          rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 24)]
      _ ≤ (Cder * (w ^ 4)⁻¹) * 24 := mul_le_mul hA1 (le_refl 24) (by norm_num) hCn4
      _ = 24 * (Cder * (w ^ 4)⁻¹) := by ring
      _ ≤ 24 * (Cder * ((w ^ 4)⁻¹ * (e ^ 4)⁻¹)) := by
          have h1 : (1:ℝ) ≤ (e ^ 4)⁻¹ := (one_le_inv₀ (by positivity)).mpr h64
          have h2 : (w ^ 4)⁻¹ ≤ (w ^ 4)⁻¹ * (e ^ 4)⁻¹ := by
            calc (w ^ 4)⁻¹ = (w ^ 4)⁻¹ * 1 := by ring
              _ ≤ (w ^ 4)⁻¹ * (e ^ 4)⁻¹ := mul_le_mul_of_nonneg_left h1 (by positivity)
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hCd0) (by norm_num)
      _ = 24 * (Cder * (M⁻¹ * (1 - γ ^ 2)⁻¹)) := by rw [← hw4, ← he4]
  rw [hmain]
  have hWnn : 0 ≤ Cder * (M⁻¹ * (1 - γ ^ 2)⁻¹) := mul_nonneg hCd0 (by positivity)
  calc |iteratedDeriv 4 F gtt * P1 ^ 4 + 6 * iteratedDeriv 3 F gtt * P1 ^ 2 * P2 +
        3 * iteratedDeriv 2 F gtt * P2 ^ 2 + 4 * iteratedDeriv 2 F gtt * P1 * P3 +
        iteratedDeriv 1 F gtt * 24|
      ≤ |iteratedDeriv 4 F gtt * P1 ^ 4| + |6 * iteratedDeriv 3 F gtt * P1 ^ 2 * P2| +
          |3 * iteratedDeriv 2 F gtt * P2 ^ 2| + |4 * iteratedDeriv 2 F gtt * P1 * P3| +
          |iteratedDeriv 1 F gtt * 24| := abs_add_five_le _ _ _ _ _
    _ ≤ 268435456 * (Cder * (M⁻¹ * (1 - γ ^ 2)⁻¹))
          + 18874368 * (Cder * (M⁻¹ * (1 - γ ^ 2)⁻¹))
          + 110592 * (Cder * (M⁻¹ * (1 - γ ^ 2)⁻¹))
          + 49152 * (Cder * (M⁻¹ * (1 - γ ^ 2)⁻¹))
          + 24 * (Cder * (M⁻¹ * (1 - γ ^ 2)⁻¹)) := by linarith [hT1, hT2, hT3, hT4, hT5]
    _ = 287469592 * (Cder * (M⁻¹ * (1 - γ ^ 2)⁻¹)) := by ring
    _ ≤ 10 ^ 11 * (Cder * (M⁻¹ * (1 - γ ^ 2)⁻¹)) := by nlinarith [hWnn]
    _ = 10 ^ 11 * Cder * M⁻¹ * (1 - γ ^ 2)⁻¹ := by ring

/-- Off the region `regG A B γ`, a majorant supported in `[A,B]` makes `s ↦ F(g(γ,s,t₂))` vanish
near `t₁`, hence all its derivatives vanish there. -/
private lemma iteratedDeriv4_gq_eq_zero_of_notMem_regG (A B γ : ℝ) (F : ℝ → ℝ)
    (hfsupp : ∀ u : ℝ, F u ≠ 0 → A ≤ u ∧ u ≤ B) (t₁ t₂ : ℝ)
    (hout : ¬ (A ≤ Work.FIArea2.gq γ t₁ t₂ ∧ Work.FIArea2.gq γ t₁ t₂ ≤ B)) :
    iteratedDeriv 4 (fun s : ℝ => F (Work.FIArea2.gq γ s t₂)) t₁ = 0 := by
  have hcont : Continuous (fun s : ℝ => Work.FIArea2.gq γ s t₂) := by
    simp only [Work.FIArea2.gq]; fun_prop
  rcases not_and_or.mp hout with h1 | h2
  · have hlt : Work.FIArea2.gq γ t₁ t₂ < A := not_le.mp h1
    exact Work.FIArea2.iteratedDeriv_eq_zero_of_eventuallyEq_zero _ 4 t₁ (by
      filter_upwards [(isOpen_lt hcont continuous_const).mem_nhds hlt] with s hs
      show F (Work.FIArea2.gq γ s t₂) = (0 : ℝ)
      exact f_gq_eq_zero_gen A B γ F hfsupp (fun h => absurd h.1 (not_le.mpr hs)))
  · have hlt : B < Work.FIArea2.gq γ t₁ t₂ := not_le.mp h2
    exact Work.FIArea2.iteratedDeriv_eq_zero_of_eventuallyEq_zero _ 4 t₁ (by
      filter_upwards [(isOpen_lt continuous_const hcont).mem_nhds hlt] with s hs
      show F (Work.FIArea2.gq γ s t₂) = (0 : ℝ)
      exact f_gq_eq_zero_gen A B γ F hfsupp (fun h => absurd h.2 (not_le.mpr hs)))

/-- **The pointwise fourfold-derivative (Faà di Bruno) bound of Lemma 7.1 for the general support
region.**  For a `C⁴` function `F` supported in `[A,B]` with `B ≤ 64 M` and
`|F^{(j)}| ≤ Cder·M^{-j}` (`j ≤ 4`, `Cder ≥ 1`),

  `‖∂₁⁴(F(g(γ,·,t₂)))‖ ≤ 10^11·Cder·M⁻¹(1−γ²)⁻¹·1_{regG A B γ}(t₁,t₂)`.

On `regG A B γ` this is `deriv4_gq_bound`; off it the indicator is `0` and the left-hand side
vanishes. -/
theorem deriv4_pointwise_gen (M γ A B Cder : ℝ) (F : ℝ → ℝ)
    (hM : 1 ≤ M) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hB : B ≤ 64 * M) (hCder : 1 ≤ Cder)
    (hF : ContDiff ℝ 4 F)
    (hfsupp : ∀ u : ℝ, F u ≠ 0 → A ≤ u ∧ u ≤ B)
    (hfd : ∀ j : ℕ, j ≤ 4 → ∀ u : ℝ, |iteratedDeriv j F u| ≤ Cder * M ^ (-(j : ℝ)))
    (t₁ t₂ : ℝ) :
    ‖iteratedDeriv 4 (fun s : ℝ => (F (Work.FIArea2.gq γ s t₂) : ℂ)) t₁‖
      ≤ 10 ^ 11 * Cder * M⁻¹ * (1 - γ ^ 2)⁻¹
        * Set.indicator (Work.FIArea2.R6.regG A B γ) (fun _ => (1 : ℝ)) (t₁, t₂) := by
  have hφ : ContDiff ℝ 4 (fun s : ℝ => F (Work.FIArea2.gq γ s t₂)) := by
    simp only [Work.FIArea2.gq]; fun_prop
  rw [Work.FIArea2.iteratedDeriv_ofReal_comp (fun s : ℝ => F (Work.FIArea2.gq γ s t₂)) hφ
      (le_refl 4) t₁, Complex.norm_real, Real.norm_eq_abs]
  by_cases hmem : (t₁, t₂) ∈ regG A B γ
  · rw [Set.indicator_of_mem hmem, mul_one]
    exact deriv4_gq_bound M γ A B Cder F hM hγ0 hγ1 hB hCder hF hfd t₁ t₂
      ((mem_regG_iff A B γ t₁ t₂).mp hmem)
  · rw [Set.indicator_of_notMem hmem, mul_zero,
      iteratedDeriv4_gq_eq_zero_of_notMem_regG A B γ F hfsupp t₁ t₂ hmem, abs_zero]

end

end Work.FIArea2.R6
