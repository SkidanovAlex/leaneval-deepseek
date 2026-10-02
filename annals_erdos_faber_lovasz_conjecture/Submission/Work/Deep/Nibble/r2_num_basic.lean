import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Nibble.r2_setup
import Submission.Work.Deep.Nibble.log_one_sub_bound
import Submission.Work.Deep.Nibble.r2_num_aux

set_option maxHeartbeats 1000000

namespace Work.Deep.Nibble

theorem r2_num_basic {r : ℕ} (hr : 2 ≤ r) {θ δ ε' ε : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1 / 100) (hδ0 : 0 < δ) (hδ1 : δ ≤ θ / 100)
    (hε'0 : 0 < ε') (hε'1 : ε' ≤ 1 / 2) (hε'2 : 100 * (ε + ε * (r : ℝ) * θ) ≤ ε')
    (hε0 : 0 < ε) (hε1 : ε ≤ θ / 100) (hεδ : 4 * ε ≤ δ) :
    ∃ N : ℕ, ∀ D : ℕ, N ≤ D →
      (1 ≤ D)
      ∧ (θ / (D:ℝ) ≤ 1 / 2)
      ∧ (2 ≤ (1 - ε) * (D:ℝ))
      ∧ (8 * θ^2 ≤ δ * (D:ℝ))
      ∧ (100 * (r:ℝ) * Real.sqrt 2 * Real.exp (2 * θ * ((r:ℝ) - 1)) < ε' * Real.sqrt (D:ℝ))
      ∧ (Work.Deep.Nibble.qV r ε' θ D ≤ 1 / 8)
      ∧ (4 * Work.Deep.Nibble.qV r ε' θ D * (100 * (r:ℝ)^3 * (D:ℝ)^3 + 4) ≤ 1 / 4)
      ∧ (8 * Work.Deep.Nibble.qV r ε' θ D ≤ δ^2 / (128 * (r:ℝ)^2))
      ∧ (8 * Work.Deep.Nibble.qV r ε' θ D ≤ δ^2 * θ^4 / (4096 * (r:ℝ) * (D:ℝ)))
      ∧ (Work.Deep.Nibble.qV r ε' θ D * Work.Deep.Nibble.nThresh r θ δ D ≤ 1 / 16)
      ∧ (48 * (r:ℝ) ≤ δ^2 * θ * (D:ℝ))
      ∧ (1536 * (r:ℝ) ≤ δ^2 * θ^3 * (D:ℝ))
      ∧ (10^4 * (r:ℝ)^2 ≤ δ^2 * (D:ℝ))
      ∧ (Real.log 48 ≤ δ^2 * (D:ℝ) / (128 * (r:ℝ)^2)) := by
  have hr1 : (1:ℝ) ≤ (r:ℝ) := by exact_mod_cast (by omega : 1 ≤ r)
  have hrpos : (0:ℝ) < (r:ℝ) := by linarith
  have hθne : θ ≠ 0 := ne_of_gt hθ0
  have hδne : δ ≠ 0 := ne_of_gt hδ0
  have hε'ne : ε' ≠ 0 := ne_of_gt hε'0
  have hθ2 : θ ≤ 1/2 := by linarith
  have hεle : ε ≤ 1/10000 := by linarith
  have hεlt1 : ε < 1 := by linarith
  have h1εpos : (0:ℝ) < 1 - ε := by linarith
  have h1εne : (1:ℝ) - ε ≠ 0 := ne_of_gt h1εpos
  -- the constant controlling the exponential decay
  set c : ℝ := 100*(r:ℝ)*Real.sqrt 2*Real.exp (2*θ*((r:ℝ)-1))/ε' with hcdef
  have hcnn : (0:ℝ) ≤ c := by rw [hcdef]; positivity
  set c0 : ℝ := ε'^2 * (Real.exp (-(2*θ*(r:ℝ))))^2 / (128 * (r:ℝ)^2) with hc0def
  have hc0pos : (0:ℝ) < c0 := by rw [hc0def]; positivity
  have hc0ne : c0 ≠ 0 := ne_of_gt hc0pos
  have hc04ne : (c0:ℝ)^4 ≠ 0 := pow_ne_zero 4 hc0ne
  -- thresholds
  set t1 : ℝ := 1 with ht1def
  set t2 : ℝ := 2/(1-ε) with ht2def
  set t3 : ℝ := 8*θ^2/δ with ht3def
  set t4 : ℝ := (c+1)^2 with ht4def
  set t5 : ℝ := 32/c0 with ht5def
  set t6 : ℝ := 256*(6400*(r:ℝ)^3+256)/c0^4 with ht6def
  set t7 : ℝ := 4096*(r:ℝ)^2/(c0*δ^2) with ht7def
  set t8 : ℝ := 524288*(r:ℝ)/(c0^2*δ^2*θ^4) with ht8def
  set t9 : ℝ := 256000000*(r:ℝ)/(c0^2*δ^2*θ^4) with ht9def
  set t10 : ℝ := 48*(r:ℝ)/(δ^2*θ) with ht10def
  set t11 : ℝ := 1536*(r:ℝ)/(δ^2*θ^3) with ht11def
  set t12 : ℝ := 10^4*(r:ℝ)^2/δ^2 with ht12def
  set t13 : ℝ := 128*(r:ℝ)^2*Real.log 48/δ^2 with ht13def
  have ht1n : (0:ℝ) ≤ t1 := by rw [ht1def]; norm_num
  have ht2n : (0:ℝ) ≤ t2 := by rw [ht2def]; positivity
  have ht3n : (0:ℝ) ≤ t3 := by rw [ht3def]; positivity
  have ht4n : (0:ℝ) ≤ t4 := by rw [ht4def]; positivity
  have ht5n : (0:ℝ) ≤ t5 := by rw [ht5def]; positivity
  have ht6n : (0:ℝ) ≤ t6 := by rw [ht6def]; positivity
  have ht7n : (0:ℝ) ≤ t7 := by rw [ht7def]; positivity
  have ht8n : (0:ℝ) ≤ t8 := by rw [ht8def]; positivity
  have ht9n : (0:ℝ) ≤ t9 := by rw [ht9def]; positivity
  have ht10n : (0:ℝ) ≤ t10 := by rw [ht10def]; positivity
  have ht11n : (0:ℝ) ≤ t11 := by rw [ht11def]; positivity
  have ht12n : (0:ℝ) ≤ t12 := by rw [ht12def]; positivity
  have ht13n : (0:ℝ) ≤ t13 := by rw [ht13def]; positivity
  refine ⟨⌈t1+t2+t3+t4+t5+t6+t7+t8+t9+t10+t11+t12+t13⌉₊, fun D hD => ?_⟩
  have hDT : t1+t2+t3+t4+t5+t6+t7+t8+t9+t10+t11+t12+t13 ≤ (D:ℝ) := Nat.ceil_le.mp hD
  have hA1 : (1:ℝ) ≤ (D:ℝ) := by linarith
  have hA2 : 2/(1-ε) ≤ (D:ℝ) := by linarith
  have hA3 : 8*θ^2/δ ≤ (D:ℝ) := by linarith
  have hA4 : (c+1)^2 ≤ (D:ℝ) := by linarith
  have hA5 : 32/c0 ≤ (D:ℝ) := by linarith
  have hA6 : 256*(6400*(r:ℝ)^3+256)/c0^4 ≤ (D:ℝ) := by linarith
  have hA7 : 4096*(r:ℝ)^2/(c0*δ^2) ≤ (D:ℝ) := by linarith
  have hA8 : 524288*(r:ℝ)/(c0^2*δ^2*θ^4) ≤ (D:ℝ) := by linarith
  have hA9 : 256000000*(r:ℝ)/(c0^2*δ^2*θ^4) ≤ (D:ℝ) := by linarith
  have hA10 : 48*(r:ℝ)/(δ^2*θ) ≤ (D:ℝ) := by linarith
  have hA11 : 1536*(r:ℝ)/(δ^2*θ^3) ≤ (D:ℝ) := by linarith
  have hA12 : 10^4*(r:ℝ)^2/δ^2 ≤ (D:ℝ) := by linarith
  have hA13 : 128*(r:ℝ)^2*Real.log 48/δ^2 ≤ (D:ℝ) := by linarith
  have hDpos : (0:ℝ) < (D:ℝ) := by linarith
  have hDne : (D:ℝ) ≠ 0 := ne_of_gt hDpos
  -- lower bound on the residual level and on the exponent of `qV`
  have hDlev : (D:ℝ) * Real.exp (-(2*θ*(r:ℝ))) ≤ Dlev r θ D :=
    r2nb_dlev_ge (by omega : 1 ≤ r) hθ0 hθ2 (by exact_mod_cast hA1)
  have hT' : c0 * (D:ℝ) ≤ (ε' * Dlev r θ D)^2 / (128 * (r:ℝ)^2 * (D:ℝ)) := by
    have h1 : ε' * ((D:ℝ) * Real.exp (-(2*θ*(r:ℝ)))) ≤ ε' * Dlev r θ D :=
      mul_le_mul_of_nonneg_left hDlev hε'0.le
    have h2 : (0:ℝ) ≤ ε' * ((D:ℝ) * Real.exp (-(2*θ*(r:ℝ)))) := by positivity
    have h3 : (ε' * ((D:ℝ) * Real.exp (-(2*θ*(r:ℝ)))))^2 ≤ (ε' * Dlev r θ D)^2 :=
      pow_le_pow_left₀ h2 h1 2
    have hden : (0:ℝ) < 128 * (r:ℝ)^2 * (D:ℝ) := by positivity
    have h4 := div_le_div_of_nonneg_right h3 hden.le
    have hkey : (ε' * ((D:ℝ) * Real.exp (-(2*θ*(r:ℝ)))))^2 / (128 * (r:ℝ)^2 * (D:ℝ))
        = c0 * (D:ℝ) := by
      rw [hc0def]; field_simp; try ring_nf
    rwa [hkey] at h4
  have hqVub : qV r ε' θ D ≤ 4 * Real.exp (-(c0 * (D:ℝ))) := by
    have hneg : -((ε' * Dlev r θ D)^2 / (128 * (r:ℝ)^2 * (D:ℝ))) ≤ -(c0 * (D:ℝ)) := by
      linarith [hT']
    have hexp : Real.exp (-((ε' * Dlev r θ D)^2 / (128 * (r:ℝ)^2 * (D:ℝ))))
        ≤ Real.exp (-(c0 * (D:ℝ))) := Real.exp_le_exp.mpr hneg
    have harg : -(ε' * Dlev r θ D)^2 / (128 * (r:ℝ)^2 * (D:ℝ))
        = -((ε' * Dlev r θ D)^2 / (128 * (r:ℝ)^2 * (D:ℝ))) := by ring_nf
    rw [qV, harg]
    linarith [hexp]
  have h4cnn : (0:ℝ) ≤ c0 * (D:ℝ) := (mul_pos hc0pos hDpos).le
  have hepos : (0:ℝ) < Real.exp (-(c0 * (D:ℝ))) := Real.exp_pos _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact_mod_cast hA1
  · have h := div_le_self hθ0.le hA1
    linarith
  · have h3 : (1-ε) * (2/(1-ε)) ≤ (1-ε) * (D:ℝ) := mul_le_mul_of_nonneg_left hA2 h1εpos.le
    have h3' : (1-ε) * (2/(1-ε)) = 2 := by rw [mul_comm, div_mul_cancel₀ 2 h1εne]
    linarith
  · have h4 : δ * (8*θ^2/δ) ≤ δ * (D:ℝ) := mul_le_mul_of_nonneg_left hA3 hδ0.le
    have h4' : δ * (8*θ^2/δ) = 8*θ^2 := by rw [mul_comm, div_mul_cancel₀ (8*θ^2) hδne]
    linarith
  · have hs1 : c+1 ≤ Real.sqrt (D:ℝ) := by
      have h := Real.sqrt_le_sqrt hA4
      rwa [Real.sqrt_sq (by linarith : (0:ℝ) ≤ c+1)] at h
    have hs2 : c < Real.sqrt (D:ℝ) := by linarith
    have hmul : ε' * c < ε' * Real.sqrt (D:ℝ) := mul_lt_mul_of_pos_left hs2 hε'0
    have hcval : ε' * c = 100*(r:ℝ)*Real.sqrt 2*Real.exp (2*θ*((r:ℝ)-1)) := by
      rw [hcdef, mul_div_cancel₀ _ hε'ne]
    rwa [hcval] at hmul
  · have h32 : 32 ≤ c0*(D:ℝ) := by
      have h := mul_le_mul_of_nonneg_left hA5 hc0pos.le
      rwa [mul_div_cancel₀ _ hc0ne] at h
    have hexp32 : (32:ℝ) ≤ Real.exp (c0*(D:ℝ)) := le_trans h32 (r2nb_exp_ge_self h4cnn)
    have hK6 : (32:ℝ) * Real.exp (-(c0*(D:ℝ))) ≤ 1 :=
      r2nb_mul_exp_neg_le_one (by norm_num) hexp32
    calc qV r ε' θ D ≤ 4 * Real.exp (-(c0*(D:ℝ))) := hqVub
      _ ≤ 1/8 := by linarith [hK6]
  · have h6 : 256*(6400*(r:ℝ)^3+256) ≤ c0^4*(D:ℝ) := by
      have h := mul_le_mul_of_nonneg_left hA6 (by positivity : (0:ℝ) ≤ c0^4)
      rwa [mul_div_cancel₀ _ hc04ne] at h
    have h6' : 256*(6400*(r:ℝ)^3+256)*(D:ℝ)^3 ≤ (c0*(D:ℝ))^4 := by
      have h := mul_le_mul_of_nonneg_right h6 (by positivity : (0:ℝ) ≤ (D:ℝ)^3)
      have he : c0^4*(D:ℝ)*(D:ℝ)^3 = (c0*(D:ℝ))^4 := by ring
      rwa [he] at h
    have h6'' : (6400*(r:ℝ)^3+256)*(D:ℝ)^3 ≤ (c0*(D:ℝ))^4/256 := by
      have h := div_le_div_of_nonneg_right h6' (by norm_num : (0:ℝ) ≤ 256)
      have he : 256*(6400*(r:ℝ)^3+256)*(D:ℝ)^3/256 = (6400*(r:ℝ)^3+256)*(D:ℝ)^3 := by
        ring_nf
      rwa [he] at h
    have hsplit : 6400*(r:ℝ)^3*(D:ℝ)^3 + 256 ≤ (6400*(r:ℝ)^3+256)*(D:ℝ)^3 := by
      have h256 : (256:ℝ) ≤ 256*(D:ℝ)^3 := by
        have h1 : (1:ℝ) ≤ (D:ℝ)^3 := one_le_pow₀ hA1
        linarith
      linarith
    have hexpbig : 6400*(r:ℝ)^3*(D:ℝ)^3 + 256 ≤ Real.exp (c0*(D:ℝ)) :=
      le_trans (le_trans hsplit h6'') (r2nb_exp_ge_biquad h4cnn)
    have hYpos : (0:ℝ) < 6400*(r:ℝ)^3*(D:ℝ)^3 + 256 := by positivity
    have hK7 : (6400*(r:ℝ)^3*(D:ℝ)^3 + 256) * Real.exp (-(c0*(D:ℝ))) ≤ 1 :=
      r2nb_mul_exp_neg_le_one hYpos hexpbig
    calc 4 * qV r ε' θ D * (100*(r:ℝ)^3*(D:ℝ)^3 + 4)
        ≤ 4 * (4 * Real.exp (-(c0*(D:ℝ)))) * (100*(r:ℝ)^3*(D:ℝ)^3 + 4) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hqVub (by norm_num)) (by positivity)
      _ = 16 * (100*(r:ℝ)^3*(D:ℝ)^3 + 4) * Real.exp (-(c0*(D:ℝ))) := by ring
      _ ≤ 1/4 := by linarith [hK7]
  · have h7 : 4096*(r:ℝ)^2/δ^2 ≤ c0*(D:ℝ) := by
      have h := mul_le_mul_of_nonneg_left hA7 hc0pos.le
      have he : c0*(4096*(r:ℝ)^2/(c0*δ^2)) = 4096*(r:ℝ)^2/δ^2 := by field_simp; try ring_nf
      rw [he] at h
      linarith [h]
    have hexpY7 : 4096*(r:ℝ)^2/δ^2 ≤ Real.exp (c0*(D:ℝ)) :=
      le_trans h7 (r2nb_exp_ge_self h4cnn)
    have hY7pos : (0:ℝ) < 4096*(r:ℝ)^2/δ^2 :=
      div_pos (mul_pos (by norm_num) (pow_pos hrpos 2)) (pow_pos hδ0 2)
    have hK8 : (4096*(r:ℝ)^2/δ^2) * Real.exp (-(c0*(D:ℝ))) ≤ 1 :=
      r2nb_mul_exp_neg_le_one hY7pos hexpY7
    have hfin8 : 32 * Real.exp (-(c0*(D:ℝ))) ≤ δ^2/(128*(r:ℝ)^2) := by
      rw [le_div_iff₀ (mul_pos (by norm_num) (pow_pos hrpos 2))]
      have h2 := mul_le_mul_of_nonneg_right hK8 (pow_pos hδ0 2).le
      have h3 : (4096*(r:ℝ)^2/δ^2)*Real.exp (-(c0*(D:ℝ)))*δ^2
          = 4096*(r:ℝ)^2*Real.exp (-(c0*(D:ℝ))) := by field_simp; try ring_nf
      rw [h3] at h2
      linarith
    calc 8 * qV r ε' θ D ≤ 8 * (4 * Real.exp (-(c0*(D:ℝ)))) :=
          mul_le_mul_of_nonneg_left hqVub (by norm_num)
      _ = 32 * Real.exp (-(c0*(D:ℝ))) := by ring
      _ ≤ δ^2/(128*(r:ℝ)^2) := hfin8
  · have h8a : 131072*(r:ℝ)/(δ^2*θ^4) ≤ c0^2*(D:ℝ)/4 := by
      have h := mul_le_mul_of_nonneg_left hA8 (by positivity : (0:ℝ) ≤ c0^2/4)
      have he : c0^2/4*(524288*(r:ℝ)/(c0^2*δ^2*θ^4)) = 131072*(r:ℝ)/(δ^2*θ^4) := by
        field_simp; try ring_nf
      rw [he] at h
      linarith [h]
    have h8b : 131072*(r:ℝ)*(D:ℝ)/(δ^2*θ^4) ≤ (c0*(D:ℝ))^2/4 := by
      have h := mul_le_mul_of_nonneg_right h8a hDpos.le
      have he1 : 131072*(r:ℝ)/(δ^2*θ^4)*(D:ℝ) = 131072*(r:ℝ)*(D:ℝ)/(δ^2*θ^4) := by
        rw [div_mul_eq_mul_div]
      have he2 : c0^2*(D:ℝ)/4*(D:ℝ) = (c0*(D:ℝ))^2/4 := by ring
      rw [he1, he2] at h
      exact h
    have hexpY8 : 131072*(r:ℝ)*(D:ℝ)/(δ^2*θ^4) ≤ Real.exp (c0*(D:ℝ)) :=
      le_trans h8b (r2nb_exp_ge_sq h4cnn)
    have hY8pos : (0:ℝ) < 131072*(r:ℝ)*(D:ℝ)/(δ^2*θ^4) :=
      div_pos (mul_pos (mul_pos (by norm_num) hrpos) hDpos)
        (mul_pos (pow_pos hδ0 2) (pow_pos hθ0 4))
    have hK9 : (131072*(r:ℝ)*(D:ℝ)/(δ^2*θ^4)) * Real.exp (-(c0*(D:ℝ))) ≤ 1 :=
      r2nb_mul_exp_neg_le_one hY8pos hexpY8
    have hfin9 : 32 * Real.exp (-(c0*(D:ℝ))) ≤ δ^2*θ^4/(4096*(r:ℝ)*(D:ℝ)) := by
      rw [le_div_iff₀ (mul_pos (mul_pos (by norm_num) hrpos) hDpos)]
      have h2 := mul_le_mul_of_nonneg_right hK9 (mul_pos (pow_pos hδ0 2) (pow_pos hθ0 4)).le
      have h3 : (131072*(r:ℝ)*(D:ℝ)/(δ^2*θ^4))*Real.exp (-(c0*(D:ℝ)))*(δ^2*θ^4)
          = 131072*(r:ℝ)*(D:ℝ)*Real.exp (-(c0*(D:ℝ))) := by field_simp; try ring_nf
      rw [h3] at h2
      linarith
    calc 8 * qV r ε' θ D ≤ 8 * (4 * Real.exp (-(c0*(D:ℝ)))) :=
          mul_le_mul_of_nonneg_left hqVub (by norm_num)
      _ = 32 * Real.exp (-(c0*(D:ℝ))) := by ring
      _ ≤ δ^2*θ^4/(4096*(r:ℝ)*(D:ℝ)) := hfin9
  · have h9a : 64000000*(r:ℝ)/(δ^2*θ^4) ≤ c0^2*(D:ℝ)/4 := by
      have h := mul_le_mul_of_nonneg_left hA9 (by positivity : (0:ℝ) ≤ c0^2/4)
      have he : c0^2/4*(256000000*(r:ℝ)/(c0^2*δ^2*θ^4)) = 64000000*(r:ℝ)/(δ^2*θ^4) := by
        field_simp; try ring_nf
      rw [he] at h
      linarith [h]
    have h9b : 64000000*(r:ℝ)*(D:ℝ)/(δ^2*θ^4) ≤ (c0*(D:ℝ))^2/4 := by
      have h := mul_le_mul_of_nonneg_right h9a hDpos.le
      have he1 : 64000000*(r:ℝ)/(δ^2*θ^4)*(D:ℝ) = 64000000*(r:ℝ)*(D:ℝ)/(δ^2*θ^4) := by
        rw [div_mul_eq_mul_div]
      have he2 : c0^2*(D:ℝ)/4*(D:ℝ) = (c0*(D:ℝ))^2/4 := by ring
      rw [he1, he2] at h
      exact h
    have hexpY9 : 64000000*(r:ℝ)*(D:ℝ)/(δ^2*θ^4) ≤ Real.exp (c0*(D:ℝ)) :=
      le_trans h9b (r2nb_exp_ge_sq h4cnn)
    have hY9pos : (0:ℝ) < 64000000*(r:ℝ)*(D:ℝ)/(δ^2*θ^4) :=
      div_pos (mul_pos (mul_pos (by norm_num) hrpos) hDpos)
        (mul_pos (pow_pos hδ0 2) (pow_pos hθ0 4))
    have hK10 : (64000000*(r:ℝ)*(D:ℝ)/(δ^2*θ^4)) * Real.exp (-(c0*(D:ℝ))) ≤ 1 :=
      r2nb_mul_exp_neg_le_one hY9pos hexpY9
    have hfin10 : 4 * Real.exp (-(c0*(D:ℝ))) * (10^6*(r:ℝ)*(D:ℝ)/(δ^2*θ^4)) ≤ 1/16 := by
      have h2 := mul_le_mul_of_nonneg_right hK10 (mul_pos (pow_pos hδ0 2) (pow_pos hθ0 4)).le
      have h3 : (64000000*(r:ℝ)*(D:ℝ)/(δ^2*θ^4))*Real.exp (-(c0*(D:ℝ)))*(δ^2*θ^4)
          = 64000000*(r:ℝ)*(D:ℝ)*Real.exp (-(c0*(D:ℝ))) := by field_simp; try ring_nf
      rw [h3] at h2
      have h4 : 4 * Real.exp (-(c0*(D:ℝ))) * (10^6*(r:ℝ)*(D:ℝ)/(δ^2*θ^4))
          = 4*10^6*(r:ℝ)*(D:ℝ)*Real.exp (-(c0*(D:ℝ)))/(δ^2*θ^4) := by ring_nf
      rw [h4]
      rw [div_le_iff₀ (mul_pos (pow_pos hδ0 2) (pow_pos hθ0 4))]
      linarith
    calc qV r ε' θ D * nThresh r θ δ D
        = qV r ε' θ D * (10^6*(r:ℝ)*(D:ℝ)/(δ^2*θ^4)) := by rw [nThresh]
      _ ≤ 4 * Real.exp (-(c0*(D:ℝ))) * (10^6*(r:ℝ)*(D:ℝ)/(δ^2*θ^4)) :=
          mul_le_mul_of_nonneg_right hqVub (by positivity)
      _ ≤ 1/16 := hfin10
  · have h := mul_le_mul_of_nonneg_left hA10 (by positivity : (0:ℝ) ≤ δ^2*θ)
    have he : δ^2*θ*(48*(r:ℝ)/(δ^2*θ)) = 48*(r:ℝ) := by field_simp; try ring_nf
    rw [he] at h
    ring_nf at h ⊢
    exact h
  · have h := mul_le_mul_of_nonneg_left hA11 (by positivity : (0:ℝ) ≤ δ^2*θ^3)
    have he : δ^2*θ^3*(1536*(r:ℝ)/(δ^2*θ^3)) = 1536*(r:ℝ) := by field_simp; try ring_nf
    rw [he] at h
    ring_nf at h ⊢
    exact h
  · have h := mul_le_mul_of_nonneg_left hA12 (by positivity : (0:ℝ) ≤ δ^2)
    have he : δ^2*(10^4*(r:ℝ)^2/δ^2) = 10^4*(r:ℝ)^2 := by field_simp; try ring_nf
    rw [he] at h
    ring_nf at h ⊢
    exact h
  · have h := mul_le_mul_of_nonneg_left hA13 (by positivity : (0:ℝ) ≤ δ^2/(128*(r:ℝ)^2))
    have he : δ^2/(128*(r:ℝ)^2)*(128*(r:ℝ)^2*Real.log 48/δ^2) = Real.log 48 := by
      field_simp; try ring_nf
    rw [he] at h
    have he2 : δ^2/(128*(r:ℝ)^2)*(D:ℝ) = δ^2*(D:ℝ)/(128*(r:ℝ)^2) := by ring_nf
    rw [he2] at h
    exact h

end Work.Deep.Nibble
