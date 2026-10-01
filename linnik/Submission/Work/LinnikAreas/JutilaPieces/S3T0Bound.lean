import Mathlib
import Submission.Work.LinnikAreas.JutilaPieces.S3FloorDefs

namespace Work.LinnikAreas.JutilaPieces

lemma log_nat_nonneg (z : ℕ) : 0 ≤ Real.log (z : ℝ) := by
  rcases Nat.eq_zero_or_pos z with h | h
  · subst h; simp
  · exact Real.log_nonneg (by exact_mod_cast h)

/-- `log u ≤ 4 u^{1/4}` for `u ≥ 1`. -/
lemma log_le_four_rpow (u : ℝ) (hu : 1 ≤ u) : Real.log u ≤ 4 * u^(1/4:ℝ) := by
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have h1 : Real.log (u^(1/4:ℝ)) = (1/4:ℝ) * Real.log u := Real.log_rpow hu0 (1/4)
  have h2 : Real.log (u^(1/4:ℝ)) ≤ u^(1/4:ℝ) - 1 :=
    Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hu0 _)
  have h3 : 0 ≤ u^(1/4:ℝ) := Real.rpow_nonneg hu0.le _
  linarith

lemma s3T0_mono (c : ℝ) : Monotone (fun z : ℕ => s3T0 c z) := by
  refine monotone_nat_of_le_succ (fun z => ?_)
  have h1 : Real.log (z:ℝ) ≤ Real.log ((z+1 : ℕ):ℝ) := by
    rcases Nat.eq_zero_or_pos z with h | h
    · subst h; simp
    · exact Real.log_le_log (by exact_mod_cast h) (by push_cast; linarith)
  have h2 : Real.log (Real.log (z:ℝ)+2) ≤ Real.log (Real.log ((z+1:ℕ):ℝ)+2) := by
    apply Real.log_le_log
    · linarith [log_nat_nonneg z]
    · linarith
  have h4 : 0 ≤ Real.log (Real.log (z:ℝ)+2)+1 := by
    have := Real.log_nonneg (show (1:ℝ) ≤ Real.log (z:ℝ)+2 by linarith [log_nat_nonneg z])
    linarith
  have h3 : Real.log (Real.log (z:ℝ)+2)+1 ≤ Real.log (Real.log ((z+1:ℕ):ℝ)+2)+1 := by linarith
  have h5 : (Real.log (Real.log (z:ℝ)+2)+1)^2 ≤ (Real.log (Real.log ((z+1:ℕ):ℝ)+2)+1)^2 :=
    pow_le_pow_left₀ h4 h3 2
  have h6 : 0 ≤ 25/c^2 := by positivity
  have h7 : 25*(Real.log (Real.log (z:ℝ)+2)+1)^2/c^2
      ≤ 25*(Real.log (Real.log ((z+1:ℕ):ℝ)+2)+1)^2/c^2 := by
    have h8 : 25*(Real.log (Real.log (z:ℝ)+2)+1)^2/c^2
        = (25/c^2)*(Real.log (Real.log (z:ℝ)+2)+1)^2 := by ring
    have h9 : 25*(Real.log (Real.log ((z+1:ℕ):ℝ)+2)+1)^2/c^2
        = (25/c^2)*(Real.log (Real.log ((z+1:ℕ):ℝ)+2)+1)^2 := by ring
    rw [h8, h9]; exact mul_le_mul_of_nonneg_left h5 h6
  have := Nat.ceil_mono (Real.exp_le_exp.mpr h7)
  simp only [s3T0]
  exact add_le_add this le_rfl

/-- `u ^ 3 ≤ exp (u/4)` for `u ≥ 256`. -/
lemma s3T0_cube_le_exp (u : ℝ) (hu : 256 ≤ u) : u^3 ≤ Real.exp (u/4) := by
  have hu0 : 0 < u := by linarith
  have hu1 : 1 ≤ u := by linarith
  have h1 : Real.log u ≤ 4 * u^(1/4:ℝ) := log_le_four_rpow u hu1
  have h4 : (256:ℝ)^(1/4:ℝ) = 4 := by
    have e : (256:ℝ) = (4:ℝ)^(4:ℕ) := by norm_num
    rw [e, ← Real.rpow_natCast (4:ℝ) 4, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 4)]
    rw [show ((4:ℕ):ℝ) * (1/4:ℝ) = 1 by norm_num, Real.rpow_one]
  have hw : (4:ℝ) ≤ u^(1/4:ℝ) := by
    have h := Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 256) hu (by norm_num : (0:ℝ) ≤ (1/4:ℝ))
    rwa [h4] at h
  have hwu : (0:ℝ) ≤ u^(1/4:ℝ) := Real.rpow_nonneg hu0.le _
  have hpow4 : (u^(1/4:ℝ))^4 = u := by
    rw [← Real.rpow_natCast (u^(1/4:ℝ)) 4, ← Real.rpow_mul hu0.le]
    rw [show (1/4:ℝ) * ((4:ℕ):ℝ) = 1 by norm_num, Real.rpow_one]
  have h64 : (48:ℝ) ≤ (u^(1/4:ℝ))^3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 4) hw 3
    norm_num at h
    linarith
  have h48 : 48 * u^(1/4:ℝ) ≤ u := by
    have hprod : (u^(1/4:ℝ))^3 * u^(1/4:ℝ) = (u^(1/4:ℝ))^4 := by ring
    have h : 48 * u^(1/4:ℝ) ≤ (u^(1/4:ℝ))^3 * u^(1/4:ℝ) :=
      mul_le_mul_of_nonneg_right h64 hwu
    rwa [hprod, hpow4] at h
  have h2 : Real.log (u^3) ≤ u/4 := by
    rw [Real.log_pow]
    push_cast
    linarith [h1, h48]
  calc u^3 = Real.exp (Real.log (u^3)) := (Real.exp_log (by positivity)).symm
    _ ≤ Real.exp (u/4) := Real.exp_le_exp.mpr h2

/-- The large-`z` estimate: if `2 ≤ L` and `(5000/c²)² ≤ L` then
`25 (log(L+2)+1)²/c² ≤ L/4`. -/
lemma s3T0_exp_arg_le_quarter (c L : ℝ) (hc : 0 < c)
    (hL2 : 2 ≤ L) (hLbig : (5000 / c^2)^2 ≤ L) :
    25 * (Real.log (L + 2) + 1)^2 / c^2 ≤ L / 4 := by
  have hc2 : 0 < c^2 := by positivity
  have hLpos : 0 < L := by linarith
  have hLp21 : (1:ℝ) ≤ L + 2 := by linarith
  have hlog : Real.log (L + 2) ≤ 4 * (L + 2)^(1/4:ℝ) := log_le_four_rpow _ hLp21
  have hlog0 : 0 ≤ Real.log (L + 2) := Real.log_nonneg hLp21
  have hw1 : (1:ℝ) ≤ (L + 2)^(1/4:ℝ) := Real.one_le_rpow hLp21 (by norm_num : (0:ℝ) ≤ (1/4:ℝ))
  have ha : Real.log (L + 2) + 1 ≤ 5 * (L + 2)^(1/4:ℝ) := by linarith
  have ha0 : 0 ≤ Real.log (L + 2) + 1 := by linarith
  have hsq : (Real.log (L + 2) + 1)^2 ≤ 25 * (L + 2)^(1/2:ℝ) := by
    have h1 : (Real.log (L + 2) + 1)^2 ≤ (5 * (L + 2)^(1/4:ℝ))^2 := pow_le_pow_left₀ ha0 ha 2
    have h2 : (5 * (L + 2)^(1/4:ℝ))^2 = 25 * ((L + 2)^(1/4:ℝ))^2 := by ring
    have h3 : ((L + 2)^(1/4:ℝ))^2 = (L + 2)^(1/2:ℝ) := by
      rw [← Real.rpow_natCast ((L + 2)^(1/4:ℝ)) 2, ← Real.rpow_mul (by linarith : (0:ℝ) ≤ L + 2)]
      rw [show (1/4:ℝ) * ((2:ℕ):ℝ) = 1/2 by norm_num]
    linarith [h1, h2, h3]
  have hhalf : (L + 2)^(1/2:ℝ) ≤ 2 * L^(1/2:ℝ) := by
    have hle : L + 2 ≤ 4 * L := by linarith
    have h1 : (L + 2)^(1/2:ℝ) ≤ (4 * L)^(1/2:ℝ) :=
      Real.rpow_le_rpow (by linarith : (0:ℝ) ≤ L + 2) hle (by norm_num : (0:ℝ) ≤ (1/2:ℝ))
    have h2 : (4 * L)^(1/2:ℝ) = (4:ℝ)^(1/2:ℝ) * L^(1/2:ℝ) :=
      Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) hLpos.le
    have h3 : (4:ℝ)^(1/2:ℝ) = 2 := by
      have e : (4:ℝ) = (2:ℝ)^(2:ℕ) := by norm_num
      rw [e, ← Real.rpow_natCast (2:ℝ) 2, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
      rw [show ((2:ℕ):ℝ) * (1/2:ℝ) = 1 by norm_num, Real.rpow_one]
    linarith [h1, h2, h3]
  have hs50 : (Real.log (L + 2) + 1)^2 ≤ 50 * L^(1/2:ℝ) := by
    have h := mul_le_mul_of_nonneg_left hhalf (by norm_num : (0:ℝ) ≤ 25)
    linarith [hsq, h]
  have hMpos : 0 < 5000 / c^2 := by positivity
  have hMle : 5000 / c^2 ≤ L^(1/2:ℝ) := by
    have h1 : ((5000/c^2)^2)^(1/2:ℝ) ≤ L^(1/2:ℝ) :=
      Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ (5000/c^2)^2) hLbig
        (by norm_num : (0:ℝ) ≤ (1/2:ℝ))
    have h2 : ((5000/c^2)^2)^(1/2:ℝ) = 5000/c^2 := by
      rw [← Real.rpow_natCast (5000/c^2) 2, ← Real.rpow_mul hMpos.le]
      rw [show ((2:ℕ):ℝ) * (1/2:ℝ) = 1 by norm_num, Real.rpow_one]
    linarith [h1, h2]
  have hs0 : 0 < L^(1/2:ℝ) := Real.rpow_pos_of_pos hLpos _
  have step2 : 25 * (Real.log (L + 2) + 1)^2 / c^2 ≤ 1250 * L^(1/2:ℝ) / c^2 := by
    have h := mul_le_mul_of_nonneg_left hs50 (by norm_num : (0:ℝ) ≤ 25)
    have h' : 25 * (50 * L^(1/2:ℝ)) = 1250 * L^(1/2:ℝ) := by ring
    calc 25 * (Real.log (L + 2) + 1)^2 / c^2 ≤ 25 * (50 * L^(1/2:ℝ)) / c^2 :=
          div_le_div_of_nonneg_right h hc2.le
      _ = 1250 * L^(1/2:ℝ) / c^2 := by rw [h']
  have step3 : 1250 * L^(1/2:ℝ) / c^2 ≤ L / 4 := by
    have hLsq : L = L^(1/2:ℝ) * L^(1/2:ℝ) := by
      rw [← Real.rpow_add hLpos]
      rw [show (1/2:ℝ) + 1/2 = 1 by norm_num, Real.rpow_one]
    have hMle' : 5000 ≤ L^(1/2:ℝ) * c^2 := (div_le_iff₀ hc2).mp hMle
    have hmul : 5000 * L^(1/2:ℝ) ≤ (L^(1/2:ℝ) * c^2) * L^(1/2:ℝ) :=
      mul_le_mul_of_nonneg_right hMle' hs0.le
    rw [div_le_div_iff₀ hc2 (by norm_num : (0:ℝ) < 4)]
    nlinarith [hmul, hLsq]
  linarith [step2, step3]

theorem S3T0Bound :
    ∀ c : ℝ, 0 < c → ∃ C : ℝ, 0 < C ∧ ∀ z : ℕ, 2 ≤ z →
      ((Work.LinnikAreas.JutilaPieces.s3T0 c z : ℝ)) ^ 2
          * (Real.log (z : ℝ) + 2) ^ 3 / (z : ℝ) ≤ C := by
  intro c hc
  set Z : ℕ := Nat.ceil (Real.exp (max 331776 ((5000 / c^2)^2))) + 2 with hZ
  have hZge : Real.exp (max 331776 ((5000 / c^2)^2)) ≤ (Z : ℝ) := by
    have h := Nat.le_ceil (Real.exp (max 331776 ((5000 / c^2)^2)))
    rw [hZ]; push_cast; linarith
  refine ⟨max 160 ((s3T0 c Z : ℝ)^2 * (Real.log (Z:ℝ) + 2)^3 / 2), ?_, ?_⟩
  · exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  intro z hz
  rcases lt_or_ge Z z with hzZ | hzZ
  · have hzpos : (0:ℝ) < (z:ℝ) := Nat.cast_pos.mpr (by omega)
    have hExpz : Real.exp (max 331776 ((5000/c^2)^2)) ≤ (z:ℝ) :=
      le_trans hZge (Nat.cast_le.mpr hzZ.le)
    have hlogz : max 331776 ((5000/c^2)^2) ≤ Real.log (z:ℝ) := by
      have h := Real.log_le_log (Real.exp_pos _) hExpz
      rwa [Real.log_exp] at h
    have hL2 : (2:ℝ) ≤ Real.log (z:ℝ) :=
      le_trans (le_trans (by norm_num : (2:ℝ) ≤ 331776) (le_max_left _ _)) hlogz
    have hLbig : (5000/c^2)^2 ≤ Real.log (z:ℝ) := le_trans (le_max_right _ _) hlogz
    have hLpos : (0:ℝ) < Real.log (z:ℝ) := by linarith
    have hkey : 25 * (Real.log (Real.log (z:ℝ) + 2) + 1)^2 / c^2 ≤ Real.log (z:ℝ)/4 :=
      s3T0_exp_arg_le_quarter c (Real.log (z:ℝ)) hc hL2 hLbig
    have hexp_le : Real.exp (25 * (Real.log (Real.log (z:ℝ) + 2) + 1)^2 / c^2)
        ≤ (z:ℝ)^(1/4:ℝ) := by
      calc Real.exp (25 * (Real.log (Real.log (z:ℝ) + 2) + 1)^2 / c^2)
            ≤ Real.exp (Real.log (z:ℝ)/4) := Real.exp_le_exp.mpr hkey
        _ = (z:ℝ)^(1/4:ℝ) := by rw [Real.rpow_def_of_pos hzpos]; congr 1; ring
    have hs3 : (s3T0 c z : ℝ) ≤ (z:ℝ)^(1/4:ℝ) + 3 := by
      have hce : ((Nat.ceil
            (Real.exp (25 * (Real.log (Real.log (z:ℝ) + 2) + 1)^2 / c^2)) : ℕ) : ℝ)
          < Real.exp (25 * (Real.log (Real.log (z:ℝ) + 2) + 1)^2 / c^2) + 1 :=
        Nat.ceil_lt_add_one (a := Real.exp (25 * (Real.log (Real.log (z:ℝ) + 2) + 1)^2 / c^2))
          (Real.exp_pos _).le
      have heq : (s3T0 c z : ℝ)
          = ((Nat.ceil
            (Real.exp (25 * (Real.log (Real.log (z:ℝ) + 2) + 1)^2 / c^2)) : ℕ) : ℝ) + 2 := by
        rw [s3T0, Nat.cast_add, Nat.cast_ofNat]
      rw [heq]; linarith
    have hz1 : (1:ℝ) ≤ (z:ℝ) := by exact_mod_cast (by omega : 1 ≤ z)
    have hz4 : (1:ℝ) ≤ (z:ℝ)^(1/4:ℝ) :=
      Real.one_le_rpow hz1 (by norm_num : (0:ℝ) ≤ (1/4:ℝ))
    have hsqz : (Real.log (z:ℝ) + 2)^3 ≤ 8 * (Real.log (z:ℝ))^3 := by
      have h : Real.log (z:ℝ) + 2 ≤ 2 * Real.log (z:ℝ) := by linarith
      have h2 : (Real.log (z:ℝ) + 2)^3 ≤ (2 * Real.log (z:ℝ))^3 :=
        pow_le_pow_left₀ (by linarith) h 3
      have h3 : (2 * Real.log (z:ℝ))^3 = 8 * (Real.log (z:ℝ))^3 := by ring
      linarith [h2, h3]
    have hL256 : (256:ℝ) ≤ Real.log (z:ℝ) :=
      le_trans (le_trans (by norm_num : (256:ℝ) ≤ 331776) (le_max_left _ _)) hlogz
    have hL3 : (Real.log (z:ℝ))^3 ≤ Real.exp (Real.log (z:ℝ)/4) :=
      s3T0_cube_le_exp _ hL256
    have hsq : ((z:ℝ)^(1/4:ℝ) + 3)^2 ≤ 16 * (z:ℝ)^(1/2:ℝ) := by
      have h30 : (0:ℝ) ≤ (z:ℝ)^(1/4:ℝ) := Real.rpow_nonneg hzpos.le _
      have h4 : (z:ℝ)^(1/4:ℝ) + 3 ≤ 4 * (z:ℝ)^(1/4:ℝ) := by linarith
      have h5 : ((z:ℝ)^(1/4:ℝ) + 3)^2 ≤ (4 * (z:ℝ)^(1/4:ℝ))^2 :=
        pow_le_pow_left₀ (by linarith) h4 2
      have h6 : (4 * (z:ℝ)^(1/4:ℝ))^2 = 16 * ((z:ℝ)^(1/4:ℝ))^2 := by ring
      have h7 : ((z:ℝ)^(1/4:ℝ))^2 = (z:ℝ)^(1/2:ℝ) := by
        rw [← Real.rpow_natCast ((z:ℝ)^(1/4:ℝ)) 2, ← Real.rpow_mul hzpos.le]
        rw [show (1/4:ℝ) * ((2:ℕ):ℝ) = 1/2 by norm_num]
      linarith [h5, h6, h7]
    have hstep : (s3T0 c z : ℝ)^2 * (Real.log (z:ℝ) + 2)^3 ≤ 128 * (z:ℝ) := by
      have hA : (s3T0 c z : ℝ)^2 ≤ ((z:ℝ)^(1/4:ℝ) + 3)^2 :=
        pow_le_pow_left₀ (by positivity) hs3 2
      have hB : (Real.log (z:ℝ) + 2)^3 ≤ 8 * Real.exp (Real.log (z:ℝ)/4) :=
        le_trans hsqz (mul_le_mul_of_nonneg_left hL3 (by norm_num))
      have h1 : (s3T0 c z : ℝ)^2 * (Real.log (z:ℝ) + 2)^3
          ≤ (16 * (z:ℝ)^(1/2:ℝ)) * (8 * Real.exp (Real.log (z:ℝ)/4)) :=
        mul_le_mul (le_trans hA hsq) hB (by positivity) (by positivity)
      have h2 : (16 * (z:ℝ)^(1/2:ℝ)) * (8 * Real.exp (Real.log (z:ℝ)/4))
          = 128 * ((z:ℝ)^(1/2:ℝ) * Real.exp (Real.log (z:ℝ)/4)) := by ring
      have h3 : (z:ℝ)^(1/2:ℝ) * Real.exp (Real.log (z:ℝ)/4) ≤ (z:ℝ) := by
        have he : (z:ℝ)^(1/2:ℝ) = Real.exp (Real.log (z:ℝ)/2) := by
          rw [Real.rpow_def_of_pos hzpos]; congr 1; ring
        rw [he, ← Real.exp_add]
        have h4 : Real.exp (Real.log (z:ℝ)/2 + Real.log (z:ℝ)/4) ≤ Real.exp (Real.log (z:ℝ)) :=
          Real.exp_le_exp.mpr (by linarith [hLpos])
        rwa [Real.exp_log hzpos] at h4
      have h4 : 128 * ((z:ℝ)^(1/2:ℝ) * Real.exp (Real.log (z:ℝ)/4)) ≤ 128 * (z:ℝ) :=
        mul_le_mul_of_nonneg_left h3 (by norm_num)
      linarith [h1, h2, h4]
    have h128 : (s3T0 c z : ℝ)^2 * (Real.log (z:ℝ) + 2)^3 / (z:ℝ) ≤ 128 := by
      rw [div_le_iff₀ hzpos]
      exact hstep
    exact le_trans h128 (le_trans (by norm_num : (128:ℝ) ≤ 160) (le_max_left _ _))
  · have hmono : (s3T0 c z : ℝ) ≤ (s3T0 c Z : ℝ) := Nat.cast_le.mpr (s3T0_mono c hzZ)
    have hzpos : (0:ℝ) < (z:ℝ) := Nat.cast_pos.mpr (by omega)
    have hlog : Real.log (z:ℝ) + 2 ≤ Real.log (Z:ℝ) + 2 := by
      have h := Real.log_le_log hzpos (Nat.cast_le.mpr hzZ)
      linarith
    have hlog0 : 0 ≤ Real.log (z:ℝ) + 2 := by linarith [log_nat_nonneg z]
    have hnum : (s3T0 c z : ℝ)^2 * (Real.log (z:ℝ) + 2)^3
        ≤ (s3T0 c Z : ℝ)^2 * (Real.log (Z:ℝ) + 2)^3 := by
      apply mul_le_mul
      · exact pow_le_pow_left₀ (by positivity) hmono 2
      · exact pow_le_pow_left₀ hlog0 hlog 3
      · positivity
      · positivity
    have hnumpos : 0 < (s3T0 c Z : ℝ)^2 * (Real.log (Z:ℝ) + 2)^3 := by
      have h1 : 0 < (s3T0 c Z : ℝ) := by
        have hz1 : 0 < s3T0 c Z := by rw [s3T0]; omega
        exact_mod_cast hz1
      have h2 : 0 < Real.log (Z:ℝ) + 2 := by linarith [log_nat_nonneg Z]
      positivity
    exact le_trans (le_trans (div_le_div_of_nonneg_right hnum hzpos.le)
        (div_le_div_of_nonneg_left hnumpos.le (by norm_num : (0:ℝ) < 2) (by exact_mod_cast hz)))
      (le_max_right _ _)

end Work.LinnikAreas.JutilaPieces
