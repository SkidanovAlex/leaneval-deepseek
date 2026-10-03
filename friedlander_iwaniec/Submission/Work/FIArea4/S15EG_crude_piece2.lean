import Mathlib
import Submission.Work.FIArea4.S15EGDefs
import Submission.Work.FIArea4.S15cutDefs

namespace Work.FIArea4

/-- The cast of the relaxed modulus window `Y = S15Y Pa X j` is at most `3N/X`. -/
lemma S15EG_S15Y_le (Pa : Work.FITop.Params) (X j : ℕ) (hX : 1 ≤ X)
    (hXN : (X:ℝ) ≤ Pa.N) : (S15Y Pa X j : ℝ) ≤ 3 * Pa.N / (X:ℝ) := by
  have hXpos : (0:ℝ) < X := by exact_mod_cast hX
  have hNpos : (0:ℝ) < Pa.N := by linarith [Pa.hN1]
  have hA0 : 0 ≤ Pa.N / ((X:ℝ) * (2:ℝ)^j) := by positivity
  have hceil := Nat.ceil_lt_add_one hA0
  have hYcast : (S15Y Pa X j : ℝ)
      = ((⌈Pa.N / ((X:ℝ) * (2:ℝ)^j)⌉₊ : ℕ) : ℝ) + 1 := by
    rw [S15Y]; push_cast; ring
  have h2j : (1:ℝ) ≤ (2:ℝ)^j := one_le_pow₀ (by norm_num)
  have hXY : (X:ℝ) ≤ (X:ℝ) * (2:ℝ)^j := by nlinarith [h2j, hXpos.le]
  have hle1 : Pa.N / ((X:ℝ) * (2:ℝ)^j) ≤ Pa.N / (X:ℝ) :=
    div_le_div_of_nonneg_left (le_of_lt hNpos) hXpos hXY
  have hNX : (1:ℝ) ≤ Pa.N / (X:ℝ) := (one_le_div hXpos).mpr hXN
  have hle2 : Pa.N / (X:ℝ) + 2 ≤ 3 * Pa.N / (X:ℝ) := by
    rw [show (3:ℝ) * Pa.N / X = 3 * (Pa.N / X) by ring]
    linarith
  rw [hYcast]
  linarith [hceil]

theorem S15EG_crude_piece2 (Pa : Work.FITop.Params) (X j e : ℕ)
    (hX : 1 ≤ X) (hXN : (X : ℝ) ≤ Pa.N) (he : 1 ≤ e)
    (heY : (e : ℝ) ≤ (Work.FIArea4.S15Y Pa X j : ℝ)) :
    ((2 : ℝ) * (X : ℝ) / (e : ℝ)) ^ (-(1 : ℝ) / 2)
        * ((Work.FIArea4.S15EG_Re Pa e : ℝ) * (Work.FIArea4.S15EG_Se Pa : ℝ))
      ≤ 30 * Pa.N * (X : ℝ) ^ (-(1 : ℝ) / 2) := by
  set Xr : ℝ := (X:ℝ) with hXr
  set er : ℝ := (e:ℝ) with her
  set N : ℝ := Pa.N with hN
  set K : ℝ := (S15EG_K Pa : ℝ) with hK
  set Re : ℝ := (S15EG_Re Pa e : ℝ) with hRe
  set Se : ℝ := (S15EG_Se Pa : ℝ) with hSe
  have hXpos : 0 < Xr := by rw [hXr]; exact_mod_cast hX
  have hepos : 0 < er := by rw [her]; exact_mod_cast he
  have he1 : 1 ≤ er := by rw [her]; exact_mod_cast he
  have hNpos : 0 < N := by rw [hN]; linarith [Pa.hN1]
  have hN1 : 1 ≤ N := by rw [hN]; exact Pa.hN1
  -- the modulus window bound
  have hYle : (S15Y Pa X j : ℝ) ≤ 3 * N / Xr := by
    have h := S15EG_S15Y_le Pa X j hX (by rw [← hXr, ← hN]; exact hXN)
    rwa [← hN, ← hXr] at h
  have heB : er ≤ 3 * N / Xr := le_trans heY hYle
  -- the numerical bounds on K
  have hKnonneg : 0 ≤ K := by rw [hK]; exact Nat.cast_nonneg _
  have hKle : K ≤ 3 * Real.sqrt N := by rw [hK, hN]; exact S15EG_K_le Pa
  have hKsq : K^2 ≤ 9 * N := by rw [hK, hN]; exact S15EG_K_sq_le Pa
  have hKge2 : 2 ≤ K := by
    have h := S15EG_K_ge_two_sqrt Pa
    rw [← hK, ← hN] at h
    have hsN : 1 ≤ Real.sqrt N := Real.one_le_sqrt.mpr hN1
    linarith
  -- the support-box bounds
  have hRe_le : Re ≤ K/(2*er)+1 := by
    have h1 : Re = ((S15EG_K Pa / (2*e) : ℕ) : ℝ) + 1 := by
      rw [hRe, S15EG_Re]; push_cast; ring
    rw [h1]
    have h2 : ((S15EG_K Pa / (2*e) : ℕ) : ℝ) ≤ (S15EG_K Pa : ℝ) / ((2*e : ℕ) : ℝ) :=
      Nat.cast_div_le
    have h3 : (S15EG_K Pa : ℝ) / ((2*e : ℕ) : ℝ) = K/(2*er) := by
      rw [← hK]; push_cast; rw [← her]
    linarith
  have hSe_le : Se ≤ K/2+1 := by
    have h1 : Se = ((S15EG_K Pa / 2 : ℕ) : ℝ) + 1 := by
      rw [hSe, S15EG_Se]; push_cast; ring
    rw [h1]
    have h2 : ((S15EG_K Pa / 2 : ℕ) : ℝ) ≤ (S15EG_K Pa : ℝ) / 2 := Nat.cast_div_le
    have h3 : (S15EG_K Pa : ℝ) / 2 = K/2 := by rw [← hK]
    linarith
  have hSeK : Se ≤ K := by linarith
  have hSepos : 0 ≤ Se := by rw [hSe]; exact Nat.cast_nonneg _
  -- the auxiliary square root
  set u : ℝ := Real.sqrt (er/2) with hu
  have hu_nonneg : 0 ≤ u := by rw [hu]; exact Real.sqrt_nonneg _
  have hu2 : u^2 = er/2 := by rw [hu]; exact Real.sq_sqrt (by positivity)
  have hu_le_one : u/er ≤ 1 := by
    rw [div_le_one hepos]
    have hsq : u^2 ≤ er^2 := by rw [hu2]; nlinarith [he1]
    have habs := (sq_le_sq.mp hsq)
    rwa [abs_of_nonneg hu_nonneg, abs_of_nonneg (le_of_lt hepos)] at habs
  have hu_le_2sqrtN : u ≤ 2*Real.sqrt N := by
    have heB' : er ≤ 3*N := by
      have h3 : 3*N/Xr ≤ 3*N := by
        have hXone : (1:ℝ) ≤ Xr := by rw [hXr]; exact_mod_cast hX
        have h := div_le_div_of_nonneg_left (by positivity : (0:ℝ) ≤ 3*N) one_pos hXone
        simpa using h
      linarith [heB, h3]
    have hle : er/2 ≤ 4*N := by linarith [heB', hNpos.le]
    rw [hu]
    have h1 : Real.sqrt (er/2) ≤ Real.sqrt (4*N) := Real.sqrt_le_sqrt hle
    have h2 : Real.sqrt (4*N) = 2*Real.sqrt N := by
      rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4), S15EG_sqrt_four]
    linarith [h1, h2.le]
  have hterm1 : u*K^2/(2*er) ≤ K^2/2 := by
    have h_eq : u*K^2/(2*er) = (u/er)*(K^2/2) := by field_simp
    rw [h_eq]
    calc (u/er)*(K^2/2) ≤ 1*(K^2/2) := mul_le_mul_of_nonneg_right hu_le_one (by positivity)
      _ = K^2/2 := one_mul _
  have hterm2 : u*K ≤ 6*N := by
    have hsimp : (2*Real.sqrt N)*(3*Real.sqrt N) = 6*N := by
      rw [show (2:ℝ)*Real.sqrt N*(3*Real.sqrt N) = 6*(Real.sqrt N)^2 by ring,
          Real.sq_sqrt (le_of_lt hNpos)]
    calc u*K ≤ (2*Real.sqrt N)*(3*Real.sqrt N) :=
          mul_le_mul hu_le_2sqrtN hKle hKnonneg (by positivity)
      _ = 6*N := hsimp
  have hmain : u*(K^2/(2*er)+K) ≤ 30*N := by
    have hexp : u*(K^2/(2*er)+K) = u*K^2/(2*er) + u*K := by ring
    rw [hexp]
    have h2 : K^2/2 + 6*N ≤ 30*N := by nlinarith [hKsq, hNpos]
    linarith [add_le_add hterm1 hterm2, h2]
  have hkey : u*(Re*Se) ≤ 30*N := by
    have h1 : Re*Se ≤ (K/(2*er)+1)*K := mul_le_mul hRe_le hSeK hSepos (by positivity)
    have h2 : u*(Re*Se) ≤ u*((K/(2*er)+1)*K) := mul_le_mul_of_nonneg_left h1 hu_nonneg
    have h3 : (K/(2*er)+1)*K = K^2/(2*er)+K := by field_simp
    rw [h3] at h2
    linarith [h2, hmain]
  -- rewrite the two `rpow`s as square roots, cancel `√X`
  have hpow1 : (2*Xr/er)^(-(1:ℝ)/2) = Real.sqrt (er/(2*Xr)) := by
    have hpos : 0 ≤ 2*Xr/er := by positivity
    rw [show -(1:ℝ)/2 = -((1:ℝ)/2) by ring, Real.rpow_neg hpos, ← Real.sqrt_eq_rpow,
        ← Real.sqrt_inv, inv_div]
  have hdiv : Real.sqrt (er/(2*Xr)) = Real.sqrt (er/2)/Real.sqrt Xr := by
    rw [show er/(2*Xr) = (er/2)/Xr by ring, Real.sqrt_div (by positivity)]
  have hpow2 : Xr^(-(1:ℝ)/2) = (Real.sqrt Xr)⁻¹ := by
    rw [show -(1:ℝ)/2 = -((1:ℝ)/2) by ring, Real.rpow_neg (le_of_lt hXpos),
        ← Real.sqrt_eq_rpow]
  rw [hpow1, hdiv, hpow2]
  calc (Real.sqrt (er/2)/Real.sqrt Xr)*(Re*Se)
      = (u*(Re*Se))*(Real.sqrt Xr)⁻¹ := by rw [hu]; ring
    _ ≤ (30*N)*(Real.sqrt Xr)⁻¹ := mul_le_mul_of_nonneg_right hkey (by positivity)
    _ = 30*N*(Real.sqrt Xr)⁻¹ := by ring

end Work.FIArea4
