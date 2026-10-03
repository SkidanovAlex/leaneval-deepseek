import Mathlib
import Submission.Work.KMTPlan.A6.MdlDefs
import Submission.Work.KMTPlan.A6.weightVarBound

set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

/-! ## Scaled Lipschitz profiles -/

lemma mdlWeightSelf_varNorm_scaledLipschitz {r : NNReal} (hr : 1 ≤ r) {u : ℕ → ℝ} {G : ℝ → ℝ}
    {α D B K ρ : ℝ} (hρ0 : 0 ≤ ρ) (hu0 : ∀ n, 0 ≤ u n) (huρ : ∀ n, u n ≤ ρ)
    (hmono : Antitone u) (hD0 : 0 ≤ D) (hα : |α| ≤ D) (hB : ∀ n, |G (u n)| ≤ B)
    (hB0 : 0 ≤ B) (hK0 : 0 ≤ K)
    (hstep : ∀ n, |G (u (n + 1)) - G (u n)| ≤ K * (u n - u (n + 1))) :
    PointwiseErgodicTheorems.variationalNorm r (fun n => ((α * G (u n) : ℝ) : ℂ))
      ≤ ENNReal.ofReal (D * (B + K * ρ)) := by
  have hsup : ∀ n, ‖((α * G (u n) : ℝ) : ℂ)‖ ≤ D * B := by
    intro n
    rw [norm_ofReal_complex, abs_mul]
    exact mul_le_mul hα (hB n) (abs_nonneg _) hD0
  have hstepl : ∀ n, ‖((α * G (u (n + 1)) : ℝ) : ℂ) - ((α * G (u n) : ℝ) : ℂ)‖
      ≤ (D * K) * (u n - u (n + 1)) := by
    intro n
    have h1 : ((α * G (u (n + 1)) : ℝ) : ℂ) - ((α * G (u n) : ℝ) : ℂ)
        = ((α * (G (u (n + 1)) - G (u n)) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_sub]
      congr 1
      ring
    rw [h1, norm_ofReal_complex, abs_mul]
    calc |α| * |G (u (n + 1)) - G (u n)| ≤ D * (K * (u n - u (n + 1))) :=
          mul_le_mul hα (hstep n) (abs_nonneg _) hD0
      _ = (D * K) * (u n - u (n + 1)) := by ring
  refine (VarNormAntitoneBound hr hρ0 hu0 huρ hmono (mul_nonneg hD0 hB0)
    (mul_nonneg hD0 hK0) hsup hstepl).trans ?_
  exact le_of_eq (congrArg ENNReal.ofReal (by ring))

/-! ## The three identities -/

lemma mdlWeightSelf_factor_pow {d : ℕ} {N t A : ℝ} (hN : N ≠ 0) :
    ((N * t) ^ (d - 1) * A) / N ^ (d - 1) = t ^ (d - 1) * A := by
  rw [mul_comm N t, mul_pow, div_eq_iff (pow_ne_zero _ hN)]
  ring

lemma mdlWeightSelf_inv_factor_pow {d : ℕ} {N t A : ℝ} (hN : N ≠ 0) (ht : t ≠ 0) (hA : A ≠ 0) :
    N ^ (d - 1) / ((N * t) ^ (d - 1) * A) = (t ^ (d - 1))⁻¹ * A⁻¹ := by
  have hNp : N ^ (d - 1) ≠ 0 := pow_ne_zero _ hN
  have htp : t ^ (d - 1) ≠ 0 := pow_ne_zero _ ht
  rw [mul_pow]
  field_simp

lemma mdlWeightSelf_factor_pow_d {d : ℕ} {N t X : ℝ} (hN : N ≠ 0) (ht : t ≠ 0) :
    N ^ d * X = (t ^ d)⁻¹ * ((N * t) ^ d * X) := by
  have hNp : N ^ d ≠ 0 := pow_ne_zero _ hN
  have htp : t ^ d ≠ 0 := pow_ne_zero _ ht
  rw [mul_pow]
  field_simp

lemma mdlWeightSelf_mdlW3_eq (P : Polynomial ℤ) {N : ℕ} {t : ℝ} (hN : 1 ≤ N) (ht : t ≠ 0) :
    mdlW3 P N t = (((t ^ (P.natDegree - 1) * Phi1u P (((N : ℝ) * t)⁻¹) : ℝ)) : ℂ) := by
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN0 : (N : ℝ) ≠ 0 := by linarith
  have hy : (N : ℝ) * t ≠ 0 := mul_ne_zero hN0 ht
  unfold mdlW3
  rw [Phi1u_mul P hy]
  congr 1
  exact mdlWeightSelf_factor_pow hN0

lemma mdlWeightSelf_mdlW1_eq (P : Polynomial ℤ) {N : ℕ} {t : ℝ} (hN : 1 ≤ N) (ht : t ≠ 0)
    (hphi : Phi1u P (((N : ℝ) * t)⁻¹) ≠ 0) :
    mdlW1 P N t = ((((t ^ (P.natDegree - 1))⁻¹
        * (Phi1u P (((N : ℝ) * t)⁻¹))⁻¹ : ℝ)) : ℂ) := by
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN0 : (N : ℝ) ≠ 0 := by linarith
  have hy : (N : ℝ) * t ≠ 0 := mul_ne_zero hN0 ht
  unfold mdlW1
  rw [Phi1u_mul P hy]
  congr 1
  exact mdlWeightSelf_inv_factor_pow hN0 ht hphi

lemma mdlWeightSelf_mdlW2_eq (P : Polynomial ℤ) (hdeg : 1 ≤ P.natDegree) {N : ℕ} {t : ℝ}
    (hN : 1 ≤ N) (ht : 0 < t) :
    mdlW2 P N t = ((((t ^ P.natDegree)⁻¹
        * (Phi2u P (((N : ℝ) * t)⁻¹) / (Phi1u P (((N : ℝ) * t)⁻¹)) ^ 2) : ℝ)) : ℂ) := by
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN0 : (N : ℝ) ≠ 0 := by linarith
  have hNp : (0 : ℝ) < (N : ℝ) := by linarith
  have hypos : 0 < (N : ℝ) * t := mul_pos hNp ht
  unfold mdlW2
  rw [mul_div_assoc]
  rw [mdlWeightSelf_factor_pow_d (d := P.natDegree) hN0 (ne_of_gt ht)]
  have h3 : ((N : ℝ) * t) ^ P.natDegree
        * (Pderiv2R P ((N : ℝ) * t) / (PderivR P ((N : ℝ) * t)) ^ 2)
      = Phi2u P (((N : ℝ) * t)⁻¹) / (Phi1u P (((N : ℝ) * t)⁻¹)) ^ 2 := by
    rw [← mul_div_assoc]
    exact seq3_identity P hdeg hypos
  rw [h3]


/-! ## The monotone-scale weight bound -/

theorem MdlWeightMonoBoundSelf (P : Polynomial ℤ) (hdeg : 1 ≤ P.natDegree) (r : NNReal)
    (hr : 1 ≤ r) :
    ∃ B : ℕ, 0 < B ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ → ℕ) (t : ℝ), Monotone N → (∀ n, B ≤ N n) →
        t ∈ Set.Icc (1 / 2 : ℝ) 1 →
        PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => mdlW1 P (N n) t) ≤ ENNReal.ofReal C ∧
        PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => mdlW2 P (N n) t) ≤ ENNReal.ofReal C ∧
        PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => mdlW3 P (N n) t) ≤ ENNReal.ofReal C := by
  have hPne : P ≠ 0 := by intro h; rw [h] at hdeg; simp at hdeg
  have hlcr : ((P.leadingCoeff : ℤ) : ℝ) ≠ 0 := fun h =>
    hPne (Polynomial.leadingCoeff_eq_zero.mp (Int.cast_eq_zero.mp h))
  have hdnat : (0 : ℝ) < (P.natDegree : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hdeg)
  have hK1nn : 0 ≤ Phi1uLip P := Phi1uLip_nonneg P
  have hA1nn : 0 ≤ Phi1uConst P := Phi1uConst_nonneg P
  have hA2nn : 0 ≤ Phi2uConst P := Phi2uConst_nonneg P
  have hK2nn : 0 ≤ Phi2uLip P := Phi2uLip_nonneg P
  set v0 : ℝ := (P.natDegree : ℝ) * |((P.leadingCoeff : ℤ) : ℝ)| with hv0def
  have hv0pos : 0 < v0 := mul_pos hdnat (abs_pos.mpr hlcr)
  set D : ℝ := (2 : ℝ) ^ P.natDegree with hDdef
  have hD1 : 1 ≤ D := by
    rw [hDdef]
    exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hD0 : 0 ≤ D := le_trans zero_le_one hD1
  -- the threshold `B`
  set B : ℕ := max 2 (Nat.ceil (4 * Phi1uLip P / v0) + 2) with hBdef
  have hB2 : 2 ≤ B := le_max_left _ _
  have hBpos : (0 : ℝ) < (B : ℝ) := by
    have h2 : (2 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB2
    linarith
  have hBposN : 0 < B := lt_of_lt_of_le (by norm_num) hB2
  have hbig : Phi1uLip P * 2 / (B : ℝ) < v0 := by
    have hle : (Nat.ceil (4 * Phi1uLip P / v0) : ℝ) + 2 ≤ (B : ℝ) := by
      have h : Nat.ceil (4 * Phi1uLip P / v0) + 2 ≤ B := le_max_right _ _
      exact_mod_cast h
    have hceil : 4 * Phi1uLip P / v0 ≤ (Nat.ceil (4 * Phi1uLip P / v0) : ℝ) := Nat.le_ceil _
    have h2 : 4 * Phi1uLip P / v0 + 2 ≤ (B : ℝ) := by linarith
    have hv0ne : v0 ≠ 0 := ne_of_gt hv0pos
    have h4 : 4 * Phi1uLip P < (B : ℝ) * v0 := by
      have hm := mul_le_mul_of_nonneg_right h2 hv0pos.le
      rw [add_mul, div_mul_cancel₀ (4 * Phi1uLip P) hv0ne] at hm
      nlinarith
    rw [div_lt_iff₀ hBpos]
    nlinarith [hK1nn]
  set ρ : ℝ := 2 / (B : ℝ) with hρdef
  have hρ0 : 0 < ρ := by rw [hρdef]; positivity
  have hρ0' : 0 ≤ ρ := le_of_lt hρ0
  have hρ1 : ρ ≤ 1 := by
    rw [hρdef, div_le_one hBpos]
    have h2 : (2 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB2
    linarith
  set c : ℝ := v0 - Phi1uLip P * ρ with hcdef
  have hc : 0 < c := by
    rw [hcdef, hρdef]
    have h := hbig
    rw [mul_div_assoc] at h
    linarith
  set T1 : ℝ := 1 / c + (Phi1uLip P / c ^ 2) * ρ with hT1def
  set T2 : ℝ := Phi2uConst P / c ^ 2
      + ((Phi2uLip P * (Phi1uConst P) ^ 2
          + 2 * Phi2uConst P * Phi1uLip P * Phi1uConst P) / c ^ 4) * ρ with hT2def
  set T3 : ℝ := Phi1uConst P + Phi1uLip P * ρ with hT3def
  have hT1nn : 0 ≤ T1 := by
    rw [hT1def]
    have h1 : 0 ≤ 1 / c := div_nonneg zero_le_one hc.le
    have h2 : 0 ≤ Phi1uLip P / c ^ 2 := div_nonneg hK1nn (by positivity)
    exact add_nonneg h1 (mul_nonneg h2 hρ0')
  have hT2nn : 0 ≤ T2 := by
    rw [hT2def]
    have h1 : 0 ≤ Phi2uConst P / c ^ 2 := div_nonneg hA2nn (by positivity)
    have h2 : 0 ≤ (Phi2uLip P * (Phi1uConst P) ^ 2
        + 2 * Phi2uConst P * Phi1uLip P * Phi1uConst P) / c ^ 4 :=
      div_nonneg (by positivity) (by positivity)
    exact add_nonneg h1 (mul_nonneg h2 hρ0')
  have hT3nn : 0 ≤ T3 := by
    rw [hT3def]
    exact add_nonneg hA1nn (mul_nonneg hK1nn hρ0')
  set Cv : ℝ := D * (T1 + T2 + T3) + 1 with hCvdef
  have hCvpos : 0 < Cv := by
    rw [hCvdef]
    have : 0 ≤ D * (T1 + T2 + T3) := mul_nonneg hD0 (by linarith)
    linarith
  refine ⟨B, hBposN, Cv, hCvpos, ?_⟩
  intro N t hNmono hNB ht
  have ht1 : (1 / 2 : ℝ) ≤ t := ht.1
  have ht2 : t ≤ 1 := ht.2
  have htpos : 0 < t := by linarith
  have htne : t ≠ 0 := ne_of_gt htpos
  have hNpos : ∀ n, (0 : ℝ) < (N n : ℝ) := by
    intro n
    have h1 : (B : ℝ) ≤ (N n : ℝ) := by exact_mod_cast hNB n
    have h2 : (2 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB2
    linarith
  have hN1 : ∀ n, 1 ≤ N n := by
    intro n
    have h1 : B ≤ N n := hNB n
    omega
  set u : ℕ → ℝ := fun n => ((N n : ℝ) * t)⁻¹ with hudef
  have hu0 : ∀ n, 0 ≤ u n := by
    intro n
    rw [hudef]
    exact inv_nonneg.mpr (mul_nonneg (hNpos n).le htpos.le)
  have huρ : ∀ n, u n ≤ ρ := by
    intro n
    have h3 : (0 : ℝ) < (N n : ℝ) * t := mul_pos (hNpos n) htpos
    have h1 : (B : ℝ) / 2 ≤ (N n : ℝ) * t := by
      have h2 : (B : ℝ) ≤ (N n : ℝ) := by exact_mod_cast hNB n
      nlinarith
    have h4 : ((B : ℝ) / 2)⁻¹ = ρ := by
      rw [hρdef]
      field_simp
    rw [hudef]
    simp only
    calc ((N n : ℝ) * t)⁻¹ ≤ ((B : ℝ) / 2)⁻¹ :=
          (inv_le_inv₀ h3 (by positivity)).mpr h1
      _ = ρ := h4
  have hu1 : ∀ n, u n ≤ 1 := fun n => (huρ n).trans hρ1
  have hu_in : ∀ n, u n ∈ Set.Icc (0 : ℝ) 1 := fun n => ⟨hu0 n, hu1 n⟩
  have hmono : Antitone u := by
    intro m n hmn
    have h1 : (N m : ℝ) ≤ (N n : ℝ) := by exact_mod_cast hNmono hmn
    have h2 : (0 : ℝ) < (N n : ℝ) * t := mul_pos (hNpos n) htpos
    have h3 : (0 : ℝ) < (N m : ℝ) * t := mul_pos (hNpos m) htpos
    have h4 : (N m : ℝ) * t ≤ (N n : ℝ) * t := mul_le_mul_of_nonneg_right h1 htpos.le
    rw [hudef]
    simp only
    exact (inv_le_inv₀ h2 h3).mpr h4
  have hphizero : |Phi1u P 0| = v0 := by
    rw [Phi1u_zero P hdeg, hv0def, abs_mul, abs_of_nonneg (Nat.cast_nonneg P.natDegree)]
  have hphi : ∀ n, c ≤ |Phi1u P (u n)| := by
    intro n
    have h3 : |Phi1u P (u n) - Phi1u P 0| ≤ Phi1uLip P * u n := by
      have h := Phi1u_lipschitz P (hu_in n) (Set.mem_Icc.mpr ⟨le_refl 0, by norm_num⟩)
      rwa [sub_zero, abs_of_nonneg (hu0 n)] at h
    have h4 := abs_sub_abs_le' (Phi1u P 0) (Phi1u P (u n))
    rw [abs_sub_comm (Phi1u P 0) (Phi1u P (u n))] at h4
    rw [hphizero] at h4
    have h5 : Phi1uLip P * u n ≤ Phi1uLip P * ρ := mul_le_mul_of_nonneg_left (huρ n) hK1nn
    rw [hcdef]
    linarith
  -- the `α`-bounds
  have hα3 : |t ^ (P.natDegree - 1)| ≤ D := by
    rw [abs_of_nonneg (pow_nonneg htpos.le _)]
    calc t ^ (P.natDegree - 1) ≤ 1 ^ (P.natDegree - 1) := pow_le_pow_left₀ htpos.le ht2 _
      _ = 1 := one_pow _
      _ ≤ D := hD1
  have hα1 : |(t ^ (P.natDegree - 1))⁻¹| ≤ D := by
    rw [abs_inv, abs_of_nonneg (pow_nonneg htpos.le _)]
    calc (t ^ (P.natDegree - 1))⁻¹ ≤ ((1 / 2 : ℝ) ^ (P.natDegree - 1))⁻¹ :=
          (inv_le_inv₀ (pow_pos htpos _) (pow_pos (by norm_num) _)).mpr
            (pow_le_pow_left₀ (by norm_num) ht1 _)
      _ = (2 : ℝ) ^ (P.natDegree - 1) := by
          rw [show ((1 : ℝ) / 2) = (2 : ℝ)⁻¹ by norm_num, inv_pow, inv_inv]
      _ ≤ D := by
          rw [hDdef]
          exact pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
  have hα2 : |(t ^ P.natDegree)⁻¹| ≤ D := by
    rw [abs_inv, abs_of_nonneg (pow_nonneg htpos.le _)]
    calc (t ^ P.natDegree)⁻¹ ≤ ((1 / 2 : ℝ) ^ P.natDegree)⁻¹ :=
          (inv_le_inv₀ (pow_pos htpos _) (pow_pos (by norm_num) _)).mpr
            (pow_le_pow_left₀ (by norm_num) ht1 _)
      _ = (2 : ℝ) ^ P.natDegree := by
          rw [show ((1 : ℝ) / 2) = (2 : ℝ)⁻¹ by norm_num, inv_pow, inv_inv]
      _ = D := hDdef.symm
  -- sup / step bounds for the three profiles
  have hsup1 : ∀ n, |(Phi1u P (u n))⁻¹| ≤ 1 / c := by
    intro n
    rw [abs_inv, one_div]
    exact (inv_le_inv₀ (lt_of_lt_of_le hc (hphi n)) hc).mpr (hphi n)
  have hsup2 : ∀ n, |Phi2u P (u n) / (Phi1u P (u n)) ^ 2| ≤ Phi2uConst P / c ^ 2 := by
    intro n
    rw [abs_div, abs_pow]
    exact div_le_div₀ hA2nn (Phi2u_abs_le P (hu_in n)) (by positivity)
      (pow_le_pow_left₀ hc.le (hphi n) 2)
  have hsup3 : ∀ n, |Phi1u P (u n)| ≤ Phi1uConst P := fun n => Phi1u_abs_le P (hu_in n)
  have hstep1 : ∀ n, |(Phi1u P (u (n + 1)))⁻¹ - (Phi1u P (u n))⁻¹|
      ≤ (Phi1uLip P / c ^ 2) * (u n - u (n + 1)) := by
    intro n
    have h := Phi1u_inv_lipschitz P hc (hu_in (n + 1)) (hu_in n) (hphi (n + 1)) (hphi n)
    have h2 : |u (n + 1) - u n| = u n - u (n + 1) := by
      rw [abs_of_nonpos (sub_nonpos.mpr (hmono (Nat.le_succ n))), neg_sub]
    rwa [h2] at h
  have hstep2 : ∀ n, |Phi2u P (u (n + 1)) / (Phi1u P (u (n + 1))) ^ 2
        - Phi2u P (u n) / (Phi1u P (u n)) ^ 2|
      ≤ ((Phi2uLip P * (Phi1uConst P) ^ 2
          + 2 * Phi2uConst P * Phi1uLip P * Phi1uConst P) / c ^ 4) * (u n - u (n + 1)) := by
    intro n
    have h := Phi_quo_lipschitz P hc (hu_in (n + 1)) (hu_in n) (hphi (n + 1)) (hphi n)
    have h2 : |u (n + 1) - u n| = u n - u (n + 1) := by
      rw [abs_of_nonpos (sub_nonpos.mpr (hmono (Nat.le_succ n))), neg_sub]
    rwa [h2] at h
  have hstep3 : ∀ n, |Phi1u P (u (n + 1)) - Phi1u P (u n)|
      ≤ Phi1uLip P * (u n - u (n + 1)) := by
    intro n
    have h := Phi1u_lipschitz P (hu_in (n + 1)) (hu_in n)
    have h2 : |u (n + 1) - u n| = u n - u (n + 1) := by
      rw [abs_of_nonpos (sub_nonpos.mpr (hmono (Nat.le_succ n))), neg_sub]
    rwa [h2] at h
  -- assembly
  have hV3 : PointwiseErgodicTheorems.variationalNorm r (fun n => mdlW3 P (N n) t)
      ≤ ENNReal.ofReal (D * T3) := by
    have h := mdlWeightSelf_varNorm_scaledLipschitz (r := r) hr (u := u) (G := fun v => Phi1u P v)
      (α := t ^ (P.natDegree - 1)) (D := D) (B := Phi1uConst P) (K := Phi1uLip P) (ρ := ρ)
      hρ0' hu0 huρ hmono hD0 hα3 hsup3 hA1nn hK1nn hstep3
    have hfun : (fun n : ℕ => ((t ^ (P.natDegree - 1) * Phi1u P (u n) : ℝ) : ℂ))
        = fun n : ℕ => mdlW3 P (N n) t := by
      funext n
      rw [hudef]
      simp only
      exact (mdlWeightSelf_mdlW3_eq P (hN1 n) htne).symm
    rw [hfun] at h
    simpa only [hT3def] using h
  have hV1 : PointwiseErgodicTheorems.variationalNorm r (fun n => mdlW1 P (N n) t)
      ≤ ENNReal.ofReal (D * T1) := by
    have h := mdlWeightSelf_varNorm_scaledLipschitz (r := r) hr (u := u) (G := fun v => (Phi1u P v)⁻¹)
      (α := (t ^ (P.natDegree - 1))⁻¹) (D := D) (B := 1 / c) (K := Phi1uLip P / c ^ 2)
      (ρ := ρ) hρ0' hu0 huρ hmono hD0 hα1 hsup1 (by positivity) (by positivity) hstep1
    have hfun : (fun n : ℕ => (((t ^ (P.natDegree - 1))⁻¹ * (Phi1u P (u n))⁻¹ : ℝ) : ℂ))
        = fun n : ℕ => mdlW1 P (N n) t := by
      funext n
      rw [hudef]
      simp only
      exact (mdlWeightSelf_mdlW1_eq P (hN1 n) htne
        (abs_pos.mp (lt_of_lt_of_le hc (hphi n)))).symm
    rw [hfun] at h
    simpa only [hT1def] using h
  have hV2 : PointwiseErgodicTheorems.variationalNorm r (fun n => mdlW2 P (N n) t)
      ≤ ENNReal.ofReal (D * T2) := by
    have h := mdlWeightSelf_varNorm_scaledLipschitz (r := r) hr (u := u)
      (G := fun v => Phi2u P v / (Phi1u P v) ^ 2)
      (α := (t ^ P.natDegree)⁻¹) (D := D) (B := Phi2uConst P / c ^ 2)
      (K := (Phi2uLip P * (Phi1uConst P) ^ 2
          + 2 * Phi2uConst P * Phi1uLip P * Phi1uConst P) / c ^ 4)
      (ρ := ρ) hρ0' hu0 huρ hmono hD0 hα2 hsup2 (by positivity) (by positivity) hstep2
    have hfun : (fun n : ℕ => (((t ^ P.natDegree)⁻¹
          * (Phi2u P (u n) / (Phi1u P (u n)) ^ 2) : ℝ) : ℂ))
        = fun n : ℕ => mdlW2 P (N n) t := by
      funext n
      rw [hudef]
      simp only
      exact (mdlWeightSelf_mdlW2_eq P hdeg (hN1 n) htpos).symm
    rw [hfun] at h
    simpa only [hT2def] using h
  refine ⟨?_, ?_, ?_⟩
  · refine hV1.trans ?_
    exact ENNReal.ofReal_le_ofReal (by
      rw [hCvdef]
      nlinarith [hT2nn, hT3nn, hD0])
  · refine hV2.trans ?_
    exact ENNReal.ofReal_le_ofReal (by
      rw [hCvdef]
      nlinarith [hT1nn, hT3nn, hD0])
  · refine hV3.trans ?_
    exact ENNReal.ofReal_le_ofReal (by
      rw [hCvdef]
      nlinarith [hT1nn, hT2nn, hD0])

end

end Work.KMTPlan.A6
