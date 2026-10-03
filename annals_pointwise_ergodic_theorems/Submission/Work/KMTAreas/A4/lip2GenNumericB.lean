import Mathlib

set_option maxHeartbeats 4000000

namespace Work.KMTAreas.A4

/-! ## Auxiliary arithmetic lemmas for `lip2GenNumericB`

Elementary real-variable bookkeeping (monotonicity of `x ↦ x^t`, comparison of
`rpow`/`zpow` expressions) that the numeric lemma `lip2GenNumericB` reduces to. -/

/-- From `Cbig * δ⁻¹ ^ Kbig ≤ N` with `0 < δ ≤ 1` we get `δ⁻¹ ^ e ≤ N / Cbig`
for every `e ≤ Kbig`. -/
lemma lipNB_dinv_le {δ e Kbig Cbig N : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hCbig0 : 0 < Cbig) (he : e ≤ Kbig)
    (hle : Cbig * δ⁻¹ ^ Kbig ≤ N) : δ⁻¹ ^ e ≤ N / Cbig := by
  have hbase : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ0).mpr hδ1
  have h1 : δ⁻¹ ^ e ≤ δ⁻¹ ^ Kbig := Real.rpow_le_rpow_of_exponent_le hbase he
  have h2 : δ⁻¹ ^ Kbig ≤ N / Cbig := by
    rw [le_div_iff₀ hCbig0, mul_comm]
    exact hle
  exact h1.trans h2

/-- `C₀ δ⁻¹^{K₀} ≤ N^{d-1}` given `C₀ ≤ Cbig`, `K₀ ≤ Kbig`, `Cbig δ⁻¹^{Kbig} ≤ N`,
`0 < δ ≤ 1`, `N ≥ 1`, `d ≥ 2`. -/
lemma lipNB_one {C₀ K₀ Kbig Cbig δ : ℝ} {N : ℕ} (d : ℕ)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hN : 1 ≤ N) (hCb0 : 0 < Cbig)
    (hCbge : C₀ ≤ Cbig) (hKge : K₀ ≤ Kbig) (hd : 2 ≤ d)
    (h9 : Cbig * δ⁻¹ ^ Kbig ≤ (N : ℝ)) :
    C₀ * δ⁻¹ ^ K₀ ≤ (N : ℝ) ^ (d - 1) := by
  have hbase : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ0).mpr hδ1
  have hK : δ⁻¹ ^ K₀ ≤ δ⁻¹ ^ Kbig := Real.rpow_le_rpow_of_exponent_le hbase hKge
  have h1 : C₀ * δ⁻¹ ^ K₀ ≤ Cbig * δ⁻¹ ^ Kbig :=
    mul_le_mul hCbge hK (Real.rpow_nonneg (le_of_lt (inv_pos.mpr hδ0)) _) (le_of_lt hCb0)
  have h2 : (N : ℝ) ≤ (N : ℝ) ^ (d - 1) := by
    have h1' : (N : ℝ) ^ (1 : ℕ) ≤ (N : ℝ) ^ (d - 1) :=
      pow_le_pow_right₀ (by exact_mod_cast hN) (by omega)
    simpa using h1'
  linarith

/-- `2^k ≤ 1/16` from `2^k ≤ CA δ^{-KA}/N` and `Cbig δ^{-Kbig} ≤ N`, when
`Cbig ≥ 16 CA`, `KA ≤ Kbig`, `0 < δ ≤ 1`. -/
lemma lipNB_two {CA KA Kbig Cbig δ : ℝ} {k : ℤ} {N : ℕ}
    (hCA : 0 < CA) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hN : 1 ≤ N)
    (hKAle : KA ≤ Kbig) (hCbig_ge : 16 * CA ≤ Cbig) (hCb0 : 0 < Cbig)
    (h2k : (2 : ℝ) ^ k ≤ CA * δ⁻¹ ^ KA / (N : ℝ))
    (h9 : Cbig * δ⁻¹ ^ Kbig ≤ (N : ℝ)) : (2 : ℝ) ^ k ≤ 1 / 16 := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (Nat.zero_lt_one.trans_le hN)
  have hbase : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ0).mpr hδ1
  have hKAle' : δ⁻¹ ^ KA ≤ δ⁻¹ ^ Kbig := Real.rpow_le_rpow_of_exponent_le hbase hKAle
  have hDpos : 0 < Cbig * δ⁻¹ ^ Kbig := mul_pos hCb0 (Real.rpow_pos_of_pos (inv_pos.mpr hδ0) Kbig)
  have hCAK0 : 0 < CA * δ⁻¹ ^ Kbig := mul_pos hCA (Real.rpow_pos_of_pos (inv_pos.mpr hδ0) Kbig)
  have step1 : CA * δ⁻¹ ^ KA / (N : ℝ) ≤ CA * δ⁻¹ ^ Kbig / (N : ℝ) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hKAle' hCA.le) hNpos.le
  have step2 : CA * δ⁻¹ ^ Kbig / (N : ℝ) ≤ CA * δ⁻¹ ^ Kbig / (Cbig * δ⁻¹ ^ Kbig) :=
    div_le_div_of_nonneg_left hCAK0.le hDpos h9
  have step3 : CA * δ⁻¹ ^ Kbig / (Cbig * δ⁻¹ ^ Kbig) = CA / Cbig := by
    field_simp
  have step4 : CA / Cbig ≤ 1 / 16 := by
    rw [div_le_iff₀ hCb0]
    linarith
  exact h2k.trans (le_trans step1 (le_trans step2 (le_trans (le_of_eq step3) step4)))

/-- The `max 2 (N δ^KA/(128 CA)) ≤ 1/(8·2^k)` estimate. -/
lemma lipNB_four {CA KA δ : ℝ} {k : ℤ} {N : ℕ}
    (hCA : 0 < CA) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hN : 1 ≤ N) (hKA : 0 < KA)
    (h2k : (2 : ℝ) ^ k ≤ CA * δ⁻¹ ^ KA / (N : ℝ))
    (h2k16 : (2 : ℝ) ^ k ≤ 1 / 16) :
    max 2 ((N : ℝ) * δ ^ KA / (128 * CA)) ≤ 1 / (8 * (2 : ℝ) ^ k) := by
  have hD : 0 < (2 : ℝ) ^ k := zpow_pos (by norm_num) k
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (Nat.zero_lt_one.trans_le hN)
  have hδKA : 0 < δ ^ KA := Real.rpow_pos_of_pos hδ0 KA
  have hP : 0 < (N : ℝ) * δ ^ KA := mul_pos hNpos hδKA
  have h1 : (2 : ℝ) ^ k * ((N : ℝ) * δ ^ KA) ≤ CA := by
    have hstep := mul_le_mul_of_nonneg_right h2k hP.le
    refine le_trans hstep (le_of_eq ?_)
    rw [Real.inv_rpow hδ0.le]
    field_simp
  have hA2 : 2 ≤ 1 / (8 * (2 : ℝ) ^ k) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 8 * (2 : ℝ) ^ k)]
    nlinarith [h2k16, hD]
  have hX : (N : ℝ) * δ ^ KA / (128 * CA) ≤ 1 / (128 * (2 : ℝ) ^ k) := by
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 128 * CA)
        (by positivity : (0 : ℝ) < 128 * (2 : ℝ) ^ k)]
    nlinarith [h1]
  have hmono : 1 / (128 * (2 : ℝ) ^ k) ≤ 1 / (8 * (2 : ℝ) ^ k) := by
    apply one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 8 * (2 : ℝ) ^ k)
    nlinarith [hD]
  exact max_le hA2 (hX.trans hmono)

/-- The key bound on `1 + N₀/μ` in terms of `δ`. -/
lemma lipNB_L {N N₀ : ℕ} {δ μ A' CA CE CS CN3 KA : ℝ} (d : ℕ)
    (hA' : 0 < A') (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hKA : 0 < KA)
    (hCE : 0 < CE) (hCS : 0 < CS) (hCN3 : 0 < CN3) (hCA : 0 < CA)
    (hN : 1 ≤ N) (hμ : 0 < μ)
    (hN0 : (N₀ : ℝ) ≤ A' * (N : ℝ) ^ d)
    (hμlow : δ ^ (8 * KA) * (N : ℝ) ^ d / (CS * CE ^ 4 * (CA + 1) ^ 4 * CA ^ 2 * CN3 ^ 2) ≤ μ) :
    1 + (N₀ : ℝ) / μ
      ≤ (1 + A' * (CS * CE ^ 4 * (CA + 1) ^ 4 * CA ^ 2 * CN3 ^ 2)) * (δ ^ (8 * KA))⁻¹ := by
  set cμ : ℝ := CS * CE ^ 4 * (CA + 1) ^ 4 * CA ^ 2 * CN3 ^ 2 with hcμ
  have hcμpos : 0 < cμ := by rw [hcμ]; positivity
  set a : ℝ := δ ^ (8 * KA) with ha
  have hapos : 0 < a := by rw [ha]; exact Real.rpow_pos_of_pos hδ0 _
  have ha1 : a ≤ 1 := by rw [ha]; exact Real.rpow_le_one hδ0.le hδ1 (by positivity)
  have hainv1 : 1 ≤ a⁻¹ := (one_le_inv₀ hapos).mpr ha1
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (Nat.zero_lt_one.trans_le hN)
  have hNd : (0 : ℝ) < (N : ℝ) ^ d := pow_pos hNpos d
  have hμlow' : a * (N : ℝ) ^ d / cμ ≤ μ := by rw [ha, hcμ]; exact hμlow
  have hprod : a * (N : ℝ) ^ d ≤ μ * cμ := (div_le_iff₀ hcμpos).1 hμlow'
  have hNd_le : (N : ℝ) ^ d ≤ μ * cμ / a := by
    rw [le_div_iff₀ hapos]; linarith [hprod]
  have h2 : (N : ℝ) ^ d / μ ≤ cμ * a⁻¹ := by
    rw [div_le_iff₀ hμ]
    calc (N : ℝ) ^ d ≤ μ * cμ / a := hNd_le
      _ = cμ * a⁻¹ * μ := by field_simp
  have h1 : (N₀ : ℝ) / μ ≤ A' * cμ * a⁻¹ := by
    calc (N₀ : ℝ) / μ ≤ A' * (N : ℝ) ^ d / μ := by
          rw [div_le_div_iff_of_pos_right hμ]
          linarith [hN0]
      _ = A' * ((N : ℝ) ^ d / μ) := by ring
      _ ≤ A' * (cμ * a⁻¹) := mul_le_mul_of_nonneg_left h2 hA'.le
      _ = A' * cμ * a⁻¹ := by ring
  have h3 : 1 + A' * cμ * a⁻¹ ≤ (1 + A' * cμ) * a⁻¹ := by
    have hAcμ : 0 ≤ A' * cμ := mul_nonneg hA'.le hcμpos.le
    nlinarith [hainv1, hAcμ]
  calc 1 + (N₀ : ℝ) / μ ≤ 1 + A' * cμ * a⁻¹ := by linarith
    _ ≤ (1 + A' * cμ) * a⁻¹ := h3
    _ = (1 + A' * (CS * CE ^ 4 * (CA + 1) ^ 4 * CA ^ 2 * CN3 ^ 2)) * (δ ^ (8 * KA))⁻¹ := by
        rw [hcμ, ha]

/-- The `(8A')^{KW}(1+N₀/μ)^{KW} ≤ N δ^{KA}/(128 CA)` estimate. -/
lemma lipNB_claim5 {A' CA KA KW Kbig Cbig CS CE CN3 Bb : ℝ} {N N₀ : ℕ} {δ μ : ℝ}
    (hA' : 2 ≤ A') (hCA : 0 < CA) (hKA : 0 < KA) (hKW : 0 < KW) (hCS : 0 < CS)
    (hCE : 0 < CE) (hCN3 : 0 < CN3) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hμ0 : 0 < μ)
    (hB : 0 < Bb)
    (hkey : 1 + (N₀ : ℝ) / μ ≤ Bb / δ ^ (8 * KA))
    (hKbig : KA + 8 * KA * KW ≤ Kbig)
    (hCbig : 128 * CA * (8 * A' * Bb) ^ KW ≤ Cbig)
    (h9 : Cbig * δ⁻¹ ^ Kbig ≤ (N : ℝ)) :
    (8 * A') ^ KW * (1 + (N₀ : ℝ) / μ) ^ KW ≤ (N : ℝ) * δ ^ KA / (128 * CA) := by
  have hδinv0 : 0 < δ⁻¹ := inv_pos.mpr hδ0
  have hA'nn : 0 ≤ 8 * A' := by linarith
  have hLpos : 0 < 1 + (N₀ : ℝ) / μ := by positivity
  have hkey' : 1 + (N₀ : ℝ) / μ ≤ Bb * δ⁻¹ ^ (8 * KA) := by
    rw [div_eq_mul_inv] at hkey
    rw [Real.inv_rpow hδ0.le]
    exact hkey
  have hLpow : (1 + (N₀ : ℝ) / μ) ^ KW ≤ Bb ^ KW * δ⁻¹ ^ (8 * KA * KW) := by
    have h1 : (1 + (N₀ : ℝ) / μ) ^ KW ≤ (Bb * δ⁻¹ ^ (8 * KA)) ^ KW :=
      Real.rpow_le_rpow hLpos.le hkey' hKW.le
    calc (1 + (N₀ : ℝ) / μ) ^ KW ≤ (Bb * δ⁻¹ ^ (8 * KA)) ^ KW := h1
      _ = Bb ^ KW * δ⁻¹ ^ (8 * KA * KW) := by
          rw [Real.mul_rpow hB.le (Real.rpow_nonneg hδinv0.le _),
            ← Real.rpow_mul hδinv0.le (8 * KA) KW]
  have hAB : (8 * A') ^ KW * (1 + (N₀ : ℝ) / μ) ^ KW
      ≤ (8 * A' * Bb) ^ KW * δ⁻¹ ^ (8 * KA * KW) := by
    have h1 : (8 * A') ^ KW * (1 + (N₀ : ℝ) / μ) ^ KW
        ≤ (8 * A') ^ KW * (Bb ^ KW * δ⁻¹ ^ (8 * KA * KW)) :=
      mul_le_mul_of_nonneg_left hLpow (Real.rpow_nonneg hA'nn _)
    have h2 : (8 * A') ^ KW * (Bb ^ KW * δ⁻¹ ^ (8 * KA * KW))
        = (8 * A' * Bb) ^ KW * δ⁻¹ ^ (8 * KA * KW) := by
      rw [Real.mul_rpow hA'nn hB.le]
      ring
    exact h1.trans (le_of_eq h2)
  have hexp : δ⁻¹ ^ (8 * KA * KW) ≤ δ ^ (KA - Kbig) := by
    have h1 : δ⁻¹ ^ (8 * KA * KW) = δ ^ (-(8 * KA * KW)) := by
      rw [Real.inv_rpow hδ0.le, Real.rpow_neg hδ0.le]
    rw [h1]
    exact Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (by linarith)
  have hNlower : 128 * CA * (8 * A' * Bb) ^ KW * δ⁻¹ ^ Kbig ≤ N :=
    le_trans (mul_le_mul_of_nonneg_right hCbig (Real.rpow_nonneg hδinv0.le _)) h9
  have hprod : δ⁻¹ ^ Kbig * δ ^ KA = δ ^ (KA - Kbig) := by
    rw [Real.inv_rpow hδ0.le, mul_comm, ← div_eq_mul_inv, ← Real.rpow_sub hδ0]
  have hfinal : (8 * A' * Bb) ^ KW * δ ^ (KA - Kbig) ≤ (N : ℝ) * δ ^ KA / (128 * CA) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 128 * CA)]
    have h := mul_le_mul_of_nonneg_right hNlower (Real.rpow_pos_of_pos hδ0 KA).le
    have hL3 : 128 * CA * (8 * A' * Bb) ^ KW * δ⁻¹ ^ Kbig * δ ^ KA
        = 128 * CA * (8 * A' * Bb) ^ KW * δ ^ (KA - Kbig) := by
      calc 128 * CA * (8 * A' * Bb) ^ KW * δ⁻¹ ^ Kbig * δ ^ KA
          = (128 * CA * (8 * A' * Bb) ^ KW) * (δ⁻¹ ^ Kbig * δ ^ KA) := by ring
        _ = (128 * CA * (8 * A' * Bb) ^ KW) * δ ^ (KA - Kbig) := by rw [hprod]
        _ = 128 * CA * (8 * A' * Bb) ^ KW * δ ^ (KA - Kbig) := by ring
    rw [hL3] at h
    calc (8 * A' * Bb) ^ KW * δ ^ (KA - Kbig) * (128 * CA)
        = 128 * CA * (8 * A' * Bb) ^ KW * δ ^ (KA - Kbig) := by ring
      _ ≤ (N : ℝ) * δ ^ KA := h
  exact hAB.trans ((mul_le_mul_of_nonneg_left hexp
    (Real.rpow_nonneg (by positivity) _)).trans hfinal)

/-- The `Cm (1+N₀/μ)^{Km} ≤ Cbig δ^{-Kbig}` estimate. -/
lemma lipNB_claim7 {δ KA Kbig Cbig Cm Km Bb L : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hKA : 0 < KA) (hKm : 0 < Km)
    (hCm : 0 < Cm) (hB : 0 < Bb) (hL0 : 0 < L) (hCb : 0 < Cbig)
    (hL : L ≤ Bb * (δ ^ (8 * KA))⁻¹)
    (hCbig : Cm * Bb ^ Km ≤ Cbig) (hKbig7 : 8 * KA * Km ≤ Kbig) :
    Cm * L ^ Km ≤ Cbig * δ⁻¹ ^ Kbig := by
  have hδinv0 : 0 < δ⁻¹ := inv_pos.mpr hδ0
  have hLpow : L ^ Km ≤ Bb ^ Km * δ⁻¹ ^ (8 * KA * Km) := by
    have h1 : L ^ Km ≤ (Bb * δ⁻¹ ^ (8 * KA)) ^ Km := by
      apply Real.rpow_le_rpow hL0.le _ hKm.le
      rw [Real.inv_rpow hδ0.le]
      exact hL
    calc L ^ Km ≤ (Bb * δ⁻¹ ^ (8 * KA)) ^ Km := h1
      _ = Bb ^ Km * δ⁻¹ ^ (8 * KA * Km) := by
          rw [Real.mul_rpow hB.le (Real.rpow_nonneg hδinv0.le _),
            ← Real.rpow_mul hδinv0.le (8 * KA) Km]
  have hexp : δ⁻¹ ^ (8 * KA * Km) ≤ δ⁻¹ ^ Kbig :=
    Real.rpow_le_rpow_of_exponent_le ((one_le_inv₀ hδ0).mpr hδ1) hKbig7
  calc Cm * L ^ Km ≤ Cm * (Bb ^ Km * δ⁻¹ ^ (8 * KA * Km)) :=
        mul_le_mul_of_nonneg_left hLpow hCm.le
    _ = Cm * Bb ^ Km * δ⁻¹ ^ (8 * KA * Km) := by ring
    _ ≤ Cbig * δ⁻¹ ^ (8 * KA * Km) :=
        mul_le_mul_of_nonneg_right hCbig (Real.rpow_nonneg hδinv0.le _)
    _ ≤ Cbig * δ⁻¹ ^ Kbig :=
        mul_le_mul_of_nonneg_left hexp (le_of_lt hCb)

/-- The `Cm (1+N₀/μ)^{Km}/(max 2 (N δ^KA/(128 CA)))^d ≤ Cbig δ^{-Kbig}/N^d` estimate. -/
lemma lipNB_claim8 {δ KA Kbig Cbig Cm Km Bb L N CA : ℝ} (d : ℕ)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hKA : 0 < KA) (hKbig : 0 < Kbig) (hKm : 0 < Km)
    (hCm : 0 < Cm) (hB : 0 < Bb) (hL0 : 0 < L) (hN : 0 < N) (hCA : 0 < CA) (hCb : 0 < Cbig)
    (hL : L ≤ Bb * (δ ^ (8 * KA))⁻¹)
    (hT : Cbig * δ⁻¹ ^ Kbig ≤ N)
    (hCbig : Cm * Bb ^ Km * (128 * CA) ^ d ≤ Cbig)
    (hKbig8 : 8 * KA * Km + KA * d ≤ Kbig) :
    Cm * L ^ Km / (max 2 (N * δ ^ KA / (128 * CA))) ^ d ≤ Cbig * δ⁻¹ ^ Kbig / N ^ d := by
  have hδinv0 : 0 < δ⁻¹ := inv_pos.mpr hδ0
  have hδKA : 0 < δ ^ KA := Real.rpow_pos_of_pos hδ0 KA
  have hApos : 0 < N * δ ^ KA / (128 * CA) := by positivity
  have hMpos : 0 < max 2 (N * δ ^ KA / (128 * CA)) :=
    lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hAM : N * δ ^ KA / (128 * CA) ≤ max 2 (N * δ ^ KA / (128 * CA)) := le_max_right _ _
  have hLpow : L ^ Km ≤ Bb ^ Km * δ⁻¹ ^ (8 * KA * Km) := by
    have h1 : L ^ Km ≤ (Bb * δ⁻¹ ^ (8 * KA)) ^ Km := by
      apply Real.rpow_le_rpow hL0.le _ hKm.le
      rw [Real.inv_rpow hδ0.le]
      exact hL
    calc L ^ Km ≤ (Bb * δ⁻¹ ^ (8 * KA)) ^ Km := h1
      _ = Bb ^ Km * δ⁻¹ ^ (8 * KA * Km) := by
          rw [Real.mul_rpow hB.le (Real.rpow_nonneg hδinv0.le _),
            ← Real.rpow_mul hδinv0.le (8 * KA) Km]
  have hXpos : 0 < Bb ^ Km * δ⁻¹ ^ (8 * KA * Km) :=
    mul_pos (Real.rpow_pos_of_pos hB Km) (Real.rpow_pos_of_pos hδinv0 _)
  have hAd : (N * δ ^ KA / (128 * CA)) ^ d
      = N ^ d / (δ⁻¹ ^ (KA * (d : ℝ)) * (128 * CA) ^ d) := by
    have hsub : (δ ^ KA) ^ d = δ ^ (KA * (d : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hδ0.le KA (d : ℝ)]
    have h1 : (N * δ ^ KA / (128 * CA)) ^ d
        = N ^ d * δ ^ (KA * (d : ℝ)) / (128 * CA) ^ d := by
      rw [div_pow, mul_pow, hsub]
    have h2 : δ ^ (KA * (d : ℝ)) = (δ⁻¹ ^ (KA * (d : ℝ)))⁻¹ := by
      rw [Real.inv_rpow hδ0.le, inv_inv]
    rw [h1, h2, div_eq_mul_inv, div_eq_mul_inv, mul_inv]
    ring
  have hstep1 : Cm * L ^ Km / (max 2 (N * δ ^ KA / (128 * CA))) ^ d
      ≤ Cm * (Bb ^ Km * δ⁻¹ ^ (8 * KA * Km)) / (N * δ ^ KA / (128 * CA)) ^ d := by
    have ha : Cm * L ^ Km / (max 2 (N * δ ^ KA / (128 * CA))) ^ d
        ≤ Cm * (Bb ^ Km * δ⁻¹ ^ (8 * KA * Km))
            / (max 2 (N * δ ^ KA / (128 * CA))) ^ d :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hLpow hCm.le)
        (pow_nonneg hMpos.le d)
    have hb : Cm * (Bb ^ Km * δ⁻¹ ^ (8 * KA * Km))
          / (max 2 (N * δ ^ KA / (128 * CA))) ^ d
        ≤ Cm * (Bb ^ Km * δ⁻¹ ^ (8 * KA * Km)) / (N * δ ^ KA / (128 * CA)) ^ d :=
      div_le_div_of_nonneg_left (mul_nonneg hCm.le hXpos.le) (pow_pos hApos d)
        (pow_le_pow_left₀ hApos.le hAM d)
    exact ha.trans hb
  have hstep2 : Cm * (Bb ^ Km * δ⁻¹ ^ (8 * KA * Km)) / (N * δ ^ KA / (128 * CA)) ^ d
      = Cm * Bb ^ Km * (128 * CA) ^ d * δ⁻¹ ^ (8 * KA * Km + KA * (d : ℝ)) / N ^ d := by
    have hinv : ((N * δ ^ KA / (128 * CA)) ^ d)⁻¹
        = (128 * CA) ^ d * δ⁻¹ ^ (KA * (d : ℝ)) / N ^ d := by
      rw [hAd, inv_div]
      ring
    calc Cm * (Bb ^ Km * δ⁻¹ ^ (8 * KA * Km)) / (N * δ ^ KA / (128 * CA)) ^ d
        = Cm * (Bb ^ Km * δ⁻¹ ^ (8 * KA * Km)) * (((N * δ ^ KA / (128 * CA)) ^ d)⁻¹) := by
          rw [div_eq_mul_inv]
      _ = Cm * (Bb ^ Km * δ⁻¹ ^ (8 * KA * Km))
            * ((128 * CA) ^ d * δ⁻¹ ^ (KA * (d : ℝ)) / N ^ d) := by
          rw [hinv]
      _ = Cm * Bb ^ Km * (128 * CA) ^ d
            * (δ⁻¹ ^ (8 * KA * Km) * δ⁻¹ ^ (KA * (d : ℝ))) / N ^ d := by
          ring
      _ = Cm * Bb ^ Km * (128 * CA) ^ d * δ⁻¹ ^ (8 * KA * Km + KA * (d : ℝ)) / N ^ d := by
          rw [Real.rpow_add hδinv0]
  have hbig : Cm * Bb ^ Km * (128 * CA) ^ d * δ⁻¹ ^ (8 * KA * Km + KA * (d : ℝ))
      ≤ Cbig * δ⁻¹ ^ Kbig :=
    mul_le_mul hCbig (Real.rpow_le_rpow_of_exponent_le ((one_le_inv₀ hδ0).mpr hδ1) hKbig8)
      (Real.rpow_nonneg hδinv0.le _) hCb.le
  calc Cm * L ^ Km / (max 2 (N * δ ^ KA / (128 * CA))) ^ d
      ≤ Cm * (Bb ^ Km * δ⁻¹ ^ (8 * KA * Km)) / (N * δ ^ KA / (128 * CA)) ^ d := hstep1
    _ = Cm * Bb ^ Km * (128 * CA) ^ d * δ⁻¹ ^ (8 * KA * Km + KA * (d : ℝ)) / N ^ d := hstep2
    _ ≤ Cbig * δ⁻¹ ^ Kbig / N ^ d := div_le_div_of_nonneg_right hbig (pow_nonneg hN.le d)

/-- The `D δ^c N^d ≤ μ/(Cm (1+N₀/μ)^{Km})` estimate, in cleared-denominator form. -/
lemma lipNB_claim9 {δ KA Km Cm cμ Bb L μ : ℝ} (N : ℝ) (d : ℕ)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hKA : 0 < KA) (hKm : 0 < Km) (hCm : 0 < Cm)
    (hcμ : 0 < cμ) (hB : 0 < Bb) (hL0 : 0 < L) (hN : 0 < N) (hμ : 0 < μ)
    (hL : L ≤ Bb * (δ ^ (8 * KA))⁻¹)
    (hμlow : δ ^ (8 * KA) * N ^ d / cμ ≤ μ) :
    (1 / (1 + cμ * Cm * Bb ^ Km)) * δ ^ (8 * KA * (1 + Km)) * N ^ d * (Cm * L ^ Km) ≤ μ := by
  have hδinv0 : 0 < δ⁻¹ := inv_pos.mpr hδ0
  have hLpow : L ^ Km ≤ Bb ^ Km * δ⁻¹ ^ (8 * KA * Km) := by
    have h1 : L ^ Km ≤ (Bb * δ⁻¹ ^ (8 * KA)) ^ Km := by
      apply Real.rpow_le_rpow hL0.le _ hKm.le
      rw [Real.inv_rpow hδ0.le]
      exact hL
    calc L ^ Km ≤ (Bb * δ⁻¹ ^ (8 * KA)) ^ Km := h1
      _ = Bb ^ Km * δ⁻¹ ^ (8 * KA * Km) := by
          rw [Real.mul_rpow hB.le (Real.rpow_nonneg hδinv0.le _),
            ← Real.rpow_mul hδinv0.le (8 * KA) Km]
  have hZpos : 0 < cμ * Cm * Bb ^ Km :=
    mul_pos (mul_pos hcμ hCm) (Real.rpow_pos_of_pos hB Km)
  have hfac : δ ^ (8 * KA * Km) * δ⁻¹ ^ (8 * KA * Km) = 1 := by
    rw [Real.inv_rpow hδ0.le, mul_inv_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos hδ0 _))]
  have hsplit : δ ^ (8 * KA * (1 + Km)) = δ ^ (8 * KA) * δ ^ (8 * KA * Km) := by
    rw [← Real.rpow_add hδ0]
    congr 1
    ring
  have hstep1 : (1 / (1 + cμ * Cm * Bb ^ Km)) * δ ^ (8 * KA * (1 + Km)) * N ^ d * (Cm * L ^ Km)
      ≤ (1 / (1 + cμ * Cm * Bb ^ Km)) * δ ^ (8 * KA * (1 + Km)) * N ^ d
          * (Cm * (Bb ^ Km * δ⁻¹ ^ (8 * KA * Km))) := by
    apply mul_le_mul_of_nonneg_left
    · exact mul_le_mul_of_nonneg_left hLpow hCm.le
    · have h1 : (0 : ℝ) ≤ 1 / (1 + cμ * Cm * Bb ^ Km) := by positivity
      have h2 : (0 : ℝ) ≤ δ ^ (8 * KA * (1 + Km)) := Real.rpow_nonneg hδ0.le _
      have h3 : (0 : ℝ) ≤ N ^ d := pow_nonneg hN.le d
      exact mul_nonneg (mul_nonneg h1 h2) h3
  have hstep2 : (1 / (1 + cμ * Cm * Bb ^ Km)) * δ ^ (8 * KA * (1 + Km)) * N ^ d
        * (Cm * (Bb ^ Km * δ⁻¹ ^ (8 * KA * Km)))
      = (1 / (1 + cμ * Cm * Bb ^ Km)) * δ ^ (8 * KA) * N ^ d * Cm * Bb ^ Km := by
    rw [hsplit]
    have hre : (1 / (1 + cμ * Cm * Bb ^ Km)) * (δ ^ (8 * KA) * δ ^ (8 * KA * Km)) * N ^ d
          * (Cm * (Bb ^ Km * δ⁻¹ ^ (8 * KA * Km)))
        = (1 / (1 + cμ * Cm * Bb ^ Km)) * δ ^ (8 * KA) * N ^ d * Cm * Bb ^ Km
            * (δ ^ (8 * KA * Km) * δ⁻¹ ^ (8 * KA * Km)) := by ring
    rw [hre, hfac, mul_one]
  have hDZ : 1 / (1 + cμ * Cm * Bb ^ Km) ≤ 1 / (cμ * Cm * Bb ^ Km) := by
    apply one_div_le_one_div_of_le hZpos
    linarith
  have hstep3 : (1 / (1 + cμ * Cm * Bb ^ Km)) * δ ^ (8 * KA) * N ^ d * Cm * Bb ^ Km
      ≤ δ ^ (8 * KA) * N ^ d * Cm * Bb ^ Km / (cμ * Cm * Bb ^ Km) := by
    have h : (1 / (1 + cμ * Cm * Bb ^ Km)) * (δ ^ (8 * KA) * N ^ d * Cm * Bb ^ Km)
        ≤ (1 / (cμ * Cm * Bb ^ Km)) * (δ ^ (8 * KA) * N ^ d * Cm * Bb ^ Km) :=
      mul_le_mul_of_nonneg_right hDZ (by positivity)
    calc (1 / (1 + cμ * Cm * Bb ^ Km)) * δ ^ (8 * KA) * N ^ d * Cm * Bb ^ Km
        = (1 / (1 + cμ * Cm * Bb ^ Km)) * (δ ^ (8 * KA) * N ^ d * Cm * Bb ^ Km) := by ring
      _ ≤ (1 / (cμ * Cm * Bb ^ Km)) * (δ ^ (8 * KA) * N ^ d * Cm * Bb ^ Km) := h
      _ = δ ^ (8 * KA) * N ^ d * Cm * Bb ^ Km / (cμ * Cm * Bb ^ Km) := by
            rw [div_eq_mul_inv]; ring
  have hstep4 : δ ^ (8 * KA) * N ^ d * Cm * Bb ^ Km / (cμ * Cm * Bb ^ Km)
      = δ ^ (8 * KA) * N ^ d / cμ := by
    rw [show δ ^ (8 * KA) * N ^ d * Cm * Bb ^ Km = (δ ^ (8 * KA) * N ^ d) * (Cm * Bb ^ Km)
          by ring,
        show cμ * Cm * Bb ^ Km = cμ * (Cm * Bb ^ Km) by ring]
    exact mul_div_mul_right _ _ (by positivity : Cm * Bb ^ Km ≠ 0)
  calc (1 / (1 + cμ * Cm * Bb ^ Km)) * δ ^ (8 * KA * (1 + Km)) * N ^ d * (Cm * L ^ Km)
      ≤ (1 / (1 + cμ * Cm * Bb ^ Km)) * δ ^ (8 * KA * (1 + Km)) * N ^ d
          * (Cm * (Bb ^ Km * δ⁻¹ ^ (8 * KA * Km))) := hstep1
    _ = (1 / (1 + cμ * Cm * Bb ^ Km)) * δ ^ (8 * KA) * N ^ d * Cm * Bb ^ Km := hstep2
    _ ≤ δ ^ (8 * KA) * N ^ d * Cm * Bb ^ Km / (cμ * Cm * Bb ^ Km) := hstep3
    _ = δ ^ (8 * KA) * N ^ d / cμ := hstep4
    _ ≤ μ := hμlow

/-- The `S ≤ CN3 N` estimate. -/
lemma lipNB_S {CA KA Kbig Cbig X CN3 : ℝ} {N : ℕ} {δ S : ℝ}
    (hCA : 0 < CA) (hKA : 0 < KA) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hN : 1 ≤ N)
    (hCb : 0 < Cbig) (hCB : Cbig * δ⁻¹ ^ Kbig ≤ (N : ℝ))
    (hX1 : 1 ≤ X) (hXnn : 0 ≤ X)
    (hCbge : 2 * X ≤ Cbig) (hKbig : 2 * KA / 11 ≤ Kbig)
    (hCN3 : 2 + X / (128 * CA) ≤ CN3)
    (hS : S ≤ (N : ℝ) + max 2 ((N : ℝ) * δ ^ KA / (128 * CA)) *
        (max 1 (X * δ⁻¹ ^ ((KA + KA) / 11)))) :
    S ≤ CN3 * (N : ℝ) := by
  have hB1ge1 : 1 ≤ X * δ⁻¹ ^ ((KA + KA) / 11) := by
    have h2 : 1 ≤ δ⁻¹ ^ ((KA + KA) / 11) :=
      Real.one_le_rpow ((one_le_inv₀ hδ0).mpr hδ1) (by positivity)
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ X * δ⁻¹ ^ ((KA + KA) / 11) := mul_le_mul hX1 h2 (by norm_num) hXnn
  rw [max_eq_right hB1ge1] at hS
  have hcore : δ⁻¹ ^ ((KA + KA) / 11) ≤ (N : ℝ) / Cbig :=
    lipNB_dinv_le hδ0 hδ1 hCb (by linarith) hCB
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (Nat.zero_lt_one.trans_le hN)
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := hNpos.le
  have hterm1 : 2 * (X * δ⁻¹ ^ ((KA + KA) / 11)) ≤ (N : ℝ) := by
    have h1 : X * δ⁻¹ ^ ((KA + KA) / 11) ≤ X * ((N : ℝ) / Cbig) :=
      mul_le_mul_of_nonneg_left hcore hXnn
    have h3 : 2 * (X / Cbig) ≤ 1 := by
      rw [show 2 * (X / Cbig) = 2 * X / Cbig by ring]
      rw [div_le_iff₀ hCb]
      linarith
    calc 2 * (X * δ⁻¹ ^ ((KA + KA) / 11)) ≤ 2 * (X * ((N : ℝ) / Cbig)) := by linarith
      _ = (N : ℝ) * (2 * (X / Cbig)) := by ring
      _ ≤ (N : ℝ) * 1 := mul_le_mul_of_nonneg_left h3 hNnn
      _ = (N : ℝ) := by ring
  have hterm2 : ((N : ℝ) * δ ^ KA / (128 * CA)) * (X * δ⁻¹ ^ ((KA + KA) / 11))
      ≤ (N : ℝ) * (X / (128 * CA)) := by
    have hfac : δ ^ KA * δ⁻¹ ^ ((KA + KA) / 11) ≤ 1 := by
      rw [Real.inv_rpow hδ0.le, ← div_eq_mul_inv, ← Real.rpow_sub hδ0]
      apply Real.rpow_le_one hδ0.le hδ1
      linarith
    calc ((N : ℝ) * δ ^ KA / (128 * CA)) * (X * δ⁻¹ ^ ((KA + KA) / 11))
        = ((N : ℝ) * X / (128 * CA)) * (δ ^ KA * δ⁻¹ ^ ((KA + KA) / 11)) := by ring
      _ ≤ ((N : ℝ) * X / (128 * CA)) * 1 := by
            apply mul_le_mul_of_nonneg_left hfac
            positivity
      _ = (N : ℝ) * (X / (128 * CA)) := by ring
  have hXle : X / (128 * CA) ≤ CN3 - 1 := by linarith
  have hS' : S ≤ (N : ℝ) + max 2 ((N : ℝ) * δ ^ KA / (128 * CA))
      * (X * δ⁻¹ ^ ((KA + KA) / 11)) := hS
  calc S ≤ (N : ℝ) + max 2 ((N : ℝ) * δ ^ KA / (128 * CA))
        * (X * δ⁻¹ ^ ((KA + KA) / 11)) := hS'
    _ = (N : ℝ) + max (2 * (X * δ⁻¹ ^ ((KA + KA) / 11)))
          (((N : ℝ) * δ ^ KA / (128 * CA)) * (X * δ⁻¹ ^ ((KA + KA) / 11))) := by
        rw [max_mul_of_nonneg]
        exact mul_nonneg hXnn (Real.rpow_nonneg (inv_nonneg.mpr hδ0.le) _)
    _ ≤ (N : ℝ) + (N : ℝ) * (CN3 - 1) := by
        have hCN1 : 1 ≤ CN3 - 1 := by
          have hnX : (0 : ℝ) ≤ X / (128 * CA) := by positivity
          linarith
        have h2 : 2 * (X * δ⁻¹ ^ ((KA + KA) / 11)) ≤ (N : ℝ) * (CN3 - 1) := by
          have hNle : (N : ℝ) ≤ (N : ℝ) * (CN3 - 1) := by
            have hh := mul_le_mul_of_nonneg_left hCN1 hNnn
            rwa [mul_one] at hh
          linarith
        have h : max (2 * (X * δ⁻¹ ^ ((KA + KA) / 11)))
            (((N : ℝ) * δ ^ KA / (128 * CA)) * (X * δ⁻¹ ^ ((KA + KA) / 11)))
            ≤ (N : ℝ) * (CN3 - 1) :=
          max_le h2 (hterm2.trans (mul_le_mul_of_nonneg_left hXle hNnn))
        linarith
    _ = CN3 * (N : ℝ) := by ring

theorem lip2GenNumericB (P : Polynomial ℤ) (hP : 2 ≤ P.natDegree) (CA KA C₀ K₀ CE Ct CS CN3 Cm Km CW KW CG A' : ℝ) (hA' : 2 ≤ A') (hCA : 0 < CA) (hKA : 0 < KA) (hC₀ : 0 < C₀) (hK₀ : 0 < K₀) (hCE : 0 < CE) (hCt : 0 < Ct) (hCS : 0 < CS) (hCN3 : 0 < CN3) (hCN3big : 2 + (2 * Ct * (CE * (CA + 1)) ^ 2 * CA + 1) / (128 * CA) ≤ CN3) (hCm : 0 < Cm) (hKm : 0 < Km) (hCW : 0 < CW) (hKW : 0 < KW) (hCG : 0 < CG) : ∃ (D Kbig Cbig c : ℝ), 0 < D ∧ 0 < Kbig ∧ 0 < Cbig ∧ 0 < c ∧ ∀ (N N₀ : ℕ) (δ : ℝ) (k : ℤ) (μ S : ℝ), 1 ≤ N → 0 < δ → δ ≤ 1 → (2 : ℝ) ^ k ≤ CA * δ⁻¹ ^ KA / (N : ℝ) → (N₀ : ℝ) ≤ A' * (N : ℝ) ^ P.natDegree → 0 < μ → δ ^ (8 * KA) * (N : ℝ) ^ P.natDegree / (CS * CE ^ 4 * (CA + 1) ^ 4 * CA ^ 2 * CN3 ^ 2) ≤ μ → Cbig * δ⁻¹ ^ Kbig ≤ (N : ℝ) → S ≤ (N : ℝ) + (max 2 ((N : ℝ) * δ ^ KA / (128 * CA))) * (max 1 ((2 * Ct * (CE * (CA + 1)) ^ 2 * CA + 1) * δ⁻¹ ^ ((KA + KA) / 11))) → (C₀ * δ⁻¹ ^ K₀ ≤ (N : ℝ) ^ (P.natDegree - 1)) ∧ ((2 : ℝ) ^ k ≤ 1 / 16) ∧ (2 ≤ max 2 ((N : ℝ) * δ ^ KA / (128 * CA))) ∧ (max 2 ((N : ℝ) * δ ^ KA / (128 * CA)) ≤ 1 / (8 * (2 : ℝ) ^ k)) ∧ ((8 * A') ^ KW * (1 + (N₀ : ℝ) / μ) ^ KW ≤ max 2 ((N : ℝ) * δ ^ KA / (128 * CA))) ∧ (S ≤ CN3 * (N : ℝ)) ∧ (Cm * (1 + (N₀ : ℝ) / μ) ^ Km ≤ Cbig * δ⁻¹ ^ Kbig) ∧ (Cm * (1 + (N₀ : ℝ) / μ) ^ Km / (max 2 ((N : ℝ) * δ ^ KA / (128 * CA))) ^ P.natDegree ≤ Cbig * δ⁻¹ ^ Kbig / (N : ℝ) ^ P.natDegree) ∧ (D * δ ^ c * (N : ℝ) ^ P.natDegree ≤ μ / (Cm * (1 + (N₀ : ℝ) / μ) ^ Km)) := by
  set K1 : ℝ := 2 * Ct * (CE * (CA + 1)) ^ 2 * CA + 1 with hK1
  set cμ : ℝ := CS * CE ^ 4 * (CA + 1) ^ 4 * CA ^ 2 * CN3 ^ 2 with hcμ
  set Bb : ℝ := 1 + A' * cμ with hBb
  set Z : ℝ := cμ * Cm * Bb ^ Km with hZ
  set KB : ℝ := K₀ + KA + 2 * KA / 11 + (8 * KA * Km + KA * (P.natDegree : ℝ))
    + KA * (8 * KW + 1) + 1 with hKB
  set CB : ℝ := C₀ + 16 * CA + 2 * K1 + 128 * CA * (8 * A') ^ KW * Bb ^ KW + Cm * Bb ^ Km
    + Cm * Bb ^ Km * (128 * CA) ^ P.natDegree + 1 with hCB
  have hA'pos : 0 < A' := by linarith
  have hK1ge1 : 1 ≤ K1 := by
    rw [hK1]
    have h : (0 : ℝ) ≤ 2 * Ct * (CE * (CA + 1)) ^ 2 * CA := by positivity
    linarith
  have hK1pos : 0 < K1 := lt_of_lt_of_le zero_lt_one hK1ge1
  have hcμpos : 0 < cμ := by rw [hcμ]; positivity
  have hBbpos : 0 < Bb := by
    rw [hBb]
    have h : 0 ≤ A' * cμ := mul_nonneg hA'pos.le hcμpos.le
    linarith
  have hZpos : 0 < Z := by
    rw [hZ]
    exact mul_pos (mul_pos hcμpos hCm) (Real.rpow_pos_of_pos hBbpos Km)
  have hCBpos : 0 < CB := by
    rw [hCB]
    have h1 : (0 : ℝ) < C₀ := hC₀
    have h2 : (0 : ℝ) < 16 * CA := by positivity
    have h3 : (0 : ℝ) < 2 * K1 := by positivity
    have h4 : (0 : ℝ) < 128 * CA * (8 * A') ^ KW * Bb ^ KW := by
      have ha : 0 < 128 * CA := by positivity
      have hb : 0 < (8 * A') ^ KW := Real.rpow_pos_of_pos (by linarith) _
      have hc : 0 < Bb ^ KW := Real.rpow_pos_of_pos hBbpos _
      exact mul_pos (mul_pos ha hb) hc
    have h5 : (0 : ℝ) < Cm * Bb ^ Km := mul_pos hCm (Real.rpow_pos_of_pos hBbpos _)
    have h6 : (0 : ℝ) ≤ Cm * Bb ^ Km * (128 * CA) ^ P.natDegree :=
      mul_nonneg h5.le (pow_nonneg (by positivity) _)
    linarith
  have hKBpos : 0 < KB := by
    rw [hKB]
    have h2 : (0 : ℝ) < KA := hKA
    have h3 : (0 : ℝ) ≤ 2 * KA / 11 := by positivity
    have h4 : (0 : ℝ) ≤ 8 * KA * Km + KA * (P.natDegree : ℝ) := by positivity
    have h5 : (0 : ℝ) ≤ KA * (8 * KW + 1) := by positivity
    linarith
  refine ⟨1 / (1 + Z), KB, CB, 8 * KA * (1 + Km), ?_, hKBpos, hCBpos, ?_, ?_⟩
  · exact div_pos one_pos (by linarith)
  · positivity
  · intro N N₀ δ k μ S hN hδ0 hδ1 h2k hN0 hμ hμlow hCbigle hS
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (Nat.zero_lt_one.trans_le hN)
    have hNnn : (0 : ℝ) ≤ (N : ℝ) := hNpos.le
    have hn16 : (0 : ℝ) ≤ 16 * CA := by positivity
    have hn2K1 : (0 : ℝ) ≤ 2 * K1 := by positivity
    have hn128 : (0 : ℝ) ≤ 128 * CA * (8 * A') ^ KW * Bb ^ KW := by
      have ha : (0 : ℝ) ≤ 128 * CA := by positivity
      have hb : (0 : ℝ) ≤ (8 * A') ^ KW := Real.rpow_nonneg (by linarith) _
      have hc : (0 : ℝ) ≤ Bb ^ KW := Real.rpow_nonneg hBbpos.le _
      exact mul_nonneg (mul_nonneg ha hb) hc
    have hnCm : (0 : ℝ) ≤ Cm * Bb ^ Km := mul_nonneg hCm.le (Real.rpow_nonneg hBbpos.le _)
    have hnCmd : (0 : ℝ) ≤ Cm * Bb ^ Km * (128 * CA) ^ P.natDegree :=
      mul_nonneg hnCm (pow_nonneg (by positivity) _)
    have hCb_C0 : C₀ ≤ CB := by rw [hCB]; linarith
    have hCb_16 : 16 * CA ≤ CB := by rw [hCB]; linarith
    have hCb_2K1 : 2 * K1 ≤ CB := by rw [hCB]; linarith
    have hCb_128 : 128 * CA * (8 * A') ^ KW * Bb ^ KW ≤ CB := by rw [hCB]; linarith
    have hCb_Cm : Cm * Bb ^ Km ≤ CB := by rw [hCB]; linarith
    have hCb_Cmd : Cm * Bb ^ Km * (128 * CA) ^ P.natDegree ≤ CB := by rw [hCB]; linarith
    have hn2KA : (0 : ℝ) ≤ 2 * KA / 11 := by positivity
    have hn8 : (0 : ℝ) ≤ 8 * KA * Km + KA * (P.natDegree : ℝ) := by positivity
    have hnKW : (0 : ℝ) ≤ KA * (8 * KW + 1) := by positivity
    have hKB_K0 : K₀ ≤ KB := by rw [hKB]; linarith
    have hKB_KA : KA ≤ KB := by rw [hKB]; linarith
    have hKB_2KA : 2 * KA / 11 ≤ KB := by rw [hKB]; linarith
    have hKB_8 : 8 * KA * Km + KA * (P.natDegree : ℝ) ≤ KB := by rw [hKB]; linarith
    have hKB_KW : KA * (8 * KW + 1) ≤ KB := by rw [hKB]; linarith
    have hKB5 : KA + 8 * KA * KW ≤ KB := by
      have heq : KA * (8 * KW + 1) = KA + 8 * KA * KW := by ring
      linarith [hKB_KW, heq]
    have hKB_8' : 8 * KA * Km ≤ KB := by
      have h : (0 : ℝ) ≤ KA * (P.natDegree : ℝ) := by positivity
      linarith [hKB_8]
    have hc1 : C₀ * δ⁻¹ ^ K₀ ≤ (N : ℝ) ^ (P.natDegree - 1) :=
      lipNB_one (d := P.natDegree) hδ0 hδ1 hN hCBpos hCb_C0 hKB_K0 hP hCbigle
    have hc2 : (2 : ℝ) ^ k ≤ 1 / 16 :=
      lipNB_two hCA hδ0 hδ1 hN hKB_KA hCb_16 hCBpos h2k hCbigle
    have hc3 : 2 ≤ max 2 ((N : ℝ) * δ ^ KA / (128 * CA)) := le_max_left 2 _
    have hc4 : max 2 ((N : ℝ) * δ ^ KA / (128 * CA)) ≤ 1 / (8 * (2 : ℝ) ^ k) :=
      lipNB_four hCA hδ0 hδ1 hN hKA h2k hc2
    have hL : 1 + (N₀ : ℝ) / μ ≤ Bb * (δ ^ (8 * KA))⁻¹ := by
      have h := lipNB_L (d := P.natDegree) hA'pos hδ0 hδ1 hKA hCE hCS hCN3 hCA hN hμ hN0 hμlow
      simpa [hBb, hcμ] using h
    have hkey : 1 + (N₀ : ℝ) / μ ≤ Bb / δ ^ (8 * KA) := by
      rw [div_eq_mul_inv]
      exact hL
    have hCb5 : 128 * CA * (8 * A' * Bb) ^ KW ≤ CB := by
      have hmr : (8 * A' * Bb) ^ KW = (8 * A') ^ KW * Bb ^ KW :=
        Real.mul_rpow (by linarith : (0 : ℝ) ≤ 8 * A') hBbpos.le
      rw [hmr]
      have h2 : 128 * CA * ((8 * A') ^ KW * Bb ^ KW)
          = 128 * CA * (8 * A') ^ KW * Bb ^ KW := by ring
      rw [h2]
      exact hCb_128
    have hc5 : (8 * A') ^ KW * (1 + (N₀ : ℝ) / μ) ^ KW
        ≤ max 2 ((N : ℝ) * δ ^ KA / (128 * CA)) :=
      (lipNB_claim5 (Bb := Bb) hA' hCA hKA hKW hCS hCE hCN3 hδ0 hδ1 hμ hBbpos hkey hKB5 hCb5
        hCbigle).trans (le_max_right _ _)
    have hCN3' : 2 + K1 / (128 * CA) ≤ CN3 := by simpa [hK1] using hCN3big
    have hS' : S ≤ (N : ℝ) + max 2 ((N : ℝ) * δ ^ KA / (128 * CA))
        * (max 1 (K1 * δ⁻¹ ^ ((KA + KA) / 11))) := by
      simpa [hK1] using hS
    have hc6 : S ≤ CN3 * (N : ℝ) :=
      lipNB_S (X := K1) hCA hKA hδ0 hδ1 hN hCBpos hCbigle hK1ge1 hK1pos.le hCb_2K1 hKB_2KA
        hCN3' hS'
    have hc7 : Cm * (1 + (N₀ : ℝ) / μ) ^ Km ≤ CB * δ⁻¹ ^ KB :=
      lipNB_claim7 hδ0 hδ1 hKA hKm hCm hBbpos (by positivity : (0 : ℝ) < 1 + (N₀ : ℝ) / μ)
        hCBpos hL hCb_Cm hKB_8'
    have hc8 : Cm * (1 + (N₀ : ℝ) / μ) ^ Km
          / (max 2 ((N : ℝ) * δ ^ KA / (128 * CA))) ^ P.natDegree
        ≤ CB * δ⁻¹ ^ KB / (N : ℝ) ^ P.natDegree :=
      lipNB_claim8 (d := P.natDegree) (Bb := Bb) (L := 1 + (N₀ : ℝ) / μ)
        hδ0 hδ1 hKA hKBpos hKm hCm hBbpos (by positivity : (0 : ℝ) < 1 + (N₀ : ℝ) / μ)
        hNpos hCA hCBpos hL hCbigle hCb_Cmd hKB_8
    have hc9 : (1 / (1 + Z)) * δ ^ (8 * KA * (1 + Km)) * (N : ℝ) ^ P.natDegree
        ≤ μ / (Cm * (1 + (N₀ : ℝ) / μ) ^ Km) := by
      have h := lipNB_claim9 (N := (N : ℝ)) (d := P.natDegree) (Bb := Bb)
        (L := 1 + (N₀ : ℝ) / μ) hδ0 hδ1 hKA hKm hCm hcμpos hBbpos
        (by positivity : (0 : ℝ) < 1 + (N₀ : ℝ) / μ) hNpos hμ hL
        (by simpa [hcμ] using hμlow)
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < Cm * (1 + (N₀ : ℝ) / μ) ^ Km)]
      simpa [hZ] using h
    exact ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9⟩

end Work.KMTAreas.A4
