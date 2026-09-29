import Mathlib

namespace Work.TMContract.Gluing

open Set

open scoped ENNReal NNReal

lemma nnreal_norm_le {t : ℝ} {R : ℝ≥0} (h : |t| ≤ (R : ℝ)) : ‖t‖₊ ≤ R :=
  NNReal.coe_le_coe.mp (by simpa [Real.norm_eq_abs] using h)

theorem taylor_slice_alt {Φ : ℝ × ℝ → ℝ} {z : ℝ × ℝ} (h : AnalyticAt ℝ Φ z) :
    ∃ r > 0, ∃ C > 0, ∃ c : ℕ → ℝ → ℝ,
      (∀ m, ContinuousOn (c m) (Set.Icc (z.2 - r) (z.2 + r))) ∧
      (∀ m x, x ∈ Set.Icc (z.2 - r) (z.2 + r) → |c m x| ≤ C * (1 / r) ^ m) ∧
      (∀ h' x, |h'| < r → |x - z.2| < r →
        HasSum (fun m => c m x * h' ^ m) (Φ (z.1 + h', x))) := by
  obtain ⟨p, r₀, hp⟩ := h
  have hradpos : 0 < p.radius := lt_of_lt_of_le hp.r_pos hp.r_le
  obtain ⟨R₀, hR₀pos, hR₀lt⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hp.r_pos
  have hR₀pos' : 0 < R₀ := ENNReal.coe_pos.mp hR₀pos
  have hR₀rad : (R₀ : ℝ≥0∞) < p.radius := lt_of_lt_of_le hR₀lt hp.r_le
  set ρ : ℝ := (R₀ : ℝ) with hρdef
  have hρpos : 0 < ρ := by rw [hρdef]; exact_mod_cast hR₀pos'
  set r : ℝ := ρ / 8 with hrdef
  have hrpos : 0 < r := by rw [hrdef]; positivity
  have hrρ : r ≤ ρ := by rw [hrdef]; linarith
  obtain ⟨C₀, hC₀pos, hC₀⟩ := p.norm_le_div_pow_of_pos_of_lt_radius (r := R₀ / 2)
      (half_pos hR₀pos')
      (lt_of_lt_of_le (ENNReal.coe_lt_coe.mpr (half_lt_self hR₀pos')) (le_of_lt hR₀rad))
  have hC₀' : ∀ n, ‖p n‖ ≤ C₀ * (2 / ρ) ^ n := by
    intro n
    have h1 : ((R₀ / 2 : ℝ≥0) : ℝ) = ρ / 2 := by
      rw [NNReal.coe_div, NNReal.coe_ofNat, hρdef]
    have h2 := hC₀ n
    rw [h1] at h2
    calc ‖p n‖ ≤ C₀ / (ρ / 2) ^ n := h2
      _ = C₀ * (2 / ρ) ^ n := by
          rw [show (2 / ρ : ℝ) = (ρ / 2)⁻¹ by ring, inv_pow, div_eq_mul_inv]
  let cl : ℝ → ℝ := fun t => max (-r) (min r t)
  have hcl_id : ∀ t, |t| ≤ r → cl t = t := by
    intro t ht
    have h1 : t ≤ r := (abs_le.mp ht).2
    have h2 : -r ≤ t := (abs_le.mp ht).1
    simp only [cl, min_eq_right h1, max_eq_right h2]
  have hcl_abs : ∀ t, |cl t| ≤ r := by
    intro t
    rw [abs_le]
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  let c : ℕ → ℝ → ℝ := fun m x =>
    (p.changeOrigin ((0:ℝ), cl (x - z.2))) m (fun _ : Fin m => (((1:ℝ), (0:ℝ)) : ℝ × ℝ))
  have hcoeff_bnd : ∀ (y : ℝ × ℝ), ‖y‖ ≤ r → ∀ m,
      ‖(p.changeOrigin y) m‖ ≤ 2 * C₀ * (1 / r) ^ m := by
    intro y hy m
    have hyρ : ‖y‖ ≤ ρ / 8 := by rw [hrdef] at hy; exact hy
    have hterm : ∀ l, ‖(p.changeOriginSeries m l) (fun _ => y)‖ ≤
        C₀ * (4 / ρ) ^ m * (1 / 2) ^ l := by
      intro l
      have h1 : ‖(p.changeOriginSeries m l) (fun _ => y)‖₊ ≤
          (2 : ℝ≥0) ^ (m + l) * (‖p (m + l)‖₊ * ‖y‖₊ ^ l) := by
        refine (p.nnnorm_changeOriginSeries_apply_le_tsum m l y).trans ?_
        rw [tsum_fintype]
        calc ∑ s : {s : Finset (Fin (m + l)) // s.card = l}, ‖p (m + l)‖₊ * ‖y‖₊ ^ l
            = (Fintype.card {s : Finset (Fin (m + l)) // s.card = l}) •
                (‖p (m + l)‖₊ * ‖y‖₊ ^ l) := by
              simp
          _ = ((Fintype.card {s : Finset (Fin (m + l)) // s.card = l} : ℕ) : ℝ≥0) *
                (‖p (m + l)‖₊ * ‖y‖₊ ^ l) := by rw [nsmul_eq_mul]
          _ ≤ (2 : ℝ≥0) ^ (m + l) * (‖p (m + l)‖₊ * ‖y‖₊ ^ l) := by
              refine mul_le_mul_of_nonneg_right ?_ (by positivity)
              calc (Fintype.card {s : Finset (Fin (m + l)) // s.card = l} : ℝ≥0)
                  ≤ ((2 ^ (m + l) : ℕ) : ℝ≥0) :=
                    Nat.cast_le.mpr (le_trans (Fintype.card_subtype_le _)
                      (by rw [Fintype.card_finset, Fintype.card_fin]))
                _ = (2 : ℝ≥0) ^ (m + l) := by rw [Nat.cast_pow]; norm_num
      have h2 : ‖(p.changeOriginSeries m l) (fun _ => y)‖ ≤
          (2 : ℝ) ^ (m + l) * (‖p (m + l)‖ * ‖y‖ ^ l) := by
        have hh := NNReal.coe_le_coe.mpr h1
        push_cast at hh
        simpa using hh
      have h3 : ‖p (m + l)‖ ≤ C₀ * (2 / ρ) ^ (m + l) := hC₀' (m + l)
      calc ‖(p.changeOriginSeries m l) (fun _ => y)‖
          ≤ (2 : ℝ) ^ (m + l) * (‖p (m + l)‖ * ‖y‖ ^ l) := h2
        _ ≤ (2 : ℝ) ^ (m + l) * ((C₀ * (2 / ρ) ^ (m + l)) * (ρ / 8) ^ l) := by
            gcongr
        _ ≤ C₀ * (4 / ρ) ^ m * (1 / 2) ^ l := by
            have hb1 : (2:ℝ) * (2 / ρ) = 4 / ρ := by field_simp; ring
            have hb2 : (2:ℝ) * (2 / ρ) * (ρ / 8) = 1 / 2 := by field_simp; ring
            have hXY : (2:ℝ) ^ (m + l) * (2 / ρ) ^ (m + l) * (ρ / 8) ^ l
                = (4 / ρ) ^ m * (1 / 2) ^ l := by
              rw [← mul_pow, pow_add, mul_assoc, ← mul_pow, hb2, hb1]
            rw [show (2:ℝ) ^ (m + l) * ((C₀ * (2 / ρ) ^ (m + l)) * (ρ / 8) ^ l)
                  = C₀ * ((2:ℝ) ^ (m + l) * (2 / ρ) ^ (m + l) * (ρ / 8) ^ l) from by ring,
                hXY]
            exact le_of_eq (mul_assoc C₀ _ _).symm
    have hsumm : Summable (fun l : ℕ => C₀ * (4 / ρ) ^ m * (1 / 2) ^ l) :=
      Summable.mul_left _ (summable_geometric_of_norm_lt_one (by norm_num : ‖(1/2 : ℝ)‖ < 1))
    have hsumm2 : Summable (fun l : ℕ => ‖(p.changeOriginSeries m l) (fun _ => y)‖) :=
      Summable.of_nonneg_of_le (fun l => norm_nonneg _) hterm hsumm
    calc ‖(p.changeOrigin y) m‖
        = ‖∑' l, (p.changeOriginSeries m l) (fun _ => y)‖ := by
            rw [FormalMultilinearSeries.changeOrigin]; rfl
      _ ≤ ∑' l, ‖(p.changeOriginSeries m l) (fun _ => y)‖ := norm_tsum_le_tsum_norm hsumm2
      _ ≤ ∑' l, C₀ * (4 / ρ) ^ m * (1 / 2) ^ l :=
            Summable.tsum_le_tsum hterm hsumm2 hsumm
      _ = C₀ * (4 / ρ) ^ m * 2 := by
            rw [tsum_mul_left, tsum_geometric_of_norm_lt_one (by norm_num : ‖(1/2 : ℝ)‖ < 1)]
            norm_num
      _ ≤ 2 * C₀ * (1 / r) ^ m := by
            have hpow : (4 / ρ) ^ m ≤ (1 / r) ^ m := by
              apply pow_le_pow_left₀ (by positivity)
              rw [div_le_div_iff₀ (by positivity) hrpos]
              nlinarith [hrdef, hρpos]
            calc C₀ * (4 / ρ) ^ m * 2 = 2 * C₀ * (4 / ρ) ^ m := by ring
              _ ≤ 2 * C₀ * (1 / r) ^ m := mul_le_mul_of_nonneg_left hpow (by positivity)
  let rN : ℝ≥0 := NNReal.mk r (le_of_lt hrpos)
  have hrN : (rN : ℝ) = r := by simp [rN]
  have hcont : ∀ m, ContinuousOn (c m) (Set.Icc (z.2 - r) (z.2 + r)) := by
    intro m
    have h1 : ContinuousOn (fun y : ℝ × ℝ => (p.changeOrigin y) m)
        (Metric.eball 0 p.radius) :=
      (FormalMultilinearSeries.hasFPowerSeriesOnBall_changeOrigin p m hradpos).analyticOnNhd.continuousOn
    have h2 : Continuous (fun x : ℝ => (((0:ℝ), cl (x - z.2)) : ℝ × ℝ)) := by
      have hc : Continuous (fun x : ℝ => cl (x - z.2)) := by
        simp only [cl]; fun_prop
      exact continuous_const.prodMk hc
    have h3 : ∀ x : ℝ, (((0:ℝ), cl (x - z.2)) : ℝ × ℝ) ∈ Metric.eball 0 p.radius := by
      intro x
      have hw : ‖(((0:ℝ), cl (x - z.2)) : ℝ × ℝ)‖₊ ≤ R₀ := by
        rw [Prod.nnnorm_def]; simp only [nnnorm_zero]
        refine max_le zero_le ?_
        exact NNReal.coe_le_coe.mp (by rw [coe_nnnorm, ← hρdef]; exact le_trans (hcl_abs _) hrρ)
      rw [Metric.mem_eball, edist_zero_right, enorm_eq_nnnorm]
      exact lt_of_le_of_lt (ENNReal.coe_le_coe.mpr hw) hR₀rad
    have h4 : Continuous (fun x : ℝ => (p.changeOrigin ((0:ℝ), cl (x - z.2))) m) :=
      h1.comp_continuous h2 h3
    have h5 : Continuous (fun x : ℝ =>
        (p.changeOrigin ((0:ℝ), cl (x - z.2))) m (fun _ : Fin m => (((1:ℝ), (0:ℝ)) : ℝ × ℝ))) :=
      continuous_eval.comp (h4.prodMk continuous_const)
    simpa only [c] using h5.continuousOn
  have hbnd : ∀ m x, x ∈ Set.Icc (z.2 - r) (z.2 + r) → |c m x| ≤ 2 * C₀ * (1 / r) ^ m := by
    intro m x hx
    have hyr : ‖(((0:ℝ), cl (x - z.2)) : ℝ × ℝ)‖ ≤ r := by
      rw [Prod.norm_def]; simp only [norm_zero]
      exact max_le (le_of_lt hrpos) (hcl_abs _)
    have hkey : |c m x| ≤ ‖(p.changeOrigin ((0:ℝ), cl (x - z.2))) m‖ := by
      have h0 : c m x = (p.changeOrigin ((0:ℝ), cl (x - z.2))) m
          (fun _ : Fin m => (((1:ℝ), (0:ℝ)) : ℝ × ℝ)) := rfl
      rw [h0, ← Real.norm_eq_abs]
      exact (ContinuousMultilinearMap.le_opNorm _ _).trans_eq (by simp [Prod.norm_def])
    exact hkey.trans (hcoeff_bnd _ hyr m)
  have hexp : ∀ h' x, |h'| < r → |x - z.2| < r →
      HasSum (fun m => c m x * h' ^ m) (Φ (z.1 + h', x)) := by
    intro h' x hh' hx
    have hclx : cl (x - z.2) = x - z.2 := hcl_id _ (le_of_lt hx)
    set y : ℝ × ℝ := ((0:ℝ), cl (x - z.2)) with hydef
    have hyr : ‖y‖ ≤ r := by
      rw [hydef, Prod.norm_def]; simp only [norm_zero]
      exact max_le (le_of_lt hrpos) (hcl_abs _)
    have hyR : (↑‖y‖₊ : ℝ≥0∞) < r₀ := by
      have h1 : ‖y‖₊ ≤ R₀ := NNReal.coe_le_coe.mp
        (by rw [coe_nnnorm, ← hρdef]; exact le_trans hyr hrρ)
      exact lt_of_le_of_lt (ENNReal.coe_le_coe.mpr h1) hR₀lt
    have hps := hp.changeOrigin hyR
    have hmem : ((h', (0:ℝ)) : ℝ × ℝ) ∈ Metric.eball (0 : ℝ × ℝ) (r₀ - (↑‖y‖₊ : ℝ≥0∞)) := by
      have ha : ‖((h', (0:ℝ)) : ℝ × ℝ)‖₊ ≤ rN := by
        rw [Prod.nnnorm_def]; simp only [nnnorm_zero]
        exact max_le (nnreal_norm_le (by rw [hrN]; exact le_of_lt hh')) zero_le
      have hb : ‖y‖₊ ≤ rN := NNReal.coe_le_coe.mp (by rw [coe_nnnorm, hrN]; exact hyr)
      have h2r : rN + rN = NNReal.mk (2 * r) (by positivity) := by
        rw [← NNReal.coe_inj]
        simp only [NNReal.coe_add, hrN, NNReal.coe_mk]
        ring
      have hlt : NNReal.mk (2 * r) (by positivity) < R₀ := by
        rw [← NNReal.coe_lt_coe, NNReal.coe_mk, ← hρdef, hrdef]; linarith
      have h1 : ‖((h', (0:ℝ)) : ℝ × ℝ)‖₊ + ‖y‖₊ < R₀ := by
        have hsum : ‖((h', (0:ℝ)) : ℝ × ℝ)‖₊ + ‖y‖₊ ≤ NNReal.mk (2 * r) (by positivity) := by
          rw [← h2r]; exact add_le_add ha hb
        exact lt_of_le_of_lt hsum hlt
      rw [Metric.mem_eball, edist_zero_right, enorm_eq_nnnorm]
      have hble : (↑‖y‖₊ : ℝ≥0∞) ≤ r₀ := le_of_lt hyR
      have hle : (↑‖((h', (0:ℝ)) : ℝ × ℝ)‖₊ : ℝ≥0∞) ≤ r₀ - (↑‖y‖₊ : ℝ≥0∞) := by
        rw [ENNReal.le_sub_iff_add_le_right ENNReal.coe_ne_top hble]
        calc (↑‖((h', (0:ℝ)) : ℝ × ℝ)‖₊ : ℝ≥0∞) + (↑‖y‖₊ : ℝ≥0∞)
            = (↑(‖((h', (0:ℝ)) : ℝ × ℝ)‖₊ + ‖y‖₊) : ℝ≥0∞) := (ENNReal.coe_add _ _).symm
          _ ≤ ↑R₀ := ENNReal.coe_le_coe.mpr (le_of_lt h1)
          _ ≤ r₀ := le_of_lt hR₀lt
      refine lt_of_le_of_ne hle ?_
      intro hcon
      have h2 : (↑‖((h', (0:ℝ)) : ℝ × ℝ)‖₊ : ℝ≥0∞) + (↑‖y‖₊ : ℝ≥0∞) < r₀ := by
        rw [← ENNReal.coe_add]
        exact (ENNReal.coe_lt_coe.mpr h1).trans_le hR₀lt.le
      rw [hcon, tsub_add_cancel_of_le hble] at h2
      exact absurd h2 (lt_irrefl _)
    have hs := hps.hasSum hmem
    have hlim : (z + y) + ((h', (0:ℝ)) : ℝ × ℝ) = (z.1 + h', x) := by
      rw [hydef, hclx]
      ext <;> simp
    have hterm : ∀ m, (p.changeOrigin y) m (fun _ : Fin m => ((h':ℝ), (0:ℝ)))
        = (p.changeOrigin y) m (fun _ : Fin m => (((1:ℝ), (0:ℝ)) : ℝ × ℝ)) * h' ^ m := by
      intro m
      rw [show (fun _ : Fin m => ((h':ℝ), (0:ℝ)))
            = (fun i : Fin m => h' • (((1:ℝ), (0:ℝ)) : ℝ × ℝ)) from by
              funext i; rw [Prod.smul_mk]; simp,
          ContinuousMultilinearMap.map_smul_univ]
      simp [Finset.prod_const, smul_eq_mul, mul_comm]
    have hterms : (fun j => (p.changeOrigin y) j (fun _ : Fin j => ((h':ℝ), (0:ℝ))))
        = (fun m => (p.changeOrigin y) m (fun _ : Fin m => (((1:ℝ), (0:ℝ)) : ℝ × ℝ)) * h' ^ m) :=
      funext hterm
    rw [hterms, hlim] at hs
    simpa only [c, hydef] using hs
  exact ⟨r, hrpos, 2 * C₀, by positivity, c, hcont, hbnd, hexp⟩

end Work.TMContract.Gluing
