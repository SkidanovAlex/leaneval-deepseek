import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseC3QAll.Est1.ComZarithb
import Submission.Work.BoseC3QAll.sum_W1sq_shift_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 4000000

namespace Work.BoseC3QAll.Est1

open Work.BoseB7 Work.BoseBox

/-- **`⟨Φ, G Φ⟩ ≥ 0`**: the PSD half of `Q3KernelFSAll.hatChiSq_form` with
`S = excited Mode`, `c = f_L`, `v s = ã_sΦ`. -/
theorem Gop_qw_nonneg' {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (K₀ : ℝ) (F : Work.BoseB7.FockData Mode) (T : Work.BoseC3QAll.TildeData F)
    (E : Work.BoseB7.Q3Env Mode) (hv : Work.BoseB7.FSParamsView E)
    (hK : Work.BoseC3QAll.Q3KernelFSAll K₀ F T E) (Φ : F.H) :
    0 ≤ F.qw Φ (T.Gop E) := by
  have hform := (hK.hatChiSq_form (excited Mode) E.fL (fun s => T.ta s Φ)
    (fun s hs h => h)).1
  have hleft : F.qw Φ (T.Gop E)
      = ∑ s ∈ excited Mode, ∑ s' ∈ excited Mode,
          E.fL s * E.fL s' * E.hatChiSq (s' - s) * F.bp (T.ta s' Φ) (T.ta s Φ) := by
    simp only [FockData.qw, Work.BoseB7A.TildeData.Gop, map_sum, LinearMap.sum_apply, map_smul,
      LinearMap.smul_apply, smul_eq_mul, LinearMap.comp_apply, bp_taDag_left]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun s' _ => ?_
    rw [F.bp_symm (T.ta s Φ) (T.ta s' Φ)]
  rw [hleft]; exact hform

/-- **The `χ̂²` half of FS `eq:EstimateQ3Tilde1`** (`eq:EstimT2comm`): the
`T₂,comm` sum is dominated by `2ρ_zŴ₁ω(0)⟨G Φ⟩`, the error bracket `C·e1A‖Φ‖²`,
the gap `(b/400)⟨gap Φ⟩` and a share `(𝓁²/8)` of the `P_H^q` kinetic reserve. -/
theorem estT2sum_comZ (K₀ b₀ : ℝ) (hb₀ : 0 < b₀) :
    ∃ C t₀ : ℝ, 0 ≤ C ∧ 0 < t₀ ∧
      ∀ {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
        (F : Work.BoseB7.FockData Mode) (T : Work.BoseC3QAll.TildeData F) (E : Work.BoseB7.Q3Env Mode)
        (hv : Work.BoseB7.FSParamsView E),
        hv.t ≤ t₀ → b₀ ≤ E.b → Work.BoseC3QAll.Q3KernelFSAll K₀ F T E →
        ∀ Φ : F.H, T.NWindow E.bigM Φ →
          ∑ k ∈ F.PHset E, (E.z / E.ell ^ 3) ^ 2 * (Work.BoseC3QAll.Est1.cD E k)⁻¹ *
              Work.BoseC3QAll.Est1.T2ComF F T E k Φ
            ≤ 2 * E.rho * E.W1omega0 * F.qw Φ (T.Gop E)
              + C * Work.BoseC3QAll.e1A E * F.normSq Φ
              + (E.b / 400) * F.qw Φ (T.gapOpT E)
              + (E.lille ^ 2 / 8) * F.qw Φ (F.dNumOpR E (F.PHq E.KH E.aScat)) := by
  obtain ⟨Car, tar, hCar, htar, har⟩ := comZ_arith K₀ b₀ hb₀
  obtain ⟨twc, htwc, hwc⟩ := wc_dev K₀ b₀ hb₀
  obtain ⟨tfa, htfa, hfa⟩ := FA_le_Q K₀ b₀ hb₀
  obtain ⟨tph, htph, hph⟩ := PH_subset_PHq_sub K₀ b₀ hb₀
  obtain ⟨tke, htke, hke⟩ := kernel_basic K₀ b₀ hb₀
  obtain ⟨tli, htli, hli⟩ := fsXp_le_of_pos_exp (A := 97) (c := 1 / 2) (by norm_num) (by norm_num)
  obtain ⟨tlk, htlk, hlk⟩ := lille_threshold K₀
  refine ⟨Car, min (min tar twc) (min tfa (min tph (min tke (min tli tlk)))), hCar,
    lt_min (lt_min htar htwc) (lt_min htfa (lt_min htph (lt_min htke (lt_min htli htlk)))), ?_⟩
  intro Mode _ _ _ F T E hv hle hb hK Φ hΦ
  have hleAr : hv.t ≤ tar := le_trans hle (le_trans (min_le_left _ _) (min_le_left _ _))
  have hleWc : hv.t ≤ twc := le_trans hle (le_trans (min_le_left _ _) (min_le_right _ _))
  have hleFa : hv.t ≤ tfa := le_trans hle (le_trans (min_le_right _ _) (min_le_left _ _))
  have hlePh : hv.t ≤ tph := le_trans hle (le_trans (min_le_right _ _)
    (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hleKe : hv.t ≤ tke := le_trans hle (le_trans (min_le_right _ _)
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))))
  have hleLi : hv.t ≤ tli := le_trans hle (le_trans (min_le_right _ _)
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (min_le_left _ _)))))
  have hleLk : hv.t ≤ tlk := le_trans hle (le_trans (min_le_right _ _)
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (min_le_right _ _)))))
  obtain ⟨hPHsub, hPHqsub, -⟩ := hph F T E hv hlePh hb hK
  obtain ⟨-, -, -, hαle, hDge⟩ := hke F T E hv hleKe hb hK
  have hηpos : 0 < eta E := eta_pos hv
  have hlil2 : E.lille ^ 2 ≤ 1 / 2 := by
    rw [lille_sq hv]; exact hli hv.t hv.t_pos hleLi
  have hk0 : 0 ≤ K₀ := K₀_nonneg_of_kernel K₀ F T E hv hK
  have hbpos : 0 < E.b := lt_of_lt_of_le hb₀ hb
  have hK1 : 0 ≤ K₀ + 1 := by linarith
  have hKHpos : 0 < E.KH := KH_pos E hv
  have hbm0 : 0 ≤ bm K₀ E := bm_nonneg hk0
  have hlile : 0 ≤ E.lille := le_of_lt (lille_pos E hv)
  have h96 : 96 * max K₀ 0 * E.lille ≤ 1 := hlk E hv hleLk
  have hKmax : K₀ ≤ max K₀ 0 := le_max_left _ _
  have hDne : ∀ k ∈ F.PHset E, E.D k ≠ 0 := by
    intro k hk
    have hkPH : F.PH E.KH E.aScat k := (Finset.mem_filter.mp hk).2
    have hqk : F.PHq E.KH E.aScat k := hPHsub k hkPH
    have h1 : ‖F.kmom k‖ ^ 2 / 4 ≤ E.D k := hDge k hqk
    have h2 : 0 < 1 / (4 * E.KH * E.aScat) := by
      have h3 : (0 : ℝ) < E.KH := hKHpos
      have h4 : (0 : ℝ) < E.aScat := hv.a_pos
      positivity
    have h5 : 0 < ‖F.kmom k‖ := lt_of_lt_of_le h2 hqk
    nlinarith
  have hposD : ∀ k ∈ F.PHset E, 0 < E.D k := by
    intro k hk
    have hkPH : F.PH E.KH E.aScat k := (Finset.mem_filter.mp hk).2
    have hqk : F.PHq E.KH E.aScat k := hPHsub k hkPH
    have h1 : ‖F.kmom k‖ ^ 2 / 4 ≤ E.D k := hDge k hqk
    have h2 : 0 < 1 / (4 * E.KH * E.aScat) := by
      have h3 : (0 : ℝ) < E.KH := hKHpos
      have h4 : (0 : ℝ) < E.aScat := hv.a_pos
      positivity
    have h5 : 0 < ‖F.kmom k‖ := lt_of_lt_of_le h2 hqk
    nlinarith
  have hℓ : 0 < E.ell := ell_pos E hv
  have hdev : ∀ k, k ∈ F.PHset E → E.W1 k ≠ 0 → ∀ s s', E.fL s ≠ 0 → E.fL s' ≠ 0 →
      |wc E k s s' - 1| ≤ devc K₀ E :=
    fun k hk hW s s' h0 h0' => hwc F T E hv hleWc hb hK k s s' hk h0 h0' hW
  have hχ : ∀ k ∈ F.PHset E, E.W1 k ≠ 0 → ∀ s, E.fL s ≠ 0 →
      |E.hatChi (s - k)| ≤ K₀ * eta E :=
    fun k hk hW s hfs => hK.hatChi_small (s - k) (hPHqsub s k hfs hk hW)
  have hFA : ∀ k ∈ F.PHset E, E.W1 k ≠ 0 → FA F T E k Φ ≤ F.qw Φ (T.Gop E)
      + cbeta K₀ E * (F.bp (T.N Φ) Φ + NPL E * F.normSq Φ) :=
    fun k hk hW => hfa F T E hv hleFa hb hK k Φ hk hW
  have hbmk : ∀ k ∈ F.PHset E, E.W1 k ≠ 0 → ∀ s, E.fL s ≠ 0 → |bA E s k| ≤ bm K₀ E := by
    intro k hk hW s hfs
    have hkPH : F.PH E.KH E.aScat k := (Finset.mem_filter.mp hk).2
    have hqk : F.PHq E.KH E.aScat k := hPHsub k hkPH
    have hqsk : F.PHq E.KH E.aScat (s - k) := hPHqsub s k hfs hk hW
    have h1 := hαle k hqk
    have h2 := hαle (s - k) hqsk
    rw [bA, abs_mul]
    have hb1 : 64 * K₀ * E.lille ≤ 2 / 3 := by nlinarith
    have hb2 : 0 ≤ 64 * K₀ * E.lille := by positivity
    calc |E.alpha k| * |E.alpha (s - k)| ≤ (64 * K₀ * E.lille) * (64 * K₀ * E.lille) :=
          mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
      _ ≤ 2 ^ 12 * K₀ ^ 2 * E.lille ^ 2 := by nlinarith [sq_nonneg E.lille, hk0, hlile]
      _ = bm K₀ E := by rw [bm, lille_sq hv]
  have hwgt0 : ∀ k ∈ F.PHset E, 0 ≤ wgt E k := by
    intro k hk
    rw [wgt, cD]
    have h2 : 0 < 1 - E.lille ^ 2 := by linarith
    have h3 : 0 < (1 - E.lille ^ 2) * E.D k := mul_pos h2 (hposD k hk)
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (le_of_lt (inv_pos.mpr h3))) (sq_nonneg _)
  have hwgt_zero : ∀ k, E.W1 k = 0 → wgt E k = 0 := by
    intro k h0
    rw [wgt, show E.W1 k ^ 2 = 0 by rw [h0]; norm_num, mul_zero]
  have hRA : ∀ k ∈ F.PHset E, E.W1 k ≠ 0 → rawA F T E k Φ - rawY F T E k Φ
      ≤ FA F T E k Φ + erm K₀ E * AbsA0 F T E k Φ := by
    intro k hk hW
    have h1 := rawA_sub_FA_le (K₀ := K₀) hK k Φ (devc_nonneg hk0) (hdev k hk hW)
    have h2 := rawY_bound (K₀ := K₀) hK k Φ hk0 (le_of_lt hηpos) (devc_nonneg hk0)
      (hχ k hk hW) (hdev k hk hW)
    rw [erm]; linarith
  have hΛle : wsum F E ≤ LamBound K₀ E := wsum_le hv hK hℓ hlil2 hDne
  have hAbs : ∀ k ∈ F.PHset E, E.W1 k ≠ 0 → AbsA0 F T E k Φ
      ≤ NPL E * ((1 + 2 * bm K₀ E + bm K₀ E ^ 2) * (F.bp (T.N Φ) Φ)
          + (bm K₀ E + bm K₀ E ^ 2) * (NPL E * F.normSq Φ)) := by
    intro k hk hW
    have h1 : AbsA0 F T E k Φ ≤ (∑ s ∈ excited Mode, E.fL s)
        * (∑ s ∈ excited Mode, E.fL s
            * F.bp (Atil F T E s k Φ) (Atil F T E s k Φ)) := AbsA0_le hK k Φ
    have h2 : (∑ s ∈ excited Mode, E.fL s) ≤ NPL E := sum_fL_le_NPL hK
    have h3 : (∑ s ∈ excited Mode, E.fL s
          * F.bp (Atil F T E s k Φ) (Atil F T E s k Φ))
        ≤ (1 + bm K₀ E) * TA F T E Φ + (bm K₀ E + bm K₀ E ^ 2) * TB F T E Φ :=
      sum_Atil_sq_le hK k Φ (hbmk k hk hW)
    have h4 : TA F T E Φ ≤ F.bp (T.N Φ) Φ := TA_le_N hK Φ
    have h5 : TB F T E Φ ≤ TA F T E Φ + NPL E * F.normSq Φ := TB_le hK Φ
    have h6 : 0 ≤ TB F T E Φ :=
      Finset.sum_nonneg fun s _ => mul_nonneg (hK.fL_nonneg s) (F.bp_nonneg _)
    have h7 : 0 ≤ TA F T E Φ :=
      Finset.sum_nonneg fun s _ => mul_nonneg (hK.fL_nonneg s) (F.bp_nonneg _)
    have h8 : 0 ≤ (∑ s ∈ excited Mode, E.fL s
          * F.bp (Atil F T E s k Φ) (Atil F T E s k Φ)) :=
      Finset.sum_nonneg fun s _ =>
        mul_nonneg (hK.fL_nonneg s) (F.bp_nonneg _)
    have hbm0 : 0 ≤ bm K₀ E := bm_nonneg hk0
    have hNAP0 : 0 ≤ F.bp (T.N Φ) Φ := T.N_nonneg Φ
    have hNS0 : 0 ≤ F.normSq Φ := F.bp_nonneg _
    have hNPL0 : 0 ≤ NPL E := NPL_nonneg E
    have hsumTB : (bm K₀ E + bm K₀ E ^ 2) * TB F T E Φ
        ≤ (bm K₀ E + bm K₀ E ^ 2) * (F.bp (T.N Φ) Φ + NPL E * F.normSq Φ) := by
      refine mul_le_mul_of_nonneg_left ?_ (by nlinarith [hbm0, sq_nonneg (bm K₀ E)])
      linarith [h4, h5]
    have hkey : (1 + bm K₀ E) * TA F T E Φ + (bm K₀ E + bm K₀ E ^ 2) * TB F T E Φ
        ≤ (1 + 2 * bm K₀ E + bm K₀ E ^ 2) * (F.bp (T.N Φ) Φ)
          + (bm K₀ E + bm K₀ E ^ 2) * (NPL E * F.normSq Φ) := by
      have e1 : (1 + bm K₀ E) * TA F T E Φ ≤ (1 + bm K₀ E) * F.bp (T.N Φ) Φ :=
        mul_le_mul_of_nonneg_left h4 (by linarith)
      linarith [e1, hsumTB, hbm0, hNAP0, hNS0, hNPL0]
    calc AbsA0 F T E k Φ ≤ (∑ s ∈ excited Mode, E.fL s)
          * (∑ s ∈ excited Mode, E.fL s
              * F.bp (Atil F T E s k Φ) (Atil F T E s k Φ)) := h1
      _ ≤ NPL E * ((1 + bm K₀ E) * TA F T E Φ + (bm K₀ E + bm K₀ E ^ 2) * TB F T E Φ) :=
          mul_le_mul h2 h3 h8 hNPL0
      _ ≤ NPL E * ((1 + 2 * bm K₀ E + bm K₀ E ^ 2) * (F.bp (T.N Φ) Φ)
            + (bm K₀ E + bm K₀ E ^ 2) * (NPL E * F.normSq Φ)) :=
          mul_le_mul_of_nonneg_left hkey hNPL0
  -- abbreviation bundle
  have herm0 : 0 ≤ erm K₀ E := by
    rw [erm]
    exact add_nonneg (devc_nonneg hk0)
      (mul_nonneg (add_nonneg zero_le_one (devc_nonneg hk0))
        (mul_nonneg (sq_nonneg K₀) (sq_nonneg _)))
  have hcb0 : 0 ≤ cbeta K₀ E := by
    rw [cbeta]
    exact mul_nonneg hK1 (by linarith [hbm0, sq_nonneg (bm K₀ E)])
  have hLm0 : 0 ≤ LamBound K₀ E := by
    rw [LamBound]
    have h1 : 0 ≤ E.W1omega0 + K₀ * E.aScat * E.KH⁻¹ :=
      add_nonneg hK.W1omega0_nonneg (mul_nonneg (mul_nonneg hk0 hv.a_pos.le)
        (inv_nonneg.mpr hKHpos.le))
    exact mul_nonneg (mul_nonneg (by linarith [Work.BoseB7.rho_pos E hv]) h1)
      (by nlinarith [sq_nonneg E.lille])
  have hNPL0 : 0 ≤ NPL E := NPL_nonneg E
  have hNS0 : 0 ≤ F.normSq Φ := F.bp_nonneg _
  have hNAP0 : 0 ≤ F.bp (T.N Φ) Φ := T.N_nonneg Φ
  -- the two sum bounds
  have hsum1 : ∑ k ∈ F.PHset E, (E.z / E.ell ^ 3) ^ 2 * (cD E k)⁻¹ * T2ComF F T E k Φ
      ≤ ∑ k ∈ F.PHset E, wgt E k * (FA F T E k Φ + erm K₀ E * AbsA0 F T E k Φ) := by
    refine Finset.sum_le_sum fun k hk => ?_
    have h1 : (E.z / E.ell ^ 3) ^ 2 * (cD E k)⁻¹ * T2ComF F T E k Φ
        = wgt E k * (rawA F T E k Φ - rawY F T E k Φ) := by
      rw [t2com_split hK k hk Φ, wgt]; ring
    rw [h1]
    by_cases hW : E.W1 k = 0
    · rw [hwgt_zero k hW, zero_mul, zero_mul]
    · exact mul_le_mul_of_nonneg_left (hRA k hk hW) (hwgt0 k hk)
  have hsumFA : ∑ k ∈ F.PHset E, wgt E k * FA F T E k Φ
      ≤ LamBound K₀ E * (F.qw Φ (T.Gop E)
          + cbeta K₀ E * (F.bp (T.N Φ) Φ + NPL E * F.normSq Φ)) := by
    have hQnn : 0 ≤ F.qw Φ (T.Gop E) + cbeta K₀ E
        * (F.bp (T.N Φ) Φ + NPL E * F.normSq Φ) :=
      add_nonneg (Gop_qw_nonneg' K₀ F T E hv hK Φ)
        (mul_nonneg hcb0 (add_nonneg hNAP0 (mul_nonneg hNPL0 hNS0)))
    calc ∑ k ∈ F.PHset E, wgt E k * FA F T E k Φ
        ≤ ∑ k ∈ F.PHset E, wgt E k *
            (F.qw Φ (T.Gop E) + cbeta K₀ E * (F.bp (T.N Φ) Φ + NPL E * F.normSq Φ)) :=
          Finset.sum_le_sum fun k hk => by
            by_cases hW : E.W1 k = 0
            · rw [hwgt_zero k hW, zero_mul, zero_mul]
            · exact mul_le_mul_of_nonneg_left (hFA k hk hW) (hwgt0 k hk)
      _ = wsum F E * (F.qw Φ (T.Gop E)
            + cbeta K₀ E * (F.bp (T.N Φ) Φ + NPL E * F.normSq Φ)) := by
          rw [wsum, Finset.sum_mul]
      _ ≤ LamBound K₀ E * (F.qw Φ (T.Gop E)
            + cbeta K₀ E * (F.bp (T.N Φ) Φ + NPL E * F.normSq Φ)) :=
          mul_le_mul_of_nonneg_right hΛle hQnn
  have hAbsB : 0 ≤ NPL E * ((1 + 2 * bm K₀ E + bm K₀ E ^ 2) * (F.bp (T.N Φ) Φ)
      + (bm K₀ E + bm K₀ E ^ 2) * (NPL E * F.normSq Φ)) :=
    mul_nonneg hNPL0 (add_nonneg (mul_nonneg (by positivity) hNAP0)
      (mul_nonneg (by positivity) (mul_nonneg hNPL0 hNS0)))
  have hsumAbs : ∑ k ∈ F.PHset E, wgt E k * AbsA0 F T E k Φ
      ≤ LamBound K₀ E * (NPL E * ((1 + 2 * bm K₀ E + bm K₀ E ^ 2) * (F.bp (T.N Φ) Φ)
          + (bm K₀ E + bm K₀ E ^ 2) * (NPL E * F.normSq Φ))) := by
    calc ∑ k ∈ F.PHset E, wgt E k * AbsA0 F T E k Φ
        ≤ ∑ k ∈ F.PHset E, wgt E k * (NPL E * ((1 + 2 * bm K₀ E + bm K₀ E ^ 2)
            * (F.bp (T.N Φ) Φ) + (bm K₀ E + bm K₀ E ^ 2) * (NPL E * F.normSq Φ))) :=
          Finset.sum_le_sum fun k hk => by
            by_cases hW : E.W1 k = 0
            · rw [hwgt_zero k hW, zero_mul, zero_mul]
            · exact mul_le_mul_of_nonneg_left (hAbs k hk hW) (hwgt0 k hk)
      _ = wsum F E * (NPL E * ((1 + 2 * bm K₀ E + bm K₀ E ^ 2) * (F.bp (T.N Φ) Φ)
            + (bm K₀ E + bm K₀ E ^ 2) * (NPL E * F.normSq Φ))) := by
          rw [wsum, Finset.sum_mul]
      _ ≤ LamBound K₀ E * (NPL E * ((1 + 2 * bm K₀ E + bm K₀ E ^ 2) * (F.bp (T.N Φ) Φ)
            + (bm K₀ E + bm K₀ E ^ 2) * (NPL E * F.normSq Φ))) :=
          mul_le_mul_of_nonneg_right hΛle hAbsB
  have hsum2 : ∑ k ∈ F.PHset E, wgt E k * (FA F T E k Φ + erm K₀ E * AbsA0 F T E k Φ)
      ≤ LamBound K₀ E * (F.qw Φ (T.Gop E)
          + cbeta K₀ E * (F.bp (T.N Φ) Φ + NPL E * F.normSq Φ))
        + erm K₀ E * (LamBound K₀ E
          * (NPL E * ((1 + 2 * bm K₀ E + bm K₀ E ^ 2) * (F.bp (T.N Φ) Φ)
            + (bm K₀ E + bm K₀ E ^ 2) * (NPL E * F.normSq Φ)))) := by
    rw [Finset.sum_congr rfl (fun k _ => by ring :
      ∀ k ∈ F.PHset E, wgt E k * (FA F T E k Φ + erm K₀ E * AbsA0 F T E k Φ)
        = wgt E k * FA F T E k Φ + erm K₀ E * (wgt E k * AbsA0 F T E k Φ))]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    exact add_le_add hsumFA (mul_le_mul_of_nonneg_left hsumAbs herm0)
  -- the deficit
  have hKA2 : 0 ≤ K₀ * E.aScat := mul_nonneg hk0 hv.a_pos.le
  have hKH1 : E.KH⁻¹ ≤ 1 := by
    rw [KHinv_val hv]; exact fsXp_le_one hv.t_pos hv.t_le_one (by norm_num)
  have hKH0 : 0 ≤ E.KH⁻¹ := inv_nonneg.mpr hKHpos.le
  have hW1 : E.W1omega0 ≤ K₀ * E.aScat := hK.W1omega0_le
  have hW10 : 0 ≤ E.W1omega0 := hK.W1omega0_nonneg
  have hLamD : LamBound K₀ E - 2 * E.rho * E.W1omega0 ≤ dlt K₀ E := by
    have hρ0 : 0 ≤ E.rho := le_of_lt (Work.BoseB7.rho_pos E hv)
    have hlil0 : 0 ≤ E.lille ^ 2 := sq_nonneg _
    rw [LamBound, dlt]
    calc 2 * E.rho * (E.W1omega0 + K₀ * E.aScat * E.KH⁻¹) * (1 + 2 * E.lille ^ 2)
          - 2 * E.rho * E.W1omega0
        = 2 * E.rho * (2 * E.lille ^ 2 * E.W1omega0
            + K₀ * E.aScat * E.KH⁻¹ * (1 + 2 * E.lille ^ 2)) := by ring
      _ ≤ 2 * E.rho * (4 * (K₀ * E.aScat) * E.lille ^ 2 + 4 * (K₀ * E.aScat * E.KH⁻¹)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by linarith)
          have e1 : 2 * E.lille ^ 2 * E.W1omega0 ≤ 2 * E.lille ^ 2 * (K₀ * E.aScat) :=
            mul_le_mul_of_nonneg_left hW1 (by linarith [hlil0])
          have e2 : K₀ * E.aScat * E.KH⁻¹ * (1 + 2 * E.lille ^ 2)
              ≤ 2 * (K₀ * E.aScat * E.KH⁻¹) := by
            have h := mul_le_mul_of_nonneg_left (by linarith [hlil2] :
              (1 : ℝ) + 2 * E.lille ^ 2 ≤ 2) (mul_nonneg hKA2 hKH0)
            linarith [h]
          have he1 : 2 * E.lille ^ 2 * E.W1omega0 ≤ 4 * (K₀ * E.aScat) * E.lille ^ 2 := by
            nlinarith [e1]
          have he2 : K₀ * E.aScat * E.KH⁻¹ * (1 + 2 * E.lille ^ 2)
              ≤ 4 * (K₀ * E.aScat * E.KH⁻¹) := by nlinarith [e2]
          linarith [he1, he2]
      _ ≤ 8 * E.rho * K₀ * E.aScat * (E.lille ^ 2 + E.KH⁻¹) := by
          have h : 2 * E.rho * (4 * (K₀ * E.aScat) * E.lille ^ 2
              + 4 * (K₀ * E.aScat * E.KH⁻¹))
              = 8 * E.rho * K₀ * E.aScat * (E.lille ^ 2 + E.KH⁻¹) := by ring
          exact le_of_eq h
  have hdlt0 : 0 ≤ dlt K₀ E := by
    rw [dlt]
    have hρ0 : 0 ≤ E.rho := le_of_lt (Work.BoseB7.rho_pos E hv)
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hρ0) hk0)
      hv.a_pos.le) (by linarith [sq_nonneg E.lille, hKH0])
  have hQle : F.qw Φ (T.Gop E) ≤ K₀ * F.bp (T.N Φ) Φ := Gop_qw_le K₀ F T E hv hK Φ
  -- the two scalar conclusions of `comZ_arith`
  have har' := har F T E hv hleAr hb hK
  have hAnum : dlt K₀ E * K₀ + LamBound K₀ E * cbeta K₀ E
      + erm K₀ E * LamBound K₀ E * NPL E * (1 + 2 * bm K₀ E + bm K₀ E ^ 2)
      ≤ (E.b / 400) * (E.ell ^ 2)⁻¹ := har'.1
  have hBnum : LamBound K₀ E * cbeta K₀ E * NPL E
      + erm K₀ E * LamBound K₀ E * (bm K₀ E + bm K₀ E ^ 2) * NPL E ^ 2
      ≤ Car * e1A E := har'.2
  -- ## the final chain
  have hgap : (E.ell ^ 2)⁻¹ * F.bp (T.N Φ) Φ ≤ F.qw Φ (T.gapOpT E) := by
    rw [FockData.qw, Work.BoseB7A.TildeData.gapOpT]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    have h1 : 0 ≤ (E.eT * (E.d * E.ell) ^ (-(2 : ℝ))) * F.bp (T.NH Φ) Φ :=
      mul_nonneg (mul_nonneg (eT_nonneg E hv)
        (Real.rpow_nonneg (le_of_lt (mul_pos (by rw [hv.d_eq]; exact fsXp_pos hv.t_pos) hℓ)) _))
        (T.NH_nonneg Φ)
    have h2 : E.ell ^ (-(2 : ℝ)) = (E.ell ^ 2)⁻¹ := by
      rw [show (-(2:ℝ)) = -((2:ℕ):ℝ) by norm_num, Real.rpow_neg (le_of_lt hℓ),
        Real.rpow_natCast]
    rw [h2]
    linarith
  have hLHS : ∑ k ∈ F.PHset E, (E.z / E.ell ^ 3) ^ 2 * (cD E k)⁻¹ * T2ComF F T E k Φ
      ≤ 2 * E.rho * E.W1omega0 * F.qw Φ (T.Gop E)
        + (dlt K₀ E * K₀
            + LamBound K₀ E * cbeta K₀ E
            + erm K₀ E * LamBound K₀ E * NPL E * (1 + 2 * bm K₀ E + bm K₀ E ^ 2))
          * F.bp (T.N Φ) Φ
        + (LamBound K₀ E * cbeta K₀ E * NPL E
            + erm K₀ E * LamBound K₀ E * (bm K₀ E + bm K₀ E ^ 2) * NPL E ^ 2)
          * F.normSq Φ := by
    have hQbound : LamBound K₀ E * F.qw Φ (T.Gop E)
        ≤ 2 * E.rho * E.W1omega0 * F.qw Φ (T.Gop E) + dlt K₀ E * K₀ * F.bp (T.N Φ) Φ := by
      have hLD : LamBound K₀ E ≤ 2 * E.rho * E.W1omega0 + dlt K₀ E := by linarith [hLamD]
      have hA0 : 0 ≤ 2 * E.rho * E.W1omega0 + dlt K₀ E := le_trans hLm0 hLD
      calc LamBound K₀ E * F.qw Φ (T.Gop E)
          ≤ (2 * E.rho * E.W1omega0 + dlt K₀ E) * F.qw Φ (T.Gop E) :=
            mul_le_mul_of_nonneg_right hLD (Gop_qw_nonneg' K₀ F T E hv hK Φ)
        _ = 2 * E.rho * E.W1omega0 * F.qw Φ (T.Gop E)
              + dlt K₀ E * F.qw Φ (T.Gop E) := by ring
        _ ≤ 2 * E.rho * E.W1omega0 * F.qw Φ (T.Gop E)
              + dlt K₀ E * (K₀ * F.bp (T.N Φ) Φ) :=
            add_le_add le_rfl (mul_le_mul_of_nonneg_left hQle hdlt0)
        _ = 2 * E.rho * E.W1omega0 * F.qw Φ (T.Gop E) + dlt K₀ E * K₀ * F.bp (T.N Φ) Φ := by ring
    have hkey : LamBound K₀ E * (F.qw Φ (T.Gop E)
          + cbeta K₀ E * (F.bp (T.N Φ) Φ + NPL E * F.normSq Φ))
        + (erm K₀ E * LamBound K₀ E) * (NPL E * ((1 + 2 * bm K₀ E + bm K₀ E ^ 2)
            * (F.bp (T.N Φ) Φ) + (bm K₀ E + bm K₀ E ^ 2) * (NPL E * F.normSq Φ)))
        = LamBound K₀ E * F.qw Φ (T.Gop E)
          + (LamBound K₀ E * cbeta K₀ E
              + erm K₀ E * LamBound K₀ E * NPL E * (1 + 2 * bm K₀ E + bm K₀ E ^ 2))
            * F.bp (T.N Φ) Φ
          + (LamBound K₀ E * cbeta K₀ E * NPL E
              + erm K₀ E * LamBound K₀ E * (bm K₀ E + bm K₀ E ^ 2) * NPL E ^ 2)
            * F.normSq Φ := by ring
    have hmain : ∑ k ∈ F.PHset E, wgt E k * (FA F T E k Φ + erm K₀ E * AbsA0 F T E k Φ)
        ≤ LamBound K₀ E * F.qw Φ (T.Gop E)
          + (LamBound K₀ E * cbeta K₀ E
              + erm K₀ E * LamBound K₀ E * NPL E * (1 + 2 * bm K₀ E + bm K₀ E ^ 2))
            * F.bp (T.N Φ) Φ
          + (LamBound K₀ E * cbeta K₀ E * NPL E
              + erm K₀ E * LamBound K₀ E * (bm K₀ E + bm K₀ E ^ 2) * NPL E ^ 2)
            * F.normSq Φ := by
      refine le_trans hsum2 (le_of_eq ?_)
      ring
    calc ∑ k ∈ F.PHset E, (E.z / E.ell ^ 3) ^ 2 * (cD E k)⁻¹ * T2ComF F T E k Φ
        ≤ ∑ k ∈ F.PHset E, wgt E k * (FA F T E k Φ + erm K₀ E * AbsA0 F T E k Φ) := hsum1
      _ ≤ LamBound K₀ E * F.qw Φ (T.Gop E)
          + (LamBound K₀ E * cbeta K₀ E
              + erm K₀ E * LamBound K₀ E * NPL E * (1 + 2 * bm K₀ E + bm K₀ E ^ 2))
            * F.bp (T.N Φ) Φ
          + (LamBound K₀ E * cbeta K₀ E * NPL E
              + erm K₀ E * LamBound K₀ E * (bm K₀ E + bm K₀ E ^ 2) * NPL E ^ 2)
            * F.normSq Φ := hmain
      _ ≤ 2 * E.rho * E.W1omega0 * F.qw Φ (T.Gop E)
          + (dlt K₀ E * K₀ + LamBound K₀ E * cbeta K₀ E
              + erm K₀ E * LamBound K₀ E * NPL E * (1 + 2 * bm K₀ E + bm K₀ E ^ 2))
            * F.bp (T.N Φ) Φ
          + (LamBound K₀ E * cbeta K₀ E * NPL E
              + erm K₀ E * LamBound K₀ E * (bm K₀ E + bm K₀ E ^ 2) * NPL E ^ 2)
            * F.normSq Φ := by
          linarith [hQbound]
  calc ∑ k ∈ F.PHset E, (E.z / E.ell ^ 3) ^ 2 * (cD E k)⁻¹ * T2ComF F T E k Φ
      ≤ 2 * E.rho * E.W1omega0 * F.qw Φ (T.Gop E)
        + (dlt K₀ E * K₀ + LamBound K₀ E * cbeta K₀ E
            + erm K₀ E * LamBound K₀ E * NPL E * (1 + 2 * bm K₀ E + bm K₀ E ^ 2))
          * F.bp (T.N Φ) Φ
        + (LamBound K₀ E * cbeta K₀ E * NPL E
            + erm K₀ E * LamBound K₀ E * (bm K₀ E + bm K₀ E ^ 2) * NPL E ^ 2)
          * F.normSq Φ := hLHS
    _ ≤ 2 * E.rho * E.W1omega0 * F.qw Φ (T.Gop E)
        + ((E.b / 400) * (E.ell ^ 2)⁻¹) * F.bp (T.N Φ) Φ
        + (Car * e1A E) * F.normSq Φ := by
        have h1 : (dlt K₀ E * K₀ + LamBound K₀ E * cbeta K₀ E
              + erm K₀ E * LamBound K₀ E * NPL E * (1 + 2 * bm K₀ E + bm K₀ E ^ 2))
              * F.bp (T.N Φ) Φ
            ≤ ((E.b / 400) * (E.ell ^ 2)⁻¹) * F.bp (T.N Φ) Φ :=
          mul_le_mul_of_nonneg_right hAnum hNAP0
        have h2 : (LamBound K₀ E * cbeta K₀ E * NPL E
              + erm K₀ E * LamBound K₀ E * (bm K₀ E + bm K₀ E ^ 2) * NPL E ^ 2)
              * F.normSq Φ ≤ (Car * e1A E) * F.normSq Φ :=
          mul_le_mul_of_nonneg_right hBnum hNS0
        linarith [h1, h2]
    _ ≤ 2 * E.rho * E.W1omega0 * F.qw Φ (T.Gop E)
        + (E.b / 400) * F.qw Φ (T.gapOpT E)
        + Car * e1A E * F.normSq Φ := by
        have h1 : ((E.b / 400) * (E.ell ^ 2)⁻¹) * F.bp (T.N Φ) Φ
            ≤ (E.b / 400) * F.qw Φ (T.gapOpT E) := by
          have hb0 : 0 ≤ E.b / 400 := by linarith
          calc ((E.b / 400) * (E.ell ^ 2)⁻¹) * F.bp (T.N Φ) Φ
              = (E.b / 400) * ((E.ell ^ 2)⁻¹ * F.bp (T.N Φ) Φ) := by ring
            _ ≤ (E.b / 400) * F.qw Φ (T.gapOpT E) := mul_le_mul_of_nonneg_left hgap hb0
        linarith [h1]
    _ ≤ 2 * E.rho * E.W1omega0 * F.qw Φ (T.Gop E)
        + Car * e1A E * F.normSq Φ
        + (E.b / 400) * F.qw Φ (T.gapOpT E)
        + (E.lille ^ 2 / 8) * F.qw Φ (F.dNumOpR E (F.PHq E.KH E.aScat)) := by
        have h1 : 0 ≤ (E.lille ^ 2 / 8) * F.qw Φ (F.dNumOpR E (F.PHq E.KH E.aScat)) := by
          refine mul_nonneg (by positivity) ?_
          simp only [FockData.qw, FockData.dNumOpR, FockData.regionSum, map_sum,
            LinearMap.sum_apply]
          refine Finset.sum_nonneg fun i hi => ?_
          simp only [LinearMap.smul_apply, map_smul, smul_eq_mul, FockData.bNumOp,
            LinearMap.comp_apply, bp_bOpDag_left]
          refine mul_nonneg ?_ (F.bp_nonneg _)
          have hiq : F.PHq E.KH E.aScat i := (Finset.mem_filter.mp hi).2
          have h5 : 0 < 1 / (4 * E.KH * E.aScat) := by
            have h3 : (0 : ℝ) < E.KH := hKHpos
            have h4 : (0 : ℝ) < E.aScat := hv.a_pos
            positivity
          have h6 : 0 < ‖F.kmom i‖ := lt_of_lt_of_le h5 hiq
          nlinarith [hDge i hiq]
        linarith [h1]

end Work.BoseC3QAll.Est1
