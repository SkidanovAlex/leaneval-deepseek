import Mathlib
import Submission.Work.HornSC.CellBoundaryJordan.grid_tour
import Submission.Work.HornSC.CellBoundaryJordan.grid_tour_basic
import Submission.Work.HornSC.CellBoundaryJordan.grid_tour_range
import Submission.Work.HornSC.CellBoundaryJordan.grid_tour_injective

namespace Work.HornSC.CellBoundaryJordan

open Set Filter

open scoped Topology

/-- The imaginary part of a unit step direction, scaled by `k > 0` and divided by `1 + εi`
(`ε > 0`), is nonzero. -/
private lemma im_unitStepDir_ne_zero_aux {k : ℕ} (hk : 0 < k) {ε : ℝ} (hε : 0 < ε)
    {p q : ℤ × ℤ} (h : IsUnitAdj p q) :
    ((k : ℂ) * (lpt q - lpt p) / (⟨1, ε⟩ : ℂ)).im ≠ 0 := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hden : (0 : ℝ) < 1 + ε ^ 2 := by positivity
  have hnorm : Complex.normSq (⟨1, ε⟩ : ℂ) = 1 + ε ^ 2 := by
    rw [Complex.normSq_apply]; simp; ring
  rcases h with h | h | h | h
  · have hd : lpt q - lpt p = 1 := by rw [h]; apply Complex.ext <;> simp [lpt]
    rw [hd, mul_one]
    have hval : ((k : ℂ) / (⟨1, ε⟩ : ℂ)).im = -(k * ε) / (1 + ε ^ 2) := by
      rw [Complex.div_im, ← Complex.ofReal_natCast k, hnorm]
      simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.one_re, Complex.one_im]
      ring
    rw [hval]
    exact div_ne_zero (neg_ne_zero.mpr (ne_of_gt (mul_pos hkR hε))) (ne_of_gt hden)
  · have hd : lpt q - lpt p = -1 := by rw [h]; apply Complex.ext <;> simp [lpt]
    rw [hd]
    have hval : ((k : ℂ) * (-1 : ℂ) / (⟨1, ε⟩ : ℂ)).im = (k * ε) / (1 + ε ^ 2) := by
      rw [Complex.div_im, ← Complex.ofReal_natCast k, hnorm]
      simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.neg_re, Complex.neg_im, Complex.one_re, Complex.one_im]
      ring
    rw [hval]
    exact div_ne_zero (ne_of_gt (mul_pos hkR hε)) (ne_of_gt hden)
  · have hd : lpt q - lpt p = Complex.I := by rw [h]; apply Complex.ext <;> simp [lpt]
    rw [hd]
    have hval : ((k : ℂ) * Complex.I / (⟨1, ε⟩ : ℂ)).im = (k : ℝ) / (1 + ε ^ 2) := by
      rw [Complex.div_im, ← Complex.ofReal_natCast k, hnorm]
      simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im]
      ring
    rw [hval]
    exact div_ne_zero (ne_of_gt hkR) (ne_of_gt hden)
  · have hd : lpt q - lpt p = -Complex.I := by rw [h]; apply Complex.ext <;> simp [lpt]
    rw [hd]
    have hval : ((k : ℂ) * (-Complex.I) / (⟨1, ε⟩ : ℂ)).im = -(k : ℝ) / (1 + ε ^ 2) := by
      rw [Complex.div_im, ← Complex.ofReal_natCast k, hnorm]
      simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im, Complex.one_re,
        Complex.one_im]
      ring
    rw [hval]
    exact div_ne_zero (neg_ne_zero.mpr (ne_of_gt hkR)) (ne_of_gt hden)

/-- The polygonal tour is affine on a neighbourhood of a parameter that lies strictly inside
its step interval. -/
private lemma tourOn_local_affine_aux {k : ℕ} (hk : 0 < k) (u : ℕ → ℤ × ℤ) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) (hleft : (edgeIdx k t : ℝ) < (k : ℝ) * t) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, |s - t| < δ →
      tourOn u k s - tourOn u k t =
        ((k : ℝ) * (s - t)) • (lpt (u (edgeIdx k t + 1)) - lpt (u (edgeIdx k t))) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hA : 0 < (k : ℝ) * t - (edgeIdx k t : ℝ) := sub_pos.mpr hleft
  have hB : 0 < (edgeIdx k t : ℝ) + 1 - (k : ℝ) * t := by
    have h := Nat.lt_floor_add_one ((k : ℝ) * t)
    show 0 < (⌊(k : ℝ) * t⌋₊ : ℝ) + 1 - (k : ℝ) * t
    linarith
  set m : ℝ := min ((k : ℝ) * t - (edgeIdx k t : ℝ))
    ((edgeIdx k t : ℝ) + 1 - (k : ℝ) * t) with hm
  have hmA : m ≤ (k : ℝ) * t - (edgeIdx k t : ℝ) := by rw [hm]; exact min_le_left _ _
  have hmB : m ≤ (edgeIdx k t : ℝ) + 1 - (k : ℝ) * t := by rw [hm]; exact min_le_right _ _
  have hmpos : 0 < m := by rw [hm]; exact lt_min hA hB
  refine ⟨m / ((k : ℝ) + 1), by positivity, ?_⟩
  intro s hs
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hkm : (k : ℝ) * (m / ((k : ℝ) + 1)) < m := by
    rw [mul_div_assoc', div_lt_iff₀ hk1]
    nlinarith
  have habs : |(k : ℝ) * s - (k : ℝ) * t| < m := by
    have h1 : (k : ℝ) * s - (k : ℝ) * t = (k : ℝ) * (s - t) := by ring
    rw [h1, abs_mul, abs_of_nonneg (le_of_lt hkR)]
    exact lt_trans (mul_lt_mul_of_pos_left hs hkR) hkm
  have hsj_gt : (edgeIdx k t : ℝ) < (k : ℝ) * s := by
    have h1 := (abs_lt.mp (lt_of_lt_of_le habs hmA)).1
    linarith
  have hsj_lt : (k : ℝ) * s < (edgeIdx k t : ℝ) + 1 := by
    have h1 := (abs_lt.mp (lt_of_lt_of_le habs hmB)).2
    linarith
  have hidx : edgeIdx k s = edgeIdx k t := by
    show ⌊(k : ℝ) * s⌋₊ = edgeIdx k t
    have hnn : (0 : ℝ) ≤ (k : ℝ) * s := by
      have hj0 : (0 : ℝ) ≤ (edgeIdx k t : ℝ) := by positivity
      linarith
    exact (Nat.floor_eq_iff hnn).mpr ⟨le_of_lt hsj_gt, hsj_lt⟩
  have hjk : edgeIdx k t < k := edgeIdx_lt hk ht0 ht1
  have hs0 : 0 ≤ s := by
    have hj0 : (0 : ℝ) ≤ (edgeIdx k t : ℝ) := Nat.cast_nonneg _
    nlinarith [hkR, hsj_gt, hj0]
  have hs1 : s < 1 := by
    have hjkR : ((edgeIdx k t : ℝ) + 1) ≤ (k : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt hjk
    nlinarith [hkR, hsj_lt, hjkR]
  have hts := tourOn_edge_form hk u ht0 ht1
  have hss := tourOn_edge_form hk u hs0 hs1
  rw [hss, hts, hidx]
  rw [add_sub_add_left_eq_sub, ← sub_smul]
  congr 1
  ring

theorem tour_crossing_strict {k : ℕ} (hk : 3 ≤ k) (u : ℕ → ℤ × ℤ)
    (hper : ∀ i, u (i + k) = u i)
    (hinj : ∀ i j, i < k → j < k → u i = u j → i = j)
    (hstep : ∀ i, i < k → IsUnitAdj (u i) (u (i + 1)))
    {a : ℂ} {ε : ℝ} (hε : 0 < ε) (ha : a ∉ cycleSet k u)
    (hgen : ∀ t : ℝ, 0 < t → ∀ m n : ℤ,
      a + (t : ℂ) * (⟨1, ε⟩ : ℂ) ≠ (m : ℂ) + (n : ℂ) * Complex.I)
    {Θ : ℝ → ℝ} (hΘc : Continuous Θ)
    (hΘrep : ∀ t : ℝ, 0 ≤ t → t < 1 →
      (tourOn u k t - a) / (⟨1, ε⟩ : ℂ) = ((‖(tourOn u k t - a) / (⟨1, ε⟩ : ℂ)‖ : ℝ) : ℂ) *
        Complex.exp ((Θ t : ℂ) * Complex.I))
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (htlvl : ∃ n : ℤ, Θ t = (n : ℝ) * (2 * Real.pi)) :
    ∃ δ : ℝ, 0 < δ ∧
      ((∀ s : ℝ, |s - t| < δ → s ≠ t → (Θ s - Θ t) * (s - t) > 0) ∨
       (∀ s : ℝ, |s - t| < δ → s ≠ t → (Θ s - Θ t) * (s - t) < 0)) := by
  have hk0 : 0 < k := by omega
  set W : ℂ := (⟨1, ε⟩ : ℂ) with hW
  have hWre : W.re = 1 := rfl
  have hWim : W.im = ε := rfl
  have hWne : W ≠ 0 := by
    intro h
    have h1 : W.re = (0 : ℂ).re := congrArg Complex.re h
    rw [hWre] at h1
    simp at h1
  set g : ℝ → ℂ := fun s => (tourOn u k s - a) / W with hg
  have hg_def : ∀ s, g s = (tourOn u k s - a) / W := fun s => rfl
  obtain ⟨n, hn⟩ := htlvl
  -- `tourOn u k t` lies on the cycle, hence differs from `a`
  have hmem : tourOn u k t ∈ cycleSet k u := tourOn_mem_cycleSet hk0 u ht0 (le_of_lt ht1)
  have htoura : tourOn u k t ≠ a := fun h => ha (h ▸ hmem)
  have hgt_ne : g t ≠ 0 := by
    rw [hg_def t]
    exact div_ne_zero (sub_ne_zero.mpr htoura) hWne
  set ρ : ℝ := ‖g t‖ with hρdef
  have hρpos : 0 < ρ := by rw [hρdef]; exact norm_pos_iff.mpr hgt_ne
  -- the exponential factor at `t` is `1`
  have hexp_t : Complex.exp ((Θ t : ℂ) * Complex.I) = 1 := by
    rw [hn]
    have hcast : ((((n : ℝ) * (2 * Real.pi)) : ℝ) : ℂ) * Complex.I
        = (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by push_cast; ring
    rw [hcast, Complex.exp_int_mul_two_pi_mul_I]
  have hgt : g t = ((ρ : ℝ) : ℂ) := by
    have hr := hΘrep t ht0 ht1
    rw [← hg_def t, ← hρdef] at hr
    rw [hr, hexp_t, mul_one]
  have hgtre : (g t).re = ρ := by rw [hgt]; simp
  have hgtim : (g t).im = 0 := by rw [hgt]; simp
  -- `tourOn u k t` is on the open ray, so it is not a lattice point
  have htour_ray : tourOn u k t = a + ((ρ : ℝ) : ℂ) * W := by
    have h1 : tourOn u k t - a = g t * W := by
      rw [hg_def t, div_mul_cancel₀ _ hWne]
    rw [(sub_eq_iff_eq_add').mp h1, hgt]
  have hnl : ∀ v : ℤ × ℤ, tourOn u k t ≠ lpt v := by
    intro v hv
    have h2 : a + ((ρ : ℝ) : ℂ) * W = (v.1 : ℂ) + (v.2 : ℂ) * Complex.I := by
      rw [← htour_ray, hv]
      apply Complex.ext <;> simp [lpt]
    rw [hW] at h2
    exact (hgen ρ hρpos v.1 v.2) h2
  have ht_pos : 0 < t := by
    rcases lt_or_eq_of_le ht0 with h | h
    · exact h
    · exfalso
      have : tourOn u k t = lpt (u 0) := by rw [← h, tourOn_zero]
      exact hnl (u 0) this
  -- the parameter is strictly inside its step interval
  have hleft : ((edgeIdx k t : ℕ) : ℝ) < (k : ℝ) * t := by
    have hle : ((edgeIdx k t : ℕ) : ℝ) ≤ (k : ℝ) * t := by
      rw [edgeIdx]; exact Nat.floor_le (by positivity)
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exfalso
      have hform := tourOn_edge_form hk0 u ht0 ht1
      have hzero : (k : ℝ) * t - (edgeIdx k t : ℝ) = 0 := by linarith
      rw [hzero, zero_smul, add_zero] at hform
      exact hnl (u (edgeIdx k t)) hform
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := tourOn_local_affine_aux hk0 u ht0 ht1 hleft
  have hjlt : edgeIdx k t < k := edgeIdx_lt hk0 ht0 ht1
  have hstepj : IsUnitAdj (u (edgeIdx k t)) (u (edgeIdx k t + 1)) := hstep _ hjlt
  set w : ℂ := (k : ℂ) * (lpt (u (edgeIdx k t + 1)) - lpt (u (edgeIdx k t))) / W with hwdef
  have hw : w.im ≠ 0 := by
    rw [hwdef, hW]
    exact im_unitStepDir_ne_zero_aux hk0 hε hstepj
  -- continuity of `g` near `t`
  have hgc : Continuous g := by
    rw [hg]
    exact ((continuous_tourOn u k).sub continuous_const).div_const W
  have hgt_re_pos : 0 < (g t).re := by rw [hgtre]; exact hρpos
  have hev_re : ∀ᶠ s in 𝓝 t, 0 < (g s).re := by
    filter_upwards [hgc.continuousAt.preimage_mem_nhds
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hgt_re_pos)] with s hs
    exact hs
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ : ∃ δ > 0, ∀ s : ℝ, |s - t| < δ → 0 < (g s).re := by
    rcases Metric.mem_nhds_iff.mp hev_re with ⟨δ₂, hδ₂pos, hsub⟩
    exact ⟨δ₂, hδ₂pos, fun s hs => hsub (by simpa [Real.dist_eq] using hs)⟩
  have hev_Θ : ∀ᶠ s in 𝓝 t, |Θ s - Θ t| < Real.pi := by
    have h1 : ∀ᶠ s in 𝓝 t, Θ s ∈ Set.Ioo (Θ t - Real.pi) (Θ t + Real.pi) := by
      filter_upwards [hΘc.continuousAt.preimage_mem_nhds
        (isOpen_Ioo.mem_nhds ⟨sub_lt_self (Θ t) Real.pi_pos,
          lt_add_of_pos_right (Θ t) Real.pi_pos⟩)] with s hs
      exact hs
    filter_upwards [h1] with s hs
    rw [abs_lt]
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  obtain ⟨δ₃, hδ₃pos, hδ₃⟩ : ∃ δ > 0, ∀ s : ℝ, |s - t| < δ → |Θ s - Θ t| < Real.pi := by
    rcases Metric.mem_nhds_iff.mp hev_Θ with ⟨δ₃, hδ₃pos, hsub⟩
    exact ⟨δ₃, hδ₃pos, fun s hs => hsub (by simpa [Real.dist_eq] using hs)⟩
  set δ : ℝ := min (min δ₁ δ₂) (min δ₃ (min (t / 2) ((1 - t) / 2))) with hδ
  have hδpos : 0 < δ := by
    rw [hδ]
    exact lt_min (lt_min hδ₁pos hδ₂pos)
      (lt_min hδ₃pos (lt_min (by linarith) (by linarith)))
  have hδδ₁ : δ ≤ δ₁ := by rw [hδ]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hδδ₂ : δ ≤ δ₂ := by rw [hδ]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hδδ₃ : δ ≤ δ₃ := by rw [hδ]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hδt : δ ≤ t / 2 := by
    rw [hδ]; exact le_trans (le_trans (min_le_right _ _) (min_le_right _ _)) (min_le_left _ _)
  have hδ1t : δ ≤ (1 - t) / 2 := by
    rw [hδ]; exact le_trans (le_trans (min_le_right _ _) (min_le_right _ _)) (min_le_right _ _)
  refine ⟨δ, hδpos, ?_⟩
  -- the key local computation
  have key : ∀ s : ℝ, |s - t| < δ → s ≠ t →
      0 < ‖g s‖ ∧ Real.sin (Θ s - Θ t) = (s - t) * w.im / ‖g s‖ ∧ |Θ s - Θ t| < Real.pi := by
    intro s hs hst
    have hs1' : |s - t| < δ₁ := lt_of_lt_of_le hs hδδ₁
    have hs2' : |s - t| < δ₂ := lt_of_lt_of_le hs hδδ₂
    have hs3' : |s - t| < δ₃ := lt_of_lt_of_le hs hδδ₃
    have hst' : |s - t| < t / 2 := lt_of_lt_of_le hs hδt
    have hs1t' : |s - t| < (1 - t) / 2 := lt_of_lt_of_le hs hδ1t
    have hs_pos : 0 < s := by linarith [(abs_lt.mp hst').1]
    have hs_lt1 : s < 1 := by linarith [(abs_lt.mp hs1t').2]
    have hnorm : 0 < ‖g s‖ := lt_of_lt_of_le (hδ₂ s hs2') (Complex.re_le_norm _)
    have hdiff := hδ₁ s hs1'
    have hgs : g s = g t + ((s - t : ℝ) : ℂ) * w := by
      have h0 : g s - g t = ((s - t : ℝ) : ℂ) * w := by
        have hnum : (tourOn u k s - a) - (tourOn u k t - a)
            = tourOn u k s - tourOn u k t := by ring
        rw [hg_def s, hg_def t, ← sub_div, hnum, hdiff, hwdef]
        rw [Complex.real_smul, mul_div_assoc]
        push_cast
        ring
      exact (sub_eq_iff_eq_add').mp h0
    have him : (g s).im = (s - t) * w.im := by
      rw [hgs, Complex.add_im, Complex.mul_im]
      simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, add_zero]
      rw [hgtim]
      ring
    have hsin : Real.sin (Θ s - Θ t) = (s - t) * w.im / ‖g s‖ := by
      have hsin_s : Real.sin (Θ s) = (g s).im / ‖g s‖ := by
        have him2 : (g s).im = ‖g s‖ * Real.sin (Θ s) := by
          have hz : g s = ((‖g s‖ : ℝ) : ℂ) * Complex.exp ((Θ s : ℂ) * Complex.I) := by
            rw [hg_def s]
            exact hΘrep s (le_of_lt hs_pos) hs_lt1
          conv_lhs => rw [hz]
          rw [Complex.exp_ofReal_mul_I]
          simp only [Complex.mul_im, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
            Complex.mul_re, Complex.add_re, Complex.I_re, Complex.I_im]
          ring
        rw [eq_div_iff (ne_of_gt hnorm), him2]
        ring
      rw [show Θ s - Θ t = Θ s - (n : ℝ) * (2 * Real.pi) from by rw [hn],
        Real.sin_sub_int_mul_two_pi]
      rw [hsin_s, him]
    exact ⟨hnorm, hsin, hδ₃ s hs3'⟩
  rcases lt_or_gt_of_ne hw with hwneg | hwpos
  · right
    intro s hs hst
    obtain ⟨hnorm, hsin, habs⟩ := key s hs hst
    rcases lt_or_gt_of_ne hst with hlt | hgt
    · have h1 : 0 < Real.sin (Θ s - Θ t) := by
        rw [hsin]
        exact div_pos (mul_pos_of_neg_of_neg (sub_neg.mpr hlt) hwneg) hnorm
      have h2 : 0 < Θ s - Θ t := not_le.mp (fun hc => by
        have h3 := Real.sin_nonpos_of_nonpos_of_neg_pi_le hc (le_of_lt (abs_lt.mp habs).1)
        linarith)
      exact mul_neg_of_pos_of_neg h2 (sub_neg.mpr hlt)
    · have h1 : Real.sin (Θ s - Θ t) < 0 := by
        rw [hsin]
        exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (sub_pos.mpr hgt) hwneg) hnorm
      have h2 : Θ s - Θ t < 0 := not_le.mp (fun hc => by
        have h3 := Real.sin_nonneg_of_nonneg_of_le_pi hc (le_of_lt (abs_lt.mp habs).2)
        linarith)
      exact mul_neg_of_neg_of_pos h2 (sub_pos.mpr hgt)
  · left
    intro s hs hst
    obtain ⟨hnorm, hsin, habs⟩ := key s hs hst
    rcases lt_or_gt_of_ne hst with hlt | hgt
    · have h1 : Real.sin (Θ s - Θ t) < 0 := by
        rw [hsin]
        exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (sub_neg.mpr hlt) hwpos) hnorm
      have h2 : Θ s - Θ t < 0 := not_le.mp (fun hc => by
        have h3 := Real.sin_nonneg_of_nonneg_of_le_pi hc (le_of_lt (abs_lt.mp habs).2)
        linarith)
      exact mul_pos_of_neg_of_neg h2 (sub_neg.mpr hlt)
    · have h1 : 0 < Real.sin (Θ s - Θ t) := by
        rw [hsin]
        exact div_pos (mul_pos (sub_pos.mpr hgt) hwpos) hnorm
      have h2 : 0 < Θ s - Θ t := not_le.mp (fun hc => by
        have h3 := Real.sin_nonpos_of_nonpos_of_neg_pi_le hc (le_of_lt (abs_lt.mp habs).1)
        linarith)
      exact mul_pos h2 (sub_pos.mpr hgt)

end Work.HornSC.CellBoundaryJordan
