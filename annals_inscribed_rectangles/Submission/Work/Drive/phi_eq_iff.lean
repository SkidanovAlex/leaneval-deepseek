import Mathlib
import Submission.Work.Drive.LensSpaceGlue
import Submission.Work.Drive.phiCap_eq_phiConf
import Submission.Work.Drive.cappingSpace_homeomorph_prod

namespace Work.Drive

noncomputable section

lemma c₁_neg (x : Eucl 3) : c₁ (-x) = -c₁ x := by
  simp only [c₁, PiLp.neg_apply]
  push_cast
  ring

lemma c₂_neg (x : Eucl 3) : c₂ (-x) = -c₂ x := by
  simp only [c₂, PiLp.neg_apply]
  push_cast
  ring

lemma eq_of_c_eq {a b : Eucl 3} (h1 : c₁ a = c₁ b) (h2 : c₂ a = c₂ b) : a = b := by
  ext i
  fin_cases i
  · have := congrArg Complex.re h1
    simpa [c₁, Complex.add_re, Complex.mul_re] using this
  · have := congrArg Complex.im h1
    simpa [c₁, Complex.add_im, Complex.mul_im] using this
  · have := congrArg Complex.re h2
    simpa [c₂, Complex.add_re, Complex.mul_re] using this
  · have := congrArg Complex.im h2
    simpa [c₂, Complex.add_im, Complex.mul_im] using this

lemma complex_pair_eq_or_eq_neg {x y x' y' : ℂ} (hy : y ≠ 0)
    (hy2 : y' ^ 2 = y ^ 2) (hxy : x' * y' = x * y) :
    (x' = x ∧ y' = y) ∨ (x' = -x ∧ y' = -y) := by
  have hfac : (y' - y) * (y' + y) = 0 := by
    have h : (y' - y) * (y' + y) = y' ^ 2 - y ^ 2 := by ring
    rw [h, hy2, sub_self]
  rcases mul_eq_zero.mp hfac with h | h
  · have hy' : y' = y := sub_eq_zero.mp h
    have hxy' : x' * y = x * y := by rw [hy'] at hxy; exact hxy
    have hxx : x' - x = 0 := by
      have hm : (x' - x) * y = 0 := by rw [sub_mul, hxy', sub_self]
      rcases mul_eq_zero.mp hm with h' | h'
      · exact h'
      · exact absurd h' hy
    exact Or.inl ⟨sub_eq_zero.mp hxx, hy'⟩
  · have hy' : y' = -y := add_eq_zero_iff_eq_neg.mp h
    have hxy' : x' * (-y) = x * y := by rw [hy'] at hxy; exact hxy
    have hxx : x' + x = 0 := by
      have hm : (x' + x) * y = 0 := by
        have hh : -(x' * y) = x * y := by rw [← mul_neg]; exact hxy'
        rw [add_mul, ← hh, add_neg_cancel]
      rcases mul_eq_zero.mp hm with h' | h'
      · exact h'
      · exact absurd h' hy
    exact Or.inr ⟨add_eq_zero_iff_eq_neg.mp hxx, hy'⟩

lemma norm_sqrt_two_mul_div_eq (z1 z2 : ℂ) (hz2 : z2 ≠ 0) :
    ‖(Real.sqrt 2 : ℂ) * z1 * z2 / ((‖z2‖ : ℝ) : ℂ)‖ = Real.sqrt 2 * ‖z1‖ := by
  rw [norm_div, norm_mul, norm_mul]
  have h2 : ‖(Real.sqrt 2 : ℂ)‖ = Real.sqrt 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 2)]
  have hz : ‖(((‖z2‖ : ℝ) : ℂ))‖ = ‖z2‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg z2)]
  rw [h2, hz, mul_div_assoc, div_self (norm_ne_zero_iff.mpr hz2), mul_one]

lemma cap_data_inj {z1 z2 z1' z2' : ℂ}
    (hsp : ‖z1‖ ^ 2 + ‖z2‖ ^ 2 = 1) (hsp' : ‖z1'‖ ^ 2 + ‖z2'‖ ^ 2 = 1)
    (hle : ‖z1‖ ≤ ‖z2‖) (hle' : ‖z1'‖ ≤ ‖z2'‖)
    (ha : (((‖z2‖ : ℝ) : ℂ) / z2) ^ 2 = (((‖z2'‖ : ℝ) : ℂ) / z2') ^ 2)
    (hb : (Real.sqrt 2 : ℂ) * z1 * z2 / ((‖z2‖ : ℝ) : ℂ)
        = (Real.sqrt 2 : ℂ) * z1' * z2' / ((‖z2'‖ : ℝ) : ℂ)) :
    (z1' = z1 ∧ z2' = z2) ∨ (z1' = -z1 ∧ z2' = -z2) := by
  have hz2 : z2 ≠ 0 := ne_zero_of_norm_le hle hsp
  have hz2' : z2' ≠ 0 := ne_zero_of_norm_le hle' hsp'
  have hz2n : ‖z2‖ ≠ 0 := norm_ne_zero_iff.mpr hz2
  have hz2n' : ‖z2'‖ ≠ 0 := norm_ne_zero_iff.mpr hz2'
  have hnorm1 : ‖z1‖ = ‖z1'‖ := by
    have h := congrArg norm hb
    rw [norm_sqrt_two_mul_div_eq z1 z2 hz2, norm_sqrt_two_mul_div_eq z1' z2' hz2'] at h
    exact mul_left_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2))) h
  have hsq1 : ‖z1‖ ^ 2 = ‖z1'‖ ^ 2 := by rw [hnorm1]
  have hm2eq : ‖z2‖ ^ 2 = ‖z2'‖ ^ 2 := by linarith
  have hm_eq : ‖z2‖ = ‖z2'‖ := by
    have h := congrArg Real.sqrt hm2eq
    rwa [Real.sqrt_sq (norm_nonneg z2), Real.sqrt_sq (norm_nonneg z2')] at h
  have hcross : ((‖z2‖ : ℂ)) ^ 2 * z2' ^ 2 = ((‖z2'‖ : ℂ)) ^ 2 * z2 ^ 2 := by
    have h := ha
    rw [div_pow, div_pow] at h
    exact (div_eq_div_iff (pow_ne_zero 2 hz2) (pow_ne_zero 2 hz2')).mp h
  have hm2c : ((‖z2‖ : ℝ) : ℂ) ^ 2 = ((‖z2'‖ : ℝ) : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, hm_eq]
  have hz2sq : z2' ^ 2 = z2 ^ 2 := by
    rw [hm2c] at hcross
    exact mul_left_cancel₀ (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hz2n')) hcross
  have hprod : z1' * z2' = z1 * z2 := by
    have h := hb
    rw [← hm_eq] at h
    have hmC : ((‖z2‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz2n
    have hmul : (Real.sqrt 2 : ℂ) * z1 * z2 = (Real.sqrt 2 : ℂ) * z1' * z2' := by
      have h' : ((Real.sqrt 2 : ℂ) * z1 * z2 / ((‖z2‖ : ℝ) : ℂ)) * ((‖z2‖ : ℝ) : ℂ)
          = ((Real.sqrt 2 : ℂ) * z1' * z2' / ((‖z2‖ : ℝ) : ℂ)) * ((‖z2‖ : ℝ) : ℂ) := by
        rw [h]
      rwa [div_mul_cancel₀ _ hmC, div_mul_cancel₀ _ hmC] at h'
    have hmul2 : (Real.sqrt 2 : ℂ) * (z1 * z2) = (Real.sqrt 2 : ℂ) * (z1' * z2') := by
      rw [mul_assoc, mul_assoc] at hmul
      exact hmul
    have hs2 : (Real.sqrt 2 : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)))
    exact (mul_left_cancel₀ hs2 hmul2).symm
  exact complex_pair_eq_or_eq_neg hz2 hz2sq hprod

lemma conf_data_inj {z1 z2 z1' z2' : ℂ}
    (hsp : ‖z1‖ ^ 2 + ‖z2‖ ^ 2 = 1) (hsp' : ‖z1'‖ ^ 2 + ‖z2'‖ ^ 2 = 1)
    (hle : ‖z2‖ ≤ ‖z1‖) (hle' : ‖z2'‖ ≤ ‖z1'‖)
    (hc : (Real.sqrt 2 : ℂ) * z2 * z1 / ((‖z1‖ : ℝ) : ℂ)
        = (Real.sqrt 2 : ℂ) * z2' * z1' / ((‖z1'‖ : ℝ) : ℂ))
    (hd : (z1 / ((‖z1‖ : ℝ) : ℂ)) ^ 2 = (z1' / ((‖z1'‖ : ℝ) : ℂ)) ^ 2) :
    (z1' = z1 ∧ z2' = z2) ∨ (z1' = -z1 ∧ z2' = -z2) := by
  have ha : (((‖z1‖ : ℝ) : ℂ) / z1) ^ 2 = (((‖z1'‖ : ℝ) : ℂ) / z1') ^ 2 := by
    have h := congrArg Inv.inv hd
    simp only [← inv_pow, inv_div] at h
    exact h
  have hres := cap_data_inj (z1 := z2) (z2 := z1) (z1' := z2') (z2' := z1')
    (by linarith [hsp]) (by linarith [hsp']) hle hle' ha hc
  rcases hres with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h2, h1⟩
  · exact Or.inr ⟨h2, h1⟩

lemma capPt_inj (v w : {v : unitSphere 3 // ‖c₁ v.1‖ ≤ ‖c₂ v.1‖})
    (h : capPt v = capPt w) : w.1.1 = v.1.1 ∨ w.1.1 = -v.1.1 := by
  have hfst := congrArg Prod.fst h
  have hsnd := congrArg Prod.snd h
  have ha : (((‖c₂ v.1.1‖ : ℝ) : ℂ) / c₂ v.1.1) ^ 2
      = (((‖c₂ w.1.1‖ : ℝ) : ℂ) / c₂ w.1.1) ^ 2 := by
    have h1 : circleOf (capPt v).1 = circleOf (capPt w).1 := congrArg circleOf hfst
    rw [capPt_fst, capPt_fst, circleOf_circOf, circleOf_circOf] at h1
    exact h1
  have hb : (Real.sqrt 2 : ℂ) * c₁ v.1.1 * c₂ v.1.1 / ((‖c₂ v.1.1‖ : ℝ) : ℂ)
      = (Real.sqrt 2 : ℂ) * c₁ w.1.1 * c₂ w.1.1 / ((‖c₂ w.1.1‖ : ℝ) : ℂ) := by
    have h1 : ((capPt v).2 : ℂ) = ((capPt w).2 : ℂ) := congrArg Subtype.val hsnd
    rw [capPt_snd, capPt_snd] at h1
    exact h1
  have hres := cap_data_inj (sq_norm_eq_one v.1) (sq_norm_eq_one w.1) v.2 w.2 ha hb
  rcases hres with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl (eq_of_c_eq h1 h2)
  · exact Or.inr (eq_of_c_eq (by rw [c₁_neg]; exact h1) (by rw [c₂_neg]; exact h2))

lemma confPt_inj (v w : {v : unitSphere 3 // ‖c₂ v.1‖ ≤ ‖c₁ v.1‖})
    (h : confPt v = confPt w) : w.1.1 = v.1.1 ∨ w.1.1 = -v.1.1 := by
  have hfst := congrArg Prod.fst h
  have hsnd := congrArg Prod.snd h
  have hc : (Real.sqrt 2 : ℂ) * c₂ v.1.1 * c₁ v.1.1 / ((‖c₁ v.1.1‖ : ℝ) : ℂ)
      = (Real.sqrt 2 : ℂ) * c₂ w.1.1 * c₁ w.1.1 / ((‖c₁ w.1.1‖ : ℝ) : ℂ) := by
    have h1 : ((confPt v).1 : ℂ) = ((confPt w).1 : ℂ) := congrArg Subtype.val hfst
    rw [confPt_fst, confPt_fst] at h1
    exact h1
  have hd : (c₁ v.1.1 / ((‖c₁ v.1.1‖ : ℝ) : ℂ)) ^ 2
      = (c₁ w.1.1 / ((‖c₁ w.1.1‖ : ℝ) : ℂ)) ^ 2 := by
    have h1 : circleOf (confPt v).2 = circleOf (confPt w).2 := congrArg circleOf hsnd
    rw [confPt_snd, confPt_snd, circleOf_circOf, circleOf_circOf] at h1
    exact h1
  have hres := conf_data_inj (sq_norm_eq_one v.1) (sq_norm_eq_one w.1) v.2 w.2 hc hd
  rcases hres with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl (eq_of_c_eq h1 h2)
  · exact Or.inr (eq_of_c_eq (by rw [c₁_neg]; exact h1) (by rw [c₂_neg]; exact h2))

lemma capPt_bdy_norm {v : unitSphere 3} {hle : ‖c₁ v.1‖ ≤ ‖c₂ v.1‖}
    (θ φ : UnitAddCircle) (h : capPt ⟨v, hle⟩ = (θ, bdy φ)) :
    ‖c₁ v.1‖ = ‖c₂ v.1‖ := by
  have hsnd : ((capPt ⟨v, hle⟩).2 : ℂ) = circleOf φ := by rw [h]; rfl
  have hnorm : ‖((capPt ⟨v, hle⟩).2 : ℂ)‖ = 1 := by rw [hsnd]; exact norm_circleOf φ
  rw [capPt_snd] at hnorm
  have hnorm2 : Real.sqrt 2 * ‖c₁ v.1‖ = 1 := by
    rw [norm_sqrt_two_mul_div_eq (c₁ v.1) (c₂ v.1)
      (ne_zero_of_norm_le hle (sq_norm_eq_one v))] at hnorm
    exact hnorm
  have hz1 : ‖c₁ v.1‖ = 1 / Real.sqrt 2 := by
    rw [eq_div_iff (ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)))]
    linarith [hnorm2]
  have hz2 : ‖c₂ v.1‖ = 1 / Real.sqrt 2 := by
    have hs := sq_norm_eq_one v
    rw [hz1] at hs
    have h2 : ‖c₂ v.1‖ ^ 2 = (1 / Real.sqrt 2) ^ 2 := by
      rw [div_pow, one_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)] at hs ⊢
      linarith
    have h := congrArg Real.sqrt h2
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (by positivity)] at h
  rw [hz1, hz2]

lemma confPt_eq_of_capPt_bdy {v : unitSphere 3} {hle : ‖c₁ v.1‖ ≤ ‖c₂ v.1‖}
    {hge : ‖c₂ v.1‖ ≤ ‖c₁ v.1‖} (heq : ‖c₁ v.1‖ = ‖c₂ v.1‖) (θ φ : UnitAddCircle)
    (h : capPt ⟨v, hle⟩ = (θ, bdy φ)) :
    confPt ⟨v, hge⟩ = (bdy φ, θ + 2 • φ) := by
  have hcc := phiCap_eq_phiConf v heq
  rw [phiCap, phiConf, dif_pos hle, dif_pos hge] at hcc
  have hrel : lensRel (Sum.inl (capPt ⟨v, hle⟩)) (Sum.inr (confPt ⟨v, hge⟩)) := Quotient.exact hcc
  obtain ⟨θ', φ', h1, h2⟩ := lensRel_inl_inr hrel
  have hpair : (θ', bdy φ') = (θ, bdy φ) := h1.symm.trans h
  have hθ : θ' = θ := congrArg Prod.fst hpair
  have hφ : φ' = φ := bdy_injective (congrArg Prod.snd hpair)
  rw [h2, hθ, hφ]

lemma capPt_neg (u : unitSphere 3) {hu : ‖c₁ u.1‖ ≤ ‖c₂ u.1‖}
    {h : ‖c₁ (-u).1‖ ≤ ‖c₂ (-u).1‖} : capPt ⟨-u, h⟩ = capPt ⟨u, hu⟩ := by
  refine Prod.ext ?_ ?_
  · apply circleOf_injective
    rw [capPt_fst, capPt_fst, circleOf_circOf, circleOf_circOf,
        show (-u : unitSphere 3).1 = -u.1 from rfl, c₂_neg, norm_neg]
    ring
  · refine Subtype.ext ?_
    rw [capPt_snd, capPt_snd, show (-u : unitSphere 3).1 = -u.1 from rfl, c₁_neg, c₂_neg, norm_neg]
    ring

lemma confPt_neg (u : unitSphere 3) {hu : ‖c₂ u.1‖ ≤ ‖c₁ u.1‖}
    {h : ‖c₂ (-u).1‖ ≤ ‖c₁ (-u).1‖} : confPt ⟨-u, h⟩ = confPt ⟨u, hu⟩ := by
  refine Prod.ext ?_ ?_
  · refine Subtype.ext ?_
    rw [confPt_fst, confPt_fst, show (-u : unitSphere 3).1 = -u.1 from rfl, c₂_neg, c₁_neg, norm_neg]
    ring
  · apply circleOf_injective
    rw [confPt_snd, confPt_snd, circleOf_circOf, circleOf_circOf,
        show (-u : unitSphere 3).1 = -u.1 from rfl, c₁_neg, norm_neg]
    ring

lemma phi_neg (v : unitSphere 3) : phi (-v) = phi v := by
  by_cases h : ‖c₁ v.1‖ ≤ ‖c₂ v.1‖
  · have h' : ‖c₁ (-v).1‖ ≤ ‖c₂ (-v).1‖ := by
      rw [show (-v).1 = -v.1 from rfl, c₁_neg, c₂_neg, norm_neg, norm_neg]; exact h
    rw [phi, dif_pos h', phi, dif_pos h]
    exact Quotient.sound (Or.inl (congrArg Sum.inl (capPt_neg v (hu := h) (h := h'))))
  · have h' : ¬ (‖c₁ (-v).1‖ ≤ ‖c₂ (-v).1‖) := by
      rw [show (-v).1 = -v.1 from rfl, c₁_neg, c₂_neg, norm_neg, norm_neg]
      exact h
    rw [phi, dif_neg h', phi, dif_neg h]
    exact Quotient.sound
      (Or.inl (congrArg Sum.inr (confPt_neg v (hu := le_of_not_ge h) (h := le_of_not_ge h'))))

/-- **The fibres of the glueing map `phi : S³ → LensSpace` are exactly the antipodal pairs.**  This
uses that `capPt` (resp. `confPt`) is a bijection from `capHemi/{±1}` onto `CapTorus` (resp.
`confHemi/{±1}` onto `ConfTorus`) together with the boundary compatibility
`Work.Drive.phiCap_eq_phiConf` (the cap boundary point `(θ, w)` is glued to `(w, θ w²)`). -/
theorem phi_eq_iff (v w : unitSphere 3) : phi v = phi w ↔ w = v ∨ w = -v := by
  constructor
  · intro h
    by_cases hv : ‖c₁ v.1‖ ≤ ‖c₂ v.1‖
    · by_cases hw : ‖c₁ w.1‖ ≤ ‖c₂ w.1‖
      · rw [phi, dif_pos hv, phi, dif_pos hw] at h
        have := capPt_inj ⟨v, hv⟩ ⟨w, hw⟩ (lensRel_inl_inl (Quotient.exact h))
        rcases this with h1 | h1
        · exact Or.inl (Subtype.ext h1)
        · exact Or.inr (Subtype.ext h1)
      · rw [phi, dif_pos hv, phi, dif_neg hw] at h
        obtain ⟨θ, φ, hbdy, hconf⟩ :=
          lensRel_inl_inr (Quotient.exact h :
            lensRel (Sum.inl (capPt ⟨v, hv⟩)) (Sum.inr (confPt ⟨w, le_of_not_ge hw⟩)))
        have heq : ‖c₁ v.1‖ = ‖c₂ v.1‖ := capPt_bdy_norm θ φ hbdy
        have hconfv := confPt_eq_of_capPt_bdy (hle := hv) (hge := heq.ge) heq θ φ hbdy
        have heq2 : confPt ⟨v, heq.ge⟩ = confPt ⟨w, le_of_not_ge hw⟩ := by
          rw [hconfv, hconf]
        have := confPt_inj ⟨v, heq.ge⟩ ⟨w, le_of_not_ge hw⟩ heq2
        rcases this with h1 | h1
        · exact Or.inl (Subtype.ext h1)
        · exact Or.inr (Subtype.ext h1)
    · rw [phi, dif_neg hv] at h
      by_cases hw : ‖c₁ w.1‖ ≤ ‖c₂ w.1‖
      · rw [phi, dif_pos hw] at h
        obtain ⟨θ, φ, hbdy, hconf⟩ :=
          lensRel_inr_inl (Quotient.exact h :
            lensRel (Sum.inr (confPt ⟨v, le_of_not_ge hv⟩)) (Sum.inl (capPt ⟨w, hw⟩)))
        have heq : ‖c₁ w.1‖ = ‖c₂ w.1‖ := capPt_bdy_norm θ φ hbdy
        have hconfw := confPt_eq_of_capPt_bdy (hle := hw) (hge := heq.ge) heq θ φ hbdy
        have heq2 : confPt ⟨v, le_of_not_ge hv⟩ = confPt ⟨w, heq.ge⟩ := by
          rw [hconf, hconfw]
        have := confPt_inj ⟨w, heq.ge⟩ ⟨v, le_of_not_ge hv⟩ heq2.symm
        rcases this with h1 | h1
        · exact Or.inl (Subtype.ext h1.symm)
        · exact Or.inr (Subtype.ext (by
            have hh := congrArg Neg.neg h1
            simpa using hh.symm))
      · rw [phi, dif_neg hw] at h
        have := confPt_inj ⟨v, le_of_not_ge hv⟩ ⟨w, le_of_not_ge hw⟩
          (lensRel_inr_inr (Quotient.exact h))
        rcases this with h1 | h1
        · exact Or.inl (Subtype.ext h1)
        · exact Or.inr (Subtype.ext h1)
  · rintro (rfl | hw)
    · rfl
    · rw [hw]; exact (phi_neg v).symm

end

end Work.Drive
