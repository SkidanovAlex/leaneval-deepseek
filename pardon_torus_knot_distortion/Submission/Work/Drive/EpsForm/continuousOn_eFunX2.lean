import Mathlib
import Submission.Work.Drive.EpsForm.WaypointDesign2

/-!
# Joint continuity of the corrected tube-coordinate map on the parameter rectangle

`eFunX2 (t,s) = eFunX t s` is continuous on `[-π,π] × [0,1]`.

The profile `profX t` is a polyline through the waypoints `W1 → W2c t → W3c t → W5c t`
at the levels `0 → sig1c t → sig2c t → 1`.  The key point is that the *piecewise* definition
of `profX` can be written as a single continuous expression, using the clamped quantities

* `Acl t s = min (max s 0) (sig1c t)`,
* `Bcl t s = min (max s (sig1c t)) (sig2c t) - sig1c t`,
* `Ccl t s = min (max s (sig2c t)) 1 - sig2c t`,

which are `0` outside the corresponding branch and reproduce the branch parameter inside it.
Writing

`Phi t s = W1 + (Acl/σ1)•(W2c - W1) + (Bcl/(σ2-σ1))•(W3c - W2c) + (Ccl/(1-σ2))•(W5c - W3c)`

one has `Phi t s = profX t s` for `0 ≤ s ≤ 1` (`profX_eq_Phi`), while `Phi` is continuous
because the first term is continuous (σ₁ ≥ 3/4 never vanishes) and the numerators of the other
two terms vanish exactly where their denominators do (`abs_Bcl_div_le_one`,
`abs_Ccl_div_le_one`), the accompanying vectors `W3c - W2c` and `W5c - W3c` also vanishing
there (`W2c_eq_W3c_of_sig1c_eq_sig2c`, `W3c_eq_W5c_of_sig2c_eq_one`).
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Filter
open scoped Topology

namespace Work.Drive.EpsForm

noncomputable section

/-! ## 1. Continuity of the constituent functions

The clamped levels `sig1c`, `sig2c` and the waypoints `W2c`, `W3c` are defined by an `if` on
the closed chord range `[u0,v0]`; they are continuous because on the three closed pieces
`(-∞,u0]`, `[u0,v0]`, `[v0,∞)` they agree with a continuous function and the pieces meet in
the common values at `u0` and `v0`. -/

theorem cont_phLift : Continuous phLift := by
  unfold phLift
  exact continuous_id.sub ((continuous_const.mul (continuous_id.sub continuous_const)).div_const _)

theorem cont_W5c : Continuous W5c := by
  unfold W5c
  exact Real.continuous_cos.prodMk Real.continuous_sin

theorem inRange_u0 : inRange u0 := ⟨le_refl u0, by unfold u0 v0; linarith [Real.pi_pos]⟩

theorem inRange_v0 : inRange v0 := ⟨by unfold u0 v0; linarith [Real.pi_pos], le_refl v0⟩

theorem sig1c_eq_sig1_of_inRange {t : ℝ} (h : inRange t) : sig1c t = sig1 t := by
  rw [sig1c, if_pos h]

theorem sig2c_eq_sig2_of_inRange {t : ℝ} (h : inRange t) : sig2c t = sig2 t := by
  rw [sig2c, if_pos h]

theorem sig1c_eq_one_of_le {t : ℝ} (h : t ≤ u0) : sig1c t = 1 := by
  rcases eq_or_lt_of_le h with h' | h'
  · rw [h', sig1c, if_pos inRange_u0, sig1_u0]
  · rw [sig1c, if_neg (fun hin => absurd hin.1 (not_le.mpr h'))]

theorem sig1c_eq_one_of_ge {t : ℝ} (h : v0 ≤ t) : sig1c t = 1 := by
  rcases eq_or_lt_of_le h with h' | h'
  · rw [← h', sig1c, if_pos inRange_v0, sig1_v0]
  · rw [sig1c, if_neg (fun hin => absurd hin.2 (not_le.mpr h'))]

theorem sig2c_eq_one_of_le {t : ℝ} (h : t ≤ u0) : sig2c t = 1 := by
  rcases eq_or_lt_of_le h with h' | h'
  · rw [h', sig2c, if_pos inRange_u0, sig2_u0]
  · rw [sig2c, if_neg (fun hin => absurd hin.1 (not_le.mpr h'))]

theorem sig2c_eq_one_of_ge {t : ℝ} (h : v0 ≤ t) : sig2c t = 1 := by
  rcases eq_or_lt_of_le h with h' | h'
  · rw [← h', sig2c, if_pos inRange_v0, sig2_v0]
  · rw [sig2c, if_neg (fun hin => absurd hin.2 (not_le.mpr h'))]

theorem closure_cover_Iic_Icc_Ici :
    (Iic u0 ∪ Icc u0 v0 ∪ Ici v0 : Set ℝ) = univ :=
  Set.eq_univ_of_forall fun t => by
    rcases le_total t u0 with h | h
    · exact Or.inl (Or.inl (mem_Iic.mpr h))
    · rcases le_total t v0 with h' | h'
      · exact Or.inl (Or.inr (mem_Icc.mpr ⟨h, h'⟩))
      · exact Or.inr (mem_Ici.mpr h')

theorem cont_sig1c : Continuous sig1c := by
  rw [← continuousOn_univ]
  have h1 : ContinuousOn sig1c (Iic u0) :=
    continuous_const.continuousOn.congr fun t ht => sig1c_eq_one_of_le ht
  have h2 : ContinuousOn sig1c (Icc u0 v0) :=
    continuous_sig1.continuousOn.congr fun t ht => sig1c_eq_sig1_of_inRange ht
  have h3 : ContinuousOn sig1c (Ici v0) :=
    continuous_const.continuousOn.congr fun t ht => sig1c_eq_one_of_ge ht
  have h12 := h1.union_of_isClosed h2 isClosed_Iic isClosed_Icc
  have h := h12.union_of_isClosed h3 (isClosed_Iic.union isClosed_Icc) isClosed_Ici
  rwa [closure_cover_Iic_Icc_Ici] at h

theorem cont_sig2c : Continuous sig2c := by
  rw [← continuousOn_univ]
  have h1 : ContinuousOn sig2c (Iic u0) :=
    continuous_const.continuousOn.congr fun t ht => sig2c_eq_one_of_le ht
  have h2 : ContinuousOn sig2c (Icc u0 v0) :=
    continuous_sig2.continuousOn.congr fun t ht => sig2c_eq_sig2_of_inRange ht
  have h3 : ContinuousOn sig2c (Ici v0) :=
    continuous_const.continuousOn.congr fun t ht => sig2c_eq_one_of_ge ht
  have h12 := h1.union_of_isClosed h2 isClosed_Iic isClosed_Icc
  have h := h12.union_of_isClosed h3 (isClosed_Iic.union isClosed_Icc) isClosed_Ici
  rwa [closure_cover_Iic_Icc_Ici] at h

theorem W2c_eq_W5c_of_le {t : ℝ} (h : t ≤ u0) : W2c t = W5c t := by
  rcases eq_or_lt_of_le h with h' | h'
  · rw [h']; exact W2c_u0
  · rw [W2c, if_neg (fun hin => absurd hin.1 (not_le.mpr h'))]

theorem W2c_eq_W5c_of_ge {t : ℝ} (h : v0 ≤ t) : W2c t = W5c t := by
  rcases eq_or_lt_of_le h with h' | h'
  · rw [← h']; exact W2c_v0
  · rw [W2c, if_neg (fun hin => absurd hin.2 (not_le.mpr h'))]

theorem W3c_u0 : W3c u0 = W5c u0 := by
  rw [W3c, if_pos inRange_u0, phLift_u0, dlt_u0, add_zero]
  rfl

theorem W3c_v0 : W3c v0 = W5c v0 := by
  rw [W3c, if_pos inRange_v0, phLift_v0, dlt_v0, add_zero]
  simp only [W5c, Real.cos_sub_two_pi, Real.sin_sub_two_pi]

theorem W3c_eq_W5c_of_le {t : ℝ} (h : t ≤ u0) : W3c t = W5c t := by
  rcases eq_or_lt_of_le h with h' | h'
  · rw [h']; exact W3c_u0
  · rw [W3c, if_neg (fun hin => absurd hin.1 (not_le.mpr h'))]

theorem W3c_eq_W5c_of_ge {t : ℝ} (h : v0 ≤ t) : W3c t = W5c t := by
  rcases eq_or_lt_of_le h with h' | h'
  · rw [← h']; exact W3c_v0
  · rw [W3c, if_neg (fun hin => absurd hin.2 (not_le.mpr h'))]

theorem cont_W2c : Continuous W2c := by
  rw [← continuousOn_univ]
  have h1 : ContinuousOn W2c (Iic u0) :=
    cont_W5c.continuousOn.congr fun t ht => W2c_eq_W5c_of_le ht
  have h2 : ContinuousOn W2c (Icc u0 v0) :=
    ((Real.continuous_cos.comp cont_phLift).prodMk
      (Real.continuous_sin.comp cont_phLift)).continuousOn.congr fun t ht => by
        rw [W2c, if_pos (show inRange t from ht)]
        rfl
  have h3 : ContinuousOn W2c (Ici v0) :=
    cont_W5c.continuousOn.congr fun t ht => W2c_eq_W5c_of_ge ht
  have h12 := h1.union_of_isClosed h2 isClosed_Iic isClosed_Icc
  have h := h12.union_of_isClosed h3 (isClosed_Iic.union isClosed_Icc) isClosed_Ici
  rwa [closure_cover_Iic_Icc_Ici] at h

theorem cont_W3c : Continuous W3c := by
  rw [← continuousOn_univ]
  have h1 : ContinuousOn W3c (Iic u0) :=
    cont_W5c.continuousOn.congr fun t ht => W3c_eq_W5c_of_le ht
  have h2 : ContinuousOn W3c (Icc u0 v0) :=
    ((Real.continuous_cos.comp (cont_phLift.add continuous_dlt)).prodMk
      (Real.continuous_sin.comp (cont_phLift.add continuous_dlt))).continuousOn.congr fun t ht => by
        rw [W3c, if_pos (show inRange t from ht)]
        rfl
  have h3 : ContinuousOn W3c (Ici v0) :=
    cont_W5c.continuousOn.congr fun t ht => W3c_eq_W5c_of_ge ht
  have h12 := h1.union_of_isClosed h2 isClosed_Iic isClosed_Icc
  have h := h12.union_of_isClosed h3 (isClosed_Iic.union isClosed_Icc) isClosed_Ici
  rwa [closure_cover_Iic_Icc_Ici] at h

/-! ## 2. Elementary comparisons between the levels -/

theorem sig1c_le_sig2c (t : ℝ) : sig1c t ≤ sig2c t := by
  by_cases h : inRange t
  · rw [sig1c_eq_sig1_of_inRange h, sig2c_eq_sig2_of_inRange h]
    have hb := bump_nonneg_of_inRange h
    unfold sig1 sig2
    linarith
  · rw [sig1c, if_neg h, sig2c, if_neg h]

/-- Where the two chord levels are equal the two chord waypoints coincide (both are the
boundary point `W5c t`). -/
theorem W2c_eq_W3c_of_sig1c_eq_sig2c {t : ℝ} (h : sig1c t = sig2c t) : W2c t = W3c t := by
  by_cases hin : inRange t
  · have hb : bump t = 0 := by
      have h' : sig1 t = sig2 t := by
        rw [← sig1c_eq_sig1_of_inRange hin, ← sig2c_eq_sig2_of_inRange hin, h]
      unfold sig1 sig2 at h'
      linarith
    rcases (bump_eq_zero_iff hin).1 hb with h' | h'
    · rw [h', W2c_u0, W3c_u0]
    · rw [h', W2c_v0, W3c_v0]
  · rw [W2c_eq_of_not_inRange hin, W3c, if_neg hin]

/-- Where the upper chord level has reached its maximal value `1` the third waypoint is the
boundary point. -/
theorem W3c_eq_W5c_of_sig2c_eq_one {t : ℝ} (h : sig2c t = 1) : W3c t = W5c t := by
  by_cases hin : inRange t
  · have hb : bump t = 0 := by
      have h' : sig2 t = 1 := by rw [← sig2c_eq_sig2_of_inRange hin, h]
      unfold sig2 at h'
      linarith
    rcases (bump_eq_zero_iff hin).1 hb with h' | h'
    · rw [h', W3c_u0]
    · rw [h', W3c_v0]
  · rw [W3c, if_neg hin]

/-! ## 3. The continuous model `Phi` of the profile -/

/-- The clamped lower parameter: `s / σ₁` on the first branch, `1` afterwards. -/
def Acl (t s : ℝ) : ℝ := min (max s 0) (sig1c t)

/-- The numerator `σ₁·b` of the middle branch parameter `b`, clamped to `[0, σ₂-σ₁]`. -/
def Bcl (t s : ℝ) : ℝ := min (max s (sig1c t)) (sig2c t) - sig1c t

/-- The numerator `(1-σ₂)·c` of the last branch parameter `c`, clamped to `[0, 1-σ₂]`. -/
def Ccl (t s : ℝ) : ℝ := min (max s (sig2c t)) 1 - sig2c t

/-- The profile as a single `+`/`•` expression, using the clamped parameters. -/
def Phi (t s : ℝ) : ℝ × ℝ :=
  (W1 + (Acl t s / sig1c t) • (W2c t - W1))
    + (Bcl t s / (sig2c t - sig1c t)) • (W3c t - W2c t)
    + (Ccl t s / (1 - sig2c t)) • (W5c t - W3c t)

/-- A segment is its initial point plus the parameter times the difference. -/
theorem seg_add_smul (P Q : ℝ × ℝ) (a b s : ℝ) :
    seg P Q a b s = P + ((s - a) / (b - a)) • (Q - P) := by
  ext <;> simp [seg] <;> ring

theorem Bcl_nonneg (t s : ℝ) : 0 ≤ Bcl t s := by
  have hle := sig1c_le_sig2c t
  have h1 : sig1c t ≤ max s (sig1c t) := le_max_right _ _
  have h2 : sig1c t ≤ min (max s (sig1c t)) (sig2c t) := le_min h1 hle
  simp only [Bcl]
  linarith

theorem Bcl_le (t s : ℝ) : Bcl t s ≤ sig2c t - sig1c t := by
  have h1 : min (max s (sig1c t)) (sig2c t) ≤ sig2c t := min_le_right _ _
  simp only [Bcl]
  linarith

theorem Ccl_nonneg (t s : ℝ) : 0 ≤ Ccl t s := by
  have hle := sig2c_le_one t
  have h1 : sig2c t ≤ max s (sig2c t) := le_max_right _ _
  have h2 : sig2c t ≤ min (max s (sig2c t)) 1 := le_min h1 hle
  simp only [Ccl]
  linarith

theorem Ccl_le (t s : ℝ) : Ccl t s ≤ 1 - sig2c t := by
  have h1 : min (max s (sig2c t)) 1 ≤ 1 := min_le_right _ _
  simp only [Ccl]
  linarith

theorem abs_Bcl_div_le_one (t s : ℝ) : |Bcl t s / (sig2c t - sig1c t)| ≤ 1 := by
  rcases eq_or_lt_of_le (sig1c_le_sig2c t) with h | h
  · have hzero : Bcl t s = 0 := by
      simp only [Bcl]
      rw [← h, min_eq_right (le_max_right s (sig1c t)), sub_self]
    rw [hzero]
    simp
  · have hpos : 0 < sig2c t - sig1c t := sub_pos.mpr h
    rw [abs_of_nonneg (div_nonneg (Bcl_nonneg t s) hpos.le)]
    exact (div_le_one hpos).mpr (Bcl_le t s)

theorem abs_Ccl_div_le_one (t s : ℝ) : |Ccl t s / (1 - sig2c t)| ≤ 1 := by
  rcases eq_or_lt_of_le (sig2c_le_one t) with h | h
  · have hzero : Ccl t s = 0 := by
      simp only [Ccl]
      rw [h, min_eq_right (le_max_right s 1), sub_self]
    rw [hzero]
    simp
  · have hpos : 0 < 1 - sig2c t := sub_pos.mpr h
    rw [abs_of_nonneg (div_nonneg (Ccl_nonneg t s) hpos.le)]
    exact (div_le_one hpos).mpr (Ccl_le t s)

/-! ## 4. The profile is the clamped expression -/

theorem profX_eq_Phi {t s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : profX t s = Phi t s := by
  have h12 : sig1c t ≤ sig2c t := sig1c_le_sig2c t
  have h2le1 : sig2c t ≤ 1 := sig2c_le_one t
  have h1pos : sig1c t ≠ 0 := ne_of_gt (sig1c_pos t)
  unfold profX Phi
  split_ifs with h1 h2
  · have hA : Acl t s = s := by
      simp only [Acl]
      rw [max_eq_left hs0, min_eq_left h1]
    have hB : Bcl t s = 0 := by
      simp only [Bcl]
      rw [max_eq_right h1, min_eq_left h12, sub_self]
    have hC : Ccl t s = 0 := by
      simp only [Ccl]
      rw [max_eq_right (le_trans h1 h12), min_eq_left h2le1, sub_self]
    rw [seg_add_smul, hA, hB, hC]
    simp only [sub_zero, zero_div, zero_smul, add_zero]
  · have hA : Acl t s = sig1c t := by
      simp only [Acl]
      rw [max_eq_left hs0, min_eq_right (le_of_not_ge h1)]
    have hB : Bcl t s = s - sig1c t := by
      simp only [Bcl]
      rw [max_eq_left (le_of_not_ge h1), min_eq_left h2]
    have hC : Ccl t s = 0 := by
      simp only [Ccl]
      rw [max_eq_right h2, min_eq_left h2le1, sub_self]
    rw [seg_add_smul, hA, hB, hC, div_self h1pos, one_smul]
    simp only [zero_div, zero_smul, add_zero, add_sub_cancel]
  · have hlt : sig2c t < 1 := lt_of_lt_of_le (not_le.mp h2) hs1
    have hin : inRange t := by
      by_contra hc
      rw [sig2c, if_neg hc] at hlt
      exact absurd hlt (lt_irrefl 1)
    have hb : 0 < bump t := by
      have h2' : sig2 t < 1 := by rw [← sig2c_eq_sig2_of_inRange hin]; exact hlt
      unfold sig2 at h2'
      linarith
    have hopen := (bump_pos_iff hin).1 hb
    have hne : sig2c t - sig1c t ≠ 0 := by
      have hlt' : sig1c t < sig2c t := by
        rw [sig1c_eq_sig1_of_inRange hin, sig2c_eq_sig2_of_inRange hin]
        exact sig1_lt_sig2 hopen.1 hopen.2
      linarith
    have hA : Acl t s = sig1c t := by
      simp only [Acl]
      rw [max_eq_left hs0, min_eq_right (le_of_not_ge h1)]
    have hB : Bcl t s = sig2c t - sig1c t := by
      simp only [Bcl]
      rw [max_eq_left (le_of_not_ge h1), min_eq_right (le_of_not_ge h2)]
    have hC : Ccl t s = s - sig2c t := by
      simp only [Ccl]
      rw [max_eq_left (le_of_not_ge h2), min_eq_left hs1]
    rw [seg_add_smul, hA, hB, hC, div_self h1pos, one_smul, div_self hne, one_smul]
    simp only [add_sub_cancel]

/-! ## 5. Continuity of `Phi` -/

theorem cont_Acl : Continuous fun p : ℝ × ℝ => Acl p.1 p.2 :=
  (continuous_snd.max continuous_const).min (cont_sig1c.comp continuous_fst)

theorem cont_Bcl : Continuous fun p : ℝ × ℝ => Bcl p.1 p.2 :=
  ((continuous_snd.max (cont_sig1c.comp continuous_fst)).min (cont_sig2c.comp continuous_fst)).sub
    (cont_sig1c.comp continuous_fst)

theorem cont_Ccl : Continuous fun p : ℝ × ℝ => Ccl p.1 p.2 :=
  ((continuous_snd.max (cont_sig2c.comp continuous_fst)).min continuous_const).sub
    (cont_sig2c.comp continuous_fst)

theorem cont_Phi_t1 :
    Continuous fun p : ℝ × ℝ => (Acl p.1 p.2 / sig1c p.1) • (W2c p.1 - W1) :=
  (cont_Acl.div (cont_sig1c.comp continuous_fst) fun p => ne_of_gt (sig1c_pos p.1)).smul
    ((cont_W2c.comp continuous_fst).sub continuous_const)

theorem cont_Phi_t2 :
    Continuous fun p : ℝ × ℝ =>
      (Bcl p.1 p.2 / (sig2c p.1 - sig1c p.1)) • (W3c p.1 - W2c p.1) := by
  rw [continuous_iff_continuousAt]
  intro p
  by_cases h : sig1c p.1 < sig2c p.1
  · have hne : sig2c p.1 - sig1c p.1 ≠ 0 := ne_of_gt (sub_pos.mpr h)
    exact ((cont_Bcl.continuousAt.div
        ((cont_sig2c.comp continuous_fst).continuousAt.sub
          (cont_sig1c.comp continuous_fst).continuousAt) hne).smul
      ((cont_W3c.comp continuous_fst).continuousAt.sub
        (cont_W2c.comp continuous_fst).continuousAt))
  · have heq : sig2c p.1 = sig1c p.1 := le_antisymm (le_of_not_gt h) (sig1c_le_sig2c p.1)
    have hzero : Bcl p.1 p.2 = 0 := by
      simp only [Bcl]
      rw [heq, min_eq_right (le_max_right p.2 (sig1c p.1)), sub_self]
    have hvec : W3c p.1 - W2c p.1 = 0 :=
      sub_eq_zero.mpr (W2c_eq_W3c_of_sig1c_eq_sig2c heq.symm).symm
    have hbound : ∀ q : ℝ × ℝ,
        ‖(Bcl q.1 q.2 / (sig2c q.1 - sig1c q.1)) • (W3c q.1 - W2c q.1)‖
          ≤ ‖W3c q.1 - W2c q.1‖ := by
      intro q
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _) (abs_Bcl_div_le_one q.1 q.2)
    have htend : Filter.Tendsto (fun q : ℝ × ℝ => ‖W3c q.1 - W2c q.1‖) (𝓝 p) (𝓝 0) := by
      have hca : Filter.Tendsto (fun q : ℝ × ℝ => ‖W3c q.1 - W2c q.1‖) (𝓝 p)
          (𝓝 ‖W3c p.1 - W2c p.1‖) :=
        (((cont_W3c.comp continuous_fst).sub (cont_W2c.comp continuous_fst)).norm).continuousAt
      rwa [hvec, norm_zero] at hca
    rw [ContinuousAt, show (Bcl p.1 p.2 / (sig2c p.1 - sig1c p.1)) • (W3c p.1 - W2c p.1)
      = 0 by rw [hzero, zero_div, zero_smul]]
    exact squeeze_zero_norm hbound htend

theorem cont_Phi_t3 :
    Continuous fun p : ℝ × ℝ =>
      (Ccl p.1 p.2 / (1 - sig2c p.1)) • (W5c p.1 - W3c p.1) := by
  rw [continuous_iff_continuousAt]
  intro p
  by_cases h : sig2c p.1 < 1
  · have hne : 1 - sig2c p.1 ≠ 0 := ne_of_gt (sub_pos.mpr h)
    exact ((cont_Ccl.continuousAt.div
        (continuous_const.sub (cont_sig2c.comp continuous_fst)).continuousAt hne).smul
      ((cont_W5c.comp continuous_fst).continuousAt.sub
        (cont_W3c.comp continuous_fst).continuousAt))
  · have heq : sig2c p.1 = 1 := le_antisymm (sig2c_le_one p.1) (not_lt.mp h)
    have hzero : Ccl p.1 p.2 = 0 := by
      simp only [Ccl]
      rw [heq, min_eq_right (le_max_right p.2 1), sub_self]
    have hvec : W5c p.1 - W3c p.1 = 0 :=
      sub_eq_zero.mpr (W3c_eq_W5c_of_sig2c_eq_one heq).symm
    have hbound : ∀ q : ℝ × ℝ,
        ‖(Ccl q.1 q.2 / (1 - sig2c q.1)) • (W5c q.1 - W3c q.1)‖
          ≤ ‖W5c q.1 - W3c q.1‖ := by
      intro q
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _) (abs_Ccl_div_le_one q.1 q.2)
    have htend : Filter.Tendsto (fun q : ℝ × ℝ => ‖W5c q.1 - W3c q.1‖) (𝓝 p) (𝓝 0) := by
      have hca : Filter.Tendsto (fun q : ℝ × ℝ => ‖W5c q.1 - W3c q.1‖) (𝓝 p)
          (𝓝 ‖W5c p.1 - W3c p.1‖) :=
        (((cont_W5c.comp continuous_fst).sub (cont_W3c.comp continuous_fst)).norm).continuousAt
      rwa [hvec, norm_zero] at hca
    rw [ContinuousAt, show (Ccl p.1 p.2 / (1 - sig2c p.1)) • (W5c p.1 - W3c p.1)
      = 0 by rw [hzero, zero_div, zero_smul]]
    exact squeeze_zero_norm hbound htend

theorem cont_Phi : Continuous fun p : ℝ × ℝ => Phi p.1 p.2 := by
  have h : Continuous fun p : ℝ × ℝ =>
      (W1 + (Acl p.1 p.2 / sig1c p.1) • (W2c p.1 - W1))
        + (Bcl p.1 p.2 / (sig2c p.1 - sig1c p.1)) • (W3c p.1 - W2c p.1)
        + (Ccl p.1 p.2 / (1 - sig2c p.1)) • (W5c p.1 - W3c p.1) :=
    ((continuous_const.add cont_Phi_t1).add cont_Phi_t2).add cont_Phi_t3
  simpa only [Phi] using h

theorem continuousOn_profX :
    ContinuousOn (fun p : ℝ × ℝ => profX p.1 p.2) (Icc (-Real.pi) Real.pi ×ˢ Icc (0 : ℝ) 1) :=
  cont_Phi.continuousOn.congr fun _ hp => profX_eq_Phi hp.2.1 hp.2.2

/-! ## 6. The corrected disc map -/

theorem continuousOn_eFunX2 :
    ContinuousOn eFunX2 (Set.Icc (-Real.pi) Real.pi ×ˢ Set.Icc (0 : ℝ) 1) := by
  set S := Set.Icc (-Real.pi) Real.pi ×ˢ Set.Icc (0 : ℝ) 1 with hS
  have hprof : ContinuousOn (fun p : ℝ × ℝ => profX p.1 p.2) S := continuousOn_profX
  have h1 : ContinuousOn (fun p : ℝ × ℝ => (profX p.1 p.2).1) S :=
    continuous_fst.comp_continuousOn hprof
  have h2 : ContinuousOn (fun p : ℝ × ℝ => (profX p.1 p.2).2) S :=
    continuous_snd.comp_continuousOn hprof
  have hcx : ContinuousOn (fun p : ℝ × ℝ => Real.cos p.1) S :=
    Real.continuous_cos.comp_continuousOn continuous_fst.continuousOn
  have hsx : ContinuousOn (fun p : ℝ × ℝ => Real.sin p.1) S :=
    Real.continuous_sin.comp_continuousOn continuous_fst.continuousOn
  have hmain : ContinuousOn (fun p : ℝ × ℝ => fun i : Fin 3 =>
      (if i.val = 0 then (2 + (profX p.1 p.2).1) * Real.cos p.1
       else if i.val = 1 then (2 + (profX p.1 p.2).1) * Real.sin p.1
       else (profX p.1 p.2).2 : ℝ)) S := by
    apply continuousOn_pi.mpr
    intro i
    fin_cases i <;> simp
    · exact (continuousOn_const.add h1).mul hcx
    · exact (continuousOn_const.add h1).mul hsx
    · exact h2
  have hfin := (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 3 => ℝ)).comp_continuousOn hmain
  refine hfin.congr fun p hp => ?_
  simp [eFunX2, eFunX]

end

end Work.Drive.EpsForm
