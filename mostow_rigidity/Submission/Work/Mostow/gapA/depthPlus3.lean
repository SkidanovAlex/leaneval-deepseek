import Mathlib
import Submission.Work.Mostow.gapA.defs
import Submission.Work.Mostow.gapA.geodFacts

/-!
# The `n = 3` depth bound `depthPlus3` (design step S5)

Given a rotation `f` about the geodesic `geodSet a b` (of angle `θ`), of finite order `m ≥ 2`,
which equals a power of `b₀` (of order `M`), and which is `η`-near-identity at `z` with `η ≤ 1`:

* the geodesic point `u` one unit beyond `z` in the direction away from the axis satisfies
  `hdist u (f • u) < η`, which gives `sinh (distGeod a b z + 1) * sin (θ/2) ≤ sinh (η/2)`;
* `m ∣ M` and `2 ≤ m` give `sin (π/M) ≤ (π/2) sin (θ/2)`;
* `M ≠ 2` (a half-turn would move the far point by at least `2`), so `M ≥ 3`.

Everything rests on `Work.Mostow.gapA.geodFacts` and the explicit far-point construction
`exists_distGeod_addOne` below (the `+1` variant of `exists_near_distGeod_ge_one`).
-/

set_option maxHeartbeats 1000000

namespace Work.Mostow.gapA

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

/-- Every point `w` has a point `u` at hyperbolic distance at most `1` whose distance to the
geodesic `geodSet a b` exceeds that of `w` by exactly `1` (move one unit away from the geodesic
along the perpendicular through `w`). -/
lemma exists_distGeod_addOne (n : ℕ) (hn : 2 ≤ n) (a b : E n) (ha : a ∈ Sph n)
    (hb : b ∈ Sph n) (hab : a ≠ b) (w : E n) :
    ∃ u : E n, hdist w u ≤ 1 ∧ distGeod a b w + 1 ≤ distGeod a b u := by
  by_cases hN : gcN a b w = 0
  · obtain ⟨Zv, hZ1, hZ2, hZ3⟩ := perpNullUnit hn ha hb hab
    have hZ1' : mink Zv (nvec a) = 0 := by simpa [mink_eq_mform, nvec_eq_theta] using hZ1
    have hZ2' : mink Zv (nvec b) = 0 := by simpa [mink_eq_mform, nvec_eq_theta] using hZ2
    have hZ3' : mink Zv Zv = 1 := by simpa [mink_eq_mform] using hZ3
    have hZ1'' : mink (nvec a) Zv = 0 := by rw [minkSeg_comm]; exact hZ1'
    have hZ2'' : mink (nvec b) Zv = 0 := by rw [minkSeg_comm]; exact hZ2'
    have hwgeod : w ∈ geodSet a b := (gcN_eq_zero_iff a b ha hb hab w).mp hN
    have hwspan : hlift w = gcA a b w • nvec a + gcB a b w • nvec b :=
      geodSet_lift_span a b ha hb hab hwgeod
    have hlevprod : lev a w * lev b w = gcL a b := (mem_geodSet_iff a b ha hb w).mp hwgeod
    have hUZ : mink (hlift w) Zv = 0 := by
      rw [hwspan, minkSeg_add_left, mink_smul_left'', mink_smul_left'', hZ1'', hZ2'']
      ring
    have hZU : mink Zv (hlift w) = 0 := by rw [minkSeg_comm]; exact hUZ
    set Yb : Fin n ⊕ Fin 1 → ℝ := Real.cosh 1 • hlift w + Real.sinh 1 • Zv with hYb
    have hUU : mink (hlift w) (hlift w) = -1 := by
      rw [mink_hlift_hlift, real_inner_self_eq_norm_sq]; nlinarith [tpart_sq w]
    have hYb_self : mink Yb Yb = -1 := by
      rw [hYb, mink_expand2, hUU, hUZ, hZU, hZ3']
      nlinarith [Real.cosh_sq_sub_sinh_sq 1]
    have hYb_hlift : mink (hlift w) Yb = -Real.cosh 1 := by
      rw [hYb, minkSeg_add_right, mink_smul_right'', mink_smul_right'', hUU, hUZ]
      ring
    have htimeb : 0 < Yb (Sum.inr 0) :=
      upper_of_mink_neg w Yb hYb_self (by rw [hYb_hlift]; exact neg_lt_zero.mpr (Real.cosh_pos 1))
    have hYblift : hlift (WithLp.toLp 2 (fun i : Fin n => Yb (Sum.inl i))) = Yb :=
      (eq_hlift_of_upper Yb (by rw [← mink_eq_mform]; exact hYb_self) htimeb).symm
    refine ⟨WithLp.toLp 2 (fun i : Fin n => Yb (Sum.inl i)), ?_, ?_⟩
    · rw [hdist_eq_arcosh_mink, hYblift, hYb_hlift, neg_neg,
        Real.arcosh_cosh (by norm_num : (0 : ℝ) ≤ 1)]
    · have hleva : lev a (WithLp.toLp 2 (fun i : Fin n => Yb (Sum.inl i)))
          = Real.cosh 1 * lev a w := by
        rw [lev_eq_neg_mink, hYblift, hYb, minkSeg_add_right, mink_smul_right'',
          mink_smul_right'', mink_nvec_hlift n a w, hZ1'']
        ring
      have hlevb : lev b (WithLp.toLp 2 (fun i : Fin n => Yb (Sum.inl i)))
          = Real.cosh 1 * lev b w := by
        rw [lev_eq_neg_mink, hYblift, hYb, minkSeg_add_right, mink_smul_right'',
          mink_smul_right'', mink_nvec_hlift n b w, hZ2'']
        ring
      have hval : Real.sqrt
          (lev a (WithLp.toLp 2 (fun i : Fin n => Yb (Sum.inl i)))
            * lev b (WithLp.toLp 2 (fun i : Fin n => Yb (Sum.inl i))) / gcL a b)
          = Real.cosh 1 := by
        rw [hleva, hlevb,
          show Real.cosh 1 * lev a w * (Real.cosh 1 * lev b w) / gcL a b
            = (Real.cosh 1) ^ 2 * (lev a w * lev b w / gcL a b) from by ring]
        rw [show lev a w * lev b w / gcL a b = 1 from by
            rw [hlevprod, div_self (gcL_ne_zero a b ha hb hab)],
          mul_one, Real.sqrt_sq (le_of_lt (Real.cosh_pos 1))]
      have hYbd : distGeod a b (WithLp.toLp 2 (fun i : Fin n => Yb (Sum.inl i))) = 1 := by
        rw [distGeod_eq a b ha hb _, hval, Real.arcosh_cosh (by norm_num : (0 : ℝ) ≤ 1)]
      have hwd : distGeod a b w = 0 := (distGeod_eq_zero_iff a b ha hb hab w).mpr hwgeod
      rw [hYbd, hwd]
      norm_num
  · have hww_nonneg := gcN_self_nonneg a b ha hb hab w
    have hww_pos : 0 < mink (gcN a b w) (gcN a b w) := by
      rcases lt_or_eq_of_le hww_nonneg with h | h
      · exact h
      · exact absurd (gcN_eq_zero_of_self a b ha hb hab w h.symm) hN
    set dd := distGeod a b w with hdd
    have hdd_nonneg : 0 ≤ dd := distGeod_nonneg a b ha hb hab w
    have hcoshdd : Real.cosh dd = Real.sqrt (lev a w * lev b w / gcL a b) := by
      rw [hdd, distGeod_eq a b ha hb w]
      exact Real.cosh_arcosh (sqrt_levdiv_ge_one a b ha hb hab w)
    have hlv : lev a w * lev b w / gcL a b = 1 + mink (gcN a b w) (gcN a b w) := by
      have h := gcN_self_mink a b ha hb hab w; linarith
    have hcoshdd_sq : Real.cosh dd ^ 2 = 1 + mink (gcN a b w) (gcN a b w) := by
      rw [hcoshdd, Real.sq_sqrt (div_nonneg (mul_nonneg (le_of_lt (lev_pos a ha w))
        (le_of_lt (lev_pos b hb w))) (le_of_lt (gcL_pos a b ha hb hab))), hlv]
    have hsinhdd_sq : Real.sinh dd ^ 2 = mink (gcN a b w) (gcN a b w) := by
      rw [Real.sinh_sq, hcoshdd_sq]; ring
    have hdd_pos : 0 < dd := by
      refine lt_of_le_of_ne hdd_nonneg (fun h0 => hww_pos.ne' ?_)
      rw [← hsinhdd_sq, ← h0, Real.sinh_zero]; norm_num
    have hsinhdd_pos : 0 < Real.sinh dd := Real.sinh_pos_iff.mpr hdd_pos
    set t := dd + 1 with ht
    have htd : t - dd = 1 := by rw [ht]; ring
    set Y : Fin n ⊕ Fin 1 → ℝ :=
      (Real.cosh t / Real.cosh dd) • (gcA a b w • nvec a + gcB a b w • nvec b)
        + (Real.sinh t / Real.sinh dd) • gcN a b w with hY
    have hS0 := mink_S0_self a b ha hb hab w
    have hS0N := mink_S0_gcN a b ha hb hab w
    have hNS0 : mink (gcN a b w) (gcA a b w • nvec a + gcB a b w • nvec b) = 0 := by
      rw [minkSeg_comm]; exact hS0N
    have hUS0 := mink_hlift_S0 a b ha hb hab w
    have hUN := mink_hlift_gcN a b ha hb hab w
    have hcdd : (Real.cosh t / Real.cosh dd) * Real.cosh dd = Real.cosh t :=
      div_mul_cancel₀ _ (ne_of_gt (Real.cosh_pos dd))
    have hsdd : (Real.sinh t / Real.sinh dd) * Real.sinh dd = Real.sinh t :=
      div_mul_cancel₀ _ (ne_of_gt hsinhdd_pos)
    have e1 : (Real.cosh t / Real.cosh dd) * (Real.cosh t / Real.cosh dd) * Real.cosh dd ^ 2
        = Real.cosh t ^ 2 := by
      rw [show (Real.cosh t / Real.cosh dd) * (Real.cosh t / Real.cosh dd) * Real.cosh dd ^ 2
          = ((Real.cosh t / Real.cosh dd) * Real.cosh dd) ^ 2 from by ring, hcdd]
    have e2 : (Real.sinh t / Real.sinh dd) * (Real.sinh t / Real.sinh dd) * Real.sinh dd ^ 2
        = Real.sinh t ^ 2 := by
      rw [show (Real.sinh t / Real.sinh dd) * (Real.sinh t / Real.sinh dd) * Real.sinh dd ^ 2
          = ((Real.sinh t / Real.sinh dd) * Real.sinh dd) ^ 2 from by ring, hsdd]
    have hY_self : mink Y Y = -1 := by
      rw [hY, mink_expand2, hS0, hS0N, hNS0]
      rw [← hcoshdd_sq, ← hsinhdd_sq]
      nlinarith [e1, e2, Real.cosh_sq_sub_sinh_sq t]
    have f1 : (Real.cosh t / Real.cosh dd) * Real.cosh dd ^ 2
        = Real.cosh t * Real.cosh dd := by
      rw [show (Real.cosh t / Real.cosh dd) * Real.cosh dd ^ 2
          = (Real.cosh t / Real.cosh dd) * Real.cosh dd * Real.cosh dd from by ring, hcdd]
    have f2 : (Real.sinh t / Real.sinh dd) * Real.sinh dd ^ 2
        = Real.sinh t * Real.sinh dd := by
      rw [show (Real.sinh t / Real.sinh dd) * Real.sinh dd ^ 2
          = (Real.sinh t / Real.sinh dd) * Real.sinh dd * Real.sinh dd from by ring, hsdd]
    have hY_hlift : mink (hlift w) Y = -Real.cosh 1 := by
      rw [hY, minkSeg_add_right, mink_smul_right'', mink_smul_right'', hUS0, hUN]
      rw [← hcoshdd_sq, ← hsinhdd_sq]
      have hcsub : Real.cosh (t - dd) = Real.cosh 1 := by rw [htd]
      nlinarith [f1, f2, Real.cosh_sub t dd, hcsub]
    have htime : 0 < Y (Sum.inr 0) :=
      upper_of_mink_neg w Y hY_self (by rw [hY_hlift]; exact neg_lt_zero.mpr (Real.cosh_pos 1))
    have hYlift : hlift (WithLp.toLp 2 (fun i : Fin n => Y (Sum.inl i))) = Y :=
      (eq_hlift_of_upper Y (by rw [← mink_eq_mform]; exact hY_self) htime).symm
    refine ⟨WithLp.toLp 2 (fun i : Fin n => Y (Sum.inl i)), ?_, ?_⟩
    · rw [hdist_eq_arcosh_mink, hYlift, hY_hlift, neg_neg,
        Real.arcosh_cosh (by norm_num : (0 : ℝ) ≤ 1)]
    · have hUa : mink (nvec a) (gcA a b w • nvec a + gcB a b w • nvec b) = -lev a w := by
        have hXX : mink (nvec a) (nvec a) = 0 := mink_nvec_self' ha
        have hXY : mink (nvec a) (nvec b) = inner ℝ a b - 1 := mink_nvec_nvec' a b
        simp only [minkSeg_add_right, mink_smul_right'', hXX, hXY, mul_zero, zero_mul,
          add_zero, zero_add]
        have h1 := gcB_mul a b ha hb hab w
        have h2 := two_gcL a b
        rw [show inner ℝ a b - 1 = -(2 * gcL a b) from by linarith [h2]]
        linarith [h1]
      have hUb : mink (nvec b) (gcA a b w • nvec a + gcB a b w • nvec b) = -lev b w := by
        have hYY : mink (nvec b) (nvec b) = 0 := mink_nvec_self' hb
        have hYX : mink (nvec b) (nvec a) = inner ℝ a b - 1 := by
          rw [mink_nvec_nvec' b a, real_inner_comm]
        simp only [minkSeg_add_right, mink_smul_right'', hYY, hYX, mul_zero, zero_mul,
          add_zero, zero_add]
        have h1 := gcA_mul a b ha hb hab w
        have h2 := two_gcL a b
        rw [show inner ℝ a b - 1 = -(2 * gcL a b) from by linarith [h2]]
        linarith [h1]
      have hleva : lev a (WithLp.toLp 2 (fun i : Fin n => Y (Sum.inl i)))
          = (Real.cosh t / Real.cosh dd) * lev a w := by
        rw [lev_eq_neg_mink, hYlift, hY, minkSeg_add_right, mink_smul_right'',
          mink_smul_right'', hUa, mink_nvec_a_gcN a b ha hb hab w]
        ring
      have hlevb : lev b (WithLp.toLp 2 (fun i : Fin n => Y (Sum.inl i)))
          = (Real.cosh t / Real.cosh dd) * lev b w := by
        rw [lev_eq_neg_mink, hYlift, hY, minkSeg_add_right, mink_smul_right'',
          mink_smul_right'', hUb, mink_nvec_b_gcN a b ha hb hab w]
        ring
      have hval : Real.sqrt
          (lev a (WithLp.toLp 2 (fun i : Fin n => Y (Sum.inl i)))
            * lev b (WithLp.toLp 2 (fun i : Fin n => Y (Sum.inl i))) / gcL a b)
          = Real.cosh t := by
        rw [hleva, hlevb]
        rw [show Real.cosh t / Real.cosh dd * lev a w
              * (Real.cosh t / Real.cosh dd * lev b w) / gcL a b
            = (Real.cosh t / Real.cosh dd) ^ 2 * (lev a w * lev b w / gcL a b) from by ring]
        rw [hlv, ← hcoshdd_sq]
        rw [show (Real.cosh t / Real.cosh dd) ^ 2 * Real.cosh dd ^ 2
            = (Real.cosh t / Real.cosh dd * Real.cosh dd) ^ 2 from by ring, hcdd,
          Real.sqrt_sq (le_of_lt (Real.cosh_pos t))]
      have hYd : distGeod a b (WithLp.toLp 2 (fun i : Fin n => Y (Sum.inl i))) = t := by
        rw [distGeod_eq a b ha hb _, hval]
        have htpos : 0 ≤ t := by rw [ht]; linarith
        rw [arcosh_cosh_abs', abs_of_nonneg htpos]
      rw [hYd, ht]

theorem depthPlus3 (hA : Submission.Mostow.POActionProp 3) (hI : Submission.Mostow.HypIsometryProp 3)
    (a b : Submission.Mostow.E 3) (ha : a ∈ Submission.Mostow.Sph 3) (hb : b ∈ Submission.Mostow.Sph 3)
    (hab : a ≠ b) (f : LeanEval.Geometry.MostowRigidity.PO 3 1) (z : Submission.Mostow.E 3) (θ : ℝ)
    (hf1 : f ≠ 1) (hf : Work.Mostow.IsRotationAbout f a b θ)
    (M : ℕ) (b₀ : LeanEval.Geometry.MostowRigidity.PO 3 1) (hMb : orderOf b₀ = M)
    (hfpow : ∃ k : ℤ, f = b₀ ^ k) (hθord : 2 ≤ (orderOf f : ℝ) * Real.sin (θ / 2))
    (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) (hnear : Submission.Mostow.NearIdAt f z η) :
    Real.sinh (Work.Mostow.distGeod a b z + 1) * Real.sin (Real.pi / (M : ℝ)) ≤
        Real.pi / 2 * Real.sinh (η / 2) ∧
      3 ≤ M := by
  obtain ⟨_, hnonneg, _, _, _⟩ :=
    geodFacts 3 (by norm_num) hA hI a b ha hb hab
  set m : ℕ := orderOf f with hm
  set s : ℝ := Real.sin (θ / 2) with hs
  have hθord' : 2 ≤ (m : ℝ) * s := hθord
  have hs_le1 : s ≤ 1 := by rw [hs]; exact Real.sin_le_one _
  have hm_ge2 : 2 ≤ m := by
    have h : (2 : ℝ) ≤ (m : ℝ) := by nlinarith [hθord', hs_le1]
    exact_mod_cast h
  have hm_pos : 0 < m := lt_of_lt_of_le (by norm_num) hm_ge2
  have hm_cast_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm_pos
  have hs_pos : 0 < s := by
    by_contra hcon
    push_neg at hcon
    have h : (m : ℝ) * s ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hm_cast_pos.le hcon
    linarith [hθord']
  -- ## `M ≠ 0`
  have hM_ne0 : M ≠ 0 := by
    intro hM0
    obtain ⟨k, hk⟩ := hfpow
    have hk0 : k ≠ 0 := by
      intro hk0
      rw [hk, hk0, zpow_zero] at hf1
      exact hf1 rfl
    have hb0inf : ¬ IsOfFinOrder b₀ := orderOf_eq_zero_iff.mp (by rw [hMb, hM0])
    have hfMm : f ^ m = 1 := by rw [hm]; exact pow_orderOf_eq_one f
    rw [hk] at hfMm
    rw [← zpow_natCast (b₀ ^ k) m, ← zpow_mul b₀ k (m : ℤ)] at hfMm
    have hmZ : (m : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt hm_pos)
    exact hb0inf ((isOfFinOrder_iff_zpow_eq_one).mpr
      ⟨k * (m : ℤ), mul_ne_zero hk0 hmZ, hfMm⟩)
  -- ## `m ∣ M`
  have hb0M : b₀ ^ M = 1 := by rw [← hMb]; exact pow_orderOf_eq_one b₀
  have hfM : f ^ M = 1 := by
    obtain ⟨k, hk⟩ := hfpow
    rw [hk, ← zpow_natCast (b₀ ^ k) M, ← zpow_mul b₀ k (M : ℤ), mul_comm,
      zpow_mul b₀ (M : ℤ) k, zpow_natCast b₀ M, hb0M, one_zpow]
  have hm_dvd_M : m ∣ M := by rw [hm]; exact orderOf_dvd_of_pow_eq_one hfM
  have hm_le_M : m ≤ M := Nat.le_of_dvd (Nat.pos_of_ne_zero hM_ne0) hm_dvd_M
  have hM_ge2 : 2 ≤ M := le_trans hm_ge2 hm_le_M
  -- ## the far point
  obtain ⟨u, hzu, hdu⟩ := exists_distGeod_addOne 3 (by norm_num) a b ha hb hab z
  have hlt : Submission.Mostow.hdist u (f • u) < η := hnear u hzu
  have hdisp : Submission.Mostow.hdist u (f • u)
      = 2 * Real.arsinh (Real.sinh (Work.Mostow.distGeod a b u) * s) := by
    rw [hf.2 u, ← hs]
  have hkey : Real.sinh (Work.Mostow.distGeod a b u) * s < Real.sinh (η / 2) := by
    have harg : Real.arsinh (Real.sinh (Work.Mostow.distGeod a b u) * s) < η / 2 := by
      have h2 := hlt
      rw [hdisp] at h2
      linarith
    have h2 := (Real.sinh_lt_sinh).mpr harg
    rwa [Real.sinh_arsinh] at h2
  have hkey2 : Real.sinh (Work.Mostow.distGeod a b z + 1) * s ≤ Real.sinh (η / 2) := by
    have h1 : Real.sinh (Work.Mostow.distGeod a b z + 1)
        ≤ Real.sinh (Work.Mostow.distGeod a b u) := (Real.sinh_le_sinh).mpr hdu
    exact le_trans (mul_le_mul_of_nonneg_right h1 hs_pos.le) hkey.le
  -- ## `sin (π/M) ≤ (π/2) sin (θ/2)`
  have hsinbnd : Real.sin (Real.pi / (M : ℝ)) ≤ Real.pi / 2 * s := by
    have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hM_ne0)
    have hmleM : (m : ℝ) ≤ (M : ℝ) := by exact_mod_cast hm_le_M
    have h1 : Real.pi / (m : ℝ) ≤ Real.pi / 2 * s := by
      rw [div_le_iff₀ hm_cast_pos]
      nlinarith [hθord', Real.pi_pos]
    have h2 : Real.pi / (M : ℝ) ≤ Real.pi / (m : ℝ) :=
      div_le_div_of_nonneg_left Real.pi_pos.le hm_cast_pos hmleM
    have h3 : Real.sin (Real.pi / (M : ℝ)) ≤ Real.pi / (M : ℝ) :=
      Real.sin_le (div_nonneg Real.pi_pos.le hMpos.le)
    linarith
  refine ⟨?_, ?_⟩
  · have hss : 0 ≤ Real.sinh (Work.Mostow.distGeod a b z + 1) :=
      le_of_lt (Real.sinh_pos_iff.mpr (by linarith [hnonneg z]))
    calc Real.sinh (Work.Mostow.distGeod a b z + 1) * Real.sin (Real.pi / (M : ℝ))
        ≤ Real.sinh (Work.Mostow.distGeod a b z + 1) * (Real.pi / 2 * s) :=
          mul_le_mul_of_nonneg_left hsinbnd hss
      _ = Real.pi / 2 * (Real.sinh (Work.Mostow.distGeod a b z + 1) * s) := by ring
      _ ≤ Real.pi / 2 * Real.sinh (η / 2) := mul_le_mul_of_nonneg_left hkey2 (by positivity)
  · by_contra hcon
    have hM_eq2 : M = 2 := by omega
    have hm_eq2 : m = 2 := by
      have hdvd2 : m ∣ 2 := by rw [← hM_eq2]; exact hm_dvd_M
      exact le_antisymm (Nat.le_of_dvd (by norm_num) hdvd2) hm_ge2
    have hs_eq1 : s = 1 := by
      have h2s : (2 : ℝ) ≤ 2 * s := by
        have hm2 : (m : ℝ) = 2 := by exact_mod_cast hm_eq2
        nlinarith [hθord']
      linarith [hs_le1, h2s]
    have hsinθ : Real.sin (θ / 2) = 1 := by rw [← hs]; exact hs_eq1
    have hdisp2 : Submission.Mostow.hdist u (f • u) = 2 * Work.Mostow.distGeod a b u := by
      rw [hf.2 u, hsinθ, mul_one, Real.arsinh_sinh]
    rw [hdisp2] at hlt
    have hdu1 : 1 ≤ Work.Mostow.distGeod a b u := by
      have := hnonneg z; linarith
    linarith [hη1, hlt, hdu1]

end

end Work.Mostow.gapA
