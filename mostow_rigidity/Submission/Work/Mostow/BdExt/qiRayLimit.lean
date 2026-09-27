import Mathlib
import Submission.Work.Mostow.BdExt.Basic
import Submission.Work.Mostow.BdExt.rayDist
import Submission.Work.Mostow.BdExt.lawCosines
import Submission.Work.Mostow.BdExt.stepSum
import Submission.Work.Mostow.BdExt.qiRayStep

/-!
# The limiting direction of a quasi-isometric ray, with rate

Let `Φ : E n → E n` be a `(K, C)`-quasi-isometry of the chart model of `ℍⁿ` and let `ξ ∈ Sph n`.
Along the geodesic ray `t ↦ ray ξ t` issued from the origin towards `ξ`, the Euclidean
directions `t ↦ dirv (Φ (ray ξ t))` converge to a boundary point `η ∈ Sph n`, and the
convergence is exponentially fast with rate `exp (-t/(2K))`.

The proof is the elementary "summable increments" argument: consecutive directions at
hyperbolic distance at most `K + C` differ by at most
`sqrt (2 (cosh (K + C) - 1) / (sinh Ls * sinh Lt))` (the quantitative law of cosines,
`qiRayStep`), while the hyperbolic levels `Ls, Lt` grow at least linearly in the parameters
(`qiRayLvlLower`).  Summing these exponentially small increments along the sequence of
integer parameters gives convergence, and comparing a real parameter with the next integer
gives the stated rate.
-/

namespace Work.Mostow.BdExt

open Submission.Mostow

noncomputable section

variable {n : ℕ}

/-- The Euclidean direction of a point of the chart is always bounded by `1`. -/
lemma dirv_norm_le_one (u : E n) : ‖dirv u‖ ≤ 1 := by
  rcases eq_or_ne u 0 with rfl | hu
  · simp [dirv]
  · rw [norm_dirv u hu]

/-- For `x ≥ 1` we have `exp x / 4 ≤ sinh x`. -/
lemma sinh_lower_exp (x : ℝ) (hx : 1 ≤ x) : Real.exp x / 4 ≤ Real.sinh x := by
  have h1 : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h2 : 2 < Real.exp x := lt_of_lt_of_le Real.exp_one_gt_two (Real.exp_le_exp.mpr hx)
  rw [Real.sinh_eq]
  linarith

/-- Lower bound on the hyperbolic level of the image of a ray: comparing the ray with the
quasi-isometry lower bound and using the triangle inequality,
`lvl (Φ (ray ξ t)) ≥ (t - C)/K - lvl (Φ (ray ξ 0))`. -/
lemma qiRayLvlLower (n : ℕ) (hI : Submission.Mostow.HypIsometryProp n)
    (Φ : Submission.Mostow.E n → Submission.Mostow.E n) (K C : ℝ) (hK : 1 ≤ K)
    (hlow : ∀ u v, Submission.Mostow.hdist u v ≤ K * Submission.Mostow.hdist (Φ u) (Φ v) + C)
    (ξ : Submission.Mostow.E n) (hξ : ξ ∈ Submission.Mostow.Sph n) (t : ℝ) (ht : 0 ≤ t) :
    (t - C) / K - lvl (Φ (ray ξ 0)) ≤ lvl (Φ (ray ξ t)) := by
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have h1 : hdist (ray ξ 0) (ray ξ t) ≤ K * hdist (Φ (ray ξ 0)) (Φ (ray ξ t)) + C := hlow _ _
  rw [hdist_ray_ray ξ hξ 0 t, zero_sub, abs_neg, abs_of_nonneg ht] at h1
  have h2 : hdist (Φ (ray ξ 0)) (Φ (ray ξ t)) ≤ lvl (Φ (ray ξ 0)) + lvl (Φ (ray ξ t)) := by
    have h := hI.2.2.2.1 (Φ (ray ξ 0)) 0 (Φ (ray ξ t))
    rw [hI.2.1 (Φ (ray ξ 0)) 0] at h
    simpa [lvl] using h
  have h3 : (t - C) / K ≤ hdist (Φ (ray ξ 0)) (Φ (ray ξ t)) := by
    rw [div_le_iff₀ hK0]; linarith
  linarith

/-- Geometric tail bound: a sequence whose successive increments are bounded by the terms of a
geometric series is within `C r^j/(1-r)` of its limit at step `j`. -/
lemma geomTailBoundAux (n : ℕ) (x : ℕ → E n) (η : E n) (C r : ℝ) (hC : 0 ≤ C)
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hstep : ∀ k : ℕ, ‖x (k + 1) - x k‖ ≤ C * r ^ k)
    (hlim : Filter.Tendsto x Filter.atTop (nhds η)) :
    ∀ j : ℕ, ‖x j - η‖ ≤ C * r ^ j / (1 - r) := by
  intro j
  have hden : 0 < 1 - r := by linarith
  have hmain : ∀ m : ℕ, j ≤ m → ‖x j - x m‖ ≤ C * r ^ j / (1 - r) := by
    intro m hjm
    have htel : ∑ i ∈ Finset.range (m - j), (x (j + (i + 1)) - x (j + i)) = x m - x j := by
      have h := Finset.sum_range_sub (fun i => x (j + i)) (m - j)
      simp only [Nat.add_zero] at h
      rw [show j + (m - j) = m by omega] at h
      exact h
    have h1 : ‖x m - x j‖ ≤ ∑ i ∈ Finset.range (m - j), C * r ^ (j + i) := by
      rw [← htel]
      calc ‖∑ i ∈ Finset.range (m - j), (x (j + (i + 1)) - x (j + i))‖
          ≤ ∑ i ∈ Finset.range (m - j), ‖x (j + (i + 1)) - x (j + i)‖ := norm_sum_le _ _
        _ ≤ ∑ i ∈ Finset.range (m - j), C * r ^ (j + i) := by
              apply Finset.sum_le_sum
              intro i _
              have hidx : j + (i + 1) = (j + i) + 1 := by omega
              rw [hidx]
              exact hstep (j + i)
    have h2 : ∑ i ∈ Finset.range (m - j), C * r ^ (j + i)
        = C * r ^ j * (∑ i ∈ Finset.range (m - j), r ^ i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [pow_add]
      ring
    have h3 : ∑ i ∈ Finset.range (m - j), r ^ i = (r ^ (m - j) - 1) / (r - 1) :=
      geom_sum_eq (by linarith : r ≠ 1) (m - j)
    have h4 : (r ^ (m - j) - 1) / (r - 1) = (1 - r ^ (m - j)) / (1 - r) := by
      have e1 : r - 1 ≠ 0 := by linarith
      have e2 : 1 - r ≠ 0 := by linarith
      field_simp
      ring_nf
    have h5 : (1 - r ^ (m - j)) / (1 - r) ≤ 1 / (1 - r) := by
      apply div_le_div_of_nonneg_right _ (le_of_lt hden)
      have : 0 ≤ r ^ (m - j) := pow_nonneg hr0 _
      linarith
    calc ‖x j - x m‖ = ‖x m - x j‖ := norm_sub_rev _ _
      _ ≤ C * r ^ j * (1 / (1 - r)) := by
            rw [h2, h3, h4] at h1
            exact le_trans h1 (mul_le_mul_of_nonneg_left h5 (mul_nonneg hC (pow_nonneg hr0 j)))
      _ = C * r ^ j / (1 - r) := by rw [div_eq_mul_inv]; ring
  have htend : Filter.Tendsto (fun m : ℕ => ‖x j - x m‖) Filter.atTop (nhds ‖x j - η‖) := by
    have h1 : Filter.Tendsto (fun m : ℕ => x j - x m) Filter.atTop (nhds (x j - η)) :=
      tendsto_const_nhds.sub hlim
    exact (continuous_norm.tendsto _).comp h1
  exact le_of_tendsto htend (Filter.eventually_atTop.mpr ⟨j, fun m hm => hmain m hm⟩)

/-- The one-step bound of `qiRayStep`, converted into an explicit exponential estimate by
`sihn_lower_exp` and the linear lower bound on the levels. -/
lemma qiRayStepExp (n : ℕ) (hI : Submission.Mostow.HypIsometryProp n)
    (Φ : Submission.Mostow.E n → Submission.Mostow.E n) (K C : ℝ) (hK : 1 ≤ K) (hC : 0 ≤ C)
    (hup : ∀ u v, Submission.Mostow.hdist (Φ u) (Φ v) ≤ K * Submission.Mostow.hdist u v + C)
    (ξ : Submission.Mostow.E n) (hξ : ξ ∈ Submission.Mostow.Sph n)
    (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : |s - t| ≤ 1)
    (hsL : (s - C) / K - lvl (Φ (ray ξ 0)) ≤ lvl (Φ (ray ξ s)))
    (htL : (t - C) / K - lvl (Φ (ray ξ 0)) ≤ lvl (Φ (ray ξ t)))
    (hs1 : 1 ≤ lvl (Φ (ray ξ s))) (ht1 : 1 ≤ lvl (Φ (ray ξ t))) :
    ‖dirv (Φ (ray ξ s)) - dirv (Φ (ray ξ t))‖ ≤
      Real.sqrt (32 * (Real.cosh (K + C) - 1)) * Real.exp (C / K + lvl (Φ (ray ξ 0))) *
        Real.exp (-((s + t) / (2 * K))) := by
  set P : ℝ := Real.exp (C / K + lvl (Φ (ray ξ 0))) with hP
  have hPpos : 0 < P := Real.exp_pos _
  set M : ℝ := Real.cosh (K + C) - 1 with hM
  -- exponential lower bounds on the levels
  have hes : Real.exp (s / K) / P ≤ Real.exp (lvl (Φ (ray ξ s))) := by
    have h1 : s / K - (C / K + lvl (Φ (ray ξ 0))) ≤ lvl (Φ (ray ξ s)) := by
      have h0 : s / K - (C / K + lvl (Φ (ray ξ 0))) = (s - C) / K - lvl (Φ (ray ξ 0)) := by ring
      rw [h0]; exact hsL
    have h2 : Real.exp (s / K) / P = Real.exp (s / K - (C / K + lvl (Φ (ray ξ 0)))) := by
      rw [hP, div_eq_mul_inv, ← Real.exp_neg, ← Real.exp_add]
      congr 1
    rw [h2]
    exact Real.exp_le_exp.mpr h1
  have het : Real.exp (t / K) / P ≤ Real.exp (lvl (Φ (ray ξ t))) := by
    have h1 : t / K - (C / K + lvl (Φ (ray ξ 0))) ≤ lvl (Φ (ray ξ t)) := by
      have h0 : t / K - (C / K + lvl (Φ (ray ξ 0))) = (t - C) / K - lvl (Φ (ray ξ 0)) := by ring
      rw [h0]; exact htL
    have h2 : Real.exp (t / K) / P = Real.exp (t / K - (C / K + lvl (Φ (ray ξ 0)))) := by
      rw [hP, div_eq_mul_inv, ← Real.exp_neg, ← Real.exp_add]
      congr 1
    rw [h2]
    exact Real.exp_le_exp.mpr h1
  -- the corresponding `sinh` lower bounds
  have hsLB : Real.exp (s / K) / P / 4 ≤ Real.sinh (lvl (Φ (ray ξ s))) := by
    have h : Real.exp (lvl (Φ (ray ξ s))) / 4 ≤ Real.sinh (lvl (Φ (ray ξ s))) :=
      sinh_lower_exp _ hs1
    linarith
  have htLB : Real.exp (t / K) / P / 4 ≤ Real.sinh (lvl (Φ (ray ξ t))) := by
    have h : Real.exp (lvl (Φ (ray ξ t))) / 4 ≤ Real.sinh (lvl (Φ (ray ξ t))) :=
      sinh_lower_exp _ ht1
    linarith
  have hMnn : 0 ≤ M := by rw [hM]; linarith [Real.one_le_cosh (K + C)]
  -- reciprocal of the product of the two `sinh`s
  have hposprod : 0 < Real.exp (s / K) / P / 4 * (Real.exp (t / K) / P / 4) :=
    mul_pos (div_pos (div_pos (Real.exp_pos _) hPpos) (by norm_num))
      (div_pos (div_pos (Real.exp_pos _) hPpos) (by norm_num))
  have hprod : Real.exp (s / K) / P / 4 * (Real.exp (t / K) / P / 4) ≤
      Real.sinh (lvl (Φ (ray ξ s))) * Real.sinh (lvl (Φ (ray ξ t))) :=
    mul_le_mul hsLB htLB (le_of_lt (div_pos (div_pos (Real.exp_pos _) hPpos) (by norm_num)))
      (le_of_lt (Real.sinh_pos_iff.mpr (by linarith)))
  have hone : 1 / (Real.sinh (lvl (Φ (ray ξ s))) * Real.sinh (lvl (Φ (ray ξ t)))) ≤
      1 / (Real.exp (s / K) / P / 4 * (Real.exp (t / K) / P / 4)) :=
    one_div_le_one_div_of_le hposprod hprod
  have hval : 1 / (Real.exp (s / K) / P / 4 * (Real.exp (t / K) / P / 4)) =
      16 * P ^ 2 * Real.exp (-((s + t) / K)) := by
    rw [show -((s + t) / K) = -(s / K) + -(t / K) by ring, Real.exp_add, Real.exp_neg, Real.exp_neg]
    field_simp
    ring
  have hrec : (Real.sinh (lvl (Φ (ray ξ s))) * Real.sinh (lvl (Φ (ray ξ t))))⁻¹ ≤
      16 * P ^ 2 * Real.exp (-((s + t) / K)) := by
    rw [← one_div]
    rw [hval] at hone
    exact hone
  -- combine with the law-of-cosines step bound
  have hbase := qiRayStep n hI Φ K C hK hC hup ξ hξ s t hst hs1 ht1
  have hkey : 2 * M / (Real.sinh (lvl (Φ (ray ξ s))) * Real.sinh (lvl (Φ (ray ξ t)))) ≤
      (Real.sqrt (32 * M) * P * Real.exp (-((s + t) / (2 * K)))) ^ 2 := by
    have h1 : 2 * M / (Real.sinh (lvl (Φ (ray ξ s))) * Real.sinh (lvl (Φ (ray ξ t))))
        ≤ 2 * M * (16 * P ^ 2 * Real.exp (-((s + t) / K))) := by
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left hrec (by linarith)
    have h2 : 2 * M * (16 * P ^ 2 * Real.exp (-((s + t) / K))) =
        (Real.sqrt (32 * M) * P * Real.exp (-((s + t) / (2 * K)))) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (mul_nonneg (by norm_num) hMnn),
        show (Real.exp (-((s + t) / (2 * K)))) ^ 2 = Real.exp (-((s + t) / K)) by
          rw [sq, ← Real.exp_add]; congr 1; ring]
      ring
    linarith
  have hsq := Real.sqrt_le_sqrt hkey
  have hsqnn : 0 ≤ Real.sqrt (32 * M) * P * Real.exp (-((s + t) / (2 * K))) :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (le_of_lt hPpos)) (Real.exp_pos _).le
  rw [Real.sqrt_sq hsqnn] at hsq
  calc ‖dirv (Φ (ray ξ s)) - dirv (Φ (ray ξ t))‖
      ≤ Real.sqrt (2 * M / (Real.sinh (lvl (Φ (ray ξ s))) * Real.sinh (lvl (Φ (ray ξ t))))) := by
        rw [← hM] at hbase
        exact hbase
    _ ≤ Real.sqrt (32 * M) * P * Real.exp (-((s + t) / (2 * K))) := hsq
    _ = Real.sqrt (32 * (Real.cosh (K + C) - 1)) * Real.exp (C / K + lvl (Φ (ray ξ 0))) *
          Real.exp (-((s + t) / (2 * K))) := by rw [← hM, ← hP]

theorem qiRayLimit (n : ℕ) (hI : Submission.Mostow.HypIsometryProp n) (Φ : Submission.Mostow.E n → Submission.Mostow.E n)
    (K C : ℝ) (hK : 1 ≤ K) (hC : 0 ≤ C)
    (hup : ∀ u v, Submission.Mostow.hdist (Φ u) (Φ v) ≤ K * Submission.Mostow.hdist u v + C)
    (hlow : ∀ u v, Submission.Mostow.hdist u v ≤ K * Submission.Mostow.hdist (Φ u) (Φ v) + C)
    (ξ : Submission.Mostow.E n) (hξ : ξ ∈ Submission.Mostow.Sph n) :
    ∃ η ∈ Submission.Mostow.Sph n,
      Filter.Tendsto (fun k : ℕ => Work.Mostow.BdExt.dirv (Φ (Work.Mostow.BdExt.ray ξ k))) Filter.atTop (nhds η) ∧
      ∃ C₄ : ℝ, 0 ≤ C₄ ∧ ∀ t : ℝ, 0 ≤ t →
        ‖Work.Mostow.BdExt.dirv (Φ (Work.Mostow.BdExt.ray ξ t)) - η‖ ≤ C₄ * Real.exp (-(t / (2 * K))) := by
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  set L0 : ℝ := lvl (Φ (ray ξ 0)) with hL0
  have hL0nn : 0 ≤ L0 := by rw [hL0]; exact hI.1 0 _
  set T0 : ℝ := K * (L0 + 1) + C with hT0
  have hT0nn : 0 ≤ T0 := by
    rw [hT0]
    have : 0 ≤ K * (L0 + 1) := mul_nonneg (le_trans zero_le_one hK) (by linarith)
    linarith
  have hlev1 : ∀ t : ℝ, T0 ≤ t → 1 ≤ lvl (Φ (ray ξ t)) := by
    intro t ht
    have ht0 : 0 ≤ t := le_trans hT0nn ht
    have h1 := qiRayLvlLower n hI Φ K C hK hlow ξ hξ t ht0
    rw [← hL0] at h1
    have h2 : L0 + 1 ≤ (t - C) / K := by
      rw [hT0] at ht
      rw [le_div_iff₀ hK0]
      linarith
    linarith
  -- the constant of the exponential step bound
  set C2 : ℝ := Real.sqrt (32 * (Real.cosh (K + C) - 1)) * Real.exp (C / K + L0) with hC2
  have hC2nn : 0 ≤ C2 := by rw [hC2]; positivity
  have hstep : ∀ s t : ℝ, T0 ≤ s → T0 ≤ t → |s - t| ≤ 1 →
      ‖dirv (Φ (ray ξ s)) - dirv (Φ (ray ξ t))‖ ≤ C2 * Real.exp (-((s + t) / (2 * K))) := by
    intro s t hs ht hst
    have hsL := qiRayLvlLower n hI Φ K C hK hlow ξ hξ s (le_trans hT0nn hs)
    have htL := qiRayLvlLower n hI Φ K C hK hlow ξ hξ t (le_trans hT0nn ht)
    rw [← hL0] at hsL htL
    have h := qiRayStepExp n hI Φ K C hK hC hup ξ hξ s t (le_trans hT0nn hs) (le_trans hT0nn ht)
      hst hsL htL (hlev1 s hs) (hlev1 t ht)
    rw [hC2, hL0]
    exact h
  -- the integer sequence of directions
  set N : ℕ := Nat.ceil T0 with hN
  have hNT0 : T0 ≤ (N : ℝ) := by rw [hN]; exact Nat.le_ceil T0
  have hNle : ∀ k : ℕ, T0 ≤ ((N + k : ℕ) : ℝ) := fun k =>
    le_trans hNT0 (Nat.cast_le.mpr (Nat.le_add_right N k))
  set r : ℝ := Real.exp (-(1 / K)) with hr
  have hr0 : 0 ≤ r := by rw [hr]; exact (Real.exp_pos _).le
  have hr1 : r < 1 := by
    rw [hr, Real.exp_lt_one_iff]
    have : (0 : ℝ) < 1 / K := div_pos zero_lt_one hK0
    linarith
  set A : ℝ := C2 * Real.exp (-(N : ℝ) / K) * Real.exp (-(1 / (2 * K))) with hA
  have hAnn : 0 ≤ A := by
    rw [hA]
    exact mul_nonneg (mul_nonneg hC2nn (Real.exp_pos _).le) (Real.exp_pos _).le
  set x : ℕ → E n := fun k => dirv (Φ (ray ξ ((N + k : ℕ) : ℝ))) with hx
  have hxstep : ∀ k : ℕ, ‖x (k + 1) - x k‖ ≤ A * r ^ k := by
    intro k
    have hs : T0 ≤ ((N + k : ℕ) : ℝ) := hNle k
    have ht : T0 ≤ ((N + (k + 1) : ℕ) : ℝ) := hNle (k + 1)
    have hst : |((N + k : ℕ) : ℝ) - ((N + (k + 1) : ℕ) : ℝ)| ≤ 1 := by
      rw [abs_of_nonpos (by push_cast; norm_num)]
      push_cast
      norm_num
    have h1 := hstep ((N + k : ℕ) : ℝ) ((N + (k + 1) : ℕ) : ℝ) hs ht hst
    have h_exp_s : Real.exp (-(((N + k : ℕ) : ℝ) / K)) =
        Real.exp (-(N : ℝ) / K) * Real.exp (-(k : ℝ) / K) := by
      rw [Nat.cast_add, ← Real.exp_add]; congr 1; ring
    have h_pow : Real.exp (-(k : ℝ) / K) = (Real.exp (-(1 / K))) ^ k := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    have h2 : C2 * Real.exp (-((((N + k : ℕ) : ℝ) + ((N + (k + 1) : ℕ) : ℝ)) / (2 * K))) = A * r ^ k := by
      rw [hA, hr]
      rw [show ((N + (k + 1) : ℕ) : ℝ) = ((N + k : ℕ) : ℝ) + 1 by push_cast; ring]
      rw [show -((((N + k : ℕ) : ℝ) + (((N + k : ℕ) : ℝ) + 1)) / (2 * K)) =
          -(((N + k : ℕ) : ℝ) / K) + -(1 / (2 * K)) by ring]
      rw [Real.exp_add, h_exp_s, h_pow]
      ring_nf
    simp only [hx]
    rw [norm_sub_rev]
    exact le_trans h1 (le_of_eq h2)
  have hsumm : Summable (fun k : ℕ => A * r ^ k) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left A
  obtain ⟨η, hη⟩ := stepSum n x (fun k : ℕ => A * r ^ k)
    (fun k => mul_nonneg hAnn (pow_nonneg hr0 k)) hsumm hxstep
  have htail := geomTailBoundAux n x η A r hAnn hr0 hr1 hxstep hη
  have hr1' : 0 < 1 - r := by linarith
  set C3 : ℝ := C2 * Real.exp (-(1 / (2 * K))) / (1 - r) with hC3
  have hC3nn : 0 ≤ C3 := by
    rw [hC3]
    exact div_nonneg (mul_nonneg hC2nn (Real.exp_pos _).le) (le_of_lt hr1')
  have htail' : ∀ j : ℕ, ‖x j - η‖ ≤ C3 * Real.exp (-(((N + j : ℕ) : ℝ)) / K) := by
    intro j
    have h := htail j
    have key : A * r ^ j / (1 - r) = C3 * Real.exp (-(((N + j : ℕ) : ℝ)) / K) := by
      rw [hA, hC3, hr]
      have h1' : Real.exp (-(N : ℝ) / K) * Real.exp (-(↑j / K)) =
          Real.exp (-((N : ℝ) + (j : ℝ)) / K) := by
        rw [← Real.exp_add]; congr 1; ring
      calc C2 * Real.exp (-(N : ℝ) / K) * Real.exp (-(1 / (2 * K))) * (Real.exp (-(1 / K))) ^ j / (1 - r)
          = C2 * Real.exp (-(N : ℝ) / K) * Real.exp (-(1 / (2 * K))) * Real.exp (-(↑j / K)) / (1 - r) := by
              rw [← Real.exp_nat_mul, show (↑j : ℝ) * (-(1 / K)) = -(↑j / K) by ring]
        _ = C2 * (Real.exp (-(N : ℝ) / K) * Real.exp (-(↑j / K))) * Real.exp (-(1 / (2 * K))) / (1 - r) := by
              ring
        _ = C2 * Real.exp (-((N : ℝ) + (j : ℝ)) / K) * Real.exp (-(1 / (2 * K))) / (1 - r) := by
              rw [h1']
        _ = (C2 * Real.exp (-(1 / (2 * K))) / (1 - r)) * Real.exp (-((N + j : ℕ) : ℝ) / K) := by
              rw [Nat.cast_add]; ring
    rw [key] at h
    exact h
  have hint : ∀ m : ℕ, N ≤ m → ‖dirv (Φ (ray ξ (m : ℝ))) - η‖ ≤ C3 * Real.exp (-(m : ℝ) / K) := by
    intro m hm
    have h := htail' (m - N)
    have hidx : N + (m - N) = m := Nat.add_sub_cancel' hm
    rw [hidx] at h
    have hx' : x (m - N) = dirv (Φ (ray ξ (m : ℝ))) := by
      simp only [hx]
      rw [hidx]
    rwa [hx'] at h
  -- boundary point
  have hxnorm : ∀ j : ℕ, ‖x j‖ = 1 := by
    intro j
    have hne : Φ (ray ξ ((N + j : ℕ) : ℝ)) ≠ 0 := by
      intro h0
      have hz : lvl (0 : E n) = 0 := (hI.2.2.1 0 0).mpr rfl
      have h1 := hlev1 ((N + j : ℕ) : ℝ) (hNle j)
      rw [h0, hz] at h1
      linarith
    have h2 : ‖x j‖ = ‖dirv (Φ (ray ξ ((N + j : ℕ) : ℝ)))‖ := by simp only [hx]
    rw [h2, norm_dirv _ hne]
  have hη_sph : η ∈ Sph n := by
    rw [mem_Sph_iff]
    have htend : Filter.Tendsto (fun j : ℕ => ‖x j‖) Filter.atTop (nhds ‖η‖) :=
      (continuous_norm.tendsto η).comp hη
    have hconst : (fun j : ℕ => ‖x j‖) = fun _ => (1 : ℝ) := funext hxnorm
    rw [hconst] at htend
    exact (tendsto_nhds_unique tendsto_const_nhds htend).symm
  have hη1 : ‖η‖ = 1 := (mem_Sph_iff η).mp hη_sph
  set C4 : ℝ := max (C2 + C3) (2 * Real.exp (T0 / (2 * K))) with hC4
  have hC4nn : 0 ≤ C4 := le_trans (by linarith) (le_max_left _ _)
  have hreal : ∀ t : ℝ, 0 ≤ t → ‖dirv (Φ (ray ξ t)) - η‖ ≤ C4 * Real.exp (-(t / (2 * K))) := by
    intro t ht
    by_cases hTt : T0 ≤ t
    · set m : ℕ := Nat.ceil t with hm
      have htm : t ≤ (m : ℝ) := by rw [hm]; exact Nat.le_ceil t
      have hmt : (m : ℝ) < t + 1 := by rw [hm]; exact Nat.ceil_lt_add_one ht
      have hNm : N ≤ m := by rw [hN, hm]; exact Nat.ceil_mono hTt
      have hmT0 : T0 ≤ (m : ℝ) := le_trans hTt htm
      have hst : |t - (m : ℝ)| ≤ 1 := by
        rw [abs_of_nonpos (by linarith)]
        linarith
      have h1 : ‖dirv (Φ (ray ξ t)) - dirv (Φ (ray ξ (m : ℝ)))‖ ≤
          C2 * Real.exp (-((t + (m : ℝ)) / (2 * K))) := hstep t (m : ℝ) hTt hmT0 hst
      have h2 := hint m hNm
      have h3 : ‖dirv (Φ (ray ξ t)) - η‖ ≤
          C2 * Real.exp (-((t + (m : ℝ)) / (2 * K))) + C3 * Real.exp (-(m : ℝ) / K) := by
        calc ‖dirv (Φ (ray ξ t)) - η‖
            = ‖(dirv (Φ (ray ξ t)) - dirv (Φ (ray ξ (m : ℝ)))) +
                (dirv (Φ (ray ξ (m : ℝ))) - η)‖ := by rw [sub_add_sub_cancel]
          _ ≤ ‖dirv (Φ (ray ξ t)) - dirv (Φ (ray ξ (m : ℝ)))‖ +
                ‖dirv (Φ (ray ξ (m : ℝ))) - η‖ := norm_add_le _ _
          _ ≤ _ := add_le_add h1 h2
      have h4a : Real.exp (-((t + (m : ℝ)) / (2 * K))) ≤ Real.exp (-(t / K)) := by
        apply Real.exp_le_exp.mpr
        rw [neg_le_neg_iff, show t / K = (2 * t) / (2 * K) by ring,
          div_le_div_iff_of_pos_right (by linarith : (0 : ℝ) < 2 * K)]
        linarith
      have h4b : Real.exp (-(m : ℝ) / K) ≤ Real.exp (-(t / K)) := by
        apply Real.exp_le_exp.mpr
        rw [neg_div, neg_le_neg_iff]
        exact div_le_div_of_nonneg_right htm (le_of_lt hK0)
      have h4c : C2 * Real.exp (-((t + (m : ℝ)) / (2 * K))) + C3 * Real.exp (-(m : ℝ) / K) ≤
          (C2 + C3) * Real.exp (-(t / K)) := by
        have e1 := mul_le_mul_of_nonneg_left h4a hC2nn
        have e2 := mul_le_mul_of_nonneg_left h4b hC3nn
        have e3 : C2 * Real.exp (-(t / K)) + C3 * Real.exp (-(t / K)) =
            (C2 + C3) * Real.exp (-(t / K)) := by ring
        linarith [e1, e2, e3]
      have h5 : Real.exp (-(t / K)) ≤ Real.exp (-(t / (2 * K))) := by
        apply Real.exp_le_exp.mpr
        rw [neg_le_neg_iff, show t / K = (2 * t) / (2 * K) by ring,
          div_le_div_iff_of_pos_right (by linarith : (0 : ℝ) < 2 * K)]
        linarith
      have h6 : (C2 + C3) * Real.exp (-(t / K)) ≤ C4 * Real.exp (-(t / (2 * K))) :=
        mul_le_mul (le_max_left _ _) h5 (le_of_lt (Real.exp_pos _)) hC4nn
      linarith [h3, h4c, h6]
    · have htT : t < T0 := not_le.mp hTt
      have h2 : ‖dirv (Φ (ray ξ t)) - η‖ ≤ 2 := by
        calc ‖dirv (Φ (ray ξ t)) - η‖ ≤ ‖dirv (Φ (ray ξ t))‖ + ‖η‖ := norm_sub_le _ _
          _ ≤ 1 + 1 := by
              have e1 := dirv_norm_le_one (Φ (ray ξ t))
              linarith
          _ = 2 := by norm_num
      have h3 : (2 : ℝ) ≤ (2 * Real.exp (T0 / (2 * K))) * Real.exp (-(t / (2 * K))) := by
        have e1 : Real.exp (T0 / (2 * K)) * Real.exp (-(t / (2 * K))) =
            Real.exp ((T0 - t) / (2 * K)) := by
          rw [← Real.exp_add]; congr 1; ring
        have e2 : 1 ≤ Real.exp ((T0 - t) / (2 * K)) := Real.one_le_exp_iff.mpr (by positivity)
        have e3 : (2 : ℝ) * (Real.exp (T0 / (2 * K)) * Real.exp (-(t / (2 * K)))) =
            (2 * Real.exp (T0 / (2 * K))) * Real.exp (-(t / (2 * K))) := by ring
        linarith [e1, e2, e3]
      have h4 : (2 * Real.exp (T0 / (2 * K))) * Real.exp (-(t / (2 * K))) ≤
          C4 * Real.exp (-(t / (2 * K))) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (le_of_lt (Real.exp_pos _))
      linarith [h2, h3, h4]
  refine ⟨η, hη_sph, ?_, C4, hC4nn, hreal⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun k => norm_nonneg _)
    (fun k => hreal (k : ℝ) (Nat.cast_nonneg k)) ?_
  have hr2nn : 0 ≤ Real.exp (-(1 / (2 * K))) := (Real.exp_pos _).le
  have hr2lt : Real.exp (-(1 / (2 * K))) < 1 := by
    rw [Real.exp_lt_one_iff]
    have : (0 : ℝ) < 1 / (2 * K) := by positivity
    linarith
  have hpc := (tendsto_pow_atTop_nhds_zero_of_lt_one hr2nn hr2lt).const_mul C4
  have hfun : (fun k : ℕ => C4 * Real.exp (-((k : ℝ) / (2 * K)))) =
      fun k : ℕ => C4 * (Real.exp (-(1 / (2 * K)))) ^ k := by
    funext k
    rw [show -((k : ℝ) / (2 * K)) = (k : ℝ) * (-(1 / (2 * K))) by ring, Real.exp_nat_mul]
  rw [hfun]
  simpa using hpc

end

end Work.Mostow.BdExt
