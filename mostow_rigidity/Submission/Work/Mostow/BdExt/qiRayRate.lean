import Mathlib
import Submission.Work.Mostow.BdExt.Basic
import Submission.Work.Mostow.BdExt.rayDist
import Submission.Work.Mostow.BdExt.lawCosines
import Submission.Work.Mostow.BdExt.stepSum
import Submission.Work.Mostow.BdExt.qiRayStep
import Submission.Work.Mostow.BdExt.qiRayLimit

/-!
# `qiRayRate`: exponential rate of convergence of the directions of a quasi-isometric ray

Let `Φ` be a `(K, C)`-quasi-isometry of the chart model `E n` of `ℍⁿ` and `ξ ∈ Sph n`.  Along the
geodesic ray `t ↦ ray ξ t` issued from the chart origin, the Euclidean directions
`t ↦ dirv (Φ (ray ξ t))` converge to a boundary point with rate `exp (-t/(2K))`.

Here we provide the *uniform* form of the statement: the constant `C₄` is required to work for
**all** boundary points `ξ` simultaneously, and the limit `η` is supplied by the caller (it is the
unique limit of the integer-indexed sequence of directions).

The mathematical content is the same "summable increments" argument as in `qiRayLimit`: the
hyperbolic level `lvl (Φ (ray ξ t))` grows at least as `t/K - (lvl (Φ 0) + C/K)`, and this bound is
*independent of `ξ`* because `ray ξ 0 = 0`; the quantitative law of cosines then gives exponentially
small increments which we sum geometrically.
-/

namespace Work.Mostow.BdExt

open Submission.Mostow

noncomputable section

variable {n : ℕ}

/-- The ray is issued from the chart origin, independently of its boundary point: `ray ξ 0 = 0`. -/
lemma ray_zero (ξ : E n) : ray ξ 0 = 0 := by simp [ray]

/-- A limit of vectors of norm at most one has norm at most one. -/
lemma dirv_limit_norm_le_one {Φ : E n → E n} {ξ η : E n}
    (hη : Filter.Tendsto (fun k : ℕ => dirv (Φ (ray ξ k))) Filter.atTop (nhds η)) :
    ‖η‖ ≤ 1 := by
  have hmem : ∀ k : ℕ, dirv (Φ (ray ξ k)) ∈ Metric.closedBall (0 : E n) 1 := by
    intro k
    rw [Metric.mem_closedBall, dist_zero_right]
    exact dirv_norm_le_one _
  have h := Metric.isClosed_closedBall.mem_of_tendsto hη (Filter.Eventually.of_forall hmem)
  rwa [Metric.mem_closedBall, dist_zero_right] at h

theorem qiRayRate (n : ℕ) (hI : Submission.Mostow.HypIsometryProp n) (Φ : Submission.Mostow.E n → Submission.Mostow.E n)
    (K C : ℝ) (hK : 1 ≤ K) (hC : 0 ≤ C)
    (hup : ∀ u v, Submission.Mostow.hdist (Φ u) (Φ v) ≤ K * Submission.Mostow.hdist u v + C)
    (hlow : ∀ u v, Submission.Mostow.hdist u v ≤ K * Submission.Mostow.hdist (Φ u) (Φ v) + C) :
    ∃ C₄ : ℝ, 0 ≤ C₄ ∧
      ∀ (ξ : Submission.Mostow.E n) (hξ : ξ ∈ Submission.Mostow.Sph n) (η : Submission.Mostow.E n)
        (hη : Filter.Tendsto (fun k : ℕ => Work.Mostow.BdExt.dirv (Φ (Work.Mostow.BdExt.ray ξ k)))
              Filter.atTop (nhds η)) (t : ℝ),
        0 ≤ t → ‖Work.Mostow.BdExt.dirv (Φ (Work.Mostow.BdExt.ray ξ t)) - η‖
          ≤ C₄ * Real.exp (-(t / (2 * K))) := by
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  -- ## ξ-independent constants
  set L0 : ℝ := lvl (Φ 0) with hL0
  have hL0nn : 0 ≤ L0 := by rw [hL0]; exact hI.1 0 (Φ 0)
  set T0 : ℝ := K * (L0 + 1) + C with hT0
  have hT0nn : 0 ≤ T0 := by
    rw [hT0]
    have h : 0 ≤ K * (L0 + 1) := mul_nonneg (le_trans zero_le_one hK) (by linarith)
    linarith
  set C2 : ℝ := Real.sqrt (32 * (Real.cosh (K + C) - 1)) * Real.exp (C / K + L0) with hC2
  have hC2nn : 0 ≤ C2 := by rw [hC2]; positivity
  set r : ℝ := Real.exp (-(1 / K)) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    rw [hr, Real.exp_lt_one_iff]
    have h : (0 : ℝ) < 1 / K := div_pos zero_lt_one hK0
    linarith
  set N : ℕ := Nat.ceil T0 with hN
  have hNT0 : T0 ≤ (N : ℝ) := by rw [hN]; exact Nat.le_ceil T0
  set A : ℝ := C2 * Real.exp (-(N : ℝ) / K) * Real.exp (-(1 / (2 * K))) with hA
  have hAnn : 0 ≤ A := by rw [hA]; positivity
  set C3 : ℝ := C2 * Real.exp (-(1 / (2 * K))) / (1 - r) with hC3
  have hC3nn : 0 ≤ C3 := by
    rw [hC3]
    exact div_nonneg (mul_nonneg hC2nn (Real.exp_pos _).le) (by linarith)
  set TT : ℝ := max T0 (N : ℝ) with hTT
  have hT0TT : T0 ≤ TT := hTT.symm ▸ le_max_left T0 (N : ℝ)
  have hNTT : (N : ℝ) ≤ TT := hTT.symm ▸ le_max_right T0 (N : ℝ)
  set C4 : ℝ := max (C2 + C3) (2 * Real.exp (TT / (2 * K))) with hC4
  have hC4nn : 0 ≤ C4 := by
    rw [hC4]
    exact le_trans (by linarith [hC2nn, hC3nn]) (le_max_left _ _)
  refine ⟨C4, hC4nn, ?_⟩
  intro ξ hξ η hη t ht
  have hray0 : ray ξ 0 = (0 : E n) := ray_zero ξ
  have hL0ray : lvl (Φ (ray ξ 0)) = L0 := by rw [hray0, ← hL0]
  -- ## the level of the image of a ray grows at least linearly, uniformly in `ξ`
  have hlev1 : ∀ s : ℝ, T0 ≤ s → 1 ≤ lvl (Φ (ray ξ s)) := by
    intro s hs
    have hs0 : 0 ≤ s := le_trans hT0nn hs
    have h1 := qiRayLvlLower n hI Φ K C hK hlow ξ hξ s hs0
    rw [hL0ray] at h1
    have h2 : L0 + 1 ≤ (s - C) / K := by
      rw [hT0] at hs
      rw [le_div_iff₀ hK0]
      linarith
    linarith
  -- ## the one-step bound, with the uniform constant `C2`
  have hstep : ∀ s u : ℝ, T0 ≤ s → T0 ≤ u → |s - u| ≤ 1 →
      ‖dirv (Φ (ray ξ s)) - dirv (Φ (ray ξ u))‖ ≤ C2 * Real.exp (-((s + u) / (2 * K))) := by
    intro s u hs hu hsu
    have hsL := qiRayLvlLower n hI Φ K C hK hlow ξ hξ s (le_trans hT0nn hs)
    have huL := qiRayLvlLower n hI Φ K C hK hlow ξ hξ u (le_trans hT0nn hu)
    have h := qiRayStepExp n hI Φ K C hK hC hup ξ hξ s u (le_trans hT0nn hs) (le_trans hT0nn hu)
      hsu hsL huL (hlev1 s hs) (hlev1 u hu)
    rw [hray0] at h
    rw [← hL0] at h
    rw [← hC2] at h
    exact h
  -- ## the integer-indexed tail
  set x : ℕ → E n := fun k => dirv (Φ (ray ξ ((k + N : ℕ) : ℝ))) with hx
  have hNle : ∀ k : ℕ, T0 ≤ ((k + N : ℕ) : ℝ) := by
    intro k
    have h1 : (N : ℝ) ≤ ((k + N : ℕ) : ℝ) := by
      have hcast : ((k + N : ℕ) : ℝ) = (k : ℝ) + (N : ℝ) := by push_cast; ring
      rw [hcast]
      linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℝ))]
    exact le_trans hNT0 h1
  have hxstep : ∀ k : ℕ, ‖x (k + 1) - x k‖ ≤ A * r ^ k := by
    intro k
    have hs : T0 ≤ ((k + 1 + N : ℕ) : ℝ) := by
      rw [show k + 1 + N = (k + 1) + N by omega]
      exact hNle (k + 1)
    have hu : T0 ≤ ((k + N : ℕ) : ℝ) := hNle k
    have hst : |((k + 1 + N : ℕ) : ℝ) - ((k + N : ℕ) : ℝ)| ≤ 1 := by
      have hidx : (k + 1 + N : ℕ) = (k + N) + 1 := by omega
      have hval : ((k + 1 + N : ℕ) : ℝ) - ((k + N : ℕ) : ℝ) = 1 := by
        rw [hidx]
        push_cast
        ring
      rw [hval]
      norm_num
    have h1 := hstep (((k + 1 + N : ℕ) : ℝ)) (((k + N : ℕ) : ℝ)) hs hu hst
    have h_exp_s : Real.exp (-(((k + N : ℕ) : ℝ) / K)) =
        Real.exp (-(N : ℝ) / K) * Real.exp (-(k : ℝ) / K) := by
      rw [← Real.exp_add]
      congr 1
      push_cast
      ring
    have h_pow : Real.exp (-(k : ℝ) / K) = (Real.exp (-(1 / K))) ^ k := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    have h2 : C2 * Real.exp (-((((k + 1 + N : ℕ) : ℝ) + ((k + N : ℕ) : ℝ)) / (2 * K))) =
        A * r ^ k := by
      rw [hA, hr]
      rw [show ((k + 1 + N : ℕ) : ℝ) = ((k + N : ℕ) : ℝ) + 1 by push_cast; ring]
      rw [show -(((((k + N : ℕ) : ℝ) + 1) + ((k + N : ℕ) : ℝ)) / (2 * K)) =
          -(((k + N : ℕ) : ℝ) / K) + -(1 / (2 * K)) by ring]
      rw [Real.exp_add, h_exp_s, h_pow]
      ring_nf
    simp only [hx]
    exact le_trans h1 (le_of_eq h2)
  have hsumm : Summable (fun k : ℕ => A * r ^ k) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left A
  obtain ⟨η₀, hη₀⟩ := stepSum n x (fun k : ℕ => A * r ^ k)
    (fun k => mul_nonneg hAnn (pow_nonneg hr0 k)) hsumm hxstep
  have htail := geomTailBoundAux n x η₀ A r hAnn hr0 hr1 hxstep hη₀
  have htail' : ∀ j : ℕ, ‖x j - η₀‖ ≤ C3 * Real.exp (-(((j + N : ℕ) : ℝ)) / K) := by
    intro j
    have h := htail j
    have key : A * r ^ j / (1 - r) = C3 * Real.exp (-(((j + N : ℕ) : ℝ)) / K) := by
      rw [hA, hC3, hr]
      have h1' : Real.exp (-(N : ℝ) / K) * Real.exp (-(↑j / K)) =
          Real.exp (-(((j + N : ℕ) : ℝ)) / K) := by
        rw [← Real.exp_add]
        congr 1
        push_cast
        ring
      calc C2 * Real.exp (-(N : ℝ) / K) * Real.exp (-(1 / (2 * K))) * (Real.exp (-(1 / K))) ^ j
              / (1 - r)
          = C2 * Real.exp (-(N : ℝ) / K) * Real.exp (-(1 / (2 * K))) * Real.exp (-(↑j / K))
              / (1 - r) := by
              rw [← Real.exp_nat_mul, show (↑j : ℝ) * (-(1 / K)) = -(↑j / K) by ring]
        _ = C2 * (Real.exp (-(N : ℝ) / K) * Real.exp (-(↑j / K))) * Real.exp (-(1 / (2 * K)))
              / (1 - r) := by ring
        _ = C2 * Real.exp (-(((j + N : ℕ) : ℝ)) / K) * Real.exp (-(1 / (2 * K))) / (1 - r) := by
              rw [h1']
        _ = (C2 * Real.exp (-(1 / (2 * K))) / (1 - r)) * Real.exp (-(((j + N : ℕ) : ℝ)) / K) := by
              ring
    rw [key] at h
    exact h
  have hshift : Filter.Tendsto x Filter.atTop (nhds η) :=
    (Filter.tendsto_add_atTop_iff_nat N).mpr hη
  have hx_eq : η₀ = η := tendsto_nhds_unique hη₀ hshift
  have hint : ∀ m : ℕ, N ≤ m → ‖dirv (Φ (ray ξ (m : ℝ))) - η‖ ≤ C3 * Real.exp (-(m : ℝ) / K) := by
    intro m hm
    have h := htail' (m - N)
    have hidx : (m - N) + N = m := Nat.sub_add_cancel hm
    rw [hidx] at h
    have hx' : x (m - N) = dirv (Φ (ray ξ (m : ℝ))) := by
      simp only [hx]
      rw [hidx]
    rw [hx', hx_eq] at h
    exact h
  -- ## the real parameter
  by_cases hTt : TT ≤ t
  · -- large `t`: compare with the integer `⌈t⌉`
    have htT0 : T0 ≤ t := le_trans hT0TT hTt
    have hNt : (N : ℝ) ≤ t := le_trans hNTT hTt
    set m : ℕ := Nat.ceil t with hm
    have htm : t ≤ (m : ℝ) := by rw [hm]; exact Nat.le_ceil t
    have hmt : (m : ℝ) < t + 1 := by rw [hm]; exact Nat.ceil_lt_add_one ht
    have hNm : N ≤ m := by
      rw [hN, hm]
      exact Nat.ceil_mono htT0
    have hmT0 : T0 ≤ (m : ℝ) := le_trans htT0 htm
    have hst : |t - (m : ℝ)| ≤ 1 := by
      rw [abs_of_nonpos (by linarith)]
      linarith
    have h1 : ‖dirv (Φ (ray ξ t)) - dirv (Φ (ray ξ (m : ℝ)))‖ ≤
        C2 * Real.exp (-((t + (m : ℝ)) / (2 * K))) := hstep t (m : ℝ) htT0 hmT0 hst
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
      mul_le_mul (hC4.symm ▸ le_max_left (C2 + C3) (2 * Real.exp (TT / (2 * K)))) h5
        (le_of_lt (Real.exp_pos _)) hC4nn
    linarith [h3, h4c, h6]
  · -- small `t`: the two directions are within `2` of each other
    have htT : t ≤ TT := le_of_lt (not_le.mp hTt)
    have h2a : ‖dirv (Φ (ray ξ t)) - η‖ ≤ 2 := by
      calc ‖dirv (Φ (ray ξ t)) - η‖ ≤ ‖dirv (Φ (ray ξ t))‖ + ‖η‖ := norm_sub_le _ _
        _ ≤ 1 + 1 := by
            have e1 := dirv_norm_le_one (Φ (ray ξ t))
            have e2 := dirv_limit_norm_le_one hη
            linarith
        _ = 2 := by norm_num
    have h2b : (2 : ℝ) ≤ 2 * Real.exp (TT / (2 * K)) * Real.exp (-(t / (2 * K))) := by
      have e1 : Real.exp (TT / (2 * K)) * Real.exp (-(t / (2 * K))) =
          Real.exp ((TT - t) / (2 * K)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have e2 : (1 : ℝ) ≤ Real.exp (TT / (2 * K)) * Real.exp (-(t / (2 * K))) := by
        rw [e1]
        exact Real.one_le_exp_iff.mpr (div_nonneg (by linarith) (by linarith))
      have e3 : (2 : ℝ) * (Real.exp (TT / (2 * K)) * Real.exp (-(t / (2 * K)))) =
          2 * Real.exp (TT / (2 * K)) * Real.exp (-(t / (2 * K))) := by ring
      linarith [mul_le_mul_of_nonneg_left e2 (by norm_num : (0 : ℝ) ≤ 2), e3]
    have h4 : (2 * Real.exp (TT / (2 * K))) * Real.exp (-(t / (2 * K))) ≤
        C4 * Real.exp (-(t / (2 * K))) :=
      mul_le_mul_of_nonneg_right
        (hC4.symm ▸ le_max_right (C2 + C3) (2 * Real.exp (TT / (2 * K))))
        (le_of_lt (Real.exp_pos _))
    exact le_trans h2a (le_trans h2b h4)

end

end Work.Mostow.BdExt
