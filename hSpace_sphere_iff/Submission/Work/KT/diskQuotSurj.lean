import Mathlib
import Submission.Work.KT.DiskAux

/-!
# Surjectivity of the quotient map `D^d → S^d`

The map `qc d : C(Ball (Euc d), Sph (ModelSphere d))` of `Submission.Work.KT.DiskAux` collapses
the boundary sphere `S^{d-1}` of the closed disc `D^d` to the north pole of `S^d`.  This file
proves `Work.KT.diskQuotSurj`, namely that it is surjective.

The proof is explicit: a point of `S^d` is a pair `(v, t)` with `‖v‖² + t² = 1`; taking the radial
parameter `r = arccos(-t)/π ∈ [0,1]` one has `cos (π r) = -t` and `sin (π r) = ‖v‖`, so the
preimage is `x = (sfun r)⁻¹ • v` when `r < 1` (it has `‖x‖ = r`), and any boundary point when
`r = 1` (where necessarily `t = 1` and `v = 0`).
-/

namespace Work.KT

noncomputable section

/-- `sfun` is positive on `[0, 1)`. -/
lemma sfun_pos {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) : 0 < sfun r := by
  rcases eq_or_lt_of_le h0 with h | h
  · subst h; rw [sfun_zero]; exact Real.pi_pos
  · have hmul : sfun r * r = Real.sin (Real.pi * r) := sfun_mul r
    have hπr : 0 < Real.pi * r := mul_pos Real.pi_pos h
    have hlt : Real.pi * r < Real.pi := by nlinarith [Real.pi_pos]
    have hsin : 0 < Real.sin (Real.pi * r) := Real.sin_pos_of_pos_of_lt_pi hπr hlt
    have hpos : 0 < sfun r * r := by rw [hmul]; exact hsin
    have hmulpos : 0 < r * sfun r := by rw [mul_comm]; exact hpos
    exact pos_of_mul_pos_right hmulpos h.le

/-- Every point of the model sphere `S^d` is the image under `qMapDisk d` of a point of the closed
disc `D^d`.  This is the unbundled form of `diskQuotSurj`. -/
lemma exists_qMapDisk_eq (d : ℕ) (hd : 1 ≤ d) (Y : ModelSphere d) (hY : ‖Y‖ = 1) :
    ∃ x : Ball (Euc d), qMapDisk d x = Y := by
  set v : Euc d := Y.fst with hv
  set t : ℝ := Y.snd with ht
  have hYmk : WithLp.toLp 2 (v, t) = Y := by rw [hv, ht]; rfl
  have hsq : ‖v‖ ^ 2 + t ^ 2 = 1 := by
    have h := WithLp.prod_norm_sq_eq_of_L2 Y
    rw [hY, one_pow, ← hv, ← ht, Real.norm_eq_abs, sq_abs] at h
    linarith
  have ht1 : t ^ 2 ≤ 1 := by nlinarith [sq_nonneg ‖v‖]
  have hlow : -1 ≤ t := (abs_le.mp ((sq_le_one_iff_abs_le_one t).mp ht1)).1
  have hupp : t ≤ 1 := (abs_le.mp ((sq_le_one_iff_abs_le_one t).mp ht1)).2
  set r : ℝ := radialAngle t with hr
  have hr0 : 0 ≤ r := by rw [hr]; exact radialAngle_nonneg t
  have hr1le : r ≤ 1 := by rw [hr]; exact radialAngle_le_one t
  have hcos : Real.cos (Real.pi * r) = -t := by rw [hr]; exact cos_radialAngle hlow hupp
  have hsin : Real.sin (Real.pi * r) = Real.sqrt (1 - t ^ 2) := by
    rw [hr]; exact sin_radialAngle t
  have hvnorm : ‖v‖ = Real.sqrt (1 - t ^ 2) := by
    have h2 : ‖v‖ ^ 2 = 1 - t ^ 2 := by linarith
    rw [← h2, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg v)]
  have hsinv : Real.sin (Real.pi * r) = ‖v‖ := by rw [hsin, hvnorm]
  by_cases hr1 : r = 1
  · -- the north pole case: `t = 1`, `v = 0`, any boundary point works
    have ht_one : t = 1 := by
      have h := hcos
      rw [hr1, mul_one, Real.cos_pi] at h
      linarith
    have hv0 : v = 0 := by
      have hnsq : ‖v‖ ^ 2 = 0 := by nlinarith [hsq, ht_one]
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnsq)
    have hbnd : (unitVec d hd) ∈ Metric.closedBall (0 : Euc d) 1 := by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_unitVec]
    refine ⟨⟨unitVec d hd, hbnd⟩, ?_⟩
    rw [← hYmk]
    unfold qMapDisk
    rw [show ((⟨unitVec d hd, hbnd⟩ : Ball (Euc d)) : Euc d) = unitVec d hd from rfl,
      (WithLp.toLp_injective 2).eq_iff, Prod.mk.injEq]
    refine ⟨?_, ?_⟩
    · rw [norm_unitVec, sfun_one, zero_smul, hv0]
    · rw [norm_unitVec, mul_one, Real.cos_pi, neg_neg, ht_one]
  · -- the interior case `r < 1`: the preimage is `x = (sfun r)⁻¹ • v`
    have hrlt : r < 1 := lt_of_le_of_ne hr1le hr1
    have hsne : sfun r ≠ 0 := sfun_ne_zero hr0 hrlt
    have hspos : 0 < sfun r := sfun_pos hr0 hrlt
    have hvn : ‖v‖ = sfun r * r := by
      rw [hvnorm, ← hsin, ← sfun_mul]
    set xv : Euc d := (sfun r)⁻¹ • v with hxv
    have hxvnorm : ‖xv‖ = r := by
      rw [hxv, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hspos), hvn]
      rw [← mul_assoc, inv_mul_cancel₀ hsne, one_mul]
    have hbnd : xv ∈ Metric.closedBall (0 : Euc d) 1 := by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, hxvnorm]
      exact hr1le
    refine ⟨⟨xv, hbnd⟩, ?_⟩
    rw [← hYmk]
    unfold qMapDisk
    rw [show ((⟨xv, hbnd⟩ : Ball (Euc d)) : Euc d) = xv from rfl,
      (WithLp.toLp_injective 2).eq_iff, Prod.mk.injEq]
    refine ⟨?_, ?_⟩
    · rw [hxvnorm, hxv, smul_smul, mul_inv_cancel₀ hsne, one_smul]
    · rw [hxvnorm, hcos, neg_neg]

theorem diskQuotSurj (d : ℕ) (hd : 1 ≤ d) : Function.Surjective (qc d) := by
  intro y
  obtain ⟨x, hx⟩ := exists_qMapDisk_eq d hd (y : ModelSphere d) (by
    have h := Metric.mem_sphere.mp y.2
    rwa [dist_eq_norm, sub_zero] at h)
  exact ⟨x, Subtype.ext (by rw [qc_apply]; exact hx)⟩

end

end Work.KT
