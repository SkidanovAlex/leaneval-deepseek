import Mathlib
import Submission.Work.Whitney.ballPairMapDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Surjectivity of the ball-pair map

`Work.Whitney.ballPairVal` (`Submission/Work/Whitney/ballPairMapDefs.lean`) maps the standard
`p`-simplex into the closed unit ball of `ℝᵖ`, with norm equal to the cone level
`1 - (p+1)·minᵢ zᵢ`.  Here we prove that it is **onto**: for every `v` with `‖v‖ ≤ 1` there is a
point of the simplex with `ballPairVal p z = v`.

The construction: for `v ≠ 0` let `u := ‖v‖⁻¹ • v` be the unit vector in its direction and

  `uu := (u 0, …, u (p-1), -∑ᵢ uᵢ) ∈ ℝ^{p+1}`,

so that `∑ uu = 0`; note `uu ≠ 0`, hence `minᵢ uuᵢ < 0`.  With `k := -minᵢ uuᵢ > 0` and
`s := ‖v‖ · ((p+1)k)⁻¹`, the point `z := c + s·uu` of the simplex (its coordinates are
`≥ c - s k = c - ‖v‖/(p+1) ≥ 0`) has

* `ballPairDis p z = s • u`, so `‖ballPairDis p z‖ = s`;
* `ballPairMin p z = c - s k`, so `ballPairLev p z = (p+1) s k = ‖v‖`;

whence `ballPairVal p z = (‖v‖ s⁻¹) • (s • u) = ‖v‖ • u = v`.  The barycentre covers `v = 0`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Whitney

open Work.Thom

noncomputable section

/-- The barycentre of `stdSimplex ℝ (Fin (p+1))`. -/
def ballPairCtrPoint (p : ℕ) : stdSimplex ℝ (Fin (p+1)) :=
  ⟨fun _ => ballPairCtr p, by
    refine ⟨fun _ => ?_, ?_⟩
    · rw [ballPairCtr]; positivity
    · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ballPairCtr]
      exact mul_inv_cancel₀ (by positivity)⟩

theorem ballPairDis_ctrPoint (p : ℕ) :
    ballPairDis p (ballPairCtrPoint p : Fin (p+1) → ℝ) = 0 := by
  rw [ballPairDis, WithLp.toLp_eq_zero]
  funext i
  change ballPairCtr p - ballPairCtr p = 0
  ring

theorem ballPairVal_ctrPoint (p : ℕ) :
    ballPairVal p (ballPairCtrPoint p : Fin (p+1) → ℝ) = 0 := by
  have h := ballPairLev_eq_zero_of_dis_eq_zero p (ballPairCtrPoint p) (ballPairDis_ctrPoint p)
  rw [ballPairVal, ballPairDis_ctrPoint p, h, zero_mul, zero_smul]

/-- The minimum of an affine function with nonnegative slope. -/
theorem ballPairMin_add_mul (p : ℕ) (w : Fin (p+1) → ℝ) {m : ℝ} (hm : 0 ≤ m) (c : ℝ) :
    ballPairMin p (fun i => c + m * w i) = c + m * ballPairMin p w := by
  unfold ballPairMin
  refine le_antisymm ?_ ?_
  · obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty w
    calc (Finset.univ : Finset (Fin (p+1))).inf' Finset.univ_nonempty (fun i => c + m * w i)
        ≤ c + m * w i := Finset.inf'_le _ (Finset.mem_univ i)
      _ = c + m * ((Finset.univ : Finset (Fin (p+1))).inf' Finset.univ_nonempty w) := by rw [hi]
  · refine Finset.le_inf' Finset.univ_nonempty (fun i => c + m * w i) (fun i _ => ?_)
    have h := Finset.inf'_le (s := Finset.univ) w (Finset.mem_univ i)
    nlinarith [h, hm]

/-- **The ball-pair map is onto the closed unit ball.** -/
theorem ballPairVal_surj (p : ℕ) (hp : 1 ≤ p) :
    Function.Surjective (fun z : stdSimplex ℝ (Fin (p+1)) =>
      (⟨ballPairVal p (z : Fin (p+1) → ℝ), ballPairVal_mem_ball p z⟩ : Work.Thom.MBall p)) := by
  intro w
  by_cases hv : (w : EuclideanSpace ℝ (Fin p)) = 0
  · refine ⟨ballPairCtrPoint p, ?_⟩
    apply Subtype.ext
    show ballPairVal p (ballPairCtrPoint p : Fin (p+1) → ℝ) = (w : EuclideanSpace ℝ (Fin p))
    rw [ballPairVal_ctrPoint p, hv]
  · have htpos : 0 < ‖(w : EuclideanSpace ℝ (Fin p))‖ := norm_pos_iff.mpr hv
    have htle : ‖(w : EuclideanSpace ℝ (Fin p))‖ ≤ 1 := w.2
    set u : EuclideanSpace ℝ (Fin p) := (‖(w : EuclideanSpace ℝ (Fin p))‖)⁻¹ •
      (w : EuclideanSpace ℝ (Fin p)) with hudef
    have hun : ‖u‖ = 1 := by
      rw [hudef, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
        inv_mul_cancel₀ (ne_of_gt htpos)]
    set uu : Fin (p+1) → ℝ :=
      Fin.snoc (fun i : Fin p => u.ofLp i) (-∑ i : Fin p, u.ofLp i) with huudef
    have huu_c : ∀ i : Fin p, uu i.castSucc = u.ofLp i := by intro i; simp [huudef]
    have huu_l : uu (Fin.last p) = -∑ i : Fin p, u.ofLp i := by simp [huudef]
    have huu_sum : ∑ i : Fin (p+1), uu i = 0 := by
      rw [Fin.sum_univ_castSucc]
      simp [huu_c, huu_l]
    have hmin_le : ballPairMin p uu ≤ 0 := by
      by_contra hcon
      have hcon' : 0 < ballPairMin p uu := not_le.mp hcon
      have hpos : 0 < ∑ i : Fin (p+1), uu i :=
        Finset.sum_pos (fun i _ => lt_of_lt_of_le hcon' (ballPairMin_le p uu i))
          Finset.univ_nonempty
      rw [huu_sum] at hpos
      exact lt_irrefl 0 hpos
    have hmin_ne : ballPairMin p uu ≠ 0 := by
      intro hzero
      have hnonneg : ∀ i ∈ (Finset.univ : Finset (Fin (p+1))), 0 ≤ uu i := by
        intro i _
        rw [← hzero]
        exact ballPairMin_le p uu i
      have hall := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp huu_sum
      have huoflp : u.ofLp = 0 := by
        funext i
        have h := hall i.castSucc (Finset.mem_univ _)
        rwa [huu_c i] at h
      have hu0 : u = 0 := by
        have h := (WithLp.toLp_ofLp 2 u).symm
        rw [show u.ofLp = (0 : Fin p → ℝ) from huoflp] at h
        simpa using h
      rw [hu0, norm_zero] at hun
      norm_num at hun
    have hmin_lt : ballPairMin p uu < 0 := lt_of_le_of_ne hmin_le hmin_ne
    set k : ℝ := -ballPairMin p uu with hkdef
    have hkpos : 0 < k := by rw [hkdef]; linarith
    have hkne : k ≠ 0 := ne_of_gt hkpos
    have hNne : (((p+1 : ℕ)) : ℝ) ≠ 0 := by positivity
    set s : ℝ := ‖(w : EuclideanSpace ℝ (Fin p))‖ * ((((p+1 : ℕ)) : ℝ) * k)⁻¹ with hsdef
    have hspos : 0 < s :=
      mul_pos htpos (inv_pos.mpr (mul_pos (by positivity) hkpos))
    have hsne : s ≠ 0 := ne_of_gt hspos
    have hsk : s * k = ‖(w : EuclideanSpace ℝ (Fin p))‖ * (((p+1 : ℕ)) : ℝ)⁻¹ := by
      have h1 : ((((p+1 : ℕ)) : ℝ) * k)⁻¹ * k = (((p+1 : ℕ)) : ℝ)⁻¹ := by
        rw [mul_inv, mul_assoc, inv_mul_cancel₀ hkne, mul_one]
      rw [hsdef, mul_assoc, h1]
    have hsk_le : s * k ≤ ballPairCtr p := by
      rw [hsk, ballPairCtr]
      have hNinv : 0 ≤ (((p+1 : ℕ)) : ℝ)⁻¹ := by positivity
      nlinarith [htle, hNinv]
    have hNsk : (((p+1 : ℕ)) : ℝ) * (s * k) = ‖(w : EuclideanSpace ℝ (Fin p))‖ := by
      rw [hsk]
      field_simp
    set zfun : Fin (p+1) → ℝ := fun i => ballPairCtr p + s * uu i with hzdef
    have hzmin : ballPairMin p zfun = ballPairCtr p + s * ballPairMin p uu := by
      rw [hzdef]
      exact ballPairMin_add_mul p uu (le_of_lt hspos) (ballPairCtr p)
    have hzmem : zfun ∈ stdSimplex ℝ (Fin (p+1)) := by
      refine ⟨fun i => ?_, ?_⟩
      · have h1 : ballPairMin p uu ≤ uu i := ballPairMin_le p uu i
        have h2 : s * ballPairMin p uu = -s * k := by rw [hkdef]; ring
        have h3 : ballPairCtr p + s * ballPairMin p uu = ballPairCtr p - s * k := by linarith
        have h4 : 0 ≤ ballPairCtr p - s * k := by linarith [hsk_le]
        have h5 : zfun i = ballPairCtr p + s * uu i := rfl
        have h6 : ballPairCtr p + s * ballPairMin p uu ≤ zfun i := by
          rw [h5]; linarith [mul_le_mul_of_nonneg_left h1 (le_of_lt hspos)]
        linarith [h3, h4, h6]
      · have hsum : ∑ i : Fin (p+1), (ballPairCtr p + s * uu i) = 1 := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, huu_sum,
            mul_zero, add_zero, ballPairCtr]
          exact mul_inv_cancel₀ (by positivity)
        simpa [hzdef] using hsum
    have hzdis : ballPairDis p zfun = s • u := by
      have hfun : (fun i : Fin p => zfun i.castSucc - ballPairCtr p) = s • u.ofLp := by
        funext i
        rw [hzdef]
        simp only [huu_c i, Pi.smul_apply, smul_eq_mul]
        ring
      rw [ballPairDis, hfun, WithLp.toLp_smul]
    have hzdisnorm : ‖ballPairDis p zfun‖ = s := by
      rw [hzdis, norm_smul, Real.norm_of_nonneg (le_of_lt hspos), hun, mul_one]
    have hzlev : ballPairLev p zfun = ‖(w : EuclideanSpace ℝ (Fin p))‖ := by
      have hNc : (((p+1 : ℕ)) : ℝ) * ballPairCtr p = 1 := by
        rw [ballPairCtr]
        exact mul_inv_cancel₀ (by positivity)
      have hmin_eq : ballPairMin p uu = -k := by rw [hkdef]; ring
      rw [ballPairLev, hzmin, hmin_eq]
      nlinarith [hNc, hNsk]
    refine ⟨⟨zfun, hzmem⟩, ?_⟩
    apply Subtype.ext
    show ballPairVal p zfun = (w : EuclideanSpace ℝ (Fin p))
    rw [ballPairVal, hzlev, hzdisnorm, hzdis, smul_smul, mul_assoc,
      inv_mul_cancel₀ hsne, mul_one, hudef, smul_smul,
      mul_inv_cancel₀ (ne_of_gt htpos), one_smul]

end

end Work.Whitney
