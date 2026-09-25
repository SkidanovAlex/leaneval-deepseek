/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The Bochner–Martinelli Schauder estimate with `C^{0,α}` data

This file proves `Work.NN.Core.bmPotential_holder_one_of_holder`: for a *continuous*, bounded,
`α`-Hölder datum `f` supported in a polydisc, the Bochner–Martinelli potential gains one
derivative with a bound in terms of the sup and Hölder bounds of the datum:

  `‖bmPotential f‖_{C^{1,α}} ≤ C Σ_j (A_j + K_j)`.

The proof follows the classical route: approximate `f` by smooth data `G m`
(`Work.NN.Core.bmSmoothApprox`, which preserves both the sup bound and the Hölder constant and
converges pointwise), apply the *existing* `C¹`-data Calderón–Zygmund estimate
`Work.CR.Flat.Cauchy.bmPotential_holder_CZ` to each `G m` (uniformly in `m`), pass the resulting
*Taylor estimates* to the pointwise limit, and conclude differentiability of the limit together
with the bound by a compactness argument in the finite-dimensional space of linear maps.
-/
import Mathlib
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.CR.Flat.Cauchy.bmDefs
import Submission.Work.CR.Flat.Cauchy.bmCZDefs
import Submission.Work.CR.Flat.Cauchy.bmPotential_holder_CZ
import Submission.Work.CR.Flat.Cauchy.bmPotential_tendsto_of_tendsto
import Submission.Work.CR.Flat.Cauchy.bmPotential_iteratedFDeriv
import Submission.Work.CR.Flat.Cauchy.holderNorm_mul_le_of_hasCompactSupport
import Submission.Work.NN.Core.bmSmoothApprox
import Submission.Work.NN.Core.holderNorm_one_le_of_tendsto

noncomputable section

set_option maxHeartbeats 3200000

open scoped NNReal ENNReal Topology
open MeasureTheory Set Filter

namespace Work.NN.Core

variable {n : ℕ}

/-! ## Reading off pointwise bounds from a `C^{1,α}` bound -/

/-- The norm of a difference of first iterated derivatives agrees with the norm of the
difference of the Fréchet derivatives (the two are identified by the linear isometry
`continuousMultilinearCurryFin1`). -/
lemma norm_iteratedFDeriv_one_sub_eq (u : (Fin n → ℂ) → ℂ) (x y : Fin n → ℂ) :
    ‖iteratedFDeriv ℝ 1 u x - iteratedFDeriv ℝ 1 u y‖
      = ‖fderiv ℝ u x - fderiv ℝ u y‖ := by
  have key : ∀ z : Fin n → ℂ, continuousMultilinearCurryFin1 ℝ (Fin n → ℂ) ℂ
      (iteratedFDeriv ℝ 1 u z) = fderiv ℝ u z := by
    intro z
    ext v
    rw [continuousMultilinearCurryFin1_apply, iteratedFDeriv_one_apply]
    simp
  have h1 : iteratedFDeriv ℝ 1 u x - iteratedFDeriv ℝ 1 u y
      = (continuousMultilinearCurryFin1 ℝ (Fin n → ℂ) ℂ).symm
          (fderiv ℝ u x - fderiv ℝ u y) := by
    rw [map_sub]
    congr 1
    · rw [← key x, LinearIsometryEquiv.symm_apply_apply]
    · rw [← key y, LinearIsometryEquiv.symm_apply_apply]
  rw [h1, LinearIsometryEquiv.norm_map]

/-- From a `C^{1,α}` bound on an open set: the sup bound. -/
lemma norm_le_of_holderNorm_one_le {α B : ℝ} {P : Set (Fin n → ℂ)} {u : (Fin n → ℂ) → ℂ}
    (hB : 0 ≤ B) (h : Work.CR.Flat.holderNorm 1 α u P ≤ ENNReal.ofReal B)
    {x : Fin n → ℂ} (hx : x ∈ P) : ‖u x‖ ≤ B := by
  have h0 : Work.CR.Flat.iterDerivNorm 0 u P ≤ ENNReal.ofReal B :=
    (Work.CR.Flat.iterDerivNorm_le_holderNorm 1 α u P (by norm_num)).trans h
  rw [Work.CR.Flat.iterDerivNorm_zero] at h0
  have h1 : ENNReal.ofReal ‖u x‖ ≤ ENNReal.ofReal B :=
    le_trans (le_iSup₂_of_le x hx le_rfl) h0
  exact (ENNReal.ofReal_le_ofReal_iff hB).mp h1

/-- From a `C^{1,α}` bound on an open set: the `α`-Hölder bound of the function. -/
lemma norm_sub_le_of_holderNorm_one_le {α B : ℝ} {P : Set (Fin n → ℂ)} {u : (Fin n → ℂ) → ℂ}
    (hB : 0 ≤ B) (h : Work.CR.Flat.holderNorm 1 α u P ≤ ENNReal.ofReal B)
    {x y : Fin n → ℂ} (hx : x ∈ P) (hy : y ∈ P) : ‖u x - u y‖ ≤ B * ‖x - y‖ ^ α := by
  have h1 : Work.CR.Flat.holderSeminorm 0 α u P ≤ ENNReal.ofReal B :=
    (Work.CR.Flat.holderSeminorm_le_holderNorm 1 α u P (by norm_num)).trans h
  rcases eq_or_ne x y with rfl | hxy
  · simp only [sub_self, norm_zero]
    positivity
  · have h2 := Work.CR.Flat.le_holderSeminorm 0 α u P hx hy hxy
    rw [Work.CR.Flat.Holder.norm_iteratedFDerivWithin_zero_sub u P x y] at h2
    have h3 : ‖u x - u y‖ / ‖x - y‖ ^ α ≤ B :=
      (ENNReal.ofReal_le_ofReal_iff hB).mp (le_trans h2 h1)
    have h4 : 0 < ‖x - y‖ ^ α := Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α
    rwa [div_le_iff₀ h4] at h3

/-- From a `C^{1,α}` bound on an open set: the sup bound of the Fréchet derivative. -/
lemma norm_fderiv_le_of_holderNorm_one_le {α B : ℝ} {P : Set (Fin n → ℂ)} {u : (Fin n → ℂ) → ℂ}
    (hP : IsOpen P) (hB : 0 ≤ B) (h : Work.CR.Flat.holderNorm 1 α u P ≤ ENNReal.ofReal B)
    {x : Fin n → ℂ} (hx : x ∈ P) : ‖fderiv ℝ u x‖ ≤ B := by
  have h1 : Work.CR.Flat.iterDerivNorm 1 u P ≤ ENNReal.ofReal B :=
    (Work.CR.Flat.iterDerivNorm_le_holderNorm 1 α u P le_rfl).trans h
  have h2 : ENNReal.ofReal ‖iteratedFDerivWithin ℝ 1 u P x‖ ≤ ENNReal.ofReal B :=
    le_trans (Work.CR.Flat.le_iterDerivNorm 1 u P hx) h1
  rw [show iteratedFDerivWithin ℝ 1 u P x = iteratedFDeriv ℝ 1 u x from
    iteratedFDerivWithin_of_isOpen 1 hP hx] at h2
  rw [norm_iteratedFDeriv_one] at h2
  exact (ENNReal.ofReal_le_ofReal_iff hB).mp h2

/-- From a `C^{1,α}` bound on an open set: the `α`-Hölder bound of the Fréchet derivative. -/
lemma norm_fderiv_sub_le_of_holderNorm_one_le {α B : ℝ} {P : Set (Fin n → ℂ)}
    {u : (Fin n → ℂ) → ℂ} (hP : IsOpen P) (hB : 0 ≤ B)
    (h : Work.CR.Flat.holderNorm 1 α u P ≤ ENNReal.ofReal B)
    {x y : Fin n → ℂ} (hx : x ∈ P) (hy : y ∈ P) :
    ‖fderiv ℝ u x - fderiv ℝ u y‖ ≤ B * ‖x - y‖ ^ α := by
  have h1 : Work.CR.Flat.holderSeminorm 1 α u P ≤ ENNReal.ofReal B :=
    (Work.CR.Flat.holderSeminorm_le_holderNorm 1 α u P le_rfl).trans h
  have hw : iteratedFDerivWithin ℝ 1 u P x = iteratedFDeriv ℝ 1 u x :=
    iteratedFDerivWithin_of_isOpen 1 hP hx
  have hw' : iteratedFDerivWithin ℝ 1 u P y = iteratedFDeriv ℝ 1 u y :=
    iteratedFDerivWithin_of_isOpen 1 hP hy
  rcases eq_or_ne x y with rfl | hxy
  · simp only [sub_self, norm_zero]
    positivity
  · have h2 := Work.CR.Flat.le_holderSeminorm 1 α u P hx hy hxy
    rw [hw, hw'] at h2
    have h2' : ENNReal.ofReal (‖iteratedFDeriv ℝ 1 u x - iteratedFDeriv ℝ 1 u y‖
        / ‖x - y‖ ^ α) ≤ ENNReal.ofReal B := le_trans h2 h1
    have h3 : ‖iteratedFDeriv ℝ 1 u x - iteratedFDeriv ℝ 1 u y‖ / ‖x - y‖ ^ α ≤ B :=
      (ENNReal.ofReal_le_ofReal_iff hB).mp h2'
    have h4 : 0 < ‖x - y‖ ^ α := Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α
    rw [div_le_iff₀ h4] at h3
    rw [norm_iteratedFDeriv_one_sub_eq u x y] at h3
    exact h3

/-! ## Auxiliary estimates -/

/-- The order-`0` supremum as an `ofReal` bound. -/
lemma iterDerivNorm_zero_le_ofReal {C : ℝ} (_hC : 0 ≤ C) {g : (Fin n → ℂ) → ℂ}
    {Ω : Set (Fin n → ℂ)} (h : ∀ x, ‖g x‖ ≤ C) :
    Work.CR.Flat.iterDerivNorm 0 g Ω ≤ ENNReal.ofReal C := by
  rw [Work.CR.Flat.iterDerivNorm_zero]
  refine iSup₂_le fun x _ => ?_
  exact le_trans (ENNReal.ofReal_le_ofReal (h x)) le_rfl

/-- The order-`0` Hölder seminorm as an `ofReal` bound. -/
lemma holderSeminorm_zero_le_ofReal {C α : ℝ} (_hC : 0 ≤ C) {g : (Fin n → ℂ) → ℂ}
    {Ω : Set (Fin n → ℂ)} (h : ∀ x y, ‖g x - g y‖ ≤ C * ‖x - y‖ ^ α) :
    Work.CR.Flat.holderSeminorm 0 α g Ω ≤ ENNReal.ofReal C := by
  rw [Work.CR.Flat.holderSeminorm]
  refine iSup₂_le fun x _ => iSup₂_le fun y _ => iSup_le fun hxy => ?_
  rw [Work.CR.Flat.Holder.norm_iteratedFDerivWithin_zero_sub g Ω x y]
  refine ENNReal.ofReal_le_ofReal ?_
  have hden : 0 < ‖x - y‖ ^ α :=
    Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α
  exact (div_le_iff₀ hden).mpr (h x y)

/-- The order-`1` supremum as an `ofReal` bound. -/
lemma iterDerivNorm_one_le_ofReal {C : ℝ} (_hC : 0 ≤ C) {Ω : Set (Fin n → ℂ)}
    (hΩ : UniqueDiffOn ℝ Ω) {g : (Fin n → ℂ) → ℂ}
    (h : ∀ x ∈ Ω, ‖fderivWithin ℝ g Ω x‖ ≤ C) :
    Work.CR.Flat.iterDerivNorm 1 g Ω ≤ ENNReal.ofReal C := by
  rw [Work.CR.Flat.iterDerivNorm]
  refine iSup₂_le fun x hx => ?_
  rw [norm_iteratedFDerivWithin_one g (hΩ x hx)]
  exact ENNReal.ofReal_le_ofReal (h x hx)

/-- The order-`1` Hölder seminorm as an `ofReal` bound. -/
lemma holderSeminorm_one_le_ofReal {C α : ℝ} (_hC : 0 ≤ C) {Ω : Set (Fin n → ℂ)}
    (hΩ : UniqueDiffOn ℝ Ω) {g : (Fin n → ℂ) → ℂ}
    (h : ∀ x ∈ Ω, ∀ y ∈ Ω,
      ‖fderivWithin ℝ g Ω x - fderivWithin ℝ g Ω y‖ ≤ C * ‖x - y‖ ^ α) :
    Work.CR.Flat.holderSeminorm 1 α g Ω ≤ ENNReal.ofReal C := by
  rw [Work.CR.Flat.holderSeminorm]
  refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
  rw [Work.CR.Flat.norm_iteratedFDerivWithin_one_sub g (hΩ x hx) (hΩ y hy)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hden : 0 < ‖x - y‖ ^ α :=
    Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α
  exact (div_le_iff₀ hden).mpr (h x hx y hy)

/-- A point of the segment between two points of a polydisc lies in the polydisc. -/
lemma mem_polydisc_segment {c : Fin n → ℂ} {s : Fin n → ℝ} {z h : Fin n → ℂ}
    (hz : ∀ i, ‖z i - c i‖ < s i) (hzh : ∀ i, ‖(z + h) i - c i‖ < s i) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (i : Fin n) : ‖(z + t • h) i - c i‖ < s i := by
  have h1 : (z + t • h) i - c i = (1 - t) * (z i - c i) + t * ((z + h) i - c i) := by
    simp only [Pi.add_apply, Pi.smul_apply, Complex.real_smul]
    ring
  rw [h1]
  have h2 : ‖(1 - t) * (z i - c i) + t * ((z + h) i - c i)‖
      ≤ (1 - t) * ‖z i - c i‖ + t * ‖(z + h) i - c i‖ := by
    calc ‖(1 - t) * (z i - c i) + t * ((z + h) i - c i)‖
        ≤ ‖(1 - t) * (z i - c i)‖ + ‖t * ((z + h) i - c i)‖ := norm_add_le _ _
      _ = (1 - t) * ‖z i - c i‖ + t * ‖(z + h) i - c i‖ := by
          have hc1 : ‖(1 - (t : ℂ))‖ = 1 - t := by
            rw [show (1 - (t : ℂ)) = ((1 - t : ℝ) : ℂ) by push_cast; ring,
              Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (sub_nonneg.mpr ht.2)]
          have hc2 : ‖((t : ℝ) : ℂ)‖ = t := by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
          rw [norm_mul, norm_mul, hc1, hc2]
  refine h2.trans_lt ?_
  have h3 : (1 - t) * s i + t * s i = s i := by ring
  rcases lt_or_eq_of_le ht.1 with h0 | h0
  · -- `0 < t`: strict in the second term
    have hle : (1 - t) * ‖z i - c i‖ ≤ (1 - t) * s i :=
      mul_le_mul_of_nonneg_left (hz i).le (sub_nonneg.mpr ht.2)
    have hlt : t * ‖(z + h) i - c i‖ < t * s i := mul_lt_mul_of_pos_left (hzh i) h0
    linarith [add_lt_add_of_le_of_lt hle hlt, h3]
  · -- `t = 0`: strict in the first term
    subst h0
    simpa using hz i

/-- **Taylor estimate from a Hölder bound on the derivative.** -/
lemma taylor_le {u : (Fin n → ℂ) → ℂ} {B α : ℝ} {z h : Fin n → ℂ} (hB : 0 ≤ B) (hα : 0 ≤ α)
    (hud : ∀ t : ℝ, HasFDerivAt u (fderiv ℝ u (z + t • h)) (z + t • h))
    (hder : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ u (z + t • h) - fderiv ℝ u z‖ ≤ B * ‖t • h‖ ^ α) :
    ‖u (z + h) - u z - (fderiv ℝ u z) h‖ ≤ B * ‖h‖ ^ (1 + α) := by
  set F : ℝ → ℂ := fun t => u (z + t • h) - (fderiv ℝ u z) (t • h) with hF
  have hFderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt F ((fderiv ℝ u (z + t • h) - fderiv ℝ u z) h) t := by
    intro t _
    have hc : HasDerivAt (fun s : ℝ => z + s • h) h t := by
      simpa using ((hasDerivAt_id t).smul_const h).const_add z
    have h1 : HasDerivAt (fun s : ℝ => u (z + s • h)) ((fderiv ℝ u (z + t • h)) h) t :=
      (hud t).comp_hasDerivAt t hc
    have h2 : HasDerivAt (fun s : ℝ => (fderiv ℝ u z) (s • h)) ((fderiv ℝ u z) h) t := by
      have hfun : (fun s : ℝ => (fderiv ℝ u z) (s • h))
          = fun s : ℝ => s • ((fderiv ℝ u z) h) := by
        funext s
        rw [map_smul]
      rw [hfun]
      simpa using (hasDerivAt_id t).smul_const ((fderiv ℝ u z) h)
    rw [hF]
    exact h1.sub h2
  have hdiff : DifferentiableOn ℝ F (Set.Icc (0 : ℝ) 1) := fun t ht =>
    (hFderiv t ht).differentiableAt.differentiableWithinAt
  have hbound : ∀ t ∈ Set.Ico (0 : ℝ) 1,
      ‖derivWithin F (Set.Icc (0 : ℝ) 1) t‖ ≤ B * ‖h‖ ^ (1 + α) := by
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1, le_of_lt ht.2⟩
    rw [((hFderiv t ht').hasDerivWithinAt).derivWithin
      (uniqueDiffOn_Icc (by norm_num : (0:ℝ) < 1) t ht')]
    have h1 : ‖(fderiv ℝ u (z + t • h) - fderiv ℝ u z) h‖
        ≤ ‖fderiv ℝ u (z + t • h) - fderiv ℝ u z‖ * ‖h‖ :=
      ContinuousLinearMap.le_opNorm _ _
    have h2 : ‖fderiv ℝ u (z + t • h) - fderiv ℝ u z‖ ≤ B * ‖t • h‖ ^ α := hder t ht'
    have h3 : ‖t • h‖ = |t| * ‖h‖ := norm_smul _ _
    have ht0 : (0:ℝ) ≤ t := ht.1
    have ht1 : t ≤ 1 := le_of_lt ht.2
    have h4 : (|t| : ℝ) = t := abs_of_nonneg ht0
    have h5 : ‖t • h‖ ^ α ≤ ‖h‖ ^ α := by
      rw [h3, h4]
      refine Real.rpow_le_rpow (by positivity) ?_ hα
      nlinarith [norm_nonneg h, ht0, ht1]
    calc ‖(fderiv ℝ u (z + t • h) - fderiv ℝ u z) h‖
        ≤ ‖fderiv ℝ u (z + t • h) - fderiv ℝ u z‖ * ‖h‖ := h1
      _ ≤ (B * ‖t • h‖ ^ α) * ‖h‖ :=
          mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
      _ ≤ (B * ‖h‖ ^ α) * ‖h‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left h5 hB) (norm_nonneg _)
      _ = B * ‖h‖ ^ (1 + α) := by
          rcases eq_or_lt_of_le (norm_nonneg h) with h0 | hpos
          · rw [← h0, Real.zero_rpow (by linarith : (1:ℝ) + α ≠ 0)]
            ring
          · rw [mul_assoc, ← Real.rpow_add_one (ne_of_gt hpos) α, add_comm]
  have hmain := norm_image_sub_le_of_norm_deriv_le_segment hdiff hbound 1 (by norm_num)
  have h5 : F 1 - F 0 = u (z + h) - u z - (fderiv ℝ u z) h := by
    simp only [hF, one_smul, zero_smul, map_zero, sub_zero, add_zero]
    abel
  rw [h5] at hmain
  simpa using hmain

/-- **The second-difference estimate from a Hölder bound on the derivative.** -/
lemma second_diff_le {u : (Fin n → ℂ) → ℂ} {B α : ℝ} {z w h : Fin n → ℂ} (hB : 0 ≤ B)
    (hα : 0 ≤ α)
    (hud : ∀ x, HasFDerivAt u (fderiv ℝ u x) x)
    (hder : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ u (z + t • h) - fderiv ℝ u (w + t • h)‖ ≤ B * ‖z - w‖ ^ α) :
    ‖u (z + h) - u z - (u (w + h) - u w)‖ ≤ B * ‖z - w‖ ^ α * ‖h‖ := by
  set F : ℝ → ℂ := fun t => u (z + t • h) - u (w + t • h) with hF
  have hFderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt F ((fderiv ℝ u (z + t • h) - fderiv ℝ u (w + t • h)) h) t := by
    intro t _
    have hc : HasDerivAt (fun s : ℝ => z + s • h) h t := by
      simpa using ((hasDerivAt_id t).smul_const h).const_add z
    have hc' : HasDerivAt (fun s : ℝ => w + s • h) h t := by
      simpa using ((hasDerivAt_id t).smul_const h).const_add w
    have h1 : HasDerivAt (fun s : ℝ => u (z + s • h)) ((fderiv ℝ u (z + t • h)) h) t :=
      (hud (z + t • h)).comp_hasDerivAt t hc
    have h2 : HasDerivAt (fun s : ℝ => u (w + s • h)) ((fderiv ℝ u (w + t • h)) h) t :=
      (hud (w + t • h)).comp_hasDerivAt t hc'
    rw [hF]
    exact h1.sub h2
  have hdiff : DifferentiableOn ℝ F (Set.Icc (0 : ℝ) 1) := fun t ht =>
    (hFderiv t ht).differentiableAt.differentiableWithinAt
  have hbound : ∀ t ∈ Set.Ico (0 : ℝ) 1,
      ‖derivWithin F (Set.Icc (0 : ℝ) 1) t‖ ≤ B * ‖z - w‖ ^ α * ‖h‖ := by
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1, le_of_lt ht.2⟩
    rw [((hFderiv t ht').hasDerivWithinAt).derivWithin (uniqueDiffOn_Icc (by norm_num : (0:ℝ) < 1) t ht')]
    calc ‖(fderiv ℝ u (z + t • h) - fderiv ℝ u (w + t • h)) h‖
        ≤ ‖fderiv ℝ u (z + t • h) - fderiv ℝ u (w + t • h)‖ * ‖h‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ (B * ‖z - w‖ ^ α) * ‖h‖ := mul_le_mul_of_nonneg_right (hder t ht') (norm_nonneg _)
      _ = B * ‖z - w‖ ^ α * ‖h‖ := by ring
  have hmain := norm_image_sub_le_of_norm_deriv_le_segment hdiff hbound 1 (by norm_num)
  have h5 : F 1 - F 0 = u (z + h) - u z - (u (w + h) - u w) := by
    simp only [hF, one_smul, zero_smul, map_zero, sub_zero, add_zero]
    abel
  rw [h5] at hmain
  simpa using hmain


/-! ## The main theorem -/

/-- **The Bochner–Martinelli potential gains one derivative from `C^{0,α}` data.**

For `n ≥ 1`, `0 < α < 1`, a polydisc `polydisc c s` and a datum `f` whose components are
continuous, bounded by `A j`, `α`-Hölder with constant `K j` and vanish off `polydisc c s`,
the potential is `C^{1,α}` on `polydisc c s` with the bound `C Σ_j (A_j + K_j)`. -/
theorem bmPotential_holder_one_of_holder {n : ℕ} (hn : 0 < n) {c : Fin n → ℂ} {s : Fin n → ℝ}
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) (hs : ∀ j, 0 < s j) :
    ∃ C : ℝ, 0 < C ∧ ∀ {A K : Fin n → ℝ}, (∀ j, 0 ≤ A j) → (∀ j, 0 ≤ K j) →
      ∀ {f : Fin n → (Fin n → ℂ) → ℂ} (hf : ∀ j, Continuous (f j))
        (hfA : ∀ j z, ‖f j z‖ ≤ A j) (hfK : ∀ j x y, ‖f j x - f j y‖ ≤ K j * ‖x - y‖ ^ α)
        (hfsupp : ∀ j z, (∃ k, s k ≤ ‖z k - c k‖) → f j z = 0),
      (Work.CR.Flat.holderNorm 1 α (Work.CR.Flat.Cauchy.bmPotential f) (Work.CR.Flat.polydisc c s)
          ≤ ENNReal.ofReal (C * ∑ j, (A j + K j))) ∧
      (∀ z ∈ Work.CR.Flat.polydisc c s,
        DifferentiableAt ℝ (Work.CR.Flat.Cauchy.bmPotential f) z) := by
  classical
  set P : Set (Fin n → ℂ) := Work.CR.Flat.polydisc c s with hP
  have hPopen : IsOpen P := Work.CR.Flat.isOpen_polydisc c s
  -- the `C¹`-data estimate, with base radii `4 s`
  set R : Fin n → ℝ := fun j => 4 * s j with hR
  have hRpos : ∀ j, 0 < R j := fun j => by rw [hR]; linarith [hs j]
  obtain ⟨C₀, hC₀pos, hC₀⟩ := Work.CR.Flat.Cauchy.bmPotential_holder_CZ (n := n) hn
    (c := c) (r := R) hα hα1 hRpos
  refine ⟨4 * C₀ + 1, by linarith, ?_⟩
  intro A K hA hK f hf hfA hfK hfsupp
  by_cases hzero : (∑ j, (A j + K j)) = 0
  · -- the datum vanishes identically
    have hfzero : f = 0 := by
      funext j z
      have hAj : A j = 0 := by
        have h1 : A j + K j ≤ ∑ i, (A i + K i) :=
          Finset.single_le_sum (fun i _ => add_nonneg (hA i) (hK i)) (Finset.mem_univ j)
        linarith [hA j, hK j]
      have h1 : ‖f j z‖ ≤ 0 := by simpa [hAj] using hfA j z
      simpa using h1
    have hbm0 : Work.CR.Flat.Cauchy.bmPotential (0 : Fin n → (Fin n → ℂ) → ℂ) = 0 := by
      funext z
      simp [Work.CR.Flat.Cauchy.bmPotential]
    refine ⟨?_, ?_⟩
    · rw [hfzero, hzero, mul_zero, ENNReal.ofReal_zero, hbm0]
      simp [Work.CR.Flat.holderNorm, Work.CR.Flat.iterDerivNorm, Work.CR.Flat.holderSeminorm]
    · intro z hz
      rw [hfzero, hbm0]
      exact differentiableAt_const 0
  · -- the main case
    have hSnn : 0 ≤ ∑ j, (A j + K j) := Finset.sum_nonneg fun j _ => add_nonneg (hA j) (hK j)
    -- the interpolated radii
    set r : Fin n → ℝ := fun j => 2 * s j with hr
    have hrpos : ∀ j, 0 < r j := fun j => by rw [hr]; linarith [hs j]
    have hsr : ∀ j, s j < r j := fun j => by rw [hr]; linarith [hs j]
    have hRr : ∀ j, R j / 2 = r j := fun j => by rw [hR, hr]; ring
    set B : ℝ := C₀ * ∑ j, (A j + K j) with hB
    have hBnn : 0 ≤ B := by rw [hB]; exact mul_nonneg hC₀pos.le hSnn
    -- the smooth approximating sequence
    have happrox : ∀ j : Fin n, ∃ G : ℕ → (Fin n → ℂ) → ℂ,
        (∀ m, ContDiff ℝ (⊤ : ℕ∞) (G m)) ∧
        (∀ m x, ‖G m x‖ ≤ A j) ∧
        (∀ m x y, ‖G m x - G m y‖ ≤ K j * ‖x - y‖ ^ α) ∧
        (∀ m z, (∃ i, r i ≤ ‖z i - c i‖) → G m z = 0) ∧
        (∀ z, Tendsto (fun m => G m z) atTop (nhds (f j z))) := fun j =>
      bmSmoothApprox (g := f j) (A := A j) (K := K j) (c := c) (s := s) (r := r)
        hα (hK j) hsr (hfA j) (hfK j) (hfsupp j)
    choose G hGsm hGA hGK hGs hGc using happrox
    set U : ℕ → (Fin n → ℂ) → ℂ := fun m => Work.CR.Flat.Cauchy.bmPotential (fun j => G j m)
      with hU
    have hUdef : ∀ m, U m = Work.CR.Flat.Cauchy.bmPotential (fun j => G j m) := fun m => rfl
    have hUm : ∀ m, ContDiff ℝ 1 (U m) := by
      intro m
      rw [hUdef m]
      exact Work.CR.Flat.Cauchy.bmPotential_contDiff_of_hasCompactSupport hn
        (fun j => (hGsm j m).of_le (by simp))
        (fun j => Work.CR.Flat.Cauchy.hasCompactSupport_of_halfPolydisc
          (c := c) (r := fun j => 2 * r j) (fun j => by linarith [hrpos j])
          (fun z hz => hGs j m z (by obtain ⟨i, hi⟩ := hz; exact ⟨i, by linarith [hi]⟩)))
    -- the uniform `C^{1,α}` bound
    have hUb : ∀ m, Work.CR.Flat.holderNorm 1 α (U m) P ≤ ENNReal.ofReal B := by
      intro m
      have h1 : Work.CR.Flat.holderNorm 1 α (Work.CR.Flat.Cauchy.bmPotential (fun j => G j m))
          (Work.CR.Flat.polydisc c (fun j => R j / 2)) ≤ ENNReal.ofReal C₀ *
            ∑ j, Work.CR.Flat.holderNorm 0 α (G j m) Set.univ :=
        hC₀ (fun j => G j m) (fun j => (hGsm j m).of_le (by simp))
          (fun j z hz => hGs j m z (by
            obtain ⟨i, hi⟩ := hz
            exact ⟨i, by rw [← hRr]; exact hi⟩))
      have hsum : (∑ j, Work.CR.Flat.holderNorm 0 α (G j m) Set.univ)
          ≤ ENNReal.ofReal (∑ j, (A j + K j)) := by
        calc (∑ j, Work.CR.Flat.holderNorm 0 α (G j m) Set.univ)
            ≤ ∑ j, ENNReal.ofReal (A j + K j) := by
              refine Finset.sum_le_sum fun j _ => ?_
              rw [Work.CR.Flat.holderNorm, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
                ENNReal.ofReal_add (hA j) (hK j)]
              exact add_le_add (iterDerivNorm_zero_le_ofReal (hA j) (hGA j m))
                (holderSeminorm_zero_le_ofReal (hK j) (hGK j m))
          _ = ENNReal.ofReal (∑ j, (A j + K j)) :=
              (ENNReal.ofReal_sum_of_nonneg fun j _ => add_nonneg (hA j) (hK j)).symm
      rw [hUdef m] at *
      refine (Work.CR.Flat.holderNorm_mono_set (Work.CR.Flat.isOpen_polydisc c r) hPopen
        (fun z hz i => lt_trans (hz i) (hsr i)) 1 α _).trans ?_
      rw [show (fun j => R j / 2) = r from funext hRr] at h1
      refine h1.trans ?_
      have h2 : ENNReal.ofReal C₀ * (∑ j, Work.CR.Flat.holderNorm 0 α (G j m) Set.univ)
          ≤ ENNReal.ofReal C₀ * ENNReal.ofReal (∑ j, (A j + K j)) :=
        mul_le_mul_of_nonneg_left hsum (by simp : (0:ℝ≥0∞) ≤ ENNReal.ofReal C₀)
      exact h2.trans (by rw [← ENNReal.ofReal_mul hC₀pos.le, hB])
    -- pointwise convergence of the potentials
    have hconv : ∀ z, Tendsto (fun m => U m z) atTop
        (nhds (Work.CR.Flat.Cauchy.bmPotential f z)) := by
      intro z
      have h1 := Work.CR.Flat.Cauchy.bmPotential_tendsto_of_tendsto (n := n) hn
        (c := c) (s := r) hrpos (R := ∑ j, A j) (Finset.sum_nonneg fun j _ => hA j)
        (F := fun m j => G j m) (f := f)
        (fun m j => (hGsm j m).continuous) hf
        (fun m j z => le_trans (hGA j m z)
          (Finset.single_le_sum (fun i _ => hA i) (Finset.mem_univ j)))
        (fun j z => le_trans (hfA j z)
          (Finset.single_le_sum (fun i _ => hA i) (Finset.mem_univ j)))
        (fun m j z hz => hGs j m z hz)
        (fun j z hz => hfsupp j z (by
          obtain ⟨i, hi⟩ := hz
          have hi' : 2 * s i ≤ ‖z i - c i‖ := hi
          exact ⟨i, by linarith [hi', hs i]⟩))
        (fun j z => hGc j z)
      simpa [hUdef] using h1 z
    -- the order-`0` bounds for the limit
    have hlimSup : ∀ z ∈ P, ‖Work.CR.Flat.Cauchy.bmPotential f z‖ ≤ B := by
      intro z hz
      have h1 : ∀ m, ‖U m z‖ ≤ B := fun m => norm_le_of_holderNorm_one_le hBnn (hUb m) hz
      have h2 : Tendsto (fun m => ‖U m z‖) atTop (nhds ‖Work.CR.Flat.Cauchy.bmPotential f z‖) :=
        (hconv z).norm
      exact le_of_tendsto_of_tendsto h2 tendsto_const_nhds (Eventually.of_forall h1)
    have hlimSub : ∀ x ∈ P, ∀ y ∈ P,
        ‖Work.CR.Flat.Cauchy.bmPotential f x - Work.CR.Flat.Cauchy.bmPotential f y‖
          ≤ B * ‖x - y‖ ^ α := by
      intro x hx y hy
      have h1 : ∀ m, ‖U m x - U m y‖ ≤ B * ‖x - y‖ ^ α :=
        fun m => norm_sub_le_of_holderNorm_one_le hBnn (hUb m) hx hy
      have h2 : Tendsto (fun m => U m x - U m y) atTop
          (nhds (Work.CR.Flat.Cauchy.bmPotential f x - Work.CR.Flat.Cauchy.bmPotential f y)) :=
        (hconv x).sub (hconv y)
      exact le_of_tendsto_of_tendsto h2.norm tendsto_const_nhds (Eventually.of_forall h1)
    -- the Taylor estimates for the approximants
    have hT : ∀ m (z : Fin n → ℂ), (∀ i, ‖z i - c i‖ < s i) → ∀ h,
        (∀ i, ‖(z + h) i - c i‖ < s i) →
        ‖U m (z + h) - U m z - (fderiv ℝ (U m) z) h‖ ≤ B * ‖h‖ ^ (1 + α) := by
      intro m z hz h hzh
      have hud : ∀ t : ℝ, HasFDerivAt (U m) (fderiv ℝ (U m) (z + t • h)) (z + t • h) :=
        fun t => ((hUm m).differentiable (by simp)).differentiableAt.hasFDerivAt
      refine taylor_le hBnn hα.le hud ?_
      intro t ht
      have hmem : (z + t • h) ∈ P := by
        rw [hP]
        exact fun i => mem_polydisc_segment hz hzh ht i
      have hmemz : z ∈ P := by rw [hP]; exact hz
      have h1 := norm_fderiv_sub_le_of_holderNorm_one_le hPopen hBnn (hUb m) hmem hmemz
      rwa [show z + t • h - z = t • h from by abel] at h1
    -- the limit of the Taylor estimates along a subsequence
    have hlimit_deriv : ∀ (z : Fin n → ℂ), (∀ i, ‖z i - c i‖ < s i) →
        ∀ (L : (Fin n → ℂ) →L[ℝ] ℂ) (φ : ℕ → ℕ), StrictMono φ →
        Tendsto (fun k => fderiv ℝ (U (φ k)) z) atTop (nhds L) → HasFDerivAt (Work.CR.Flat.Cauchy.bmPotential f) L z := by
      intro z hz L φ hφ hφt
      have hTaylor : ∀ h, (∀ i, ‖(z + h) i - c i‖ < s i) →
          ‖Work.CR.Flat.Cauchy.bmPotential f (z + h) - Work.CR.Flat.Cauchy.bmPotential f z - L h‖
            ≤ B * ‖h‖ ^ (1 + α) := by
        intro h hzh
        have h1 : ∀ k, ‖U (φ k) (z + h) - U (φ k) z - (fderiv ℝ (U (φ k)) z) h‖
            ≤ B * ‖h‖ ^ (1 + α) := fun k => hT (φ k) z hz h hzh
        have h2 : Tendsto (fun k => U (φ k) (z + h) - U (φ k) z - (fderiv ℝ (U (φ k)) z) h)
            atTop (nhds (Work.CR.Flat.Cauchy.bmPotential f (z + h)
              - Work.CR.Flat.Cauchy.bmPotential f z - L h)) := by
          have h3 : Tendsto (fun k => (fderiv ℝ (U (φ k)) z) h) atTop (nhds (L h)) :=
            ((ContinuousLinearMap.apply ℝ ℂ h).continuous.tendsto L).comp hφt
          exact (((hconv (z + h)).comp hφ.tendsto_atTop).sub
            ((hconv z).comp hφ.tendsto_atTop)).sub h3
        exact le_of_tendsto_of_tendsto h2.norm tendsto_const_nhds (Eventually.of_forall h1)
      rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
      intro c₀ hc₀
      -- `z` has room inside the polydisc
      obtain ⟨δ, hδpos, hδ⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ h : Fin n → ℂ, ‖h‖ < δ →
          (∀ i, ‖(z + h) i - c i‖ < s i) := by
        set m : Fin n → ℝ := fun i => s i - ‖z i - c i‖ with hm
        have hmpos : ∀ i, 0 < m i := fun i => sub_pos.mpr (hz i)
        haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
        have hne : (Finset.univ : Finset (Fin n)).Nonempty := Finset.univ_nonempty
        refine ⟨Finset.univ.inf' hne m / 2, ?_, ?_⟩
        · have h1 : 0 < Finset.univ.inf' hne m := by
            rw [Finset.lt_inf'_iff]
            intro i _
            exact hmpos i
          linarith
        · intro h hh i
          have h1 : Finset.univ.inf' hne m ≤ m i := Finset.inf'_le _ (Finset.mem_univ i)
          have h3 : ‖(z + h) i - c i‖ ≤ ‖h‖ + ‖z i - c i‖ := by
            calc ‖(z + h) i - c i‖ = ‖((z + h) i - z i) + (z i - c i)‖ := by ring_nf
              _ ≤ ‖(z + h) i - z i‖ + ‖z i - c i‖ := norm_add_le _ _
              _ ≤ ‖h‖ + ‖z i - c i‖ := by
                  refine add_le_add ?_ le_rfl
                  rw [show (z + h) i - z i = h i from by simp]
                  exact norm_le_pi_norm h i
          have h4 : ‖h‖ < Finset.univ.inf' hne m / 2 := hh
          have hzi := hz i
          simp only [hm] at h1
          linarith
      -- the comparison exponent
      obtain ⟨η, hηpos, hη⟩ : ∃ η : ℝ, 0 < η ∧ B * η ^ α ≤ c₀ := by
        rcases eq_or_lt_of_le hBnn with hB0 | hBpos
        · exact ⟨1, one_pos, by rw [← hB0, zero_mul]; exact hc₀.le⟩
        · refine ⟨(c₀ / (2 * B)) ^ (1 / α), Real.rpow_pos_of_pos (by positivity) _, ?_⟩
          have h1 : ((c₀ / (2 * B)) ^ (1 / α)) ^ α = c₀ / (2 * B) := by
            rw [← Real.rpow_mul (by positivity : (0:ℝ) ≤ c₀ / (2 * B))]
            have h2 : 1 / α * α = 1 := by field_simp
            rw [h2, Real.rpow_one]
          rw [h1]
          have h2 : B * (c₀ / (2 * B)) = c₀ / 2 := by field_simp
          rw [h2]
          linarith
      filter_upwards [Metric.ball_mem_nhds (0 : Fin n → ℂ) (lt_min hδpos hηpos)] with h hh
      rcases eq_or_ne h 0 with h0 | h0
      · subst h0
        simp
      · have hh' : ‖h‖ < min δ η := by simpa [dist_eq_norm] using Metric.mem_ball.mp hh
        have hhδ : ‖h‖ < δ := lt_of_lt_of_le hh' (min_le_left _ _)
        have hhη : ‖h‖ < η := lt_of_lt_of_le hh' (min_le_right _ _)
        have hpos : 0 < ‖h‖ := norm_pos_iff.mpr h0
        calc ‖Work.CR.Flat.Cauchy.bmPotential f (z + h) - Work.CR.Flat.Cauchy.bmPotential f z - L h‖
            ≤ B * ‖h‖ ^ (1 + α) := hTaylor h (hδ h hhδ)
          _ = B * (‖h‖ ^ α * ‖h‖) := by
              rw [show (1 : ℝ) + α = α + 1 by ring, Real.rpow_add_one (ne_of_gt hpos) α]
          _ ≤ B * (η ^ α * ‖h‖) := by
              refine mul_le_mul_of_nonneg_left ?_ hBnn
              exact mul_le_mul_of_nonneg_right
                (Real.rpow_le_rpow (norm_nonneg h) hhη.le hα.le) (norm_nonneg h)
          _ = (B * η ^ α) * ‖h‖ := by ring
          _ ≤ c₀ * ‖h‖ := mul_le_mul_of_nonneg_right hη (norm_nonneg h)
    -- existence of the derivative at each point of the polydisc
    have hder_all : ∀ z, (∀ i, ‖z i - c i‖ < s i) →
        ∃ L : (Fin n → ℂ) →L[ℝ] ℂ, ‖L‖ ≤ B ∧ HasFDerivAt (Work.CR.Flat.Cauchy.bmPotential f) L z := by
      intro z hz
      have hmem : ∀ m, fderiv ℝ (U m) z ∈ Metric.closedBall (0 : (Fin n → ℂ) →L[ℝ] ℂ) B := by
        intro m
        rw [Metric.mem_closedBall, dist_zero_right]
        exact norm_fderiv_le_of_holderNorm_one_le hPopen hBnn (hUb m) (by rw [hP]; exact hz)
      obtain ⟨L, hLmem, φ, hφ, hφt⟩ :=
        ((isCompact_closedBall (0 : (Fin n → ℂ) →L[ℝ] ℂ) B).isSeqCompact).subseq_of_frequently_in
          (x := fun m => fderiv ℝ (U m) z) (Frequently.of_forall hmem)
      refine ⟨L, ?_, hlimit_deriv z hz L φ hφ hφt⟩
      rwa [Metric.mem_closedBall, dist_zero_right] at hLmem
    -- the derivative satisfies the bound
    have hder : ∀ z, (∀ i, ‖z i - c i‖ < s i) →
        ‖fderiv ℝ (Work.CR.Flat.Cauchy.bmPotential f) z‖ ≤ B := by
      intro z hz
      obtain ⟨L, hL, hF⟩ := hder_all z hz
      rw [hF.fderiv]
      exact hL
    -- the derivative is `α`-Hölder
    have hderH : ∀ x y, (∀ i, ‖x i - c i‖ < s i) → (∀ i, ‖y i - c i‖ < s i) →
        ‖fderiv ℝ (Work.CR.Flat.Cauchy.bmPotential f) x - fderiv ℝ (Work.CR.Flat.Cauchy.bmPotential f) y‖ ≤ B * ‖x - y‖ ^ α := by
      intro x y hx hy
      rcases eq_or_ne x y with rfl | hxy
      · rw [sub_self, norm_zero]
        exact mul_nonneg hBnn (Real.rpow_nonneg (norm_nonneg _) α)
      · have hpair : ∀ m, (fderiv ℝ (U m) x, fderiv ℝ (U m) y)
            ∈ (Metric.closedBall (0 : (Fin n → ℂ) →L[ℝ] ℂ) B) ×ˢ
              (Metric.closedBall (0 : (Fin n → ℂ) →L[ℝ] ℂ) B) := by
          intro m
          refine ⟨?_, ?_⟩
          · rw [Metric.mem_closedBall, dist_zero_right]
            exact norm_fderiv_le_of_holderNorm_one_le hPopen hBnn (hUb m) (by rw [hP]; exact hx)
          · rw [Metric.mem_closedBall, dist_zero_right]
            exact norm_fderiv_le_of_holderNorm_one_le hPopen hBnn (hUb m) (by rw [hP]; exact hy)
        obtain ⟨⟨Lx, Ly⟩, -, φ, hφ, hφt⟩ :=
          (((isCompact_closedBall (0 : (Fin n → ℂ) →L[ℝ] ℂ) B).prod
            (isCompact_closedBall (0 : (Fin n → ℂ) →L[ℝ] ℂ) B)).isSeqCompact).subseq_of_frequently_in
            (x := fun m => (fderiv ℝ (U m) x, fderiv ℝ (U m) y)) (Frequently.of_forall hpair)
        have hφx : Tendsto (fun k => fderiv ℝ (U (φ k)) x) atTop (nhds Lx) :=
          ((Prod.tendsto_iff _ _).mp hφt).1
        have hφy : Tendsto (fun k => fderiv ℝ (U (φ k)) y) atTop (nhds Ly) :=
          ((Prod.tendsto_iff _ _).mp hφt).2
        have hFx := hlimit_deriv x hx Lx φ hφ hφx
        have hFy := hlimit_deriv y hy Ly φ hφ hφy
        rw [hFx.fderiv, hFy.fderiv]
        have h1 : ∀ k, ‖fderiv ℝ (U (φ k)) x - fderiv ℝ (U (φ k)) y‖ ≤ B * ‖x - y‖ ^ α :=
          fun k => norm_fderiv_sub_le_of_holderNorm_one_le hPopen hBnn
            (hUb (φ k)) (by rw [hP]; exact hx) (by rw [hP]; exact hy)
        exact le_of_tendsto_of_tendsto (hφx.sub hφy).norm tendsto_const_nhds
          (Eventually.of_forall h1)
    -- assembly of the four components of the norm
    have hsup : Work.CR.Flat.iterDerivNorm 0 (Work.CR.Flat.Cauchy.bmPotential f) P ≤ ENNReal.ofReal B := by
      rw [Work.CR.Flat.iterDerivNorm_zero]
      refine iSup₂_le fun z hz => ?_
      exact ENNReal.ofReal_le_ofReal (hlimSup z hz)
    have hsem : Work.CR.Flat.holderSeminorm 0 α (Work.CR.Flat.Cauchy.bmPotential f) P ≤ ENNReal.ofReal B := by
      rw [Work.CR.Flat.holderSeminorm]
      refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
      refine ENNReal.ofReal_le_ofReal ?_
      rw [Work.CR.Flat.Holder.norm_iteratedFDerivWithin_zero_sub]
      have hden : 0 < ‖x - y‖ ^ α :=
        Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α
      exact (div_le_iff₀ hden).mpr (hlimSub x hx y hy)
    have hder1 : Work.CR.Flat.iterDerivNorm 1 (Work.CR.Flat.Cauchy.bmPotential f) P ≤ ENNReal.ofReal B := by
      rw [Work.CR.Flat.iterDerivNorm]
      refine iSup₂_le fun z hz => ?_
      rw [iteratedFDerivWithin_of_isOpen 1 hPopen hz, norm_iteratedFDeriv_one]
      exact ENNReal.ofReal_le_ofReal (hder z hz)
    have hderH1 : Work.CR.Flat.holderSeminorm 1 α (Work.CR.Flat.Cauchy.bmPotential f) P ≤ ENNReal.ofReal B := by
      rw [Work.CR.Flat.holderSeminorm]
      refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
      refine ENNReal.ofReal_le_ofReal ?_
      · rw [iteratedFDerivWithin_of_isOpen 1 hPopen hx,
          iteratedFDerivWithin_of_isOpen 1 hPopen hy, norm_iteratedFDeriv_one_sub_eq]
        have hden : 0 < ‖x - y‖ ^ α :=
          Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α
        exact (div_le_iff₀ hden).mpr (hderH x y hx hy)
    have hmain : Work.CR.Flat.holderNorm 1 α (Work.CR.Flat.Cauchy.bmPotential f) P ≤ ENNReal.ofReal (4 * B) := by
      rw [Work.CR.Flat.holderNorm, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_zero, zero_add]
      calc (Work.CR.Flat.iterDerivNorm 0 (Work.CR.Flat.Cauchy.bmPotential f) P + Work.CR.Flat.holderSeminorm 0 α (Work.CR.Flat.Cauchy.bmPotential f) P)
            + (Work.CR.Flat.iterDerivNorm 1 (Work.CR.Flat.Cauchy.bmPotential f) P
              + Work.CR.Flat.holderSeminorm 1 α (Work.CR.Flat.Cauchy.bmPotential f) P)
          ≤ ENNReal.ofReal B + ENNReal.ofReal B + (ENNReal.ofReal B + ENNReal.ofReal B) :=
            add_le_add (add_le_add hsup hsem) (add_le_add hder1 hderH1)
        _ = ENNReal.ofReal (4 * B) := by
            rw [← ENNReal.ofReal_add hBnn hBnn,
              ← ENNReal.ofReal_add (add_nonneg hBnn hBnn) (add_nonneg hBnn hBnn)]
            congr 1
            ring
    refine ⟨?_, ?_⟩
    · refine hmain.trans ?_
      rw [hB]
      refine ENNReal.ofReal_le_ofReal ?_
      nlinarith [hC₀pos.le, hSnn]
    · intro z hz
      obtain ⟨L, hL, hF⟩ := hder_all z hz
      exact hF.differentiableAt


/-- **The `C^{1,α}` bound in terms of the `C^{0,α}`-norm of the datum.**

Restatement of `bmPotential_holder_one_of_holder` with the data bounds packaged as the finiteness
of the `C^{0,α}`-norm (plus the differentiability of the potential, which is also proved there). -/
theorem bmPotential_holder_one_of_holderNorm {n : ℕ} (hn : 0 < n) {c : Fin n → ℂ}
    {s : Fin n → ℝ} {α : ℝ} (hα : 0 < α) (hα1 : α < 1) (hs : ∀ j, 0 < s j) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : Fin n → (Fin n → ℂ) → ℂ, (∀ j, Continuous (f j)) →
      (∀ j z, (∃ k, s k ≤ ‖z k - c k‖) → f j z = 0) →
      (∑ j, Work.CR.Flat.holderNorm 0 α (f j) Set.univ) ≠ ⊤ →
      (Work.CR.Flat.holderNorm 1 α (Work.CR.Flat.Cauchy.bmPotential f)
          (Work.CR.Flat.polydisc c s)
        ≤ ENNReal.ofReal C * ∑ j, Work.CR.Flat.holderNorm 0 α (f j) Set.univ) ∧
      (∀ z ∈ Work.CR.Flat.polydisc c s,
        DifferentiableAt ℝ (Work.CR.Flat.Cauchy.bmPotential f) z) := by
  classical
  obtain ⟨C₁, hC₁pos, hC₁⟩ :=
    bmPotential_holder_one_of_holder (n := n) hn (c := c) (s := s) hα hα1 hs
  refine ⟨C₁ + 1, by linarith, ?_⟩
  intro f hf hsupp htop
  have hfin : ∀ j, Work.CR.Flat.holderNorm 0 α (f j) Set.univ ≠ ⊤ := by
    intro j hj
    exact htop (top_le_iff.mp (hj ▸ Finset.single_le_sum
      (f := fun i => Work.CR.Flat.holderNorm 0 α (f i) Set.univ)
      (fun i _ => bot_le) (Finset.mem_univ j)))
  set A : Fin n → ℝ := fun j => (Work.CR.Flat.iterDerivNorm 0 (f j) Set.univ).toReal with hAdef
  set K : Fin n → ℝ := fun j => (Work.CR.Flat.holderSeminorm 0 α (f j) Set.univ).toReal with hKdef
  have hA0 : ∀ j, 0 ≤ A j := fun j => ENNReal.toReal_nonneg
  have hK0 : ∀ j, 0 ≤ K j := fun j => ENNReal.toReal_nonneg
  have hiter : ∀ j, Work.CR.Flat.iterDerivNorm 0 (f j) Set.univ ≠ ⊤ := by
    intro j h
    exact hfin j (by
      rw [Work.CR.Flat.holderNorm, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, h]
      simp)
  have hsem : ∀ j, Work.CR.Flat.holderSeminorm 0 α (f j) Set.univ ≠ ⊤ := by
    intro j h
    exact hfin j (by
      rw [Work.CR.Flat.holderNorm, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, h]
      simp)
  have hofA : ∀ j, ENNReal.ofReal (A j) = Work.CR.Flat.iterDerivNorm 0 (f j) Set.univ :=
    fun j => ENNReal.ofReal_toReal (hiter j)
  have hofK : ∀ j, ENNReal.ofReal (K j) = Work.CR.Flat.holderSeminorm 0 α (f j) Set.univ :=
    fun j => ENNReal.ofReal_toReal (hsem j)
  have hfA : ∀ j z, ‖f j z‖ ≤ A j := by
    intro j z
    have h1 : ENNReal.ofReal ‖f j z‖ ≤ ENNReal.ofReal (A j) := by
      rw [hofA j, Work.CR.Flat.iterDerivNorm_zero]
      exact le_iSup₂_of_le z (Set.mem_univ z) le_rfl
    exact (ENNReal.ofReal_le_ofReal_iff (hA0 j)).mp h1
  have hfK : ∀ j x y, ‖f j x - f j y‖ ≤ K j * ‖x - y‖ ^ α := by
    intro j x y
    rcases eq_or_ne x y with rfl | hxy
    · simp only [sub_self, norm_zero]
      positivity
    · have h1 : ENNReal.ofReal (‖iteratedFDerivWithin ℝ 0 (f j) Set.univ x
            - iteratedFDerivWithin ℝ 0 (f j) Set.univ y‖ / ‖x - y‖ ^ α)
          ≤ ENNReal.ofReal (K j) := by
        rw [hofK j]
        exact Work.CR.Flat.le_holderSeminorm 0 α (f j) Set.univ (Set.mem_univ x)
          (Set.mem_univ y) hxy
      rw [Work.CR.Flat.Holder.norm_iteratedFDerivWithin_zero_sub] at h1
      have h2 : ‖f j x - f j y‖ / ‖x - y‖ ^ α ≤ K j :=
        (ENNReal.ofReal_le_ofReal_iff (hK0 j)).mp h1
      have h3 : 0 < ‖x - y‖ ^ α :=
        Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α
      rwa [div_le_iff₀ h3] at h2
  obtain ⟨hbd, hdiff⟩ := hC₁ (A := A) (K := K) hA0 hK0 hf hfA hfK hsupp
  refine ⟨?_, hdiff⟩
  -- rewrite the sum of the `A j + K j` as the sum of the `C^{0,α}`-norms
  have hsum : ENNReal.ofReal (∑ j, (A j + K j))
      = ∑ j, Work.CR.Flat.holderNorm 0 α (f j) Set.univ := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => add_nonneg (hA0 j) (hK0 j))]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ENNReal.ofReal_add (hA0 j) (hK0 j), hofA j, hofK j, Work.CR.Flat.holderNorm,
      Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  refine hbd.trans ?_
  have h2 : ENNReal.ofReal (C₁ * ∑ j, (A j + K j))
      = ENNReal.ofReal C₁ * ∑ j, Work.CR.Flat.holderNorm 0 α (f j) Set.univ := by
    rw [ENNReal.ofReal_mul hC₁pos.le, hsum]
  rw [h2]
  exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (by linarith)) bot_le

end Work.NN.Core
