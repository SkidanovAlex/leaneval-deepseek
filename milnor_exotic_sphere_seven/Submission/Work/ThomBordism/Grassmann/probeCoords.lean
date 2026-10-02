import Mathlib
import Submission.Work.ThomBordism.Grassmann.probeDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

namespace Work.ThomBordism.Grassmann

open Work.TangentClasses

noncomputable section

variable {k m : ℕ}

/-! ## The standard basis and the inner product -/

theorem inner_single_ite {n : ℕ} (a b : Fin n) :
    inner ℝ (EuclideanSpace.single (𝕜 := ℝ) a (1:ℝ) : EuclideanSpace ℝ (Fin n))
      (EuclideanSpace.single (𝕜 := ℝ) b 1) = if a = b then 1 else 0 := by
  rw [EuclideanSpace.inner_single_left]
  simp [PiLp.single_apply]

theorem inner_single_left' {n : ℕ} (a : Fin n) (v : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (EuclideanSpace.single (𝕜 := ℝ) a (1:ℝ)) v = v.ofLp a := by
  rw [EuclideanSpace.inner_single_left]
  simp

theorem inner_single_right' {n : ℕ} (a : Fin n) (v : EuclideanSpace ℝ (Fin n)) :
    inner ℝ v (EuclideanSpace.single (𝕜 := ℝ) a (1:ℝ)) = v.ofLp a := by
  rw [EuclideanSpace.inner_single_right]
  simp

theorem single_coord_self {n : ℕ} (a b : Fin n) :
    (EuclideanSpace.single (𝕜 := ℝ) a (1:ℝ) : EuclideanSpace ℝ (Fin n)).ofLp b
      = if b = a then 1 else 0 := by
  simp [PiLp.single_apply]

theorem single_coord_ne {n : ℕ} {a b : Fin n} (h : b ≠ a) :
    (EuclideanSpace.single (𝕜 := ℝ) a (1:ℝ) : EuclideanSpace ℝ (Fin n)).ofLp b = 0 := by
  rw [single_coord_self, if_neg h]

theorem sum_single_eq (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    (∑ i : Fin n, x.ofLp i • (EuclideanSpace.single (𝕜 := ℝ) i 1 : EuclideanSpace ℝ (Fin n)))
      = x := by
  rw [WithLp.ext_iff]
  funext j
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  rw [Finset.sum_eq_single j]
  · rw [WithLp.ofLp_smul, Pi.smul_apply, single_coord_self, if_pos rfl, smul_eq_mul, mul_one]
  · intro i _ hi
    rw [WithLp.ofLp_smul, Pi.smul_apply, single_coord_ne (a := i) (b := j) (Ne.symm hi),
      smul_zero]
  · intro h; exact absurd (Finset.mem_univ j) h

/-! ## The coordinate isometry -/

theorem probeEmb_apply (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) (u : Amb 6) :
    probeEmb k m hk hm u = ∑ i : Fin 6, u.ofLp i •
      (EuclideanSpace.single (𝕜 := ℝ) (probeAmbIdx k m hk hm i) 1 : Amb (k + m)) := by
  simp only [probeEmb, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [ContinuousLinearMap.smulRight_apply]
  rfl

theorem probeEmb_coord (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) (u : Amb 6) (i : Fin 6) :
    (probeEmb k m hk hm u).ofLp (probeAmbIdx k m hk hm i) = u.ofLp i := by
  rw [probeEmb_apply, WithLp.ofLp_sum, Finset.sum_apply]
  rw [Finset.sum_eq_single i]
  · rw [WithLp.ofLp_smul, Pi.smul_apply, single_coord_self, if_pos rfl, smul_eq_mul, mul_one]
  · intro j _ hj
    rw [WithLp.ofLp_smul, Pi.smul_apply,
      single_coord_ne (a := probeAmbIdx k m hk hm j) (b := probeAmbIdx k m hk hm i)
        (fun hh => hj (probeAmbIdx_injective k m hk hm hh.symm)), smul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem probeEmb_inner (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) (u w : Amb 6) :
    inner ℝ (probeEmb k m hk hm u) (probeEmb k m hk hm w) = inner ℝ u w := by
  have h1 : ∀ i j : Fin 6,
      inner ℝ (u.ofLp i • (EuclideanSpace.single (𝕜 := ℝ) (probeAmbIdx k m hk hm i) 1 : Amb (k + m)))
        (w.ofLp j • (EuclideanSpace.single (𝕜 := ℝ) (probeAmbIdx k m hk hm j) 1 : Amb (k + m)))
      = (u.ofLp i) * (w.ofLp j) * (if i = j then (1:ℝ) else 0) := by
    intro i j
    rw [real_inner_smul_left, real_inner_smul_right, inner_single_ite]
    by_cases h : i = j
    · rw [if_pos h, if_pos (by rw [h])]; ring
    · rw [if_neg h, if_neg (fun hij => h (probeAmbIdx_injective k m hk hm hij))]; ring
  rw [probeEmb_apply, probeEmb_apply, sum_inner]
  conv_lhs => enter [2, i]; rw [inner_sum]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => h1 i j))]
  rw [show inner ℝ u w = ∑ i : Fin 6, (u.ofLp i) * (w.ofLp i) from by
    rw [PiLp.inner_apply]
    exact Finset.sum_congr rfl (fun i _ => by
      rw [RCLike.inner_apply]
      simp only [starRingEnd_apply, star_trivial]
      ring)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.sum_eq_single j]
  · rw [if_pos rfl, mul_one]
  · intro i _ hij; rw [if_neg hij, mul_zero]
  · intro h; exact absurd (Finset.mem_univ j) h

theorem probeEmb_norm (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) (u : Amb 6) :
    ‖probeEmb k m hk hm u‖ = ‖u‖ := by
  have h := probeEmb_inner k m hk hm u u
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg (probeEmb k m hk hm u), norm_nonneg u]

theorem probeEmb_injective (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) :
    Function.Injective (probeEmb k m hk hm) := by
  intro u w h
  have h2 : ‖probeEmb k m hk hm (u - w)‖ = 0 := by
    rw [map_sub, h, sub_self, norm_zero]
  rw [probeEmb_norm, norm_eq_zero] at h2
  exact sub_eq_zero.mp h2

theorem probeCy_apply (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) (z : Amb (k + m)) :
    probeCy k m hk hm z = ∑ i : Fin 6, z.ofLp (probeAmbIdx k m hk hm i) •
      (EuclideanSpace.single (𝕜 := ℝ) i 1 : Amb 6) := by
  simp only [probeCy, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [ContinuousLinearMap.smulRight_apply]
  rfl

theorem probeCy_inner (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) (z : Amb (k + m)) (u : Amb 6) :
    inner ℝ (probeCy k m hk hm z) u = inner ℝ z (probeEmb k m hk hm u) := by
  have hL : inner ℝ (probeCy k m hk hm z) u
      = ∑ i : Fin 6, z.ofLp (probeAmbIdx k m hk hm i) * u.ofLp i := by
    rw [probeCy_apply, sum_inner]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [real_inner_smul_left, inner_single_left']
  have hR : inner ℝ z (probeEmb k m hk hm u)
      = ∑ i : Fin 6, z.ofLp (probeAmbIdx k m hk hm i) * u.ofLp i := by
    rw [probeEmb_apply, inner_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [real_inner_smul_right, inner_single_right']
    ring
  rw [hL, hR]

theorem probeCy_probeEmb (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) (u : Amb 6) :
    probeCy k m hk hm (probeEmb k m hk hm u) = u := by
  rw [probeCy_apply]
  rw [Finset.sum_congr rfl (fun i _ => by rw [probeEmb_coord])]
  exact sum_single_eq 6 u

/-! ## The fixed complement frame -/

theorem probeTailVec_inner (k m : ℕ) (hk : 2 ≤ k) (l l' : Fin (k - 2)) :
    inner ℝ (probeTailVec k m hk l) (probeTailVec k m hk l') = if l = l' then (1:ℝ) else 0 := by
  rw [probeTailVec, probeTailVec, inner_single_ite]
  by_cases h : l = l'
  · rw [if_pos h, if_pos (by rw [h])]
  · rw [if_neg h, if_neg (fun hh => h (probeTailIdx_injective k m hk hh))]

theorem probeTailVec_orthonormal (k m : ℕ) (hk : 2 ≤ k) :
    Orthonormal ℝ (probeTailVec k m hk) := by
  rw [orthonormal_iff_ite]
  exact probeTailVec_inner k m hk

theorem probeTailComb_apply (k m : ℕ) (hk : 2 ≤ k) (u : Amb (k - 2)) :
    probeTailComb k m hk u = ∑ l : Fin (k - 2), u.ofLp l • probeTailVec k m hk l := by
  simp only [probeTailComb, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [ContinuousLinearMap.smulRight_apply]
  rfl

theorem probeUx_apply (k m : ℕ) (hk : 2 ≤ k) (z : Amb (k + m)) :
    probeUx k m hk z = ∑ l : Fin (k - 2), z.ofLp (probeTailIdx k m hk l) •
      (EuclideanSpace.single (𝕜 := ℝ) l 1 : Amb (k - 2)) := by
  simp only [probeUx, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [ContinuousLinearMap.smulRight_apply]
  rfl

theorem probeTailComb_coord (k m : ℕ) (hk : 2 ≤ k) (u : Amb (k - 2)) (l : Fin (k - 2)) :
    (probeTailComb k m hk u).ofLp (probeTailIdx k m hk l) = u.ofLp l := by
  rw [probeTailComb_apply, WithLp.ofLp_sum, Finset.sum_apply]
  rw [Finset.sum_eq_single l]
  · rw [WithLp.ofLp_smul, Pi.smul_apply, probeTailVec, single_coord_self, if_pos rfl,
      smul_eq_mul, mul_one]
  · intro l' _ hl'
    rw [WithLp.ofLp_smul, Pi.smul_apply, probeTailVec,
      single_coord_ne (a := probeTailIdx k m hk l') (b := probeTailIdx k m hk l)
        (fun hh => hl' (probeTailIdx_injective k m hk hh.symm)), smul_zero]
  · intro h; exact absurd (Finset.mem_univ l) h

theorem probeUx_tailComb (k m : ℕ) (hk : 2 ≤ k) (u : Amb (k - 2)) :
    probeUx k m hk (probeTailComb k m hk u) = u := by
  rw [probeUx_apply]
  rw [Finset.sum_congr rfl (fun l _ => by rw [probeTailComb_coord])]
  exact sum_single_eq (k - 2) u

theorem probeTailComb_inner (k m : ℕ) (hk : 2 ≤ k) (u : Amb (k - 2)) (z : Amb (k + m)) :
    inner ℝ (probeTailComb k m hk u) z = inner ℝ u (probeUx k m hk z) := by
  have hL : inner ℝ (probeTailComb k m hk u) z
      = ∑ l : Fin (k - 2), u.ofLp l * z.ofLp (probeTailIdx k m hk l) := by
    rw [probeTailComb_apply, sum_inner]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [real_inner_smul_left, probeTailVec, inner_single_left']
  have hR : inner ℝ u (probeUx k m hk z)
      = ∑ l : Fin (k - 2), u.ofLp l * z.ofLp (probeTailIdx k m hk l) := by
    rw [probeUx_apply, inner_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [real_inner_smul_right, inner_single_right']
    ring
  rw [hL, hR]

theorem probeUx_probeEmb (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) (z : Amb 6) :
    probeUx k m hk (probeEmb k m hk hm z) = 0 := by
  rw [probeUx_apply]
  refine Finset.sum_eq_zero (fun l _ => ?_)
  have h : (probeEmb k m hk hm z).ofLp (probeTailIdx k m hk l) = 0 := by
    rw [probeEmb_apply, WithLp.ofLp_sum, Finset.sum_apply]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [WithLp.ofLp_smul, Pi.smul_apply,
      single_coord_ne (a := probeAmbIdx k m hk hm i) (b := probeTailIdx k m hk l)
        (fun hh => probeAmbIdx_ne_probeTailIdx k m hk hm i l hh.symm), smul_zero]
  rw [h, zero_smul]

end

end Work.ThomBordism.Grassmann
