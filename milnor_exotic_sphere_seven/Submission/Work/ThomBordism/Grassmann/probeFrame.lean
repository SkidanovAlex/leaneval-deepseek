import Mathlib
import Submission.Work.ThomBordism.Grassmann.probeCoords

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

/-! ## The unit vector of a complex line -/

theorem cxOf_ne_zero {v : Fin 3 → ℂ} (hv : v ≠ 0) : cxOf v ≠ 0 := by
  intro h
  rw [WithLp.ext_iff] at h
  exact hv (by simpa [cxOf] using h)

theorem cxUnit_norm {v : Fin 3 → ℂ} (hv : v ≠ 0) : ‖cxUnit v‖ = 1 := by
  have hne : ‖cxOf v‖ ≠ 0 := norm_ne_zero_iff.mpr (cxOf_ne_zero hv)
  rw [cxUnit, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _),
    inv_mul_cancel₀ hne]

theorem cxUnit_ne_zero {v : Fin 3 → ℂ} (hv : v ≠ 0) : cxUnit v ≠ 0 := by
  intro h
  have := cxUnit_norm hv
  rw [h, norm_zero] at this
  exact one_ne_zero this.symm

theorem probeTailVec_eq_tailComb (k m : ℕ) (hk : 2 ≤ k) (l : Fin (k - 2)) :
    probeTailVec k m hk l
      = probeTailComb k m hk (EuclideanSpace.single (𝕜 := ℝ) l (1:ℝ)) := by
  rw [probeTailComb_apply]
  rw [Finset.sum_eq_single l]
  · rw [single_coord_self, if_pos rfl, one_smul]
  · intro l' _ hl'
    rw [single_coord_ne (a := l) (b := l') hl', zero_smul]
  · intro h; exact absurd (Finset.mem_univ l) h

theorem probePairVec_val (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) (v : Fin 3 → ℂ) (a : Fin 2) :
    probePairVec k m hk hm v a = probeEmb k m hk hm (cxE (cxUnit v))
      ∨ probePairVec k m hk hm v a
        = -(probeEmb k m hk hm (cxE (Complex.I • cxUnit v))) := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem probePairVec_inner_tail (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) (v : Fin 3 → ℂ)
    (l : Fin (k - 2)) (a : Fin 2) :
    inner ℝ (probeTailVec k m hk l) (probePairVec k m hk hm v a) = 0 := by
  rw [probeTailVec_eq_tailComb, probeTailComb_inner]
  rcases probePairVec_val k m hk hm v a with h | h
  · rw [h, probeUx_probeEmb, inner_zero_right]
  · rw [h, map_neg, probeUx_probeEmb, neg_zero, inner_zero_right]

/-- **The orthogonality of `probeEmb`'s image and the fixed complement frame.** -/
theorem probeEmb_orthogonal_tailComb (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) (z : Amb 6)
    (u : Amb (k - 2)) :
    inner ℝ (probeEmb k m hk hm z) (probeTailComb k m hk u) = 0 := by
  rw [real_inner_comm, probeTailComb_inner, probeUx_probeEmb, inner_zero_right]

/-! ## The frame is orthonormal -/

theorem probePairVec_inner (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) (v : Fin 3 → ℂ) (hv : v ≠ 0) :
    ∀ a a' : Fin 2, inner ℝ (probePairVec k m hk hm v a) (probePairVec k m hk hm v a')
      = if a = a' then (1:ℝ) else 0 := by
  have hu : ‖cxUnit v‖ = 1 := cxUnit_norm hv
  have hI : ‖Complex.I • cxUnit v‖ = 1 := by
    rw [norm_smul, Complex.norm_I, one_mul]; exact hu
  have horth : inner ℝ (cxUnit v) (Complex.I • cxUnit v) = 0 := real_inner_I_smul_self ℂ _
  have hX : inner ℝ (probeEmb k m hk hm (cxE (cxUnit v)))
      (probeEmb k m hk hm (cxE (cxUnit v))) = 1 := by
    rw [probeEmb_inner k m hk hm (cxE (cxUnit v)) (cxE (cxUnit v)),
      cxE.inner_map_map, real_inner_self_eq_norm_sq, hu]
    norm_num
  have hY : inner ℝ (probeEmb k m hk hm (cxE (Complex.I • cxUnit v)))
      (probeEmb k m hk hm (cxE (Complex.I • cxUnit v))) = 1 := by
    rw [probeEmb_inner k m hk hm (cxE (Complex.I • cxUnit v)) (cxE (Complex.I • cxUnit v)),
      cxE.inner_map_map, real_inner_self_eq_norm_sq, hI]
    norm_num
  have hXY : inner ℝ (probeEmb k m hk hm (cxE (cxUnit v)))
      (probeEmb k m hk hm (cxE (Complex.I • cxUnit v))) = 0 := by
    rw [probeEmb_inner k m hk hm (cxE (cxUnit v)) (cxE (Complex.I • cxUnit v)),
      cxE.inner_map_map, horth]
  intro a a'
  fin_cases a <;> fin_cases a' <;> simp only [probePairVec, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, if_true, if_false, reduceCtorEq,
    not_false_eq_true, one_ne_zero, zero_ne_one, Fin.zero_eta, Fin.mk_one]
  · exact hX
  · rw [inner_neg_right, hXY, neg_zero]
  · rw [inner_neg_left, real_inner_comm, hXY, neg_zero]
  · rw [inner_neg_left, inner_neg_right, hY, neg_neg]

theorem probeFrameRep_orthonormal (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m)
    (v : Fin 3 → ℂ) (hv : v ≠ 0) :
    Orthonormal ℝ (probeFrameRep k m hk hm v) := by
  rw [orthonormal_iff_ite]
  intro i j
  obtain ⟨p, rfl⟩ := (probeSplit k hk).surjective i
  obtain ⟨q, rfl⟩ := (probeSplit k hk).surjective j
  have hiff : ∀ x y : Fin 2, (probeSplit k hk (Sum.inl x) = probeSplit k hk (Sum.inl y))
      ↔ x = y := by
    intro x y
    exact ⟨fun h => Sum.inl_injective ((probeSplit k hk).injective h), fun h => by rw [h]⟩
  rcases p with a | l <;> rcases q with a' | l'
  · rw [probeFrameRep_inl, probeFrameRep_inl, probePairVec_inner k m hk hm v hv a a']
    by_cases h : a = a'
    · rw [if_pos h, if_pos ((hiff a a').mpr h)]
    · rw [if_neg h, if_neg (fun hij => h ((hiff a a').mp hij))]
  · rw [probeFrameRep_inl, probeFrameRep_inr, real_inner_comm, probePairVec_inner_tail]
    exact (if_neg (fun hij => Sum.inl_ne_inr ((probeSplit k hk).injective hij))).symm
  · rw [probeFrameRep_inr, probeFrameRep_inl, probePairVec_inner_tail]
    exact (if_neg (fun hij => Sum.inr_ne_inl ((probeSplit k hk).injective hij))).symm
  · rw [probeFrameRep_inr, probeFrameRep_inr, probeTailVec_inner]
    by_cases h : l = l'
    · rw [if_pos h, if_pos (by rw [h])]
    · rw [if_neg h, if_neg (fun hij => h (Sum.inr_injective ((probeSplit k hk).injective hij)))]

end

end Work.ThomBordism.Grassmann
