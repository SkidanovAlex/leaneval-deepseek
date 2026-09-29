import Mathlib
import Submission.Work.TMContract.Defs

/-!
# Projective lifts of `SL(2,ℝ)`-matrices (C13 infrastructure)

A matrix `M : Matrix (Fin 2) (Fin 2) ℝ` with nonzero determinant acts on the circle of
*unoriented directions* in `ℝ²`.  We parametrize directions by half-turns: the direction of
`(cos (π t), sin (π t))` is called `t`.  A *projective lift* of `M` is a continuous function
`g : ℝ → ℝ` with `g (t + 1) = g t + 1` which sends the direction `t` to the direction `g t`.

The main lemma of this file is `eq_add_int_of_dir_eq`: two such lifts of the *same* matrix
differ by a constant integer.  This is the "lift calculus" that turns the matrix identity
`C (x + α) * tmR lam E x = rot (φ x) * C x` into an identity of lifts of the Prüfer type.
-/

noncomputable section

namespace Work.TMC13

open Matrix Filter

open scoped Topology

/-- The direction vector whose half-turn angle is `t`. -/
def dvec (t : ℝ) : Fin 2 → ℝ := ![Real.cos (Real.pi * t), Real.sin (Real.pi * t)]

@[simp] lemma dvec_zero_coord (t : ℝ) : dvec t 0 = Real.cos (Real.pi * t) := rfl

@[simp] lemma dvec_one_coord (t : ℝ) : dvec t 1 = Real.sin (Real.pi * t) := rfl

lemma dvec_ne_zero (t : ℝ) : dvec t ≠ 0 := by
  intro h
  have h0 : Real.cos (Real.pi * t) = 0 := by
    have := congrFun h 0; simpa using this
  have h1 : Real.sin (Real.pi * t) = 0 := by
    have := congrFun h 1; simpa using this
  have h2 := Real.cos_sq_add_sin_sq (Real.pi * t)
  rw [h0, h1] at h2
  norm_num at h2

/-- `g` is a projective lift of `M`: continuous, degree one, and direction preserving. -/
def IsProjLift (M : Matrix (Fin 2) (Fin 2) ℝ) (g : ℝ → ℝ) : Prop :=
  Continuous g ∧ (∀ t, g (t + 1) = g t + 1) ∧
    ∀ t, ∃ c : ℝ, c ≠ 0 ∧ M.mulVec (dvec t) = c • dvec (g t)

/-- Two real numbers whose direction vectors are proportional differ by an integer. -/
lemma exists_int_sub_of_dvec_eq {s s' : ℝ}
    (h : ∃ c : ℝ, c ≠ 0 ∧ dvec s = c • dvec s') : ∃ k : ℤ, s - s' = k := by
  obtain ⟨c, hc, hcs⟩ := h
  have h1 : Real.cos (Real.pi * s) = c * Real.cos (Real.pi * s') := by
    have := congrFun hcs 0
    simpa [Pi.smul_apply, mul_comm] using this
  have h2 : Real.sin (Real.pi * s) = c * Real.sin (Real.pi * s') := by
    have := congrFun hcs 1
    simpa [Pi.smul_apply, mul_comm] using this
  have hcsq : Real.cos (Real.pi * s') ^ 2 + Real.sin (Real.pi * s') ^ 2 = 1 :=
    Real.cos_sq_add_sin_sq _
  have hc2 : c ^ 2 = 1 := by
    have h3 : Real.cos (Real.pi * s) ^ 2 + Real.sin (Real.pi * s) ^ 2 = 1 :=
      Real.cos_sq_add_sin_sq _
    rw [h1, h2, mul_pow, mul_pow] at h3
    nlinarith [h3, hcsq]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  rcases eq_or_eq_neg_of_sq_eq_sq c 1 (by rw [hc2]; norm_num) with hc1 | hc1
  · subst hc1
    simp only [one_mul] at h1 h2
    have hcos : Real.cos (Real.pi * (s - s')) = 1 := by
      have : Real.cos (Real.pi * s - Real.pi * s') = 1 := by
        rw [Real.cos_sub, h1, h2]
        nlinarith [hcsq]
      simpa [mul_sub] using this
    obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff _).mp hcos
    refine ⟨2 * n, ?_⟩
    have hn' : (n : ℝ) * (2 * Real.pi) = Real.pi * (s - s') := hn
    have hs : s - s' = 2 * n := by
      have h2' : ((n : ℝ) * 2) * Real.pi = (s - s') * Real.pi := by
        have := hn'; ring_nf at this ⊢; linarith [this]
      have h3 := mul_right_cancel₀ hpi h2'
      push_cast
      linarith [h3]
    rw [hs]; push_cast; ring
  · subst hc1
    simp only [neg_mul] at h1 h2
    have hcos : Real.cos (Real.pi * (s - s')) = -1 := by
      have : Real.cos (Real.pi * s - Real.pi * s') = -1 := by
        rw [Real.cos_sub, h1, h2]
        nlinarith [hcsq]
      simpa [mul_sub] using this
    have hcos1 : Real.cos (Real.pi * (s - s') - Real.pi) = 1 := by
      rw [Real.cos_sub, hcos, Real.cos_pi, Real.sin_pi]
      ring
    obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff _).mp hcos1
    refine ⟨2 * n + 1, ?_⟩
    have hn' : (n : ℝ) * (2 * Real.pi) = Real.pi * (s - s') - Real.pi := hn
    have hs : s - s' = 2 * n + 1 := by
      have h2' : ((n : ℝ) * 2 + 1) * Real.pi = (s - s') * Real.pi := by
        have := hn'; ring_nf at this ⊢; linarith [this]
      have h3 := mul_right_cancel₀ hpi h2'
      push_cast
      linarith [h3]
    rw [hs]; push_cast; ring

/-- A continuous real function that only takes integer values is constant. -/
lemma exists_int_eq_const {f : ℝ → ℝ} (hf : Continuous f)
    (hint : ∀ t : ℝ, ∃ k : ℤ, f t = k) : ∃ k : ℤ, ∀ t : ℝ, f t = k := by
  have hlc : IsLocallyConstant f := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro t
    have hball : ∀ᶠ s in 𝓝 t, f s ∈ Set.Ioo (f t - 1/2) (f t + 1/2) :=
      hf.continuousAt (Ioo_mem_nhds (by linarith) (by linarith))
    filter_upwards [hball] with s hs
    obtain ⟨k', hk'⟩ := hint s
    obtain ⟨k, hk⟩ := hint t
    rw [hk', hk] at hs
    simp only [Set.mem_Ioo] at hs
    have h3 : -1 < (k' - k : ℤ) := by
      have hh : ((-1 : ℤ) : ℝ) < ((k' - k : ℤ) : ℝ) := by
        push_cast
        linarith [hs.1]
      exact_mod_cast hh
    have h4 : (k' - k : ℤ) < 1 := by
      have hh : ((k' - k : ℤ) : ℝ) < ((1 : ℤ) : ℝ) := by
        push_cast
        linarith [hs.2]
      exact_mod_cast hh
    have h5 : k' = k := by omega
    rw [hk', hk, h5]
  obtain ⟨k, hk⟩ := hint 0
  refine ⟨k, fun t => ?_⟩
  rw [hlc.apply_eq_of_isPreconnected isPreconnected_univ (Set.mem_univ t) (Set.mem_univ 0), hk]

/-- **Lift calculus.**  Two continuous degree-one functions inducing the same map on the
circle of directions differ by a constant integer. -/
theorem eq_add_int_of_dir_eq {g g' : ℝ → ℝ} (hg : Continuous g) (hg' : Continuous g')
    (hd : ∀ t, ∃ c : ℝ, c ≠ 0 ∧ dvec (g t) = c • dvec (g' t)) :
    ∃ k : ℤ, ∀ t, g t = g' t + k := by
  have hint : ∀ t : ℝ, ∃ k : ℤ, g t - g' t = k := by
    intro t
    obtain ⟨k, hk⟩ := exists_int_sub_of_dvec_eq (hd t)
    exact ⟨k, hk⟩
  obtain ⟨k, hk⟩ := exists_int_eq_const (hg.sub hg') hint
  exact ⟨k, fun t => by have h := hk t; rw [Pi.sub_apply] at h; linarith⟩

lemma IsProjLift.continuous {M : Matrix (Fin 2) (Fin 2) ℝ} {g : ℝ → ℝ} (h : IsProjLift M g) :
    Continuous g := h.1

/-- Two projective lifts of the same matrix differ by a constant integer. -/
theorem IsProjLift.eq_add_int {M : Matrix (Fin 2) (Fin 2) ℝ} {g g' : ℝ → ℝ}
    (hg : IsProjLift M g) (hg' : IsProjLift M g') : ∃ k : ℤ, ∀ t, g t = g' t + k := by
  refine eq_add_int_of_dir_eq hg.1 hg'.1 (fun t => ?_)
  obtain ⟨c₁, hc₁, h1⟩ := hg.2.2 t
  obtain ⟨c₂, hc₂, h2⟩ := hg'.2.2 t
  have key : c₁ • dvec (g t) = c₂ • dvec (g' t) := by rw [← h1, h2]
  refine ⟨c₂ / c₁, div_ne_zero hc₂ hc₁, ?_⟩
  have h3 : dvec (g t) = c₁⁻¹ • (c₁ • dvec (g t)) := by
    rw [smul_smul, inv_mul_cancel₀ hc₁, one_smul]
  rw [h3, key, smul_smul, div_eq_inv_mul]

theorem IsProjLift.comp {M N : Matrix (Fin 2) (Fin 2) ℝ} {g g' : ℝ → ℝ}
    (hg : IsProjLift M g) (hg' : IsProjLift N g') : IsProjLift (M * N) (g ∘ g') := by
  refine ⟨hg.1.comp hg'.1, fun t => ?_, fun t => ?_⟩
  · show g (g' (t + 1)) = g (g' t) + 1
    rw [hg'.2.1 t, hg.2.1]
  · obtain ⟨c, hc, h1⟩ := hg'.2.2 t
    obtain ⟨d, hd, h2⟩ := hg.2.2 (g' t)
    refine ⟨c * d, mul_ne_zero hc hd, ?_⟩
    show (M * N).mulVec (dvec t) = (c * d) • dvec (g (g' t))
    rw [← Matrix.mulVec_mulVec, h1, Matrix.mulVec_smul, h2, smul_smul]

/-- The rotation matrix induces the translation by `2 c` in half-turn coordinates. -/
theorem isProjLift_rot (c : ℝ) : IsProjLift (Work.TMContract.rot c) (fun t => t + 2 * c) := by
  refine ⟨by fun_prop, fun t => by ring, fun t => ⟨1, one_ne_zero, ?_⟩⟩
  show (Work.TMContract.rot c).mulVec (dvec t) = (1 : ℝ) • dvec (t + 2 * c)
  ext i
  fin_cases i
  · simp only [Matrix.mulVec_fin_two, dvec, Work.TMContract.rot]
    simp
    try (rw [show Real.pi * (t + 2 * c) = 2 * Real.pi * c + Real.pi * t by ring, Real.cos_add])
    try ring
  · simp only [Matrix.mulVec_fin_two, dvec, Work.TMContract.rot]
    simp
    try (rw [show Real.pi * (t + 2 * c) = 2 * Real.pi * c + Real.pi * t by ring, Real.sin_add])
    try ring

end Work.TMC13
