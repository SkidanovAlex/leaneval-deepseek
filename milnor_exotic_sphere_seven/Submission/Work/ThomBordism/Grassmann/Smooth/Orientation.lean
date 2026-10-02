import Mathlib
import Submission.Work.ThomBordism.Grassmann.Smooth.Graph
import Submission.Work.ThomBordism.Grassmann.Linear

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

/-!
# Orientation of frames and the points of the Grassmannian they define

Two orthonormal frames of the same subspace of `ℝ^{k+m}` define the same point of the oriented
Grassmannian `G̃r_k(ℝ^{k+m})` exactly when they induce the same orientation, which is detected by the
sign of the `S`-minor of the frame matrix (`mkEqOfDetSign`).
-/

open scoped Topology

namespace Work.ThomBordism.Grassmann.Smooth

noncomputable section

variable {k m : ℕ}

/-- A vector of `span f` is determined by its `S`-coordinates when the `S`-minor of `f` does not
vanish. -/
theorem eq_of_mem_span_of_coordinates_eq {S : ChartIdx k m} {f : Fin k → Amb (k + m)}
    (hdet : (frameMatrix S f).det ≠ 0) {u v : Amb (k + m)}
    (hu : u ∈ Submodule.span ℝ (Set.range f)) (hv : v ∈ Submodule.span ℝ (Set.range f))
    (h : ∀ i, u (idxS S i) = v (idxS S i)) : u = v := by
  classical
  have h1 : u - v ∈ Submodule.span ℝ (Set.range f) := Submodule.sub_mem _ hu hv
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp h1
  have hof : (u - v).ofLp = coeffMap f c := by
    rw [← hc]
    funext y
    simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, coeffMap_apply]
    exact Finset.sum_congr rfl fun i _ => by simp

  have hker : coordProj S ((u - v).ofLp) = 0 := by
    rw [coordProj_eq_zero_iff]
    intro y hy
    have h4 : ((u - v).ofLp) y = u.ofLp y - v.ofLp y := by
      rw [← ofLpCLM_apply, map_sub, Pi.sub_apply, ofLpCLM_apply, ofLpCLM_apply]
    rw [h4]
    have h5 : u.ofLp y = v.ofLp y := by
      have h6 := h ((S.1.equivFinOfCardEq S.2) ⟨y, hy⟩)
      rwa [idxS_apply S y hy] at h6
    rw [h5, sub_self]

  have hzero : (frameMatrix S f).mulVec c = 0 := by
    have h2 : (Matrix.toLin' (frameMatrix S f)) c = coordProj S (coeffMap f c) := by
      rw [toLin'_frameMatrix]
      rfl
    have h3 : (Matrix.toLin' (frameMatrix S f)) c = 0 := by
      rw [h2, ← hof]
      exact hker
    rwa [Matrix.toLin'_apply] at h3
  have hc0 : c = 0 := by
    have h5 : (frameMatrix S f)⁻¹.mulVec ((frameMatrix S f).mulVec c) = c := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet),
        Matrix.one_mulVec]
    rw [hzero, Matrix.mulVec_zero] at h5
    exact h5.symm
  rw [hc0] at hc
  simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero] at hc
  exact sub_eq_zero.mp hc.symm

/-- **Two orthonormal frames of the same subspace whose `S`-minors have the same sign define the
same point of the oriented Grassmannian.** -/
theorem mkEqOfDetSign {S : ChartIdx k m} {f g : Fin k → Amb (k + m)}
    (hf : Orthonormal ℝ f) (hg : Orthonormal ℝ g)
    (hspan : Submodule.span ℝ (Set.range f) = Submodule.span ℝ (Set.range g))
    (hdetf : (frameMatrix S f).det ≠ 0)
    (hsign : 0 < (frameMatrix S f).det * (frameMatrix S g).det) :
    (Quotient.mk'' (⟨g, hg⟩ : Stiefel k m) : OG k m)
      = Quotient.mk'' (⟨f, hf⟩ : Stiefel k m) := by
  classical
  have hunit : IsUnit (frameMatrix S f).det := isUnit_iff_ne_zero.mpr hdetf
  have hdetg : (frameMatrix S g).det ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hsign
    exact lt_irrefl 0 hsign
  set A : Matrix (Fin k) (Fin k) ℝ := (frameMatrix S f)⁻¹ * frameMatrix S g with hA
  have hmat : frameMatrix S (soActFun A f) = frameMatrix S g := by
    rw [frameMatrix_soActFun, hA, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hunit, Matrix.one_mul]
  have hmemf : ∀ i, soActFun A f i ∈ Submodule.span ℝ (Set.range f) := by
    intro i
    rw [soActFun]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hmemg : ∀ i, g i ∈ Submodule.span ℝ (Set.range f) := by
    intro i
    rw [hspan]
    exact Submodule.subset_span ⟨i, rfl⟩
  have hfg : soActFun A f = g := by
    funext i
    refine eq_of_mem_span_of_coordinates_eq hdetf (hmemf i) (hmemg i) fun l => ?_
    show (soActFun A f i) (idxS S l) = (g i) (idxS S l)
    rw [show (soActFun A f i) (idxS S l) = frameMatrix S (soActFun A f) l i from rfl,
      show (g i) (idxS S l) = frameMatrix S g l i from rfl, hmat]
  have hAorth : A.transpose * A = 1 := by
    ext i j
    have key : inner ℝ (soActFun A f i) (soActFun A f j) = (A.transpose * A) i j := by
      have h1 : inner ℝ (soActFun A f i) (soActFun A f j) = ∑ l, A l i * A l j := by
        simp only [soActFun]
        rw [sum_inner]
        refine Finset.sum_congr rfl fun l _ => ?_
        have h2 : inner ℝ (f l) (∑ n, A n j • f n) = A l j := by
          rw [inner_sum]
          rw [Finset.sum_eq_single l]
          · rw [inner_smul_right, orthonormal_iff_ite.mp hf, if_pos rfl, mul_one]
          · intro n _ hn
            rw [inner_smul_right, orthonormal_iff_ite.mp hf, if_neg (Ne.symm hn), mul_zero]
          · intro h; exact absurd (Finset.mem_univ l) h
        rw [inner_smul_left, h2]
        simp
      rw [h1, Matrix.mul_apply]
      exact Finset.sum_congr rfl fun l _ => by rw [Matrix.transpose_apply]
    rw [← key, hfg, orthonormal_iff_ite.mp hg, Matrix.one_apply]

  have hAdet : A.det = 1 := by
    have h1 : (frameMatrix S g).det = (frameMatrix S f).det * A.det := by
      rw [← hmat, det_frameMatrix_soActFun]
    have h2 : A.det * A.det = 1 := by
      have := congrArg Matrix.det hAorth
      rwa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at this
    rcases mul_self_eq_one_iff.mp h2 with h | h
    · exact h
    · exfalso
      have h3 : (frameMatrix S f).det * (frameMatrix S g).det
          = -((frameMatrix S f).det * (frameMatrix S f).det) := by
        rw [h1, h]
        ring
      rw [h3] at hsign
      nlinarith [mul_self_nonneg (frameMatrix S f).det]
  refine (Quot.sound ?_).symm
  exact ⟨⟨A, hAorth, hAdet⟩, Subtype.ext hfg.symm⟩

end

end Work.ThomBordism.Grassmann.Smooth
