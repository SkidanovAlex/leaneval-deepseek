import Mathlib
import Submission.Work.ORVonNeumann.Rep.vnCore

open scoped InnerProduct
open scoped InnerProductSpace

-- `haveI` is used below to make `CompleteSpace A.range` available for instance search.
set_option linter.style.haveILetI false

namespace Work.ORVonNeumann.Rep

/-- For every bounded operator `T : HSum m → HSum n` and every `ε > 0`, the positive
self-adjoint operator `T† ∘ T + ε • 1` on `HSum m` is invertible (as a bounded operator):
it is bounded below by `ε`, hence injective and with closed range, and being self-adjoint
its range is dense, so it is surjective. -/
theorem vnExistsInvAdd {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] {m n : ℕ} (T : Work.ORVonNeumann.Rep.HSum (G := G) m →L[ℂ] Work.ORVonNeumann.Rep.HSum (G := G) n) {ε : ℝ} (hε : 0 < ε) : ∃ S : Work.ORVonNeumann.Rep.HSum (G := G) m →L[ℂ] Work.ORVonNeumann.Rep.HSum (G := G) m, S.comp ((ContinuousLinearMap.adjoint T).comp T + (ε : ℂ) • 1) = 1 ∧ ((ContinuousLinearMap.adjoint T).comp T + (ε : ℂ) • 1).comp S = 1 := by
  set A : HSum (G:=G) m →L[ℂ] HSum (G:=G) m :=
    (ContinuousLinearMap.adjoint T).comp T + (ε : ℂ) • 1 with hAdef
  -- `A` is bounded below by `ε`
  have hbound : ∀ x : HSum (G:=G) m, ε * ‖x‖ ≤ ‖A x‖ := by
    intro x
    have hsmul : ∀ z : HSum (G:=G) m,
        RCLike.re (inner ℂ ((ε:ℂ) • z) z) = ε * ‖z‖^2 := by
      intro z
      calc RCLike.re (inner ℂ ((ε:ℂ) • z) z)
          = RCLike.re ((ε:ℂ) * inner ℂ z z) := by rw [inner_smul_left, Complex.conj_ofReal]
        _ = ε * RCLike.re (inner ℂ z z) := RCLike.re_ofReal_mul ε _
        _ = ε * ‖z‖^2 := by rw [inner_self_eq_norm_sq]
    have hadj : RCLike.re (inner ℂ ((T†) (T x)) x) = ‖T x‖^2 := by
      rw [ContinuousLinearMap.adjoint_inner_left]
      exact inner_self_eq_norm_sq _
    have h1 : RCLike.re (inner ℂ (A x) x) = ‖T x‖^2 + ε * ‖x‖^2 := by
      have hAx : A x = (T†) (T x) + (ε:ℂ) • x := by rw [hAdef]; rfl
      rw [hAx, inner_add_left, map_add, hadj, hsmul]
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx
      have h2 : RCLike.re (inner ℂ (A x) x) ≤ ‖A x‖ * ‖x‖ := re_inner_le_norm _ _
      have h3 : ε * ‖x‖^2 ≤ ‖A x‖ * ‖x‖ := by
        rw [h1] at h2; nlinarith [sq_nonneg ‖T x‖]
      nlinarith [h3, hxn]
  -- `A` is self-adjoint
  have hstar : A† = A := by
    rw [hAdef]
    rw [eq_comm, ContinuousLinearMap.eq_adjoint_iff]
    intro x y
    simp only [add_apply, ContinuousLinearMap.comp_apply, one_apply_eq_self, smul_apply]
    rw [inner_add_left, inner_add_right, ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.adjoint_inner_right, inner_smul_left, inner_smul_right,
      Complex.conj_ofReal]
  -- injectivity
  have hker : A.ker = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro x y hxy
    have h : ε * ‖x - y‖ ≤ ‖A (x - y)‖ := hbound (x - y)
    have hzero : A (x - y) = 0 := by rw [map_sub]; exact sub_eq_zero.mpr hxy
    rw [hzero, norm_zero] at h
    have h1 : ‖x - y‖ = 0 := by nlinarith [h, hε, norm_nonneg (x - y)]
    exact sub_eq_zero.mp (norm_eq_zero.mp h1)
  -- `A` is antilipschitz, hence has closed range
  have hanti : AntilipschitzWith (ε⁻¹).toNNReal A := by
    apply ContinuousLinearMap.antilipschitz_of_bound
    intro x
    rw [Real.coe_toNNReal _ (le_of_lt (inv_pos.mpr hε)), le_inv_mul_iff₀ hε]
    exact hbound x
  have hclosed : IsClosed (A.range : Set (HSum (G:=G) m)) :=
    hanti.isClosed_range A.uniformContinuous
  -- self-adjointness upgrades closed range to surjectivity
  have hSA : IsSelfAdjoint A := hstar
  have hSN : IsStarNormal A := hSA.isStarNormal
  have horth : A.rangeᗮ = ⊥ := by
    rw [ContinuousLinearMap.IsStarNormal.orthogonal_range hSN, hker]
  have hrange : A.range = ⊤ := by
    haveI : CompleteSpace A.range := hclosed.completeSpace_coe
    exact Submodule.orthogonal_eq_bot_iff.mp horth
  obtain ⟨e, he⟩ : ∃ e : HSum (G:=G) m ≃L[ℂ] HSum (G:=G) m, ⇑e = ⇑A :=
    ⟨ContinuousLinearEquiv.ofBijective A hker hrange,
      ContinuousLinearEquiv.coeFn_ofBijective A hker hrange⟩
  refine ⟨e.symm.toContinuousLinearMap, ?_, ?_⟩
  · apply ContinuousLinearMap.ext; intro x
    change e.symm (A x) = x
    rw [← he, ContinuousLinearEquiv.symm_apply_apply]
  · apply ContinuousLinearMap.ext; intro x
    change A (e.symm x) = x
    rw [← he, ContinuousLinearEquiv.apply_symm_apply]

end Work.ORVonNeumann.Rep
