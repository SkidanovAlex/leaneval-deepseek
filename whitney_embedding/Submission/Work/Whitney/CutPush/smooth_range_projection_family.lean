import Mathlib

/-!
# The orthogonal projection onto the image of a smooth family of injections

The dual of `CutPush/smooth_kernel_projection_family.lean`.  The fibered flattening of the collar
uses the smooth family of planes `T t = range (Ψ t)` (concretely: the slice tangent planes, given
by a smooth frame field `Ψ`), and the per-fiber shear needs their orthogonal projections, smoothly in
`t`.

This file proves: for a smooth family `Ψ : ℝ → E →L[ℝ] F` with every `Ψ t` **injective**, there is a
smooth family `Q : ℝ → F →L[ℝ] F` of self-adjoint projections with
`LinearMap.range (Q t) = LinearMap.range (Ψ t)`.  The construction is the Moore–Penrose formula

  `Q t = Ψ t ∘ ((Ψ t)^* ∘ Ψ t)⁻¹ ∘ (Ψ t)^*`,

whose ingredients are all smooth in `t`: the adjoint (a `≃ₗᵢ⋆`), the positive definite operator
`(Ψ t)^* ∘ Ψ t` (invertible because `⟨Ψ^*Ψ v, v⟩ = ‖Ψ v‖²` and `Ψ` is injective), and the inverse of a
smooth family of invertible operators (`ContinuousLinearMap.IsInvertible.contDiffAt_map_inverse`).
No genericity, no Baire, no bundle theory enters.
-/

open scoped ContDiff
open Filter Topology

namespace Work.Whitney.CutPush

/-- **The orthogonal projection onto the image of a smooth family of injections.** -/
theorem exists_smooth_projection_range_family {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] [FiniteDimensional ℝ F]
    (Ψ : ℝ → E →L[ℝ] F) (hΨ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ)
    (hinj : ∀ t : ℝ, Function.Injective (Ψ t)) :
    ∃ Q : ℝ → F →L[ℝ] F,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × F => Q p.1 p.2) ∧
      (∀ t : ℝ, LinearMap.range (Q t : F →ₗ[ℝ] F) = LinearMap.range (Ψ t : E →ₗ[ℝ] F)) ∧
      (∀ t : ℝ, ∀ x y : F, inner ℝ (Q t x) y = inner ℝ x (Q t y)) := by
  classical
  -- ## the smooth family of adjoints
  have hadj : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t : ℝ => ContinuousLinearMap.adjoint (Ψ t)) :=
    (((ContinuousLinearMap.adjoint :
        (E →L[ℝ] F) ≃ₗᵢ⋆[ℝ] (F →L[ℝ] E)).toLinearIsometry).toContinuousLinearMap).contDiff.comp hΨ
  -- ## the smooth family of positive definite operators `(Ψ t)^* ∘ Ψ t`
  set S : ℝ → E →L[ℝ] E := fun t => (ContinuousLinearMap.adjoint (Ψ t)).comp (Ψ t) with hSdef
  have hS : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) S := by
    have h := hadj.clm_comp hΨ
    simpa [hSdef, ContinuousLinearMap.comp_apply] using h
  have hS_apply : ∀ (t : ℝ) (v : E),
      S t v = (ContinuousLinearMap.adjoint (Ψ t)) (Ψ t v) := by
    intro t v
    rw [hSdef]
    rfl
  -- ## each `S t` is injective, hence invertible
  have hinjS : ∀ t : ℝ, Function.Injective (S t) := by
    intro t x y hxy
    have hkey : ∀ z : E, inner ℝ (S t z) z = ‖Ψ t z‖ ^ 2 := by
      intro z
      rw [hS_apply t z, ContinuousLinearMap.adjoint_inner_left (Ψ t) z (Ψ t z),
        real_inner_self_eq_norm_sq]
    have hzero : S t (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    have h2 : ‖Ψ t (x - y)‖ ^ 2 = 0 := by
      rw [← hkey (x - y), hzero]
      simp
    have h4 : ‖Ψ t (x - y)‖ = 0 := by
      nlinarith [norm_nonneg (Ψ t (x - y))]
    have h3 : Ψ t (x - y) = 0 := norm_eq_zero.mp h4
    exact sub_eq_zero.mp (hinj t (by rw [h3, map_zero]))
  have hinv : ∀ t : ℝ, (S t).IsInvertible := by
    intro t
    have hbij : Function.Bijective (S t) :=
      ⟨hinjS t, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (rfl : Module.finrank ℝ E = Module.finrank ℝ E)).mp (hinjS t)⟩
    refine ⟨(LinearEquiv.ofBijective (S t : E →ₗ[ℝ] E) hbij).toContinuousLinearEquiv, ?_⟩
    ext x
    rfl
  have hSinv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t : ℝ => ContinuousLinearMap.inverse (S t)) := by
    rw [contDiff_iff_contDiffAt]
    intro t
    exact (hinv t).contDiffAt_map_inverse.comp t hS.contDiffAt
  have hSinv_apply : ∀ (t : ℝ) (v : E), S t ((ContinuousLinearMap.inverse (S t)) v) = v := by
    intro t v
    exact (((hinv t).inverse_apply_eq (x := (S t).inverse v) (y := v)).mp rfl).symm
  -- ## the smooth family of projections
  set Q : ℝ → F →L[ℝ] F := fun t =>
    (Ψ t).comp (((S t).inverse).comp (ContinuousLinearMap.adjoint (Ψ t))) with hQdef
  have hQ_apply : ∀ (t : ℝ) (x : F), Q t x =
      Ψ t ((S t).inverse ((ContinuousLinearMap.adjoint (Ψ t)) x)) := by
    intro t x
    rw [hQdef]
    simp only [ContinuousLinearMap.comp_apply]
  have hQsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Q := by
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun t : ℝ =>
          (Ψ t).comp (((S t).inverse).comp (ContinuousLinearMap.adjoint (Ψ t)))) :=
      hΨ.clm_comp (hSinv.clm_comp hadj)
    simpa [hQdef] using h1
  -- ## the range is the image of `Ψ`
  have hrange : ∀ t : ℝ, LinearMap.range (Q t : F →ₗ[ℝ] F) = LinearMap.range (Ψ t : E →ₗ[ℝ] F) := by
    intro t
    apply le_antisymm
    · rintro y ⟨x, rfl⟩
      refine ⟨(S t).inverse ((ContinuousLinearMap.adjoint (Ψ t)) x), ?_⟩
      show (Ψ t) ((S t).inverse ((ContinuousLinearMap.adjoint (Ψ t)) x)) = (Q t) x
      rw [hQ_apply t x]
    · rintro y ⟨x, rfl⟩
      refine ⟨Ψ t x, ?_⟩
      show (Q t) (Ψ t x) = (Ψ t) x
      rw [hQ_apply t (Ψ t x)]
      have h1 : (S t).inverse ((ContinuousLinearMap.adjoint (Ψ t)) (Ψ t x)) = x := by
        rw [← hS_apply t x]
        exact hinjS t (hSinv_apply t (S t x))
      rw [h1]
  -- ## the inverse family is self-adjoint
  have hMinner : ∀ (t : ℝ) (u v : E),
      inner ℝ ((S t).inverse u) v = inner ℝ u ((S t).inverse v) := by
    intro t u v
    have hv : v = (S t) ((S t).inverse v) := (hSinv_apply t v).symm
    have hu : u = (S t) ((S t).inverse u) := (hSinv_apply t u).symm
    have h1 : inner ℝ ((S t).inverse u) v
        = inner ℝ (Ψ t ((S t).inverse u)) (Ψ t ((S t).inverse v)) := by
      calc inner ℝ ((S t).inverse u) v
          = inner ℝ ((S t).inverse u) ((S t) ((S t).inverse v)) := by conv_lhs => rw [hv]
        _ = inner ℝ ((S t).inverse u)
              ((ContinuousLinearMap.adjoint (Ψ t)) (Ψ t ((S t).inverse v))) := by
              rw [hS_apply t ((S t).inverse v)]
        _ = inner ℝ (Ψ t ((S t).inverse u)) (Ψ t ((S t).inverse v)) := by
              rw [ContinuousLinearMap.adjoint_inner_right (Ψ t) ((S t).inverse u)
                (Ψ t ((S t).inverse v))]
    have h2 : inner ℝ u ((S t).inverse v)
        = inner ℝ (Ψ t ((S t).inverse u)) (Ψ t ((S t).inverse v)) := by
      calc inner ℝ u ((S t).inverse v)
          = inner ℝ ((S t) ((S t).inverse u)) ((S t).inverse v) := by conv_lhs => rw [hu]
        _ = inner ℝ ((ContinuousLinearMap.adjoint (Ψ t)) (Ψ t ((S t).inverse u)))
              ((S t).inverse v) := by rw [hS_apply t ((S t).inverse u)]
        _ = inner ℝ (Ψ t ((S t).inverse u)) (Ψ t ((S t).inverse v)) := by
              rw [ContinuousLinearMap.adjoint_inner_left (Ψ t) ((S t).inverse v)
                (Ψ t ((S t).inverse u))]
    rw [h1, h2]
  -- ## self-adjointness of `Q`
  have hQadj : ∀ (t : ℝ) (x y : F), inner ℝ (Q t x) y = inner ℝ x (Q t y) := by
    intro t x y
    have h1 : inner ℝ (Q t x) y
        = inner ℝ ((S t).inverse ((ContinuousLinearMap.adjoint (Ψ t)) x))
            ((ContinuousLinearMap.adjoint (Ψ t)) y) := by
      rw [hQ_apply t x, ← ContinuousLinearMap.adjoint_inner_right (Ψ t)
        ((S t).inverse ((ContinuousLinearMap.adjoint (Ψ t)) x)) y]
    have h2 : inner ℝ ((S t).inverse ((ContinuousLinearMap.adjoint (Ψ t)) x))
            ((ContinuousLinearMap.adjoint (Ψ t)) y) = inner ℝ x (Q t y) := by
      rw [hQ_apply t y,
        ← real_inner_comm x (Ψ t ((S t).inverse ((ContinuousLinearMap.adjoint (Ψ t)) y))),
        ← ContinuousLinearMap.adjoint_inner_right (Ψ t)
          ((S t).inverse ((ContinuousLinearMap.adjoint (Ψ t)) y)) x]
      exact (hMinner t ((ContinuousLinearMap.adjoint (Ψ t)) x)
          ((ContinuousLinearMap.adjoint (Ψ t)) y)).trans
        (real_inner_comm ((S t).inverse ((ContinuousLinearMap.adjoint (Ψ t)) y))
          ((ContinuousLinearMap.adjoint (Ψ t)) x))
    rw [h1, h2]
  refine ⟨Q, ?_, hrange, hQadj⟩
  exact (hQsm.comp contDiff_fst).clm_apply contDiff_snd

end Work.Whitney.CutPush
