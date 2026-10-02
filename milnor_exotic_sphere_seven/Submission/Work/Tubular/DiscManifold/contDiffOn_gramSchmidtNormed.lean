import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Tubular.DiscManifold

/-- The normalized Gram-Schmidt process applied to a family of vectors depending
`C¹`-ly (in the real sense) on a parameter is again `C¹`, on the region where the
family is linearly independent.

This is used to build smooth (local) orthonormal frames out of a smoothly varying
linearly independent family of sections. -/
theorem contDiffOn_gramSchmidtNormed {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedSpace ℝ E] {ι : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι] [WellFoundedLT ι] {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {s : Set X} {f : X → ι → E} (hf : ∀ i, ContDiffOn ℝ 1 (fun x => f x i) s) (hlin : ∀ x ∈ s, LinearIndependent 𝕜 (f x)) (n : ι) : ContDiffOn ℝ 1 (fun x => InnerProductSpace.gramSchmidtNormed 𝕜 (f x) n) s := by
  -- The Gram-Schmidt vectors are `C¹` and non-zero on `s`; we prove both by
  -- well-founded induction on the index.
  have key : ∀ m : ι,
      ContDiffOn ℝ 1 (fun x => InnerProductSpace.gramSchmidt 𝕜 (f x) m) s ∧
        (∀ x ∈ s, InnerProductSpace.gramSchmidt 𝕜 (f x) m ≠ 0) := by
    intro n0
    refine wellFounded_lt.induction
      (C := fun m => ContDiffOn ℝ 1 (fun x => InnerProductSpace.gramSchmidt 𝕜 (f x) m) s ∧
        (∀ x ∈ s, InnerProductSpace.gramSchmidt 𝕜 (f x) m ≠ 0)) n0 fun m ih => ?_
    have hgs : ∀ i, i < m →
        ContDiffOn ℝ 1 (fun x => InnerProductSpace.gramSchmidt 𝕜 (f x) i) s :=
      fun i hi => (ih i hi).1
    have hgn : ∀ i, i < m → ∀ x ∈ s, InnerProductSpace.gramSchmidt 𝕜 (f x) i ≠ 0 :=
      fun i hi => (ih i hi).2
    refine ⟨?_, fun x hx => InnerProductSpace.gramSchmidt_ne_zero m (hlin x hx)⟩
    -- Unfold the recursion, writing the orthogonal projection onto `𝕜 ∙ gᵢ` explicitly.
    have hsum : ContDiffOn ℝ 1 (fun x => ∑ i ∈ Finset.Iio m,
        (inner 𝕜 (InnerProductSpace.gramSchmidt 𝕜 (f x) i) (f x m) *
          (inner 𝕜 (InnerProductSpace.gramSchmidt 𝕜 (f x) i)
            (InnerProductSpace.gramSchmidt 𝕜 (f x) i))⁻¹)
          • InnerProductSpace.gramSchmidt 𝕜 (f x) i) s := by
      refine ContDiffOn.sum fun i hi => ?_
      have hi' : i < m := Finset.mem_Iio.mp hi
      have hgi : ContDiffOn ℝ 1 (fun x => InnerProductSpace.gramSchmidt 𝕜 (f x) i) s :=
        hgs i hi'
      have hnum : ContDiffOn ℝ 1
          (fun x => inner 𝕜 (InnerProductSpace.gramSchmidt 𝕜 (f x) i) (f x m)) s :=
        hgi.inner 𝕜 (hf m)
      have hden : ContDiffOn ℝ 1
          (fun x => inner 𝕜 (InnerProductSpace.gramSchmidt 𝕜 (f x) i)
            (InnerProductSpace.gramSchmidt 𝕜 (f x) i)) s :=
        hgi.inner 𝕜 hgi
      have hden_ne : ∀ x ∈ s, inner 𝕜 (InnerProductSpace.gramSchmidt 𝕜 (f x) i)
          (InnerProductSpace.gramSchmidt 𝕜 (f x) i) ≠ 0 :=
        fun x hx => inner_self_ne_zero.mpr (hgn i hi' x hx)
      have hquot : ContDiffOn ℝ 1 (fun x => inner 𝕜 (InnerProductSpace.gramSchmidt 𝕜 (f x) i)
          (f x m) * (inner 𝕜 (InnerProductSpace.gramSchmidt 𝕜 (f x) i)
            (InnerProductSpace.gramSchmidt 𝕜 (f x) i))⁻¹) s :=
        ContDiffOn.mul hnum (ContDiffOn.inv hden hden_ne)
      exact ContDiffOn.smul hquot hgi
    have hfun : (fun x => InnerProductSpace.gramSchmidt 𝕜 (f x) m) = fun x => f x m -
        ∑ i ∈ Finset.Iio m,
        (inner 𝕜 (InnerProductSpace.gramSchmidt 𝕜 (f x) i) (f x m) *
          (inner 𝕜 (InnerProductSpace.gramSchmidt 𝕜 (f x) i)
            (InnerProductSpace.gramSchmidt 𝕜 (f x) i))⁻¹)
          • InnerProductSpace.gramSchmidt 𝕜 (f x) i := by
      funext x
      conv_lhs => rw [InnerProductSpace.gramSchmidt_def]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [Submodule.starProjection_singleton]
      congr 1
      rw [div_eq_mul_inv]
      congr 1
      rw [inner_self_eq_norm_sq_to_K, RCLike.ofReal_pow]
    rw [hfun]
    exact (hf m).sub hsum
  have h := (key n).1
  have hne := (key n).2
  -- `gramSchmidtNormed` is `gramSchmidt` scaled by the inverse of its norm.
  have hfun : (fun x => InnerProductSpace.gramSchmidtNormed 𝕜 (f x) n) = fun x =>
      (↑‖InnerProductSpace.gramSchmidt 𝕜 (f x) n‖ : 𝕜)⁻¹ •
        InnerProductSpace.gramSchmidt 𝕜 (f x) n := by
    funext x
    rw [InnerProductSpace.gramSchmidtNormed]
  rw [hfun]
  have hnormR : ContDiffOn ℝ 1 (fun x => ‖InnerProductSpace.gramSchmidt 𝕜 (f x) n‖) s :=
    h.norm 𝕜 hne
  have hnormK : ContDiffOn ℝ 1 (fun x => (‖InnerProductSpace.gramSchmidt 𝕜 (f x) n‖ : 𝕜)) s :=
    (RCLike.ofRealCLM (K := 𝕜)).contDiff.comp_contDiffOn hnormR
  have hinv : ContDiffOn ℝ 1
      (fun x => (↑‖InnerProductSpace.gramSchmidt 𝕜 (f x) n‖ : 𝕜)⁻¹) s :=
    hnormK.inv fun x hx => by
      rw [RCLike.ofReal_ne_zero]
      exact norm_ne_zero_iff.mpr (hne x hx)
  exact ContDiffOn.smul hinv h

end Work.Tubular.DiscManifold
