import Mathlib
import Submission.Work.Drive.Whitney.diskFrame
import Submission.Work.Whitney.CutPush.smooth_range_projection_family

/-!
# A smooth two-parameter family of orthogonal projections onto the complement of a
smooth family of independent `k`-frames

Target (`Work.Drive.Whitney.smooth_kernelProjection_twoParam`): given a `C^∞` family
`b : ℝ × ℝ → Fin k → EuclideanSpace ℝ (Fin m)` whose values are linearly independent at every
point, there is a `C^∞` family `P` of *orthogonal projections* of `EuclideanSpace ℝ (Fin m)` with

* `P x * P x = P x` (idempotent),
* `inner ℝ (P x y) z = inner ℝ y (P x z)` (self-adjoint),
* `finrank (range (P x)) = m - k`,
* `range (P x) = (span ℝ (Set.range (b x)))ᗮ`,

i.e. `P x` is the orthogonal projection onto the orthogonal complement of the `k`-plane spanned by
`b x`, smoothly in the two parameters `x : ℝ × ℝ`.

## The construction

* `spanFam b x : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m)` is the linear map
  `c ↦ ∑ i, c i • b x i`; it is `C^∞` jointly in `(x, c)` (`spanFam_contDiff`) and injective at
  every `x` because `b x` is linearly independent (`spanFam_injective`).
* `exists_smooth_projection_range_family_param` is the Moore–Penrose brick of
  `Work.Whitney.CutPush.exists_smooth_projection_range_family`
  (`Submission/Work/Whitney/CutPush/smooth_range_projection_family.lean`), generalised from the
  one-parameter domain `ℝ` to an arbitrary real normed parameter space `Z` — needed here because the
  parameter is two-dimensional.  It produces a `C^∞` family `Q` of orthogonal projections onto the
  ranges of `spanFam b` (which are exactly the spans of the `b x`).
* `P x := 1 - Q x` is the orthogonal projection onto the orthogonal complement; the complement
  lemmas `range_one_sub_eq_orthogonal` and `finrank_range_one_sub` are elementary and proved here.
-/

open scoped ContDiff
open Filter Topology

namespace Work.Drive.Whitney

/-! ## 1. The Moore–Penrose range projection over a general normed parameter space -/

/-- **The orthogonal projection onto the image of a smooth family of injections**, for a family
parametrised by an arbitrary real normed space `Z`.  This is
`Work.Whitney.CutPush.exists_smooth_projection_range_family` with the parameter space generalised
from `ℝ` to `Z` (the proof is verbatim the same, the Moore–Penrose formula

  `Q z = Ψ z ∘ ((Ψ z)^* ∘ Ψ z)⁻¹ ∘ (Ψ z)^*`

being built from the smooth family of adjoints, the pointwise-invertible family
`(Ψ z)^* ∘ Ψ z` and Mathlib's smoothness of the inverse of an invertible operator). -/
theorem exists_smooth_projection_range_family_param {Z : Type*} [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] [FiniteDimensional ℝ F]
    (Ψ : Z → E →L[ℝ] F) (hΨ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ)
    (hinj : ∀ z : Z, Function.Injective (Ψ z)) :
    ∃ Q : Z → F →L[ℝ] F,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : Z × F => Q p.1 p.2) ∧
      (∀ z : Z, LinearMap.range (Q z : F →ₗ[ℝ] F) = LinearMap.range (Ψ z : E →ₗ[ℝ] F)) ∧
      (∀ (z : Z) (x y : F), inner ℝ (Q z x) y = inner ℝ x (Q z y)) ∧
      (∀ z : Z, Q z * Q z = Q z) := by
  classical
  -- ## the smooth family of adjoints
  have hadj : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : Z => ContinuousLinearMap.adjoint (Ψ z)) :=
    (((ContinuousLinearMap.adjoint :
        (E →L[ℝ] F) ≃ₗᵢ⋆[ℝ] (F →L[ℝ] E)).toLinearIsometry).toContinuousLinearMap).contDiff.comp hΨ
  -- ## the smooth family of positive definite operators `(Ψ z)^* ∘ Ψ z`
  set S : Z → E →L[ℝ] E := fun z => (ContinuousLinearMap.adjoint (Ψ z)).comp (Ψ z) with hSdef
  have hS : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) S := by
    have h := hadj.clm_comp hΨ
    simpa [hSdef, ContinuousLinearMap.comp_apply] using h
  have hS_apply : ∀ (z : Z) (v : E),
      S z v = (ContinuousLinearMap.adjoint (Ψ z)) (Ψ z v) := by
    intro z v
    rw [hSdef]
    rfl
  -- ## each `S z` is injective, hence invertible
  have hinjS : ∀ z : Z, Function.Injective (S z) := by
    intro z x y hxy
    have hkey : ∀ u : E, inner ℝ (S z u) u = ‖Ψ z u‖ ^ 2 := by
      intro u
      rw [hS_apply z u, ContinuousLinearMap.adjoint_inner_left (Ψ z) u (Ψ z u),
        real_inner_self_eq_norm_sq]
    have hzero : S z (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    have h2 : ‖Ψ z (x - y)‖ ^ 2 = 0 := by
      rw [← hkey (x - y), hzero]
      simp
    have h4 : ‖Ψ z (x - y)‖ = 0 := by
      nlinarith [norm_nonneg (Ψ z (x - y))]
    have h3 : Ψ z (x - y) = 0 := norm_eq_zero.mp h4
    exact sub_eq_zero.mp (hinj z (by rw [h3, map_zero]))
  have hinv : ∀ z : Z, (S z).IsInvertible := by
    intro z
    have hbij : Function.Bijective (S z) :=
      ⟨hinjS z, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (rfl : Module.finrank ℝ E = Module.finrank ℝ E)).mp (hinjS z)⟩
    refine ⟨(LinearEquiv.ofBijective (S z : E →ₗ[ℝ] E) hbij).toContinuousLinearEquiv, ?_⟩
    ext x
    rfl
  have hSinv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : Z => ContinuousLinearMap.inverse (S z)) := by
    rw [contDiff_iff_contDiffAt]
    intro z
    exact (hinv z).contDiffAt_map_inverse.comp z hS.contDiffAt
  have hSinv_apply : ∀ (z : Z) (v : E), S z ((S z).inverse v) = v := by
    intro z v
    exact (((hinv z).inverse_apply_eq (x := (S z).inverse v) (y := v)).mp rfl).symm
  -- ## the smooth family of projections
  set Q : Z → F →L[ℝ] F := fun z =>
    (Ψ z).comp (((S z).inverse).comp (ContinuousLinearMap.adjoint (Ψ z))) with hQdef
  have hQ_apply : ∀ (z : Z) (x : F), Q z x =
      Ψ z ((S z).inverse ((ContinuousLinearMap.adjoint (Ψ z)) x)) := by
    intro z x
    rw [hQdef]
    simp only [ContinuousLinearMap.comp_apply]
  have hQsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Q := by
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z : Z =>
          (Ψ z).comp (((S z).inverse).comp (ContinuousLinearMap.adjoint (Ψ z)))) :=
      hΨ.clm_comp (hSinv.clm_comp hadj)
    simpa [hQdef] using h1
  -- ## the range is the image of `Ψ`
  have hrange : ∀ z : Z, LinearMap.range (Q z : F →ₗ[ℝ] F) = LinearMap.range (Ψ z : E →ₗ[ℝ] F) := by
    intro z
    apply le_antisymm
    · rintro y ⟨x, rfl⟩
      refine ⟨(S z).inverse ((ContinuousLinearMap.adjoint (Ψ z)) x), ?_⟩
      show (Ψ z) ((S z).inverse ((ContinuousLinearMap.adjoint (Ψ z)) x)) = (Q z) x
      rw [hQ_apply z x]
    · rintro y ⟨x, rfl⟩
      refine ⟨Ψ z x, ?_⟩
      show (Q z) (Ψ z x) = (Ψ z) x
      rw [hQ_apply z (Ψ z x)]
      have h1 : (S z).inverse ((ContinuousLinearMap.adjoint (Ψ z)) (Ψ z x)) = x := by
        rw [← hS_apply z x]
        exact hinjS z (hSinv_apply z (S z x))
      rw [h1]
  -- ## the inverse family is self-adjoint
  have hMinner : ∀ (z : Z) (u v : E),
      inner ℝ ((S z).inverse u) v = inner ℝ u ((S z).inverse v) := by
    intro z u v
    have hv : v = (S z) ((S z).inverse v) := (hSinv_apply z v).symm
    have hu : u = (S z) ((S z).inverse u) := (hSinv_apply z u).symm
    have h1 : inner ℝ ((S z).inverse u) v
        = inner ℝ (Ψ z ((S z).inverse u)) (Ψ z ((S z).inverse v)) := by
      calc inner ℝ ((S z).inverse u) v
          = inner ℝ ((S z).inverse u) ((S z) ((S z).inverse v)) := by conv_lhs => rw [hv]
        _ = inner ℝ ((S z).inverse u)
              ((ContinuousLinearMap.adjoint (Ψ z)) (Ψ z ((S z).inverse v))) := by
              rw [hS_apply z ((S z).inverse v)]
        _ = inner ℝ (Ψ z ((S z).inverse u)) (Ψ z ((S z).inverse v)) := by
              rw [ContinuousLinearMap.adjoint_inner_right (Ψ z) ((S z).inverse u)
                (Ψ z ((S z).inverse v))]
    have h2 : inner ℝ u ((S z).inverse v)
        = inner ℝ (Ψ z ((S z).inverse u)) (Ψ z ((S z).inverse v)) := by
      calc inner ℝ u ((S z).inverse v)
          = inner ℝ ((S z) ((S z).inverse u)) ((S z).inverse v) := by conv_lhs => rw [hu]
        _ = inner ℝ ((ContinuousLinearMap.adjoint (Ψ z)) (Ψ z ((S z).inverse u)))
              ((S z).inverse v) := by rw [hS_apply z ((S z).inverse u)]
        _ = inner ℝ (Ψ z ((S z).inverse u)) (Ψ z ((S z).inverse v)) := by
              rw [ContinuousLinearMap.adjoint_inner_left (Ψ z) ((S z).inverse v)
                (Ψ z ((S z).inverse u))]
    rw [h1, h2]
  -- ## self-adjointness of `Q`
  have hQadj : ∀ (z : Z) (x y : F), inner ℝ (Q z x) y = inner ℝ x (Q z y) := by
    intro z x y
    have h1 : inner ℝ (Q z x) y
        = inner ℝ ((S z).inverse ((ContinuousLinearMap.adjoint (Ψ z)) x))
            ((ContinuousLinearMap.adjoint (Ψ z)) y) := by
      rw [hQ_apply z x, ← ContinuousLinearMap.adjoint_inner_right (Ψ z)
        ((S z).inverse ((ContinuousLinearMap.adjoint (Ψ z)) x)) y]
    have h2 : inner ℝ ((S z).inverse ((ContinuousLinearMap.adjoint (Ψ z)) x))
            ((ContinuousLinearMap.adjoint (Ψ z)) y) = inner ℝ x (Q z y) := by
      rw [hQ_apply z y,
        ← real_inner_comm x (Ψ z ((S z).inverse ((ContinuousLinearMap.adjoint (Ψ z)) y))),
        ← ContinuousLinearMap.adjoint_inner_right (Ψ z)
          ((S z).inverse ((ContinuousLinearMap.adjoint (Ψ z)) y)) x]
      exact (hMinner z ((ContinuousLinearMap.adjoint (Ψ z)) x)
          ((ContinuousLinearMap.adjoint (Ψ z)) y)).trans
        (real_inner_comm ((S z).inverse ((ContinuousLinearMap.adjoint (Ψ z)) y))
          ((ContinuousLinearMap.adjoint (Ψ z)) x))
    rw [h1, h2]
  -- ## idempotence of `Q`
  have hidem : ∀ z : Z, Q z * Q z = Q z := by
    intro z
    refine ContinuousLinearMap.ext fun x => ?_
    show Q z (Q z x) = Q z x
    rw [hQ_apply z (Q z x), hQ_apply z x,
      ← hS_apply z ((S z).inverse ((ContinuousLinearMap.adjoint (Ψ z)) x)),
      hSinv_apply z]
  refine ⟨Q, ?_, hrange, hQadj, hidem⟩
  exact (hQsm.comp contDiff_fst).clm_apply contDiff_snd

/-! ## 2. The span family of a family of frames -/

/-- The linear map `c ↦ ∑ i, c i • b x i`, as a continuous linear map on the Euclidean space
`EuclideanSpace ℝ (Fin k)` of coefficients. -/
noncomputable def spanFam {m k : ℕ} (b : ℝ × ℝ → Fin k → EuclideanSpace ℝ (Fin m)) :
    ℝ × ℝ → (EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m)) :=
  fun x => ∑ i : Fin k, (EuclideanSpace.proj (𝕜 := ℝ) i).smulRight (b x i)

theorem spanFam_apply {m k : ℕ} (b : ℝ × ℝ → Fin k → EuclideanSpace ℝ (Fin m)) (x : ℝ × ℝ)
    (c : EuclideanSpace ℝ (Fin k)) : spanFam b x c = ∑ i, c i • b x i := by
  simp [spanFam, ContinuousLinearMap.smulRight_apply]

theorem spanFam_contDiff {m k : ℕ} (b : ℝ × ℝ → Fin k → EuclideanSpace ℝ (Fin m))
    (hb : ∀ i : Fin k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × ℝ => b x i)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (spanFam b) := by
  have h : ∀ i : Fin k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ × ℝ => (EuclideanSpace.proj (𝕜 := ℝ) i).smulRight (b x i)) := by
    intro i
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (((ContinuousLinearMap.smulRightL ℝ (EuclideanSpace ℝ (Fin k))
            (EuclideanSpace ℝ (Fin m))) (EuclideanSpace.proj (𝕜 := ℝ) i)) :
          EuclideanSpace ℝ (Fin m) →L[ℝ]
            (EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m))) :=
      ContinuousLinearMap.contDiff _
    exact h1.comp (hb i)
  have hsum := ContDiff.sum (s := Finset.univ) (fun i _ => h i)
  show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ × ℝ => ∑ i ∈ (Finset.univ : Finset (Fin k)),
        (EuclideanSpace.proj (𝕜 := ℝ) i).smulRight (b x i))
  exact hsum

theorem spanFam_injective {m k : ℕ} (b : ℝ × ℝ → Fin k → EuclideanSpace ℝ (Fin m))
    (x : ℝ × ℝ) (hind : LinearIndependent ℝ (b x)) : Function.Injective (spanFam b x) := by
  intro c c' hcc
  have hsub : spanFam b x (c - c') = 0 := by
    rw [map_sub, hcc, sub_self]
  have h2 : (∑ i, (c - c') i • b x i) = 0 := by
    rw [← spanFam_apply, hsub]
  have h3 : ∀ i, (c - c') i = 0 :=
    (Fintype.linearIndependent_iff.mp hind) (fun i => (c - c') i) h2
  ext i
  have h4 : (c - c') i = c i - c' i := by simp
  have h5 := h3 i
  rw [h4] at h5
  exact sub_eq_zero.mp h5

theorem spanFam_range {m k : ℕ} (b : ℝ × ℝ → Fin k → EuclideanSpace ℝ (Fin m)) (x : ℝ × ℝ) :
    LinearMap.range (spanFam b x : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))
      = Submodule.span ℝ (Set.range (b x)) := by
  refine le_antisymm ?_ ?_
  · rintro y ⟨c, rfl⟩
    change spanFam b x c ∈ Submodule.span ℝ (Set.range (b x))
    rw [spanFam_apply]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · refine Submodule.span_le.mpr ?_
    rintro y ⟨i, rfl⟩
    refine ⟨EuclideanSpace.single i 1, ?_⟩
    change spanFam b x (EuclideanSpace.single i 1) = b x i
    rw [spanFam_apply]
    simp [EuclideanSpace.single]

/-! ## 3. The orthogonal complement of the range of a self-adjoint idempotent -/

/-- **The range of `1 - Q` is the orthogonal complement of the range of `Q`**, for a self-adjoint
idempotent `Q` of a real inner product space. -/
theorem range_one_sub_eq_orthogonal {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (Q : F →L[ℝ] F) (hidem : Q * Q = Q)
    (hadj : ∀ x y : F, inner ℝ (Q x) y = inner ℝ x (Q y)) :
    LinearMap.range ((1 - Q : F →L[ℝ] F) : F →ₗ[ℝ] F) = (LinearMap.range (Q : F →ₗ[ℝ] F))ᗮ := by
  have hQQ : ∀ w : F, Q (Q w) = Q w := by
    intro w
    have h := congrArg (fun f : F →L[ℝ] F => f w) hidem
    rwa [mul_apply_eq_comp] at h
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    rw [Submodule.mem_orthogonal']
    intro u hu
    obtain ⟨w, rfl⟩ := hu
    change inner ℝ ((1 - Q) x) (Q w) = 0
    rw [sub_apply, one_apply_eq_self, inner_sub_left, hadj x (Q w), hQQ w,
      sub_self]
  · intro y hy
    have hQy : Q y = 0 := by
      rw [Submodule.mem_orthogonal'] at hy
      have h1 : inner ℝ y (Q y) = 0 := hy (Q y) ⟨y, rfl⟩
      have h2 : inner ℝ (Q y) (Q y) = inner ℝ y (Q y) := by rw [hadj y (Q y), hQQ y]
      have h3 : inner ℝ (Q y) (Q y) = 0 := by rw [h2, h1]
      have h4 : ‖Q y‖ ^ 2 = 0 := by rw [← real_inner_self_eq_norm_sq]; exact h3
      exact norm_eq_zero.mp (by nlinarith [norm_nonneg (Q y)])
    refine ⟨y, ?_⟩
    change (1 - Q) y = y
    rw [sub_apply, one_apply_eq_self, hQy, sub_zero]

/-- **The rank of `1 - Q`** is `finrank F - finrank (range Q)` for a self-adjoint idempotent `Q`. -/
theorem finrank_range_one_sub {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F]
    (Q : F →L[ℝ] F) (hidem : Q * Q = Q)
    (hadj : ∀ x y : F, inner ℝ (Q x) y = inner ℝ x (Q y)) :
    Module.finrank ℝ (LinearMap.range ((1 - Q : F →L[ℝ] F) : F →ₗ[ℝ] F))
      = Module.finrank ℝ F - Module.finrank ℝ (LinearMap.range (Q : F →ₗ[ℝ] F)) := by
  rw [range_one_sub_eq_orthogonal Q hidem hadj]
  have h := Submodule.finrank_add_finrank_orthogonal (LinearMap.range (Q : F →ₗ[ℝ] F))
  omega

/-! ## 4. The target -/

theorem smooth_kernelProjection_twoParam {m k : ℕ}
    (b : ℝ × ℝ → Fin k → EuclideanSpace ℝ (Fin m))
    (hb : ∀ i : Fin k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × ℝ => b x i))
    (hind : ∀ x : ℝ × ℝ, LinearIndependent ℝ (b x)) :
    ∃ P : ℝ × ℝ → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : (ℝ × ℝ) × EuclideanSpace ℝ (Fin m) => P p.1 p.2) ∧
      (∀ x : ℝ × ℝ, P x * P x = P x) ∧
      (∀ (x : ℝ × ℝ) (y z : EuclideanSpace ℝ (Fin m)), inner ℝ (P x y) z = inner ℝ y (P x z)) ∧
      (∀ x : ℝ × ℝ, Module.finrank ℝ (LinearMap.range
        (P x : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))) = m - k) ∧
      (∀ x : ℝ × ℝ, LinearMap.range (P x : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))
        = (Submodule.span ℝ (Set.range (b x)))ᗮ) := by
  classical
  -- The range projection onto the spans of the `b x`.
  obtain ⟨Q, hQsm, hQrange, hQadj, hQidem⟩ :=
    exists_smooth_projection_range_family_param (Z := ℝ × ℝ)
      (E := EuclideanSpace ℝ (Fin k)) (F := EuclideanSpace ℝ (Fin m))
      (spanFam b) (spanFam_contDiff b hb) (fun x => spanFam_injective b x (hind x))
  -- The complement is smooth.
  have hPsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : (ℝ × ℝ) × EuclideanSpace ℝ (Fin m) => (1 - Q p.1) p.2) := by
    have hfam : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : ℝ × ℝ =>
          (1 - Q x : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))) := by
      rw [contDiff_clm_apply_iff]
      intro y
      have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun x : ℝ × ℝ => ((x, y) : (ℝ × ℝ) × EuclideanSpace ℝ (Fin m))) :=
        contDiff_id.prodMk contDiff_const
      have h3 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × ℝ => Q x y) := hQsm.comp h2
      have h4 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun x : ℝ × ℝ => y - Q x y) := contDiff_const.sub h3
      simpa using h4
    exact (hfam.comp contDiff_fst).clm_apply contDiff_snd
  refine ⟨fun x => 1 - Q x, hPsm, ?_, ?_, ?_, ?_⟩
  · intro x
    rw [sub_mul, one_mul, mul_sub, mul_one, hQidem x]
    abel
  · intro x y z
    rw [sub_apply, one_apply_eq_self, sub_apply,
      one_apply_eq_self, inner_sub_left, inner_sub_right, hQadj x y z]
  · intro x
    rw [finrank_range_one_sub (Q x) (hQidem x) (hQadj x), hQrange x, spanFam_range b x,
      finrank_span_eq_card (hind x), Fintype.card_fin, finrank_euclideanSpace, Fintype.card_fin]
  · intro x
    rw [range_one_sub_eq_orthogonal (Q x) (hQidem x) (hQadj x), hQrange x, spanFam_range b x]

end Work.Drive.Whitney
