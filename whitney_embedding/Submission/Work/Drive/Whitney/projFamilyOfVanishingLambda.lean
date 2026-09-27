import Mathlib

/-!
# The range projections of a family that degenerates on the zero set of `lam`

`Work.Drive.Whitney.projFamilyOfVanishingLambda`: for a `C^∞` family
`Ψ : ℝ × ℝ → (ℝ^r →L[ℝ] ℝ^m)` whose members are *injective wherever* a nonnegative `C^∞` function
`lam` vanishes, there is a `C^∞` family `P` of *orthogonal projections* on `ℝ^m` with
`P p * P p = P p` and `range (P p) = range (Ψ p)` for every `p` with `lam p = 0`.

The construction is the smoothed Moore–Penrose formula

    P p = Ψ p ∘ ((lam p)^2 • Id + (Ψ p)^* ∘ Ψ p)^{-1} ∘ (Ψ p)^*.

The operator `S p := (lam p)^2 • Id + (Ψ p)^* ∘ Ψ p` is positive definite (hence invertible) at
*every* `p`: for `x ≠ 0` either `lam p ≠ 0`, and then `⟪S p x, x⟫ ≥ (lam p)^2 ‖x‖^2 > 0`, or
`lam p = 0`, and then `⟪S p x, x⟫ = ‖Ψ p x‖^2 > 0` by injectivity of `Ψ p`.  Smoothness of
`p ↦ (S p)⁻¹` is the smoothness of inversion of continuous linear maps
(`ContinuousLinearMap.IsInvertible.contDiffAt_map_inverse`), and at a zero of `lam` the formula
collapses to the usual orthogonal projection onto `range (Ψ p)` because
`(Ψ p)^* ∘ Ψ p = S p` there.
-/

namespace Work.Drive.Whitney

theorem projFamilyOfVanishingLambda {m r : ℕ}
    (Ψ : ℝ × ℝ → (EuclideanSpace ℝ (Fin r) →L[ℝ] EuclideanSpace ℝ (Fin m)))
    (hΨ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : (ℝ × ℝ) × EuclideanSpace ℝ (Fin r) => Ψ q.1 q.2))
    (lam : ℝ × ℝ → ℝ) (hlam : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) lam)
    (hlamnn : ∀ p, 0 ≤ lam p) (hlinj : ∀ p, lam p = 0 → Function.Injective (Ψ p)) :
    ∃ P : ℝ × ℝ → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : (ℝ × ℝ) × EuclideanSpace ℝ (Fin m) => P q.1 q.2) ∧
      ∀ p, lam p = 0 → P p * P p = P p ∧
        LinearMap.range (P p : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))
          = LinearMap.range (Ψ p : EuclideanSpace ℝ (Fin r) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) := by
  classical
  -- the family itself, as a `C^∞` curve of operators
  have hΨfam : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => Ψ p) :=
    contDiff_clm_apply_iff.mpr (fun y => hΨ.comp (contDiff_prodMk_left y))
  -- its adjoint is `C^∞`, being the image under the linear isometry `A ↦ A^*`
  have hadj : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => ContinuousLinearMap.adjoint (Ψ p)) :=
    (((ContinuousLinearMap.adjoint :
        (EuclideanSpace ℝ (Fin r) →L[ℝ] EuclideanSpace ℝ (Fin m)) ≃ₗᵢ⋆[ℝ]
          (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin r))).toLinearIsometry).toContinuousLinearMap).contDiff.comp hΨfam
  -- the regularised Gram operator `S p = (lam p)^2 • Id + (Ψ p)^* ∘ Ψ p`
  set S : ℝ × ℝ → (EuclideanSpace ℝ (Fin r) →L[ℝ] EuclideanSpace ℝ (Fin r)) :=
    fun q => (lam q)^2 • (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin r)))
      + (ContinuousLinearMap.adjoint (Ψ q)).comp (Ψ q) with hSdef
  have hS : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) S := by
    have h3 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : ℝ × ℝ => (lam q)^2 • (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin r)))) :=
      (hlam.pow 2).smul contDiff_const
    have h4 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : ℝ × ℝ => (ContinuousLinearMap.adjoint (Ψ q)).comp (Ψ q)) := hadj.clm_comp hΨfam
    simpa [hSdef] using h3.add h4
  have hS_apply : ∀ (q : ℝ × ℝ) (z : EuclideanSpace ℝ (Fin r)),
      S q z = (lam q)^2 • z + (ContinuousLinearMap.adjoint (Ψ q)) (Ψ q z) := by
    intro q z
    rw [hSdef]
    simp [ContinuousLinearMap.comp_apply]
  -- `S p` is positive definite, hence injective
  have hinjS : ∀ p : ℝ × ℝ, Function.Injective (S p) := by
    intro p x y hxy
    have hkey : ∀ z : EuclideanSpace ℝ (Fin r),
        inner ℝ (S p z) z = (lam p)^2 * ‖z‖^2 + ‖Ψ p z‖^2 := by
      intro z
      rw [hS_apply p z, inner_add_left, real_inner_smul_left,
        ContinuousLinearMap.adjoint_inner_left (Ψ p) z (Ψ p z), real_inner_self_eq_norm_sq,
        real_inner_self_eq_norm_sq]
    have hker : S p (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have hsum : (lam p)^2 * ‖x - y‖^2 + ‖Ψ p (x - y)‖^2 = 0 := by
      rw [← hkey (x - y), hker]; simp
    have hA0 : ‖Ψ p (x - y)‖^2 = 0 := by
      nlinarith [mul_nonneg (sq_nonneg (lam p)) (sq_nonneg ‖x - y‖), sq_nonneg ‖Ψ p (x - y)‖]
    have hA : Ψ p (x - y) = 0 := by
      have h : ‖Ψ p (x - y)‖ = 0 := by nlinarith [norm_nonneg (Ψ p (x - y))]
      exact norm_eq_zero.mp h
    by_cases hlam0 : lam p = 0
    · exact sub_eq_zero.mp (hlinj p hlam0 (by rw [hA, map_zero]))
    · have hlt : 0 < (lam p)^2 := pow_pos (lt_of_le_of_ne (hlamnn p) (Ne.symm hlam0)) 2
      have h2 : (lam p)^2 * ‖x - y‖^2 = 0 := by nlinarith [hsum, hA0]
      have h3 : ‖x - y‖^2 = 0 := by
        rcases mul_eq_zero.mp h2 with h | h
        · exact absurd h (ne_of_gt hlt)
        · exact h
      exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp h3))
  -- so it is invertible, and its inverse depends smoothly on `p`
  have hinv : ∀ p : ℝ × ℝ, (S p).IsInvertible := by
    intro p
    refine ⟨(LinearEquiv.ofBijective (S p : EuclideanSpace ℝ (Fin r) →ₗ[ℝ] EuclideanSpace ℝ (Fin r))
      ⟨hinjS p, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (rfl : Module.finrank ℝ (EuclideanSpace ℝ (Fin r)) = Module.finrank ℝ (EuclideanSpace ℝ (Fin r)))).mp (hinjS p)⟩).toContinuousLinearEquiv, ?_⟩
    ext x
    rfl
  have hSinv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => (S p).inverse) := by
    rw [contDiff_iff_contDiffAt]
    intro p
    exact ((hinv p).contDiffAt_map_inverse).comp p hS.contDiffAt
  -- the Moore–Penrose family
  set P : ℝ × ℝ → (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) :=
    fun q => (Ψ q).comp (((S q).inverse).comp (ContinuousLinearMap.adjoint (Ψ q))) with hPdef
  have hPsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) P := by
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : ℝ × ℝ => ((S q).inverse).comp (ContinuousLinearMap.adjoint (Ψ q))) :=
      hSinv.clm_comp hadj
    have h2 := hΨfam.clm_comp h1
    simpa [hPdef] using h2
  have hP_apply : ∀ (q : ℝ × ℝ) (x : EuclideanSpace ℝ (Fin m)),
      P q x = Ψ q ((S q).inverse ((ContinuousLinearMap.adjoint (Ψ q)) x)) := by
    intro q x
    rw [hPdef]
    rfl
  -- at a zero of `lam` the regulariser disappears
  have hS_eq : ∀ q : ℝ × ℝ, lam q = 0 → S q = (ContinuousLinearMap.adjoint (Ψ q)).comp (Ψ q) := by
    intro q hq
    apply ContinuousLinearMap.ext
    intro z
    rw [hS_apply q z, hq]
    simp [ContinuousLinearMap.comp_apply]
  refine ⟨P, ?_, ?_⟩
  · exact (hPsmooth.comp contDiff_fst).clm_apply contDiff_snd
  · intro p hp
    have hSp : S p = (ContinuousLinearMap.adjoint (Ψ p)).comp (Ψ p) := hS_eq p hp
    have hBA : ∀ z : EuclideanSpace ℝ (Fin r),
        (ContinuousLinearMap.adjoint (Ψ p)) (Ψ p z) = S p z := by
      intro z; rw [hSp]; rfl
    have hBAinv : ∀ y : EuclideanSpace ℝ (Fin m),
        (ContinuousLinearMap.adjoint (Ψ p))
          (Ψ p ((S p).inverse ((ContinuousLinearMap.adjoint (Ψ p)) y)))
          = (ContinuousLinearMap.adjoint (Ψ p)) y := by
      intro y
      rw [hBA ((S p).inverse ((ContinuousLinearMap.adjoint (Ψ p)) y)),
        ContinuousLinearMap.IsInvertible.self_apply_inverse (hinv p)
          ((ContinuousLinearMap.adjoint (Ψ p)) y)]
    -- `P p` fixes `range (Ψ p)`
    have hfix : ∀ x : EuclideanSpace ℝ (Fin r), P p (Ψ p x) = Ψ p x := by
      intro x
      rw [hP_apply p (Ψ p x), hBA x,
        ContinuousLinearMap.IsInvertible.inverse_apply_self (hinv p) x]
    constructor
    · -- idempotence: `P ∘ P = Ψ ∘ S⁻¹ ∘ (Ψ^* ∘ Ψ) ∘ S⁻¹ ∘ Ψ^* = Ψ ∘ S⁻¹ ∘ Ψ^*`
      apply ContinuousLinearMap.ext
      intro x
      show P p (P p x) = P p x
      simp only [hP_apply]
      rw [hBAinv x]
    · -- and its range is exactly `range (Ψ p)`
      apply le_antisymm
      · intro y hy
        obtain ⟨x, hx⟩ := LinearMap.mem_range.mp hy
        refine LinearMap.mem_range.mpr ⟨(S p).inverse ((ContinuousLinearMap.adjoint (Ψ p)) x), ?_⟩
        rw [← hx]
        exact (hP_apply p x).symm
      · intro y hy
        obtain ⟨x, hx⟩ := LinearMap.mem_range.mp hy
        refine LinearMap.mem_range.mpr ⟨Ψ p x, ?_⟩
        rw [← hx]
        exact hfix x

end Work.Drive.Whitney
