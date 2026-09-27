import Mathlib
import Submission.Work.Mostow.geodDeps
import Submission.Work.Mostow.weightDomination
import Submission.Work.Mostow.chord_sq_eq

/-!
# Displacement of a vector by a block-diagonal rotation

`displacementBlocks` is the "block" form of the displacement estimate for an isometry `R` of
`E m = ℝ^m` which preserves an orthogonal decomposition of `ℝ^m` into `m/2` two-dimensional
planes `span {e (i,0), e (i,1)}` and acts on the `i`-th plane as the rotation by the angle
`φ i` (the only thing the hypothesis `hblock` says is that such an angle exists, i.e. that
`R` is a *rotation* -- angle `0` or `π` included -- on that plane).  For any `W`,

  `‖R W - W‖² = Σᵢ ‖Pᵢ W‖² · (2 - 2 cos (φᵢ)) = Σᵢ ‖Pᵢ W‖² · chord(φᵢ)²`,

where `Pᵢ` is the orthogonal projection onto the `i`-th plane and `chord` is the chord length
`2 sin (‖x‖/2)` of the circular angle `x`.  Hence `‖R W - W‖ ≤ ε` gives the weighted bound
`Σᵢ ‖Pᵢ W‖² · chord(φᵢ)² ≤ ε²` used in the GeodStrata/Dirichlet-box chapter of GAP-A.

The proof is linear algebra in the orthonormal basis `e`: `e.repr` turns `e` into coordinates,
the hypothesis `hblock` identifies the coordinates of `R W - W` as `((cᵢ-1) x - sᵢ y, sᵢ x +
(cᵢ-1) y)`, and the identity `((c-1)x - sy)² + (sx + (c-1)y)² = (x²+y²)(2-2c)` plus
`4 sin²(t/2) = 2 - 2 cos t` finishes.
-/

namespace Work.Mostow

open Submission.Mostow

/-- **The block displacement identity.**  If an isometry `R` of a real inner product space `X`
acts on the `i`-th two-dimensional block of an orthonormal basis `e : Fin r × Fin 2 → X` as the
rotation with (cosine, sine) `(c i, s i)` (with `c i ^ 2 + s i ^ 2 = 1`), then the displacement
of `W` splits over the blocks, each block contributing `‖Pᵢ W‖² (2 - 2 c i)`. -/
private lemma block_core {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] {r : ℕ}
    (e : OrthonormalBasis (Fin r × Fin 2) ℝ X) (R : X ≃ₗᵢ[ℝ] X) (c s : Fin r → ℝ)
    (huniv : ∀ i, c i ^ 2 + s i ^ 2 = 1)
    (hblock : ∀ (i : Fin r) (x y : ℝ),
      R (x • e (i, 0) + y • e (i, 1)) =
        (c i * x - s i * y) • e (i, 0) + (s i * x + c i * y) • e (i, 1))
    (W : X) :
    ‖R W - W‖ ^ 2 =
      ∑ i, ‖(inner ℝ (e (i, 0)) W) • e (i, 0) + (inner ℝ (e (i, 1)) W) • e (i, 1)‖ ^ 2 *
        (2 - 2 * c i) := by
  -- the inverse rotation on the block basis vectors
  have hsymm0 : ∀ i : Fin r, R.symm (e (i, 0)) = c i • e (i, 0) - s i • e (i, 1) := by
    intro i
    have h1 : R (c i • e (i, 0) + (-s i) • e (i, 1)) = e (i, 0) := by
      rw [hblock i (c i) (-s i)]
      have hs : c i * c i - s i * -s i = 1 := by nlinarith [huniv i]
      have hs2 : s i * c i + c i * -s i = 0 := by ring
      rw [hs, hs2, one_smul, zero_smul, add_zero]
    have h2 := congrArg R.symm h1
    rw [LinearIsometryEquiv.symm_apply_apply] at h2
    rw [← h2, sub_eq_add_neg, neg_smul]
  have hsymm1 : ∀ i : Fin r, R.symm (e (i, 1)) = s i • e (i, 0) + c i • e (i, 1) := by
    intro i
    have h1 : R (s i • e (i, 0) + c i • e (i, 1)) = e (i, 1) := by
      rw [hblock i (s i) (c i)]
      have hs : c i * s i - s i * c i = 0 := by ring
      have hs2 : s i * s i + c i * c i = 1 := by nlinarith [huniv i]
      rw [hs, hs2, zero_smul, one_smul, zero_add]
    have h2 := congrArg R.symm h1
    rw [LinearIsometryEquiv.symm_apply_apply] at h2
    exact h2.symm
  -- coordinates of the displacement in the basis `e`
  have hcoord0 : ∀ i : Fin r, (e.repr (R W - W)).ofLp (i, 0) =
      (c i - 1) * inner ℝ (e (i, 0)) W - s i * inner ℝ (e (i, 1)) W := by
    intro i
    rw [map_sub, WithLp.ofLp_sub, Pi.sub_apply, OrthonormalBasis.repr_apply_apply,
        OrthonormalBasis.repr_apply_apply]
    have h1 : inner ℝ (e (i, 0)) (R W) = inner ℝ (R.symm (e (i, 0))) W := by
      conv_lhs => rw [← LinearIsometryEquiv.apply_symm_apply R (e (i, 0))]
      rw [LinearIsometryEquiv.inner_map_map]
    rw [h1, hsymm0 i, inner_sub_left, real_inner_smul_left, real_inner_smul_left]
    ring
  have hcoord1 : ∀ i : Fin r, (e.repr (R W - W)).ofLp (i, 1) =
      s i * inner ℝ (e (i, 0)) W + (c i - 1) * inner ℝ (e (i, 1)) W := by
    intro i
    rw [map_sub, WithLp.ofLp_sub, Pi.sub_apply, OrthonormalBasis.repr_apply_apply,
        OrthonormalBasis.repr_apply_apply]
    have h1 : inner ℝ (e (i, 1)) (R W) = inner ℝ (R.symm (e (i, 1))) W := by
      conv_lhs => rw [← LinearIsometryEquiv.apply_symm_apply R (e (i, 1))]
      rw [LinearIsometryEquiv.inner_map_map]
    rw [h1, hsymm1 i, inner_add_left, real_inner_smul_left, real_inner_smul_left]
    ring
  -- the squared norm of the `i`-th block component of `W`
  have hZi : ∀ i : Fin r, ‖(inner ℝ (e (i, 0)) W) • e (i, 0) + (inner ℝ (e (i, 1)) W) • e (i, 1)‖ ^ 2
      = (inner ℝ (e (i, 0)) W) ^ 2 + (inner ℝ (e (i, 1)) W) ^ 2 := by
    intro i
    have hu : ‖e (i, 0)‖ ^ 2 = 1 := by
      rw [← real_inner_self_eq_norm_sq, e.inner_eq_ite (i, 0) (i, 0)]; simp
    have hv : ‖e (i, 1)‖ ^ 2 = 1 := by
      rw [← real_inner_self_eq_norm_sq, e.inner_eq_ite (i, 1) (i, 1)]; simp
    have hinner : inner ℝ (e (i, 0)) (e (i, 1)) = 0 := by
      rw [e.inner_eq_ite (i, 0) (i, 1)]; simp
    rw [norm_add_sq_real, real_inner_smul_left, real_inner_smul_right, hinner, norm_smul, norm_smul,
        mul_pow, mul_pow, hu, hv, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
    ring
  calc ‖R W - W‖ ^ 2
      = ∑ j : Fin r × Fin 2, (e.repr (R W - W)).ofLp j ^ 2 := by
        rw [← LinearIsometryEquiv.norm_map (e.repr) (R W - W), EuclideanSpace.real_norm_sq_eq]
    _ = ∑ i, (((e.repr (R W - W)).ofLp (i, 0)) ^ 2 + ((e.repr (R W - W)).ofLp (i, 1)) ^ 2) := by
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro i _
        rw [Fin.sum_univ_two]
    _ = ∑ i, (((c i - 1) * inner ℝ (e (i, 0)) W - s i * inner ℝ (e (i, 1)) W) ^ 2
          + (s i * inner ℝ (e (i, 0)) W + (c i - 1) * inner ℝ (e (i, 1)) W) ^ 2) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hcoord0 i, hcoord1 i]
    _ = ∑ i, ‖(inner ℝ (e (i, 0)) W) • e (i, 0) +
            (inner ℝ (e (i, 1)) W) • e (i, 1)‖ ^ 2 * (2 - 2 * c i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hZi i]
        nlinarith [huniv i]

/-- `chord` in terms of `Real.Angle.cos`, i.e. the well-defined cosine of the circular angle. -/
private lemma chord_sq_angle (x : AddCircle (2 * Real.pi)) :
    (chord x) ^ 2 = 2 - 2 * Real.Angle.cos x := by
  rw [chord]
  exact chord_sq_eq x

theorem displacementBlocks (m : ℕ) (hm : Even m)
    (e : OrthonormalBasis (Fin (m / 2) × Fin 2) ℝ (Submission.Mostow.E m))
    (R : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m)
    (φ : Fin (m / 2) → AddCircle (2 * Real.pi))
    (hblock : ∀ (i : Fin (m / 2)) (x y : ℝ), ∃ t : ℝ, (t : AddCircle (2 * Real.pi)) = φ i ∧
      R (x • e (i, Fin.castSucc 0) + y • e (i, 1)) =
        (Real.cos t * x - Real.sin t * y) • e (i, Fin.castSucc 0) +
          (Real.sin t * x + Real.cos t * y) • e (i, 1))
    (W : Submission.Mostow.E m) (ε : ℝ) (hε : 0 ≤ ε) (hW : ‖R W - W‖ ≤ ε) :
    ∑ i, (‖(inner ℝ (e (i, Fin.castSucc 0)) W) • e (i, Fin.castSucc 0) +
        (inner ℝ (e (i, 1)) W) • e (i, 1)‖) ^ 2 * (Submission.Mostow.chord (φ i)) ^ 2 ≤ ε ^ 2 := by
  -- the block hypothesis is unambiguous: the cosine and sine of the angle are those of `φ i`
  have huniv : ∀ i : Fin (m / 2), Real.Angle.cos (φ i) ^ 2 + Real.Angle.sin (φ i) ^ 2 = 1 :=
    fun i => Real.Angle.cos_sq_add_sin_sq (φ i)
  have hblock' : ∀ (i : Fin (m / 2)) (x y : ℝ),
      R (x • e (i, 0) + y • e (i, 1)) =
        (Real.Angle.cos (φ i) * x - Real.Angle.sin (φ i) * y) • e (i, 0) +
          (Real.Angle.sin (φ i) * x + Real.Angle.cos (φ i) * y) • e (i, 1) := by
    intro i x y
    obtain ⟨t, ht, hR⟩ := hblock i x y
    have hcos : Real.cos t = Real.Angle.cos (φ i) := by
      rw [← ht]; exact Real.Angle.cos_coe t
    have hsin : Real.sin t = Real.Angle.sin (φ i) := by
      rw [← ht]; exact Real.Angle.sin_coe t
    rw [hcos, hsin] at hR
    exact hR
  have hcore := block_core e R (fun i => Real.Angle.cos (φ i)) (fun i => Real.Angle.sin (φ i))
      huniv hblock' W
  have hmain : ∑ i, (‖(inner ℝ (e (i, Fin.castSucc 0)) W) • e (i, Fin.castSucc 0) +
        (inner ℝ (e (i, 1)) W) • e (i, 1)‖) ^ 2 * (Submission.Mostow.chord (φ i)) ^ 2
      = ‖R W - W‖ ^ 2 := by
    rw [hcore]
    apply Finset.sum_congr rfl
    intro i _
    rw [chord_sq_angle (φ i)]
    rfl
  rw [hmain]
  exact pow_le_pow_left₀ (norm_nonneg _) hW 2

end Work.Mostow
