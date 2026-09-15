/-
Copyright: the formalization team of the Vinogradov mean value theorem project.
-/
import Submission.Vinogradov.CurveLayer
import Submission.Commons.Analysis.MomentCurve.projected_torsion_det_orthogonal
import Submission.Commons.Analysis.MomentCurve.linearIndependent_gam
import Submission.Commons.Analysis.MomentCurve.gam_gram_det_lower
import Submission.Commons.Analysis.MomentCurve.gammaDeriv_taylor_tail

/-!
# The lower-dimensional projection of the moment curve (GLYZ §3.4)

Guo–Li–Yung–Zorin-Kranich, *A short proof of ℓ² decoupling for the moment curve*
(arXiv:1912.09798), §3.4: for `ξ' ∈ [0,1]` let

    `V^{k-l}(ξ') = span{Γ^{(1)}(ξ'), …, Γ^{(k-l)}(ξ')}`,

the space spanned by the first `k-l` derivative vectors of the moment curve, and let
`H = V^{k-l}(ξ')^⊥`, an `l`-dimensional subspace of `E k`.  Restricting a function with Fourier
support in a `k`-dimensional plate to the translates `H + z` of `H`, and using
`H ≅ ℝ^l`, produces a function on `E l` whose Fourier support lies in the plate of the
*projected curve* `P ∘ Γ`, where `P` is the orthogonal projection onto `H`.

This module sets up that projection:

* `torsionSpan k l ξ'`, `torsionCompl k l ξ'` (the subspace `H`), with
  `finrank_torsionCompl : finrank ℝ H = l`;
* `torsionBasis` — an orthonormal basis `b : Fin l → E k` of `H`, and
  `projMapLin k l b : E k →ₗ[ℝ] E l` (`x ↦ (⟪b i, x⟫)_i`, the coordinates of the orthogonal
  projection of `x` onto `H`) with its transpose `projEmbedLin k l b : E l →ₗ[ℝ] E k`
  (`y ↦ Σ i, y i • b i`);
* `projCurveDeriv k l b i t = projMapLin k l b (Γ^{(i)}(t))` — the derivative family of the
  projected curve;
* the three hypotheses `CurveBounded`, `CurveTaylor`, `CurveTorsion` are verified for that
  family, with explicit constants (the torsion one is the content of GLYZ Lemma 3.5 via
  `Commons.Analysis.MomentCurve.projected_torsion_det_orthogonal`);
* `projMapLin_image_plate` — the image of a plate under the projection is *exactly* the plate of
  the projected curve (no constants lost);
* `isFourierRep_proj_map` — the restriction of an element of the class to the translates of `H`
  belongs to the class of the projected curve.
-/

noncomputable section
open MeasureTheory Complex Classical Filter
open scoped Real BigOperators Topology RealInnerProductSpace ENNReal NNReal Pointwise

set_option autoImplicit false
set_option linter.style.emptyLine false
set_option maxHeartbeats 1000000

namespace Submission.Vinogradov

/-! ## 1. The torsion subspace and its orthogonal complement -/

/-- `V^{k-l}(ξ')`: the span of the first `k-l` derivative vectors of the moment curve at `ξ'`. -/
noncomputable def torsionSpan (k l : ℕ) (ξ' : ℝ) : Submodule ℝ (E k) :=
  Submodule.span ℝ (Set.range (fun i : Fin (k - l) => gammaDeriv k (i.val + 1) ξ'))

/-- `H = V^{k-l}(ξ')^⊥`, the `l`-dimensional subspace onto which GLYZ §3.4 projects. -/
noncomputable def torsionCompl (k l : ℕ) (ξ' : ℝ) : Submodule ℝ (E k) := (torsionSpan k l ξ')ᗮ

/-- The derivative vector `Γ^{(i)}(t)` of the moment curve is the `L²`-model representative of
the `gam`-coordinate vector of the commons development. -/
lemma gammaDeriv_eq_lpSymm_gam (k : ℕ) (i : ℕ) (t : ℝ) :
    gammaDeriv k i t
      = (WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).symm
          (Commons.Analysis.MomentCurve.gam k t i) := by
  have h : (WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).symm
        (Commons.Analysis.MomentCurve.gam k t i)
      = (WithLp.equiv 2 (Fin k → ℝ)).symm
          (Commons.Analysis.MomentCurve.gam k t i) := rfl
  rw [h]
  ext j
  rw [gammaDeriv_apply, WithLp.equiv_symm_apply, WithLp.ofLp_toLp,
    Commons.Analysis.MomentCurve.gam_apply]

/-- The first `k-l` derivative vectors of the moment curve at `ξ'` are linearly independent. -/
lemma linearIndependent_torsionSpan (k l : ℕ) (hlk : l ≤ k) (ξ' : ℝ) :
    LinearIndependent ℝ (fun i : Fin (k - l) => gammaDeriv k (i.val + 1) ξ') := by
  have hgam := Commons.Analysis.MomentCurve.linearIndependent_gam k (k - l) (by omega) ξ'
  have hker : LinearMap.ker ((WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).symm :
      (Fin k → ℝ) →ₗ[ℝ] E k) = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro a b h
    exact (WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).symm.injective h
  have h1 := hgam.map' ((WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).symm :
      (Fin k → ℝ) →ₗ[ℝ] E k) hker
  have heq : (fun i : Fin (k - l) => gammaDeriv k (i.val + 1) ξ')
      = ((WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).symm ∘
          fun i : Fin (k - l) => Commons.Analysis.MomentCurve.gam k ξ' (i.val + 1)) := by
    funext i
    exact gammaDeriv_eq_lpSymm_gam k (i.val + 1) ξ'
  rw [heq]
  exact h1

/-- The span of the first `k-l` derivative vectors has dimension `k-l`. -/
lemma finrank_torsionSpan (k l : ℕ) (hlk : l ≤ k) (ξ' : ℝ) :
    Module.finrank ℝ (torsionSpan k l ξ') = k - l := by
  rw [torsionSpan]
  rw [finrank_span_eq_card (linearIndependent_torsionSpan k l hlk ξ')]
  simp

/-- `H = V^{k-l}(ξ')^⊥` has dimension `l`. -/
lemma finrank_torsionCompl (k l : ℕ) (hlk : l ≤ k) (ξ' : ℝ) :
    Module.finrank ℝ (torsionCompl k l ξ') = l := by
  have h := Submodule.finrank_add_finrank_orthogonal (torsionSpan k l ξ')
  rw [finrank_torsionSpan k l hlk ξ', finrank_euclideanSpace] at h
  have h2 : (k - l) + Module.finrank ℝ (torsionCompl k l ξ') = k := by
    rw [torsionCompl]; simpa using h
  omega

/-! ## 2. An orthonormal basis of `H`, and the projection pair -/

/-- An orthonormal basis of `H = V^{k-l}(ξ')^⊥`, indexed by `Fin l`. -/
noncomputable def torsionBasis (k l : ℕ) (hlk : l ≤ k) (ξ' : ℝ) :
    OrthonormalBasis (Fin l) ℝ (torsionCompl k l ξ') :=
  (stdOrthonormalBasis ℝ (torsionCompl k l ξ')).reindex
    (finCongr (finrank_torsionCompl k l hlk ξ'))

/-- The orthonormal family of `E k` underlying `torsionBasis`. -/
noncomputable def torsionVec (k l : ℕ) (hlk : l ≤ k) (ξ' : ℝ) : Fin l → E k :=
  fun i => ((torsionBasis k l hlk ξ') i : E k)

lemma orthonormal_torsionVec (k l : ℕ) (hlk : l ≤ k) (ξ' : ℝ) :
    Orthonormal ℝ (torsionVec k l hlk ξ') := by
  rw [orthonormal_iff_ite]
  intro i j
  simp only [torsionVec]
  rw [← Submodule.coe_inner (torsionCompl k l ξ') (torsionBasis k l hlk ξ' i)
    (torsionBasis k l hlk ξ' j)]
  exact (orthonormal_iff_ite.mp (torsionBasis k l hlk ξ').orthonormal i j)

/-- The orthonormal family `torsionVec` spans `H`. -/
lemma span_torsionVec (k l : ℕ) (hlk : l ≤ k) (ξ' : ℝ) :
    Submodule.span ℝ (Set.range (torsionVec k l hlk ξ')) = torsionCompl k l ξ' := by
  refine le_antisymm ?_ ?_
  · rw [Submodule.span_le]
    rintro x ⟨i, rfl⟩
    exact (torsionBasis k l hlk ξ' i).2
  · intro x hx
    have h := OrthonormalBasis.sum_repr (torsionBasis k l hlk ξ')
      (⟨x, hx⟩ : ↥(torsionCompl k l ξ'))
    have h2 := congrArg (fun z : ↥(torsionCompl k l ξ') => (z : E k)) h
    have hmem : (∑ i : Fin l,
          ((torsionBasis k l hlk ξ').repr (⟨x, hx⟩ : ↥(torsionCompl k l ξ'))).ofLp i
            • torsionVec k l hlk ξ' i) = x := by
      simpa [torsionVec] using h2
    rw [← hmem]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-! ## 3. The projection pair: `E k → E l` (coordinates) and its transpose -/

/-- **The coordinate map of the orthogonal projection onto `H`**: `x ↦ (⟪b i, x⟫)_i`, where
`b` is an orthonormal basis of `H`. -/
noncomputable def projMapLin (k l : ℕ) (b : Fin l → E k) : E k →ₗ[ℝ] E l :=
  ((WithLp.linearEquiv 2 ℝ (Fin l → ℝ)).symm).toLinearMap.comp
    (LinearMap.pi fun i => ((innerSL ℝ (b i)).toLinearMap : E k →ₗ[ℝ] ℝ))

/-- **The transpose**: `y ↦ Σ i, y i • b i`, the linear map with range `H`. -/
noncomputable def projEmbedLin (k l : ℕ) (b : Fin l → E k) : E l →ₗ[ℝ] E k where
  toFun y := ∑ i : Fin l, y i • b i
  map_add' y z := by
    simp only [PiLp.add_apply]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [add_smul]
  map_smul' c y := by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [PiLp.smul_apply, smul_eq_mul, smul_smul]
      simp

lemma projMapLin_apply (k l : ℕ) (b : Fin l → E k) (x : E k) :
    WithLp.ofLp (projMapLin k l b x) = fun i => ⟪b i, x⟫ := by
  funext i
  simp only [projMapLin, LinearMap.comp_apply, LinearMap.pi_apply,
    WithLp.equiv_symm_apply, WithLp.ofLp_toLp]
  rfl

lemma projMapLin_apply_coord (k l : ℕ) (b : Fin l → E k) (x : E k) (i : Fin l) :
    projMapLin k l b x i = ⟪b i, x⟫ := by
  have h := congrFun (projMapLin_apply k l b x) i
  simpa using h

lemma projEmbedLin_apply (k l : ℕ) (b : Fin l → E k) (y : E l) :
    projEmbedLin k l b y = ∑ i : Fin l, y i • b i := rfl

/-- The two maps are adjoint to one another. -/
lemma inner_projEmbed_projMap (k l : ℕ) (b : Fin l → E k) (y : E l) (x : E k) :
    ⟪projEmbedLin k l b y, x⟫ = ⟪y, projMapLin k l b x⟫ := by
  rw [projEmbedLin_apply, sum_inner, PiLp.inner_apply, projMapLin_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_smul_left]
  simp [Real.inner_apply, mul_comm]

/-- The composition `projMapLin ∘ projEmbedLin` is the identity on `E l` for an orthonormal
family `b`. -/
lemma projMapLin_projEmbedLin (k l : ℕ) {b : Fin l → E k} (hb : Orthonormal ℝ b) (y : E l) :
    projMapLin k l b (projEmbedLin k l b y) = y := by
  apply WithLp.ofLp_injective
  rw [projMapLin_apply]
  funext i
  rw [projEmbedLin_apply, inner_sum]
  have h : ∀ j : Fin l, ⟪b i, y j • b j⟫ = (if i = j then y j else 0) := by
    intro j
    rw [inner_smul_right, orthonormal_iff_ite.mp hb i j]
    by_cases hij : i = j
    · rw [if_pos hij, if_pos hij, mul_one]
    · rw [if_neg hij, if_neg hij, mul_zero]
  rw [Finset.sum_congr rfl (fun j _ => h j), Finset.sum_ite_eq]
  simp

/-! ## 4. The orthogonal projection expanded in an orthonormal family -/

/-- **The orthogonal projection onto the span of an orthonormal family**, expanded in the
family: `H.starProjection x = Σ i, ⟪b i, x⟫ • b i`. -/
lemma starProjection_eq_sum_inner_smul {k l : ℕ} {H : Submodule ℝ (E k)} {b : Fin l → E k}
    (hb : Orthonormal ℝ b) (hspan : Submodule.span ℝ (Set.range b) = H) (x : E k) :
    H.starProjection x = ∑ i : Fin l, ⟪b i, x⟫ • b i := by
  have hmem : (∑ i : Fin l, ⟪b i, x⟫ • b i) ∈ H :=
    Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (hspan ▸ Submodule.subset_span (Set.mem_range_self i))
  have horth : ∀ w ∈ H, ⟪x - ∑ i : Fin l, ⟪b i, x⟫ • b i, w⟫ = 0 := by
    intro w hw
    have hw' : w ∈ Submodule.span ℝ (Set.range b) := by rw [hspan]; exact hw
    have hprop : ∀ w ∈ Submodule.span ℝ (Set.range b),
        ⟪x - ∑ i : Fin l, ⟪b i, x⟫ • b i, w⟫ = 0 := by
      intro w hw
      refine Submodule.span_induction (p := fun w (_ : w ∈ Submodule.span ℝ (Set.range b)) =>
        ⟪x - ∑ i : Fin l, ⟪b i, x⟫ • b i, w⟫ = 0) ?_ ?_ ?_ ?_ hw
      · intro w hw
        obtain ⟨j, rfl⟩ := hw
        rw [inner_sub_left, sum_inner]
        have h : ∀ i : Fin l, ⟪⟪b i, x⟫ • b i, b j⟫ = (if i = j then ⟪b i, x⟫ else 0) := by
          intro i
          rw [inner_smul_left, starRingEnd_apply, star_trivial,
            orthonormal_iff_ite.mp hb i j]
          by_cases hij : i = j
          · rw [if_pos hij, if_pos hij, mul_one]
          · rw [if_neg hij, if_neg hij, mul_zero]
        rw [Finset.sum_congr rfl (fun i _ => h i), Finset.sum_ite_eq',
          if_pos (Finset.mem_univ j), sub_eq_zero]
        exact (real_inner_comm x (b j)).symm
      · simp
      · intro a c ha hc hpa hpc
        rw [inner_add_right, hpa, hpc, add_zero]
      · intro r c hc hpc
        rw [inner_smul_right, hpc, mul_zero]
    exact hprop w hw'
  exact Submodule.eq_starProjection_of_mem_of_inner_eq_zero hmem horth

/-- **The Gram matrix of the projected vectors.**  For an orthonormal family `b` spanning `H`,
the Gram matrix of the images of `v` under the coordinate map of the projection equals the
Gram matrix of the orthogonal projections of `v` onto `H`. -/
lemma gram_projMapLin_eq_gram_starProjection {k l : ℕ} {H : Submodule ℝ (E k)} {b : Fin l → E k}
    (hb : Orthonormal ℝ b) (hspan : Submodule.span ℝ (Set.range b) = H)
    {ι : Type*} (v : ι → E k) :
    Matrix.gram ℝ (fun i => projMapLin k l b (v i))
      = Matrix.gram ℝ (fun i => H.starProjection (v i)) := by
  ext i j
  rw [Matrix.gram_apply, Matrix.gram_apply]
  have hL : ⟪projMapLin k l b (v i), projMapLin k l b (v j)⟫
      = ∑ m : Fin l, ⟪b m, v i⟫ * ⟪b m, v j⟫ := by
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [projMapLin_apply_coord, projMapLin_apply_coord, Real.inner_apply]
  have hR : ⟪H.starProjection (v i), H.starProjection (v j)⟫
      = ∑ m : Fin l, ⟪b m, v i⟫ * ⟪b m, v j⟫ := by
    rw [starProjection_eq_sum_inner_smul hb hspan (v i),
      starProjection_eq_sum_inner_smul hb hspan (v j), sum_inner]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [inner_sum, Finset.sum_eq_single m]
    · rw [inner_smul_left, starRingEnd_apply, star_trivial, inner_smul_right,
        orthonormal_iff_ite.mp hb m m, if_pos rfl]
      ring
    · intro n _ hn
      rw [inner_smul_left, starRingEnd_apply, star_trivial, inner_smul_right,
        orthonormal_iff_ite.mp hb m n, if_neg (Ne.symm hn)]
      ring
    · intro hm; exact absurd (Finset.mem_univ m) hm
  rw [hL, hR]

/-- The coordinate map of the projection is a contraction. -/
lemma norm_projMapLin_le (k l : ℕ) {b : Fin l → E k} (hb : Orthonormal ℝ b) (x : E k) :
    ‖projMapLin k l b x‖ ≤ ‖x‖ := by
  have h2 : ‖projMapLin k l b x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [norm_sq_coord_sum]
    have h1 : (∑ j : Fin l, (projMapLin k l b x).ofLp j ^ 2)
        = ∑ j : Fin l, ⟪b j, x⟫ ^ 2 := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [projMapLin_apply_coord]
    rw [h1]
    have hbessel := Orthonormal.sum_inner_products_le x hb (s := Finset.univ)
    simpa [Real.norm_eq_abs, sq_abs] using hbessel
  have h3 := Real.sqrt_le_sqrt h2
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h3

/-- The coordinate map of the projection is adjoint to the embedding of `H`. -/
lemma isFourierRep_proj_map (k l : ℕ) (b : Fin l → E k) (z : E k)
    {U : Set (E k)} {f : E k → ℂ} (hf : IsFourierRep k U f) :
    IsFourierRep l (projMapLin k l b '' U) (fun y => f (projEmbedLin k l b y + z)) := by
  obtain ⟨ι, m, Γ, ν, φ, hν, hφ, hΓ, hmφ, hU, hf⟩ := isFourierRep_iff.mp hf
  have h := isFourierRep_proj (k := k) (l := l) z (projEmbedLin k l b) (projMapLin k l b)
    (inner_projEmbed_projMap k l b) hν hφ hmφ hΓ hU
  rw [repFun_proj_eq k l Γ ν φ z (projEmbedLin k l b) (projMapLin k l b)
    (inner_projEmbed_projMap k l b)] at h
  rw [← hf] at h
  exact h

/-! ## 5. The projected curve -/

/-- The derivative family of the projected curve: `D i t = M(Γ^{(i)}(t))` where `M` is the
coordinate map of the orthogonal projection onto `H = span b`. -/
noncomputable def projCurveDeriv (k l : ℕ) (b : Fin l → E k) (i : ℕ) (t : ℝ) : E l :=
  projMapLin k l b (gammaDeriv k i t)

lemma projCurveDeriv_zero (k l : ℕ) (b : Fin l → E k) (t : ℝ) :
    projCurveDeriv k l b 0 t = projMapLin k l b (gammaVec k t) := by
  rw [projCurveDeriv, gammaDeriv_zero]

/-- The coordinate map of the projection of the moment-curve derivative vectors, in the
`gam`-normalisation of the commons development. -/
lemma projCurveDeriv_eq_lpSymm (k l : ℕ) (b : Fin l → E k) (i : ℕ) (t : ℝ) :
    projCurveDeriv k l b i t
      = projMapLin k l b ((WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).symm
          (Commons.Analysis.MomentCurve.gam k t i)) := by
  rw [projCurveDeriv, gammaDeriv_eq_lpSymm_gam]

/-- The projected curve is coordinate-wise bounded on `[0,1]` by `√k · k!`. -/
lemma CurveBounded_projCurveDeriv (k l : ℕ) (hlk : l ≤ k) {b : Fin l → E k}
    (hb : Orthonormal ℝ b) :
    CurveBounded l (projCurveDeriv k l b) (Real.sqrt k * (k.factorial : ℝ)) := by
  intro i _ t ht j
  have hcoe : projCurveDeriv k l b i t j = ⟪b j, gammaDeriv k i t⟫ := by
    rw [projCurveDeriv, projMapLin_apply]
  have hb1 : ‖b j‖ = 1 := hb.1 j
  calc |projCurveDeriv k l b i t j| = |⟪b j, gammaDeriv k i t⟫| := by rw [hcoe]
    _ ≤ ‖b j‖ * ‖gammaDeriv k i t‖ := abs_real_inner_le_norm _ _
    _ = ‖gammaDeriv k i t‖ := by rw [hb1, one_mul]
    _ ≤ Real.sqrt k * (k.factorial : ℝ) := by
        refine norm_le_sqrt_card_mul_of_coord_le _ (Nat.cast_nonneg _) fun j' => ?_
        exact gammaDeriv_coord_abs_le k (by rw [abs_of_nonneg ht.1]; exact ht.2) i j'

/-- The `L²`-model of a `gam`-vector is controlled by the sup norm of its coordinates. -/
lemma norm_lpSymm_le (k : ℕ) (w : Fin k → ℝ) :
    ‖((WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).symm w : E k)‖ ≤ Real.sqrt k * ‖w‖ := by
  refine norm_le_sqrt_card_mul_of_coord_le _ (norm_nonneg w) fun j => ?_
  rw [show ((WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).symm w : E k) j = w j from rfl]
  exact norm_le_pi_norm w j

/-- The projected curve satisfies the Taylor-remainder bound. -/
lemma CurveTaylor_projCurveDeriv (k l : ℕ) (hl : 1 ≤ l) (hlk : l ≤ k) {b : Fin l → E k}
    (hb : Orthonormal ℝ b) :
    ∃ R : ℝ, 0 < R ∧ CurveTaylor l (projCurveDeriv k l b) R := by
  obtain ⟨C, hC, htail⟩ := Commons.Analysis.MomentCurve.gammaDeriv_taylor_tail k
  have hk1 : 1 ≤ k := le_trans hl hlk
  have hkpos : 0 < Real.sqrt k := Real.sqrt_pos.mpr (by exact_mod_cast hk1)
  refine ⟨Real.sqrt k * C, mul_pos hkpos hC, ?_⟩
  intro i m t u him hml ht hu
  set w : E k := (WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).symm
      (Commons.Analysis.MomentCurve.gam k (t + u) i
        - ∑ j ∈ Finset.Icc i m, (u ^ (j - i) / ((j - i).factorial : ℝ))
            • Commons.Analysis.MomentCurve.gam k t j) with hw
  have hterm : ∀ (j : ℕ) (s : ℝ), projCurveDeriv k l b j s
      = projMapLin k l b ((WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).symm
          (Commons.Analysis.MomentCurve.gam k s j)) := fun j s => projCurveDeriv_eq_lpSymm k l b j s
  have hsum : (∑ j ∈ Finset.Icc i m, (u ^ (j - i) / ((j - i).factorial : ℝ))
        • projCurveDeriv k l b j t)
      = projMapLin k l b (∑ j ∈ Finset.Icc i m, (u ^ (j - i) / ((j - i).factorial : ℝ))
          • (WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).symm
              (Commons.Analysis.MomentCurve.gam k t j)) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [map_smul, hterm j t]
  have hsub : projCurveDeriv k l b i (t + u)
        - ∑ j ∈ Finset.Icc i m, (u ^ (j - i) / ((j - i).factorial : ℝ))
            • projCurveDeriv k l b j t
      = projMapLin k l b w := by
    rw [hterm i (t + u), hsum, ← map_sub]
    congr 1
    have hsum' : (∑ j ∈ Finset.Icc i m, (u ^ (j - i) / ((j - i).factorial : ℝ))
          • (WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).symm
              (Commons.Analysis.MomentCurve.gam k t j))
        = (WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).symm
            (∑ j ∈ Finset.Icc i m, (u ^ (j - i) / ((j - i).factorial : ℝ))
              • Commons.Analysis.MomentCurve.gam k t j) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [map_smul]
    rw [hsum', ← map_sub, hw]
  rw [hsub]
  refine (norm_projMapLin_le k l hb w).trans ?_
  have hwn : ‖w‖ ≤ Real.sqrt k * ‖Commons.Analysis.MomentCurve.gam k (t + u) i
      - ∑ j ∈ Finset.Icc i m, (u ^ (j - i) / ((j - i).factorial : ℝ))
          • Commons.Analysis.MomentCurve.gam k t j‖ := by
    rw [hw]
    exact norm_lpSymm_le k _
  refine hwn.trans ?_
  calc Real.sqrt k * ‖Commons.Analysis.MomentCurve.gam k (t + u) i
        - ∑ j ∈ Finset.Icc i m, (u ^ (j - i) / ((j - i).factorial : ℝ))
            • Commons.Analysis.MomentCurve.gam k t j‖
      ≤ Real.sqrt k * (C * |u| ^ (m + 1 - i)) :=
        mul_le_mul_of_nonneg_left
          (htail i m t u him (le_trans hml hlk) (by rw [abs_of_nonneg ht.1]; exact ht.2) hu)
          (Real.sqrt_nonneg k)
    _ = Real.sqrt k * C * |u| ^ (m + 1 - i) := by ring

/-- **The torsion of the projected curve** on the part of `[0,1]` separated from `ξ'`: this is
GLYZ Lemma 3.5 in the quantitative Gram-determinant form, taken from
`Commons.Analysis.MomentCurve.projected_torsion_det_orthogonal`. -/
lemma torsion_projCurveDeriv (k l : ℕ) (hl : 1 ≤ l) (hlk : l ≤ k) (ξ' : ℝ)
    (hξ' : ξ' ∈ Set.Icc (0 : ℝ) 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1, 1 / 4 ≤ |t - ξ'| →
      c ≤ (Matrix.gram ℝ
        (fun j : Fin l => projCurveDeriv k l (torsionVec k l hlk ξ') (j.val + 1) t)).det := by
  obtain ⟨c, hc, h⟩ :=
    Commons.Analysis.MomentCurve.projected_torsion_det_orthogonal k l hl hlk
  refine ⟨c, hc, ?_⟩
  intro t ht hsep
  have hgram := gram_projMapLin_eq_gram_starProjection
    (orthonormal_torsionVec k l hlk ξ') (span_torsionVec k l hlk ξ')
    (fun j : Fin l => gammaDeriv k (j.val + 1) t)
  simp only [projCurveDeriv]
  rw [hgram]
  have hV : Submodule.span ℝ (Set.range (fun i : Fin (k - l) =>
      (WithLp.equiv 2 (Fin k → ℝ)).symm (Commons.Analysis.MomentCurve.gam k ξ' (i.val + 1))))
      = torsionSpan k l ξ' := by
    rw [torsionSpan]
    congr 1
  have hmain := h ξ' t hξ'.1 hξ'.2 ht.1 ht.2 (by rwa [abs_sub_comm] at hsep)
  rw [hV] at hmain
  have harg : ∀ j : Fin l, (WithLp.equiv 2 (Fin k → ℝ)).symm
      (Commons.Analysis.MomentCurve.gam k t (j.val + 1)) = gammaDeriv k (j.val + 1) t :=
    fun j => (gammaDeriv_eq_lpSymm_gam k (j.val + 1) t).symm
  simpa only [torsionCompl, harg] using hmain

/-! ## 6. The image of a `k`-dimensional plate under the projection: reduction to the
`l`-dimensional plate plus a small remainder -/

/-- **The `k`-dimensional plate as the image of the standard box under `plateMapLin`.** -/
lemma plate_eq_image_plateMapLin (k : ℕ) (δ c : ℝ) :
    plate k δ c = (fun u : E k => gammaVec k c + plateMapLin k δ c u) '' unitBox k := by
  have hbox : plateBox k = diagFact k '' unitBox k := by
    rw [unitBox, diagFact_image_box]
  rw [plate, hbox, Set.image_image]
  congr 1

/-- **The image of a plate under the projection.**  With `T := projMapLin ∘ plateMapLin`, the
projection of the `k`-dimensional plate is the affine image of the standard box under `T`. -/
lemma projMapLin_image_plate_eq (k l : ℕ) (b : Fin l → E k) (δ c : ℝ) :
    projMapLin k l b '' plate k δ c
      = (fun u : E k => projMapLin k l b (gammaVec k c)
          + (projMapLin k l b).comp (plateMapLin k δ c) u) '' unitBox k := by
  rw [plate_eq_image_plateMapLin, Set.image_image]
  congr 1
  funext u
  rw [map_add, LinearMap.comp_apply]

/-- **The action of `projMapLin ∘ plateMapLin` on the coordinates**: the `i`-th coordinate vector
is sent to `δ^(i+1) · D^(i+1)(c)`. -/
lemma comp_plateMapLin_single (k l : ℕ) (b : Fin l → E k) (δ c : ℝ) (i : Fin k) :
    (projMapLin k l b).comp (plateMapLin k δ c) (PiLp.single 2 i 1)
      = δ ^ (i.val + 1) • projCurveDeriv k l b (i.val + 1) c := by
  rw [LinearMap.comp_apply, plateMapLin_single, map_smul, projCurveDeriv]

lemma comp_plateMapLin_apply (k l : ℕ) (b : Fin l → E k) (δ c : ℝ) (u : E k) :
    (projMapLin k l b).comp (plateMapLin k δ c) u
      = ∑ i : Fin k, u i • (δ ^ (i.val + 1) • projCurveDeriv k l b (i.val + 1) c) := by
  conv_lhs => rw [← sum_single_eq k u]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, comp_plateMapLin_single]

/-- Splitting a sum over `Fin k` into the part with index `< l` and its complement, the former
reindexed by `Fin l`. -/
lemma sum_filter_castLE {M : Type*} [AddCommMonoid M] (k l : ℕ) (hlk : l ≤ k)
    (F : Fin k → M) :
    (∑ i ∈ (Finset.univ.filter fun i : Fin k => i.val < l), F i)
      = ∑ j : Fin l, F ⟨j.val, lt_of_lt_of_le j.isLt hlk⟩ := by
  have hset : (Finset.univ.filter fun i : Fin k => i.val < l)
      = Finset.univ.image (fun j : Fin l => (⟨j.val, lt_of_lt_of_le j.isLt hlk⟩ : Fin k)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h
      exact ⟨⟨i.val, h⟩, by ext; rfl⟩
    · rintro ⟨j, rfl⟩
      exact j.isLt
  rw [hset]
  exact Finset.sum_image (s := Finset.univ)
    (g := fun j : Fin l => (⟨j.val, lt_of_lt_of_le j.isLt hlk⟩ : Fin k)) (f := F)
    (fun x _ y _ h => Fin.ext (by simpa using congrArg Fin.val h))

/-- The set of coordinates `u : E l` with `|u i| ≤ 1` is convex. -/
lemma convex_unitBox (l : ℕ) : Convex ℝ (unitBox l) := by
  have h : unitBox l = (WithLp.linearEquiv 2 ℝ (Fin l → ℝ)) ⁻¹'
      Set.pi Set.univ (fun _ : Fin l => Set.Icc (-1 : ℝ) 1) := by
    ext y
    simp only [unitBox, Set.mem_preimage, WithLp.coe_linearEquiv,
      Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_Icc, abs_le, Set.mem_ofPred_eq]
  rw [h]
  exact (convex_pi fun _ _ => convex_Icc (-1 : ℝ) 1).linear_preimage _

/-- **Scaling a plate box.**  For `λ ≥ 1`, `λ` times the box `curvePlateLin l D δ t '' unitBox l`
is contained in the box at scale `λ δ`: the coefficient change `w i ↦ w i / λ^i` keeps the
coordinates inside `[-1,1]` and compensates the scaling of the `i`-th side exactly. -/
lemma smul_curvePlateLin_subset {l : ℕ} (D : ℕ → ℝ → E l) {δ t lam : ℝ} (hlam : 1 ≤ lam) :
    lam • (curvePlateLin l D δ t '' unitBox l)
      ⊆ curvePlateLin l D (lam * δ) t '' unitBox l := by
  rintro x ⟨y, ⟨w, hw, rfl⟩, rfl⟩
  have hlam0 : (0 : ℝ) < lam := lt_of_lt_of_le zero_lt_one hlam
  refine ⟨(WithLp.equiv 2 (Fin l → ℝ)).symm (fun i => w i / lam ^ (i.val)), ?_, ?_⟩
  · intro i
    have hcoe : ((WithLp.equiv 2 (Fin l → ℝ)).symm (fun i => w i / lam ^ (i.val))) i
        = w i / lam ^ (i.val) := rfl
    rw [hcoe, abs_div, abs_of_nonneg (pow_nonneg hlam0.le _), div_le_one (pow_pos hlam0 _)]
    exact (hw i).trans (one_le_pow₀ hlam)
  · have hmain : lam • curvePlateLin l D δ t w
        = curvePlateLin l D (lam * δ) t ((WithLp.equiv 2 (Fin l → ℝ)).symm
            (fun i => w i / lam ^ (i.val))) := by
      rw [curvePlateLin_apply, Finset.smul_sum, curvePlateLin_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hcoe : ((WithLp.equiv 2 (Fin l → ℝ)).symm (fun i => w i / lam ^ (i.val))) i
          = w i / lam ^ (i.val) := rfl
      rw [hcoe]
      have hscal : lam * w i * δ ^ (i.val + 1)
          = w i / lam ^ (i.val) * (lam * δ) ^ (i.val + 1) := by
        have h1 : (lam * δ) ^ (i.val + 1) = lam ^ (i.val + 1) * δ ^ (i.val + 1) := mul_pow _ _ _
        rw [h1, pow_succ lam i.val]
        field_simp
      rw [smul_smul, smul_smul, hscal, smul_smul]
    exact hmain.symm

/-- **The image of a `k`-dimensional plate under the projection is contained in the plate of the
projected curve.**  This is GLYZ's "`P(U_J) ⊆ C U_{J,P∘Γ}`" (§3.4), in the quantitative form
needed by the descent: the projection of the `k`-dimensional plate of side lengths `δ¹,…,δ^k`
is contained in the plate of the projected curve at scale `λδ` for the *fixed* factor
`λ = 1 + (k·√k·k! + 1)/c'`, where `c'` is the radius of the ball that the projected curve's
plate is known to contain.

The proof: writing `plate k δ t = {γ(t) + Σ_{i<k} u_i δ^{i+1}Γ^{(i+1)}(t)}` and projecting,
the terms `i < l` already form the projected plate at scale `δ`, while the terms `l ≤ i < k`
form a remainder of norm `≤ k·√k·k!·δ^{l+1}`, which is absorbed into the plate by convexity of
the box and the fact that the plate contains a ball of radius `c'δ^l`. -/
theorem projMapLin_image_plate_subset {k l : ℕ} (hl : 1 ≤ l) (hlk : l ≤ k) {b : Fin l → E k}
    (hb : Orthonormal ℝ b) {t c' : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (hc' : 0 < c')
    (hball : ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      Metric.ball (projCurveDeriv k l b 0 t) (c' * δ ^ l)
        ⊆ curvePlate l (projCurveDeriv k l b) δ t)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    projMapLin k l b '' plate k δ t
      ⊆ curvePlate l (projCurveDeriv k l b)
          ((1 + ((k : ℝ) * (Real.sqrt k * (k.factorial : ℝ)) + 1) / c') * δ) t := by
  set B : ℝ := (k : ℝ) * (Real.sqrt k * (k.factorial : ℝ)) with hB
  have ht1 : |t| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2
  have hK0 : ∀ m : ℕ, ‖projCurveDeriv k l b m t‖ ≤ Real.sqrt k * (k.factorial : ℝ) := fun m =>
    (norm_projMapLin_le k l hb _).trans
      (norm_le_sqrt_card_mul_of_coord_le _ (Nat.cast_nonneg _)
        (fun j => gammaDeriv_coord_abs_le k ht1 m j))
  have hB0 : 0 ≤ B := by
    rw [hB]
    exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg _))
  have hBpos : 0 < B := by
    rw [hB]
    have hk1 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (le_trans hl hlk : 1 ≤ k)
    have hk0 : (0 : ℝ) < Real.sqrt k := Real.sqrt_pos.mpr (by exact_mod_cast (le_trans hl hlk))
    exact mul_pos hk1 (mul_pos hk0 (Nat.cast_pos.mpr (Nat.factorial_pos k)))
  -- the convexity and the ball inside the box
  have hK0conv : Convex ℝ (curvePlateLin l (projCurveDeriv k l b) δ t '' unitBox l) :=
    (convex_unitBox l).linear_image _
  have h0K0 : (0 : E l) ∈ curvePlateLin l (projCurveDeriv k l b) δ t '' unitBox l :=
    ⟨0, fun i => by simp [unitBox], by simp⟩
  have hK0ball : Metric.ball (0 : E l) (c' * δ ^ l)
      ⊆ curvePlateLin l (projCurveDeriv k l b) δ t '' unitBox l := by
    intro z hz
    have hz' : ‖z‖ < c' * δ ^ l := by
      have h := hz
      rw [Metric.mem_ball, dist_eq_norm, sub_zero] at h
      exact h
    have hmem : projCurveDeriv k l b 0 t + z
        ∈ Metric.ball (projCurveDeriv k l b 0 t) (c' * δ ^ l) := by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
      exact hz'
    obtain ⟨y, hy, hyeq⟩ := hball δ hδ0 hδ1 hmem
    refine ⟨y, hy, ?_⟩
    have h2 : projCurveDeriv k l b 0 t + curvePlateLin l (projCurveDeriv k l b) δ t y
        = projCurveDeriv k l b 0 t + z := by simpa using hyeq
    exact add_left_cancel h2
  -- the main argument
  intro x hx
  rw [projMapLin_image_plate_eq] at hx
  obtain ⟨u, hu, rfl⟩ := hx
  change projMapLin k l b (gammaVec k t)
      + ((projMapLin k l b).comp (plateMapLin k δ t)) u
      ∈ curvePlate l (projCurveDeriv k l b)
          ((1 + (B + 1) / c') * δ) t
  rw [comp_plateMapLin_apply]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun i : Fin k => i.val < l)
    (fun i => u i • (δ ^ (i.val + 1) • projCurveDeriv k l b (i.val + 1) t))]
  set w : E l := (WithLp.equiv 2 (Fin l → ℝ)).symm
    (fun j : Fin l => u ⟨j.val, lt_of_lt_of_le j.isLt hlk⟩) with hw
  have hAeq : (∑ i ∈ (Finset.univ.filter fun i : Fin k => i.val < l),
        u i • (δ ^ (i.val + 1) • projCurveDeriv k l b (i.val + 1) t))
      = curvePlateLin l (projCurveDeriv k l b) δ t w := by
    rw [sum_filter_castLE k l hlk
      (fun i => u i • (δ ^ (i.val + 1) • projCurveDeriv k l b (i.val + 1) t))]
    rw [curvePlateLin_apply, hw]
    refine Finset.sum_congr rfl fun j _ => ?_
    rfl
  have hwu : w ∈ unitBox l := by
    intro j
    have hcoe : w j = u ⟨j.val, lt_of_lt_of_le j.isLt hlk⟩ := rfl
    rw [hcoe]
    exact hu _
  rw [hAeq]
  set R : E l := ∑ i ∈ (Finset.univ.filter fun i : Fin k => ¬ i.val < l),
      u i • (δ ^ (i.val + 1) • projCurveDeriv k l b (i.val + 1) t) with hRdef
  have hRbound : ‖R‖ ≤ B * δ ^ (l + 1) := by
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ i ∈ (Finset.univ.filter fun i : Fin k => ¬ i.val < l),
        ‖u i • (δ ^ (i.val + 1) • projCurveDeriv k l b (i.val + 1) t)‖
          ≤ δ ^ (l + 1) * (Real.sqrt k * (k.factorial : ℝ)) := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hi
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (pow_nonneg hδ0.le _)]
      have hu1 : |u i| ≤ 1 := hu i
      have hle : δ ^ (i.val + 1) ≤ δ ^ (l + 1) :=
        pow_le_pow_of_le_one hδ0.le hδ1 (by omega)
      calc |u i| * (δ ^ (i.val + 1) * ‖projCurveDeriv k l b (i.val + 1) t‖)
          ≤ 1 * (δ ^ (l + 1) * (Real.sqrt k * (k.factorial : ℝ))) := by
            refine mul_le_mul hu1 (mul_le_mul hle (hK0 (i.val + 1)) (norm_nonneg _)
              (pow_nonneg hδ0.le _)) (mul_nonneg (pow_nonneg hδ0.le _) (norm_nonneg _))
              zero_le_one
        _ = δ ^ (l + 1) * (Real.sqrt k * (k.factorial : ℝ)) := by ring
    refine (Finset.sum_le_sum hterm).trans ?_
    have hcard : ((Finset.univ.filter fun i : Fin k => ¬ i.val < l)).card ≤ k := by
      calc ((Finset.univ.filter fun i : Fin k => ¬ i.val < l)).card
          ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_le_card (Finset.filter_subset _ _)
        _ = k := Finset.card_univ.trans (Fintype.card_fin k)
    rw [Finset.sum_const, nsmul_eq_mul]
    rw [hB]
    have hX : (0 : ℝ) ≤ δ ^ (l + 1) * (Real.sqrt k * (k.factorial : ℝ)) :=
      mul_nonneg (pow_nonneg hδ0.le _) (mul_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg _))
    calc (((Finset.univ.filter fun i : Fin k => ¬ i.val < l)).card : ℝ)
          * (δ ^ (l + 1) * (Real.sqrt k * (k.factorial : ℝ)))
        ≤ (k : ℝ) * (δ ^ (l + 1) * (Real.sqrt k * (k.factorial : ℝ))) :=
          mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard) hX
      _ = (k : ℝ) * (Real.sqrt k * (k.factorial : ℝ)) * δ ^ (l + 1) := by ring
  -- absorbing the remainder
  set ε : ℝ := (B + 1) * δ / c' with hεdef
  have hεpos : 0 < ε := by
    rw [hεdef]; exact div_pos (mul_pos (by linarith) hδ0) hc'
  have hεbound : ε⁻¹ * (B * δ ^ (l + 1)) = c' * δ ^ l * (B / (B + 1)) := by
    rw [hεdef]; field_simp; ring
  obtain ⟨z₀, hz₀mem, hz₀eq⟩ : ∃ z₀ ∈ curvePlateLin l (projCurveDeriv k l b) δ t '' unitBox l,
      R = ε • z₀ := by
    refine ⟨ε⁻¹ • R, hK0ball ?_, by rw [smul_smul, mul_inv_cancel₀ hεpos.ne', one_smul]⟩
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hεpos)]
    calc ε⁻¹ * ‖R‖ ≤ ε⁻¹ * (B * δ ^ (l + 1)) :=
          mul_le_mul_of_nonneg_left hRbound (by positivity)
      _ = c' * δ ^ l * (B / (B + 1)) := hεbound
      _ < c' * δ ^ l * 1 := by
          refine mul_lt_mul_of_pos_left ?_ (mul_pos hc' (pow_pos hδ0 l))
          rw [div_lt_one (by linarith : (0 : ℝ) < B + 1)]
          linarith
      _ = c' * δ ^ l := by ring
  -- convexity: `y + R ∈ (1 + ε) • K₀`
  have hconv : curvePlateLin l (projCurveDeriv k l b) δ t w + R
      ∈ (1 + ε) • (curvePlateLin l (projCurveDeriv k l b) δ t '' unitBox l) := by
    have h1e : (0 : ℝ) < 1 + ε := by linarith
    have hcombo : (1 / (1 + ε)) • curvePlateLin l (projCurveDeriv k l b) δ t w
        + (ε / (1 + ε)) • z₀
        ∈ curvePlateLin l (projCurveDeriv k l b) δ t '' unitBox l :=
      hK0conv ⟨w, hwu, rfl⟩ hz₀mem (by positivity) (by positivity) (by field_simp)
    refine ⟨_, hcombo, ?_⟩
    change (1 + ε) • ((1 / (1 + ε)) • curvePlateLin l (projCurveDeriv k l b) δ t w
      + (ε / (1 + ε)) • z₀) = curvePlateLin l (projCurveDeriv k l b) δ t w + R
    rw [hz₀eq, smul_add, smul_smul, smul_smul, mul_one_div_cancel h1e.ne', one_smul,
      mul_div_cancel₀ ε h1e.ne']
  have hscale : (1 + ε) • (curvePlateLin l (projCurveDeriv k l b) δ t '' unitBox l)
      ⊆ curvePlateLin l (projCurveDeriv k l b) ((1 + ε) * δ) t '' unitBox l :=
    smul_curvePlateLin_subset _ (by linarith)
  obtain ⟨y', hy', hy'eq⟩ := hscale hconv
  refine curvePlate_mono (δ := (1 + ε) * δ) (mul_nonneg (by linarith) hδ0.le) ?_
    ⟨y', hy', ?_⟩
  · have h1 : (B + 1) * δ ≤ B + 1 := mul_le_of_le_one_right (by linarith) hδ1
    have h2 : (B + 1) * δ / c' ≤ (B + 1) / c' := div_le_div_of_nonneg_right h1 hc'.le
    refine mul_le_mul_of_nonneg_right ?_ hδ0.le
    simpa [hεdef] using h2
  · change projCurveDeriv k l b 0 t + curvePlateLin l (projCurveDeriv k l b) ((1 + ε) * δ) t y'
      = projMapLin k l b (gammaVec k t)
        + (curvePlateLin l (projCurveDeriv k l b) δ t w + R)
    rw [hy'eq, projCurveDeriv_zero]

/-- **The plate inclusion, instantiated for the projected moment curve.**  For `ξ' ∈ [0,1]`,
there is a *fixed* `λ ≥ 1` such that for every plate scale `δ ∈ (0,1]` and every centre
`t ∈ [0,1]` separated from `ξ'` (so that the projected curve has torsion at `t`),

`projMapLin '' plate k δ t ⊆ curvePlate l (projCurveDeriv k l b) (λ δ) t`.

This is the form consumed by the §3.4 reduction: after restricting to `H + z`, a function of
the class `𝒞(plate k δ t)` becomes a function of the class `𝒞(curvePlate l Dproj (λδ) t)`, to
which the `l`-dimensional model theorem may be applied. -/
theorem projMapLin_image_plate_subset' {k l : ℕ} (hl : 1 ≤ l) (hlk : l ≤ k) (ξ' : ℝ)
    (hξ' : ξ' ∈ Set.Icc (0 : ℝ) 1) :
    ∃ lam : ℝ, 1 ≤ lam ∧ ∀ (δ t : ℝ), 0 < δ → δ ≤ 1 → t ∈ Set.Icc (0 : ℝ) 1 →
      1 / 4 ≤ |t - ξ'| →
      projMapLin k l (torsionVec k l hlk ξ') '' plate k δ t
        ⊆ curvePlate l (projCurveDeriv k l (torsionVec k l hlk ξ')) (lam * δ) t := by
  obtain ⟨c, hc, htor⟩ := torsion_projCurveDeriv k l hl hlk ξ' hξ'
  set c' : ℝ := c / ((l : ℝ) * ((l - 1).factorial : ℝ)
    * (Real.sqrt l * (Real.sqrt k * (k.factorial : ℝ))) ^ (2 * l - 1) * Real.sqrt l) with hc'def
  have hfact : (0 : ℝ) < ((l - 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (l - 1)
  have hsqrtl1 : 1 ≤ Real.sqrt l := by
    rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by exact_mod_cast hl)
  have hsqrtlpos : 0 < Real.sqrt l := lt_of_lt_of_le zero_lt_one hsqrtl1
  have hA1 : 1 ≤ Real.sqrt k * (k.factorial : ℝ) := by
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (le_trans hl hlk)
    have h1 : 1 ≤ Real.sqrt k := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hk1
    have h2 : 1 ≤ (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ Real.sqrt k * (k.factorial : ℝ) := mul_le_mul h1 h2 zero_le_one (by positivity)
  have hKpos : 0 < (l : ℝ) * ((l - 1).factorial : ℝ)
      * (Real.sqrt l * (Real.sqrt k * (k.factorial : ℝ))) ^ (2 * l - 1) * Real.sqrt l := by
    refine mul_pos (mul_pos (mul_pos ?_ hfact) ?_) hsqrtlpos
    · exact_mod_cast hl
    · have hA2 : 1 ≤ Real.sqrt l * (Real.sqrt k * (k.factorial : ℝ)) := by
        calc (1 : ℝ) = 1 * 1 := by ring
          _ ≤ Real.sqrt l * (Real.sqrt k * (k.factorial : ℝ)) :=
              mul_le_mul hsqrtl1 hA1 zero_le_one (Real.sqrt_nonneg l)
      exact pow_pos (lt_of_lt_of_le zero_lt_one hA2) _
  have hc'pos : 0 < c' := by rw [hc'def]; exact div_pos hc hKpos
  refine ⟨1 + ((k : ℝ) * (Real.sqrt k * (k.factorial : ℝ)) + 1) / c', by
    have h0 : (0 : ℝ) ≤ ((k : ℝ) * (Real.sqrt k * (k.factorial : ℝ)) + 1) / c' :=
      div_nonneg (by positivity) hc'pos.le
    linarith, ?_⟩
  intro δ t hδ0 hδ1 ht hsep
  have hbd : ∀ i : ℕ, i ≤ l + 1 → ∀ j : Fin l,
      |projCurveDeriv k l (torsionVec k l hlk ξ') i t j| ≤ Real.sqrt k * (k.factorial : ℝ) :=
    fun i hi j => CurveBounded_projCurveDeriv k l hlk (orthonormal_torsionVec k l hlk ξ') i hi t ht j
  have hball := ball_subset_curvePlate_of_bounded_torsion_at (D := projCurveDeriv k l
      (torsionVec k l hlk ξ')) (A := Real.sqrt k * (k.factorial : ℝ)) (c := c) (t := t)
    hl hc hA1 hbd (htor t ht hsep)
  have hsub := projMapLin_image_plate_subset hl hlk (orthonormal_torsionVec k l hlk ξ')
    ht hc'pos hball hδ0 hδ1
  exact hsub.trans (curvePlate_mono
    (δ := (1 + ((k : ℝ) * (Real.sqrt k * (k.factorial : ℝ)) + 1) / c') * δ)
    (mul_nonneg (by
      have h0 : (0 : ℝ) ≤ ((k : ℝ) * (Real.sqrt k * (k.factorial : ℝ)) + 1) / c' :=
        div_nonneg (by positivity) hc'pos.le
      linarith) hδ0.le) le_rfl)

/-! ## 5b. The moment curve satisfies the curve hypotheses (needed to instantiate the descent) -/

/-- The Gram matrix of the moment curve's derivative vectors equals the explicit Euclidean Gram
matrix of the `gam`-normalisation. -/
lemma gram_gammaDeriv_eq (k : ℕ) (t : ℝ) :
    Matrix.gram ℝ (fun i : Fin k => gammaDeriv k (i.val + 1) t)
      = fun i j : Fin k => ∑ l : Fin k,
          Commons.Analysis.MomentCurve.gam k t (i.val + 1) l
            * Commons.Analysis.MomentCurve.gam k t (j.val + 1) l := by
  ext i j
  rw [Matrix.gram_apply, gammaDeriv_eq_lpSymm_gam, gammaDeriv_eq_lpSymm_gam]
  simp only [PiLp.inner_apply, RCLike.inner_apply', starRingEnd_apply, star_trivial]
  apply Finset.sum_congr rfl
  intro x _
  rfl

/-- **The moment curve has (quantitative) torsion**: the Gram determinant of
`γ^{(1)}(t),…,γ^{(k)}(t)` is bounded below by a positive constant on `[0,1]`. -/
lemma CurveTorsion_gammaDeriv (k : ℕ) (hk : 1 ≤ k) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ CurveTorsion k (gammaDeriv k) c₀ := by
  obtain ⟨c, hc, h⟩ := Commons.Analysis.MomentCurve.gam_gram_det_lower k hk
  refine ⟨c, hc, fun t ht => ?_⟩
  rw [gram_gammaDeriv_eq]
  exact h t ht

/-- **The moment curve satisfies the Taylor-remainder hypothesis** with an explicit constant,
transported from `Commons.Analysis.MomentCurve.gammaDeriv_taylor_tail` through the linear
equivalence `WithLp.linearEquiv` (whose norm is at most `√k`). -/
lemma CurveTaylor_gammaDeriv (k : ℕ) :
    ∃ R : ℝ, 0 ≤ R ∧ CurveTaylor k (gammaDeriv k) R := by
  obtain ⟨C, hC, htail⟩ := Commons.Analysis.MomentCurve.gammaDeriv_taylor_tail k
  refine ⟨Real.sqrt k * C, by positivity, ?_⟩
  intro i m t u hi hm ht hu
  have ht1 : |t| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2
  have h := htail i m t u hi hm ht1 hu
  have hkey : gammaDeriv k i (t + u) - ∑ j ∈ Finset.Icc i m,
        (u ^ (j - i) / ((j - i).factorial : ℝ)) • gammaDeriv k j t
      = (WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).symm
          (Commons.Analysis.MomentCurve.gam k (t + u) i - ∑ j ∈ Finset.Icc i m,
            (u ^ (j - i) / ((j - i).factorial : ℝ))
              • Commons.Analysis.MomentCurve.gam k t j) := by
    rw [map_sub, map_sum]
    refine congrArg₂ (· - ·) ?_ ?_
    · exact gammaDeriv_eq_lpSymm_gam k i (t + u)
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, gammaDeriv_eq_lpSymm_gam]
  rw [hkey]
  calc ‖(WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).symm
        (Commons.Analysis.MomentCurve.gam k (t + u) i - ∑ j ∈ Finset.Icc i m,
          (u ^ (j - i) / ((j - i).factorial : ℝ))
            • Commons.Analysis.MomentCurve.gam k t j)‖
      ≤ Real.sqrt k * ‖Commons.Analysis.MomentCurve.gam k (t + u) i - ∑ j ∈ Finset.Icc i m,
          (u ^ (j - i) / ((j - i).factorial : ℝ))
            • Commons.Analysis.MomentCurve.gam k t j‖ := norm_lpSymm_le k _
    _ ≤ Real.sqrt k * (C * |u| ^ (m + 1 - i)) :=
        mul_le_mul_of_nonneg_left h (Real.sqrt_nonneg k)
    _ = Real.sqrt k * C * |u| ^ (m + 1 - i) := by ring
