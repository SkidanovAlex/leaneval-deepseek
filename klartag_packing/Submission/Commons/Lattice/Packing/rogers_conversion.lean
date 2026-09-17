import Mathlib.Algebra.Module.ZLattice.Covolume
import Submission.Commons.LinearAlgebra.Matrix.det_le_prod_diag_of_posSemidef
import Submission.Commons.Lattice.Discrete.discreteTopology_of_linearImage

/-!
# Rogers' conversion: from a bound on `∑ log(1/‖x‖)` to a lattice of minimum `≥ 1`

Given a lattice `L ⊆ ℝ^d` and a real number `E` with
`∑_{x ∈ L, x ≠ 0} max 0 (log (1/‖x‖)) ≤ E`, there is a lattice `Λ` all of whose nonzero
vectors have norm at least `1`, with `covolume Λ ≤ exp E · covolume L`.

The construction is explicit:  let `S` be the (finite) set of nonzero vectors of `L` of norm
`< 1` and let
`q = 1 + ∑_{x ∈ S} c_x · (x ⊗ x)`,  `c_x = (1 - ‖x‖²)/‖x‖⁴`.
Then `q` is positive definite with `q(v) ≥ 1` for every `v ∈ L \ {0}`, and
`det q ≤ ∏_{x ∈ S} (1 + c_x ‖x‖²) = ∏_{x ∈ S} ‖x‖^{-2} ≤ exp (2E)`.
Finally `Λ := √q (L)`, where `√q` is the positive-definite square root of `q`, satisfies
`min Λ ≥ 1` and `covolume Λ = √(det q) · covolume L ≤ exp E · covolume L`.
-/

open MeasureTheory Module
open scoped BigOperators RealInnerProductSpace Matrix
open InnerProductSpace

namespace Commons.Lattice.Packing

noncomputable section

/-! ### A determinant inequality for sums of rank-one positive matrices -/

/-- Hadamard's inequality for positive semi-definite matrices, for an arbitrary finite index
type. -/
lemma det_le_prod_diag_of_posSemidef' {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix m m ℝ} (hA : A.PosSemidef) : A.det ≤ ∏ i, A i i := by
  classical
  let e := Fintype.equivFin m
  have hA' : (Matrix.reindex e e A).PosSemidef := by
    rw [Matrix.reindex_apply]
    exact hA.submatrix e.symm
  have hmain := Commons.LinearAlgebra.Matrix.det_le_prod_diag_of_posSemidef
    (Matrix.reindex e e A) hA'
  rw [Matrix.det_reindex_self e A] at hmain
  refine hmain.trans (le_of_eq ?_)
  exact Fintype.prod_equiv e.symm _ _ (fun i => by rw [Matrix.reindex_apply]; rfl)

private lemma term1 {a b s t : ℝ} (hs : s * s = a) : a * (b * t) = b * s * (t * s) := by
  rw [← hs]; ring

private lemma term2 {a b s : ℝ} (hs : s * s = a) : b * s * (b * s) = a * b ^ 2 := by
  rw [show b * s * (b * s) = (s * s) * b ^ 2 by ring, hs]

/-- For a real matrix `U : Fin d → m → ℝ` and nonnegative weights `c`,
`det (1 + ∑ i, c i • (U · i) ⊗ (U · i)) ≤ ∏ i, (1 + c i * ∑ k, (U k i)²)`.

This is the Weinstein–Aronszajn identity followed by Hadamard's inequality. -/
lemma det_one_add_sum_vecMulVec_le {d : ℕ} {m : Type*} [Fintype m] [DecidableEq m]
    (U : Fin d → m → ℝ) (c : m → ℝ) (hc : ∀ i, 0 ≤ c i) :
    (1 + ∑ i, c i • Matrix.vecMulVec (fun k => U k i) (fun k => U k i)).det
      ≤ ∏ i, (1 + c i * ∑ k, U k i ^ 2) := by
  classical
  set R : Matrix (Fin d) m ℝ := Matrix.of U * Matrix.diagonal (fun i => Real.sqrt (c i)) with hR
  have hRk : ∀ k i, R k i = U k i * Real.sqrt (c i) := by
    intro k i
    simp [hR, Matrix.mul_diagonal]
  have hW : (1 + ∑ i, c i • Matrix.vecMulVec (fun k => U k i) (fun k => U k i)) = 1 + R * Rᵀ := by
    ext k l
    rw [Matrix.add_apply, Matrix.add_apply, Matrix.sum_apply, Matrix.mul_apply]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [Matrix.transpose_apply]
    simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, hRk, smul_eq_mul]
    exact term1 (Real.mul_self_sqrt (hc i))
  rw [hW]
  have hpsd : (1 + Rᵀ * R).PosSemidef := by
    have h1 : (1 : Matrix m m ℝ).PosSemidef := Matrix.PosSemidef.one
    have h2 : (Rᵀ * R).PosSemidef := by
      have := Matrix.posSemidef_conjTranspose_mul_self R
      simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using this
    exact h1.add h2
  calc (1 + R * Rᵀ).det = (1 + Rᵀ * R).det := Matrix.det_one_add_mul_comm R Rᵀ
    _ ≤ ∏ i, (1 + Rᵀ * R : Matrix m m ℝ) i i := det_le_prod_diag_of_posSemidef' hpsd
    _ = ∏ i, (1 + c i * ∑ k, U k i ^ 2) := by
        apply Finset.prod_congr rfl
        intro i _
        have hdiag : (1 + Rᵀ * R : Matrix m m ℝ) i i = 1 + ∑ k, c i * U k i ^ 2 := by
          rw [Matrix.add_apply, Matrix.mul_apply, Matrix.one_apply, if_pos rfl]
          congr 1
          apply Finset.sum_congr rfl
          intro k _
          rw [Matrix.transpose_apply]
          simp only [hRk]
          exact term2 (Real.mul_self_sqrt (hc i))
        rw [hdiag, Finset.mul_sum]

/-- The matrix in an orthonormal basis of a self-adjoint rank-one operator `u ⊗ u`. -/
lemma toMatrix_rankOne_self {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E) (u : E) :
    (LinearMap.toMatrix b.toBasis b.toBasis) ((InnerProductSpace.rankOne ℝ u u).toLinearMap)
      = Matrix.vecMulVec (fun k => ⟪b k, u⟫_ℝ) (fun k => ⟪b k, u⟫_ℝ) := by
  have h := InnerProductSpace.toMatrix_rankOne (𝕜 := ℝ) u u b.toBasis b
  simp only [star_trivial] at h
  rw [h]
  have h1 : (⇑(b.toBasis.repr u) : Fin (Module.finrank ℝ E) → ℝ) = fun k => ⟪b k, u⟫_ℝ := by
    ext k
    rw [show (b.toBasis.repr u) k = (b.repr u).ofLp k from rfl]
    rw [OrthonormalBasis.repr_apply_apply]
  have h2 : (b.repr u).ofLp = fun k => ⟪b k, u⟫_ℝ := by
    ext k; rw [OrthonormalBasis.repr_apply_apply]
  rw [h1, h2]

/-- The determinant of `1 + ∑ i, c i • (u i ⊗ u i)` is at most
`∏ i, (1 + c i * ‖u i‖²)` for nonnegative weights `c`. -/
lemma det_one_add_sum_rankOne_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι]
    (u : ι → E) (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i) :
    LinearMap.det (1 + ∑ i, c i • (InnerProductSpace.rankOne ℝ (u i) (u i)).toLinearMap)
      ≤ ∏ i, (1 + c i * ‖u i‖ ^ 2) := by
  classical
  let b := stdOrthonormalBasis ℝ E
  have hrank : ∀ i, (LinearMap.toMatrix b.toBasis b.toBasis)
      ((InnerProductSpace.rankOne ℝ (u i) (u i)).toLinearMap)
      = Matrix.vecMulVec (fun k => ⟪b k, u i⟫_ℝ) (fun k => ⟪b k, u i⟫_ℝ) :=
    fun i => toMatrix_rankOne_self b (u i)
  have hmat : (LinearMap.toMatrix b.toBasis b.toBasis)
      (1 + ∑ i, c i • (InnerProductSpace.rankOne ℝ (u i) (u i)).toLinearMap)
      = 1 + ∑ i, c i • Matrix.vecMulVec (fun k => ⟪b k, u i⟫_ℝ) (fun k => ⟪b k, u i⟫_ℝ) := by
    rw [map_add, map_sum]
    congr 1
    · rw [LinearMap.toMatrix_one]
    · apply Finset.sum_congr rfl
      intro i _
      rw [map_smul, hrank i]
  rw [← LinearMap.det_toMatrix b.toBasis, hmat]
  refine (det_one_add_sum_vecMulVec_le (fun k i => ⟪b k, u i⟫_ℝ) c hc).trans (le_of_eq ?_)
  apply Finset.prod_congr rfl
  intro i _
  have hsum : ∑ k, ⟪b k, u i⟫_ℝ ^ 2 = ‖u i‖ ^ 2 := by
    have h2 : ∑ k, ⟪u i, b k⟫_ℝ * ⟪b k, u i⟫_ℝ = ⟪u i, u i⟫_ℝ :=
      OrthonormalBasis.sum_inner_mul_inner b (u i) (u i)
    have h3 : ‖u i‖ ^ 2 = ⟪u i, u i⟫_ℝ := (inner_self_eq_norm_sq_to_K (u i)).symm
    rw [h3, ← h2]
    apply Finset.sum_congr rfl
    intro k _
    rw [sq, real_inner_comm (u i) (b k)]
  rw [hsum]

/-! ### Square roots of positive definite self-adjoint operators -/

lemma rankOneL_isSymmetric {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (u : E) :
    ((InnerProductSpace.rankOne ℝ u u).toLinearMap).IsSymmetric := by
  intro x y
  rw [show ((InnerProductSpace.rankOne ℝ u u).toLinearMap) x
      = (InnerProductSpace.rankOne ℝ u u) x from rfl,
    show ((InnerProductSpace.rankOne ℝ u u).toLinearMap) y
      = (InnerProductSpace.rankOne ℝ u u) y from rfl,
    InnerProductSpace.rankOne_apply, InnerProductSpace.rankOne_apply,
    inner_smul_left, inner_smul_right, starRingEnd_apply, star_trivial, real_inner_comm u x]
  ring

/-- **Square root of a positive definite self-adjoint operator.**  For a self-adjoint
`q : E →ₗ[ℝ] E` with `⟪q v, v⟫ > 0` for all `v ≠ 0` there is a self-adjoint `T` with
`T ∘ T = q` and `det T = √(det q)`. -/
lemma exists_sqrt_isSymmetric {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (q : E →ₗ[ℝ] E) (hq : q.IsSymmetric)
    (hpos : ∀ v : E, v ≠ 0 → 0 < ⟪q v, v⟫_ℝ) :
    ∃ T : E →ₗ[ℝ] E, T.IsSymmetric ∧ T ∘ₗ T = q ∧
      LinearMap.det T = Real.sqrt (LinearMap.det q) := by
  classical
  let b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E := hq.eigenvectorBasis rfl
  let ν : Fin (Module.finrank ℝ E) → ℝ := hq.eigenvalues rfl
  have hbii : ∀ i, ⟪b i, b i⟫_ℝ = 1 := fun i => by
    rw [(orthonormal_iff_ite.mp b.orthonormal) i i]; simp
  have hbq : ∀ i, q (b i) = ν i • b i := fun i => hq.apply_eigenvectorBasis rfl i
  have hbne : ∀ i, b i ≠ 0 := by
    intro i h
    have := hbii i
    rw [h, inner_zero_left] at this
    norm_num at this
  have hνpos : ∀ i, 0 < ν i := by
    intro i
    have h1 : ⟪q (b i), b i⟫_ℝ = ν i := by
      rw [hbq i, inner_smul_left, hbii i, mul_one]
      simp
    rw [← h1]
    exact hpos (b i) (hbne i)
  let T : E →ₗ[ℝ] E := ∑ i, Real.sqrt (ν i) • (InnerProductSpace.rankOne ℝ (b i) (b i)).toLinearMap
  have hTb : ∀ i, T (b i) = Real.sqrt (ν i) • b i := by
    intro i
    show (∑ j, Real.sqrt (ν j) • (InnerProductSpace.rankOne ℝ (b j) (b j)).toLinearMap) (b i) = _
    rw [LinearMap.sum_apply, Finset.sum_eq_single i]
    · rw [LinearMap.smul_apply]
      change Real.sqrt (ν i) • (InnerProductSpace.rankOne ℝ (b i) (b i)) (b i) = _
      rw [InnerProductSpace.rankOne_apply, hbii i]
      simp
    · intro j _ hj
      rw [LinearMap.smul_apply]
      change Real.sqrt (ν j) • (InnerProductSpace.rankOne ℝ (b j) (b j)) (b i) = 0
      rw [InnerProductSpace.rankOne_apply, (orthonormal_iff_ite.mp b.orthonormal) j i, if_neg hj,
        zero_smul, smul_zero]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  have hTsym : T.IsSymmetric := by
    refine Finset.sum_induction _ _ (fun a b ha hb => ha.add hb) LinearMap.IsSymmetric.zero ?_
    intro i _
    exact LinearMap.IsSymmetric.smul (by simp) (rankOneL_isSymmetric (b i))
  have hTT : T ∘ₗ T = q := by
    refine Module.Basis.ext b.toBasis (fun i => ?_)
    show T (T ((b.toBasis) i)) = q ((b.toBasis) i)
    rw [show (b.toBasis) i = b i from rfl, hTb i, map_smul, hTb i, smul_smul,
      Real.mul_self_sqrt (le_of_lt (hνpos i)), hbq i]
  have hbcoef : ∀ j, (b.toBasis).repr (b j) = Finsupp.single j (1 : ℝ) := by
    intro j
    have h := Module.Basis.repr_self b.toBasis j
    simpa using h
  have hmat : (b.toBasis).toMatrix (T ∘ ⇑b.toBasis) = Matrix.diagonal (fun i => Real.sqrt (ν i)) := by
    ext i j
    rw [Module.Basis.toMatrix_apply, Function.comp_apply,
      show (b.toBasis) j = b j from congrFun (OrthonormalBasis.coe_toBasis b) j, hTb j, map_smul,
      hbcoef j, Finsupp.smul_single]
    simp only [Matrix.diagonal_apply, Finsupp.single_apply, smul_eq_mul, mul_one]
    by_cases h : i = j
    · subst h; simp
    · rw [if_neg h, if_neg (Ne.symm h)]
  have hdetT : LinearMap.det T = ∏ i, Real.sqrt (ν i) := by
    rw [show LinearMap.det T = (b.toBasis).det (T ∘ ⇑b.toBasis) from ?_, Module.Basis.det_apply,
      hmat, Matrix.det_diagonal]
    rw [Module.Basis.det_comp, Module.Basis.det_self, mul_one]
  have hdetq : LinearMap.det q = ∏ i, ν i := by
    have h := hq.det_eq_prod_eigenvalues (rfl : Module.finrank ℝ E = Module.finrank ℝ E)
    simpa [ν] using h
  refine ⟨T, hTsym, hTT, ?_⟩
  rw [hdetT, hdetq, ← Real.sqrt_prod (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
    (fun i _ => le_of_lt (hνpos i))]

/-! ### Covolume of the image under an injective linear map -/

/-- The covolume of the image of a lattice under an injective linear endomorphism is
`|det|` times the covolume. -/
lemma covolume_map_linear {d : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin d)))
    [DiscreteTopology L] [IsZLattice ℝ L]
    (T : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) (hT : Function.Injective T)
    [DiscreteTopology (Submodule.map (T.restrictScalars ℤ) L)]
    [IsZLattice ℝ (Submodule.map (T.restrictScalars ℤ) L)] :
    ZLattice.covolume (Submodule.map (T.restrictScalars ℤ) L)
      = |LinearMap.det T| * ZLattice.covolume L := by
  classical
  have hfin : Module.finrank ℤ L = d := by
    rw [ZLattice.rank ℝ L, finrank_euclideanSpace_fin]
  let b : Basis (Fin d) ℤ L := (Free.chooseBasis ℤ L).reindex
    (Fintype.equivOfCardEq (by rw [Fintype.card_fin, ← Module.finrank_eq_card_chooseBasisIndex, hfin]))
  let b₀ : Basis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)) := b.ofZLatticeBasis ℝ L
  let Tℤ : EuclideanSpace ℝ (Fin d) →ₗ[ℤ] EuclideanSpace ℝ (Fin d) := T.restrictScalars ℤ
  let e : L ≃ₗ[ℤ] (Submodule.map Tℤ L) := Submodule.equivMapOfInjective Tℤ hT L
  let b' : Basis (Fin d) ℤ (Submodule.map Tℤ L) := b.map e
  have hcoe : ∀ i, ((b' i : Submodule.map Tℤ L) : EuclideanSpace ℝ (Fin d)) = T (b i) := by
    intro i
    rw [show ((b' i : Submodule.map Tℤ L) : EuclideanSpace ℝ (Fin d)) = e (b i) from rfl]
    rw [show ((e (b i) : Submodule.map Tℤ L) : EuclideanSpace ℝ (Fin d)) = Tℤ (b i : L) from rfl]
    rfl
  have hcomp : (Subtype.val ∘ ⇑b') = T ∘ (Subtype.val ∘ ⇑b) := by
    funext i; exact hcoe i
  have h1 := ZLattice.covolume_eq_det_mul_measureReal (Submodule.map Tℤ L) volume b' b₀
  have h2 := ZLattice.covolume_eq_det_mul_measureReal L volume b b₀
  rw [hcomp] at h1
  rw [Module.Basis.det_comp b₀ T (Subtype.val ∘ ⇑b), abs_mul, mul_assoc] at h1
  rw [h1, ← h2]


/-- **Rogers' conversion.**  If the sum of `max 0 (log (1/‖x‖))` over the nonzero vectors of
a lattice `L ⊆ ℝ^d` is at most `E`, then there is a lattice `Λ` with minimum `≥ 1` and
`covolume Λ ≤ exp E · covolume L`. -/
theorem rogers_conversion {d : ℕ} (hd : 0 < d)
    (L : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology L] [IsZLattice ℝ L]
    {E : ℝ}
    (hE : (∑' x : L, max 0 (Real.log (1 / ‖(x : EuclideanSpace ℝ (Fin d))‖))) ≤ E) :
    ∃ (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))) (_ : DiscreteTopology Λ) (_ : IsZLattice ℝ Λ),
      (∀ v : Λ, v ≠ 0 → 1 ≤ ‖(v : EuclideanSpace ℝ (Fin d))‖) ∧
      ZLattice.covolume Λ ≤ Real.exp E * ZLattice.covolume L := by
  classical
  -- ## Step 1: the nonzero vectors of `L` of norm `< 1` form a finite set
  have hclosed : IsClosed ((L : Set (EuclideanSpace ℝ (Fin d)))) := by
    simpa using (AddSubgroup.isClosed_of_discreteTopology (U := L.toAddSubgroup))
  have hfin : ((Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) ∩
      (L : Set (EuclideanSpace ℝ (Fin d)))).Finite :=
    Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete Metric.isBounded_ball hclosed
  let S : Set L := {x | x ≠ 0 ∧ ‖(x : EuclideanSpace ℝ (Fin d))‖ < 1}
  have hSfin : S.Finite := by
    refine Set.Finite.of_injOn (s := S)
      (t := (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) ∩ (L : Set (EuclideanSpace ℝ (Fin d))))
      (f := (Subtype.val : L → EuclideanSpace ℝ (Fin d))) ?_ ?_ hfin
    · intro x hx
      exact ⟨by simpa [Metric.mem_ball] using hx.2, x.2⟩
    · exact Subtype.val_injective.injOn
  haveI : Fintype S := hSfin.fintype
  -- ## Step 2: the hypothesis is a bound for the sum over `S`
  let f : L → ℝ := fun x => max 0 (Real.log (1 / ‖(x : EuclideanSpace ℝ (Fin d))‖))
  have hf_zero : ∀ x : L, x ∉ S → f x = 0 := by
    intro x hx
    have hx' : x = 0 ∨ 1 ≤ ‖(x : EuclideanSpace ℝ (Fin d))‖ := by
      by_contra h
      push Not at h
      exact hx ⟨h.1, h.2⟩
    rcases hx' with rfl | hx1
    · show max 0 (Real.log (1 / ‖((0 : L) : EuclideanSpace ℝ (Fin d))‖)) = 0
      simp
    · have hpos : 0 < ‖(x : EuclideanSpace ℝ (Fin d))‖ := lt_of_lt_of_le zero_lt_one hx1
      have hle : 1 / ‖(x : EuclideanSpace ℝ (Fin d))‖ ≤ 1 := by
        rw [div_le_one hpos]; exact hx1
      show max 0 (Real.log (1 / ‖(x : EuclideanSpace ℝ (Fin d))‖)) = 0
      rw [max_eq_left (Real.log_nonpos (by positivity) hle)]
  have htsum : (∑' x : L, f x) = ∑ x : S, f x := by
    have hind : S.indicator f = f := by
      funext x
      by_cases hx : x ∈ S
      · rw [Set.indicator_of_mem hx]
      · rw [Set.indicator_of_notMem hx, hf_zero x hx]
    conv_lhs => rw [← hind]
    rw [← tsum_subtype S f]
    exact tsum_fintype (fun x : S => f x)
  have hsum_le : (∑ x : S, Real.log (1 / ‖((x : L) : EuclideanSpace ℝ (Fin d))‖)) ≤ E := by
    have hmax : ∀ x : S, f x = Real.log (1 / ‖((x : L) : EuclideanSpace ℝ (Fin d))‖) := by
      intro x
      have hlt : ‖((x : L) : EuclideanSpace ℝ (Fin d))‖ < 1 := x.2.2
      have hpos : 0 < ‖((x : L) : EuclideanSpace ℝ (Fin d))‖ := by
        rw [norm_pos_iff]
        intro h
        exact x.2.1 (Subtype.ext h)
      have h1 : 1 < 1 / ‖((x : L) : EuclideanSpace ℝ (Fin d))‖ := one_lt_one_div hpos hlt
      exact max_eq_right (le_of_lt (Real.log_pos h1))
    calc (∑ x : S, Real.log (1 / ‖((x : L) : EuclideanSpace ℝ (Fin d))‖))
        = ∑ x : S, f x := by
          apply Finset.sum_congr rfl
          intro x _
          rw [hmax x]
      _ = ∑' x : L, f x := htsum.symm
      _ ≤ E := hE
  -- ## Step 3: the quadratic form `q = 1 + ∑ c_x (x ⊗ x)`
  let u : S → EuclideanSpace ℝ (Fin d) := fun x => ((x : L) : EuclideanSpace ℝ (Fin d))
  let c : S → ℝ := fun x => (1 - ‖u x‖ ^ 2) / ‖u x‖ ^ 4
  have hu_pos : ∀ x : S, 0 < ‖u x‖ := by
    intro x
    rw [show u x = ((x : L) : EuclideanSpace ℝ (Fin d)) from rfl, norm_pos_iff]
    intro h
    exact x.2.1 (Subtype.ext h)
  have hu_lt : ∀ x : S, ‖u x‖ < 1 := fun x => x.2.2
  have hc_nonneg : ∀ x : S, 0 ≤ c x := by
    intro x
    have h1 : 0 ≤ 1 - ‖u x‖ ^ 2 := by nlinarith [norm_nonneg (u x), hu_lt x]
    have h2 : 0 ≤ ‖u x‖ ^ 4 := by positivity
    simp only [c]
    positivity
  have hcy : ∀ x : S, 1 + c x * ‖u x‖ ^ 2 = 1 / ‖u x‖ ^ 2 := by
    intro x
    have hne : ‖u x‖ ≠ 0 := ne_of_gt (hu_pos x)
    simp only [c]
    field_simp
    ring
  let A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d) :=
    ∑ x : S, c x • (InnerProductSpace.rankOne ℝ (u x) (u x)).toLinearMap
  let q : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d) := 1 + A
  have hA_sym : A.IsSymmetric := by
    refine Finset.sum_induction _ _ (fun a b ha hb => ha.add hb) LinearMap.IsSymmetric.zero ?_
    intro x _
    exact LinearMap.IsSymmetric.smul (by simp) (rankOneL_isSymmetric (u x))
  have hq_sym : q.IsSymmetric := LinearMap.IsSymmetric.one.add hA_sym
  have hAquad : ∀ w : EuclideanSpace ℝ (Fin d),
      ⟪A w, w⟫_ℝ = ∑ x : S, c x * ⟪u x, w⟫_ℝ ^ 2 := by
    intro w
    show ⟪(∑ x : S, c x • (InnerProductSpace.rankOne ℝ (u x) (u x)).toLinearMap) w, w⟫_ℝ = _
    rw [LinearMap.sum_apply, sum_inner]
    apply Finset.sum_congr rfl
    intro x _
    rw [LinearMap.smul_apply, inner_smul_left, starRingEnd_apply, star_trivial]
    rw [show ((InnerProductSpace.rankOne ℝ (u x) (u x)).toLinearMap) w
        = ⟪u x, w⟫_ℝ • u x from InnerProductSpace.rankOne_apply (u x) (u x) w]
    rw [inner_smul_left, starRingEnd_apply, star_trivial, sq]
  have hqquad : ∀ w : EuclideanSpace ℝ (Fin d),
      ⟪q w, w⟫_ℝ = ‖w‖ ^ 2 + ∑ x : S, c x * ⟪u x, w⟫_ℝ ^ 2 := by
    intro w
    rw [show q w = w + A w from by simp [q], inner_add_left, hAquad w,
      inner_self_eq_norm_sq_to_K]
    simp
  have hq_pos : ∀ w : EuclideanSpace ℝ (Fin d), w ≠ 0 → 0 < ⟪q w, w⟫_ℝ := by
    intro w hw
    rw [hqquad w]
    have hnn : 0 ≤ ∑ x : S, c x * ⟪u x, w⟫_ℝ ^ 2 :=
      Finset.sum_nonneg (fun x _ => mul_nonneg (hc_nonneg x) (sq_nonneg _))
    have hw2 : 0 < ‖w‖ ^ 2 := by positivity
    linarith
  -- ## Step 4: the determinant bound
  have hdetq : LinearMap.det q ≤ Real.exp (2 * E) := by
    have h1 := det_one_add_sum_rankOne_le (E := EuclideanSpace ℝ (Fin d)) u c hc_nonneg
    have hqeq : q = 1 + ∑ x : S, c x • (InnerProductSpace.rankOne ℝ (u x) (u x)).toLinearMap :=
      rfl
    rw [hqeq]
    refine h1.trans ?_
    have hprod : (∏ x : S, (1 + c x * ‖u x‖ ^ 2)) = ∏ x : S, (1 / ‖u x‖ ^ 2) := by
      apply Finset.prod_congr rfl
      intro x _
      rw [hcy x]
    rw [hprod]
    have hexp : ∀ x : S, 1 / ‖u x‖ ^ 2 = Real.exp (2 * Real.log (1 / ‖u x‖)) := by
      intro x
      have hpos : (0 : ℝ) < 1 / ‖u x‖ := one_div_pos.mpr (hu_pos x)
      rw [show (2 : ℝ) * Real.log (1 / ‖u x‖)
        = Real.log (1 / ‖u x‖) + Real.log (1 / ‖u x‖) by ring, Real.exp_add, Real.exp_log hpos]
      ring
    rw [Finset.prod_congr rfl (fun x _ => hexp x), ← Real.exp_sum]
    apply Real.exp_le_exp.mpr
    have h2 : (∑ x : S, 2 * Real.log (1 / ‖u x‖)) = 2 * ∑ x : S, Real.log (1 / ‖u x‖) := by
      rw [Finset.mul_sum]
    rw [h2]
    have h3 : (∑ x : S, Real.log (1 / ‖u x‖)) ≤ E := hsum_le
    linarith
  -- ## Step 5: the square root `T` of `q`
  obtain ⟨T, hTsym, hTT, hTdet⟩ := exists_sqrt_isSymmetric q hq_sym hq_pos
  have hdetT_abs : |LinearMap.det T| ≤ Real.exp E := by
    rw [hTdet, abs_of_nonneg (Real.sqrt_nonneg _)]
    calc Real.sqrt (LinearMap.det q) ≤ Real.sqrt (Real.exp (2 * E)) := Real.sqrt_le_sqrt hdetq
      _ = Real.exp E := by
          rw [show Real.exp (2 * E) = Real.exp E * Real.exp E by
            rw [← Real.exp_add]; ring_nf]
          rw [Real.sqrt_mul_self (le_of_lt (Real.exp_pos E))]
  have hTinj : Function.Injective T := by
    intro x y hxy
    have hz : T (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have hz' : x - y = 0 := by
      by_contra hne
      have hpos := hq_pos (x - y) hne
      rw [← hTT, LinearMap.comp_apply, hz, map_zero, inner_zero_left] at hpos
      exact lt_irrefl 0 hpos
    exact sub_eq_zero.mp hz'
  -- ## Step 6: the lattice `Λ = T(L)`
  let Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d)) := Submodule.map (T.restrictScalars ℤ) L
  haveI hΛdisc : DiscreteTopology Λ :=
    Commons.Lattice.Discrete.discreteTopology_of_linearImage T hTinj L
  haveI hΛZL : IsZLattice ℝ Λ := by
    refine ⟨?_⟩
    have hset : (Λ : Set (EuclideanSpace ℝ (Fin d))) =
        T '' (L : Set (EuclideanSpace ℝ (Fin d))) := by
      ext y
      simp only [Λ, Set.mem_image]
      constructor
      · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
      · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
    rw [hset, ← Submodule.map_span, IsZLattice.span_top, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr
      ((LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hTinj)
  have hmin : ∀ v : Λ, v ≠ 0 → 1 ≤ ‖(v : EuclideanSpace ℝ (Fin d))‖ := by
    intro v hv
    obtain ⟨w, hwL, hwv⟩ := Submodule.mem_map.mp v.2
    have hw0 : w ≠ 0 := by
      intro h
      rw [h, map_zero] at hwv
      exact hv (Subtype.ext hwv.symm)
    have hwV : (T w : EuclideanSpace ℝ (Fin d)) = (v : EuclideanSpace ℝ (Fin d)) := hwv
    have hqe : 1 ≤ ⟪q w, w⟫_ℝ := by
      rw [hqquad w]
      have hnn : 0 ≤ ∑ x : S, c x * ⟪u x, w⟫_ℝ ^ 2 :=
        Finset.sum_nonneg (fun x _ => mul_nonneg (hc_nonneg x) (sq_nonneg _))
      rcases le_or_gt 1 ‖w‖ with h | h
      · nlinarith [norm_nonneg w]
      · have hwL' : (⟨w, hwL⟩ : L) ≠ 0 := by
          intro hh
          exact hw0 (congrArg (Subtype.val) hh)
        have hwS : (⟨w, hwL⟩ : L) ∈ S := ⟨hwL', h⟩
        set z : S := ⟨⟨w, hwL⟩, hwS⟩ with hz
        have hzw : u z = w := rfl
        have hsingle : c z * ⟪u z, w⟫_ℝ ^ 2 ≤ ∑ x : S, c x * ⟪u x, w⟫_ℝ ^ 2 :=
          Finset.single_le_sum (f := fun x : S => c x * ⟪u x, w⟫_ℝ ^ 2)
            (fun x _ => mul_nonneg (hc_nonneg x) (sq_nonneg _)) (Finset.mem_univ z)
        have hval : c z * ⟪u z, w⟫_ℝ ^ 2 = 1 - ‖w‖ ^ 2 := by
          have hinner : ⟪w, w⟫_ℝ = ‖w‖ ^ 2 := by
            rw [inner_self_eq_norm_sq_to_K]; simp
          simp only [c]
          rw [hzw, hinner]
          have hne : ‖w‖ ≠ 0 := by
            rw [norm_ne_zero_iff]; exact hw0
          field_simp
        nlinarith
    have hv2 : ‖(v : EuclideanSpace ℝ (Fin d))‖ ^ 2 = ⟪q w, w⟫_ℝ := by
      have h1 : ‖(v : EuclideanSpace ℝ (Fin d))‖ ^ 2
          = ⟪(v : EuclideanSpace ℝ (Fin d)), (v : EuclideanSpace ℝ (Fin d))⟫_ℝ := by
        rw [inner_self_eq_norm_sq_to_K]; simp
      rw [h1, ← hwV]
      rw [hTsym w (T w), ← LinearMap.comp_apply, hTT]
      exact (real_inner_comm w (q w)).symm
    have : 1 ≤ ‖(v : EuclideanSpace ℝ (Fin d))‖ ^ 2 := by rw [hv2]; exact hqe
    nlinarith [norm_nonneg (v : EuclideanSpace ℝ (Fin d))]
  refine ⟨Λ, hΛdisc, hΛZL, hmin, ?_⟩
  rw [covolume_map_linear L T hTinj]
  exact mul_le_mul_of_nonneg_right hdetT_abs (ZLattice.covolume_pos (L := L) (μ := volume)).le

end

end Commons.Lattice.Packing