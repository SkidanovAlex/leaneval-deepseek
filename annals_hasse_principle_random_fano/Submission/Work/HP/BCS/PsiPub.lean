import Mathlib
import Submission.Work.HP.MMDefs
import Submission.Work.HP.Defs
import Submission.Work.HP.BCS.Defs
import Submission.Work.HP.BCS.Setup
import Submission.Work.HP.Lat.detL_basis_gram

/-!
# Coordinate transport for the cone-count `Work.HP.BCS.BallConeCountPub`

Given an integral lattice `L ⊆ ℤ^ι` of rank `k` and a `ℤ`-basis `b` of `L`, the coefficient
lattice is presented as an injective `ℝ`-linear endomorphism of `ℝ^k`
```
pPsiOf L b : ℝ^k → ℝ^k,   pPsiOf L b (toEk t) = (coefficients of Σ i, t i • b i in an
                                                    orthonormal basis of span_ℝ L).
```
Integration (Lebesgue measure) on `span_ℝ L` is transported by the isometry `pIsomSpan L b`, and
the cone `𝒞_v^{(γ)}` becomes `coneSet (pConeVec L b v) (‖toE v‖ / (2γ))`.
-/

set_option autoImplicit false
noncomputable section
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

open MeasureTheory Finset Matrix
open scoped Pointwise Topology

namespace Work.HP.BCS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Elementary casts -/

/-- The canonical linear isometry `(Fin k → ℝ) ≃ ℝ^k`. -/
def pToEkEquiv (k : ℕ) : (Fin k → ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin k) :=
  (WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).symm

@[simp] theorem pToEkEquiv_apply (k : ℕ) (x : Fin k → ℝ) :
    pToEkEquiv k x = WithLp.toLp 2 x := rfl

@[simp] theorem pToEkEquiv_symm_apply (k : ℕ) (x : EuclideanSpace ℝ (Fin k)) :
    (pToEkEquiv k).symm x = x.ofLp := rfl

theorem pToEk_eq {k : ℕ} (t : Fin k → ℤ) :
    toEk t = pToEkEquiv k (fun i => (t i : ℝ)) := rfl

/-- The inner product of two embedded integer vectors. -/
theorem pInner_toEr_toEr (u v : ι → ℤ) :
    inner ℝ (toEr u) (toEr v) = dotR (toR v) (toR u) := by
  rw [show toEr u = toE (toR u) from rfl, inner_toE_toEr, dotR_comm]

/-! ## The coefficient equivalence and the coordinate lattice map -/

/-- The coefficient map of a `ℤ`-basis of `L`, as a linear equivalence onto `span_ℝ L`. -/
def pCoeffEquiv {k : ℕ} (L : Submodule ℤ (ι → ℤ)) (b : Module.Basis (Fin k) ℤ L) :
    (Fin k → ℝ) ≃ₗ[ℝ] spanE L :=
  LinearEquiv.ofBijective
    ((coeffMap (fun i => (b i : ι → ℤ))).codRestrict (spanE L) (by
      intro x
      rw [← coeffMap_range L b]
      exact LinearMap.mem_range_self _ x))
    ⟨fun x y h => coeffMap_injective L b (congrArg Subtype.val h), fun y => by
      have hy : (y : EuclideanSpace ℝ ι) ∈ (coeffMap (fun i => (b i : ι → ℤ))).range := by
        rw [coeffMap_range L b]; exact y.2
      obtain ⟨x, hx⟩ := hy
      exact ⟨x, Subtype.ext hx⟩⟩

theorem pCoeffEquiv_coe {k : ℕ} (L : Submodule ℤ (ι → ℤ)) (b : Module.Basis (Fin k) ℤ L)
    (x : Fin k → ℝ) :
    ((pCoeffEquiv L b x : spanE L) : EuclideanSpace ℝ ι)
      = coeffMap (fun i => (b i : ι → ℤ)) x := rfl

/-- An orthonormal-coordinate isomorphism `span_ℝ L ≅ ℝ^k`. -/
def pIsomSpan {k : ℕ} (L : Submodule ℤ (ι → ℤ)) (b : Module.Basis (Fin k) ℤ L) :
    spanE L ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k) := by
  have h : Module.finrank ℝ (spanE L) = k := finrank_spanE L b
  let e := (stdOrthonormalBasis ℝ (spanE L)).repr
  rw [h] at e
  exact e

/-- The coordinate presentation of the lattice `L` as an endomorphism of `ℝ^k`. -/
def pPsiOf {k : ℕ} (L : Submodule ℤ (ι → ℤ)) (b : Module.Basis (Fin k) ℤ L) :
    EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k) :=
  (pIsomSpan L b).toLinearMap.comp
    ((pCoeffEquiv L b).toLinearMap.comp (pToEkEquiv k).symm.toLinearMap)

theorem pPsiOf_injective {k : ℕ} (L : Submodule ℤ (ι → ℤ)) (b : Module.Basis (Fin k) ℤ L) :
    Function.Injective (pPsiOf L b) := by
  intro x y h
  simp only [pPsiOf, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_toLinearMap] at h
  exact (pToEkEquiv k).symm.injective
    ((pCoeffEquiv L b).injective ((pIsomSpan L b).injective h))

/-! ## The value of `pPsiOf` on the standard basis vectors -/

theorem pCast_piSingle {k : ℕ} (i : Fin k) :
    (fun j => ((Pi.single i (1 : ℤ) : Fin k → ℤ) j : ℝ)) = (Pi.single i (1 : ℝ) : Fin k → ℝ) := by
  funext j
  by_cases h : j = i
  · subst h; simp
  · rw [show (Pi.single i (1 : ℤ) : Fin k → ℤ) j = 0 by simp [Pi.single_eq_of_ne, h]]
    rw [show (Pi.single i (1 : ℝ) : Fin k → ℝ) j = 0 by simp [Pi.single_eq_of_ne, h]]
    simp

theorem pToEk_single_eq_single {k : ℕ} (i : Fin k) :
    toEk (Pi.single i (1 : ℤ)) = EuclideanSpace.single i (1 : ℝ) := by
  rw [toEk, EuclideanSpace.single, pCast_piSingle i, PiLp.single]

theorem pToEkEquiv_symm_single {k : ℕ} (i : Fin k) :
    (pToEkEquiv k).symm.toLinearMap (EuclideanSpace.single i 1)
      = Function.update (0 : Fin k → ℝ) i 1 := by
  change (pToEkEquiv k).symm (EuclideanSpace.single i 1) = Function.update (0 : Fin k → ℝ) i 1
  funext j
  rw [pToEkEquiv_symm_apply, EuclideanSpace.single, PiLp.single_apply, Function.update_apply]
  by_cases h : j = i <;> simp [h]

theorem pCoeffMap_update {k : ℕ} (L : Submodule ℤ (ι → ℤ)) (b : Module.Basis (Fin k) ℤ L)
    (i : Fin k) :
    coeffMap (fun i => (b i : ι → ℤ)) (Function.update (0 : Fin k → ℝ) i 1)
      = toEr ((b i : ι → ℤ)) := by
  rw [coeffMap_eq_sum, Finset.sum_eq_single i]
  · rw [Function.update_self, one_smul]
  · intro j _ hj
    have hupd : Function.update (0 : Fin k → ℝ) i 1 j = 0 :=
      Function.update_of_ne (a := j) (a' := i) hj (1 : ℝ) (0 : Fin k → ℝ)
    rw [hupd, zero_smul]
  · intro hi; exact absurd (Finset.mem_univ i) hi

theorem pPsiOf_single_eq {k : ℕ} (L : Submodule ℤ (ι → ℤ)) (b : Module.Basis (Fin k) ℤ L)
    (i : Fin k) :
    pPsiOf L b (EuclideanSpace.single i 1)
      = pIsomSpan L b ⟨toEr ((b i : ι → ℤ)),
          Submodule.subset_span ⟨_, (b i).2, rfl⟩⟩ := by
  rw [pPsiOf, LinearMap.comp_apply, LinearMap.comp_apply, pToEkEquiv_symm_single i]
  show (pIsomSpan L b) (pCoeffEquiv L b (Function.update (0 : Fin k → ℝ) i 1))
      = (pIsomSpan L b) ⟨toEr ((b i : ι → ℤ)), Submodule.subset_span ⟨_, (b i).2, rfl⟩⟩
  exact congrArg (pIsomSpan L b) (Subtype.ext (by
    simpa using (pCoeffEquiv_coe L b (Function.update (0 : Fin k → ℝ) i 1)).trans
      (pCoeffMap_update L b i)))

theorem pNorm_pPsiOf_single {k : ℕ} (L : Submodule ℤ (ι → ℤ)) (b : Module.Basis (Fin k) ℤ L)
    (i : Fin k) :
    ‖pPsiOf L b (EuclideanSpace.single i 1)‖ = eNorm ((b i : ι → ℤ)) := by
  rw [pPsiOf_single_eq L b i, LinearIsometryEquiv.norm_map]
  exact norm_toEr _

theorem pCellRad_pPsiOf {k : ℕ} (L : Submodule ℤ (ι → ℤ)) (b : Module.Basis (Fin k) ℤ L) :
    cellRad (pPsiOf L b) = ∑ i, eNorm ((b i : ι → ℤ)) := by
  rw [cellRad]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pToEk_single_eq_single i]
  exact pNorm_pPsiOf_single L b i

/-! ## The cone vector -/

/-- The Riesz vector of the functional `y ↦ ⟪toE v, (pIsomSpan L b).symm y⟫` on `ℝ^k`. -/
def pConeVec {k : ℕ} (L : Submodule ℤ (ι → ℤ)) (b : Module.Basis (Fin k) ℤ L)
    (v : ι → ℝ) : EuclideanSpace ℝ (Fin k) :=
  (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin k))).symm
    ((innerSL ℝ (toE v)).comp
      ((Submodule.subtypeL (spanE L)).comp
        (((pIsomSpan L b).symm : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] spanE L).toContinuousLinearEquiv.toContinuousLinearMap)))

theorem pInner_pConeVec {k : ℕ} (L : Submodule ℤ (ι → ℤ)) (b : Module.Basis (Fin k) ℤ L)
    (v : ι → ℝ) (y : EuclideanSpace ℝ (Fin k)) :
    inner ℝ (pConeVec L b v) y
      = inner ℝ (toE v) (((pIsomSpan L b).symm y : spanE L) : EuclideanSpace ℝ ι) := by
  rw [pConeVec, InnerProductSpace.toDual_symm_apply]
  rfl

/-! ## The count of lattice points -/

/-- The basis vector `b i` of the lattice `L`, as an element of `ι → ℤ`. -/
def pB {k : ℕ} (L : Submodule ℤ (ι → ℤ)) (b : Module.Basis (Fin k) ℤ L) (i : Fin k) : ι → ℤ :=
  ↑(b i)

/-- The Gram matrix over `ℝ` of the lattice basis `b` (the matrix of `Work.HP.Lat.detL_basis_gram`). -/
def pGramMat {k : ℕ} (L : Submodule ℤ (ι → ℤ)) (b : Module.Basis (Fin k) ℤ L) :
    Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun i j => ∑ x : ι, ((pB L b i) x : ℝ) * ((pB L b j) x : ℝ)

/-- `dotR` of two embedded integer vectors as an explicit sum. -/
theorem pDotR_toR (u v : ι → ℤ) : dotR (toR u) (toR v) = ∑ x : ι, (u x : ℝ) * (v x : ℝ) := rfl

theorem pInner_pPsiOf_single {k : ℕ} (L : Submodule ℤ (ι → ℤ)) (b : Module.Basis (Fin k) ℤ L)
    (i j : Fin k) :
    inner ℝ (pPsiOf L b (EuclideanSpace.single i 1)) (pPsiOf L b (EuclideanSpace.single j 1))
      = pGramMat L b i j := by
  rw [pPsiOf_single_eq L b i, pPsiOf_single_eq L b j,
    LinearIsometryEquiv.inner_map_map (pIsomSpan L b)]
  show inner ℝ (toEr (pB L b i)) (toEr (pB L b j)) = pGramMat L b i j
  rw [pInner_toEr_toEr, pDotR_toR, pGramMat, Matrix.of_apply]
  exact Finset.sum_congr rfl fun κ _ => mul_comm _ _

theorem pGram_pPsiOf {k : ℕ} (L : Submodule ℤ (ι → ℤ)) (b : Module.Basis (Fin k) ℤ L) :
    (Matrix.gram ℝ (fun x => pPsiOf L b ((EuclideanSpace.basisFun (Fin k) ℝ) x)))
      = pGramMat L b := by
  ext i j
  rw [Matrix.gram_apply, EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_apply]
  exact pInner_pPsiOf_single L b i j

theorem pGramMat_psd {k : ℕ} (L : Submodule ℤ (ι → ℤ)) (b : Module.Basis (Fin k) ℤ L) :
    (pGramMat L b).PosSemidef := by
  have h : pGramMat L b = Matrix.gram ℝ (fun i => toEr (pB L b i)) := by
    ext i j
    rw [Matrix.gram_apply, pInner_toEr_toEr, pDotR_toR, pGramMat, Matrix.of_apply]
    exact Finset.sum_congr rfl fun κ _ => mul_comm _ _
  rw [h]
  exact Matrix.posSemidef_gram ℝ _

/-- The norm-determinant of the coordinate lattice map is the covolume of the lattice. -/
theorem pNormDet_pPsiOf {k : ℕ} (L : Submodule ℤ (ι → ℤ)) (b : Module.Basis (Fin k) ℤ L) :
    (pPsiOf L b).normDet = detL L := by
  have hgram := pGram_pPsiOf L b
  have hMnonneg : 0 ≤ (pGramMat L b).det :=
    Matrix.PosSemidef.det_nonneg (pGramMat_psd L b)
  have h1 : (pPsiOf L b).normDet ^ 2 = (pGramMat L b).det := by
    have h := LinearMap.normDet_sq_eq_det_gram (pPsiOf L b) (EuclideanSpace.basisFun (Fin k) ℝ)
    rw [hgram] at h
    simpa using h
  have h2 : detL L ^ 2 = (pGramMat L b).det := by
    rw [Work.HP.Lat.detL_basis_gram L b]
    exact Real.sq_sqrt hMnonneg
  have heq : (pPsiOf L b).normDet ^ 2 = (detL L) ^ 2 := h1.trans h2.symm
  have hn : 0 ≤ (pPsiOf L b).normDet := LinearMap.normDet_nonneg (pPsiOf L b)
  have hd : 0 ≤ detL L := by rw [detL]; exact Real.sqrt_nonneg _
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp heq with h | h
  · exact h
  · linarith

/-! ## The value of `pPsiOf` on the lattice coordinates -/

/-- `toEr` of the `t`-th combination of the basis is the corresponding real linear combination. -/
theorem pToEr_equivFunSymm {k : ℕ} (L : Submodule ℤ (ι → ℤ)) (b : Module.Basis (Fin k) ℤ L)
    (t : Fin k → ℤ) :
    toEr ((b.equivFun.symm t : L) : ι → ℤ)
      = ∑ i, (t i : ℝ) • toEr (((b i : L) : ι → ℤ)) := by
  have h1 : ((b.equivFun.symm t : L) : ι → ℤ) = ((∑ i, t i • b i : L) : ι → ℤ) := by
    rw [b.equivFun_symm_apply]
  rw [h1]
  have h2 : ((∑ i, t i • b i : L) : ι → ℤ) = ∑ i, t i • ((b i : L) : ι → ℤ) := by
    change (Submodule.subtype L) (∑ i, t i • b i) = _
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => map_smul _ _ _
  rw [h2]
  show toErLin (∑ i, t i • ((b i : L) : ι → ℤ))
      = ∑ i, (t i : ℝ) • toEr (((b i : L) : ι → ℤ))
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul]
  exact (Int.cast_smul_eq_zsmul ℝ (t i) (toEr (((b i : L) : ι → ℤ)))).symm

/-- The coefficient vector of `Σ i, t i • b i` is the image of `t` under `pPsiOf`. -/
theorem pCoeffEquiv_toEr {k : ℕ} (L : Submodule ℤ (ι → ℤ)) (b : Module.Basis (Fin k) ℤ L)
    (t : Fin k → ℤ) :
    ((pCoeffEquiv L b (fun i => (t i : ℝ)) : spanE L) : EuclideanSpace ℝ ι)
      = toEr ((b.equivFun.symm t : L) : ι → ℤ) := by
  rw [pCoeffEquiv_coe, coeffMap_eq_sum]
  exact (pToEr_equivFunSymm L b t).symm

/-- `pPsiOf` on the lattice coordinates, exposed as an element of `span_ℝ L`. -/
theorem pPsiOf_toEk_spaneq {k : ℕ} (L : Submodule ℤ (ι → ℤ)) (b : Module.Basis (Fin k) ℤ L)
    (t : Fin k → ℤ) :
    pPsiOf L b (toEk t) = pIsomSpan L b ⟨toEr ((b.equivFun.symm t : L) : ι → ℤ),
      Submodule.subset_span ⟨((b.equivFun.symm t : L) : ι → ℤ), (b.equivFun.symm t).2, rfl⟩⟩ := by
  have h0 : pPsiOf L b (toEk t) = pIsomSpan L b (pCoeffEquiv L b (fun i => (t i : ℝ))) := by
    rw [pPsiOf, LinearMap.comp_apply, LinearMap.comp_apply, pToEk_eq t]
    simp
  rw [h0]
  exact congrArg (pIsomSpan L b) (Subtype.ext (pCoeffEquiv_toEr L b t))

theorem pPsiOf_toEk_norm {k : ℕ} (L : Submodule ℤ (ι → ℤ)) (b : Module.Basis (Fin k) ℤ L)
    (t : Fin k → ℤ) :
    ‖pPsiOf L b (toEk t)‖ = eNorm ((b.equivFun.symm t : L) : ι → ℤ) := by
  rw [pPsiOf_toEk_spaneq L b t, LinearIsometryEquiv.norm_map]
  exact norm_toEr _

theorem pPsiOf_toEk_inner {k : ℕ} (L : Submodule ℤ (ι → ℤ)) (b : Module.Basis (Fin k) ℤ L)
    (v : ι → ℝ) (t : Fin k → ℤ) :
    inner ℝ (pConeVec L b v) (pPsiOf L b (toEk t))
      = dotR v (toR ((b.equivFun.symm t : L) : ι → ℤ)) := by
  rw [pPsiOf_toEk_spaneq L b t, pInner_pConeVec, LinearIsometryEquiv.symm_apply_apply]
  exact inner_toE_toEr v ((b.equivFun.symm t : L) : ι → ℤ)

/-- The cone condition transfers to the lattice coordinates. -/
theorem pMem_coneSet_iff {k : ℕ} (L : Submodule ℤ (ι → ℤ)) (b : Module.Basis (Fin k) ℤ L)
    (v : ι → ℝ) (γ : ℝ) (t : Fin k → ℤ) :
    (pPsiOf L b (toEk t) ∈ coneSet (pConeVec L b v) (‖toE v‖ / (2 * γ)))
      ↔ (toR ((b.equivFun.symm t : L) : ι → ℤ) ∈ Cgam v γ) := by
  rw [mem_Cgam_iff, coneSet, Set.mem_setOf_eq, pPsiOf_toEk_inner L b v t,
    pPsiOf_toEk_norm L b t, div_mul_eq_mul_div, inner_toE_toEr, norm_toEr]

theorem pToEk_injective (k : ℕ) : Function.Injective (toEk (k := k)) := by
  intro x y h
  rw [pToEk_eq] at h
  have h1 := (pToEkEquiv k).injective h
  funext i
  exact_mod_cast congrFun h1 i

/-- The count of lattice points with coordinates `t` equals the count of the corresponding
points `pPsiOf L b (toEk t)` in `ℝ^k`. -/
theorem pNcard_lat {k : ℕ} (L : Submodule ℤ (ι → ℤ)) (b : Module.Basis (Fin k) ℤ L)
    (v w : ι → ℝ) (γ T : ℝ) :
    ({y : EuclideanSpace ℝ (Fin k) | y ∈ latImage (pPsiOf L b) ∧
        y ∈ coneSet (pConeVec L b v) (‖toE v‖ / (2 * γ)) ∧
        y ∈ coneSet (pConeVec L b w) (‖toE w‖ / (2 * γ)) ∧ ‖y‖ ≤ T}.ncard : ℝ)
      = ({t : Fin k → ℤ | pPsiOf L b (toEk t) ∈ latImage (pPsiOf L b) ∧
          pPsiOf L b (toEk t) ∈ coneSet (pConeVec L b v) (‖toE v‖ / (2 * γ)) ∧
          pPsiOf L b (toEk t) ∈ coneSet (pConeVec L b w) (‖toE w‖ / (2 * γ)) ∧
          ‖pPsiOf L b (toEk t)‖ ≤ T}.ncard : ℝ) := by
  have hset : ({y : EuclideanSpace ℝ (Fin k) | y ∈ latImage (pPsiOf L b) ∧
        y ∈ coneSet (pConeVec L b v) (‖toE v‖ / (2 * γ)) ∧
        y ∈ coneSet (pConeVec L b w) (‖toE w‖ / (2 * γ)) ∧ ‖y‖ ≤ T} : Set _)
      = (fun t : Fin k → ℤ => pPsiOf L b (toEk t)) '' {t : Fin k → ℤ |
          pPsiOf L b (toEk t) ∈ latImage (pPsiOf L b) ∧
          pPsiOf L b (toEk t) ∈ coneSet (pConeVec L b v) (‖toE v‖ / (2 * γ)) ∧
          pPsiOf L b (toEk t) ∈ coneSet (pConeVec L b w) (‖toE w‖ / (2 * γ)) ∧
          ‖pPsiOf L b (toEk t)‖ ≤ T} := by
    ext y
    constructor
    · rintro ⟨hy, h1, h2, h3⟩
      obtain ⟨z, ⟨t, rfl⟩, hzy⟩ := hy
      exact ⟨t, ⟨⟨toEk t, ⟨t, rfl⟩, rfl⟩, by rwa [hzy], by rwa [hzy], by rwa [hzy]⟩, hzy⟩
    · rintro ⟨t, ⟨-, h1, h2, h3⟩, rfl⟩
      exact ⟨⟨toEk t, ⟨t, rfl⟩, rfl⟩, h1, h2, h3⟩
  have hinj : Function.Injective (fun t : Fin k → ℤ => pPsiOf L b (toEk t)) :=
    fun x y hxy => pToEk_injective k (pPsiOf_injective L b hxy)
  rw [hset, Set.ncard_image_of_injective _ hinj]

/-- The count of lattice points in the two cones equals the count of the coordinate vectors
of the corresponding combinations of the basis. -/
theorem pNcard_L {k : ℕ} (L : Submodule ℤ (ι → ℤ)) (b : Module.Basis (Fin k) ℤ L)
    (v w : ι → ℝ) (γ T : ℝ) :
    ({a : ι → ℤ | a ∈ L ∧ eNorm a ≤ T ∧ toR a ∈ Cgam v γ ∧ toR a ∈ Cgam w γ}.ncard : ℝ)
      = ({t : Fin k → ℤ | pPsiOf L b (toEk t) ∈ latImage (pPsiOf L b) ∧
          pPsiOf L b (toEk t) ∈ coneSet (pConeVec L b v) (‖toE v‖ / (2 * γ)) ∧
          pPsiOf L b (toEk t) ∈ coneSet (pConeVec L b w) (‖toE w‖ / (2 * γ)) ∧
          ‖pPsiOf L b (toEk t)‖ ≤ T}.ncard : ℝ) := by
  have hφinj : Function.Injective
      (fun t : Fin k → ℤ => ((b.equivFun.symm t : L) : ι → ℤ)) := by
    intro t u h
    exact b.equivFun.symm.injective (Subtype.ext h)
  have hset : ({a : ι → ℤ |
        a ∈ L ∧ eNorm a ≤ T ∧ toR a ∈ Cgam v γ ∧ toR a ∈ Cgam w γ} : Set (ι → ℤ))
      = (fun t : Fin k → ℤ => ((b.equivFun.symm t : L) : ι → ℤ)) '' {t : Fin k → ℤ |
          pPsiOf L b (toEk t) ∈ latImage (pPsiOf L b) ∧
          pPsiOf L b (toEk t) ∈ coneSet (pConeVec L b v) (‖toE v‖ / (2 * γ)) ∧
          pPsiOf L b (toEk t) ∈ coneSet (pConeVec L b w) (‖toE w‖ / (2 * γ)) ∧
          ‖pPsiOf L b (toEk t)‖ ≤ T} := by
    ext a
    constructor
    · rintro ⟨haL, h1, h2, h3⟩
      have hφeq : ((b.equivFun.symm (b.equivFun ⟨a, haL⟩) : L) : ι → ℤ) = a :=
        congrArg Subtype.val (b.equivFun.symm_apply_apply (⟨a, haL⟩ : L))
      refine ⟨b.equivFun ⟨a, haL⟩, ⟨?_, ?_, ?_, ?_⟩, hφeq⟩
      · exact ⟨toEk _, ⟨_, rfl⟩, rfl⟩
      · exact (pMem_coneSet_iff L b v γ (b.equivFun ⟨a, haL⟩)).mpr (by rw [hφeq]; exact h2)
      · exact (pMem_coneSet_iff L b w γ (b.equivFun ⟨a, haL⟩)).mpr (by rw [hφeq]; exact h3)
      · rw [pPsiOf_toEk_norm, hφeq]
        exact h1
    · rintro ⟨t, ⟨-, h1, h2, h3⟩, rfl⟩
      exact ⟨(b.equivFun.symm t).2, by rw [← pPsiOf_toEk_norm L b t]; exact h3,
        (pMem_coneSet_iff L b v γ t).mp h1, (pMem_coneSet_iff L b w γ t).mp h2⟩
  rw [hset, Set.ncard_image_of_injective _ hφinj]

theorem pNcard_core {k : ℕ} (L : Submodule ℤ (ι → ℤ)) (b : Module.Basis (Fin k) ℤ L)
    (v w : ι → ℝ) (γ T : ℝ) :
    ({a : ι → ℤ | a ∈ L ∧ eNorm a ≤ T ∧ toR a ∈ Cgam v γ ∧ toR a ∈ Cgam w γ}.ncard : ℝ)
      = ({y : EuclideanSpace ℝ (Fin k) | y ∈ latImage (pPsiOf L b) ∧
            y ∈ coneSet (pConeVec L b v) (‖toE v‖ / (2 * γ)) ∧
            y ∈ coneSet (pConeVec L b w) (‖toE w‖ / (2 * γ)) ∧ ‖y‖ ≤ T}.ncard : ℝ) := by
  rw [pNcard_L L b v w γ T, pNcard_lat L b v w γ T]

/-! ## The volume of the cone slice -/

theorem pConeVol {k : ℕ} (L : Submodule ℤ (ι → ℤ)) (b : Module.Basis (Fin k) ℤ L)
    (v w : ι → ℝ) (γ : ℝ) :
    coneSliceVol L v w γ
      = (volume {y : EuclideanSpace ℝ (Fin k) |
            y ∈ coneSet (pConeVec L b v) (‖toE v‖ / (2 * γ)) ∧
            y ∈ coneSet (pConeVec L b w) (‖toE w‖ / (2 * γ)) ∧ ‖y‖ ≤ 1}).toReal := by
  set B : Set (EuclideanSpace ℝ (Fin k)) := {y : EuclideanSpace ℝ (Fin k) |
      y ∈ coneSet (pConeVec L b v) (‖toE v‖ / (2 * γ)) ∧
      y ∈ coneSet (pConeVec L b w) (‖toE w‖ / (2 * γ)) ∧ ‖y‖ ≤ 1} with hB
  set A : Set (spanE L) := {t : spanE L |
      |inner ℝ (toE v) (t : EuclideanSpace ℝ ι)| ≤ ‖toE v‖ * ‖(t : EuclideanSpace ℝ ι)‖ / (2 * γ) ∧
      |inner ℝ (toE w) (t : EuclideanSpace ℝ ι)| ≤ ‖toE w‖ * ‖(t : EuclideanSpace ℝ ι)‖ / (2 * γ) ∧
      ‖(t : EuclideanSpace ℝ ι)‖ ≤ 1} with hA
  have hcs : coneSliceVol L v w γ = (volume A).toReal := by
    rw [hA, coneSliceVol, subVol]
    simp only [Set.mem_setOf_eq]
  have hpre : (pIsomSpan L b) ⁻¹' B = A := by
    ext t
    have hnorm : ‖(pIsomSpan L b) t‖ = ‖(t : EuclideanSpace ℝ ι)‖ := by
      rw [LinearIsometryEquiv.norm_map]
      exact (Submodule.norm_coe t).symm
    have hv : inner ℝ (pConeVec L b v) ((pIsomSpan L b) t)
        = inner ℝ (toE v) (t : EuclideanSpace ℝ ι) := by
      rw [pInner_pConeVec, LinearIsometryEquiv.symm_apply_apply]
    have hw : inner ℝ (pConeVec L b w) ((pIsomSpan L b) t)
        = inner ℝ (toE w) (t : EuclideanSpace ℝ ι) := by
      rw [pInner_pConeVec, LinearIsometryEquiv.symm_apply_apply]
    simp only [Set.mem_preimage, hB, hA, Set.mem_setOf_eq, coneSet, hnorm, hv, hw,
      div_mul_eq_mul_div]
  have hvol : volume A = volume B := by
    have hmp : MeasurePreserving (pIsomSpan L b).toMeasurableEquiv volume volume :=
      (pIsomSpan L b).measurePreserving
    have h := hmp.measure_preimage_equiv B
    have hA : (⇑(pIsomSpan L b).toMeasurableEquiv) ⁻¹' B = A := hpre
    rw [hA] at h
    exact h
  rw [hcs, hvol]

end Work.HP.BCS
