import Mathlib
import Submission.Work.Thom.realSumStableDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The complex splitting `ρC` and its compatibility with the real splitting `rhoR`

The real splitting `Work.Thom.rhoR k : ℝ^k × ℝ¹ ≃L[ℝ] ℝ^{k+1}` is the explicit coordinate
concatenation `EuclideanSpace.finAddEquivProd`.  Its complex counterpart is

`ρC := (EuclideanSpace.finAddEquivProd (𝕜 := ℂ) (n := k) (m := 1)).symm : ℂ^k × ℂ¹ ≃L[ℂ] ℂ^{k+1}`.

This file proves that `ρC` is *compatible* with `rhoR` in the two ways needed for the stability of
the (complexified) Pontryagin classes:

* `rhoC_cxOfReal_pair` : on the real part of the fibre, `ρC` is `rhoR`, i.e.
  `ρC (cxOfReal u, cxOfReal v) = cxOfReal (rhoR k (u, v))`;
* `rhoC_intertwine` (the second conjunct of the main statement) : `ρC` intertwines the
  complexification `cxTrans` of a real endomorphism with the complexification of the conjugate of
  that endomorphism by the two splittings.

The main theorem `Work.Thom.exists_rhoC_compat` packages both.  Note that these coordinate lemmas
are `rfl`-true: `EuclideanSpace.finAddEquivProd` is built from `LinearIsometryEquiv.piLpCongrLeft`
and `PiLp.sumPiLpEquivProdLpPiLp`, which act on the underlying coordinates and are insensitive to the
field `𝕜 ∈ {ℝ, ℂ}`.
-/

open scoped RealInnerProductSpace

namespace Work.Thom

noncomputable section

/-! ## Coordinate formulae for `EuclideanSpace.finAddEquivProd`

`finAddEquivProd 𝕜 : EuclideanSpace 𝕜 (Fin (n+m)) ≃L[𝕜] EuclideanSpace 𝕜 (Fin n) × EuclideanSpace
𝕜 (Fin m)` is the canonical coordinate shuffle along `finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n+m)`.
The following four lemmas record its effect on coordinates; the first two hold by `rfl`, the last two
says that the inverse (i.e. `rhoR`) does the same shuffle. -/

theorem finAddEquivProd_fst {𝕜 : Type*} [RCLike 𝕜] {n m : ℕ}
    (w : EuclideanSpace 𝕜 (Fin (n + m))) (i : Fin n) :
    ((EuclideanSpace.finAddEquivProd (𝕜 := 𝕜) (n := n) (m := m)) w).1 i
      = w (finSumFinEquiv (Sum.inl i)) := rfl

theorem finAddEquivProd_snd {𝕜 : Type*} [RCLike 𝕜] {n m : ℕ}
    (w : EuclideanSpace 𝕜 (Fin (n + m))) (j : Fin m) :
    ((EuclideanSpace.finAddEquivProd (𝕜 := 𝕜) (n := n) (m := m)) w).2 j
      = w (finSumFinEquiv (Sum.inr j)) := rfl

/-- The inverse of the coordinate shuffle, on the `inl` coordinates. -/
theorem finAddEquivProd_symm_apply_inl {𝕜 : Type*} [RCLike 𝕜] {n m : ℕ}
    (x : EuclideanSpace 𝕜 (Fin n)) (y : EuclideanSpace 𝕜 (Fin m)) (i : Fin n) :
    ((EuclideanSpace.finAddEquivProd (𝕜 := 𝕜) (n := n) (m := m)).symm (x, y)).ofLp
        (finSumFinEquiv (Sum.inl i)) = x.ofLp i := by
  have h1 := finAddEquivProd_fst (𝕜 := 𝕜) (n := n) (m := m)
      ((EuclideanSpace.finAddEquivProd (𝕜 := 𝕜) (n := n) (m := m)).symm (x, y)) i
  have h2 : (((EuclideanSpace.finAddEquivProd (𝕜 := 𝕜) (n := n) (m := m))
      ((EuclideanSpace.finAddEquivProd (𝕜 := 𝕜) (n := n) (m := m)).symm (x, y))).1).ofLp i
        = x.ofLp i := by
    rw [ContinuousLinearEquiv.apply_symm_apply]
  exact h1.symm.trans h2

/-- The inverse of the coordinate shuffle, on the `inr` coordinates. -/
theorem finAddEquivProd_symm_apply_inr {𝕜 : Type*} [RCLike 𝕜] {n m : ℕ}
    (x : EuclideanSpace 𝕜 (Fin n)) (y : EuclideanSpace 𝕜 (Fin m)) (j : Fin m) :
    ((EuclideanSpace.finAddEquivProd (𝕜 := 𝕜) (n := n) (m := m)).symm (x, y)).ofLp
        (finSumFinEquiv (Sum.inr j)) = y.ofLp j := by
  have h1 := finAddEquivProd_snd (𝕜 := 𝕜) (n := n) (m := m)
      ((EuclideanSpace.finAddEquivProd (𝕜 := 𝕜) (n := n) (m := m)).symm (x, y)) j
  have h2 : (((EuclideanSpace.finAddEquivProd (𝕜 := 𝕜) (n := n) (m := m))
      ((EuclideanSpace.finAddEquivProd (𝕜 := 𝕜) (n := n) (m := m)).symm (x, y))).2).ofLp j
        = y.ofLp j := by
    rw [ContinuousLinearEquiv.apply_symm_apply]
  exact h1.symm.trans h2

/-! ## The complex splitting `ρC` and the real inclusion `cxOfReal` -/

/-- **The complex splitting agrees with the real splitting on the real part**: the coordinate shuffle
is insensitive to the coefficient field, so it commutes with the inclusion `cxOfReal` of the real part
of the fibre. -/
theorem rhoC_cxOfReal_pair (k : ℕ) (u : EuclideanSpace ℝ (Fin k)) (v : EuclideanSpace ℝ (Fin 1)) :
    (EuclideanSpace.finAddEquivProd (𝕜 := ℂ) (n := k) (m := 1)).symm (cxOfReal u, cxOfReal v)
      = cxOfReal (rhoR k (u, v)) := by
  simp only [rhoR]
  ext t
  obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective t
  rcases s with i | j
  · rw [finAddEquivProd_symm_apply_inl]
    simp only [cxOfReal, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp]
    rw [finAddEquivProd_symm_apply_inl]
  · rw [finAddEquivProd_symm_apply_inr]
    simp only [cxOfReal, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp]
    rw [finAddEquivProd_symm_apply_inr]

/-- The inverse of the complex splitting on a vector lying in the real part of the fibre: it splits
according to the inverse of the real splitting. -/
theorem rhoC_symm_cxOfReal (k : ℕ) (u : EuclideanSpace ℝ (Fin (k + 1))) :
    ((EuclideanSpace.finAddEquivProd (𝕜 := ℂ) (n := k) (m := 1)).symm).symm (cxOfReal u)
      = (cxOfReal (((rhoR k).symm u).1), cxOfReal (((rhoR k).symm u).2)) := by
  have h := rhoC_cxOfReal_pair k (((rhoR k).symm u).1) (((rhoR k).symm u).2)
  rw [show rhoR k (((rhoR k).symm u).1, ((rhoR k).symm u).2) = u from by
        rw [show (((rhoR k).symm u).1, ((rhoR k).symm u).2) = (rhoR k).symm u from rfl,
          ContinuousLinearEquiv.apply_symm_apply]] at h
  rw [← h, ContinuousLinearEquiv.symm_apply_apply]

/-! ## A linearity criterion: ℂ-linear maps agreeing on the real part agree

This is the small amount of linear algebra that lets us reduce the intertwining identity to the
computation on `cxOfReal u`. -/

/-- Multiplication by `i` is the ℂ-scalar multiplication by `Complex.I`. -/
theorem cxMulI_eq_smul_one (j : ℕ) (v : EuclideanSpace ℂ (Fin j)) :
    cxMulI v = Complex.I • v := rfl

/-- Two ℂ-linear endomorphisms of `ℂ^j` which agree on the image of the real inclusion `cxOfReal`
are equal: every vector is `cxRePart v + i · cxImPart v`. -/
theorem cxLinearMap_ext_cxOfReal {j : ℕ}
    {f g : EuclideanSpace ℂ (Fin j) →L[ℂ] EuclideanSpace ℂ (Fin j)}
    (h : ∀ u : EuclideanSpace ℝ (Fin j), f (cxOfReal u) = g (cxOfReal u)) : f = g := by
  ext w
  have hd : cxOfReal (cxRePart w) + Complex.I • cxOfReal (cxImPart w) = w := by
    rw [← cxMulI_eq_smul_one]
    exact cxOfReal_cxRePart_add_cxMulI_cxImPart w
  conv_lhs => rw [← hd]
  conv_rhs => rw [← hd]
  simp only [map_add, map_smul, h]

/-! ## The main theorem -/

theorem exists_rhoC_compat (k : ℕ) :
    ∃ ρC : (EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin 1)) ≃L[ℂ] EuclideanSpace ℂ (Fin (k + 1)),
      (∀ (u : EuclideanSpace ℝ (Fin k)) (v : EuclideanSpace ℝ (Fin 1)),
        ρC (cxOfReal u, cxOfReal v) = cxOfReal (rhoR k (u, v))) ∧
      (∀ (T : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k))
        (w : EuclideanSpace ℂ (Fin (k + 1))),
        cxTrans (((rhoR k) : (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin 1)) →L[ℝ]
              EuclideanSpace ℝ (Fin (k + 1))).comp
            (((T.prodMap (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1)))).comp
              ((rhoR k).symm : EuclideanSpace ℝ (Fin (k + 1)) →L[ℝ]
                (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin 1)))))) w
          = ρC (((cxTrans T).prodMap (ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1))))
              (ρC.symm w))) := by
  refine ⟨(EuclideanSpace.finAddEquivProd (𝕜 := ℂ) (n := k) (m := 1)).symm, ?_, ?_⟩
  · intro u v
    exact rhoC_cxOfReal_pair k u v
  · intro T w
    -- The conjugate of `T` by the splittings, as a real endomorphism of `ℝ^{k+1}`.
    set S : EuclideanSpace ℝ (Fin (k + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (k + 1)) :=
      ((rhoR k) : (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin 1)) →L[ℝ]
          EuclideanSpace ℝ (Fin (k + 1))).comp
        (((T.prodMap (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1)))).comp
          ((rhoR k).symm : EuclideanSpace ℝ (Fin (k + 1)) →L[ℝ]
            (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin 1)))))
    -- It suffices to check the identity on the real part of the fibre.
    have hpt : ∀ a : EuclideanSpace ℝ (Fin (k + 1)),
        cxTrans S (cxOfReal a)
          = (EuclideanSpace.finAddEquivProd (𝕜 := ℂ) (n := k) (m := 1)).symm
              (((cxTrans T).prodMap (ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1))))
                (((EuclideanSpace.finAddEquivProd (𝕜 := ℂ) (n := k) (m := 1)).symm).symm
                  (cxOfReal a))) := by
      intro a
      rw [cxTrans_cxOfReal, rhoC_symm_cxOfReal]
      simp only [ContinuousLinearMap.coe_prodMap', Prod.map_apply, ContinuousLinearMap.id_apply]
      rw [cxTrans_cxOfReal, rhoC_cxOfReal_pair]
      congr 1
    -- Decompose an arbitrary vector into real and imaginary parts and use ℂ-linearity.
    have hd : cxOfReal (cxRePart w) + Complex.I • cxOfReal (cxImPart w) = w := by
      rw [← cxMulI_eq_smul_one]
      exact cxOfReal_cxRePart_add_cxMulI_cxImPart w
    rw [← hd]
    simp only [map_add, map_smul, hpt]

end

end Work.Thom
