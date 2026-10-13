import Submission.Work.DSM2p.CSAlgPosAux
import Submission.Work.DSFFP.flat_quot_quot_pow
import Mathlib.RingTheory.Flat.Stability

/-!
# The reduction `A_∞ ⧸ ϖA_∞ = (A_∞ ⧸ I_∞) ⧸ ϖ`

The main lemma of this file, `CSAlgPos_quot_varpi_flat_of_quot_ideal_flat`, performs the
"mod `ϖ`" step of `Work.DSM2p.CSAlgPos_mod_varpi_flat`: from the flatness of `A_∞ ⧸ I_∞` over `A`
(Česnavičius–Scholze: flat because `A_∞/I_∞ ≅ Λ/I₀` is free) it deduces the flatness of
`A_∞ ⧸ ϖA_∞` over `A ⧸ (ϖ)`.

The mathematical content is the identification
`A_∞ ⧸ ϖA_∞ ≅ (A ⧸ (ϖ)) ⊗[A] (A_∞ ⧸ I_∞)`, which holds because `I_∞ ⊆ ϖA_∞`
(`I_∞` is `ϖ`-divisible: `F(T_F)/ϖ^m = ϖ · F(T_F)/ϖ^{m+1}`).
-/

open scoped Classical

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1000000

namespace Work.DSM2p

universe u

section Varpi

variable (A : Type u) [CommRing A] (p : ℕ) (ϖ : A)

/-- **`I_∞` is contained in `ϖ·A_∞`.**  This is the `ϖ`-divisibility of the Česnavičius–Scholze
ideal `I_∞ = (F(T_F)/ϖ^m)`: the generator of level `m` is `ϖ` times the generator of level
`m + 1`. -/
theorem CSIdealPos_le_map_span_varpi :
    CSIdealPos A p ϖ ≤ (Ideal.span {ϖ}).map (algebraMap A ↥(CSAlgPos A p ϖ)) := by
  have hspan : (Ideal.span ({ϖ} : Set A)).map (algebraMap A ↥(CSAlgPos A p ϖ))
      = Ideal.span {algebraMap A ↥(CSAlgPos A p ϖ) ϖ} := by
    rw [Ideal.map_span, Set.image_singleton]
  rw [hspan]
  refine Ideal.span_le.mpr ?_
  rintro y ⟨q, rfl⟩
  rw [SetLike.mem_coe, Ideal.mem_span_singleton']
  refine ⟨(⟨algebraMap (RootAlgPos A p) (RootAlgLocPos A p ϖ)
        (Polynomial.aeval (rootVarPos A p q.1) q.1.1) *
      IsLocalization.Away.invSelf (algebraMap A (RootAlgPos A p) ϖ) ^ (q.2 + 1),
      (Subring.subset_closure (Set.mem_union_right _
        ⟨(q.1, q.2 + 1), rfl⟩) : _ ∈ CSAlgPos A p ϖ)⟩ : ↥(CSAlgPos A p ϖ)), ?_⟩
  apply Subtype.ext
  simp only [Subring.coe_mul, Subring.coe_pow]
  set B : RootAlgLocPos A p ϖ :=
    IsLocalization.Away.invSelf (algebraMap A (RootAlgPos A p) ϖ) with hBdef
  set s : RootAlgLocPos A p ϖ :=
    algebraMap (RootAlgPos A p) (RootAlgLocPos A p ϖ) (algebraMap A (RootAlgPos A p) ϖ)
    with hsdef
  have hcoe : ((algebraMap A ↥(CSAlgPos A p ϖ) ϖ : ↥(CSAlgPos A p ϖ)) :
      RootAlgLocPos A p ϖ) = s := by
    rw [hsdef]
    exact RootAlgPos.toCSAlgPos_apply A p ϖ _
  have hB : B * s = 1 := by
    rw [hBdef, hsdef, mul_comm, IsLocalization.Away.mul_invSelf]
  rw [hcoe]
  change algebraMap (RootAlgPos A p) (RootAlgLocPos A p ϖ)
        (Polynomial.aeval (rootVarPos A p q.1) q.1.1) * B ^ (q.2 + 1) * s
      = algebraMap (RootAlgPos A p) (RootAlgLocPos A p ϖ)
        (Polynomial.aeval (rootVarPos A p q.1) q.1.1) * B ^ q.2
  rw [pow_succ]
  calc algebraMap (RootAlgPos A p) (RootAlgLocPos A p ϖ)
        (Polynomial.aeval (rootVarPos A p q.1) q.1.1) * (B ^ q.2 * B) * s
      = algebraMap (RootAlgPos A p) (RootAlgLocPos A p ϖ)
          (Polynomial.aeval (rootVarPos A p q.1) q.1.1) * B ^ q.2 * (B * s) := by ring
    _ = algebraMap (RootAlgPos A p) (RootAlgLocPos A p ϖ)
          (Polynomial.aeval (rootVarPos A p q.1) q.1.1) * B ^ q.2 * 1 := by rw [hB]
    _ = algebraMap (RootAlgPos A p) (RootAlgLocPos A p ϖ)
          (Polynomial.aeval (rootVarPos A p q.1) q.1.1) * B ^ q.2 := by ring

end Varpi

section Transfer

open scoped TensorProduct

variable (A : Type u) [CommRing A] (p : ℕ) (ϖ : A)

/-- **The mod-`ϖ` step.**  If `A_∞ ⧸ I_∞` is flat over `A`, then `A_∞ ⧸ ϖA_∞` is flat over
`A ⧸ (ϖ)`.  Indeed `I_∞ ⊆ ϖA_∞` and `A_∞ ⧸ ϖA_∞ ≅ (A ⧸ (ϖ)) ⊗[A] (A_∞ ⧸ I_∞)`
(change of rings, `TensorProduct.quotTensorEquivQuotSMul`, and the third isomorphism theorem). -/
theorem CSAlgPos_quot_varpi_flat_of_quot_ideal_flat
    (h : Module.Flat A (↥(CSAlgPos A p ϖ) ⧸ CSIdealPos A p ϖ)) :
    Module.Flat (A ⧸ Ideal.span {ϖ})
      (↥(CSAlgPos A p ϖ) ⧸ (Ideal.span {ϖ}).map (algebraMap A ↥(CSAlgPos A p ϖ))) := by
  haveI := h
  have hle : CSIdealPos A p ϖ ≤ (Ideal.span {ϖ}).map (algebraMap A ↥(CSAlgPos A p ϖ)) :=
    CSIdealPos_le_map_span_varpi A p ϖ
  haveI hbase : Module.Flat (A ⧸ Ideal.span {ϖ})
      ((A ⧸ Ideal.span {ϖ}) ⊗[A] (↥(CSAlgPos A p ϖ) ⧸ CSIdealPos A p ϖ)) :=
    Module.Flat.baseChange A (A ⧸ Ideal.span {ϖ}) _
  -- #### Part 1: the identification `(A ⧸ (ϖ)) ⊗[A] (A_∞ ⧸ I_∞) ≅ (A_∞ ⧸ I_∞) ⧸ ϖ·(A_∞ ⧸ I_∞)`
  have e1 : ((A ⧸ Ideal.span {ϖ}) ⊗[A] (↥(CSAlgPos A p ϖ) ⧸ CSIdealPos A p ϖ)) ≃ₗ[A]
      ((↥(CSAlgPos A p ϖ) ⧸ CSIdealPos A p ϖ) ⧸
        Ideal.map (algebraMap A (↥(CSAlgPos A p ϖ) ⧸ CSIdealPos A p ϖ)) (Ideal.span {ϖ})) :=
    (TensorProduct.quotTensorEquivQuotSMul (↥(CSAlgPos A p ϖ) ⧸ CSIdealPos A p ϖ)
        (Ideal.span {ϖ})).trans
      ((Submodule.quotEquivOfEq _ _ (Ideal.smul_top_eq_map (Ideal.span {ϖ}))).trans
        (Submodule.Quotient.restrictScalarsEquiv (S := A)
          (Ideal.map (algebraMap A (↥(CSAlgPos A p ϖ) ⧸ CSIdealPos A p ϖ))
            (Ideal.span {ϖ}))))
  -- #### Part 2: the third isomorphism theorem `(A_∞ ⧸ I_∞) ⧸ ϖ·(A_∞ ⧸ I_∞) ≅ A_∞ ⧸ ϖA_∞`
  have hJT : Ideal.map (algebraMap A (↥(CSAlgPos A p ϖ) ⧸ CSIdealPos A p ϖ)) (Ideal.span {ϖ})
      = Ideal.map (Ideal.Quotient.mk (CSIdealPos A p ϖ))
          ((Ideal.span {ϖ}).map (algebraMap A ↥(CSAlgPos A p ϖ))) := by
    rw [Ideal.map_map]
    congr 1
  let e2r : ((↥(CSAlgPos A p ϖ) ⧸ CSIdealPos A p ϖ) ⧸
        Ideal.map (algebraMap A (↥(CSAlgPos A p ϖ) ⧸ CSIdealPos A p ϖ)) (Ideal.span {ϖ})) ≃+*
      (↥(CSAlgPos A p ϖ) ⧸ (Ideal.span {ϖ}).map (algebraMap A ↥(CSAlgPos A p ϖ))) :=
    (Ideal.quotEquivOfEq hJT).trans
      ((DoubleQuot.quotQuotEquivQuotSup (CSIdealPos A p ϖ)
          ((Ideal.span {ϖ}).map (algebraMap A ↥(CSAlgPos A p ϖ)))).trans
        (Ideal.quotEquivOfEq (sup_eq_right.mpr hle)))
  let Y : Type u := (↥(CSAlgPos A p ϖ) ⧸ CSIdealPos A p ϖ) ⧸
        Ideal.map (algebraMap A (↥(CSAlgPos A p ϖ) ⧸ CSIdealPos A p ϖ)) (Ideal.span {ϖ})
  let Z : Type u := ↥(CSAlgPos A p ϖ) ⧸ (Ideal.span {ϖ}).map (algebraMap A ↥(CSAlgPos A p ϖ))
  -- the formula of `e2r` on representatives
  have e2r_mk : ∀ m : ↥(CSAlgPos A p ϖ),
      e2r (Ideal.Quotient.mk _
        (Ideal.Quotient.mk (CSIdealPos A p ϖ) m : ↥(CSAlgPos A p ϖ) ⧸ CSIdealPos A p ϖ))
        = Ideal.Quotient.mk ((Ideal.span {ϖ}).map (algebraMap A ↥(CSAlgPos A p ϖ))) m := by
    intro m
    dsimp only [e2r]
    rw [RingEquiv.trans_apply, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
    show (Ideal.quotEquivOfEq (sup_eq_right.mpr hle))
        (DoubleQuot.quotQuotEquivQuotSup (CSIdealPos A p ϖ)
          ((Ideal.span {ϖ}).map (algebraMap A ↥(CSAlgPos A p ϖ)))
          (DoubleQuot.quotQuotMk (CSIdealPos A p ϖ)
            ((Ideal.span {ϖ}).map (algebraMap A ↥(CSAlgPos A p ϖ))) m))
      = Ideal.Quotient.mk ((Ideal.span {ϖ}).map (algebraMap A ↥(CSAlgPos A p ϖ))) m
    rw [DoubleQuot.quotQuotEquivQuotSup_quotQuotMk, Ideal.quotEquivOfEq_mk]
  -- the `A`-module action on the iterated quotient
  have smul_Y : ∀ (a : A) (x : ↥(CSAlgPos A p ϖ) ⧸ CSIdealPos A p ϖ),
      a • (Ideal.Quotient.mk _ x : Y) = Ideal.Quotient.mk _ (a • x) := by
    intro a x
    rw [show (a : A) • (Ideal.Quotient.mk _ x : Y) =
          (Ideal.Quotient.mk _ (algebraMap A (↥(CSAlgPos A p ϖ) ⧸ CSIdealPos A p ϖ) a)) *
        (Ideal.Quotient.mk _ x) from rfl]
    rw [← map_mul]
    rw [show a • x = algebraMap A (↥(CSAlgPos A p ϖ) ⧸ CSIdealPos A p ϖ) a * x from
      Algebra.smul_def a x]
  have smul_X : ∀ (a : A) (m : ↥(CSAlgPos A p ϖ)),
      a • (Ideal.Quotient.mk (CSIdealPos A p ϖ) m : ↥(CSAlgPos A p ϖ) ⧸ CSIdealPos A p ϖ)
        = Ideal.Quotient.mk (CSIdealPos A p ϖ) (a • m) := by
    intro a m
    rw [show (a : A) • (Ideal.Quotient.mk (CSIdealPos A p ϖ) m :
          ↥(CSAlgPos A p ϖ) ⧸ CSIdealPos A p ϖ)
        = (Ideal.Quotient.mk (CSIdealPos A p ϖ) (algebraMap A ↥(CSAlgPos A p ϖ) a)) *
          (Ideal.Quotient.mk (CSIdealPos A p ϖ) m) from rfl]
    rw [← map_mul]
    rw [show a • m = algebraMap A ↥(CSAlgPos A p ϖ) a * m from Algebra.smul_def a m]
  have smul_Z : ∀ (a : A) (m : ↥(CSAlgPos A p ϖ)),
      a • (Ideal.Quotient.mk ((Ideal.span {ϖ}).map (algebraMap A ↥(CSAlgPos A p ϖ))) m : Z)
        = Ideal.Quotient.mk ((Ideal.span {ϖ}).map (algebraMap A ↥(CSAlgPos A p ϖ))) (a • m) := by
    intro a m
    rw [show (a : A) • (Ideal.Quotient.mk _
          m : Z) = (Ideal.Quotient.mk _
          (algebraMap A ↥(CSAlgPos A p ϖ) a)) * (Ideal.Quotient.mk _ m) from rfl]
    rw [← map_mul]
    rw [show a • m = algebraMap A ↥(CSAlgPos A p ϖ) a * m from Algebra.smul_def a m]
  -- the `A`-linear equivalence `(A_∞ ⧸ I_∞) ⧸ ϖ· ⊤ ≅ A_∞ ⧸ ϖA_∞`
  have e2lin : Y ≃ₗ[A] Z :=
    { toFun := e2r
      invFun := e2r.symm
      left_inv := e2r.left_inv
      right_inv := e2r.right_inv
      map_add' := e2r.map_add
      map_smul' := by
        intro a y
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
        obtain ⟨m, rfl⟩ := Ideal.Quotient.mk_surjective x
        rw [smul_Y, smul_X, e2r_mk, e2r_mk, smul_Z]
        simp }
  exact Module.Flat.of_linearEquiv
    (LinearEquiv.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
      (e1.trans e2lin)).symm

end Transfer

end Work.DSM2p
