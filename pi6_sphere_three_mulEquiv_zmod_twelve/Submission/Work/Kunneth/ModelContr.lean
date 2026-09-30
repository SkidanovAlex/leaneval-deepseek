import Mathlib
import Submission.Work.Kunneth.EZAWDefs

/-!
# Acyclicity of the Koszul tensor product of two contracted complexes

This file proves that the Koszul tensor product `tpC C D` of two chain complexes of `ℤ`-modules
which carry a "contraction" (a degree-`+1` map `s` with `d s + s d = 𝟙 - P`, where `P` is a
degree-`0` deficiency operator) is acyclic in positive degrees.  The explicit contracting
homotopy of the tensor product is `H = s ⊗ 1 + P ⊗ t`, and `d H + H d = 𝟙 - P ⊗ Q`, which
vanishes in positive total degrees.

The contraction of the singular chains of the standard simplex `Δ[p]` (from the extra
degeneracy of `Δ[p]` as an augmented simplicial set) is constructed here as well, giving the
acyclicity of the Eilenberg–Zilber model complex `tMod p q = C_*(Δ[p]) ⊗_ℤ C_*(Δ[q])`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct Simplicial

namespace Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

/-! ## 1. Contractions and the deficiency operator -/

/-- The index `(p+1,q)` of total degree `n+1`, attached to the index `(p,q)` of degree `n`. -/
abbrev tpIdxL (n : ℕ) (pq : tpIdx n) : tpIdx (n+1) := ⟨(pq.1.1 + 1, pq.1.2), by omega⟩

/-- The index `(p,q+1)` of total degree `n+1`, attached to the index `(p,q)` of degree `n`. -/
abbrev tpIdxR (n : ℕ) (pq : tpIdx n) : tpIdx (n+1) := ⟨(pq.1.1, pq.1.2 + 1), by omega⟩

/-- A contraction of a chain complex `C` of `ℤ`-modules: degree-`+1` maps `s` together with a
"deficiency" operator `P`, such that `d s + s d = 𝟙 - P` in every degree.  In degree `0` the
term `s (n-1) (d x)` is absent, which is why the degree-`0` identity is stated separately. -/
structure ModelContr (C : ChainComplex (ModuleCat ℤ) ℕ) where
  /-- the degree-`+1` map of the contraction -/
  s : ∀ n, ↥(C.X n) →ₗ[ℤ] ↥(C.X (n+1))
  /-- the deficiency operator, which is zero in positive degrees -/
  P : ∀ n, ↥(C.X n) →ₗ[ℤ] ↥(C.X n)
  /-- the contraction identity in degree `0` -/
  s_zero : ∀ x : ↥(C.X 0), (C.d 1 0).hom (s 0 x) = x - P 0 x
  /-- the contraction identity in positive degrees -/
  s_succ : ∀ m (x : ↥(C.X (m+1))),
    (C.d (m+2) (m+1)).hom (s (m+1) x) + (s m) ((C.d (m+1) m).hom x) = x - P (m+1) x
  /-- the deficiency vanishes in positive degrees -/
  P_succ : ∀ m, P (m+1) = 0
  /-- the deficiency is compatible with the differential -/
  Pd : ∀ p (x : ↥(C.X p)), (C.d p (p-1)).hom (P p x) + P (p-1) ((C.d p (p-1)).hom x) = 0

/-! ## 2. The contracting homotopy of the tensor product -/

section Tensor

variable {C D : ChainComplex (ModuleCat ℤ) ℕ}

/-- **The contracting homotopy of the Koszul tensor product**: `s ⊗ 1 + P ⊗ t`. -/
def modelH (cC : ModelContr C) (cD : ModelContr D) (n : ℕ) :
    tpX C D n →ₗ[ℤ] tpX C D (n+1) :=
  DirectSum.toModule ℤ (tpIdx n) (tpX C D (n+1)) (fun pq =>
    (tpLof C D (n+1) (tpIdxL n pq)).comp (TensorProduct.map (cC.s pq.1.1) LinearMap.id)
      + (tpLof C D (n+1) (tpIdxR n pq)).comp
          (TensorProduct.map (cC.P pq.1.1) (cD.s pq.1.2)))

/-- **The deficiency of the tensor product contraction**: `P ⊗ Q`. -/
def modelQ (cC : ModelContr C) (cD : ModelContr D) (n : ℕ) :
    tpX C D n →ₗ[ℤ] tpX C D n :=
  DirectSum.toModule ℤ (tpIdx n) (tpX C D n) (fun pq =>
    (tpLof C D n pq).comp (TensorProduct.map (cC.P pq.1.1) (cD.P pq.1.2)))

/-- The value of `modelH` on a summand generator. -/
theorem modelH_tmul (cC : ModelContr C) (cD : ModelContr D) (n : ℕ) (pq : tpIdx n)
    (x : ↥(C.X pq.1.1)) (y : ↥(D.X pq.1.2)) :
    modelH cC cD n (tpLof C D n pq (x ⊗ₜ[ℤ] y))
      = tpLof C D (n+1) (tpIdxL n pq) (cC.s pq.1.1 x ⊗ₜ[ℤ] y)
        + tpLof C D (n+1) (tpIdxR n pq) (cC.P pq.1.1 x ⊗ₜ[ℤ] cD.s pq.1.2 y) := by
  have hA : (tpLof C D (n+1) (tpIdxL n pq))
      ((TensorProduct.map (cC.s pq.1.1)
        (LinearMap.id : ↥(D.X pq.1.2) →ₗ[ℤ] ↥(D.X pq.1.2))) (x ⊗ₜ[ℤ] y))
      = (tpLof C D (n+1) (tpIdxL n pq)) (cC.s pq.1.1 x ⊗ₜ[ℤ] y) :=
    congrArg (fun z => (tpLof C D (n+1) (tpIdxL n pq)) z)
      (TensorProduct.map_tmul (cC.s pq.1.1)
        (LinearMap.id : ↥(D.X pq.1.2) →ₗ[ℤ] ↥(D.X pq.1.2)) x y)
  have hB : (tpLof C D (n+1) (tpIdxR n pq))
      ((TensorProduct.map (cC.P pq.1.1) (cD.s pq.1.2)) (x ⊗ₜ[ℤ] y))
      = (tpLof C D (n+1) (tpIdxR n pq)) (cC.P pq.1.1 x ⊗ₜ[ℤ] cD.s pq.1.2 y) :=
    congrArg (fun z => (tpLof C D (n+1) (tpIdxR n pq)) z)
      (TensorProduct.map_tmul (cC.P pq.1.1) (cD.s pq.1.2) x y)
  rw [modelH, DirectSum.toModule_lof, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.comp_apply]
  exact (congrArg (fun z => z + (tpLof C D (n+1) (tpIdxR n pq))
        ((TensorProduct.map (cC.P pq.1.1) (cD.s pq.1.2)) (x ⊗ₜ[ℤ] y))) hA).trans
    (congrArg (fun z => (tpLof C D (n+1) (tpIdxL n pq)) (cC.s pq.1.1 x ⊗ₜ[ℤ] y) + z) hB)

/-- The value of `modelQ` on a summand generator. -/
theorem modelQ_tmul (cC : ModelContr C) (cD : ModelContr D) (n : ℕ) (pq : tpIdx n)
    (x : ↥(C.X pq.1.1)) (y : ↥(D.X pq.1.2)) :
    modelQ cC cD n (tpLof C D n pq (x ⊗ₜ[ℤ] y))
      = tpLof C D n pq (cC.P pq.1.1 x ⊗ₜ[ℤ] cD.P pq.1.2 y) := by
  rw [modelQ, DirectSum.toModule_lof, LinearMap.comp_apply]
  exact congrArg (fun z => (tpLof C D n pq) z)
    (TensorProduct.map_tmul (cC.P pq.1.1) (cD.P pq.1.2) x y)

/-- The zero family is sent to zero by `DirectSum.toModule`. -/
lemma DirectSum.toModule_zero' {ι : Type*} [DecidableEq ι] {M : ι → Type*}
    [(i : ι) → AddCommMonoid (M i)] [(i : ι) → Module ℤ (M i)] {N : Type*}
    [AddCommMonoid N] [Module ℤ N] :
    DirectSum.toModule ℤ ι N (0 : ∀ i, M i →ₗ[ℤ] N) = 0 := by
  refine DirectSum.linearMap_ext ℤ (fun i => ?_)
  ext x
  simp only [LinearMap.comp_apply, DirectSum.toModule_lof, Pi.zero_apply, LinearMap.zero_apply]

/-- The deficiency `P ⊗ Q` vanishes in positive total degree. -/
theorem modelQ_eq_zero (cC : ModelContr C) (cD : ModelContr D) (n : ℕ) :
    modelQ cC cD (n+1) = 0 := by
  rw [modelQ]
  have hzero : (fun pq : tpIdx (n+1) =>
      (tpLof C D (n+1) pq).comp (TensorProduct.map (cC.P pq.1.1) (cD.P pq.1.2)))
      = (0 : ∀ pq : tpIdx (n+1),
          tpSummand C D pq.1.1 pq.1.2 →ₗ[ℤ] tpX C D (n+1)) := by
    funext pq
    show (tpLof C D (n+1) pq).comp (TensorProduct.map (cC.P pq.1.1) (cD.P pq.1.2)) = 0
    apply TensorProduct.ext'
    intro x y
    show (tpLof C D (n+1) pq)
        ((TensorProduct.map (cC.P pq.1.1) (cD.P pq.1.2)) (x ⊗ₜ[ℤ] y)) = 0
    rcases pq with ⟨⟨p, q⟩, hpq⟩
    have h2 : (tpLof C D (n+1) ⟨(p, q), hpq⟩)
        ((TensorProduct.map (cC.P p) (cD.P q)) (x ⊗ₜ[ℤ] y))
        = (tpLof C D (n+1) ⟨(p, q), hpq⟩) (cC.P p x ⊗ₜ[ℤ] cD.P q y) :=
      congrArg (fun z => (tpLof C D (n+1) ⟨(p, q), hpq⟩) z)
        (TensorProduct.map_tmul (cC.P p) (cD.P q) x y)
    rw [h2]
    rcases Nat.eq_zero_or_pos p with hp | hp
    · subst hp
      obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
      simp [cD.P_succ q']
    · obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
      simp [cC.P_succ p']
  rw [hzero, DirectSum.toModule_zero']

end Tensor

/-! ## 3. The contraction of the chains of the standard simplex -/

section StandardSimplex

/-- The extra degeneracy of the standard simplex, as an augmented simplicial set. -/
noncomputable def stdED (p : ℕ) :
    SimplicialObject.Augmented.ExtraDegeneracy (SSet.Augmented.stdSimplex.obj ⦋p⦌) :=
  SSet.Augmented.StandardSimplex.extraDegeneracy ⦋p⦌

/-- The cone map on the `n`-simplices of `Δ[p]`: the extra degeneracy of the standard simplex. -/
noncomputable def stdCone (p n : ℕ) : (SdS p) _⦋n⦌ → (SdS p) _⦋n+1⦌ := (stdED p).s n

/-- The base `0`-simplex of `Δ[p]` (the image of the section of the augmentation). -/
noncomputable def stdPt (p : ℕ) : (SdS p) _⦋0⦌ :=
  (stdED p).s' ((Limits.terminal.from PUnit) PUnit.unit)

/-- **The contraction of the chains of `Δ[p]`** induced by the cone: on the generator of an
`n`-simplex `σ` it is the generator of the coned `(n+1)`-simplex `stdCone p n σ`. -/
noncomputable def stdS (p n : ℕ) :
    ↥((sChain (SdS p)).X n) →ₗ[ℤ] ↥((sChain (SdS p)).X (n+1)) :=
  ((((SdS p).isColimitChainComplexXCofan zz n).desc
    (Cofan.mk ((sChain (SdS p)).X (n+1))
      (fun σ => (SdS p).ιChainComplex (R := zz) (stdCone p n σ)))) :
      ((sChain (SdS p)).X n ⟶ (sChain (SdS p)).X (n+1))).hom

/-- The augmentation `C_0(Δ[p]) → ℤ`: the sum of the coefficients. -/
noncomputable def stdAug (p : ℕ) : ↥((sChain (SdS p)).X 0) →ₗ[ℤ] ℤ :=
  ((((SdS p).isColimitChainComplexXCofan zz 0).desc
    (Cofan.mk zz (fun _ => 𝟙 zz))) : ((sChain (SdS p)).X 0 ⟶ zz)).hom

/-- The base `0`-chain of `Δ[p]`, the generator of the base point `stdPt p`. -/
noncomputable def stdBP (p : ℕ) : ↥((sChain (SdS p)).X 0) :=
  ((SdS p).ιChainComplex (R := zz) (stdPt p)).hom 1

/-- The deficiency operator of the contraction of `C_*(Δ[p])`: the rank-one projection onto the
base point in degree `0`, and zero in positive degrees. -/
noncomputable def stdPl (p : ℕ) (n : ℕ) :
    ↥((sChain (SdS p)).X n) →ₗ[ℤ] ↥((sChain (SdS p)).X n) :=
  match n with
  | 0 => (LinearMap.toSpanSingleton ℤ ↥((sChain (SdS p)).X 0) (stdBP p)).comp (stdAug p)
  | (_ + 1) => 0

/-- The value of `stdS` on the generator of a simplex. -/
theorem stdS_gen (p n : ℕ) (σ : (SdS p) _⦋n⦌) :
    stdS p n (((SdS p).ιChainComplex (R := zz) σ).hom 1)
      = ((SdS p).ιChainComplex (R := zz) (stdCone p n σ)).hom 1 := by
  have h : ((SdS p).ιChainComplex (R := zz) σ) ≫
      (((SdS p).isColimitChainComplexXCofan zz n).desc
        (Cofan.mk ((sChain (SdS p)).X (n+1))
          (fun σ => (SdS p).ιChainComplex (R := zz) (stdCone p n σ))))
      = (SdS p).ιChainComplex (R := zz) (stdCone p n σ) :=
    Cofan.IsColimit.fac _ _ σ
  rw [stdS]
  exact congrArg (fun (φ : (zz ⟶ (sChain (SdS p)).X (n+1))) => φ.hom 1) h

/-- The value of the augmentation on the generator of a `0`-simplex. -/
theorem stdAug_gen (p : ℕ) (σ : (SdS p) _⦋0⦌) :
    stdAug p (((SdS p).ιChainComplex (R := zz) σ).hom 1) = 1 := by
  have h : ((SdS p).ιChainComplex (R := zz) σ) ≫
      (((SdS p).isColimitChainComplexXCofan zz 0).desc (Cofan.mk zz (fun _ => 𝟙 zz)))
      = 𝟙 zz :=
    Cofan.IsColimit.fac _ _ σ
  rw [stdAug]
  exact congrArg (fun (φ : (zz ⟶ zz)) => φ.hom 1) h

/-- `stdPl` is zero in positive degrees. -/
theorem stdPl_succ (p m : ℕ) : stdPl p (m+1) = 0 := rfl

/-- The value of `stdPl` in degree zero. -/
theorem stdPl_zero_apply (p : ℕ) (x : ↥((sChain (SdS p)).X 0)) :
    stdPl p 0 x
      = (LinearMap.toSpanSingleton ℤ ↥((sChain (SdS p)).X 0) (stdBP p)) (stdAug p x) := by
  simp only [stdPl, LinearMap.comp_apply]


end StandardSimplex

end

end Work.Kunneth
