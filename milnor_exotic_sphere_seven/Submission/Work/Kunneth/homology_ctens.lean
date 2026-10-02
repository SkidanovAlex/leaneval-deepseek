import Mathlib
import Submission.Work.Kunneth.TensorCo
import Submission.Work.Kunneth.ctensAux
import Submission.Work.Kunneth.homologyIsoKerQuotRange
import Submission.Work.Kunneth.flatKerQuotRange

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The homology of `ctens A T` with flat coefficients

This file proves

`Work.Kunneth.homology_ctens`:
`H^n(ctens A T) ≅ ⨁_{p+q=n} H^p(A) ⊗ T q`

for a cochain complex `A` of `ℤ`-modules and a family `T` of flat `ℤ`-modules.

The proof has three ingredients, each of which is proved here:

* `ctens A T` is the direct sum, over the second bidegree `q`, of the coefficient complexes
  `A ⊗ T q`.  Concretely, `ker (ctensD A T n)` is the product of the kernels
  `ker (dTensOut A T p q)` (`ker_ctensD`) and the image of the incoming differential is the product
  of the images (`range_ctensDIn`).
* hence `H^n (ctens A T)` is the product of the groups `ker (d ⊗ 1) ⧸ im (d ⊗ 1)` of the
  coefficient complexes (`ctensHQuot_iso_prod`).
* and `ker (d ⊗ 1) ⧸ im (d ⊗ 1) ≅ H^p(A) ⊗ T q` because `T q` is flat
  (`Work.Kunneth.flatKerQuotRange`), while `H^p(A)` is the concrete quotient
  `ker d ⧸ im d` (`Work.Kunneth.homologyIsoKerQuotRange`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct

namespace Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

variable (A : CochainComplex (ModuleCat ℤ) ℕ) (T : ℕ → ModuleCat ℤ)

/-! ## Elementary facts about the incoming differential -/

/-- The incoming differential in degree `0` is zero. -/
theorem dTensIn_zero (q : ℕ) : dTensIn A T 0 q = 0 := by
  have h : A.d 0 0 = 0 := HomologicalComplex.shape A 0 0 (by simp [ComplexShape.up_Rel])
  rw [dTensIn, show (0 : ℕ) - 1 = 0 from rfl, h, ModuleCat.hom_zero]
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a t => rw [LinearMap.rTensor_tmul]; simp; try rfl
  | add x y hx hy => rw [map_add, hx, hy, map_add]

/-- Its range in degree `0` is trivial. -/
theorem range_dTensIn_zero (q : ℕ) : (dTensIn A T 0 q).range = ⊥ := by
  rw [dTensIn_zero A T q, LinearMap.range_zero]

/-- The range of the incoming differential at the "extra" bidegree `(0, n+1)` is trivial. -/
theorem range_dTensIn_tpZero (n : ℕ) :
    (dTensIn A T (tpZero n).1.1 (tpZero n).1.2).range = ⊥ :=
  range_dTensIn_zero A T (n + 1)

/-- In degree `0` the "product over the summands" description is trivial when the single
summand is trivial. -/
theorem ctensProdSub_zero_eq_bot
    {P : ∀ pq : tpIdx 0, Submodule ℤ (ctensSummand A T pq.1.1 pq.1.2)}
    (h : P ⟨(0, 0), rfl⟩ = ⊥) : ctensProdSub A T 0 P = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [mem_ctensProdSub] at hx
  have hx' : x ⟨(0, 0), rfl⟩ = 0 := by
    have := hx ⟨(0, 0), rfl⟩
    rwa [h, Submodule.mem_bot] at this
  rw [Submodule.mem_bot]
  apply DirectSum.ext
  intro j
  have h1 : j.1.1 = 0 := by have := j.2; omega
  have h2 : j.1.2 = 0 := by have := j.2; omega
  have hj : j = ⟨(0, 0), rfl⟩ := Subtype.ext (Prod.ext h1 h2)
  rw [hj, hx']
  simp

/-! ## The kernel of `ctensD` -/

/-- The kernel of the differential of `ctens A T` in degree `n` is the product of the kernels of
the outgoing differentials of the summands. -/
theorem ker_ctensD (n : ℕ) :
    (ctensD A T n).ker
      = ctensProdSub A T n (fun pq => (dTensOut A T pq.1.1 pq.1.2).ker) := by
  ext x
  rw [mem_ctensProdSub, LinearMap.mem_ker]
  constructor
  · intro hx pq
    simpa [hx] using (ctensD_apply_step A T n x pq).symm
  · intro hx
    apply DirectSum.ext
    intro j
    by_cases hj : j.1.1 = 0
    · rw [eq_tpZero_of_fst_eq_zero hj, ctensD_apply_zero]
      simp
    · have hj1 : 1 ≤ j.1.1 := by omega
      obtain ⟨pq, rfl⟩ :
          ∃ pq : tpIdx n, j = tpStep n pq :=
        ⟨⟨(j.1.1 - 1, j.1.2), by omega⟩, eq_tpStep_of_pos hj1⟩
      rw [ctensD_apply_step]
      exact hx pq

/-- Membership in the kernel of the differential of `ctens`, componentwise. -/
theorem mem_ker_ctensD_iff (n : ℕ) (x : ctensX A T n) :
    x ∈ (ctensD A T n).ker ↔ ∀ pq, x pq ∈ (dTensOut A T pq.1.1 pq.1.2).ker := by
  rw [ker_ctensD A T n, mem_ctensProdSub]

/-! ## The range of the differentials of `ctens` -/

/-- The range of the differential `ctensD A T n` is the product of the ranges of the incoming
differentials of the summands. -/
theorem range_ctensD (n : ℕ) :
    (ctensD A T n).range
      = ctensProdSub A T (n + 1) (fun j => (dTensIn A T j.1.1 j.1.2).range) := by
  ext x
  rw [mem_ctensProdSub, LinearMap.mem_range]
  constructor
  · rintro ⟨y, rfl⟩ j
    by_cases hj : j.1.1 = 0
    · rw [eq_tpZero_of_fst_eq_zero hj, ctensD_apply_zero]
      exact Submodule.zero_mem _
    · have hj1 : 1 ≤ j.1.1 := by omega
      obtain ⟨pq, rfl⟩ :
          ∃ pq : tpIdx n, j = tpStep n pq :=
        ⟨⟨(j.1.1 - 1, j.1.2), by omega⟩, eq_tpStep_of_pos hj1⟩
      rw [ctensD_apply_step]
      exact ⟨y pq, rfl⟩
  · intro hx
    have hmem : ∀ j : tpIdx (n + 1), 1 ≤ j.1.1 →
        ∃ w : ctensSummand A T (j.1.1 - 1) j.1.2, dTensIn A T j.1.1 j.1.2 w = x j := by
      intro j _
      exact hx j
    refine ⟨ctensMk A T n (fun pq => Classical.choose (hmem (tpStep n pq) (by simp [tpStep]))),
      ?_⟩
    apply DirectSum.ext
    intro j
    by_cases hj : j.1.1 = 0
    · rw [eq_tpZero_of_fst_eq_zero hj, ctensD_apply_zero]
      have h := hx (tpZero n)
      rw [range_dTensIn_tpZero A T n, Submodule.mem_bot] at h
      exact h.symm
    · have hj1 : 1 ≤ j.1.1 := by omega
      obtain ⟨pq, rfl⟩ :
          ∃ pq : tpIdx n, j = tpStep n pq :=
        ⟨⟨(j.1.1 - 1, j.1.2), by omega⟩, eq_tpStep_of_pos hj1⟩
      rw [ctensD_apply_step, ctensMk_apply]
      exact Classical.choose_spec (hmem (tpStep n pq) (by simp [tpStep]))

/-- The range of the incoming differential of `ctens A T` in degree `n` is the product of the
ranges of the incoming differentials of the summands. -/
theorem range_ctensDIn (n : ℕ) :
    (ctensDIn A T n).range
      = ctensProdSub A T n (fun pq => (dTensIn A T pq.1.1 pq.1.2).range) := by
  match n with
  | 0 =>
    rw [ctensDIn_zero, LinearMap.range_zero]
    symm
    exact ctensProdSub_zero_eq_bot A T (range_dTensIn_zero A T 0)
  | (m + 1) =>
    rw [ctensDIn_succ]
    exact range_ctensD A T m

/-! ## The quotient description of `H^n (ctens A T)` -/

/-- The concrete `H^n` of `ctens A T`: cycles modulo boundaries. -/
def ctensHQuot (n : ℕ) : ModuleCat ℤ :=
  ModuleCat.of ℤ (LinearMap.ker (ctensD A T n) ⧸
    (LinearMap.range (ctensDIn A T n)).comap (LinearMap.ker (ctensD A T n)).subtype)

/-- The submodule of the cycles in bidegree `pq` coming from the incoming differential. -/
def cycBnd (n : ℕ) (pq : tpIdx n) :
    Submodule ℤ ↥(LinearMap.ker (dTensOut A T pq.1.1 pq.1.2)) :=
  (LinearMap.range (dTensIn A T pq.1.1 pq.1.2)).comap
    (LinearMap.ker (dTensOut A T pq.1.1 pq.1.2)).subtype

/-- The "raw" quotient of the cycles in bidegree `pq`. -/
abbrev cycQuot (n : ℕ) (pq : tpIdx n) : Type :=
  ↥(LinearMap.ker (dTensOut A T pq.1.1 pq.1.2)) ⧸ cycBnd A T n pq

/-- The projection of the cycles of `ctens A T` onto the cycles of one summand. -/
def cycProj (n : ℕ) (pq : tpIdx n) :
    ↥(LinearMap.ker (ctensD A T n)) →ₗ[ℤ] ↥(LinearMap.ker (dTensOut A T pq.1.1 pq.1.2)) where
  toFun x := ⟨(x : ctensX A T n) pq, (mem_ker_ctensD_iff A T n (x : ctensX A T n)).mp x.2 pq⟩
  map_add' x y := by
    apply Subtype.ext
    simp
  map_smul' c x := by
    apply Subtype.ext
    exact DirectSum.smul_apply c (x : ctensX A T n) pq

/-- The value of the projection, as an element of the ambient module. -/
theorem cycProj_val (n : ℕ) (pq : tpIdx n) (x : ↥(LinearMap.ker (ctensD A T n))) :
    ((cycProj A T n pq x : ↥(LinearMap.ker (dTensOut A T pq.1.1 pq.1.2)))
      : ↥(A.X pq.1.1 ⊗ T pq.1.2)) = (x : ctensX A T n) pq := rfl

/-- The same statement with the canonical inclusion of the submodule written out. -/
theorem cycProj_subtype (n : ℕ) (pq : tpIdx n) (x : ↥(LinearMap.ker (ctensD A T n))) :
    (LinearMap.ker (dTensOut A T pq.1.1 pq.1.2)).subtype (cycProj A T n pq x)
      = (x : ctensX A T n) pq := rfl

/-- The projection of the cycles onto the product of the quotients of the summands' cycles. -/
def cycToProd (n : ℕ) :
    ↥(LinearMap.ker (ctensD A T n)) →ₗ[ℤ] (∀ pq : tpIdx n, cycQuot A T n pq) :=
  LinearMap.pi (fun pq => (Submodule.mkQ (cycBnd A T n pq)).comp (cycProj A T n pq))

theorem cycToProd_apply (n : ℕ) (x : ↥(LinearMap.ker (ctensD A T n))) (pq : tpIdx n) :
    cycToProd A T n x pq
      = (Submodule.mkQ (cycBnd A T n pq)) (cycProj A T n pq x) := rfl

/-- The kernel of the projection is exactly the submodule of boundaries. -/
theorem ker_cycToProd (n : ℕ) :
    (cycToProd A T n).ker
      = (LinearMap.range (ctensDIn A T n)).comap (LinearMap.ker (ctensD A T n)).subtype := by
  ext x
  rw [LinearMap.mem_ker, funext_iff, Submodule.mem_comap, range_ctensDIn, mem_ctensProdSub]
  constructor
  · intro h pq
    have h' : cycToProd A T n x pq = 0 := by simpa using h pq
    rw [cycToProd_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, cycBnd,
      Submodule.mem_comap, cycProj_subtype] at h'
    exact h'
  · intro hx pq
    show cycToProd A T n x pq = 0
    rw [cycToProd_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, cycBnd,
      Submodule.mem_comap, cycProj_subtype]
    exact hx pq

/-- The projection is surjective. -/
theorem cycToProd_surjective (n : ℕ) : Function.Surjective (cycToProd A T n) := by
  intro f
  choose g hg using fun pq => Submodule.mkQ_surjective (cycBnd A T n pq) (f pq)
  have hz : ctensMk A T n (fun pq => (g pq : ↥(A.X pq.1.1 ⊗ T pq.1.2)))
      ∈ LinearMap.ker (ctensD A T n) := by
    rw [mem_ker_ctensD_iff]
    intro pq
    rw [ctensMk_apply]
    exact (g pq).2
  refine ⟨⟨ctensMk A T n (fun pq => (g pq : ↥(A.X pq.1.1 ⊗ T pq.1.2))), hz⟩, ?_⟩
  funext pq
  show cycToProd A T n ⟨ctensMk A T n (fun pq => (g pq : ↥(A.X pq.1.1 ⊗ T pq.1.2))), hz⟩ pq
    = f pq
  rw [cycToProd_apply]
  have hsub : cycProj A T n pq ⟨ctensMk A T n (fun pq => (g pq : ↥(A.X pq.1.1 ⊗ T pq.1.2))),
      hz⟩ = g pq := by
    apply Subtype.ext
    rw [cycProj_val, ctensMk_apply]
  rw [hsub]
  exact hg pq

/-- `H^n (ctens A T)` is the product, over the bidegrees `p + q = n`, of
`ker (d ⊗ 1) ⧸ im (d ⊗ 1)`. -/
theorem ctensHQuot_iso_prod (n : ℕ) :
    Nonempty (ctensHQuot A T n ≅
      ModuleCat.of ℤ (∀ pq : tpIdx n, ↥(kerQuotTens A T pq.1.1 pq.1.2))) := by
  refine ⟨Iso.trans (LinearEquiv.toModuleIso
      ((Submodule.quotEquivOfEq _ _ (ker_cycToProd A T n).symm).trans
        (LinearMap.quotKerEquivOfSurjective (cycToProd A T n) (cycToProd_surjective A T n))))
    (LinearEquiv.toModuleIso (LinearEquiv.piCongrRight (fun pq => ?_)))⟩
  exact { toFun := id, invFun := id, left_inv := fun x => rfl, right_inv := fun x => rfl,
          map_add' := fun x y => rfl, map_smul' := fun c x => rfl }

/-! ## The assembly -/

/-- The `ℤ`-linear equivalence underlying an isomorphism of `ℤ`-modules. -/
def isoToLinearEquiv {X Y : ModuleCat ℤ} (e : X ≅ Y) : ↥X ≃ₗ[ℤ] ↥Y where
  toLinearMap := e.hom.hom
  invFun := e.inv.hom
  left_inv x := by
    have h := congrArg ModuleCat.Hom.hom e.hom_inv_id
    simp only [ModuleCat.hom_comp, ModuleCat.hom_id] at h
    exact LinearMap.congr_fun h x
  right_inv x := by
    have h := congrArg ModuleCat.Hom.hom e.inv_hom_id
    simp only [ModuleCat.hom_comp, ModuleCat.hom_id] at h
    exact LinearMap.congr_fun h x

/-- The differentials of `ctens A T` are `ctensD` and `ctensDIn`, so the concrete descriptions
of the homology agree. -/
theorem homologyQuot_ctens_eq (n : ℕ) : homologyQuot (ctens A T) n = ctensHQuot A T n := by
  rw [homologyQuot, ctensHQuot, ctens_d A T n, ctens_d_in A T n]
  rfl

/-- The product, over the bidegrees `p + q = n`, of the flat base change isomorphisms. -/
theorem prod_kerQuotTens_iso (hT : ∀ q, Module.Flat ℤ ↥(T q)) (n : ℕ) :
    Nonempty (ModuleCat.of ℤ (∀ pq : tpIdx n, ↥(kerQuotTens A T pq.1.1 pq.1.2)) ≅
      ModuleCat.of ℤ (∀ pq : tpIdx n, ↥(homologyTensor A T pq.1.1 pq.1.2))) :=
  ⟨LinearEquiv.toModuleIso (LinearEquiv.piCongrRight (fun pq =>
    isoToLinearEquiv (flatKerQuotRange A T pq.1.2 pq.1.1 (hT pq.1.2)).some))⟩

/-- The product `∏_{p+q=n} H^p(A) ⊗ T q` is `ctensH A T n`. -/
theorem prod_homologyTensor_eq (n : ℕ) :
    ModuleCat.of ℤ (∀ pq : tpIdx n, ↥(homologyTensor A T pq.1.1 pq.1.2)) = ctensH A T n := rfl

theorem homology_ctens (A : CochainComplex (ModuleCat ℤ) ℕ) (T : ℕ → ModuleCat ℤ)
    (hT : ∀ q, Module.Flat ℤ ↥(T q)) (n : ℕ) :
    Nonempty (CategoryTheory.Iso ((Work.Kunneth.ctens A T).homology n)
      (Work.Kunneth.ctensH A T n)) :=
  ⟨((homologyIsoKerQuotRange (ctens A T) n).some.trans
    ((eqToIso (homologyQuot_ctens_eq A T n)).trans
      ((ctensHQuot_iso_prod A T n).some.trans
        (((prod_kerQuotTens_iso A T hT n).some).trans
          (eqToIso (prod_homologyTensor_eq A T n))))))⟩

end

end Work.Kunneth
