import Mathlib
import Submission.Work.Whitney.TCMDefs
import Submission.Work.Whitney.tcmF_inv_general
import Submission.Work.Whitney.tcmSuccOneAux
import Submission.Work.Whitney.tcmRelCup_natural
import Submission.Work.Whitney.Mn_one_eq_pairDelta
import Submission.Work.Thom.stepDefs
import Submission.Work.Thom.naturalModelClass_punct
import Submission.Work.Thom.capRelCohIsoA
import Submission.Work.Cohomology.h0Evaluation

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The external product of the model classes: definitions

This module carries the *definitions* and the elementary bilinearity of

* `Work.Whitney.Pstep`, the punctured suspension (`jMap (Pstep τ) = step (jMap τ)`), with the
  recursion `Mpun (n+1) = Pstep (Mpun n)`;
* `Work.Whitney.tcmProd`, the external product of two punctured model classes, and
  `Work.Whitney.tcmJ B m n = tcmProd B m n (Mpun m B) (Mpun n B)`.

They are placed here, *upstream* of `Submission/Work/Whitney/tcmCup_step.lean` (which imports this
module and re-exports everything), so that the induction step `Work.Whitney.tcmCup_step` and its
inputs — the rank-one case `tcmJ B n 1 = (-1)^n Mpun (n+1) B` and the associativity of `tcmProd` —
can be stated and proved in modules that do not themselves import `tcmCup_step` (in particular in
modules that the file `tcmCup_step.lean` may in turn import).
-/

namespace Work.Whitney

open Work.Thom

noncomputable section

/-! ## The punctured suspension `Pstep`

`Work.Thom.step` is defined on the *sphere* pair `(B × ℝ^n, Sph B n)`.  Its conjugate under the
isomorphism `jMap : H^*(B×ℝ^n, Punct B n) → H^*(B×ℝ^n, Sph B n)` of the punctured pair with the
sphere pair is the operation used in the derivation, `Pstep`.  (`Mpun n B` is itself a
`Classical.choose` preimage under `jMap`, so this is the same kind of definition; every use goes
through the gauge equation `Pstep_spec`.) -/

noncomputable def Pstep (B : Type) [TopologicalSpace B] (n : ℕ)
    (τ : RelCoh ℤ n (B × EuclideanSpace ℝ (Fin n)) (Punct B n)) :
    RelCoh ℤ (n + 1) (B × EuclideanSpace ℝ (Fin (n + 1))) (Punct B (n + 1)) :=
  (Equiv.ofBijective _ (bijective_jMap B (n + 1) (n + 1))).symm
    (step B n ((relCohMap (ContinuousMap.id (B × EuclideanSpace ℝ (Fin n)))
      (Sph B n) (Punct B n) (mem_Sph_punct B n) ℤ n).hom τ))

/-- **The defining equation of `Pstep`**: it is the `jMap`-conjugate of `Work.Thom.step`. -/
theorem Pstep_spec (B : Type) [TopologicalSpace B] (n : ℕ)
    (τ : RelCoh ℤ n (B × EuclideanSpace ℝ (Fin n)) (Punct B n)) :
    (relCohMap (ContinuousMap.id (B × EuclideanSpace ℝ (Fin (n + 1))))
      (Sph B (n + 1)) (Punct B (n + 1)) (mem_Sph_punct B (n + 1)) ℤ (n + 1)).hom (Pstep B n τ)
      = step B n ((relCohMap (ContinuousMap.id (B × EuclideanSpace ℝ (Fin n)))
          (Sph B n) (Punct B n) (mem_Sph_punct B n) ℤ n).hom τ) :=
  (Equiv.ofBijective _ (bijective_jMap B (n + 1) (n + 1))).apply_symm_apply _

/-- The recursion of `Mpun` in the punctured group: `Mpun (n+1) B = Pstep B n (Mpun n B)`. -/
theorem Mpun_succ (B : Type) [TopologicalSpace B] (n : ℕ) :
    Mpun (n + 1) B = Pstep B n (Mpun n B) := by
  apply (bijective_jMap B (n + 1) (n + 1)).1
  rw [Pstep_spec, Mpun_spec (n + 1) B, Mpun_spec n B]
  rfl

/-- The cap pullback in the exact form of `Work.Thom.stepSph_spec`, as an equality of linear maps
(clean-island copy). -/
theorem capPullback_eq (B : Type) [TopologicalSpace B] (n : ℕ) :
    relCohMap (capMapPairSph B n) (DiscB B n) (SphB B n)
        (CleanA.capMapPairSph_mem_mLower n) ℤ n
      = relCohMap (capMapPairSph B n) (DiscB B n) (SphB B n)
          (fun q hq => by
            have h1 : capMap n (q.2 : EuclideanSpace ℝ (Fin n)) ∈ mLower n :=
              equator_subset_mLower n (capMap_mem_equator n hq)
            simpa [capMapPairSph] using h1) ℤ n :=
  relCohMap_hcongrA _ _ _ _ _ ℤ n

/-- **Uniqueness form of `Work.Thom.stepSph`**: any class whose cap pullback is the disc transfer
of `τ` is `stepSph B n τ`.  (Clean-island copy of the corresponding lemma of
`Submission/Work/Whitney/tcmStep_linear.lean`, which cannot be imported here: see the module
docstring.  The only change is `CleanA.capRelCohIso` in place of `capRelCohIso`.) -/
theorem eq_stepSph (B : Type) [TopologicalSpace B] (n : ℕ)
    (τ : RelCoh ℤ n (B × EuclideanSpace ℝ (Fin n)) (Sph B n))
    (w : RelCoh ℤ n (B × MSph (n + 1)) (SphB B n))
    (h : (relCohMap (capMapPairSph B n) (DiscB B n) (SphB B n)
        (CleanA.capMapPairSph_mem_mLower n) ℤ n).hom w = stepDisc B n τ) :
    w = stepSph B n τ := by
  apply (CleanA.capRelCohIso B n n).1
  rw [capPullback_eq B n, h, ← capPullback_eq B n, stepSph_spec]

/-- `Work.Thom.stepDisc` is additive. -/
theorem stepDisc_add (B : Type) [TopologicalSpace B] (n : ℕ)
    (τ₁ τ₂ : RelCoh ℤ n (B × EuclideanSpace ℝ (Fin n)) (Sph B n)) :
    stepDisc B n (τ₁ + τ₂) = stepDisc B n τ₁ + stepDisc B n τ₂ := by
  simp only [stepDisc]
  exact map_add _ _ _

/-- `Work.Thom.stepDisc` is `ℤ`-linear. -/
theorem stepDisc_zsmul (B : Type) [TopologicalSpace B] (n : ℕ) (c : ℤ)
    (τ : RelCoh ℤ n (B × EuclideanSpace ℝ (Fin n)) (Sph B n)) :
    stepDisc B n (c • τ) = c • stepDisc B n τ := by
  simp only [stepDisc]
  exact map_zsmul _ _ _

/-- **`Work.Thom.stepSph` is additive.** -/
theorem stepSph_add (B : Type) [TopologicalSpace B] (n : ℕ)
    (τ₁ τ₂ : RelCoh ℤ n (B × EuclideanSpace ℝ (Fin n)) (Sph B n)) :
    stepSph B n (τ₁ + τ₂) = stepSph B n τ₁ + stepSph B n τ₂ := by
  refine (eq_stepSph B n (τ₁ + τ₂) (stepSph B n τ₁ + stepSph B n τ₂) ?_).symm
  rw [map_add, stepSph_spec, stepSph_spec, stepDisc_add]

/-- **`Work.Thom.stepSph` is `ℤ`-linear.** -/
theorem stepSph_zsmul (B : Type) [TopologicalSpace B] (n : ℕ) (c : ℤ)
    (τ : RelCoh ℤ n (B × EuclideanSpace ℝ (Fin n)) (Sph B n)) :
    stepSph B n (c • τ) = c • stepSph B n τ := by
  refine (eq_stepSph B n (c • τ) (c • stepSph B n τ) ?_).symm
  rw [map_zsmul, stepSph_spec, stepDisc_zsmul]

/-- **`Work.Thom.step` is `ℤ`-linear in its argument.** -/
theorem step_zsmul (B : Type) [TopologicalSpace B] (n : ℕ) (c : ℤ)
    (τ : RelCoh ℤ n (B × EuclideanSpace ℝ (Fin n)) (Sph B n)) :
    step B n (c • τ) = c • step B n τ := by
  simp only [step, stepSph_zsmul, map_zsmul]

/-- `Work.Thom.step` is additive in its argument. -/
theorem step_add (B : Type) [TopologicalSpace B] (n : ℕ)
    (τ₁ τ₂ : RelCoh ℤ n (B × EuclideanSpace ℝ (Fin n)) (Sph B n)) :
    step B n (τ₁ + τ₂) = step B n τ₁ + step B n τ₂ := by
  simp only [step, stepSph_add, map_add]

/-- **`Pstep` is additive.** -/
theorem Pstep_add (B : Type) [TopologicalSpace B] (n : ℕ)
    (τ₁ τ₂ : RelCoh ℤ n (B × EuclideanSpace ℝ (Fin n)) (Punct B n)) :
    Pstep B n (τ₁ + τ₂) = Pstep B n τ₁ + Pstep B n τ₂ := by
  apply (bijective_jMap B (n + 1) (n + 1)).1
  simp only [Pstep_spec, map_add, step_add]

/-- **`Pstep` is `ℤ`-linear.** -/
theorem Pstep_zsmul (B : Type) [TopologicalSpace B] (n : ℕ) (c : ℤ)
    (τ : RelCoh ℤ n (B × EuclideanSpace ℝ (Fin n)) (Punct B n)) :
    Pstep B n (c • τ) = c • Pstep B n τ := by
  apply (bijective_jMap B (n + 1) (n + 1)).1
  simp only [Pstep_spec, map_zsmul, step_zsmul]

end

/-! ## The external product of punctured classes

`tcmProd B m n a b` is the "external product" of the model classes: pull `a` back along the
projection of `B × (ℝ^m × ℝ^n)` onto the first block, `b` along the projection onto the second
block, cup them with the canonical relative–relative cup, and move the result to `B × ℝ^{m+n}`
along the coordinate identification — into the **punctured** group (`Punct B (m+n)`).

`tcmProd B m n (Mpun m B) (Mpun n B)` is the class whose `jMap`-image is the left hand side of
`tcmCup_step` at `(m,n)`; the two are related by `jMap`, which is injective, so it is harmless to
work in the punctured group.  The derivation of `tcmCup_step` (see the module docstring) uses its
bilinearity (`tcmProd_add_left`, `tcmProd_zsmul_left`, `tcmProd_add_right`, `tcmProd_zsmul_right`,
proved here), associativity, and the suspension rule. -/

/-- The pair condition of the coordinate identification into the *punctured* pair: a point whose
fibre coordinate is non-zero stays in `A ∪ C`. -/
theorem tcmF_inv_mem_punct_union (B : Type) [TopologicalSpace B] (m n : ℕ) :
    ∀ y ∈ Punct B (m + n), Fib.tcmF_inv B m n y ∈ tcmA B m n ∪ tcmC B m n := by
  intro y hy
  rw [tcmA_union_tcmC]
  simp only [Set.mem_ofPred_eq, Fib.tcmF_inv_apply]
  intro h
  exact hy (by
    have h2 := congrArg (tcmSumLin m n) h
    simpa only [ContinuousLinearEquiv.apply_symm_apply, map_zero] using h2)

/-- **The external product of two punctured classes.** -/
noncomputable def tcmProd (B : Type) [TopologicalSpace B] (m n : ℕ)
    (a : RelCoh ℤ m (B × EuclideanSpace ℝ (Fin m)) (Punct B m))
    (b : RelCoh ℤ n (B × EuclideanSpace ℝ (Fin n)) (Punct B n)) :
    RelCoh ℤ (m + n) (B × EuclideanSpace ℝ (Fin (m + n))) (Punct B (m + n)) :=
  (relCohMap (Fib.tcmF_inv B m n) (Punct B (m + n)) (tcmA B m n ∪ tcmC B m n)
    (tcmF_inv_mem_punct_union B m n) ℤ (m + n)).hom
    ((tcmRelCup (tcmA B m n) (tcmC B m n) (isOpen_tcmA B m n) (isOpen_tcmC B m n) m n
      ((relCohMap (tcmPr1 B m n) (tcmA B m n) (Punct B m) (fun x hx => hx) ℤ m).hom a))
      ((relCohMap (tcmPr2 B m n) (tcmC B m n) (Punct B n) (fun x hx => hx) ℤ n).hom b))

/-- The model product class in the punctured group: the external product of the two punctured
model classes.  Its `jMap`-image is the left hand side of `tcmCup_step`. -/
noncomputable abbrev tcmJ (B : Type) [TopologicalSpace B] (m n : ℕ) :
    RelCoh ℤ (m + n) (B × EuclideanSpace ℝ (Fin (m + n))) (Punct B (m + n)) :=
  tcmProd B m n (Mpun m B) (Mpun n B)

/-- `tcmProd` is additive in its first argument. -/
theorem tcmProd_add_left (B : Type) [TopologicalSpace B] (m n : ℕ)
    (a a' : RelCoh ℤ m (B × EuclideanSpace ℝ (Fin m)) (Punct B m))
    (b : RelCoh ℤ n (B × EuclideanSpace ℝ (Fin n)) (Punct B n)) :
    tcmProd B m n (a + a') b = tcmProd B m n a b + tcmProd B m n a' b := by
  simp only [tcmProd, map_add, LinearMap.add_apply]

/-- `tcmProd` is additive in its second argument. -/
theorem tcmProd_add_right (B : Type) [TopologicalSpace B] (m n : ℕ)
    (a : RelCoh ℤ m (B × EuclideanSpace ℝ (Fin m)) (Punct B m))
    (b b' : RelCoh ℤ n (B × EuclideanSpace ℝ (Fin n)) (Punct B n)) :
    tcmProd B m n a (b + b') = tcmProd B m n a b + tcmProd B m n a b' := by
  simp only [tcmProd, map_add]

/-- `tcmProd` is `ℤ`-linear in its second argument. -/
theorem tcmProd_zsmul_right (B : Type) [TopologicalSpace B] (m n : ℕ) (c : ℤ)
    (a : RelCoh ℤ m (B × EuclideanSpace ℝ (Fin m)) (Punct B m))
    (b : RelCoh ℤ n (B × EuclideanSpace ℝ (Fin n)) (Punct B n)) :
    tcmProd B m n a (c • b) = c • tcmProd B m n a b := by
  simp only [tcmProd, map_zsmul]


/-- `tcmProd B m n · b` as an additive map (its additivity is `tcmProd_add_left`). -/
noncomputable def tcmProdAddHom (B : Type) [TopologicalSpace B] (m n : ℕ)
    (b : RelCoh ℤ n (B × EuclideanSpace ℝ (Fin n)) (Punct B n)) :
    RelCoh ℤ m (B × EuclideanSpace ℝ (Fin m)) (Punct B m) →+
      RelCoh ℤ (m + n) (B × EuclideanSpace ℝ (Fin (m + n))) (Punct B (m + n)) :=
  { toFun := fun a => tcmProd B m n a b
    map_zero' := by simp only [tcmProd, map_zero, LinearMap.zero_apply]
    map_add' := fun a a' => tcmProd_add_left B m n a a' b }

@[simp] theorem tcmProdAddHom_apply (B : Type) [TopologicalSpace B] (m n : ℕ)
    (b : RelCoh ℤ n (B × EuclideanSpace ℝ (Fin n)) (Punct B n))
    (a : RelCoh ℤ m (B × EuclideanSpace ℝ (Fin m)) (Punct B m)) :
    tcmProdAddHom B m n b a = tcmProd B m n a b := rfl

/-- `tcmProd` is `ℤ`-linear in its first argument. -/
theorem tcmProd_zsmul_left (B : Type) [TopologicalSpace B] (m n : ℕ) (c : ℤ)
    (a : RelCoh ℤ m (B × EuclideanSpace ℝ (Fin m)) (Punct B m))
    (b : RelCoh ℤ n (B × EuclideanSpace ℝ (Fin n)) (Punct B n)) :
    tcmProd B m n (c • a) b = c • tcmProd B m n a b := by
  simpa only [tcmProdAddHom_apply] using map_zsmul (tcmProdAddHom B m n b) c a

end Work.Whitney
