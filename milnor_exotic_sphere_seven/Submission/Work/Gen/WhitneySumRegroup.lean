import Mathlib
import Submission.Work.Whitney.Basic

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 800000
set_option linter.style.haveILetI false

/-!
# The regrouping of `whitneySum Z (ε²)` as `whitneySum (whitneySum Z ε¹) ε¹`

`Work.Whitney.whitneySum Z (trivial ℂ (Fin 2) ι₀)` and
`Work.Whitney.whitneySum (whitneySum Z (trivial ℂ (Fin 1) ι₁)) (trivial ℂ (Fin 1) ι₂)` are two
presentations of `Z ⊕ ε¹ ⊕ ε¹`.  By `Work.Whitney.whitneySum_coordChange` their transition
functions are the transports of the block-diagonal `diag(g, 1, 1)` (`g` the transition of `Z`) along
the structure maps `sumFibreC`: the flat one along `α = sumFibreC m 2`, the nested one along `γ`
applied to the `β`-transport of `diag(g,1)`, with `β = sumFibreC m 1`, `γ = sumFibreC (m+1) 1`.

The **regrouping gauge** `Work.Gen.regroupGauge m` of this file is the constant linear equivalence
that shuffles `ℂ^{m+2} ≅ ℂ^m × ℂ²` into `ℂ^{(m+1)+1} ≅ (ℂ^m × ℂ¹) × ℂ¹`, i.e. the one that turns
`diag(g,1,1)` into `diag(diag(g,1),1)`.  With it the two presentations are gauge-equivalent, which
gives the regrouping isomorphism and hence `c_j(Z ⊕ ε²) = c_j(Z)` in the `whitneySum` presentation
(`Work.Gen.chernClass_whitneySum_trivial_two`).
-/

namespace Work.Gen

open Work.TangentClasses

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι ι₀ ι₁ ι₂ : Type} [Inhabited ι₀] [Inhabited ι₁]
  [Inhabited ι₂] [Fintype ι] [Fintype ι₀] [Fintype ι₁] [Fintype ι₂] {m : ℕ}

/-- **The regrouping gauge**: the constant linear equivalence between the standard fibres of
`Z ⊕ ε²` (flat presentation) and `(Z ⊕ ε¹) ⊕ ε¹` (nested presentation). -/
noncomputable def regroupGauge (m : ℕ) :
    EuclideanSpace ℂ (Fin (m + 2)) ≃L[ℂ] EuclideanSpace ℂ (Fin ((m + 1) + 1)) :=
  let e₂ : (EuclideanSpace ℂ (Fin m) × EuclideanSpace ℂ (Fin 2)) ≃L[ℂ]
      (EuclideanSpace ℂ (Fin m) × (EuclideanSpace ℂ (Fin 1) × EuclideanSpace ℂ (Fin 1))) :=
    (ContinuousLinearEquiv.refl ℂ (EuclideanSpace ℂ (Fin m))).prodCongr
      (Work.Whitney.sumFibreC 1 1).symm
  let e₃ : (EuclideanSpace ℂ (Fin m) × (EuclideanSpace ℂ (Fin 1) × EuclideanSpace ℂ (Fin 1))) ≃L[ℂ]
      ((EuclideanSpace ℂ (Fin m) × EuclideanSpace ℂ (Fin 1)) × EuclideanSpace ℂ (Fin 1)) :=
    (ContinuousLinearEquiv.prodAssoc ℂ (EuclideanSpace ℂ (Fin m)) (EuclideanSpace ℂ (Fin 1))
      (EuclideanSpace ℂ (Fin 1))).symm
  let e₄ : ((EuclideanSpace ℂ (Fin m) × EuclideanSpace ℂ (Fin 1)) × EuclideanSpace ℂ (Fin 1)) ≃L[ℂ]
      (EuclideanSpace ℂ (Fin (m + 1)) × EuclideanSpace ℂ (Fin 1)) :=
    (Work.Whitney.sumFibreC m 1).prodCongr (ContinuousLinearEquiv.refl ℂ (EuclideanSpace ℂ (Fin 1)))
  (Work.Whitney.sumFibreC m 2).symm.trans
    (e₂.trans (e₃.trans (e₄.trans (Work.Whitney.sumFibreC (m + 1) 1))))

/-- The inverse laws of `Work.Gen.regroupGauge`. -/
theorem regroupGauge_comp (m : ℕ) :
    ((regroupGauge m).symm.toContinuousLinearMap).comp
        (regroupGauge m).toContinuousLinearMap = 1 := by
  ext x i
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearMap.one_apply] using
    congrArg (fun w : EuclideanSpace ℂ (Fin ((m + 1) + 1)) => w.ofLp i)
      ((regroupGauge m).symm_apply_apply x)

theorem regroupGauge_symm_comp (m : ℕ) :
    ((regroupGauge m).toContinuousLinearMap).comp
        (regroupGauge m).symm.toContinuousLinearMap = 1 := by
  ext x i
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearMap.one_apply] using
    congrArg (fun w : EuclideanSpace ℂ (Fin (m + 2)) => w.ofLp i)
      ((regroupGauge m).apply_symm_apply x)

/-! ## The base sets of the two presentations are those of `Z` -/

/-- The trivial core has all base sets `univ`. -/
@[simp] theorem trivialVectorBundleCore_baseSet (R : Type*) [NontriviallyNormedField R]
    {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace R F]
    {ι : Type} [Inhabited ι] (i : ι) :
    (trivialVectorBundleCore R B F ι).baseSet i = Set.univ := rfl

theorem whitneySum_triv_two_baseSet (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (p : ι × ι₀) :
    (Work.Whitney.whitneySum Z
      (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 2)) ι₀)).baseSet p
      = Z.baseSet p.1 := by
  rw [Work.Whitney.whitneySum_baseSet, trivialVectorBundleCore_baseSet, Set.inter_univ]

theorem whitneySum_triv_two_nested_baseSet
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (p : (ι × ι₁) × ι₂) :
    (Work.Whitney.whitneySum
      (Work.Whitney.whitneySum Z
        (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₁))
      (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₂)).baseSet p
      = Z.baseSet p.1.1 := by
  rw [Work.Whitney.whitneySum_baseSet, Work.Whitney.whitneySum_baseSet,
    trivialVectorBundleCore_baseSet, trivialVectorBundleCore_baseSet, Set.inter_univ,
    Set.inter_univ]


/-! ## The conjugacy of the two transition functions -/

/-- The trivial core has identically the identity transition function. -/
@[simp] theorem trivialVectorBundleCore_coordChange (R : Type*) [NontriviallyNormedField R]
    {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace R F]
    {ι : Type} [Inhabited ι] (i j : ι) (b : B) :
    (trivialVectorBundleCore R B F ι).coordChange i j b = 1 := rfl

/-! ## The juggling lemmas of the block shuffle

`prodAssoc_symm_conj` (proved below) is the first of the two juggling lemmas: the associativity
equivalence conjugates the block diagonal `T \u00d7 (1 \u00d7 1)` to `(T \u00d7 1) \u00d7 1`.

The second is `e\u2082 \u2218 (T \u00d7 1) \u2218 e\u2082\u207b\u00b9 = T \u00d7 1` with `e\u2082 = 1 \u00d7 (sumFibreC 1 1)\u207b\u00b9` (the shuffle
`\u2102\u00b2 \u2243 \u2102\u00b9 \u00d7 \u2102\u00b9` acts trivially on a block diagonal because the trivial slot carries the
identity).  Its proof reduces, after `ContinuousLinearEquiv.coe_prodCongr`, to the two `\u2243L` facts
`sumFibreC 1 1`.symm.symm `= sumFibreC 1 1` and `e (e.symm w) = w` on the middle slot, which were not
found by `simp only` in the pass that closed the first lemma \u2014 a `simp`-config or an explicit
`rw`-chain is now closed below (`prodCongr_sumFibreC_conj`).
-/

/-- **First juggling lemma**: the associativity equivalence conjugates the block diagonal
`T \u00d7 (1 \u00d7 1)` on `\u2102^m \u00d7 (\u2102^1 \u00d7 \u2102^1)` to the block diagonal `(T \u00d7 1) \u00d7 1`. -/
theorem prodAssoc_symm_conj (m : ℕ)
    (T : EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m)) :
    (((ContinuousLinearEquiv.prodAssoc ℂ (EuclideanSpace ℂ (Fin m)) (EuclideanSpace ℂ (Fin 1))
        (EuclideanSpace ℂ (Fin 1))).symm).toContinuousLinearMap).comp
      ((T.prodMap ((1 : EuclideanSpace ℂ (Fin 1) →L[ℂ] EuclideanSpace ℂ (Fin 1)).prodMap
          (1 : EuclideanSpace ℂ (Fin 1) →L[ℂ] EuclideanSpace ℂ (Fin 1)))).comp
        (((ContinuousLinearEquiv.prodAssoc ℂ (EuclideanSpace ℂ (Fin m)) (EuclideanSpace ℂ (Fin 1))
          (EuclideanSpace ℂ (Fin 1))).symm).symm).toContinuousLinearMap)
    = (T.prodMap (1 : EuclideanSpace ℂ (Fin 1) →L[ℂ] EuclideanSpace ℂ (Fin 1))).prodMap
        (1 : EuclideanSpace ℂ (Fin 1) →L[ℂ] EuclideanSpace ℂ (Fin 1)) := by
  refine ContinuousLinearMap.ext (fun v => ?_)
  obtain ⟨⟨x, y⟩, z⟩ := v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  rfl



/-- **Second juggling lemma**: the shuffle `sumFibreC 1 1` (splitting `ℂ²` as `ℂ^1 × ℂ^1`)
conjugates the block diagonal `T × 1` on `ℂ^m × ℂ²` to `T × 1` on `ℂ^m × (ℂ^1 × ℂ^1)`: the
trivial slot carries the identity, so the shuffle cancels.

Proof shape (learned the hard way, like `prodAssoc_symm_conj`): `ContinuousLinearMap.ext` with an
explicit pair, then the `rw`-chain `prodCongr_symm` → (`simp only` for `prodCongr_apply`) →
`symm_symm` → the `rfl`-level middle-slot projection fact → `symm_apply_apply` →
`refl_symm`/`refl_apply`, closing with `rfl`.  In particular `apply_symm_apply` is the *wrong*
direction here (`σ` appears as `σ.symm` on the outside), and no `simp` lemma unfolds the projections of a
`prodMap`-application: the projection has to be rewritten by a `rfl`-lemma whose shape is exactly the
goal's. -/
theorem prodCongr_sumFibreC_conj (m : ℕ)
    (T : EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m)) :
    (((ContinuousLinearEquiv.refl ℂ (EuclideanSpace ℂ (Fin m))).prodCongr
        (Work.Whitney.sumFibreC 1 1).symm).toContinuousLinearMap).comp
      ((T.prodMap (1 : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2))).comp
        (((ContinuousLinearEquiv.refl ℂ (EuclideanSpace ℂ (Fin m))).prodCongr
          (Work.Whitney.sumFibreC 1 1).symm).symm).toContinuousLinearMap)
    = T.prodMap (1 : EuclideanSpace ℂ (Fin 1) × EuclideanSpace ℂ (Fin 1) →L[ℂ]
        EuclideanSpace ℂ (Fin 1) × EuclideanSpace ℂ (Fin 1)) := by
  refine ContinuousLinearMap.ext (fun v => ?_)
  obtain ⟨x, w⟩ := v
  rw [ContinuousLinearEquiv.prodCongr_symm]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.prodCongr_apply]
  rw [ContinuousLinearEquiv.symm_symm]
  have hsnd : ((T.prodMap (1 : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)))
      ((ContinuousLinearEquiv.refl ℂ (EuclideanSpace ℂ (Fin m))).symm x,
        (Work.Whitney.sumFibreC 1 1) w)).2
      = (Work.Whitney.sumFibreC 1 1) w := rfl
  rw [hsnd, ContinuousLinearEquiv.symm_apply_apply]
  simp only [ContinuousLinearEquiv.refl_symm, ContinuousLinearEquiv.refl_apply]
  rfl

/-! ## The remaining step: the conjugacy, with the reduction verified

The conjugacy `regroupGauge_conj` (the transition function of `whitneySum Z (ε²)` is carried to
that of `whitneySum (whitneySum Z ε¹) ε¹` by `regroupGauge`) reduces by the following chain, which
**typechecks** (verified in this stretch; the residual goal is the block-shuffle identity below):

1. `rw [Work.Whitney.whitneySum_coordChange, Work.Whitney.whitneySum_coordChange,
   Work.Whitney.whitneySum_coordChange]` — the outer, inner and flat transitions;
2. `simp only [trivialVectorBundleCore_coordChange]` — the trivial summands' transitions are `1`;
3. `unfold regroupGauge` then
   `simp only [ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.coe_coe,
   ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_assoc]` — the gauge becomes
   `γ ∘ e₄ ∘ e₃ ∘ e₂ ∘ α⁻¹` (with `α = sumFibreC m 2`, `β = sumFibreC m 1`,
   `γ = sumFibreC (m+1) 1`, `e₂ = 1 × (sumFibreC 1 1)⁻¹`, `e₃ = (prodAssoc …).symm`, `e₄ = β × 1`),

and the residual goal's head is `γ ∘ₛₗ …`, i.e. exactly the block-shuffle identity below.

-/

/-! ## The remaining step: the block-shuffle identity

The conjugacy of the two transition functions is *reduced* (verified by hand and in the unclosed
goal of this file's development) to the following identity of continuous linear maps, in the
notation `\u03b1 = sumFibreC m 2`, `\u03b2 = sumFibreC m 1`, `\u03b3 = sumFibreC (m+1) 1`,
`e\u2082 = (1 \u00d7 (sumFibreC 1 1)\u207b\u00b9)`, `e\u2083 = (prodAssoc \u2102 \u2102^m \u2102\u00b9 \u2102\u00b9).symm`,
`e\u2084 = (sumFibreC m 1) \u00d7 1`, `g = (Z.coordChange i i' b)`, and `regroupGauge m` the composite
`\u03b1\u207b\u00b9 \u226b e\u2082 \u226b e\u2083 \u226b e\u2084 \u226b \u03b3` (in the direction `\u2102^{m+2} \u2192 \u2102^{(m+1)+1}`):

  `\u03b3 \u2218 (((\u03b2 \u2218 (g \u00d7 1) \u2218 \u03b2\u207b\u00b9) \u00d7 1) \u2218 \u03b3\u207b\u00b9 \u2218 regroupGauge m`
    `= regroupGauge m \u2218 \u03b1 \u2218 (g \u00d7 1) \u2218 \u03b1\u207b\u00b9`.

Both sides are conjugates of `diag(g,1,1)`; the shuffle cancels because the trivial slot carries the
identity, so the two ingredients are the two juggling lemmas

* `e\u2083 \u2218 (T \u00d7 1) \u2218 e\u2083\u207b\u00b9 = (T \u00d7 1) \u00d7 1` (associativity of a block-diagonal),
* `e\u2082 \u2218 (T \u00d7 1) \u2218 e\u2082\u207b\u00b9 = T \u00d7 1` (the `Fin 2 \u2243 Fin 1 \u00d7 Fin 1` split acts trivially on a block
  diagonal),

both provable by `Prod.ext`-style component reasoning (or by the `prodMap`-composition laws).  With
the conjugacy, the `BundleIso` is assembled as in
`Work.Whitney.nonempty_bundleIso_sumEps_whitneySum` (a constant gauge: `hom := fun _ => ...`,
`left_inv`/`right_inv` from the gauge laws, and the two `ContinuousOn` chart expressions from
`trivialVectorBundleCore_baseSet` and the conjugacy), giving the regrouping isomorphism and hence
`Work.Gen.chernClass_whitneySum_trivial_two`. -/

end


/-- **Rearranged form of the second juggling lemma** (the form the conjugacy consumes):
`e₂` commutes with a block diagonal, `e₂ ∘ (T × 1) = (T × 1) ∘ e₂`. -/
theorem prodCongr_sumFibreC_comm (m : ℕ)
    (T : EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m)) :
    (((ContinuousLinearEquiv.refl ℂ (EuclideanSpace ℂ (Fin m))).prodCongr
        (Work.Whitney.sumFibreC 1 1).symm).toContinuousLinearMap).comp
      (T.prodMap (1 : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)))
    = (T.prodMap (1 : EuclideanSpace ℂ (Fin 1) × EuclideanSpace ℂ (Fin 1) →L[ℂ]
        EuclideanSpace ℂ (Fin 1) × EuclideanSpace ℂ (Fin 1))).comp
        (((ContinuousLinearEquiv.refl ℂ (EuclideanSpace ℂ (Fin m))).prodCongr
          (Work.Whitney.sumFibreC 1 1).symm).toContinuousLinearMap) := by
  rw [← prodCongr_sumFibreC_conj m T]
  refine ContinuousLinearMap.ext (fun v => ?_)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply]

/-- **Rearranged form of the first juggling lemma**: `e₃ ∘ (T × (1 × 1)) = ((T × 1) × 1) ∘ e₃`. -/
theorem prodAssoc_symm_comm (m : ℕ)
    (T : EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m)) :
    (((ContinuousLinearEquiv.prodAssoc ℂ (EuclideanSpace ℂ (Fin m)) (EuclideanSpace ℂ (Fin 1))
        (EuclideanSpace ℂ (Fin 1))).symm).toContinuousLinearMap).comp
      (T.prodMap ((1 : EuclideanSpace ℂ (Fin 1) →L[ℂ] EuclideanSpace ℂ (Fin 1)).prodMap
        (1 : EuclideanSpace ℂ (Fin 1) →L[ℂ] EuclideanSpace ℂ (Fin 1))))
    = ((T.prodMap (1 : EuclideanSpace ℂ (Fin 1) →L[ℂ] EuclideanSpace ℂ (Fin 1))).prodMap
        (1 : EuclideanSpace ℂ (Fin 1) →L[ℂ] EuclideanSpace ℂ (Fin 1))).comp
        (((ContinuousLinearEquiv.prodAssoc ℂ (EuclideanSpace ℂ (Fin m)) (EuclideanSpace ℂ (Fin 1))
          (EuclideanSpace ℂ (Fin 1))).symm).toContinuousLinearMap) := by
  rw [← prodAssoc_symm_conj m T]
  refine ContinuousLinearMap.ext (fun v => ?_)
  obtain ⟨x, y, z⟩ := v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  rfl

end Work.Gen
