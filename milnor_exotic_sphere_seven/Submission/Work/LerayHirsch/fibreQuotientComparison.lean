import Mathlib
import Submission.Work.LerayHirsch.exists_quotientBundle_descend
import Submission.Work.LerayHirsch.FibreRestrict
import Submission.Work.LerayHirsch.fibreMap_bijective
import Submission.Work.LerayHirsch.FibreIso

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-!
# The tautological quotient on a fibre is the universal tautological quotient

Let `Z` be a complex vector bundle of rank `m + 1` over `B` given as gluing data and let `b : B`.
The *tautological quotient* `Q_Z = π^*Z / ℂ·s` is a complex bundle of rank `m` over the
projectivisation `P(E) = (E∖0)/ℂˣ` (`Work.LerayHirsch.quotientBundle`, the descent of
`Work.Thom.tautQuotient`).  On the fibre `P(E)_b ≅ ℂP^m` of `π : P(E) → B`, the bundle `Q_Z`
restricts to the pullback of the *universal* tautological quotient `Q_{ε^{m+1}}` of the trivial
bundle `ε^{m+1}` over `P(ε^{m+1})` along the canonical identification
`projUniv (m+1) ∘ projClassFibre Z b : P(E)_b → P(ε^{m+1})` which sends a point of the fibre to the
class of its fibre coordinate:

`fibreQuotientComparison : π_b^*(Q_Z) ≅ (projUniv ∘ projClassFibre)^*(Q_{ε^{m+1}})`.

This is the rank-`m` companion of `Work.LerayHirsch.nonempty_bundleIso_tautLine_fibre`
(`Submission/Work/LerayHirsch/FibreIso.lean`), and the `ζ`-class input of the Leray–Hirsch
theorem on a fibre.

The proof follows the pattern of that companion: the fibrewise gauge is the linear isomorphism
`quoFun ρ w ∘ fillFun κ` comparing the two *preferred* frames of the quotient (the frame of the
chart `(indexAt b, ·)` of `Z` and that of the chart `(·, ·)` of the trivial bundle), where
`w = fibreVec Z p` is the fibre coordinate of a lift `p` and `κ`, `ρ` are the chosen non-vanishing
coordinates of the tautological section in the two bundles.  The chart condition of
`Work.Thom.continuous_totalSpaceMap_clm` then reduces to
`quotientCoord Z i₁ (indexAt b, i₂.2)`, a transition function of `Z`'s quotient, which is
continuous by `Work.LerayHirsch.continuousOn_quotientCoord`; the algebraic core is
`Work.LerayHirsch.quoFun_fillFun_quoFun`.
-/

namespace Work.LerayHirsch

open Work.TangentClasses Work.Thom

open scoped LinearAlgebra.Projectivization

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι] {m : ℕ}

/-! ## The linear algebra of the gauge -/

/-- **The quotient projection is insensitive to replacing `u` by the filling of its class**: for
`w a ≠ 0` the vector `fillFun a (quoFun a w u)` differs from `u` by a multiple of `w`, which any
`quoFun l w` kills. -/
theorem quoFun_fillFun_quoFun {n : ℕ} (a l : Fin (n + 1))
    (w u : EuclideanSpace ℂ (Fin (n + 1))) (hwa : w a ≠ 0) (hwl : w l ≠ 0) :
    quoFun l w (fillFun a (quoFun a w u)) = quoFun l w u := by
  have h1 : fillFun a (quoFun a w u) = u - (u a / w a) • w := by
    have h := sub_fillFun_quoFun a w u hwa
    rw [← h]
    abel
  have hw0 : (quoCLM l w) w = 0 := by rw [quoCLM_apply, quoFun_self l w hwl]
  have h3 : (quoCLM l w) (fillFun a (quoFun a w u)) = (quoCLM l w) u := by
    rw [h1, map_sub, map_smul, hw0, smul_zero, sub_zero]
  rwa [quoCLM_apply, quoCLM_apply] at h3

/-- The same identity, in the form of a composition of continuous linear maps. -/
theorem quoCLM_comp_fillCLM_comp_quoCLM {n : ℕ} (a l : Fin (n + 1))
    (w : EuclideanSpace ℂ (Fin (n + 1))) (hwa : w a ≠ 0) (hwl : w l ≠ 0) :
    (quoCLM l w).comp ((fillCLM a).comp (quoCLM a w)) = quoCLM l w := by
  refine ContinuousLinearMap.ext fun z => ?_
  simp only [ContinuousLinearMap.comp_apply, quoCLM_apply, fillCLM_apply]
  exact quoFun_fillFun_quoFun a l w z hwa hwl

/-! ## The two preferred coordinates of the fibre vector, and the gauge -/

/-- The chosen non-vanishing coordinate of the tautological section of `Z` at `p`, read in the
*punctured fibre* picture: it is the index `k` such that `(fibreVec Z p) k ≠ 0`. -/
def qCoordK (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι)
    (p : ↥(zeroComplement (realification Z))) : Fin (m + 1) :=
  tqCoord Z p

/-- The chosen non-vanishing coordinate of the tautological section of the *trivial* bundle at the
point `tautPunct Z p` whose fibre vector is `fibreVec Z p`. -/
def qCoordL (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι)
    (p : ↥(zeroComplement (realification Z))) : Fin (m + 1) :=
  tqCoord (trivCore (m + 1)) (tautPunct Z p)

theorem fibreVec_qCoordK_ne_zero (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι)
    (p : ↥(zeroComplement (realification Z))) : (fibreVec Z p) (qCoordK Z p) ≠ 0 := by
  rw [qCoordK, ← chartCoord_indexAt_eq_fibreVec Z p rfl]
  exact tqCoord_spec Z p

theorem fibreVec_qCoordL_ne_zero (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι)
    (p : ↥(zeroComplement (realification Z))) : (fibreVec Z p) (qCoordL Z p) ≠ 0 := by
  rw [qCoordL, ← chartCoord_tautPunct Z PUnit.unit p]
  exact tqCoord_spec (trivCore (m + 1)) (tautPunct Z p)

/-- **The gauge at `p`**: the linear isomorphism `ℂ^m → ℂ^m` comparing the two preferred
frames of the tautological quotient, namely the frame of the chart of `Z` at `b` in the coordinate
`qCoordK` and the frame of the trivial bundle in the coordinate `qCoordL`. -/
def qGaugeCLM (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι)
    (p : ↥(zeroComplement (realification Z))) :
    EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m) :=
  (quoCLM (qCoordL Z p) (fibreVec Z p)).comp (fillCLM (qCoordK Z p))

/-- The inverse of the gauge. -/
def qGaugeInvCLM (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι)
    (p : ↥(zeroComplement (realification Z))) :
    EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m) :=
  (quoCLM (qCoordK Z p) (fibreVec Z p)).comp (fillCLM (qCoordL Z p))

theorem qGaugeCLM_apply (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι)
    (p : ↥(zeroComplement (realification Z))) (z : EuclideanSpace ℂ (Fin m)) :
    qGaugeCLM Z p z = quoFun (qCoordL Z p) (fibreVec Z p) (fillFun (qCoordK Z p) z) := by
  rw [qGaugeCLM, ContinuousLinearMap.comp_apply, quoCLM_apply, fillCLM_apply]

theorem qGaugeInvCLM_apply (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι)
    (p : ↥(zeroComplement (realification Z))) (z : EuclideanSpace ℂ (Fin m)) :
    qGaugeInvCLM Z p z = quoFun (qCoordK Z p) (fibreVec Z p) (fillFun (qCoordL Z p) z) := by
  rw [qGaugeInvCLM, ContinuousLinearMap.comp_apply, quoCLM_apply, fillCLM_apply]

theorem qGaugeCLM_comp_inv_apply (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι)
    (p : ↥(zeroComplement (realification Z))) (z : EuclideanSpace ℂ (Fin m)) :
    qGaugeCLM Z p (qGaugeInvCLM Z p z) = z := by
  rw [qGaugeCLM_apply, qGaugeInvCLM_apply]
  rw [quoFun_fillFun_quoFun (qCoordK Z p) (qCoordL Z p) (fibreVec Z p)
      (fillFun (qCoordL Z p) z) (fibreVec_qCoordK_ne_zero Z p) (fibreVec_qCoordL_ne_zero Z p)]
  exact quoFun_fillFun (qCoordL Z p) (fibreVec Z p) z (fibreVec_qCoordL_ne_zero Z p)

theorem qGaugeInvCLM_comp_apply (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι)
    (p : ↥(zeroComplement (realification Z))) (z : EuclideanSpace ℂ (Fin m)) :
    qGaugeInvCLM Z p (qGaugeCLM Z p z) = z := by
  rw [qGaugeCLM_apply, qGaugeInvCLM_apply]
  rw [quoFun_fillFun_quoFun (qCoordL Z p) (qCoordK Z p) (fibreVec Z p)
      (fillFun (qCoordK Z p) z) (fibreVec_qCoordL_ne_zero Z p) (fibreVec_qCoordK_ne_zero Z p)]
  exact quoFun_fillFun (qCoordK Z p) (fibreVec Z p) z (fibreVec_qCoordK_ne_zero Z p)

theorem qGaugeCLM_comp_inv (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι)
    (p : ↥(zeroComplement (realification Z))) :
    (qGaugeCLM Z p).comp (qGaugeInvCLM Z p) = ContinuousLinearMap.id ℂ _ :=
  ContinuousLinearMap.ext fun z => qGaugeCLM_comp_inv_apply Z p z

theorem qGaugeInvCLM_comp (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι)
    (p : ↥(zeroComplement (realification Z))) :
    (qGaugeInvCLM Z p).comp (qGaugeCLM Z p) = ContinuousLinearMap.id ℂ _ :=
  ContinuousLinearMap.ext fun z => qGaugeInvCLM_comp_apply Z p z

/-- **The gauge, as a linear equivalence** `ℂ^m ≃ₗ ℂ^m`. -/
def qGaugeEquiv (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι)
    (p : ↥(zeroComplement (realification Z))) :
    EuclideanSpace ℂ (Fin m) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin m) :=
  LinearEquiv.ofLinearMap (qGaugeCLM Z p).toLinearMap (qGaugeInvCLM Z p).toLinearMap
    (by ext z : 1; exact qGaugeCLM_comp_inv_apply Z p z)
    (by ext z : 1; exact qGaugeInvCLM_comp_apply Z p z)

theorem qGaugeEquiv_apply (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι)
    (p : ↥(zeroComplement (realification Z))) (z : EuclideanSpace ℂ (Fin m)) :
    qGaugeEquiv Z p z = qGaugeCLM Z p z := rfl

theorem qGaugeEquiv_symm_apply (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι)
    (p : ↥(zeroComplement (realification Z))) (z : EuclideanSpace ℂ (Fin m)) :
    (qGaugeEquiv Z p).symm z = qGaugeInvCLM Z p z := rfl

/-! ## The two bundles of the comparison -/

/-- **The left-hand bundle**: the tautological quotient `Q_Z` of `Z`, restricted to the fibre of
the projectivisation over `b`. -/
def qL (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι) (b : B) :
    VectorBundleCore ℂ (ProjFibre Z b) (EuclideanSpace ℂ (Fin m)) (ι × Fin (m + 1)) :=
  bundleComap (quotientBundle Z) (fibreIncl Z b)

/-- **The right-hand bundle**: the tautological quotient `Q_{ε^{m+1}}` of the trivial bundle,
pulled back along the class of the fibre coordinate. -/
def qR (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι) (b : B) :
    VectorBundleCore ℂ (ProjFibre Z b) (EuclideanSpace ℂ (Fin m)) (PUnit × Fin (m + 1)) :=
  bundleComap (quotientBundle (trivCore (m + 1)))
    ((projUniv (m + 1)).comp (projClassFibre Z b))

/-- A chosen lift of a point of the fibre of the projectivisation. -/
noncomputable def qLift (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι) (b : B)
    (x : ProjFibre Z b) : ↥(zeroComplement (realification Z)) :=
  Classical.choose (surjective_mkProj Z x.1)

theorem qLift_spec (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι) (b : B)
    (x : ProjFibre Z b) : mkProj Z (qLift Z b x) = x.1 :=
  Classical.choose_spec (surjective_mkProj Z x.1)

theorem qLift_proj (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι) (b : B)
    (x : ProjFibre Z b) : (qLift Z b x).1.proj = b := by
  have h := qLift_spec Z b x
  have h2 : projMap Z (mkProj Z (qLift Z b x)) = b := by rw [h]; exact x.2
  rwa [projMap_mkProj] at h2

theorem qLift_tautPunct (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι) (b : B)
    (x : ProjFibre Z b) :
    (projUniv (m + 1)) (projClassFibre Z b x) = mkProj (trivCore (m + 1)) (tautPunct Z (qLift Z b x)) := by
  rw [projClassFibre_apply, show (x.1 : ProjSpace Z) = mkProj Z (qLift Z b x) from (qLift_spec Z b x).symm]
  exact projUniv_projClass_mkProj Z (qLift Z b x)

/-! ## The index maps and the transition functions on the fibre -/

theorem qL_indexAt (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι) (b : B)
    (x : ProjFibre Z b) :
    (qL Z b).indexAt x = (Z.indexAt b, qCoordK Z (qLift Z b x)) := by
  show quotientIndexAt Z (fibreIncl Z b x) = _
  rw [show fibreIncl Z b x = mkProj Z (qLift Z b x) from (qLift_spec Z b x).symm,
    quotientIndexAt_mk, tautQuotient_indexAt_eq, qLift_proj, qCoordK]

theorem qR_indexAt (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι) (b : B)
    (x : ProjFibre Z b) :
    (qR Z b).indexAt x = (PUnit.unit, qCoordL Z (qLift Z b x)) := by
  show quotientIndexAt (trivCore (m + 1)) ((projUniv (m + 1)).comp (projClassFibre Z b) x) = _
  rw [ContinuousMap.comp_apply, qLift_tautPunct, quotientIndexAt_mk]
  rw [tautQuotient_indexAt_eq]
  rfl

/-- The second component of the local trivialization in the preferred chart of the base point is
the fibre coordinate, in the syntactic shape produced by `Work.Thom.tautQuotient_coordChange_eq`. -/
theorem localTriv_indexAt_snd (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι)
    (p : ↥(zeroComplement (realification Z))) {b : B} (hp : p.1.proj = b) :
    (Z.localTriv (Z.indexAt b) (p : (realification Z).TotalSpace)).2 = fibreVec Z p :=
  chartCoord_indexAt_eq_fibreVec Z p hp

/-- The transition functions of the trivial core are the identity, in the syntactic shape
produced by `Work.Thom.tautQuotient_coordChange_eq`. -/
theorem coordChange_trivCore (i j : PUnit) (x : PUnit) :
    (trivCore (m + 1)).coordChange i j x
      = ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin (m + 1))) := rfl

/-- The transition function of `tautQuotient Z` between the chart `i₁` and the *preferred* chart
`(indexAt b, qCoordK)` at a punctured point of the fibre, read in the `quoCLM`/`fillCLM` form. -/
theorem qL_tautQuotient_indexAt (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι)
    (b : B) (i₁ : ι × Fin (m + 1)) (x : ProjFibre Z b) :
    (tautQuotient Z).coordChange i₁ (Z.indexAt b, qCoordK Z (qLift Z b x)) (qLift Z b x)
      = (quoCLM (qCoordK Z (qLift Z b x)) (fibreVec Z (qLift Z b x))).comp
          ((Z.coordChange i₁.1 (Z.indexAt b) b).comp (fillCLM i₁.2)) := by
  rw [tautQuotient_coordChange_eq,
    localTriv_indexAt_snd Z (qLift Z b x) (qLift_proj Z b x), qLift_proj Z b x]

/-- The transition function of `tautQuotient (trivCore)` between the preferred chart and the chart
`i₂` at the tautological point attached to `p`, read in the `quoCLM`/`fillCLM` form. -/
theorem qR_tautQuotient_indexAt (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι)
    (b : B) (i₂ : PUnit × Fin (m + 1)) (x : ProjFibre Z b) :
    (tautQuotient (trivCore (m + 1))).coordChange (PUnit.unit, qCoordL Z (qLift Z b x)) i₂
        (tautPunct Z (qLift Z b x))
      = (quoCLM i₂.2 (fibreVec Z (qLift Z b x))).comp (fillCLM (qCoordL Z (qLift Z b x))) := by
  rw [tautQuotient_coordChange_eq,
    show (((trivCore (m + 1)).localTriv i₂.1
        (tautPunct Z (qLift Z b x) :
          (realification (trivCore (m + 1))).TotalSpace)).2) = fibreVec Z (qLift Z b x)
      from chartCoord_tautPunct Z i₂.1 (qLift Z b x),
    coordChange_trivCore, ContinuousLinearMap.id_comp]

theorem qL_coordChange (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι) (b : B)
    (i₁ : ι × Fin (m + 1)) (x : ProjFibre Z b) :
    (qL Z b).coordChange i₁ ((qL Z b).indexAt x) x
      = (quoCLM (qCoordK Z (qLift Z b x)) (fibreVec Z (qLift Z b x))).comp
          ((Z.coordChange i₁.1 (Z.indexAt b) b).comp (fillCLM i₁.2)) := by
  show quotientCoord Z i₁ ((qL Z b).indexAt x) (fibreIncl Z b x) = _
  rw [qL_indexAt Z b x,
    show fibreIncl Z b x = mkProj Z (qLift Z b x) from (qLift_spec Z b x).symm,
    quotientCoord_mk]
  exact qL_tautQuotient_indexAt Z b i₁ x

theorem qR_coordChange (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι) (b : B)
    (i₂ : PUnit × Fin (m + 1)) (x : ProjFibre Z b) :
    (qR Z b).coordChange ((qR Z b).indexAt x) i₂ x
      = (quoCLM i₂.2 (fibreVec Z (qLift Z b x))).comp (fillCLM (qCoordL Z (qLift Z b x))) := by
  show quotientCoord (trivCore (m + 1)) ((qR Z b).indexAt x) i₂
    ((projUniv (m + 1)).comp (projClassFibre Z b) x) = _
  rw [ContinuousMap.comp_apply, qLift_tautPunct, qR_indexAt Z b x, quotientCoord_mk]
  exact qR_tautQuotient_indexAt Z b i₂ x

/-! ## The linear algebra of the two-step simplification -/

/-- **The two-step simplification**: composing the gauge with the transition functions in the
preferred charts reduces to a single quotient projection.  This is the pointwise form of the
identity `A ∘ fill λ ∘ quo λ w ∘ fill κ ∘ quo κ w = A ∘ quo κ w` (`A = quoCLM l w`), the
`quoFun`-analogue of `Work.Thom.quoFun_transport`. -/
theorem qGauge_algebra_apply {n : ℕ} (κ ρ l : Fin (n + 1))
    (w : EuclideanSpace ℂ (Fin (n + 1)))
    (C : EuclideanSpace ℂ (Fin (n + 1)) →L[ℂ] EuclideanSpace ℂ (Fin (n + 1)))
    (k : Fin (n + 1)) (z : EuclideanSpace ℂ (Fin n))
    (hκ : w κ ≠ 0) (hρ : w ρ ≠ 0) (hl : w l ≠ 0) :
    quoFun l w (fillFun ρ (quoFun ρ w (fillFun κ (quoFun κ w (C (fillFun k z))))))
      = quoFun l w (C (fillFun k z)) := by
  rw [quoFun_fillFun_quoFun κ ρ w (C (fillFun k z)) hκ hρ,
    quoFun_fillFun_quoFun ρ l w (C (fillFun k z)) hρ hl]

/-! ## The containment of the charts -/

/-- On the chart `i₂` of the right-hand bundle, the corresponding fibre coordinate of the lift
does not vanish. -/
theorem qR_baseSet_ne_zero (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι)
    (b : B) (i₂ : PUnit × Fin (m + 1)) (x : ProjFibre Z b)
    (hx : x ∈ (qR Z b).baseSet i₂) : (fibreVec Z (qLift Z b x)) i₂.2 ≠ 0 := by
  have hx' : (projUniv (m + 1)) ((projClassFibre Z b) x)
      ∈ (quotientBundle (trivCore (m + 1))).baseSet i₂ := hx
  rw [quotientBundle_baseSet] at hx'
  rw [qLift_tautPunct] at hx'
  have h2 := (mem_tautBaseSetProj_mk (trivCore (m + 1)) i₂ (tautPunct Z (qLift Z b x))).mp hx'
  rw [mem_tautBaseSet] at h2
  rw [chartCoord_tautPunct Z i₂.1 (qLift Z b x)] at h2
  exact h2.2

/-- On the chart `i₂` of the right-hand bundle, the point of the fibre lies in the chart
`(indexAt b, i₂.2)` of the left-hand bundle. -/
theorem qR_baseSet_mem_tautBaseSetProj (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι)
    (b : B) (i₂ : PUnit × Fin (m + 1)) (x : ProjFibre Z b)
    (hx : x ∈ (qR Z b).baseSet i₂) : x.1 ∈ tautBaseSetProj Z (Z.indexAt b, i₂.2) := by
  rw [show x.1 = mkProj Z (qLift Z b x) from (qLift_spec Z b x).symm, mem_tautBaseSetProj_mk,
    mem_tautBaseSet]
  exact ⟨by rw [qLift_proj]; exact Z.mem_baseSet_at b,
    by rw [chartCoord_indexAt_eq_fibreVec Z (qLift Z b x) (qLift_proj Z b x)]
       exact qR_baseSet_ne_zero Z b i₂ x hx⟩

/-! ## The reverse transitions, and the inverse chart identity -/

theorem qL_baseSet_ne_zero (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι)
    (b : B) (i₁ : ι × Fin (m + 1)) (x : ProjFibre Z b)
    (hx : x ∈ (qL Z b).baseSet i₁) : (chartCoord Z i₁.1 (qLift Z b x)) i₁.2 ≠ 0 := by
  have h : x.1 ∈ tautBaseSetProj Z i₁ := hx
  rw [show x.1 = mkProj Z (qLift Z b x) from (qLift_spec Z b x).symm, mem_tautBaseSetProj_mk,
    mem_tautBaseSet] at h
  exact h.2

theorem qL_baseSet_ne_zero' (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι)
    (b : B) (i₁ : ι × Fin (m + 1)) (x : ProjFibre Z b)
    (hx : x ∈ (qL Z b).baseSet i₁) :
    ((Z.coordChange (Z.indexAt b) i₁.1 b) (fibreVec Z (qLift Z b x))) i₁.2 ≠ 0 := by
  have h := qL_baseSet_ne_zero Z b i₁ x hx
  rwa [chartCoord_def, qLift_proj Z b x] at h

/-- The reverse transition function of the tautological quotient of `Z` at a point of the fibre. -/
theorem qL_coordChange_rev (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι) (b : B)
    (i₁ : ι × Fin (m + 1)) (x : ProjFibre Z b) :
    (qL Z b).coordChange ((qL Z b).indexAt x) i₁ x
      = (quoCLM i₁.2 (chartCoord Z i₁.1 (qLift Z b x))).comp
          ((Z.coordChange (Z.indexAt b) i₁.1 b).comp (fillCLM (qCoordK Z (qLift Z b x)))) := by
  show quotientCoord Z ((qL Z b).indexAt x) i₁ (fibreIncl Z b x) = _
  rw [qL_indexAt Z b x,
    show fibreIncl Z b x = mkProj Z (qLift Z b x) from (qLift_spec Z b x).symm,
    quotientCoord_mk, tautQuotient_coordChange_eq, qLift_proj Z b x,
    show (Z.localTriv i₁.1 (qLift Z b x : (realification Z).TotalSpace)).2
      = chartCoord Z i₁.1 (qLift Z b x) from rfl]

/-- The reverse transition function of the tautological quotient of the trivial bundle at a point
of the fibre. -/
theorem qR_coordChange_rev (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι) (b : B)
    (i₂ : PUnit × Fin (m + 1)) (x : ProjFibre Z b) :
    (qR Z b).coordChange i₂ ((qR Z b).indexAt x) x
      = (quoCLM (qCoordL Z (qLift Z b x)) (fibreVec Z (qLift Z b x))).comp (fillCLM i₂.2) := by
  show quotientCoord (trivCore (m + 1)) i₂ ((qR Z b).indexAt x)
    ((projUniv (m + 1)).comp (projClassFibre Z b) x) = _
  rw [ContinuousMap.comp_apply, qLift_tautPunct, qR_indexAt Z b x, quotientCoord_mk,
    tautQuotient_coordChange_eq,
    show (((trivCore (m + 1)).localTriv PUnit.unit
        (tautPunct Z (qLift Z b x) :
          (realification (trivCore (m + 1))).TotalSpace)).2) = fibreVec Z (qLift Z b x)
      from chartCoord_tautPunct Z PUnit.unit (qLift Z b x),
    coordChange_trivCore, ContinuousLinearMap.id_comp]

/-! ## The linear algebra of the inverse direction -/

/-- **The inverse simplification**: `C` applied to the two-step filling of the class of `fillFun k z`
modulo `ℂw` differs from `C (fillFun k z)` by a multiple of `C w`, so any `quoFun l (C w)` sees the
same value. -/
theorem qGauge_algebra_inv_apply {n : ℕ} (κ ρ l k : Fin (n + 1))
    (w : EuclideanSpace ℂ (Fin (n + 1)))
    (C : EuclideanSpace ℂ (Fin (n + 1)) →L[ℂ] EuclideanSpace ℂ (Fin (n + 1)))
    (z : EuclideanSpace ℂ (Fin n))
    (hκ : w κ ≠ 0) (hρ : w ρ ≠ 0) (hl : (C w) l ≠ 0) :
    quoFun l (C w) (C (fillFun κ (quoFun κ w (fillFun ρ (quoFun ρ w (fillFun k z))))))
      = quoFun l (C w) (C (fillFun k z)) := by
  rw [quoFun_fillFun_quoFun ρ κ w (fillFun k z) hρ hκ]
  have h1 : fillFun κ (quoFun κ w (fillFun k z))
      = fillFun k z - ((fillFun k z) κ / w κ) • w := by
    have h := sub_fillFun_quoFun κ w (fillFun k z) hκ
    rw [← h]
    abel
  rw [h1, ContinuousLinearMap.map_sub, ContinuousLinearMap.map_smul]
  have h2 : (quoCLM l (C w)) (C w) = 0 := by rw [quoCLM_apply, quoFun_self l (C w) hl]
  have h3 : (quoCLM l (C w)) (C (fillFun k z) - ((fillFun k z) κ / w κ) • C w)
      = (quoCLM l (C w)) (C (fillFun k z)) := by
    rw [ContinuousLinearMap.map_sub, ContinuousLinearMap.map_smul, h2, smul_zero, sub_zero]
  rwa [quoCLM_apply, quoCLM_apply] at h3

/-! ## The chart identity of the gauge -/

theorem qGauge_chart_identity_apply (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι)
    (b : B) (i₁ : ι × Fin (m + 1)) (i₂ : PUnit × Fin (m + 1)) (x : ProjFibre Z b)
    (hx : x ∈ (qR Z b).baseSet i₂) (z : EuclideanSpace ℂ (Fin m)) :
    (((qR Z b).coordChange ((qR Z b).indexAt x) i₂ x).comp
        ((qGaugeCLM Z (qLift Z b x)).comp ((qL Z b).coordChange i₁ ((qL Z b).indexAt x) x))) z
      = (quotientCoord Z i₁ (Z.indexAt b, i₂.2) x.1) z := by
  have hRHS : quotientCoord Z i₁ (Z.indexAt b, i₂.2) x.1
      = (quoCLM i₂.2 (fibreVec Z (qLift Z b x))).comp
          ((Z.coordChange i₁.1 (Z.indexAt b) b).comp (fillCLM i₁.2)) := by
    rw [show x.1 = mkProj Z (qLift Z b x) from (qLift_spec Z b x).symm, quotientCoord_mk,
      tautQuotient_coordChange_eq, localTriv_indexAt_snd Z (qLift Z b x) (qLift_proj Z b x),
      qLift_proj Z b x]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, qR_coordChange, qL_coordChange,
    hRHS]
  simp only [ContinuousLinearMap.comp_apply, qGaugeCLM, quoCLM_apply, fillCLM_apply]
  exact qGauge_algebra_apply (qCoordK Z (qLift Z b x)) (qCoordL Z (qLift Z b x)) i₂.2
    (fibreVec Z (qLift Z b x)) (Z.coordChange i₁.1 (Z.indexAt b) b) i₁.2 z
    (fibreVec_qCoordK_ne_zero Z (qLift Z b x)) (fibreVec_qCoordL_ne_zero Z (qLift Z b x))
    (qR_baseSet_ne_zero Z b i₂ x hx)

theorem qGauge_chart_identity (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι)
    (b : B) (i₁ : ι × Fin (m + 1)) (i₂ : PUnit × Fin (m + 1)) (x : ProjFibre Z b)
    (hx : x ∈ (qR Z b).baseSet i₂) :
    ((qR Z b).coordChange ((qR Z b).indexAt x) i₂ x).comp
        ((qGaugeCLM Z (qLift Z b x)).comp ((qL Z b).coordChange i₁ ((qL Z b).indexAt x) x))
      = quotientCoord Z i₁ (Z.indexAt b, i₂.2) x.1 :=
  ContinuousLinearMap.ext fun z => qGauge_chart_identity_apply Z b i₁ i₂ x hx z

theorem qGauge_chart_identity_inv (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι)
    (b : B) (i₁ : ι × Fin (m + 1)) (i₂ : PUnit × Fin (m + 1)) (x : ProjFibre Z b)
    (hx : x ∈ (qL Z b).baseSet i₁) :
    ((qL Z b).coordChange ((qL Z b).indexAt x) i₁ x).comp
        ((qGaugeInvCLM Z (qLift Z b x)).comp ((qR Z b).coordChange i₂ ((qR Z b).indexAt x) x))
      = quotientCoord Z (Z.indexAt b, i₂.2) i₁ x.1 := by
  refine ContinuousLinearMap.ext fun z => ?_
  have hRHS : quotientCoord Z (Z.indexAt b, i₂.2) i₁ x.1
      = (quoCLM i₁.2 (chartCoord Z i₁.1 (qLift Z b x))).comp
          ((Z.coordChange (Z.indexAt b) i₁.1 b).comp (fillCLM i₂.2)) := by
    rw [show x.1 = mkProj Z (qLift Z b x) from (qLift_spec Z b x).symm, quotientCoord_mk,
      tautQuotient_coordChange_eq, qLift_proj Z b x,
      show (Z.localTriv i₁.1 (qLift Z b x : (realification Z).TotalSpace)).2
        = chartCoord Z i₁.1 (qLift Z b x) from rfl]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, qL_coordChange_rev,
    qR_coordChange_rev, hRHS]
  simp only [ContinuousLinearMap.comp_apply, qGaugeInvCLM, quoCLM_apply, fillCLM_apply]
  rw [show chartCoord Z i₁.1 (qLift Z b x)
      = (Z.coordChange (Z.indexAt b) i₁.1 b) (fibreVec Z (qLift Z b x)) from by
        rw [chartCoord_def, qLift_proj Z b x]
        rfl]
  exact qGauge_algebra_inv_apply (qCoordK Z (qLift Z b x)) (qCoordL Z (qLift Z b x)) i₁.2 i₂.2
    (fibreVec Z (qLift Z b x)) (Z.coordChange (Z.indexAt b) i₁.1 b) z
    (fibreVec_qCoordK_ne_zero Z (qLift Z b x)) (fibreVec_qCoordL_ne_zero Z (qLift Z b x))
    (qL_baseSet_ne_zero' Z b i₁ x hx)

/-! ## Continuity -/

theorem qGauge_chart_continuousOn (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι)
    (b : B) (i₁ : ι × Fin (m + 1)) (i₂ : PUnit × Fin (m + 1)) :
    ContinuousOn (fun x : ProjFibre Z b =>
      ((qR Z b).coordChange ((qR Z b).indexAt x) i₂ x).comp
        ((qGaugeCLM Z (qLift Z b x)).comp ((qL Z b).coordChange i₁ ((qL Z b).indexAt x) x)))
      ((qL Z b).baseSet i₁ ∩ (qR Z b).baseSet i₂) := by
  refine ContinuousOn.congr (f := fun x : ProjFibre Z b =>
    quotientCoord Z i₁ (Z.indexAt b, i₂.2) x.1) ?_ ?_
  · refine (continuousOn_quotientCoord Z i₁ (Z.indexAt b, i₂.2)).comp
      continuous_subtype_val.continuousOn ?_
    intro x hx
    exact ⟨hx.1, qR_baseSet_mem_tautBaseSetProj Z b i₂ x hx.2⟩
  · intro x hx
    exact qGauge_chart_identity Z b i₁ i₂ x hx.2

theorem qGaugeInv_chart_continuousOn (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι)
    (b : B) (i₁ : ι × Fin (m + 1)) (i₂ : PUnit × Fin (m + 1)) :
    ContinuousOn (fun x : ProjFibre Z b =>
      ((qL Z b).coordChange ((qL Z b).indexAt x) i₁ x).comp
        ((qGaugeInvCLM Z (qLift Z b x)).comp ((qR Z b).coordChange i₂ ((qR Z b).indexAt x) x)))
      ((qR Z b).baseSet i₂ ∩ (qL Z b).baseSet i₁) := by
  refine ContinuousOn.congr (f := fun x : ProjFibre Z b =>
    quotientCoord Z (Z.indexAt b, i₂.2) i₁ x.1) ?_ ?_
  · refine (continuousOn_quotientCoord Z (Z.indexAt b, i₂.2) i₁).comp
      continuous_subtype_val.continuousOn ?_
    intro x hx
    exact ⟨qR_baseSet_mem_tautBaseSetProj Z b i₂ x hx.1, hx.2⟩
  · intro x hx
    exact qGauge_chart_identity_inv Z b i₁ i₂ x hx.2

/-! ## The comparison -/

/-- **The bundle isomorphism comparing the restriction of the tautological quotient of `Z` to a
fibre with the restriction of the tautological quotient of the trivial bundle along the class of
the fibre coordinate.**  The fibrewise map is the gauge `Work.LerayHirsch.qGaugeEquiv` at the
chosen lift. -/
noncomputable def fibreQuotientIso (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι)
    (b : B) : BundleIso (qL Z b) (qR Z b) where
  hom x := (qGaugeEquiv Z (qLift Z b x) : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] EuclideanSpace ℂ (Fin m))
  inv x := ((qGaugeEquiv Z (qLift Z b x)).symm :
    EuclideanSpace ℂ (Fin m) →ₗ[ℂ] EuclideanSpace ℂ (Fin m))
  left_inv x v := (qGaugeEquiv Z (qLift Z b x)).symm_apply_apply v
  right_inv x v := (qGaugeEquiv Z (qLift Z b x)).apply_symm_apply v
  continuous_hom := by
    refine (continuous_totalSpaceMap_clm (qL Z b) (qR Z b) (ContinuousMap.id _)
      (fun x => qGaugeCLM Z (qLift Z b x)) ?_).congr (fun p => rfl)
    intro i₁ i₂
    simpa only [ContinuousMap.coe_id, Set.preimage_id, ContinuousMap.id_apply] using
      qGauge_chart_continuousOn Z b i₁ i₂
  continuous_inv := by
    refine (continuous_totalSpaceMap_clm (qR Z b) (qL Z b) (ContinuousMap.id _)
      (fun x => qGaugeInvCLM Z (qLift Z b x)) ?_).congr (fun p => rfl)
    intro j₂ j₁
    simpa only [ContinuousMap.coe_id, Set.preimage_id, ContinuousMap.id_apply] using
      qGaugeInv_chart_continuousOn Z b j₁ j₂

/-- **The comparison of the tautological quotient on a fibre with the universal tautological
quotient**, in the form in which the Leray--Hirsch chapter needs it. -/
theorem fibreQuotientComparison {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι] {m : ℕ}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι) (b : B) :
    Nonempty (Work.Thom.BundleIso
      (Work.Thom.bundleComap (Work.LerayHirsch.quotientBundle Z)
        (Work.LerayHirsch.fibreIncl Z b))
      (Work.Thom.bundleComap (Work.LerayHirsch.quotientBundle (Work.LerayHirsch.trivCore (m + 1)))
        ((Work.LerayHirsch.projUniv (m + 1)).comp (Work.LerayHirsch.projClassFibre Z b)))) :=
  ⟨fibreQuotientIso Z b⟩

end

end Work.LerayHirsch
