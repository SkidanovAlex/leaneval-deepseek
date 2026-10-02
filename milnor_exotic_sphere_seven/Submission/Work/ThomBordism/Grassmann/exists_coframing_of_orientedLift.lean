import Mathlib
import Submission.Work.ThomBordism.Grassmann.Oriented
import Submission.Work.ThomBordism.Grassmann.EvalBundle
import Submission.Work.ThomBordism.Grassmann.chartFrameAt
import Submission.Work.PTGeometric.exists_projOfPlane
import Submission.Work.ThomBordism.Grassmann.coframingDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

namespace Work.ThomBordism.Grassmann

noncomputable section

variable {k m : ℕ}

/-! ## The members of the covering cover -/

theorem exists_goodSet {M : Type} [TopologicalSpace M] (Γ : M → OG k m) (y : M) :
    ∃ i : ChartIdx k m × Bool, y ∈ cfGoodSet Γ i := by
  classical
  have hS : Γ y ∈ baseSet (chartCover (Γ y)) := mem_baseSet_chartCover (Γ y)
  have hs : frameSign (chartCover (Γ y)) (Γ y) * frameSign (chartCover (Γ y)) (Γ y) = 1 :=
    frameSign_mul_self _ _ hS
  rcases mul_self_eq_one_iff.mp hs with h | h
  · exact ⟨(chartCover (Γ y), true), hS, by rw [h, signOf_true]; norm_num⟩
  · exact ⟨(chartCover (Γ y), false), hS, by rw [h, signOf_false]; norm_num⟩

/-! ## The two fundamental properties of the coframing -/

/-- The fixed left inverse of the coframing is indeed a left inverse of it. -/
theorem ellOf_eOf_of_mem {M : Type} [TopologicalSpace M] {Γ : M → OG k m}
    {i : ChartIdx k m × Bool} {y : M} (hy : y ∈ cfGoodSet Γ i) (c : Amb k) :
    ellOf i (eOf Γ i y c) = c := by
  have hS : Quotient.out (Γ y) ∈ chartSet i.1 :=
    (mem_baseSet_iff i.1 (Quotient.out (Γ y))).mp (by rw [Quotient.out_eq']; exact hy.1)
  rw [ellOf_eOf, coordProjCLM_coordEval i.1 _ _ hS,
    signCLM_involutive _ (signOf_mul_self i.2) c]

/-- The coframing lands in the plane, so the orthogonal projection of the family fixes it. -/
theorem projOfPlane_eOf_of_mem {M : Type} [TopologicalSpace M] {Γ : M → OG k m}
    {P : M → Work.PTGeometric.EndOp (k + m)}
    (hΓ : ∀ x, Work.PTGeometric.projOfPlane k m (Γ x) = P x)
    {i : ChartIdx k m × Bool} {y : M} (hy : y ∈ cfGoodSet Γ i) (c : Amb k) :
    P y (eOf Γ i y c) = eOf Γ i y c := by
  have hout : Quotient.mk'' (Quotient.out (Γ y)) = Γ y := Quotient.out_eq' _
  rw [← hΓ y, Work.PTGeometric.projOfPlane_fixed_iff, ← hout]
  exact memPlane_coordEval i.1 (Quotient.out (Γ y)) (signCLM (cfSignOf i.2) c)

/-- The coframing is injective. -/
theorem injective_eOf_of_mem {M : Type} [TopologicalSpace M] {Γ : M → OG k m}
    {i : ChartIdx k m × Bool} {y : M} (hy : y ∈ cfGoodSet Γ i) :
    Function.Injective (eOf Γ i y) := by
  intro a b hab
  have h := congrArg (ellOf i) hab
  rwa [ellOf_eOf_of_mem hy a, ellOf_eOf_of_mem hy b] at h

/-! ## The two coframings of an overlap are orientation related -/

/-- The composite `ℓ' ∘ e` is the orientation-consistent transition function `coordChangeO`, whose
determinant is positive (`det_coordChangeO_pos`). -/
theorem comp_ellOf_eOf_eq_coordChangeO {M : Type} [TopologicalSpace M] {Γ : M → OG k m}
    {i i' : ChartIdx k m × Bool} {y : M} (hy : y ∈ cfGoodSet Γ i) (hy' : y ∈ cfGoodSet Γ i') :
    (ellOf i').comp (eOf Γ i y) = coordChangeO i.1 i'.1 (Γ y) := by
  have hS : Quotient.out (Γ y) ∈ chartSet i.1 :=
    (mem_baseSet_iff i.1 (Quotient.out (Γ y))).mp (by rw [Quotient.out_eq']; exact hy.1)
  have hT : Quotient.out (Γ y) ∈ chartSet i'.1 :=
    (mem_baseSet_iff i'.1 (Quotient.out (Γ y))).mp (by rw [Quotient.out_eq']; exact hy'.1)
  have hout : Quotient.mk'' (Quotient.out (Γ y)) = Γ y := Quotient.out_eq' _
  refine ContinuousLinearMap.ext fun c => ?_
  rw [ContinuousLinearMap.comp_apply]
  show signCLM (cfSignOf i'.2)
      (coordProjCLM i'.1 (coordEval i.1 (Quotient.out (Γ y)) (signCLM (cfSignOf i.2) c)))
    = coordChangeO i.1 i'.1 (Γ y) c
  rw [coordProjCLM_coordEval_eq i.1 i'.1 (Quotient.out (Γ y)) hS hT (signCLM (cfSignOf i.2) c)]
  rw [show coordChangeAux i.1 i'.1 (Quotient.out (Γ y)) = coordChange i.1 i'.1 (Γ y) from by
    rw [← coordChange_mk i.1 i'.1 (Quotient.out (Γ y)), hout]]
  rw [signCLM_apply, signCLM_apply, signMat_eq_orientMat (frameSign_eq_of_mem_goodSet hy'),
    signMat_eq_orientMat (frameSign_eq_of_mem_goodSet hy)]
  rfl

theorem det_eOf_pos {M : Type} [TopologicalSpace M] {Γ : M → OG k m}
    {i i' : ChartIdx k m × Bool} {y : M} (hy : y ∈ cfGoodSet Γ i) (hy' : y ∈ cfGoodSet Γ i') :
    0 < LinearMap.det (((ellOf i').comp (eOf Γ i y) : Amb k →L[ℝ] Amb k) :
      Amb k →ₗ[ℝ] Amb k) := by
  rw [comp_ellOf_eOf_eq_coordChangeO hy hy']
  exact det_coordChangeO_pos i.1 i'.1 (Γ y) ⟨hy.1, hy'.1⟩

end

/-- **A continuous family of oriented `k`-planes in `ℝ^{k+m}` admits a finite orientation-consistent
coframing.**

The plane family is given through its orthogonal projections `P : M → Gr (k+m) k`, obtained from a
continuous oriented lift `Γ : M → G̃r_k(ℝ^{k+m})` by `projOfPlane k m (Γ x) = P x`.  We produce a
finite cover `U j` of `W` together with a **fixed** linear left inverse `ℓ j` and a varying
parametrisation `e j y : ℝ^k ≅ P y` of the plane, the coframings of overlapping members being
orientation related (`det (ℓ j' ∘ e j y) > 0`).

The construction uses the standard charts `baseSet S` of the Grassmannian and the sign gauge
`orientMat S` of `Oriented.lean`: the covering is indexed by `(S, b) : ChartIdx k m × Bool` with
`U (S,b) = Γ ⁻¹' {x ∈ baseSet S : frameSign S x ≠ -cfSignOf b}` (so that on `U (S,b)` the orientation
gauge is the constant matrix `cfSignMat (cfSignOf b) = diag(±1, 1, …, 1)`, `signMat_eq_orientMat`),
`ℓ (S,b) = cfSignMat (cfSignOf b) ∘ coordProjCLM S` and `e (S,b) y = cfCoordEvalCLM S (out (Γ y)) ∘
cfSignMat (cfSignOf b)`.  The orientation consistency is then exactly the positivity of the determinant
of the orientation-consistent transition function `coordChangeO` (`det_coordChangeO_pos`), via
`comp_ellOf_eOf_eq_coordChangeO`.

The hypotheses `hPc` and `hPgr` are not used: `P` enters only through `hΓ`. -/
theorem exists_coframing_of_orientedLift
    {k m : ℕ} {M : Type} [TopologicalSpace M]
    {P : M → Work.PTGeometric.EndOp (k + m)}
    (hPc : Continuous P) (hPgr : ∀ x, P x ∈ Work.PTGeometric.Gr (k + m) k)
    (Γ : M → Work.ThomBordism.Grassmann.OG k m) (hΓc : Continuous Γ)
    (hΓ : ∀ x, Work.PTGeometric.projOfPlane k m (Γ x) = P x)
    (W : Set M) :
    ∃ (mE : ℕ) (U : Fin mE → Set M)
      (ℓ : Fin mE → Work.PTGeometric.Amb (k + m) →L[ℝ] Work.PTGeometric.Amb k)
      (e : Fin mE → M → Work.PTGeometric.Amb k →L[ℝ] Work.PTGeometric.Amb (k + m)),
      (∀ j, IsOpen (U j)) ∧
      (∀ x ∈ W, ∃ j, x ∈ U j) ∧
      (∀ j y, y ∈ U j → ∀ c : Work.PTGeometric.Amb k,
        ℓ j (e j y c) = c ∧ P y (e j y c) = e j y c) ∧
      (∀ j y, y ∈ U j → Function.Injective (e j y)) ∧
      (∀ j j' y, y ∈ U j → y ∈ U j' →
        0 < LinearMap.det ((ℓ j').comp (e j y) : Work.PTGeometric.Amb k →ₗ[ℝ] Work.PTGeometric.Amb k)) := by
  classical
  let eι : ChartIdx k m × Bool ≃ Fin (Fintype.card (ChartIdx k m × Bool)) :=
    Fintype.equivFin (ChartIdx k m × Bool)
  refine ⟨Fintype.card (ChartIdx k m × Bool), fun j => cfGoodSet Γ (eι.symm j),
    fun j => ellOf (eι.symm j), fun j => eOf Γ (eι.symm j), ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    exact isOpen_goodSet hΓc (eι.symm j)
  · intro x _
    obtain ⟨i, hi⟩ := exists_goodSet Γ x
    exact ⟨eι i, by simpa using hi⟩
  · intro j y hy c
    refine ⟨?_, ?_⟩
    · exact ellOf_eOf_of_mem (by simpa using hy) c
    · exact projOfPlane_eOf_of_mem (k := k) (m := m) hΓ (by simpa using hy) c
  · intro j y hy
    exact injective_eOf_of_mem (by simpa using hy)
  · intro j j' y hy hy'
    exact det_eOf_pos (by simpa using hy) (by simpa using hy')

end Work.ThomBordism.Grassmann
