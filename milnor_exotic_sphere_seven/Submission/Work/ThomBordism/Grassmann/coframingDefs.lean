import Mathlib
import Submission.Work.ThomBordism.Grassmann.Oriented
import Submission.Work.ThomBordism.Grassmann.EvalBundle
import Submission.Work.ThomBordism.Grassmann.chartFrameAt
import Submission.Work.PTGeometric.exists_projOfPlane

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-!
# Coframings of a continuous family of oriented planes: the vocabulary

Given a continuous family of oriented `k`-planes in `ℝ^{k+m}` — i.e. a continuous map
`Γ : M → G̃r_k(ℝ^{k+m})` into the oriented Grassmannian, or equivalently (via
`Work.PTGeometric.projOfPlane`) a continuous family `P : M → Gr (k+m) k` of orthogonal projections
of rank `k` — we want to cover `M` by open sets on which the family admits a **coframing**: a
continuously varying isomorphism `e y : ℝ^k ≅ P y` together with a *fixed* linear left inverse
`ℓ : ℝ^{k+m} → ℝ^k`, the coframings of two members of the cover being **orientation related**
(`det (ℓ' ∘ e) > 0`).

This module contains the vocabulary of that construction:

* `cfSignMat ε = diag(ε, 1, …, 1)` and `signCLM ε = matLin (cfSignMat ε)` — the reflection of the first
  coordinate, used to correct the orientation of the chart trivialisations;
* `signMat_eq_orientMat` — on the chart `S` at a point where `frameSign S x = ε`, the correction
  `cfSignMat ε` is exactly the sign gauge `orientMat S x` of `Oriented.lean` (this is what makes the
  positivity of the transition determinants available);
* `coordProjCLM S` — the `S`-coordinate projection as a continuous linear map
  `ℝ^{k+m} → ℝ^k`;
* `coordEvalLin S f`, `cfCoordEvalCLM S f` — the parametrisation `v ↦ coordEval S f v` of the plane
  of the frame `f` by its `S`-coordinates, as a linear (continuous linear) map;
* `coordProjCLM_coordEval`, `coordProjCLM_coordEval_eq` — the two basic identities: the coordinate
  projection is a left inverse of the parametrisation, and it composed with the parametrisation of
  *another* chart is `coordChangeAux`;
* `cfGoodSet Γ i` for `i : ChartIdx k m × Bool` — the open set
  `Γ ⁻¹' (baseSet S ∩ {frameSign S = ±1})`, the members of the covering;
* `ellOf i`, `eOf Γ i y` — the fixed left inverse and the varying parametrisation.
-/

namespace Work.ThomBordism.Grassmann

open scoped Topology

noncomputable section

variable {k m : ℕ}

/-! ## The sign correction `diag(ε, 1, …, 1)` -/

/-- The `±1`-valued sign attached to a `Bool`. -/
def cfSignOf (b : Bool) : ℝ := if b then 1 else -1

@[simp] theorem signOf_true : cfSignOf true = 1 := rfl
@[simp] theorem signOf_false : cfSignOf false = -1 := rfl

theorem signOf_mul_self (b : Bool) : cfSignOf b * cfSignOf b = 1 := by
  cases b <;> norm_num [cfSignOf]

theorem signOf_eq_one_or_eq_neg_one (b : Bool) : cfSignOf b = 1 ∨ cfSignOf b = -1 := by
  cases b <;> simp

theorem signOf_ne_zero (b : Bool) : cfSignOf b ≠ 0 := by
  have := signOf_mul_self b
  intro h; rw [h, mul_zero] at this; exact one_ne_zero this.symm

/-- The matrix `diag(ε, 1, …, 1)` (the identity for `k = 0`). -/
def cfSignMat (ε : ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  if h : k = 0 then 1 else
    Matrix.diagonal fun i : Fin k =>
      if i = (⟨0, Nat.pos_of_ne_zero h⟩ : Fin k) then ε else 1

/-- **The sign correction as a continuous linear endomorphism of `ℝ^k`.** -/
def signCLM (ε : ℝ) : Amb k →L[ℝ] Amb k := matLin (cfSignMat ε)

theorem signCLM_apply (ε : ℝ) (c : Amb k) : signCLM ε c = matLin (cfSignMat ε) c := rfl

theorem cfSignMat_mul_self (ε : ℝ) (hε : ε * ε = 1) :
    cfSignMat (k := k) ε * cfSignMat (k := k) ε = 1 := by
  by_cases h : k = 0
  · rw [cfSignMat, dif_pos h]; exact mul_one 1
  · rw [cfSignMat, dif_neg h, Matrix.diagonal_mul_diagonal]
    have hfun : (fun i : Fin k =>
        (if i = (⟨0, Nat.pos_of_ne_zero h⟩ : Fin k) then ε else 1)
          * (if i = (⟨0, Nat.pos_of_ne_zero h⟩ : Fin k) then ε else 1))
        = fun _ : Fin k => (1 : ℝ) := by
      funext i
      by_cases hi : i = (⟨0, Nat.pos_of_ne_zero h⟩ : Fin k)
      · rw [if_pos hi, hε]
      · rw [if_neg hi]; norm_num
    rw [hfun, Matrix.diagonal_one]

/-- **The sign correction is an involution** on `ℝ^k` whenever `ε² = 1`. -/
theorem signCLM_involutive (ε : ℝ) (hε : ε * ε = 1) (c : Amb k) :
    signCLM ε (signCLM ε c) = c := by
  rw [signCLM_apply, signCLM_apply, ← ContinuousLinearMap.comp_apply, ← matLin_mul,
    cfSignMat_mul_self ε hε, matLin_one]
  rfl

theorem signCLM_injective (ε : ℝ) (hε : ε * ε = 1) :
    Function.Injective (signCLM (k := k) ε) := by
  intro a b hab
  have h1 := congrArg (signCLM ε) hab
  rwa [signCLM_involutive ε hε a, signCLM_involutive ε hε b] at h1

/-- **On a chart, at a point of sign `ε`, the sign correction is the orientation gauge** of
`Oriented.lean`.  This identifies the corrected chart trivialisation with the orientation-consistent
one, whose transition determinants are positive (`det_coordChangeO_pos`). -/
theorem signMat_eq_orientMat {S : ChartIdx k m} {x : OG k m} {ε : ℝ}
    (hx : frameSign S x = ε) : cfSignMat ε = orientMat S x := by
  by_cases h : k = 0
  · rw [cfSignMat, dif_pos h, orientMat, dif_pos h]
  · rw [cfSignMat, dif_neg h, orientMat_of_ne_zero h]
    congr 1
    funext i
    by_cases hi : i = (⟨0, Nat.pos_of_ne_zero h⟩ : Fin k)
    · rw [if_pos hi, if_pos hi, hx]
    · rw [if_neg hi, if_neg hi]

/-! ## The `S`-coordinate projection as a continuous linear map -/

/-- **The `S`-coordinate projection** `ℝ^{k+m} → ℝ^k` (in the coordinates in `S`, ordered by
`Finset.equivFinOfCardEq`), as a continuous linear map. -/
def coordProjCLM (S : ChartIdx k m) : Amb (k + m) →L[ℝ] Amb k :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => WithLp.toLp 2 (coordProj S (WithLp.ofLp v))
      map_add' := by
        intro v w
        rw [WithLp.ofLp_add, map_add, WithLp.toLp_add]
      map_smul' := by
        intro c v
        rw [WithLp.ofLp_smul, map_smul, WithLp.toLp_smul]
        rfl }

theorem coordProjCLM_apply (S : ChartIdx k m) (v : Amb (k + m)) :
    coordProjCLM S v = WithLp.toLp 2 (coordProj S (WithLp.ofLp v)) := rfl

/-- **The coordinate projection is a left inverse of the chart parametrisation.** -/
theorem coordProjCLM_coordEval (S : ChartIdx k m) (f : Stiefel k m) (v : Amb k)
    (hf : f ∈ chartSet S) : coordProjCLM S (coordEval S f v) = v := by
  rw [coordProjCLM_apply, coordProj_coordEval S f v hf, WithLp.toLp_ofLp]

/-- **The chart parametrisation of `S` followed by the coordinate projection of `T` is the
transition function `coordChangeAux`.** -/
theorem coordProjCLM_coordEval_eq (S T : ChartIdx k m) (f : Stiefel k m)
    (hS : f ∈ chartSet S) (hT : f ∈ chartSet T) (u : Amb k) :
    coordProjCLM T (coordEval S f u) = coordChangeAux S T f u := by
  rw [coordEval_coordChangeAux S T f hS hT u]
  exact coordProjCLM_coordEval T f _ hT

/-! ## The chart parametrisation as a (continuous) linear map -/

/-- The chart parametrisation `v ↦ coordEval S f v` of the plane of the frame `f` by the
`S`-coordinates, as a linear map. -/
def coordEvalLin (S : ChartIdx k m) (f : Stiefel k m) : Amb k →ₗ[ℝ] Amb (k + m) where
  toFun := fun v => coordEval S f v
  map_add' := by
    intro v w
    simp only [coordEval, WithLp.ofLp_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' := by
    intro c v
    simp only [coordEval, WithLp.ofLp_smul, Pi.smul_apply, Finset.smul_sum, smul_smul,
      smul_eq_mul, RingHom.id_apply]

theorem coordEvalLin_apply (S : ChartIdx k m) (f : Stiefel k m) (v : Amb k) :
    coordEvalLin S f v = coordEval S f v := rfl

/-- The chart parametrisation as a continuous linear map. -/
def cfCoordEvalCLM (S : ChartIdx k m) (f : Stiefel k m) : Amb k →L[ℝ] Amb (k + m) :=
  LinearMap.toContinuousLinearMap (coordEvalLin S f)

theorem cfCoordEvalCLM_apply (S : ChartIdx k m) (f : Stiefel k m) (v : Amb k) :
    cfCoordEvalCLM S f v = coordEval S f v := rfl

/-- The parametrised vectors lie in the plane of the frame. -/
theorem coordEval_mem_span (S : ChartIdx k m) (f : Stiefel k m) (v : Amb k) :
    coordEval S f v ∈ Submodule.span ℝ (Set.range (f.1 : Fin k → Amb (k + m))) := by
  rw [coordEval]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (coordVec_mem_span S f i)

/-- The parametrised vectors lie in the plane of the frame, in the `memPlane` form. -/
theorem memPlane_coordEval (S : ChartIdx k m) (f : Stiefel k m) (v : Amb k) :
    memPlane (Quotient.mk'' f) (coordEval S f v) :=
  (Work.PTGeometric.memPlane_mk_iff f (coordEval S f v)).mpr (coordEval_mem_span S f v)

/-! ## The covering and the coframings -/

/-- **The members of the covering**: for `i = (S, b)` the set of points `y` of `M` whose plane
`Γ y` lies in the chart `S` and has sign `cfSignOf b` there.  It is written as the pullback of
`{x ∈ baseSet S : frameSign S x ≠ -cfSignOf b}`, which is *open* (the complement of the closed set
`{frameSign S = -cfSignOf b}` intersected with the open `baseSet S`); on `baseSet S` the sign is `±1`
(`frameSign_mul_self`), so this is exactly `{x : x ∈ baseSet S, frameSign S x = cfSignOf b}`. -/
def cfGoodSet {M : Type} [TopologicalSpace M] (Γ : M → OG k m)
    (i : ChartIdx k m × Bool) : Set M :=
  Γ ⁻¹' {x | x ∈ baseSet i.1 ∧ frameSign i.1 x ≠ -cfSignOf i.2}

theorem mem_goodSet {M : Type} [TopologicalSpace M] {Γ : M → OG k m}
    {i : ChartIdx k m × Bool} {y : M} :
    y ∈ cfGoodSet Γ i ↔ Γ y ∈ baseSet i.1 ∧ frameSign i.1 (Γ y) ≠ -cfSignOf i.2 := Iff.rfl

/-- **The members of the covering are open.** -/
theorem isOpen_goodSet {M : Type} [TopologicalSpace M] {Γ : M → OG k m}
    (hΓc : Continuous Γ) (i : ChartIdx k m × Bool) : IsOpen (cfGoodSet Γ i) := by
  have hset : {x : OG k m | x ∈ baseSet i.1 ∧ frameSign i.1 x ≠ -cfSignOf i.2}
      = baseSet i.1 ∩ frameSign i.1 ⁻¹' ({-(cfSignOf i.2)}ᶜ : Set ℝ) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff,
      Set.mem_singleton_iff, ne_eq]
  rw [cfGoodSet, hset]
  exact ((continuousOn_frameSign i.1).isOpen_inter_preimage (isOpen_baseSet i.1)
    isClosed_singleton.isOpen_compl).preimage hΓc

/-- On a member of the covering the sign really is `cfSignOf b` (because it is `±1` on a chart). -/
theorem frameSign_eq_of_mem_goodSet {M : Type} [TopologicalSpace M] {Γ : M → OG k m}
    {i : ChartIdx k m × Bool} {y : M} (hy : y ∈ cfGoodSet Γ i) :
    frameSign i.1 (Γ y) = cfSignOf i.2 := by
  have h1 : frameSign i.1 (Γ y) * frameSign i.1 (Γ y) = 1 := frameSign_mul_self _ _ hy.1
  rcases mul_self_eq_one_iff.mp h1 with h | h
  · rcases signOf_eq_one_or_eq_neg_one i.2 with hs | hs
    · exact h.trans hs.symm
    · exact absurd (by rw [h, hs]; norm_num : frameSign i.1 (Γ y) = -cfSignOf i.2) hy.2
  · rcases signOf_eq_one_or_eq_neg_one i.2 with hs | hs
    · exact absurd (by rw [h, hs] : frameSign i.1 (Γ y) = -cfSignOf i.2) hy.2
    · exact h.trans hs.symm

/-- **The fixed left inverse of the coframing over `cfGoodSet Γ (S,b)`**: the sign-corrected
`S`-coordinate projection.  It is a single linear map, independent of the point `y`. -/
def ellOf (i : ChartIdx k m × Bool) : Amb (k + m) →L[ℝ] Amb k :=
  (signCLM (cfSignOf i.2)).comp (coordProjCLM i.1)

theorem ellOf_apply (i : ChartIdx k m × Bool) (w : Amb (k + m)) :
    ellOf i w = signCLM (cfSignOf i.2) (coordProjCLM i.1 w) := rfl

/-- **The varying coframing over `cfGoodSet Γ (S,b)`**: the sign-corrected parametrisation of the
plane of a frame representing `Γ y` by its `S`-coordinates. -/
def eOf {M : Type} [TopologicalSpace M] (Γ : M → OG k m) (i : ChartIdx k m × Bool) (y : M) :
    Amb k →L[ℝ] Amb (k + m) :=
  (cfCoordEvalCLM i.1 (Quotient.out (Γ y))).comp (signCLM (cfSignOf i.2))

theorem eOf_apply {M : Type} [TopologicalSpace M] (Γ : M → OG k m) (i : ChartIdx k m × Bool)
    (y : M) (c : Amb k) :
    eOf Γ i y c = coordEval i.1 (Quotient.out (Γ y)) (signCLM (cfSignOf i.2) c) := rfl

theorem ellOf_eOf {M : Type} [TopologicalSpace M] (Γ : M → OG k m) (i : ChartIdx k m × Bool)
    (y : M) (c : Amb k) :
    ellOf i (eOf Γ i y c)
      = signCLM (cfSignOf i.2)
          (coordProjCLM i.1 (coordEval i.1 (Quotient.out (Γ y)) (signCLM (cfSignOf i.2) c))) :=
  rfl

end

end Work.ThomBordism.Grassmann
