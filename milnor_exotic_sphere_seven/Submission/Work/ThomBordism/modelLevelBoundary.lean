import Submission.Work.ThomBordism.modelLevelOrientation
import Submission.Work.PTGeometric.nonempty_halfBallSource

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# THOM: the boundary of the linear half-space model of a cooriented level set

Second piece of the project lead's round-34 model lemma (`NOTE_MODEL_AND_SOUNDNESS.md` §2, §7–§11):
the **boundary generator** of the model level set, i.e. the independent description of the induced
orientation of the boundary `∂W₀ = {x₀ = 0} ∩ {v = 0}`.

The model is parametrised by the **boundary dimension** `m` (so that the level set has dimension
`m + 1`): the ambient is `ℝ^{m+1+k}`, the half-space coordinate is the `0`-th one, and

* `Work.ThomBordism.modelBdry` — the closed subset `{x₀ = 0}` of the model level set
  `{x₀ ≥ 0} ∩ {v = 0}` (its boundary, as a manifold with boundary);
* `Work.ThomBordism.modelBdryChart` — the **linear chart** of the boundary:
  `y ↦ tailCLM m ((Φ.symm y).1)` (the coordinates `1,…,m` of the splitting), a *global*
  homeomorphism onto `ℝ^m` (its source and target are everything);
* `Work.ThomBordism.modelBdryGen` — **the boundary generator**: the Euclidean model family
  `Work.PTGeometric.HOF.eucFam m` transferred along the boundary chart.  This is the independent
  description against which the boundary class of ORIENT's relative fundamental class
  (`Work.CorientBdry.locClass_apply`) is compared, with a constant that the model lemma
  (`Work.ThomBordism.modelBoundarySign`) proves to be independent of the level set `v`, the splitting
  `Φ` and the point.

`Work.ThomBordism.ModelSplit.half` is the *equality* `(Φ p) 0 = p.1 0` (not merely a sign
equivalence): with it the boundary chart is well posed (the `0`-coordinate of `(Φ.symm y).1` vanishes
exactly on the boundary), which is what makes `tailCLM` injective there.
-/

set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open Work.PTGeometric
open scoped Topology

namespace Work.ThomBordism

noncomputable section

variable {m k : ℕ} [NeZero (m + 1 + k)] {v : Euc (m + 1 + k) →L[ℝ] Euc k}

/-- **The boundary hyperplane** of the model level set: the points of `{x₀ ≥ 0} ∩ {v = 0}` with
`x₀ = 0`. -/
def modelBdry (s : ModelSplit (a := m + 1) (k := k) v) :
    Set ↥(ModelLevelSet (a := m + 1) (k := k) v) :=
  {x | (x.1 : Euc (m + 1 + k)) 0 = 0}

theorem mem_modelBdry_iff (s : ModelSplit (a := m + 1) (k := k) v)
    (x : ↥(ModelLevelSet (a := m + 1) (k := k) v)) :
    x ∈ modelBdry (k := k) s ↔ (x.1 : Euc (m + 1 + k)) 0 = 0 := Iff.rfl

/-- The `0`-th coordinate of the first factor of the splitting vanishes exactly on the boundary. -/
theorem modelSplit_symm_fst_zero (s : ModelSplit (a := m + 1) (k := k) v)
    {y : ↥(ModelLevelSet (a := m + 1) (k := k) v)}
    (hy : (y.1 : Euc (m + 1 + k)) 0 = 0) : (s.Φ.symm y.1).1 0 = 0 :=
  (modelSplit_coord_zero_iff (s := s) (s.Φ.symm y.1)).mp
    (by rw [s.Φ.apply_symm_apply]; exact hy)

/-- The second factor of the splitting vanishes on the model level set. -/
theorem modelSplit_symm_snd_eq_zero (s : ModelSplit (a := m + 1) (k := k) v)
    (y : ↥(ModelLevelSet (a := m + 1) (k := k) v)) : (s.Φ.symm y.1).2 = 0 := by
  have h := s.fst (s.Φ.symm y.1)
  rw [s.Φ.apply_symm_apply] at h
  exact h.symm.trans y.2.2

/-- **The interior of the model level set is the complement of the boundary hyperplane**, in the
chart form used by `Work.ThomBordism.modelGamma`. -/
theorem modelChartSource_eq_compl (s : ModelSplit (a := m + 1) (k := k) v) :
    (modelChartSource s : Set ↥(ModelLevelSet (a := m + 1) (k := k) v))
      = {x | x ∉ modelBdry (k := k) s} := by
  ext x
  have hiff : 0 < (s.Φ.symm x.1).1 0 ↔ 0 < (x.1 : Euc (m + 1 + k)) 0 := by
    have h := modelSplit_coord_pos_iff (s := s) (s.Φ.symm x.1)
    rw [s.Φ.apply_symm_apply] at h
    exact h.symm
  constructor
  · intro hx hmem
    have h0 : (x.1 : Euc (m + 1 + k)) 0 = 0 := hmem
    have hx' : 0 < (s.Φ.symm x.1).1 0 := hx
    exact absurd (hiff.mp hx') (by rw [h0]; exact lt_irrefl 0)
  · intro hx
    have h0 : (x.1 : Euc (m + 1 + k)) 0 ≠ 0 :=
      fun h => hx (show x ∈ modelBdry (k := k) s from h)
    exact hiff.mpr (lt_of_le_of_ne x.2.1 (Ne.symm h0))

/-- **The linear chart of the boundary** of the model level set: the coordinates `1,…,m` of the
splitting `Φ.symm`.  It is a *global* homeomorphism onto `ℝ^m` (source and target are everything). -/
def modelBdryChart (s : ModelSplit (a := m + 1) (k := k) v) :
    OpenPartialHomeomorph (TopCat.of ↥(modelBdry (k := k) s)) (Euc m) where
  toFun y := tailCLM m ((s.Φ.symm (y : ↥(ModelLevelSet (a := m + 1) (k := k) v)).1).1)
  invFun u := ⟨⟨s.Φ (consCLM m (0, u), 0), by
      exact (s.half (consCLM m (0, u), 0)).mpr (ge_of_eq (consCLM_apply_zero m 0 u)), by
      show v (s.Φ (consCLM m (0, u), 0)) = 0
      rw [s.fst (consCLM m (0, u), 0)]⟩, by
    show (s.Φ (consCLM m (0, u), 0) : Euc (m + 1 + k)) 0 = 0
    exact (modelSplit_coord_zero_iff (s := s) (consCLM m (0, u), 0)).mpr
      (consCLM_apply_zero m 0 u)⟩
  source := Set.univ
  target := Set.univ
  map_source' := by intro x _; trivial
  map_target' := by intro x _; trivial
  left_inv' := by
    intro y _
    refine Subtype.ext (Subtype.ext ?_)
    show s.Φ (consCLM m (0, tailCLM m ((s.Φ.symm (y : ↥(ModelLevelSet (a := m + 1) (k := k) v)).1).1)),
      0) = (y : ↥(ModelLevelSet (a := m + 1) (k := k) v)).1
    rw [← s.Φ.apply_symm_apply (y : ↥(ModelLevelSet (a := m + 1) (k := k) v)).1]
    congr 1
    refine Prod.ext ?_ ?_
    · rw [s.Φ.symm_apply_apply, ← modelSplit_symm_fst_zero (k := k) s y.2]
      exact consCLM_tail m _
    · exact (modelSplit_symm_snd_eq_zero (k := k) s y).symm
  right_inv' := by
    intro u _
    show tailCLM m ((s.Φ.symm (s.Φ (consCLM m (0, u), 0))).1) = u
    rw [s.Φ.symm_apply_apply]
    exact tailCLM_consCLM m 0 u
  open_source := isOpen_univ
  open_target := isOpen_univ
  continuousOn_toFun := ((tailCLM m).continuous.comp (continuous_fst.comp
    (s.Φ.symm.continuous.comp (continuous_subtype_val.comp continuous_subtype_val)))).continuousOn
  continuousOn_invFun :=
    (Continuous.subtype_mk (Continuous.subtype_mk
      (s.Φ.continuous.comp (Continuous.prodMk
        ((consCLM m).continuous.comp (Continuous.prodMk continuous_const continuous_id))
        continuous_const))
      (fun u => ⟨(s.half (consCLM m (0, u), 0)).mpr
        (ge_of_eq (consCLM_apply_zero m 0 u)), by
        show v (s.Φ (consCLM m (0, u), 0)) = 0
        rw [s.fst (consCLM m (0, u), 0)]⟩))
      (fun u => (modelSplit_coord_zero_iff (s := s) (consCLM m (0, u), 0)).mpr
        (consCLM_apply_zero m 0 u))).continuousOn

@[simp] theorem modelBdryChart_source (s : ModelSplit (a := m + 1) (k := k) v) :
    (modelBdryChart (k := k) s).source = Set.univ := rfl

/-- **THE MODEL BOUNDARY GENERATOR**: the orientation of the boundary `∂W₀ = {x₀ = 0} ∩ {v = 0}` of
the model level set given by the standard orientation of the boundary coordinates — the Euclidean
model family `Work.PTGeometric.HOF.eucFam` transferred along the boundary chart
`Work.ThomBordism.modelBdryChart`.  It is the *independent* description of the induced boundary
orientation (the "`∂`-convention applied to `o`" side of the model lemma). -/
noncomputable def modelBdryGen (s : ModelSplit (a := m + 1) (k := k) v) (hm : 1 ≤ m)
    (y : ↥(modelBdry (k := k) s)) :
    Work.Orient.RelH (TopCat.of ↥(modelBdry (k := k) s)) m
      ({y} : Set ↥(modelBdry (k := k) s)) :=
  let U : Work.Orient.RelH (TopCat.of (Euc m)) m
      ({(modelBdryChart (k := k) s) y} : Set (Euc m)) :=
    Work.PTGeometric.HOF.eucFam m hm (modelBdryChart (k := k) s y)
  Work.PTGeometric.HOF.chartTr (e := modelBdryChart (k := k) s) (w := y)
    (hw := by rw [modelBdryChart_source]; exact Set.mem_univ y) U

/-- **Positivity of a splitting**: its determinant against the standard product orientation of
`ℝ^{m+1} × ℝ^k` and the standard orientation of `ℝ^{m+1+k}` is positive.  The model lemma
(`Work.ThomBordism.modelBoundarySign`) is stated for positive splittings, which is the situation in
which the chart of the level set is orientation-preserving. -/
def splitPos (s : ModelSplit (a := m + 1) (k := k) v) : Prop :=
  0 < LinearMap.det (((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := m + 1) (m := k)).toLinearEquiv.trans
    s.Φ.toLinearEquiv : Euc (m + 1 + k) ≃ₗ[ℝ] Euc (m + 1 + k)).toLinearMap)

/-- **The model orientation family at the level dimension `m + 1`**: the rule *ambient ⊗ normal⁻¹*,
`Work.Orient.LocH`-valued, read through the linear chart `Work.ThomBordism.modelChart` supplied by the
splitting.  (This is `Work.ThomBordism.modelGamma` of the model vocabulary, stated at the level
dimension `m + 1` so that it pairs with the boundary vocabulary of this file.)

**Lean note (the defeq loop).**  The two transfers below must be given `chartTr`'s *named* implicit
arguments `(W := …)` and `(N := …)`: without them, the `w`-dependent type `RelH W N {w}` drives
`whnf` into `TopCat.of`/`RelH` and the elaboration does not terminate. -/
noncomputable def modelOrientation (s : ModelSplit (a := m + 1) (k := k) v) (hm : 1 ≤ m)
    (x : ↥(ModelLevelSet (a := m + 1) (k := k) v)) (hx : x ∈ modelChartSource s) :
    Work.Orient.RelH (TopCat.of ↥(ModelLevelSet (a := m + 1) (k := k) v)) (m + 1)
      ({x} : Set ↥(ModelLevelSet (a := m + 1) (k := k) v)) :=
  let U : Work.Orient.RelH (TopCat.of (Euc (m + 1))) (m + 1)
      ({(modelChart (a := m + 1) (k := k) s) x} : Set (Euc (m + 1))) :=
    Work.PTGeometric.HOF.eucFam (m + 1) (by omega) (modelChart (a := m + 1) (k := k) s x)
  Work.PTGeometric.HOF.chartTr (W := TopCat.of ↥(ModelLevelSet (a := m + 1) (k := k) v))
    (N := m + 1) (e := modelChart (a := m + 1) (k := k) s) (w := x) (hw := hx) U

/-- **The closed unit ball** of the ambient model space. -/
def modelBall (m k : ℕ) : Set (Euc (m + 1 + k)) := {x | ‖x‖ ≤ 1}

/-- **The truncated (half-ball) model level set**: the level set intersected with the closed unit
ball.  Unlike `ModelLevelSet` itself this has non-degenerate relative homology
(`H_{m+1}(W₁,∂W₁) ≅ ℤ`, `W₁/∂W₁ ≅ S^{m+1}`), which is what makes the model lemma non-vacuous: on the
untruncated half-space `H_{m+1}(W,∂W) = 0` and `Work.Orient.IsRelFundClass` is unsatisfiable. -/
def modelLevelBall (v : Euc (m + 1 + k) →L[ℝ] Euc k) : Set (Euc (m + 1 + k)) :=
  ModelLevelSet (a := m + 1) (k := k) v ∩ modelBall m k

/-- **The boundary of the truncated model level set**: the flat part `{x₀ = 0}` together with the
spherical part `{‖x‖ = 1}`. -/
def modelLevelBallBdry (v : Euc (m + 1 + k) →L[ℝ] Euc k) :
    Set ↥(modelLevelBall (k := k) v) :=
  {y | (y.1 : Euc (m + 1 + k)) 0 = 0 ∨ ‖(y.1 : Euc (m + 1 + k))‖ = 1}

end

end Work.ThomBordism
