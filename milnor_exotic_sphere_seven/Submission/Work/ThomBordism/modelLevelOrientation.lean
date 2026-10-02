import Mathlib
import Submission.Work.PTGeometric.HOFEuclid
import Submission.Work.PTGeometric.HOFXfer
import Submission.Work.Orient.Boundary

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# THOM: the linear half-space model of a cooriented level set

Vocabulary for the project lead's round-34 model lemma (`NOTE_MODEL_AND_SOUNDNESS.md` §2): the model
data, the *splitting* of a linear surjection which fixes the half-space coordinates, and the chart of
the level set.  The model orientation family `modelGamma` (the rule *ambient ⊗ normal⁻¹*, i.e.
`HOF.chartTr` of `HOF.eucFam` along this chart) is the next declaration; see
`NOTE_MODEL_AND_SOUNDNESS.md` §12 for its one remaining elaboration obstruction.

Dimensions: `a` = the level set dimension, `k` = the codimension, ambient `ℝ^{a+k}` (application
`a = 9`, `k ≥ 11` odd).  The *positivity* of a splitting is deliberately **not** a field of
`ModelSplit`: the model lemma's content is that the boundary constant is *independent* of the
splitting among the positive ones.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000


open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Topology

namespace Work.ThomBordism

noncomputable section

/-- The Euclidean model space `ℝ^N`. -/
abbrev Euc (N : ℕ) := EuclideanSpace ℝ (Fin N)

/-- **The half-space model domain** `{x : ℝ^N | 0 ≤ x 0}`. -/
def ModelDomain (N : ℕ) [NeZero N] : Set (Euc N) := {x | 0 ≤ x 0}

/-- **The linear half-space model of a cooriented level set**: `M₀ = {x₀ ≥ 0}`,
`W₀ = M₀ ∩ {v = 0}`. -/
def ModelLevelSet {a k : ℕ} [NeZero (a + k)]
    (v : Euc (a + k) →L[ℝ] Euc k) : Set (Euc (a + k)) :=
  ModelDomain (a + k) ∩ {x | v x = 0}

/-- **A splitting of the linear map `v` respecting the half-space coordinates**: a linear isomorphism
`Φ : ℝ^a × ℝ^k ≃ ℝ^{a+k}` with `v (Φ p) = p.2` and `0 ≤ (Φ p) 0 ↔ 0 ≤ p.1 0`. -/
structure ModelSplit {a k : ℕ} [NeZero a] [NeZero (a + k)] (v : Euc (a + k) →L[ℝ] Euc k) where
  /-- the splitting -/
  Φ : (Euc a × Euc k) ≃L[ℝ] Euc (a + k)
  /-- the second coordinate is `v` -/
  fst : ∀ p : Euc a × Euc k, v (Φ p) = p.2
  /-- the splitting respects the half-space coordinate -/
  half : ∀ p : Euc a × Euc k, 0 ≤ (Φ p) 0 ↔ 0 ≤ p.1 0

/-- The canonical continuous linear equivalence `ℝ^m ≃ (Fin m → ℝ)`. -/
abbrev euclToPi' (m : ℕ) : Euc m ≃L[ℝ] (Fin m → ℝ) := PiLp.continuousLinearEquiv 2 ℝ _

variable {a k : ℕ} [NeZero a] [NeZero (a + k)]
  {v : Euc (a + k) →L[ℝ] Euc k} (s : ModelSplit v)

/-- Continuity of the first coordinate of `ℝ^m` (the `Euc`-version of `continuous_apply`). -/
theorem continuous_coord (m : ℕ) [NeZero m] :
    Continuous fun u : Euc m => u 0 :=
  (continuous_apply (0 : Fin m)).comp (euclToPi' m).continuous

/-- **The point of the model level set over `u : ℝ^a`** (the second factor is `0`, so `v` vanishes). -/
def modelPointOf (u : Euc a) (hu : 0 ≤ u 0) : ↥(ModelLevelSet v) :=
  ⟨s.Φ (u, 0), (s.half (u, 0)).mpr hu, by
    show v (s.Φ (u, 0)) = 0
    rw [s.fst (u, 0)]⟩

/-- The underlying point of `modelPointOf`. -/
@[simp] theorem modelPointOf_val (u : Euc a) (hu : 0 ≤ u 0) :
    (modelPointOf s u hu : Euc (a + k)) = s.Φ (u, 0) := rfl

/-- **The chart source**: the part of the model level set that the chart sends into
`{u : ℝ^a | 0 < u 0}` (the interior), i.e. the domain of the lead's `γ`. -/
def modelChartSource : Set ↥(ModelLevelSet v) :=
  {x | (s.Φ.symm x.1).1 ∈ ({u : Euc a | 0 < u 0} : Set (Euc a))}

theorem isOpen_modelChartSource : IsOpen (modelChartSource s) :=
  (isOpen_lt continuous_const (continuous_coord a)).preimage
    (continuous_fst.comp (s.Φ.symm.continuous.comp continuous_subtype_val))

/-- **The linear chart of the model level set**: the inverse splitting followed by the projection onto
the first factor.  Its target is `{u : ℝ^a | 0 < u 0}` (the interior of the half-space model), which
is exactly the domain of the lead's `γ`. -/
def modelChart : OpenPartialHomeomorph ↥(ModelLevelSet v) (Euc a) where
  toFun x := (s.Φ.symm x.1).1
  invFun u := if hu : u ∈ ({u : Euc a | 0 < u 0} : Set (Euc a)) then
      modelPointOf s u (le_of_lt hu)
    else modelPointOf s 0 (by simp)
  source := modelChartSource s
  target := {u : Euc a | 0 < u 0}
  map_source' := by
    intro x hx
    simpa only [modelChartSource, Set.mem_setOf_eq] using hx
  map_target' := by
    intro u hu
    show (s.Φ.symm ((if hu' : u ∈ ({u : Euc a | 0 < u 0} : Set (Euc a)) then
        modelPointOf s u (le_of_lt hu')
      else modelPointOf s 0 (by simp) : ↥(ModelLevelSet v)) : Euc (a + k))).1
      ∈ ({u : Euc a | 0 < u 0} : Set (Euc a))
    rw [dif_pos hu]
    show (s.Φ.symm (s.Φ (u, 0))).1 ∈ ({u : Euc a | 0 < u 0} : Set (Euc a))
    rw [s.Φ.symm_apply_apply]
    exact hu
  left_inv' := by
    intro x hx
    have hx' : (s.Φ.symm x.1).1 ∈ ({u : Euc a | 0 < u 0} : Set (Euc a)) := by
      simpa only [modelChartSource, Set.mem_setOf_eq] using hx
    show (if hu : ((s.Φ.symm) x.1).1 ∈ ({u : Euc a | 0 < u 0} : Set (Euc a)) then
        modelPointOf s ((s.Φ.symm) x.1).1 (le_of_lt hu)
      else modelPointOf s 0 (by simp)) = x
    rw [dif_pos hx']
    refine Subtype.ext ?_
    show s.Φ (((s.Φ.symm) x.1).1, 0) = x.1
    conv_rhs => rw [← s.Φ.apply_symm_apply x.1]
    congr 1
    refine Prod.ext rfl ?_
    have hx2 : v x.1 = 0 := x.2.2
    have h := s.fst (s.Φ.symm x.1)
    rw [s.Φ.apply_symm_apply x.1] at h
    exact (h.symm.trans hx2).symm
  right_inv' := by
    intro u hu
    show (s.Φ.symm ((if hu' : u ∈ ({u : Euc a | 0 < u 0} : Set (Euc a)) then
        modelPointOf s u (le_of_lt hu')
      else modelPointOf s 0 (by simp) : ↥(ModelLevelSet v)) : Euc (a + k))).1 = u
    rw [dif_pos hu]
    show (s.Φ.symm (s.Φ (u, 0))).1 = u
    rw [s.Φ.symm_apply_apply]
  open_source := isOpen_modelChartSource s
  open_target := isOpen_lt continuous_const (continuous_coord a)
  continuousOn_toFun := (continuous_fst.comp
    (s.Φ.symm.continuous.comp continuous_subtype_val)).continuousOn
  continuousOn_invFun := by
    rw [continuousOn_iff_continuous_domRestrict]
    refine Continuous.subtype_mk
      (Continuous.congr (f := fun p : ↥({u : Euc a | 0 < u 0} : Set (Euc a)) =>
        s.Φ ((p : Euc a), (0 : Euc k))) ?_ ?_) ?_
    · exact s.Φ.continuous.comp (continuous_subtype_val.prodMk
        (continuous_const : Continuous fun _ : ↥({u : Euc a | 0 < u 0} : Set (Euc a)) =>
          (0 : Euc k)))
    · intro p
      show s.Φ ((p : Euc a), (0 : Euc k)) = ((if hu : (p : Euc a) ∈
          ({u : Euc a | 0 < u 0} : Set (Euc a)) then
          modelPointOf s (p : Euc a) (le_of_lt hu)
        else modelPointOf s 0 (by simp) : ↥(ModelLevelSet v)) : Euc (a + k))
      rw [dif_pos p.2]
      exact (modelPointOf_val s (p : Euc a) (le_of_lt p.2)).symm

@[simp] theorem modelChart_apply (x : ↥(ModelLevelSet v)) :
    modelChart s x = (s.Φ.symm x.1).1 := rfl

/-- **The half-space coordinate of a splitting vanishes exactly on the hyperplane.**  `ModelSplit.half`
is a *sign* equivalence, so it forces `(Φ p) 0 = c · p.1 0` with `c > 0`; the `±p` argument below
gives the usable form (the equality `(Φ p) 0 = p.1 0` would be too strong: `Φ = (2·id) × id` is a
legitimate splitting).  This is what makes the boundary chart `y ↦ tail ((Φ.symm y).1)` injective on
`{x₀ = 0}` (`Submission/Work/ThomBordism/modelLevelBoundary.lean`). -/
theorem modelSplit_coord_zero_iff (p : Euc a × Euc k) : (s.Φ p) 0 = 0 ↔ p.1 0 = 0 := by
  have hneg : (s.Φ ((-1 : ℝ) • p)) 0 = -((s.Φ p) 0) := by
    rw [map_smul]
    simp
  have hneg' : ((-1 : ℝ) • p).1 0 = -(p.1 0) := by simp
  constructor
  · intro h
    have h1 : 0 ≤ p.1 0 := (s.half p).mp (ge_of_eq h)
    have h2 : 0 ≤ -(p.1 0) := by
      rw [← hneg']
      exact (s.half ((-1 : ℝ) • p)).mp (by rw [hneg, h]; simp)
    linarith
  · intro h
    have h1 : 0 ≤ (s.Φ p) 0 := (s.half p).mpr (ge_of_eq h)
    have h2 : 0 ≤ -((s.Φ p) 0) := by
      rw [← hneg]
      exact (s.half ((-1 : ℝ) • p)).mpr (by rw [hneg', h]; simp)
    linarith

/-- The strict companion of `ModelSplit.half` and of `modelSplit_coord_zero_iff`: the half-space
coordinate is positive exactly on the interior (this is what makes the chart source/target of
`modelChart` the *interior*). -/
theorem modelSplit_coord_pos_iff (p : Euc a × Euc k) : 0 < (s.Φ p) 0 ↔ 0 < p.1 0 := by
  have hz := modelSplit_coord_zero_iff (s := s) p
  constructor
  · intro h
    rcases lt_or_eq_of_le ((s.half p).mp (le_of_lt h)) with h2 | h2
    · exact h2
    · exact absurd (hz.mpr h2.symm) (ne_of_gt h)
  · intro h
    rcases lt_or_eq_of_le ((s.half p).mpr (le_of_lt h)) with h2 | h2
    · exact h2
    · exact absurd (hz.mp h2.symm) (ne_of_gt h)

/-- The second factor of a splitting vanishes on the model level set (the companion of
`modelSplit_coord_zero_iff` for the `k`-coordinates). -/
theorem modelSplit_symm_snd_zero (x : ↥(ModelLevelSet v)) : (s.Φ.symm x.1).2 = 0 := by
  have h := s.fst (s.Φ.symm x.1)
  rw [s.Φ.apply_symm_apply] at h
  exact h.symm.trans x.2.2

end

end Work.ThomBordism
