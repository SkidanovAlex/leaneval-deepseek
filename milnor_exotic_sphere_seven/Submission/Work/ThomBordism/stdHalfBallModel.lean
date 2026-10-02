import Mathlib
import Submission.Work.ThomBordism.modelLevelBoundary
import Submission.Work.PTGeometric.HOFXfer

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# THOM: the standard half-ball model of a cooriented level set near a boundary point

This file provides the *pure* model vocabulary for the boundary sign of a cooriented level set
(`NOTE_MODEL_AND_SOUNDNESS.md`, `NOTE_MBS_VACUITY.md`): the standard half-ball
`W = {u : ℝ^N | 0 ≤ u 0, ‖u‖ ≤ 1}` — the compact truncation of the half-space model, whose boundary
is the flat face `{u 0 = 0}` together with the spherical part `{‖u‖ = 1}` — and the two *explicit*
charts that make the statement of the model lemma concrete:

* `stdIntChart N` — the identity chart of the interior `{0 < u 0, ‖u‖ < 1}` of `W`, so that "the
  local class of `w` at an interior point is the standard generator" is a formula and not a choice of
  an orientation of `W`;
* `stdFlatChart m` — the chart `y ↦ tail y` of the flat face `{y 0 = 0, ‖y‖ < 1}` of `∂W`
  (`N = m + 1`), i.e. the *piece* coordinates of `∂W`.

The two orientations of the model:

* `stdIntOrient m x hx : LocH ↥W (m+1) x` — the standard generator of the local homology of `W` at
  the interior point `x`, read in `stdIntChart`: the transfer of `HOF.eucFam` along the identity
  chart.  This is the local orientation of `W` that the model lemma's *hypothesis* prescribes;
* `stdFlatGen m hm y hy : LocH ↥∂W m y` — the standard generator of the local homology of the flat
  face at `y`, read in `stdFlatChart`: the transfer of `HOF.eucFam` along the piece coordinates.

The model lemma itself (`Work.ThomBordism.stdHalfBallBoundarySign`) says that the boundary class
`hPairδ w` of a class `w ∈ H_{m+1}(W,∂W)` whose interior local classes are the prescribed ones has,
at every point of the flat face, the local class `c • stdFlatGen`, with `c = ±1` **independent of `w`
and of the point**.  (Only the uniformity of `c` is used downstream; its value is absorbed by
`w ↦ -w`.)

## Why this *pure* form of the model

An earlier round stated the model lemma on the linear model `↥(ModelLevelSet v)` with the splitting
chart of a `ModelSplit v` (and `splitPos`), which is **vacuous**: the linear model is contractible, so
`H_{m+1}(W,∂W) = 0` and the prescribed-local-class hypothesis is unsatisfiable
(`NOTE_MBS_VACUITY.md`).  The *compact* repair is the standard half-ball, which has
`H_{m+1}(W,∂W) ≅ ℤ` and a *single* explicit chart, so the statement needs neither the perturbation
`v` nor a splitting and has no sign ambiguity to resolve:

* a splitting-consistency check (worth recording, since the earlier notes worried about it): if
  `Φ' = Φ ∘ A` is a second splitting, then `ModelSplit.fst` forces `A(p) = (B p.1 + L p.2, p.2)`
  and `ModelSplit.half` forces `L` to land in `{u 0 = 0}`; `half` also forces `B = [[b₀₀, 0],[L', B₀]]`
  with `b₀₀ > 0`.  Hence `det A = b₀₀ · det B₀`, and `splitPos` — which says `det (Φ ∘ std) > 0` — gives
  `0 < b₀₀ · det B₀`, i.e. `det B₀ > 0`.  So a positive splitting does pin the sign of the flat-face
  identification, and the `modelLevelBall` form with `splitPos` is consistent after all.  (This
  contradicts an intermediate worry recorded in a previous session's note; the computation above is
  the resolution.)  The pure form is nevertheless preferable: one chart, no `splitPos`, and the
  transport to the source's geometry is where the positivity has to be proved anyway.

## Lean notes

* `Euc N` is `Work.ThomBordism.Euc N = EuclideanSpace ℝ (Fin N)`, and `Fin N` is only inhabited for
  `N ≠ 0`; the half-ball vocabulary therefore carries `[NeZero N]`.
* `OpenPartialHomeomorph`'s `invFun` must be a total function, so both charts use the usual
  `if hu : u ∈ target then … else default` pattern with an explicit default point (the origin).
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Topology Manifold ContDiff
open Classical
open Work.PTGeometric

namespace Work.ThomBordism

noncomputable section

/-! ## The standard half-ball -/

/-- **The standard half-ball** `{u : ℝ^N | 0 ≤ u 0, ‖u‖ ≤ 1}`. -/
def stdHalfBall (N : ℕ) [NeZero N] : Set (Euc N) := {u | 0 ≤ u 0 ∧ ‖u‖ ≤ 1}

/-- **The boundary of the standard half-ball**: the flat face together with the spherical part. -/
def stdHalfBallBdry (N : ℕ) [NeZero N] : Set ↥(stdHalfBall N) :=
  {y | (y.1 : Euc N) 0 = 0 ∨ ‖(y.1 : Euc N)‖ = 1}

theorem zero_mem_stdHalfBall (N : ℕ) [NeZero N] : (0 : Euc N) ∈ stdHalfBall N := by
  refine ⟨le_of_eq ?_, by simp⟩
  show (0 : Euc N) 0 = 0
  simp

/-- The origin is a boundary point of the standard half-ball. -/
def stdOrigin (N : ℕ) [NeZero N] : ↥(stdHalfBallBdry N) :=
  ⟨⟨0, zero_mem_stdHalfBall N⟩, Or.inl (by simp)⟩

/-- The interior points of the standard half-ball are exactly the points outside the boundary. -/
theorem mem_stdHalfBallInterior_iff (N : ℕ) [NeZero N] (x : ↥(stdHalfBall N)) :
    (0 < (x.1 : Euc N) 0 ∧ ‖(x.1 : Euc N)‖ < 1) ↔ x ∉ stdHalfBallBdry N := by
  constructor
  · intro hx hb
    rcases hb with hb | hb
    · exact absurd hb (ne_of_gt hx.1)
    · exact absurd hb (ne_of_lt hx.2)
  · intro hx
    refine ⟨?_, ?_⟩
    · exact lt_of_le_of_ne x.2.1 (fun h => hx (Or.inl h.symm))
    · exact lt_of_le_of_ne x.2.2 (fun h => hx (Or.inr h))

/-! ## The named target sets of the two charts -/

/-- The interior of the standard half-ball, as a set of the ambient space: the target of
`stdIntChart`. -/
def stdIntTarget (N : ℕ) [NeZero N] : Set (Euc N) := {u : Euc N | 0 < u 0 ∧ ‖u‖ < 1}

/-- The image of the flat chart: the flat face of the boundary, as seen in `ℝ^m`.  This is the target
of `stdFlatChart`. -/
def stdFlatTarget (m : ℕ) : Set (Euc m) := {u : Euc m | ‖consCLM m ((0 : ℝ), u)‖ < 1}

/-! ## The inserted vector -/

/-- The norm of `consCLM m (0, u)` is the norm of `u` (the inserted `0`-th coordinate is `0`). -/
theorem norm_consCLM_zero (m : ℕ) (u : Euc m) : ‖consCLM m ((0 : ℝ), u)‖ = ‖u‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  rw [Fin.sum_univ_succ]
  simp only [consCLM_apply_zero, consCLM_apply_succ, norm_zero, pow_two, zero_mul, zero_add]

/-- `consCLM m (0, u)` lies in the standard half-ball as soon as `‖u‖ ≤ 1`. -/
theorem consCLM_zero_mem_stdHalfBall (m : ℕ) {u : Euc m} (hu : ‖u‖ ≤ 1) :
    consCLM m ((0 : ℝ), u) ∈ stdHalfBall (m + 1) := by
  refine ⟨?_, ?_⟩
  · simp [consCLM_apply_zero]
  · rwa [norm_consCLM_zero]

/-- `consCLM m (0, u)` lies on the flat face of the boundary of the standard half-ball. -/
theorem consCLM_zero_mem_stdHalfBallBdry (m : ℕ) {u : Euc m} (hu : ‖u‖ ≤ 1) :
    (⟨consCLM m ((0 : ℝ), u), consCLM_zero_mem_stdHalfBall m hu⟩ : ↥(stdHalfBall (m + 1)))
      ∈ stdHalfBallBdry (m + 1) :=
  Or.inl (by simp [consCLM_apply_zero])

/-- A vector of `ℝ^{m+1}` whose `0`-th coordinate vanishes is recovered from its tail. -/
theorem consCLM_tail_of_coord_zero (m : ℕ) (x : Euc (m + 1)) (hx : x 0 = 0) :
    consCLM m ((0 : ℝ), tailCLM m x) = x := by
  have h := consCLM_tail m x
  rw [hx] at h
  exact h

/-! ## The interior chart of the standard half-ball -/

/-- The (total) inverse of the identity chart of the interior, with the origin as default. -/
def stdIntInv (N : ℕ) [NeZero N] (u : Euc N) : ↥(stdHalfBall N) :=
  if hu : u ∈ stdIntTarget N then ⟨u, hu.1.le, hu.2.le⟩ else ⟨0, zero_mem_stdHalfBall N⟩

/-- **The interior chart of the standard half-ball**: the identity on `{0 < u 0, ‖u‖ < 1}`. -/
def stdIntChart (N : ℕ) [NeZero N] :
    OpenPartialHomeomorph (TopCat.of ↥(stdHalfBall N)) (Euc N) where
  toFun x := (x.1 : Euc N)
  invFun := stdIntInv N
  source := {x : ↥(stdHalfBall N) | (x.1 : Euc N) ∈ stdIntTarget N}
  target := stdIntTarget N
  map_source' := fun _ hx => hx
  map_target' := by
    intro u hu
    show stdIntInv N u ∈ ({x : ↥(stdHalfBall N) | (x.1 : Euc N) ∈ stdIntTarget N} :
      Set ↥(stdHalfBall N))
    have hu' : u ∈ stdIntTarget N := hu
    unfold stdIntInv
    rw [dif_pos hu']
    exact hu'
  left_inv' := by
    intro x hx
    show stdIntInv N (x.1 : Euc N) = x
    have hx' : (x.1 : Euc N) ∈ stdIntTarget N := hx
    unfold stdIntInv
    rw [dif_pos hx']
  right_inv' := by
    intro u hu
    show (stdIntInv N u).1 = u
    have hu' : u ∈ stdIntTarget N := hu
    unfold stdIntInv
    rw [dif_pos hu']
  open_source := by
    show IsOpen ((Subtype.val) ⁻¹' ({u : Euc N | 0 < u 0} ∩ {u : Euc N | ‖u‖ < 1}))
    exact ((isOpen_lt continuous_const (continuous_coord N)).inter
      (isOpen_lt continuous_norm continuous_const)).preimage continuous_subtype_val
  open_target := by
    show IsOpen ({u : Euc N | 0 < u 0} ∩ {u : Euc N | ‖u‖ < 1})
    exact (isOpen_lt continuous_const (continuous_coord N)).inter
      (isOpen_lt continuous_norm continuous_const)
  continuousOn_toFun := continuous_subtype_val.continuousOn
  continuousOn_invFun := by
    rw [continuousOn_iff_continuous_domRestrict]
    have h : Set.domRestrict (stdIntTarget N) (stdIntInv N)
        = fun p : ↥(stdIntTarget N) =>
            (⟨(p : Euc N), p.2.1.le, p.2.2.le⟩ : ↥(stdHalfBall N)) := by
      funext p
      show stdIntInv N (p : Euc N) = _
      unfold stdIntInv
      rw [dif_pos p.2]
    rw [h]
    exact Continuous.subtype_mk continuous_subtype_val _

/-! ## The flat chart of the boundary of the standard half-ball -/

/-- The (total) inverse of the flat chart, with the origin as default. -/
def stdFlatInv (m : ℕ) (u : Euc m) : ↥(stdHalfBallBdry (m + 1)) :=
  if hu : u ∈ stdFlatTarget m then
    ⟨⟨consCLM m ((0 : ℝ), u), ⟨by simp [consCLM_apply_zero], le_of_lt hu⟩⟩,
      Or.inl (by simp [consCLM_apply_zero])⟩
  else stdOrigin (m + 1)

/-- **The flat chart of the boundary of the standard half-ball**: the piece coordinates
`y ↦ tail y` of the flat face `{y 0 = 0, ‖y‖ < 1}` of `∂W`. -/
def stdFlatChart (m : ℕ) :
    OpenPartialHomeomorph (TopCat.of ↥(stdHalfBallBdry (m + 1))) (Euc m) where
  toFun y := tailCLM m (y.1.1 : Euc (m + 1))
  invFun := stdFlatInv m
  source := {y : ↥(stdHalfBallBdry (m + 1)) |
    (y.1.1 : Euc (m + 1)) 0 = 0 ∧ ‖(y.1.1 : Euc (m + 1))‖ < 1}
  target := stdFlatTarget m
  map_source' := by
    intro y hy
    show ‖consCLM m ((0 : ℝ), tailCLM m (y.1.1 : Euc (m + 1)))‖ < 1
    rw [consCLM_tail_of_coord_zero m (y.1.1 : Euc (m + 1)) hy.1]
    exact hy.2
  map_target' := by
    intro u hu
    show ((stdFlatInv m u).1.1 : Euc (m + 1)) 0 = 0 ∧
      ‖((stdFlatInv m u).1.1 : Euc (m + 1))‖ < 1
    unfold stdFlatInv
    rw [dif_pos hu]
    exact ⟨by simp [consCLM_apply_zero], hu⟩
  left_inv' := by
    intro y hy
    show stdFlatInv m (tailCLM m (y.1.1 : Euc (m + 1))) = y
    have h1 : consCLM m ((0 : ℝ), tailCLM m (y.1.1 : Euc (m + 1))) = (y.1.1 : Euc (m + 1)) :=
      consCLM_tail_of_coord_zero m (y.1.1 : Euc (m + 1)) hy.1
    have h2 : tailCLM m (y.1.1 : Euc (m + 1)) ∈ stdFlatTarget m := by
      show ‖consCLM m ((0 : ℝ), tailCLM m (y.1.1 : Euc (m + 1)))‖ < 1
      rw [h1]; exact hy.2
    unfold stdFlatInv
    rw [dif_pos h2]
    exact Subtype.ext (Subtype.ext h1)
  right_inv' := by
    intro u hu
    show tailCLM m (((stdFlatInv m u).1.1 : Euc (m + 1))) = u
    unfold stdFlatInv
    rw [dif_pos hu]
    exact tailCLM_consCLM m 0 u
  open_source := by
    have h : {y : ↥(stdHalfBallBdry (m + 1)) |
        (y.1.1 : Euc (m + 1)) 0 = 0 ∧ ‖(y.1.1 : Euc (m + 1))‖ < 1}
        = {y : ↥(stdHalfBallBdry (m + 1)) | ‖(y.1.1 : Euc (m + 1))‖ < 1} := by
      ext y
      constructor
      · exact fun h => h.2
      · intro h
        rcases y.2 with h0 | h1
        · exact ⟨h0, h⟩
        · have hc : ‖(y.1.1 : Euc (m + 1))‖ < 1 := h
          rw [h1] at hc
          exact absurd hc (lt_irrefl 1)
    rw [h]
    exact isOpen_lt (continuous_norm.comp (continuous_subtype_val.comp continuous_subtype_val))
      continuous_const
  open_target := isOpen_lt (continuous_norm.comp
    ((consCLM m).continuous.comp (Continuous.prodMk continuous_const continuous_id)))
    continuous_const
  continuousOn_toFun := ((tailCLM m).continuous.comp
    (continuous_subtype_val.comp continuous_subtype_val)).continuousOn
  continuousOn_invFun := by
    rw [continuousOn_iff_continuous_domRestrict]
    have h : Set.domRestrict (stdFlatTarget m) (stdFlatInv m)
        = fun p : ↥(stdFlatTarget m) =>
            (⟨⟨consCLM m ((0 : ℝ), (p : Euc m)),
                ⟨by simp [consCLM_apply_zero], le_of_lt (show ‖consCLM m ((0 : ℝ), (p : Euc m))‖
                  < 1 from p.2)⟩⟩,
              Or.inl (by simp [consCLM_apply_zero])⟩ : ↥(stdHalfBallBdry (m + 1))) := by
      funext p
      show stdFlatInv m (p : Euc m) = _
      unfold stdFlatInv
      rw [dif_pos p.2]
    rw [h]
    refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
    exact (consCLM m).continuous.comp (Continuous.prodMk continuous_const continuous_subtype_val)

theorem stdIntChart_source_notMem (N : ℕ) [NeZero N] {x : ↥(stdHalfBall N)}
    (hx : x ∈ (stdIntChart N).source) : x ∉ stdHalfBallBdry N :=
  (mem_stdHalfBallInterior_iff N x).mp hx

/-! ## The two standard orientations -/

/-- **The standard orientation of the interior of the model**: the local class at the interior point
`x` of the relative fundamental class of the standard half-ball, read in the identity chart — i.e. the
transfer of the Euclidean generator `HOF.eucFam` along `stdIntChart`.  This is the local orientation of
the model level set that the model lemma's hypothesis prescribes. -/
noncomputable def stdIntOrient (m : ℕ) (x : ↥(stdHalfBall (m + 1)))
    (hx : x ∈ (stdIntChart (m + 1)).source) :
    Work.Orient.LocH (TopCat.of ↥(stdHalfBall (m + 1))) (m + 1) x :=
  Work.PTGeometric.HOF.chartTr (e := stdIntChart (m + 1)) x hx
    (Work.PTGeometric.HOF.eucFam (m + 1) (by omega) ((stdIntChart (m + 1)) x))

/-- **The standard generator of the flat face of the model**: the transfer of the Euclidean
generator `HOF.eucFam` along the piece coordinates `stdFlatChart`. -/
noncomputable def stdFlatGen (m : ℕ) (hm : 1 ≤ m)
    (y : ↥(stdHalfBallBdry (m + 1))) (hy : y ∈ (stdFlatChart m).source) :
    Work.Orient.LocH (TopCat.of ↥(stdHalfBallBdry (m + 1))) m y :=
  Work.PTGeometric.HOF.chartTr (e := stdFlatChart m) y hy
    (Work.PTGeometric.HOF.eucFam m hm ((stdFlatChart m) y))

end

end Work.ThomBordism
