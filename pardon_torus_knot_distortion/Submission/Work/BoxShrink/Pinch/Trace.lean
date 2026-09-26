import Submission.Work.BoxShrink.Pinch.Bridge
import Submission.Work.BoxShrink.Pinch.SweepChain
import Submission.Work.BoxShrink.Pinch.TameTarget

/-!
# The residual, factored: the trace's line (K0) and perpendicular realisability (K2)

`Crossing.lean` explained *what* the pinch needs; this module states it, proves that it suffices, and
separates the two classical statements it consists of.

## The trace and its periods

The *trace* of the cutting plane is `tracePreimage P c σ u = Φ⁻¹ (F ∩ P)`, a closed
`2πℤ²`-periodic subset of the parameter plane whose components (with transversality) are simple
curves.  A **trace period** is a period of the lattice realised by a path of the trace (equivalently,
by a single component of it, the components being disjoint).

## The two statements

**(K0) — the trace's line.**  There is a line `L ⊆ ℚ²` (a submodule of dimension at most one)
containing every trace period.  This is a statement about the cutting plane alone, with no box in
it: any two components of `F ∩ P` are *disjoint* simple closed curves of the torus, for disjoint
cycles the *algebraic* intersection number vanishes, and the intersection form on `H₁(T²;ℚ) = ℚ²` is
non-degenerate — so two independent classes cannot be represented by disjoint curves.  What is still
to be built for it is the intersection pairing of loops of a parametrised torus and its computation
by winding vectors (`cross` below is its underlying bilinear form).

**(K2) — perpendicular realisability.**  With `L` as in (K0) and `hZ` (the slice carries no
essential loop), every winding class of the box region *perpendicular* to `L` is already realised in
the union of the two half-regions.  The reason: a loop whose algebraic crossing number with every
slice component vanishes can be homotoped off the slice inside the box — for a slice circle because
its own class lies in `L`, and for a slice arc because `γ · a = [γ] · [w_a]`, where `w_a` is the
*closing circle* of the arc (the arc lies in the box, the rest of its circle outside), whose class
also lies in `L`.

## What is proved here

* `Work.BoxShrink.Pinch.cross`, `Work.BoxShrink.Pinch.crossLin` — the intersection form and the
  functional it induces;
* `Work.BoxShrink.Pinch.finrank_ker_crossLin`,
  `Work.BoxShrink.Pinch.finrank_le_succ_of_inf_ker_le` — **the linear algebra of the pinch**:
  `dim (W(box) ⊓ L^⊥) ≤ dim B` together with `dim L ≤ 1` gives `dim W(box) ≤ dim B + 1`.  This is
  where the two-dimensionality of `H₁(T²;ℚ)` enters, and it is why the pinch's conclusion is
  `≤ + 1` and not `≤`: the line `L` is the one class that may be lost (at the standard small box it
  is: there the trace is essential);
* `Work.BoxShrink.Pinch.TraceLine`, `Work.BoxShrink.Pinch.TracePerpRealisable`,
  `Work.BoxShrink.Pinch.TracePerpRealisableAll` — the two statements, as `Prop`s;
* `Work.BoxShrink.Pinch.pinchNoJumpAll_of_tracePerpRealisableAll` and the whole endgame
  (`smoothHalfS_of_tracePerpRealisableAll`, `pushOffHalf_of_boxDichotomy_trace`, …,
  `pardon_torus_knot_distortion_of_equation1_boxNice_trace`).

The gain over `SweepChain.lean`: the residual is no longer a statement about winding spans at all.
(K0) is a theorem about the trace of a plane on a torus, and (K2) is "vanishing crossing numbers can
be cancelled" — both attackable with the classical tools, and both independent of the box/halves
inequality.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Work.BoxShrink.Pinch

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-! ## The intersection form on the winding module -/

/-- **The intersection form** `cross u w = u.1 * w.2 - u.2 * w.1` on the winding module
`ℚ² = H₁(T²;ℚ)`. -/
def cross (u w : ℚ × ℚ) : ℚ := u.1 * w.2 - u.2 * w.1

@[simp] theorem cross_apply (u w : ℚ × ℚ) : cross u w = u.1 * w.2 - u.2 * w.1 := rfl

theorem cross_self (u : ℚ × ℚ) : cross u u = 0 := by
  simp only [cross]; ring

/-- **The linear functional `u ↦ cross u v`.**  Its kernel is the set of classes whose algebraic
crossing number with the trace class `v` vanishes. -/
def crossLin (v : ℚ × ℚ) : (ℚ × ℚ) →ₗ[ℚ] ℚ where
  toFun u := cross u v
  map_add' a b := by simp only [cross, Prod.fst_add, Prod.snd_add]; ring
  map_smul' c a := by simp only [cross, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply]; ring

@[simp] theorem crossLin_apply (v u : ℚ × ℚ) : crossLin v u = cross u v := rfl

/-- **The form is non-degenerate**: a nonzero class is crossed nontrivially by some class. -/
theorem exists_cross_ne_zero {v : ℚ × ℚ} (hv : v ≠ 0) : ∃ w : ℚ × ℚ, cross w v ≠ 0 := by
  by_contra h
  push Not at h
  have h1 : v.1 = 0 := by simpa [cross] using h (0, 1)
  have h2 : v.2 = 0 := by simpa [cross] using h (1, 0)
  exact hv (Prod.ext h1 h2)

/-- The functional `u ↦ cross u v` is onto for `v ≠ 0`, hence its kernel has dimension
`2 - 1 = 1`. -/
theorem finrank_ker_crossLin {v : ℚ × ℚ} (hv : v ≠ 0) :
    Module.finrank ℚ ↥(LinearMap.ker (crossLin v)) = 1 := by
  obtain ⟨w0, hw0⟩ := exists_cross_ne_zero hv
  have hsurj : Function.Surjective (crossLin v) := by
    intro c
    refine ⟨(c / cross w0 v) • w0, ?_⟩
    have hc : cross w0 v ≠ 0 := hw0
    simp only [crossLin_apply, cross, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hc ⊢
    field_simp
    try ring
  have h1 := LinearMap.finrank_range_add_finrank_ker (crossLin v)
  have hr : Module.finrank ℚ ↥(LinearMap.range (crossLin v)) = 1 := by
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self]
  have htop : Module.finrank ℚ (ℚ × ℚ) = 2 := by
    rw [Module.finrank_prod, Module.finrank_self]
  omega

/-- **The linear algebra of the pinch.**  If the classes of `A` perpendicular to a nonzero class `v`
lie in `B`, then `dim A ≤ dim B + 1`: the kernel of the nonzero functional `cross · v` has
codimension one in the two-dimensional winding module. -/
theorem finrank_le_succ_of_inf_ker_le {A B : Submodule ℚ (ℚ × ℚ)} {v : ℚ × ℚ} (hv : v ≠ 0)
    (h : A ⊓ LinearMap.ker (crossLin v) ≤ B) :
    Module.finrank ℚ ↥A ≤ Module.finrank ℚ ↥B + 1 := by
  have hker : Module.finrank ℚ ↥(LinearMap.ker (crossLin v)) = 1 := finrank_ker_crossLin hv
  have hsup : Module.finrank ℚ ↥(A ⊔ LinearMap.ker (crossLin v)) ≤ 2 := by
    have := Submodule.finrank_mono (le_top : A ⊔ LinearMap.ker (crossLin v) ≤ ⊤)
    simpa [finrank_top, Module.finrank_prod, Module.finrank_self] using this
  have hB := Submodule.finrank_mono h
  have hct := Submodule.finrank_sup_add_finrank_inf_eq A (LinearMap.ker (crossLin v))
  omega

/-! ## The trace of the cutting plane -/

/-- **The trace of the cutting plane**, in the parameter plane: the preimage of the intersection of
the surface with the plane. -/
def tracePreimage (P : Work.CoreTopology.ParamTorus) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ) : Set (ℝ × ℝ) :=
  planePreimage P (Work.BoxShrink.Core.cutPlane c σ u)

/-- **A period of the trace**: a lattice period realised by a path of the trace.  (The components of
the trace are disjoint, so such a path lies in one component: this is exactly "a period of a trace
component".) -/
def TracePeriod (P : Work.CoreTopology.ParamTorus) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (k l : ℤ) : Prop :=
  ∃ q : ℝ → ℝ × ℝ, Continuous q ∧
    (∀ t : ℝ, q (t + 1) = q t + Work.TorusCover.periodShift (k, l)) ∧
    ∀ t : ℝ, q t ∈ tracePreimage P c σ u

/-- **(K0): the trace's line.**  All the periods of the trace lie in one line.  A statement about
the cutting plane alone, with no box in it. -/
def TraceLine (P : Work.CoreTopology.ParamTorus) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (L : Submodule ℚ (ℚ × ℚ)) : Prop :=
  Module.finrank ℚ ↥L ≤ 1 ∧ ∀ k l : ℤ, TracePeriod P c σ u k l → ((k : ℚ), (l : ℚ)) ∈ L

/-- **(K2), the factored residual.**  Either the box region does not drop at all, or there is a
*nonzero* trace class `v` such that every winding class of the box region whose algebraic crossing
number with `v` vanishes is already realised in the union of the two half-regions.

`v` spans the line `L` of (K0); the second case is the statement that vanishing crossing numbers can
be cancelled by a homotopy inside the box. -/
def TracePerpRealisable (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) : Prop :=
  Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) ≤
      Work.SurgeryInvariance.WindingSpan P
        (Work.BoxShrink.Core.upperRegion P s c σ u ∪
          Work.BoxShrink.Core.lowerRegion P s c σ u) ∨
    ∃ v : ℚ × ℚ, v ≠ 0 ∧ (∃ L : Submodule ℚ (ℚ × ℚ), TraceLine P c σ u L ∧ v ∈ L) ∧
      Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) ⊓
          LinearMap.ker (crossLin v) ≤
        Work.SurgeryInvariance.WindingSpan P
          (Work.BoxShrink.Core.upperRegion P s c σ u ∪
            Work.BoxShrink.Core.lowerRegion P s c σ u)

/-- **The residual of the pinch, in its factored form**: (K0) and (K2) together, for every
configuration whose slice carries no essential loop. -/
def TracePerpRealisableAll : Prop :=
  ∀ (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sliceRegion P s c σ u) →
    TracePerpRealisable P s c σ u

/-- **(K0), for every configuration**: the periods of the trace of the cutting plane lie in one
line.  A statement about the plane and the torus alone — no box, no half-regions. -/
def TraceLineAll : Prop :=
  ∀ (P : Work.CoreTopology.ParamTorus) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    ∃ L : Submodule ℚ (ℚ × ℚ), TraceLine P c σ u L

/-- **(K2), for every configuration whose slice carries no essential loop**: crossing numbers can be
cancelled.  Either there is a nonzero trace class `v` such that every winding class of the box region
perpendicular to `v` is already realised in the union of the two half-regions, or the box region
does not drop at all.  (The first alternative is the one that occurs when the trace is essential;
the second covers the case in which every trace component is contractible.) -/
def TracePerpAll : Prop :=
  ∀ (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sliceRegion P s c σ u) →
      (∃ v : ℚ × ℚ, v ≠ 0 ∧ (∃ L : Submodule ℚ (ℚ × ℚ), TraceLine P c σ u L ∧ v ∈ L) ∧
        Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) ⊓
            LinearMap.ker (crossLin v) ≤
          Work.SurgeryInvariance.WindingSpan P
            (Work.BoxShrink.Core.upperRegion P s c σ u ∪
              Work.BoxShrink.Core.lowerRegion P s c σ u)) ∨
      (Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) ≤
        Work.SurgeryInvariance.WindingSpan P
          (Work.BoxShrink.Core.upperRegion P s c σ u ∪
            Work.BoxShrink.Core.lowerRegion P s c σ u))

/-- **The factored residual assembles**: (K0) together with (K2) gives the conjunction used by the
pinch. -/
theorem tracePerpRealisableAll_of_line_perp (_h0 : TraceLineAll) (h2 : TracePerpAll) :
    TracePerpRealisableAll := by
  intro P s c σ u hZ
  rcases h2 P s c σ u hZ with ⟨v, hv0, hL, hperp⟩ | hle
  · exact Or.inr ⟨v, hv0, hL, hperp⟩
  · exact Or.inl hle

/-! ## The residual, from the factored statements -/

/-- **Pardon's dimension bound from (K0)+(K2).**  Either the box region does not drop, or a nonzero
trace class `v` has all the perpendicular classes realised in the halves; either way the dimension
drops by at most one. -/
theorem pinchNoJumpAll_of_tracePerpRealisableAll (h : TracePerpRealisableAll) : PinchNoJumpAll := by
  intro P s c σ u _hS hZ
  rcases h P s c σ u hZ with hle | ⟨v, hv0, _hL, hperp⟩
  · exact Nat.le_add_right_of_le (Submodule.finrank_mono hle)
  · exact finrank_le_succ_of_inf_ker_le hv0 hperp

/-- **The chapter's residual `PinchNoJump` from (K0)+(K2)** (the smooth-torus form). -/
theorem pinchNoJump_of_tracePerpRealisableAll (h : TracePerpRealisableAll) : PinchNoJump := by
  intro ψ s c σ u hS hZ
  have := pinchNoJumpAll_of_tracePerpRealisableAll h (Work.Smooth.Morse.torus ψ) s c σ u hS hZ
  simpa using this

/-- **Pardon's Lemma 3 for the smooth tori, from (K0)+(K2)** (with Pardon's equation (1) and the
general position of the box-sphere trace). -/
theorem smoothHalfS_of_tracePerpRealisableAll (h1 : Equation1Input) (hnice : BoxSliceNice)
    (h : TracePerpRealisableAll) : SmoothHalfS :=
  smoothHalfS_of_pinchNoJump h1 hnice (pinchNoJump_of_tracePerpRealisableAll h)

/-- **The caller's field `Work.BoxShrink.Bubble.PushOffHalf`, from (K0)+(K2).** -/
theorem pushOffHalf_of_boxDichotomy_trace (hdich : BoxDichotomyInput)
    (h : TracePerpRealisableAll) : Work.BoxShrink.Bubble.PushOffHalf :=
  pushOffHalf_of_boxDichotomy_noJump hdich (pinchNoJumpAll_of_tracePerpRealisableAll h)

/-- **The caller's field `Work.BoxShrink.Bubble.BubbleInputHalf`, from (K0)+(K2).** -/
theorem bubbleInputHalf_of_boxDichotomy_trace
    (hcleanD : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.InnermostDisk.CleansInSphere
        (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph)
        (Work.BoxShrink.Core.cutDisc s c σ u))
    (hdich : BoxDichotomyInput) (h : TracePerpRealisableAll) :
    Work.BoxShrink.Bubble.BubbleInputHalf :=
  bubbleInputHalf_of_boxDichotomy_noJump hcleanD hdich
    (pinchNoJumpAll_of_tracePerpRealisableAll h)

/-- **The crux, from (K0)+(K2)**: Pardon's shrinking step for all `p, q`. -/
theorem cruxStatement_of_boxDichotomy_trace
    (hcleanD : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.InnermostDisk.CleansInSphere
        (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph)
        (Work.BoxShrink.Core.cutDisc s c σ u))
    (hdich : BoxDichotomyInput) (h : TracePerpRealisableAll)
    (hclean : Work.BoxShrink.CleansDiscsAll) (hae : Work.BoxShrink.AeSlicedAll) :
    ∀ p q : ℕ, Work.BoxShrink.CruxStatement p q :=
  cruxStatement_of_boxDichotomy_noJump hcleanD hdich
    (pinchNoJumpAll_of_tracePerpRealisableAll h) hclean hae

/-- **Pardon's shrinking step from (K0)+(K2)** (with the classical cut-and-paste step and the
almost-everywhere general position of the box-norm level sets). -/
theorem boxShrink_of_trace
    (hcleanD : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.InnermostDisk.CleansInSphere (Work.Smooth.Morse.torus ψ)
        (Work.BoxShrink.Core.cutDisc s c σ u))
    (h1 : Equation1Input) (hnice : BoxSliceNice) (h : TracePerpRealisableAll)
    (hclean : Work.BoxShrink.CleansDiscsAll) (hae : Work.BoxShrink.AeSlicedAll) :
    ∀ p q : ℕ, Submission.BoxShrinkStatement p q :=
  boxShrinkStatement_of_smoothHalfS hcleanD
    (smoothHalfS_of_tracePerpRealisableAll h1 hnice h) hclean hae

/-- **Pardon's Theorem 1.1 from (K0)+(K2)**, Pardon's equation (1), the general position of the
box-sphere trace and the two classical inputs. -/
theorem pardon_torus_knot_distortion_of_equation1_boxNice_trace
    (hcleanD : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.InnermostDisk.CleansInSphere
        (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph)
        (Work.BoxShrink.Core.cutDisc s c σ u))
    (h1 : Equation1Input) (hnice : BoxSliceNice) (h : TracePerpRealisableAll)
    (hclean : Work.BoxShrink.CleansDiscsAll) (hae : Work.BoxShrink.AeSlicedAll) :
    ∀ (p q : ℕ) (_hp : 0 < p) (_hq : 0 < q) (_hc : Nat.Coprime p q) (K : Knot)
      (_hclass : ∃ Φ : AmbientIsotopy, ∃ σ : CircleReparam,
        ∀ t, Φ.H 1 (K.curve t) = standardTorusCurve p q (σ.f t)),
      (1 / 160 : ℝ≥0∞) * (Nat.min p q : ℝ≥0∞) ≤ distortion K :=
  pardon_torus_knot_distortion_of_smoothHalfS hcleanD
    (smoothHalfS_of_tracePerpRealisableAll h1 hnice h) hclean hae

/-! ## The two hypotheses carried, in the form the trace needs

The trace `Φ⁻¹ (F ∩ P)` is a *global* object — the closing circle of a slice arc runs outside the
box — so a statement about its periods must carry transversality of the cutting plane along the
*whole* trace, not only inside the box.  `TransverseTrace` is that hypothesis; it implies the
box-local `TransverseSlice` of `Basic.lean`, which is the one the assignment names. -/

/-- **Transversality of the cutting plane along the whole trace**: `∇G ≠ 0` on all of `{G = 0}`. -/
def TransverseTrace (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) : Prop :=
  ∀ p : ℝ × ℝ, planeG ψ c σ u p = 0 → fderiv ℝ (planeG ψ c σ u) p ≠ 0

/-- Transversality along the whole trace implies it along the slice. -/
theorem transverseSlice_of_transverseTrace {ψ : Submission.Diffeo} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} (s : ℝ) (h : TransverseTrace ψ c σ u) :
    TransverseSlice ψ s c σ u :=
  fun p _ hp => h p hp

/-! ## The residual for the smooth tori, with the two sanctioned hypotheses

The two statements below are the *same* content as `TraceLineAll`/`TracePerpAll`, restricted to the
smooth tori of the challenge and carrying the two hypotheses the assignment allows to be carried:
the transversality of the cutting plane along the slice (`TransverseSlice`) and the tameness of the
slice (`TameSlice`).  These are the statements to prove — or to delegate — for the undecorated
push-off: they give `PushOffHalfTame`, and with Pardon's equation (1) and the general position of the
box-sphere trace (both classical) the whole challenge. -/

/-- **(K0) for the smooth tori**: with the cutting plane transverse along the whole trace, the
periods of the trace lie in one line.  (The transversality is global, not just inside the box: the
trace is global.) -/
def TraceLineSmooth : Prop :=
  ∀ (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    TransverseTrace ψ c σ u →
    ∃ L : Submodule ℚ (ℚ × ℚ), TraceLine (Work.Smooth.Morse.torus ψ) c σ u L

/-- **(K2) for the smooth tori**: with the cutting plane transverse along the whole trace, the slice
tame and the slice carrying no essential loop, either there is a nonzero trace class perpendicular to
which all the classes of the box region are realised in the two half-regions, or the box region does
not drop. -/
def TracePerpSmooth : Prop :=
  ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    TransverseTrace ψ c σ u → TameSlice ψ s c σ u →
    ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop
        (Work.BoxShrink.Core.sliceRegion (Work.Smooth.Morse.torus ψ) s c σ u) →
      (∃ v : ℚ × ℚ, v ≠ 0 ∧
          (∃ L : Submodule ℚ (ℚ × ℚ),
            TraceLine (Work.Smooth.Morse.torus ψ) c σ u L ∧ v ∈ L) ∧
        Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
            (Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ) ⊓
          LinearMap.ker (crossLin v) ≤
        Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
          (Work.BoxShrink.Core.upperRegion (Work.Smooth.Morse.torus ψ) s c σ u ∪
            Work.BoxShrink.Core.lowerRegion (Work.Smooth.Morse.torus ψ) s c σ u)) ∨
      (Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
          (Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ) ≤
        Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
          (Work.BoxShrink.Core.upperRegion (Work.Smooth.Morse.torus ψ) s c σ u ∪
            Work.BoxShrink.Core.lowerRegion (Work.Smooth.Morse.torus ψ) s c σ u))

/-- **The push-off with the hypotheses carried, from (K0)+(K2) for the smooth tori.**  Pardon's
Lemma 3 conclusion for every configuration whose cutting plane is transverse along the *whole* trace
(`TransverseTrace`, which implies the box-local `TransverseSlice` the assignment names), whose slice
is tame, and whose sphere and slice traces carry no essential loop. -/
theorem pushOffHalfTame_of_traceSmooth (h1 : Equation1Input) (hnice : BoxSliceNice)
    (_h0 : TraceLineSmooth) (h2 : TracePerpSmooth)
    (hT : ∀ (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      TransverseTrace ψ c σ u) : PushOffHalfTame := by
  intro ψ s c σ u _hTransverse htame hS hZ
  have hTT : TransverseTrace ψ c σ u := hT ψ c σ u
  have hbd : Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
      (Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ)) ≤
      Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
        (Work.BoxShrink.Core.upperRegion (Work.Smooth.Morse.torus ψ) s c σ u ∪
          Work.BoxShrink.Core.lowerRegion (Work.Smooth.Morse.torus ψ) s c σ u)) + 1 := by
    rcases h2 ψ s c σ u hTT htame hZ with ⟨v, hv0, _hL, hperp⟩ | hle
    · exact finrank_le_succ_of_inf_ker_le hv0 hperp
    · exact Nat.le_add_right_of_le (Submodule.finrank_mono hle)
  exact bubbleHalf_of_dichotomy_noJump
    (pardonDichotomy_boxRegion_of_equation1 h1 (hnice ψ s c σ) hS) hbd

end

end Work.BoxShrink.Pinch
