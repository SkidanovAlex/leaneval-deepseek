import Submission.Work.BoxShrink.PinchOff.KeyTame
import Submission.Work.BoxShrink.Pinch.Trace

/-!
# The residual of the pinch in its *box-local* crossing form

The parent chapter factored the residual of the pinch into two statements about the cutting plane
(`Submission/Work/BoxShrink/Pinch/Trace.lean`):

* **(K0)** `TraceLine` — the periods of the trace `F ∩ {plane}` of the cutting plane lie in one line;
* **(K2)** `TracePerpRealisable` — either the box region does not drop to the halves at all, or there
  is a *nonzero* trace class `v` such that every winding class of the box region whose algebraic
  crossing number with `v` vanishes is already realised in the two half-regions together.

(K0) is a **theorem** for the smooth tori of the challenge
(`Work.BoxShrink.Pinch.traceLineSmooth_holds`, from the delegated
`TraceSpanLeOneSmoothHolds`), and the whole of (K2) is open.  The parent chapter's own assembly of
the two, `Work.BoxShrink.Pinch.pushOffHalfTame_of_traceSmooth`, carries the hypothesis
`∀ ψ c σ u, TransverseTrace ψ c σ u` — transversality of the cutting plane along the *whole* trace,
outside the box included — and that hypothesis is **false**: at the standard torus with the box
centre `(1,0,0)`, `s = 13/10`, `σ = (0 1 2)`, `u = 0` the plane is tangent to the surface
(`Work.BoxShrink.PinchOff.not_forall_transverseTrace`).  So that assembly, although proved, cannot
be applied: the deliverable needs the residual with the *box-local* hypothesis `TransverseSlice`
that the assignment names.

This module supplies exactly that.  It states the box-local crossing residual

  `TracePerpSlice` — for every smooth torus, box and plane with a transverse and *tame* slice whose
  slice carries no essential loop, the parent's factored statement `TracePerpRealisable` holds,

proves that it gives the corrected residual of this chapter (`smoothHalfSTame_of_tracePerpSlice`,
through the tamed dimension bound `KeyTame` and the dichotomy at the box region), and records the
configurations in which it is inhabited.  It is the *usable* form of the parent's route: after this
module the deliverable `Work.BoxShrink.Pinch.PushOffHalfTame` follows from a single geometric
statement about the box, with no false hypothesis anywhere on the path.

## Where the mathematics of `TracePerpSlice` is

`TracePerpSlice` is not refuted, and (K0)'s part of it is proved for the configurations in which the
line of the trace is available.  What it *is* is Pardon's Lemma 3 itself, in the sharpest form the
workspace has isolated: the classes of the box region perpendicular to the trace's direction can be
pushed off the trace (their algebraic crossing number with every trace component vanishes, so the
crossings can be cancelled pairwise), the pairs being cancelled by a homotopy *inside the box*.  The
difficulty is that the cancellation bigon can in principle leave the box when the trace has arcs —
the arcs end on the boundary sphere `∂Ω = {B = s}` — and it is the convexity of Pardon's box that
rules this out in the plane slice `D = PBox ∩ {plane}`, in which the trace lies.  See `README.md` §3
for the state of that argument.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff

noncomputable section

variable {ψ : Submission.Diffeo} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}

/-! ## The box-local crossing residual -/

/-- **The residual of the pinch in box-local crossing form.**  For every smooth torus of the
challenge, every box and every plane whose slice is transverse (`TransverseSlice`) and tame
(`TameSlice`) and whose slice carries no essential loop, the parent chapter's factored statement
`Work.BoxShrink.Pinch.TracePerpRealisable` holds: either the box region does not drop to the two
half-regions at all, or some nonzero class `v` of the trace's line has all the classes of the box
region perpendicular to it already realised in the two half-regions.

This is the parent's `Work.BoxShrink.Pinch.TracePerpSmooth` with the *global* transversality
hypothesis `TransverseTrace` replaced by the box-local one, which is what the assignment allows and
what the deliverable needs (`TracePerpSmooth` remains implied by this statement wherever the global
hypothesis does hold; see `tracePerpSlice_of_tracePerpSmooth`). -/
def TracePerpSlice : Prop :=
  ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u → Work.BoxShrink.Pinch.TameSlice ψ s c σ u →
    ¬ (surface ψ).ContainsEssentialLoop (Sigma ψ s c σ u) →
    Work.BoxShrink.Pinch.TracePerpRealisable (surface ψ) s c σ u

/-- **The parent's (K2) implies the box-local one**, at the configurations where the cutting plane
is transverse along the whole trace.  (That hypothesis is refuted for *all* configurations
(`Work.BoxShrink.PinchOff.not_forall_transverseTrace`), which is why the box-local form above is the
one to prove.) -/
theorem tracePerpSlice_of_tracePerpSmooth (h : Work.BoxShrink.Pinch.TracePerpSmooth)
    (hT : ∀ (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.BoxShrink.Pinch.TransverseTrace ψ c σ u) : TracePerpSlice :=
  fun ψ s c σ u _ hTame hZ =>
    (h ψ s c σ u (hT ψ c σ u) hTame hZ).elim (fun hv => Or.inr hv) (fun hle => Or.inl hle)

/-! ## The residual gives the tamed dimension bound and the corrected residual -/

/-- **The box-local crossing residual gives the tamed dimension bound.**  In the first alternative
the bound is monotonicity of the dimension; in the second it is the linear algebra of the
intersection form on `ℚ² = H₁(T²;ℚ)`: the kernel of the nonzero functional `cross · v` is
one-dimensional (`Work.BoxShrink.Pinch.finrank_le_succ_of_inf_ker_le`). -/
theorem keyTame_of_tracePerpSlice (h : TracePerpSlice) : KeyTame := by
  intro ψ s c σ u hT hTame hS hZ
  rcases h ψ s c σ u hT hTame hZ with hle | ⟨v, hv, _hL, hperp⟩
  · exact Nat.le_add_right_of_le (Submodule.finrank_mono hle)
  · exact Work.BoxShrink.Pinch.finrank_le_succ_of_inf_ker_le hv hperp

/-- **The box-local crossing residual gives the corrected residual of the chapter**
(`SmoothHalfSTame` = the parent's `PushOffHalfTame`), given the general position of the box-sphere
trace (`BoxSliceNice`).  This is the deliverable's route with no false hypothesis on it. -/
theorem smoothHalfSTame_of_tracePerpSlice (hnice : Work.BoxShrink.Pinch.BoxSliceNice)
    (h : TracePerpSlice) : SmoothHalfSTame :=
  smoothHalfSTame_of_keyTame hnice (keyTame_of_tracePerpSlice h)

/-- The same, in the parent chapter's own name. -/
theorem pushOffHalfTame_of_tracePerpSlice (hnice : Work.BoxShrink.Pinch.BoxSliceNice)
    (h : TracePerpSlice) : Work.BoxShrink.Pinch.PushOffHalfTame :=
  smoothHalfSTame_of_tracePerpSlice hnice h

/-- **End to end**: the box-local crossing residual, Pardon's equation (1) (discharged in
`Dichotomy.lean`) and the general position of the box-sphere trace give Pardon's Lemma 3 for the
smooth tori of the challenge under the two endpoint hypotheses. -/
theorem smoothHalfS_of_tracePerpSlice (hnice : Work.BoxShrink.Pinch.BoxSliceNice)
    (h : TracePerpSlice)
    (htrans : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u)
    (htame : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.BoxShrink.Pinch.TameSlice ψ s c σ u) :
    Work.BoxShrink.Pinch.SmoothHalfS :=
  Work.BoxShrink.Pinch.smoothHalfS_of_pushOffHalfTame
    (pushOffHalfTame_of_tracePerpSlice hnice h) htrans htame

/-! ## The configurations in which the residual is inhabited -/

/-- **The residual holds whenever the box region does not drop to the halves**: the first
alternative of `TracePerpRealisable` is then satisfied. -/
theorem tracePerpSlice_of_span_le
    (h : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.SurgeryInvariance.WindingSpan (surface ψ) (Omega ψ s c σ) ≤
        Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u)) : TracePerpSlice :=
  fun ψ s c σ u _ _ _ => Or.inl (h ψ s c σ u)

/-- **The residual holds whenever the box region is inessential**: then its span is `⊥` and every
inclusion holds. -/
theorem tracePerpSlice_of_boxRegion_inessential
    (h : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      ¬ (surface ψ).ContainsEssentialLoop (Omega ψ s c σ)) : TracePerpSlice :=
  tracePerpSlice_of_span_le fun ψ s c σ u => by
    rw [(Work.SurgeryInvariance.WindingSpan_eq_bot_iff _ _).mpr (h ψ s c σ u)]
    exact bot_le

/-- **The residual holds whenever every slice is carried by disjoint discs inside the box** (the
configuration of the assignment's named partial target): then the two spans are *equal*
(`strong_of_slice_in_discs`), so the box region does not drop. -/
theorem tracePerpSlice_of_slice_in_discs
    (h : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      ∃ L : List (Work.SurgeryInvariance.DiscRegion (surface ψ)), L.Nodup ∧
        (∀ D ∈ L, ∀ D' ∈ L, D ≠ D' → Disjoint D.carrier D'.carrier) ∧
        (∀ D ∈ L, D.carrier ⊆ Omega ψ s c σ) ∧
        (∀ x ∈ Sigma ψ s c σ u, ∃ D ∈ L, x ∈ D.interior)) : TracePerpSlice :=
  tracePerpSlice_of_span_le fun ψ s c σ u => by
    obtain ⟨L, hn, hd, hs, hc⟩ := h ψ s c σ u
    exact le_of_eq (strong_of_slice_in_discs L hn hd hs hc)

/-- **The kernel of `cross · v` for `v ≠ 0` is contained in the line spanned by `v`** (the
intersection form of `ℚ²` is symplectic). -/
theorem ker_crossLin_le_span {v : ℚ × ℚ} (hv : v ≠ 0) :
    LinearMap.ker (Work.BoxShrink.Pinch.crossLin v) ≤ Submodule.span ℚ {v} := by
  intro w hw
  have hwv : Work.BoxShrink.Pinch.cross w v = 0 := hw
  rw [Submodule.mem_span_singleton]
  rcases eq_or_ne v.1 0 with h1 | h1
  · have h2 : v.2 ≠ 0 := by
      intro h2
      exact hv (Prod.ext h1 h2)
    have hw1 : w.1 = 0 := by
      have h0 : w.1 * v.2 = 0 := by simpa [Work.BoxShrink.Pinch.cross, h1] using hwv
      exact (mul_eq_zero.mp h0).resolve_right h2
    refine ⟨w.2 / v.2, ?_⟩
    ext <;> simp [hw1, h1]
    field_simp
  · have hw2 : w.2 * v.1 = w.1 * v.2 := by
      have h := hwv
      simp only [Work.BoxShrink.Pinch.cross] at h
      linarith
    refine ⟨w.1 / v.1, ?_⟩
    ext <;> simp
    · field_simp
    · field_simp
      linarith

/-- **The residual holds when the trace line is not realised in the box region**: if the trace's
line `L` is nontrivial and disjoint from the box region's winding span, then every class of the box
region perpendicular to a trace class is zero, hence trivially realised in the halves. -/
theorem tracePerpSlice_of_span_disjoint_traceLine
    (hL : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      ∃ L : Submodule ℚ (ℚ × ℚ), Work.BoxShrink.Pinch.TraceLine (surface ψ) c σ u L ∧
        L ≠ ⊥ ∧
        Work.SurgeryInvariance.WindingSpan (surface ψ) (Omega ψ s c σ) ⊓ L = ⊥) :
    TracePerpSlice := by
  intro ψ s c σ u _ _ _
  obtain ⟨L, hline, hLne, hdisj⟩ := hL ψ s c σ u
  obtain ⟨v, hvL, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hLne
  refine Or.inr ⟨v, hv0, ⟨L, hline, hvL⟩, ?_⟩
  have hker_le : LinearMap.ker (Work.BoxShrink.Pinch.crossLin v) ≤ L :=
    (ker_crossLin_le_span hv0).trans ((Submodule.span_singleton_le_iff_mem v L).mpr hvL)
  have hbot : Work.SurgeryInvariance.WindingSpan (surface ψ) (Omega ψ s c σ) ⊓
      LinearMap.ker (Work.BoxShrink.Pinch.crossLin v) = ⊥ := by
    rw [← le_bot_iff]
    exact le_trans (inf_le_inf_left _ hker_le) (le_of_eq hdisj)
  rw [hbot]
  exact bot_le


/-! ## Pairwise disjoint loops have collinear winding classes -/

/-- **The residual holds for an empty slice**: then the box region *is* the union of the two
half-regions, so the first alternative of `TracePerpRealisable` is satisfied with equality. -/
theorem tracePerpSlice_of_emptySlice
    (h : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Sigma ψ s c σ u = ∅) : TracePerpSlice :=
  tracePerpSlice_of_span_le fun ψ s c σ u => by
    have hbox : Omega ψ s c σ = Halves ψ s c σ u := by
      have hunion : Omega ψ s c σ = Halves ψ s c σ u ∪ Sigma ψ s c σ u :=
        Work.BoxShrink.Core.boxRegion_eq_union (surface ψ) s c σ u
      rw [hunion, h ψ s c σ u, Set.union_empty]
    rw [hbox]

/-- **Pairwise disjoint loops of a parametrised torus have collinear winding classes.**  Each pair
contributes a vanishing algebraic intersection number
(`Work.BoxShrink.Pinch.DisjointLoopsWindingDet`); the intersection form of `ℚ²` is symplectic, so
every class lies in the line spanned by any one nonzero class
(`Work.BoxShrink.Pinch.cross_eq_zero_iff_eq_smul`).

This is ingredient (K0) in the form in which the **components of the trace that meet the box**
supply it: distinct components of a `1`-manifold are pairwise disjoint.  (The parent chapter proves
(K0) in the form `∃ L, TraceLine …` for the *whole* trace, which is why its statement carries the
*global* transversality hypothesis; for the components meeting the box the disjointness above is
enough, and box-local hypotheses suffice.) -/
theorem exists_collinear_windingOf_of_pairwise_disjoint {ι : Type*}
    (P : Work.CoreTopology.ParamTorus) (z : ι → Work.CoreTopology.ClosedCurve P)
    (hdisj : Pairwise fun i j => Disjoint (Set.range (z i).γ) (Set.range (z j).γ)) :
    ∃ L : Submodule ℚ (ℚ × ℚ), Module.finrank ℚ ↥L ≤ 1 ∧
      ∀ i, zzClass (P := P) (z i) ∈ L := by
  by_cases h0 : ∀ i, zzClass (P := P) (z i) = 0
  · exact ⟨⊥, by simp, fun i => by simp [h0 i]⟩
  · push_neg at h0
    obtain ⟨i0, hi0⟩ := h0
    refine ⟨zzLine (Work.SurgeryInvariance.windingOf P (z i0)), ?_, fun i => ?_⟩
    · have hv : zzCast (Work.SurgeryInvariance.windingOf P (z i0)) ≠ 0 := fun h => hi0 h
      rw [zzLine, finrank_span_singleton hv]
    · rw [zzLine, Submodule.mem_span_singleton]
      have hne0 : zzClass (P := P) (z i0) ≠ 0 := hi0
      have hcross : Work.BoxShrink.Pinch.cross (zzClass (P := P) (z i))
          (zzClass (P := P) (z i0)) = 0 := by
        rcases eq_or_ne i i0 with rfl | hne
        · exact Work.BoxShrink.Pinch.cross_self _
        · have h := Work.BoxShrink.Pinch.DisjointLoopsWindingDet P (z i) (z i0) (hdisj hne)
          simp only [zzClass, zzCast, Work.BoxShrink.Pinch.cross]
          exact_mod_cast h
      obtain ⟨a, ha⟩ := (Work.BoxShrink.Pinch.cross_eq_zero_iff_eq_smul hne0).mp hcross
      exact ⟨a, ha.symm⟩

end

end Work.BoxShrink.PinchOff
