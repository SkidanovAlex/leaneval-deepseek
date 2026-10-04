import Mathlib
import Submission.Work.Diff.EXT.reactDefs
import Submission.Work.Diff.EXT.towerReactDefs
import Submission.Work.Diff.GE.exists_ON_frame_field_eq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Plumbing lemmas for the reaction ladder of the `k`-th order Shi estimate

This module collects two foundational facts used by every proof of the reaction bound
`Work.Diff.EXT.EvolCompKFixReact k` (the `k`-th order Shi reaction estimate):

* `Work.Diff.EXT.evolX.isFrameNear_exists` — the existence of a smooth field family `Ef` which is an
  orthonormal frame near `x` and whose value at `x` is the prescribed frame `onFrame g x`.  This is
  what makes the definition `Work.Diff.EXT.reactOpEfD` (the reaction traced in the frame *field*
  `Ef`) usable: the trace `∑ m ∇_{Ef m}∇_{Ef m} τ` is the honest rough Laplacian `Δτ` near `x`
  exactly when `Ef` is orthonormal near `x`, and the value at `x` is the `onFrame g x`-trace used in
  the definition of `Work.Diff.EXT.lapCovKRm` when `Ef m x = onFrame g x m`.

* `Work.Diff.EXT.evolX.jetAll_congr_of_eventuallyEq` — **locality of the jets**: the iterated
  covariant derivative `jetAll g j K S G x` depends only on the germ of the packed operator
  `S : (Fin K → TField) → M → ℝ` at `x`.  This is what allows a reaction operator defined through
  *any* smooth auxiliary data (e.g. a frame field, a cutoff, `Classical.epsilon` extensions) to be
  replaced, jet by jet, by its identifiable geometric value near the base point.

Both are independent of the Ricci-flow evolution theory and can be imported freely.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.EXT.evolX

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-! ## The frame field near a point -/

/-- **A smooth field family which is an orthonormal frame near `x` with prescribed value.**  Given a
metric `g`, a point `x` and the chosen frame `onFrame g x` of `TₓM`, there is a family `Ef` of
*globally* `C^∞` fields with `Ef i x = onFrame g x i` which is `g`-orthonormal near `x`
(`Work.Diff.EXT.IsFrameNear`).

Immediate from the proved `Work.Diff.GE.exists_ON_frame_field_eq` (pointwise Gram–Schmidt on the
smooth extensions `smoothExt x (onFrame g x i)` plus a cutoff), applied to the frame
`onFrame g x`. -/
theorem isFrameNear_exists [I.Boundaryless] [T2Space M]
    (g : Submission.Diff.SMet I M) (x : M) :
    ∃ Ef : Fin (Module.finrank ℝ E) → TField (I := I) (M := M),
      IsFrameNear g x Ef ∧ (∀ i, Ef i x = Submission.Diff.onFrame g x i) := by
  obtain ⟨Ef, hval, hsm, hon⟩ :=
    Work.Diff.GE.exists_ON_frame_field_eq (I := I) (M := M) g x
      (Submission.Diff.onFrame g x) (Work.Diff.GE.isONFrame_onFrame g x)
  exact ⟨Ef, ⟨fun i => hsm i, hon⟩, hval⟩

/-! ## Locality of the jets -/

/-- **Congruence of `mvfderiv` for real-valued functions**: it depends only on the germ. -/
theorem mvfderiv_congr_of_eventuallyEq_real' {f g : M → ℝ} {x : M} (h : f =ᶠ[𝓝 x] g) :
    mvfderiv I f x = mvfderiv I g x := by
  rw [mvfderiv, mvfderiv, h.eq_of_nhds, Filter.EventuallyEq.mfderiv_eq h]
  all_goals first | rfl | (ext v; rfl)

/-- **`mvfderiv` is local**: two functions agreeing near `x` have the same `mvfderiv` near `x`. -/
theorem mvfderiv_eventuallyEq_of_eventuallyEq {f g : M → ℝ} {x : M} (h : f =ᶠ[𝓝 x] g) :
    ∀ᶠ y in 𝓝 x, mvfderiv I f y = mvfderiv I g y := by
  obtain ⟨U, hUsub, hUo, hxU⟩ := mem_nhds_iff.mp h
  filter_upwards [hUo.mem_nhds hxU] with y hy
  exact mvfderiv_congr_of_eventuallyEq_real' (I := I)
    (Filter.mem_of_superset (hUo.mem_nhds hy) hUsub)

/-- **Localization of the iterated covariant derivative `jetAll`.**  If two packed operators
`S S' : (Fin K → TField) → M → ℝ` agree near `x` (as functions of the point, for every tuple), then
their `j`-th jets agree near `x`, on every tuple `G`.

The proof is the induction on the jet order `j`, stated for the *eventual* equality at the base
point — the step differentiates the two operators in space, so it needs the inductive hypothesis as
a germ statement: for `j + 1` both sides are `extStep`, i.e. a `mvfderiv` term plus the Leibniz
corrections in the slots of the running tuple; the `mvfderiv` terms agree near `x`
(`mvfderiv_eventuallyEq_of_eventuallyEq`), and the finitely many correction terms agree near `x` by
the induction hypothesis. -/
theorem jetAll_eventuallyEq_of_eventuallyEq {g : Submission.Diff.SMet I M} :
    ∀ (j : ℕ) (K : ℕ)
      (S S' : (Fin K → TField (I := I) (M := M)) → M → ℝ) (x : M),
      (∀ F, S F =ᶠ[𝓝 x] S' F) →
      ∀ G : Fin (K + j) → TField (I := I) (M := M),
        jetAll g j K S G =ᶠ[𝓝 x] jetAll g j K S' G := by
  intro j
  induction j with
  | zero =>
      intro K S S' x h G
      exact h G
  | succ l ih =>
      intro K S S' x h G
      simp only [jetAll]
      simp only [extStep, Pi.sub_apply, Finset.sum_apply]
      -- the `mvfderiv` integrands agree near `x`
      have hmv : ∀ᶠ y in 𝓝 x,
          mvfderiv I (fun y' : M => jetAll g l K S (fun i : Fin (K + l) => G i.succ) y') y
            (G 0 y)
          = mvfderiv I (fun y' : M => jetAll g l K S' (fun i : Fin (K + l) => G i.succ) y') y
            (G 0 y) := by
        filter_upwards [mvfderiv_eventuallyEq_of_eventuallyEq (I := I)
          (ih K S S' x h (fun i : Fin (K + l) => G i.succ))] with y hy
        exact congrArg (fun L : TangentSpace I y →L[ℝ] ℝ => L (G 0 y)) hy
      -- the Leibniz corrections agree near `x`
      have hcorr : ∀ᶠ y in 𝓝 x, ∀ s : Fin (K + l),
          jetAll g l K S
              (Function.update (fun i : Fin (K + l) => G i.succ) s
                (dirF g ((fun i : Fin (K + l) => G i.succ) s) (G 0))) y
            = jetAll g l K S'
              (Function.update (fun i : Fin (K + l) => G i.succ) s
                (dirF g ((fun i : Fin (K + l) => G i.succ) s) (G 0))) y :=
        Filter.eventually_all.mpr fun s =>
          ih K S S' x h (Function.update (fun i : Fin (K + l) => G i.succ) s
            (dirF g ((fun i : Fin (K + l) => G i.succ) s) (G 0)))
      filter_upwards [hmv, hcorr] with y hy1 hy2
      rw [hy1, Finset.sum_congr rfl (fun s _ => hy2 s)]

/-- **Locality of the jets at a point**, the form used by the ladder: two packed operators agreeing
near `x` have equal `j`-th jets at `x`, on every tuple. -/
theorem jetAll_congr_of_eventuallyEq {g : Submission.Diff.SMet I M} {K j : ℕ}
    {S S' : (Fin K → TField (I := I) (M := M)) → M → ℝ} {x : M}
    (h : ∀ F, S F =ᶠ[𝓝 x] S' F) (G : Fin (K + j) → TField (I := I) (M := M)) :
    jetAll g j K S G x = jetAll g j K S' G x :=
  (jetAll_eventuallyEq_of_eventuallyEq (I := I) (M := M) j K S S' x h G).eq_of_nhds

end Work.Diff.EXT.evolX
