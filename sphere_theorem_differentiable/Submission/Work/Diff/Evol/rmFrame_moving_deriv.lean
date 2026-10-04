import Mathlib
import Submission.Work.Diff.Evol.Deps
import Submission.Work.Diff.Evol.rmFrameHelpers
import Submission.Work.Diff.Evol.rmP_moving_general

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Derivative of the curvature components in a moving orthonormal frame

`Work.Diff.Evol.rmFrame_moving_deriv`: if `e : ℝ → (Fin n → TₓM)` is a moving family of frames,
`e t` is the `G t`-orthonormal frame `f`, and the vectors move with velocities
`e' i = ∑ p, Md i p • f p` while the curvature components in the *fixed* frame have derivatives `D`,
then the curvature components `s ↦ rmFrame (G s) x (e s)` in the moving frame are differentiable
with the product-rule derivative

`D i j k l + ∑ p (Md i p * R p j k l + Md j p * R i p k l + Md k p * R i j p l + Md l p * R i j k p)`,

where `R = rmP (G t) x (f ·) (f ·) (f ·) (f ·)`.

The proof applies `Work.Diff.Evol.rmP_moving_general` componentwise and collapses the resulting
`4`-fold product-rule sum with `Work.Diff.Evol.collapse_bridge`.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Work.Diff.Evol

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Finset

theorem rmFrame_moving_deriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [T2Space M]
    (hLC : LCSmooth I M) (G : ℝ → SMet I M) (t : ℝ) (x : M)
    (f : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (e : ℝ → Fin (Module.finrank ℝ E) → TangentSpace I x)
    (Md : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ)
    (D : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
         Fin (Module.finrank ℝ E) → ℝ)
    (he : ∀ i, e t i = f i)
    (hon : ∀ i j, (G t).inner x (f i) (f j) = if i = j then (1 : ℝ) else 0)
    (hd : ∀ i, HasDerivAt (fun s ↦ ((e s i : TangentSpace I x) : E))
            (((∑ p, Md i p • f p : TangentSpace I x)) : E) t)
    (hD : ∀ p q r u, HasDerivAt (fun s ↦ rmP (G s) x (f p) (f q) (f r) (f u)) (D p q r u) t) :
    HasDerivAt (fun s ↦ rmFrame (G s) x (e s))
      (fun i j k l ↦ D i j k l
        + ∑ p, (Md i p * rmP (G t) x (f p) (f j) (f k) (f l)
              + Md j p * rmP (G t) x (f i) (f p) (f k) (f l)
              + Md k p * rmP (G t) x (f i) (f j) (f p) (f l)
              + Md l p * rmP (G t) x (f i) (f j) (f k) (f p))) t := by
  classical
  by_cases hn : 0 < Module.finrank ℝ E
  · -- ## Non-degenerate case: `Fin n` is nonempty.
    have hgen : ∀ (i j k l : Fin (Module.finrank ℝ E)),
        HasDerivAt (fun s ↦ rmP (G s) x (e s i) (e s j) (e s k) (e s l))
          (∑ p, ∑ q, ∑ r, ∑ u,
            ((((G t).inner x (f p) (∑ a, Md i a • f a)) *
                (((G t).inner x (f q) (e t j)) *
                  (((G t).inner x (f r) (e t k)) *
                    (((G t).inner x (f u) (e t l)) *
                      rmP (G t) x (f p) (f q) (f r) (f u))))) +
              ((G t).inner x (f p) (e t i)) *
                ((((G t).inner x (f q) (∑ a, Md j a • f a)) *
                    (((G t).inner x (f r) (e t k)) *
                      (((G t).inner x (f u) (e t l)) *
                        rmP (G t) x (f p) (f q) (f r) (f u)))) +
                  ((G t).inner x (f q) (e t j)) *
                    ((((G t).inner x (f r) (∑ a, Md k a • f a)) *
                        (((G t).inner x (f u) (e t l)) *
                          rmP (G t) x (f p) (f q) (f r) (f u))) +
                      ((G t).inner x (f r) (e t k)) *
                        ((((G t).inner x (f u) (∑ a, Md l a • f a)) *
                            rmP (G t) x (f p) (f q) (f r) (f u)) +
                          ((G t).inner x (f u) (e t l)) * D p q r u))))) t := by
      intro i j k l
      exact rmP_moving_general (hLC := hLC) (G := G) (t := t) (x := x) (f := f) (hn := hn)
        (A := fun s => e s i) (B := fun s => e s j) (C := fun s => e s k) (D := fun s => e s l)
        (A' := (∑ a, Md i a • f a : TangentSpace I x))
        (B' := (∑ a, Md j a • f a : TangentSpace I x))
        (C' := (∑ a, Md k a • f a : TangentSpace I x))
        (D' := (∑ a, Md l a • f a : TangentSpace I x))
        (Dc := D) hon (hd i) (hd j) (hd k) (hd l) hD
    -- pointwise function equality: replace the frame by `f`
    have hframe : (fun s => rmFrame (G s) x (e s))
        = (fun s => fun i j k l => rmP (G s) x (e s i) (e s j) (e s k) (e s l)) := by
      funext s; rfl
    rw [hframe]
    -- reduce to components
    rw [hasDerivAt_pi]
    intro i
    rw [hasDerivAt_pi]
    intro j
    rw [hasDerivAt_pi]
    intro k
    rw [hasDerivAt_pi]
    intro l
    -- the component statement
    refine (hgen i j k l).congr_deriv ?_
    have hcoefi : ∀ p, (G t).inner x (f p) (∑ a, Md i a • f a) = Md i p :=
      fun p => inner_frame_sum (G := G) (t := t) hon Md i p
    have hcoefj : ∀ p, (G t).inner x (f p) (∑ a, Md j a • f a) = Md j p :=
      fun p => inner_frame_sum (G := G) (t := t) hon Md j p
    have hcoefk : ∀ p, (G t).inner x (f p) (∑ a, Md k a • f a) = Md k p :=
      fun p => inner_frame_sum (G := G) (t := t) hon Md k p
    have hcoefl : ∀ p, (G t).inner x (f p) (∑ a, Md l a • f a) = Md l p :=
      fun p => inner_frame_sum (G := G) (t := t) hon Md l p
    have hei : e t i = f i := he i
    have hej : e t j = f j := he j
    have hek : e t k = f k := he k
    have hel : e t l = f l := he l
    simp only [hcoefi, hcoefj, hcoefk, hcoefl, hei, hej, hek, hel]
    rw [collapse_bridge (fun a b => (G t).inner x (f a) (f b)) hon Md
          (fun p q r u => rmP (G t) x (f p) (f q) (f r) (f u)) D i j k l]
  · -- ## Degenerate case: `finrank = 0`, so the target type is a subsingleton.
    have h0 : Module.finrank ℝ E = 0 := Nat.eq_zero_of_not_pos hn
    haveI : Subsingleton (Curv4 (Module.finrank ℝ E)) := by
      rw [h0]
      exact ⟨fun a b => funext fun i => Fin.elim0 i⟩
    have hfun : (fun s : ℝ => rmFrame (G s) x (e s))
        = (fun _ : ℝ => rmFrame (G t) x (e t)) := by
      funext s
      exact Subsingleton.elim _ _
    rw [hfun]
    exact (hasDerivAt_const (x := t) (c := rmFrame (G t) x (e t))).congr_deriv
      (Subsingleton.elim (0 : Curv4 (Module.finrank ℝ E)) _)

end Work.Diff.Evol
