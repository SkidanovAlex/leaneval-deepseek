import Submission.HopfRinow2
import Submission.EDist

/-!
# Sub-arcs of a minimising geodesic

If `γ` is a unit-speed curve on `[0,L]` from `p = γ 0` to `q = γ L` whose length equals the
Riemannian distance `d(p,q)`, then every sub-arc `[a,b] ⊆ [0,L]` realises the distance between its
endpoints: `d(γ a, γ b) = b - a`.

The proof is the classical one: the upper bound is the length of the sub-arc, and for the lower
bound one applies the triangle inequality to `d(γ 0, γ L)` together with the length bound on the two
outer arcs.

Main result: `riemannianEDist_eq_ofReal_of_unit_speed_of_minimising`.
-/

set_option linter.unusedSectionVars false

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Submission.Geodesic
open Submission.Length
open Submission.HopfRinow

namespace Submission.Minimising

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

noncomputable section

open Commons.Geometry.Manifold in
/-- **Sub-arcs of a minimising unit-speed curve are minimising.** -/
theorem riemannianEDist_eq_ofReal_of_unit_speed_of_minimising {γ : ℝ → M} {L : ℝ}
    (hL : 0 ≤ L) (hγ : CMDiff[Icc (0:ℝ) L] 1 γ)
    (hsp : ∀ t ∈ Icc (0:ℝ) L, ‖curveVelocity (I := I) γ t‖ = 1)
    (hmin : Manifold.riemannianEDist I (γ 0) (γ L) = ENNReal.ofReal L) :
    ∀ a ∈ Icc (0:ℝ) L, ∀ b ∈ Icc (0:ℝ) L, a ≤ b →
      Manifold.riemannianEDist I (γ a) (γ b) = ENNReal.ofReal (b - a) := by
  intro a ha b hb hab
  have hsub : Icc a b ⊆ Icc (0:ℝ) L := Icc_subset_Icc ha.1 hb.2
  have hγab : CMDiff[Icc a b] 1 γ := hγ.mono hsub
  have hpa : Manifold.riemannianEDist I (γ 0) (γ a) ≤ ENNReal.ofReal a := by
    have h0a : Icc (0:ℝ) a ⊆ Icc (0:ℝ) L := Icc_subset_Icc le_rfl ha.2
    have h := Manifold.riemannianEDist_le_pathELength (I := I) (x := γ 0) (y := γ a)
      (hγ.mono h0a) rfl rfl ha.1
    rw [pathELength_of_unit_speed (I := I) (γ := γ) (a := 0) (b := a)
      (fun t ht => hsp t (h0a ht)), sub_zero] at h
    exact h
  have hpb : Manifold.riemannianEDist I (γ b) (γ L) ≤ ENNReal.ofReal (L - b) := by
    have hbL : Icc b L ⊆ Icc (0:ℝ) L := Icc_subset_Icc hb.1 le_rfl
    have h := Manifold.riemannianEDist_le_pathELength (I := I) (x := γ b) (y := γ L)
      (hγ.mono hbL) rfl rfl hb.2
    rw [pathELength_of_unit_speed (I := I) (γ := γ) (a := b) (b := L)
      (fun t ht => hsp t (hbL ht))] at h
    exact h
  -- upper bound
  have hup : Manifold.riemannianEDist I (γ a) (γ b) ≤ ENNReal.ofReal (b - a) := by
    have h := Manifold.riemannianEDist_le_pathELength (I := I) (x := γ a) (y := γ b)
      hγab rfl rfl hab
    rw [pathELength_of_unit_speed (I := I) (γ := γ) (a := a) (b := b)
      (fun t ht => hsp t (hsub ht))] at h
    exact h
  -- lower bound from the triangle inequality
  have htri1 : Manifold.riemannianEDist I (γ 0) (γ b)
      ≤ Manifold.riemannianEDist I (γ 0) (γ a) + Manifold.riemannianEDist I (γ a) (γ b) :=
    Manifold.riemannianEDist_triangle
  have htri2 : Manifold.riemannianEDist I (γ 0) (γ L)
      ≤ Manifold.riemannianEDist I (γ 0) (γ b) + Manifold.riemannianEDist I (γ b) (γ L) :=
    Manifold.riemannianEDist_triangle
  have hsum : ENNReal.ofReal L ≤ ENNReal.ofReal a + Manifold.riemannianEDist I (γ a) (γ b)
      + ENNReal.ofReal (L - b) := by
    calc ENNReal.ofReal L = Manifold.riemannianEDist I (γ 0) (γ L) := hmin.symm
      _ ≤ Manifold.riemannianEDist I (γ 0) (γ b) + Manifold.riemannianEDist I (γ b) (γ L) := htri2
      _ ≤ (Manifold.riemannianEDist I (γ 0) (γ a) + Manifold.riemannianEDist I (γ a) (γ b))
            + Manifold.riemannianEDist I (γ b) (γ L) := add_le_add htri1 le_rfl
      _ ≤ (ENNReal.ofReal a + Manifold.riemannianEDist I (γ a) (γ b)) + ENNReal.ofReal (L - b) :=
          add_le_add (add_le_add hpa le_rfl) hpb
  have hsplit : ENNReal.ofReal L
      = ENNReal.ofReal a + ENNReal.ofReal (b - a) + ENNReal.ofReal (L - b) := by
    have h1 : ENNReal.ofReal L = ENNReal.ofReal (a + ((b - a) + (L - b))) := by
      congr 1; ring
    have h2 : ENNReal.ofReal (a + ((b - a) + (L - b)))
        = ENNReal.ofReal a + ENNReal.ofReal ((b - a) + (L - b)) :=
      ENNReal.ofReal_add (by linarith [ha.1]) (by linarith [hab, hb.2])
    have h3 : ENNReal.ofReal ((b - a) + (L - b))
        = ENNReal.ofReal (b - a) + ENNReal.ofReal (L - b) :=
      ENNReal.ofReal_add (by linarith [hab]) (by linarith [hb.2])
    rw [h1, h2, h3, add_assoc]
  have hlow : ENNReal.ofReal (b - a) ≤ Manifold.riemannianEDist I (γ a) (γ b) := by
    have h := hsum
    rw [hsplit] at h
    exact (ENNReal.add_le_add_iff_left ENNReal.ofReal_ne_top).mp
      ((ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).mp h)
  exact le_antisymm hup hlow

end

end Submission.Minimising
