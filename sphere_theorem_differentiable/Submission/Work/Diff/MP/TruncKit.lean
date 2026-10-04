import Mathlib
import Submission.Diff.Evol
import Submission.Work.Diff.MP.Basic
import Submission.Work.Diff.MP.Defs
import Submission.Work.Diff.MP.frobDot_rot
import Submission.Work.Diff.MP.frobInfDist_rmFrame_eq
import Submission.Work.Diff.GE.contMDiff_rmP_fields

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Elementary Frobenius and continuity facts for the truncated family

The Frobenius norm is preserved by `rot A` for `A ∈ O(n)`, so the truncated family
`F t ∩ frobBall (Υ t)` of an `O(n)`-invariant family `F` is `O(n)`-invariant and the Frobenius
distance to it may be computed in any orthonormal frame; and for a fixed metric the distance
`x ↦ frobInfDist (rmC g x) K` is continuous.
-/

set_option maxHeartbeats 8000000

namespace Work.Diff.MP

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

/-! ## Elementary Frobenius facts for the truncated family

`rot A` is a Frobenius isometry (`frobDot_rot`), hence preserves `frobNorm` and the Frobenius balls;
this makes the truncated family `F t ∩ frobBall (Υ t)` invariant under the orthogonal group, which is
what lets the Frobenius distance to it be computed in *any* orthonormal frame. -/

/-- `rot A` preserves the Frobenius norm. -/
theorem frobNorm_rot {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ) (X : Curv4 n) :
    frobNorm (rot A X) = frobNorm X := by
  rw [frobNorm, frobNorm, frobDot_rot n A hA X X]

/-- `rot A` maps the Frobenius ball to itself. -/
theorem mem_frobBall_rot {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ) {ρ : ℝ} {X : Curv4 n} :
    rot A X ∈ frobBall ρ ↔ X ∈ frobBall ρ := by
  rw [frobBall_mem, frobBall_mem, frobNorm_rot A hA X]

/-- `rot A` preserves the Frobenius distance. -/
theorem frobDist_rot_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ) (X Y : Curv4 n) :
    frobDist (rot A X) (rot A Y) = frobDist X Y := by
  have hsub : rot A X - rot A Y = rot A (X - Y) := by
    ext i j k l
    simp only [rot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  rw [frobDist, frobDist, hsub, frobNorm_rot A hA (X - Y)]

section Trunc

variable {n : ℕ}

/-- The truncated family `F t ∩ frobBall (Υ t)` is invariant under `O(n)` when `F` is. -/
theorem truncFam_rot {F : ℝ → Set (Curv4 n)} (hF : IsInvariantFamily F) (Υ : ℝ → ℝ) (t : ℝ)
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ) {R : Curv4 n}
    (hR : R ∈ F t ∩ frobBall (Υ t)) : rot A R ∈ F t ∩ frobBall (Υ t) :=
  ⟨hF.2.2.2.1 t A hA R hR.1, (mem_frobBall_rot A hA).mpr hR.2⟩

/-- The Frobenius distance from the curvature at `(g, x)` to an `O(n)`-invariant set is the distance
computed in any orthonormal frame. -/
theorem frobInfDist_truncFam_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    (hLC : LCSmooth I M) {F : ℝ → Set (Curv4 (Module.finrank ℝ E))} (hF : IsInvariantFamily F)
    {Υ : ℝ → ℝ} (t : ℝ) (g : SMet I M) (x : M)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x) (he : IsONFrame g x e) :
    frobInfDist (rmFrame g x e) (F t ∩ frobBall (Υ t))
      = frobInfDist (rmC g x) (F t ∩ frobBall (Υ t)) :=
  frobInfDist_rmFrame_eq (I := I) (M := M) hLC g x (F t ∩ frobBall (Υ t))
    (fun A hA R hR => truncFam_rot hF Υ t hA hR) e he

/-- The Frobenius distance to a set is 1-Lipschitz in the point, for a nonempty set. -/
theorem abs_frobInfDist_sub_le {n : ℕ} {K : Set (Curv4 n)} (hKne : K.Nonempty) (P Q : Curv4 n) :
    |frobInfDist P K - frobInfDist Q K| ≤ frobDist P Q := by
  rw [abs_sub_le_iff]
  constructor
  · have h : frobInfDist P K - frobDist P Q ≤ frobInfDist Q K := by
      refine le_frobInfDist (P := Q) hKne (fun S hS => ?_)
      have h1 : frobInfDist P K ≤ frobDist P S := frobInfDist_le hS
      have h2 : frobDist P S ≤ frobDist P Q + frobDist Q S := frobDist_triangle P Q S
      linarith
    linarith
  · have h : frobInfDist Q K - frobDist P Q ≤ frobInfDist P K := by
      refine le_frobInfDist (P := P) hKne (fun S hS => ?_)
      have h1 : frobInfDist Q K ≤ frobDist Q S := frobInfDist_le hS
      have h2 : frobDist Q S ≤ frobDist P Q + frobDist P S := by
        rw [frobDist_comm P Q]; exact frobDist_triangle Q P S
      linarith
    linarith

end Trunc


/-! ## Spatial continuity of the Frobenius distance

For a fixed metric `g` and an `O(n)`-invariant set `K`, the map `x ↦ frobInfDist (rmC g x) K` is
continuous: near each point the curvature components may be computed in the smooth orthonormal frame
field supplied by `LapRmFrameParallel` (`hLP`), and those components are continuous
(`contMDiff_rmP_fields`), while the distance to a fixed set is 1-Lipschitz. -/

/-- The Frobenius distance to a fixed set is continuous in the point (the distance function of a set
is 1-Lipschitz on a nonempty set and constantly `0` for the empty set). -/
theorem continuous_frobInfDist {n : ℕ} (K : Set (Curv4 n)) :
    Continuous fun P : Curv4 n => frobInfDist P K := by
  rcases Set.eq_empty_or_nonempty K with hK | hKne
  · have h0 : (fun P : Curv4 n => frobInfDist P K) = fun _ => (0 : ℝ) := by
      funext P
      simp only [frobInfDist, hK, Set.image_empty, Real.sInf_empty]
    rw [h0]
    exact continuous_const
  · rw [continuous_iff_continuousAt]
    intro P
    rw [Metric.continuousAt_iff]
    intro ε hε
    have hden : (0 : ℝ) < (n : ℝ) ^ 2 + 1 := by positivity
    refine ⟨ε / ((n : ℝ) ^ 2 + 1), by positivity, fun Q hQ => ?_⟩
    have h1 : |frobInfDist Q K - frobInfDist P K| ≤ frobDist Q P := abs_frobInfDist_sub_le hKne Q P
    have h2 : frobDist Q P ≤ ((n : ℝ) ^ 2 + 1) * ‖Q - P‖ := by
      refine le_trans (frobNorm_le_mul_norm (Q - P)) ?_
      nlinarith [sq_nonneg (n : ℝ), norm_nonneg (Q - P)]
    have h3 : ‖Q - P‖ < ε / ((n : ℝ) ^ 2 + 1) := by simpa [dist_eq_norm] using hQ
    have h5 : ((n : ℝ) ^ 2 + 1) * (ε / ((n : ℝ) ^ 2 + 1)) = ε := by
      field_simp
    rw [Real.dist_eq]
    calc |frobInfDist Q K - frobInfDist P K| ≤ frobDist Q P := h1
      _ ≤ ((n : ℝ) ^ 2 + 1) * ‖Q - P‖ := h2
      _ < ((n : ℝ) ^ 2 + 1) * (ε / ((n : ℝ) ^ 2 + 1)) := mul_lt_mul_of_pos_left h3 hden
      _ = ε := h5

section SpatialCont

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [I.Boundaryless] [T2Space M]

/-- The curvature form in smooth fields is continuous (entrywise input for the frame version). -/
theorem continuous_rmP_field (hLC : LCSmooth I M) (g : SMet I M)
    (A B C D : Π y : M, TangentSpace I y) (hA : CMDiff ∞ (T% A)) (hB : CMDiff ∞ (T% B))
    (hC : CMDiff ∞ (T% C)) (hD : CMDiff ∞ (T% D)) :
    Continuous fun y : M => rmP g y (A y) (B y) (C y) (D y) :=
  (Work.Diff.GE.contMDiff_rmP_fields (I := I) (M := M) hLC g hA hB hC hD).continuous

/-- The curvature components of a smooth metric in a smooth frame field are continuous. -/
theorem continuous_rmFrame_field (hLC : LCSmooth I M) (g : SMet I M)
    (Ef : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y)
    (hEf : ∀ i, CMDiff ∞ (T% (Ef i))) :
    Continuous fun y : M => rmFrame g y (fun i => Ef i y) := by
  have hfun : (fun y : M => rmFrame g y (fun i => Ef i y))
      = fun y : M => (fun i j k l => rmP g y (Ef i y) (Ef j y) (Ef k y) (Ef l y)) := rfl
  rw [hfun]
  exact continuous_pi (fun i => continuous_pi (fun j => continuous_pi (fun k =>
    continuous_pi (fun l => continuous_rmP_field hLC g (Ef i) (Ef j) (Ef k) (Ef l)
      (hEf i) (hEf j) (hEf k) (hEf l)))))

/-- **Spatial continuity of the distance to the truncated family.**  For a fixed metric `g`, the
map `x ↦ frobInfDist (rmC g x) (F t ∩ frobBall (Υ t))` is continuous: near each point the curvature
components may be computed in the smooth orthonormal frame field supplied by `LapRmFrameParallel`. -/
theorem continuous_frobInfDist_truncFam (hLC : LCSmooth I M) (hLP : LapRmFrameParallel I M)
    (g : SMet I M) {F : ℝ → Set (Curv4 (Module.finrank ℝ E))} (hF : IsInvariantFamily F)
    (Υ : ℝ → ℝ) (t : ℝ) :
    Continuous fun x : M => frobInfDist (rmC g x) (F t ∩ frobBall (Υ t)) := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨Ef, -, hEfsm, hEfON, -⟩ := hLP g x (onFrame g x) (Work.Diff.GE.isONFrame_onFrame g x)
  have h2 : ContinuousAt
      (fun y : M => frobInfDist (rmFrame g y (fun i => Ef i y)) (F t ∩ frobBall (Υ t))) x :=
    (continuous_frobInfDist (F t ∩ frobBall (Υ t))).continuousAt.comp
      (continuous_rmFrame_field hLC g Ef hEfsm).continuousAt
  refine h2.congr ?_
  filter_upwards [hEfON] with y hy
  exact frobInfDist_truncFam_eq (I := I) (M := M) hLC hF t g y (fun i => Ef i y) hy

end SpatialCont

end Work.Diff.MP
