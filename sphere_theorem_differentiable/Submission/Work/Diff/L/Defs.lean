import Mathlib
import Submission.Diff.Grad

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Shared definitions and elementary lemmas for the `flow_end_ge` area

This module holds the (sorry-free) foundation that the assembly of `Work.Diff.L.flow_end_ge`
and the delegated sub-lemmas share:

* `initSMet`: the ambient (instance) Riemannian metric, as an `SMet`;
* `exists_isONFrame` / `onFrame_isONFrame`: `g`-orthonormal frames exist, so the `Classical.epsilon`
  choice `Submission.Diff.onFrame` really is an orthonormal frame;
* elementary `Curv4` algebra: a component is bounded by the norm, and the scalar curvature by
  `n^2 * ‖R‖`;
* the quantitative consequence of a pinching set that the argument needs:
  a curvature tensor in `F` with large scalar curvature is `δ`-pinched.
-/

namespace Work.Diff.L

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M]

/-! ## The ambient metric as an `SMet` -/

section InitMetric

variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

/-- The Riemannian metric given by the ambient `RiemannianBundle` instance, as an `SMet`. -/
noncomputable def initSMet : SMet I M where
  inner := (RiemannianBundle.g (E := fun x : M ↦ TangentSpace I x)).inner
  symm := (RiemannianBundle.g (E := fun x : M ↦ TangentSpace I x)).symm
  pos := (RiemannianBundle.g (E := fun x : M ↦ TangentSpace I x)).pos
  isVonNBounded := (RiemannianBundle.g (E := fun x : M ↦ TangentSpace I x)).isVonNBounded
  contMDiff := by
    obtain ⟨g₀, hg₀, hspec⟩ :=
      (inferInstance : IsContMDiffRiemannianBundle I ∞ E
        (fun x : M ↦ TangentSpace I x)).exists_contMDiff
    refine hg₀.congr (fun x => ?_)
    have heq : (RiemannianBundle.g (E := fun x : M ↦ TangentSpace I x)).inner x = g₀ x := by
      ext v w
      exact (show ((RiemannianBundle.g (E := fun x : M ↦ TangentSpace I x)).inner x) v w
        = inner ℝ v w from rfl).trans (hspec x v w)
    rw [heq]

@[simp] lemma initSMet_inner (x : M) (v w : TangentSpace I x) :
    initSMet.inner x v w = inner ℝ v w := rfl

/-- The instance metric of the `SMet` and of the ambient bundle agree, definitionally. -/
lemma initSMet_toRiemannianMetric_inner (x : M) (v w : TangentSpace I x) :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨initSMet.toRiemannianMetric⟩
    inner ℝ v w = initSMet.inner x v w := rfl

end InitMetric

/-! ## Existence of `g`-orthonormal frames -/

/-- Every point admits a `g`-orthonormal frame. -/
theorem exists_isONFrame (g : SMet I M) (x : M) :
    ∃ e : Fin (Module.finrank ℝ E) → TangentSpace I x, IsONFrame g x e := by
  letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  have key : ∀ v w : TangentSpace I x, inner ℝ v w = g.inner x v w := fun v w => rfl
  refine ⟨fun i => stdOrthonormalBasis ℝ (TangentSpace I x) i, fun i j => ?_⟩
  have h := orthonormal_iff_ite.mp (stdOrthonormalBasis ℝ (TangentSpace I x)).orthonormal i j
  exact (key _ _).symm.trans h

/-- The `Classical.epsilon` choice `onFrame` really is a `g`-orthonormal frame. -/
theorem onFrame_isONFrame (g : SMet I M) (x : M) : IsONFrame g x (onFrame g x) :=
  Classical.epsilon_spec (exists_isONFrame g x)

/-- An `IsONFrame` is pointwise nonzero. -/
lemma IsONFrame.ne_zero {g : SMet I M} {x : M} {e : Fin (Module.finrank ℝ E) → TangentSpace I x}
    (he : IsONFrame g x e) (i : Fin (Module.finrank ℝ E)) : e i ≠ 0 := by
  intro h
  have h1 : g.inner x (e i) (e i) = 1 := by simpa using he i i
  rw [h] at h1
  have h2 : g.inner x (0 : TangentSpace I x) (0 : TangentSpace I x) = 0 := by simp
  rw [h2] at h1
  exact one_ne_zero h1.symm

/-! ## Elementary `Curv4` algebra -/

section Alg

variable {n : ℕ}

/-- Every component of `R : Curv4 n` is bounded by its norm. -/
lemma Curv4.abs_apply_le_norm (R : Curv4 n) (i j k l : Fin n) : |R i j k l| ≤ ‖R‖ := by
  have h0 : ‖R i j k l‖ = |R i j k l| := Real.norm_eq_abs _
  rw [← h0]
  exact (norm_le_pi_norm (R i j k) l).trans
    ((norm_le_pi_norm (R i j) k).trans ((norm_le_pi_norm (R i) j).trans (norm_le_pi_norm R i)))

/-- The scalar curvature of `R : Curv4 n` is bounded by `n^2` times its norm. -/
lemma abs_scalAlg_le (R : Curv4 n) : |scalAlg R| ≤ (n : ℝ) ^ 2 * ‖R‖ := by
  rw [scalAlg]
  calc |∑ i, ∑ j, R i j i j| ≤ ∑ i, |∑ j, R i j i j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |R i j i j| :=
        Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, ‖R‖ :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => Curv4.abs_apply_le_norm R i j i j
    _ = (n : ℝ) ^ 2 * ‖R‖ := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        ring

/-- **Consequence of a pinching set.**  For every `δ < 1` there is a threshold `ρ` such that every
curvature tensor of `F` whose scalar curvature exceeds `ρ` is `δ`-pinched.  (`scalAlg R ≤ n^2 ‖R‖`
converts the boundedness of the non-`δ`-pinched part of `F` into a lower bound on the scalar
curvature.) -/
theorem isPinchedAlg_of_scalAlg_le {F : Set (Curv4 n)} (hF : IsPinchingSet F) {δ : ℝ}
    (hδ : δ < 1) : ∃ ρ : ℝ, ∀ R ∈ F, ρ ≤ scalAlg R → IsPinchedAlg δ R := by
  obtain ⟨r, hr⟩ := (isBounded_iff_subset_ball (0 : Curv4 n)).mp (hF.2 δ hδ)
  refine ⟨(n : ℝ) ^ 2 * r + 1, fun R hR hρ => ?_⟩
  by_contra hnot
  have hb : R ∈ {R | R ∈ F ∧ ¬ IsPinchedAlg δ R} := ⟨hR, hnot⟩
  have h1 : ‖R‖ < r := by have := hr hb; simpa [dist_eq_norm] using this
  have h2 : scalAlg R ≤ (n : ℝ) ^ 2 * ‖R‖ := le_trans (le_abs_self _) (abs_scalAlg_le R)
  have h3 : (0 : ℝ) ≤ (n : ℝ) ^ 2 := sq_nonneg _
  nlinarith

end Alg

/-! ## The pointwise sectional curvature of a metric -/

/-- The sectional curvature of the plane spanned by `u, v` at `x`, computed with `rmVec`. -/
noncomputable def secCurvAt (g : SMet I M) (x : M) (u v : TangentSpace I x) : ℝ :=
  g.inner x (rmVec (lcOf g) x u v v) u

end Work.Diff.L
