import Mathlib
import Submission.Work.Diff.L.Deps

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Cauchy–Schwarz for the gradient: `(du v)² ≤ |∇u|²_g · g.inner x v v`

`gradSq g u x = ∑ i, (du (onFrame g x i))²` is the squared norm `|∇u|²_g` of the gradient of `u`:
`onFrame g x` is a `g`-orthonormal family of `finrank ℝ E` vectors in the `finrank ℝ E`-dimensional
tangent space `TₓM`, hence a `g`-orthonormal basis.  Writing the Riesz representative of the linear
functional `du = mvfderiv I u x` in that basis and applying Cauchy–Schwarz yields

`(du v)² ≤ |∇u|²_g (x) · g.inner x v v`.

The finite-dimensional Parseval/Cauchy–Schwarz input (`∑ i, (φ (e i))² = ⟪w, w⟫` for the Riesz
representative `w` of `φ`) is proved here for an arbitrary finite-dimensional real inner product
space, so this file is self-contained; the same result is available in the shared library as
`Work.Diff.GE.orthonormal_cauchy`.
-/

namespace Work.Diff.L

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

set_option linter.style.haveILetI false

/-- **Cauchy–Schwarz in an orthonormal frame.**  For a continuous linear functional `φ` on a
finite-dimensional real inner product space `T`, a family `e : ι → T` that is orthonormal with
`Fintype.card ι = finrank ℝ T` (hence an orthonormal basis) and every `v : T`,
`(φ v)² ≤ (∑ i, (φ (e i))²) · ⟪v, v⟫`.

Proof: let `w` be the Riesz representative of `φ` (`InnerProductSpace.toDual`), so `φ y = ⟪w, y⟫`.
Parseval in the orthonormal basis `e` gives `∑ i, (φ (e i))² = ∑ i, ⟪e i, w⟫² = ‖w‖² = ⟪w, w⟫`,
and Cauchy–Schwarz (`real_inner_mul_inner_self_le`) turns `(φ v)² = ⟪w, v⟫²` into
`⟪w, w⟫ ⟪v, v⟫`.  If `ι` is empty then `T` is trivial and both sides vanish. -/
private theorem orthonormal_cauchy_aux
    {T : Type*} [NormedAddCommGroup T] [InnerProductSpace ℝ T] [FiniteDimensional ℝ T]
    {ι : Type*} [Fintype ι] {e : ι → T} (he : Orthonormal ℝ e)
    (hcard : Fintype.card ι = Module.finrank ℝ T) (φ : T →L[ℝ] ℝ) (v : T) :
    (φ v) ^ 2 ≤ (∑ i, φ (e i) ^ 2) * inner ℝ v v := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · -- `ι` empty: `finrank ℝ T = 0`, hence `T` is trivial and both sides vanish.
    haveI := hι
    have hcard0 : Fintype.card ι = 0 := Fintype.card_eq_zero_iff.mpr hι
    have hzero : Module.finrank ℝ T = 0 := by rw [← hcard]; exact hcard0
    have hv : v = 0 := by
      have hall : ∀ x : T, x = 0 := by
        intro x
        obtain ⟨a, ha, hax⟩ := (Module.finrank_eq_zero_iff (R := ℝ) (M := T)).mp hzero x
        rcases smul_eq_zero.mp hax with h | h
        · exact absurd h ha
        · exact h
      exact hall v
    rw [hv]
    simp
  · haveI := hι
    -- `e` is an orthonormal basis
    let b : OrthonormalBasis ι ℝ T :=
      (basisOfOrthonormalOfCardEqFinrank he hcard).toOrthonormalBasis (by
        rw [coe_basisOfOrthonormalOfCardEqFinrank]; exact he)
    have hb : (b : ι → T) = e := by
      rw [Module.Basis.coe_toOrthonormalBasis]
      exact coe_basisOfOrthonormalOfCardEqFinrank he hcard
    -- the Riesz representative `w` of `φ`
    let w : T := (InnerProductSpace.toDual ℝ T).symm φ
    have hw1 : (InnerProductSpace.toDual ℝ T) w = φ :=
      (InnerProductSpace.toDual ℝ T).apply_symm_apply φ
    have hw : ∀ y : T, φ y = inner ℝ w y := by
      intro y
      have h1 : ((InnerProductSpace.toDual ℝ T) w) y = inner ℝ w y := rfl
      rw [hw1] at h1
      exact h1
    -- Parseval: `∑ i, (φ (e i))² = ‖w‖² = ⟪w, w⟫`
    have hsum : (∑ i, φ (e i) ^ 2) = inner ℝ w w := by
      rw [real_inner_self_eq_norm_sq, ← OrthonormalBasis.sum_sq_inner_right b w]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hw, real_inner_comm, ← hb]
    calc (φ v) ^ 2 = inner ℝ w v * inner ℝ w v := by rw [hw v]; ring
      _ ≤ inner ℝ w w * inner ℝ v v := real_inner_mul_inner_self_le w v
      _ = (∑ i, φ (e i) ^ 2) * inner ℝ v v := by rw [hsum]

/-- Cauchy-Schwarz for the gradient: `gradSq g u x = ∑ i, (mvfderiv I u x (onFrame g x i)) ^ 2` is
`|∇u|²_g` (Parseval for the `g`-orthonormal frame `onFrame g x`, which has `finrank ℝ E` vectors in
the `finrank ℝ E`-dimensional tangent space, hence spans — see
`Work.Diff.GE.sum_inner_smul_eq_self` for the expansion, and `Work.Diff.L.onFrame_isONFrame` for
orthonormality), so `(du v) ^ 2 ≤ gradSq g u x * g.inner x v v` for every `v`. -/
theorem gradSq_cauchy
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
    (g : SMet I M) {u : M → ℝ} (hu : CMDiff ∞ u) (x : M) (v : TangentSpace I x) :
    (mvfderiv I u x v) ^ 2 ≤ gradSq g u x * g.inner x v v := by
  -- work in the metric `g`: `g.inner = inner ℝ` for the instance below
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x) := inferInstance
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  -- the frame is orthonormal, of the right cardinality
  have hon : Orthonormal ℝ (onFrame g x) := by
    rw [orthonormal_iff_ite]
    intro i j
    exact onFrame_isONFrame g x i j
  have hcard : Fintype.card (Fin (Module.finrank ℝ E)) = Module.finrank ℝ (TangentSpace I x) := by
    rw [Fintype.card_fin]; rfl
  -- Parseval + Cauchy–Schwarz for `du = mvfderiv I u x`
  exact orthonormal_cauchy_aux hon hcard (mvfderiv I u x) v

end Work.Diff.L
