import Mathlib
import Submission.Work.EXT.sum_inner_smul_eq_self_of_isONFrame

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Bundle

namespace Work.Diff.Evol

set_option linter.style.haveILetI false in
/-- Expansion of the inner product in an orthonormal frame: if `B` is a `g`-orthonormal frame at
`y` (so that `IsONFrame g y B` holds and `B` is an orthonormal base of `T_yM`), then for all
tangent vectors `e i`, `e k` the components of `e k` in the frame `B` reproduce the inner product,
`∑ j, g.inner y (e i) (B j) * g.inner y (e k) (B j) = g.inner y (e i) (e k)`. -/
theorem sum_inner_mul_inner_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (g : Submission.Diff.SMet I M) (y : M)
    (B : Fin (Module.finrank ℝ E) → TangentSpace I y)
    (hB : Submission.Diff.IsONFrame g y B)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I y) :
    ∀ i k, (∑ j, (g.inner y (e i) (B j)) * (g.inner y (e k) (B j))) =
      g.inner y (e i) (e k) := by
  classical
  -- Work with the inner product space structure on the tangent space induced by `g`.
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I (⊤ : ℕ∞) E (fun x : M ↦ TangentSpace I x) := inferInstance
  haveI : FiniteDimensional ℝ (TangentSpace I y) := inferInstanceAs (FiniteDimensional ℝ E)
  -- `B` is orthonormal for that inner product (`Inner.inner ℝ` is `g.inner y` by definition).
  have hon : Orthonormal ℝ B := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [show Inner.inner ℝ (B i) (B j) = g.inner y (B i) (B j) from rfl]
    exact hB i j
  have hli : LinearIndependent ℝ B := hon.linearIndependent
  have hcard : Fintype.card (Fin (Module.finrank ℝ E)) = Module.finrank ℝ (TangentSpace I y) := by
    rw [Fintype.card_fin]; rfl
  -- A linearly independent family of `finrank` vectors is a basis (primed constructor: no
  -- `Nonempty ι` needed, so `finrank ℝ E = 0` is fine as well).
  let bb : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I y) :=
    basisOfLinearIndependentOfCardEqFinrank' B hli hcard
  have hb : (bb : Fin (Module.finrank ℝ E) → TangentSpace I y) = B :=
    coe_basisOfLinearIndependentOfCardEqFinrank' B hli hcard
  have honb : Orthonormal ℝ (bb : Fin (Module.finrank ℝ E) → TangentSpace I y) := by
    rw [hb]; exact hon
  let B' : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I y) :=
    bb.toOrthonormalBasis honb
  have hB' : (B' : Fin (Module.finrank ℝ E) → TangentSpace I y) = B := by
    rw [Module.Basis.coe_toOrthonormalBasis]; exact hb
  -- `OrthonormalBasis.sum_inner_mul_inner` is the corresponding expansion in `B'`, which is `B`.
  intro i k
  have h := OrthonormalBasis.sum_inner_mul_inner B' (e i) (e k)
  rw [hB'] at h
  rw [show Inner.inner ℝ (e i) (e k) = g.inner y (e i) (e k) from rfl] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro j _
  rw [show Inner.inner ℝ (e i) (B j) = g.inner y (e i) (B j) from rfl,
      show Inner.inner ℝ (B j) (e k) = g.inner y (B j) (e k) from rfl,
      g.symm y (B j) (e k)]

end Work.Diff.Evol
