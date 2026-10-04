import Submission.LiftUniform
import Submission.Commons.Geometry.Manifold.exists_finite_cover_isCompact_subset_chartAt

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.GlobalExp
open Submission.InjRadius

/-!
# Uniform continuity of the inverse of the exponential map, uniformly over the manifold

`Submission.LiftUniform.exists_pos_forall_edist_lt_imp_norm_sub_lt_of_chart` gives the uniform
continuity of the inverse of `exp` on a *single compact chart piece*, with a modulus `δ` depending on
the piece.

This module assembles the finitely many pieces of a compact manifold
(`Commons.Geometry.Manifold.exists_finite_cover_isCompact_subset_chartAt`) and takes the minimum of
the finitely many radii and moduli, obtaining the global statement

> `InjAllAtLeast hmet ρ` ⟹ `∃ ρ' ∈ (0,ρ], ∃ δ > 0`, for every point `q` and every pair of tangent
> vectors `v, w` at `q` with `‖v‖, ‖w‖ ≤ ρ'`: if `d (GExp q v) (GExp q w) < δ` then `‖v - w‖ < ε`.

This is the "the inverse of the exponential map is uniformly continuous, uniformly over `M`"
statement that the parametric (family) lifting arguments of Klingenberg's estimate consume; it is
step 1 of `Submission.Roadmap.lean` §126.4ter.
-/

namespace Submission.LiftGlobal

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- **Uniform continuity of the inverse of `exp`, uniformly over the manifold.**

If the exponential map is injective on the ball of radius `ρ` at *every* point, then for every
`ε > 0` there are `ρ' ∈ (0, ρ]` and `δ > 0` such that for every point `q`, every pair of tangent
vectors `v, w` at `q` with `‖v‖, ‖w‖ ≤ ρ'` and `d (GExp q v) (GExp q w) < δ` satisfies
`‖v - w‖ < ε`. -/
theorem exists_pos_forall_edist_lt_imp_norm_lt_of_injAllAtLeast
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M]
    {ρ : ℝ} (hρ : 0 < ρ) (hinj : InjAllAtLeast hmet ρ) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ' : ℝ, 0 < ρ' ∧ ρ' ≤ ρ ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ (q : M) (v w : TangentSpace I q), ‖v‖ ≤ ρ' → ‖w‖ ≤ ρ' →
        Manifold.riemannianEDist I (GExp (cov := cov) hmet q v)
          (GExp (cov := cov) hmet q w) < ENNReal.ofReal δ → ‖v - w‖ < ε := by
  classical
  obtain ⟨n, z, Z, hZc, hZsrc, hcov⟩ :=
    Commons.Geometry.Manifold.exists_finite_cover_isCompact_subset_chartAt (I := I) (M := M)
  -- on each piece of the cover there is a pair `(ρf i, δf i)` doing the job
  have hpiece : ∀ i : Fin n, ∃ ρ' δ : ℝ, 0 < ρ' ∧ ρ' ≤ ρ ∧ 0 < δ ∧
      ∀ q ∈ Z i, ∀ v w : TangentSpace I q, ‖v‖ ≤ ρ' → ‖w‖ ≤ ρ' →
        Manifold.riemannianEDist I (GExp (cov := cov) hmet q v)
          (GExp (cov := cov) hmet q w) < ENNReal.ofReal δ → ‖v - w‖ < ε := by
    intro i
    by_cases hne : (Z i).Nonempty
    · obtain ⟨ρ', hρ'0, hρ'ρ, δ, hδ0, hspec⟩ :=
        Submission.LiftUniform.exists_pos_forall_edist_lt_imp_norm_sub_lt_of_chart
          (cov := cov) hmet htor (hZsrc i) (hZc i) hne hρ (fun q _ => hinj q) hε
      exact ⟨ρ', δ, hρ'0, hρ'ρ, hδ0, fun q hq => hspec q hq⟩
    · exact ⟨ρ, 1, hρ, le_rfl, one_pos, fun q hq => absurd ⟨q, hq⟩ hne⟩
  choose ρf δf hρf0 hρfρ hδf0 hspec using hpiece
  rcases Nat.eq_zero_or_pos n with hn | hn
  · -- the cover is empty, so `M` is empty: the statement is vacuous
    subst hn
    refine ⟨ρ, hρ, le_rfl, 1, one_pos, ?_⟩
    intro q v w _ _ _
    obtain ⟨i, _⟩ := Set.mem_iUnion.mp (hcov (Set.mem_univ q))
    exact Fin.elim0 i
  · haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    let sfρ : Finset ℝ := (Finset.univ : Finset (Fin n)).image ρf
    let sfδ : Finset ℝ := (Finset.univ : Finset (Fin n)).image δf
    have hneρ : sfρ.Nonempty := Finset.image_nonempty.mpr Finset.univ_nonempty
    have hneδ : sfδ.Nonempty := Finset.image_nonempty.mpr Finset.univ_nonempty
    have hleastρ : ∀ y ∈ sfρ, sfρ.min' hneρ ≤ y := fun y hy =>
      (Finset.isLeast_min' sfρ hneρ).2 hy
    have hleastδ : ∀ y ∈ sfδ, sfδ.min' hneδ ≤ y := fun y hy =>
      (Finset.isLeast_min' sfδ hneδ).2 hy
    refine ⟨sfρ.min' hneρ, ?_, ?_, sfδ.min' hneδ, ?_, ?_⟩
    · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (Finset.min'_mem sfρ hneρ)
      rw [← hi]; exact hρf0 i
    · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (Finset.min'_mem sfρ hneρ)
      rw [← hi]; exact hρfρ i
    · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (Finset.min'_mem sfδ hneδ)
      rw [← hi]; exact hδf0 i
    · intro q v w hv hw himg
      obtain ⟨i, hqi⟩ := Set.mem_iUnion.mp (hcov (Set.mem_univ q))
      have h1 : ‖v‖ ≤ ρf i := le_trans hv (hleastρ (ρf i) (Finset.mem_image_of_mem ρf (Finset.mem_univ i)))
      have h2 : ‖w‖ ≤ ρf i := le_trans hw (hleastρ (ρf i) (Finset.mem_image_of_mem ρf (Finset.mem_univ i)))
      have h3 : Manifold.riemannianEDist I (GExp (cov := cov) hmet q v)
          (GExp (cov := cov) hmet q w) < ENNReal.ofReal (δf i) :=
        lt_of_lt_of_le himg (ENNReal.ofReal_le_ofReal
          (hleastδ (δf i) (Finset.mem_image_of_mem δf (Finset.mem_univ i))))
      exact hspec i q hqi v w h1 h2 h3

end

end Submission.LiftGlobal
