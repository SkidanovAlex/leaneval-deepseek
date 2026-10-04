import Mathlib
import Submission.Work.Diff.L.Defs
import Submission.Work.Diff.L.Stmt

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.L

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

/-- **A time slice of the flow whose scalar curvature can be spread with an arbitrarily small `β`.**

Let `G` be a Ricci flow on `[0,T)` whose curvature lies in a pinching set `F`, and suppose that for
every bound `N` there is a time `t` at which `scalAt (G t)` is *nonnegative everywhere* and has a
*maximum* at least `N` (`hbig`; this holds for the flows produced by the flow-end assembly, where the
nonnegativity comes from the invariant family `{0 ≤ scalAlg}` and the largeness from either the
blow-up of `scal` or from unbounded curvature).  Given a *uniform* constant `K` with
`|∇ scal(g)|² ≤ K |∇Rm|²_g` for all metrics `g` (see `Work.Diff.L.gradSq_le_dRmNormSq`), for every
`Θ > 0` and `β > 0` there is a time slice `g = G t` with

* `scalAt (G t) ≥ 0` everywhere,
* a maximum point `x₀` with `S₀ := scalAt (G t) x₀ ≥ Θ` and `scalAt (G t) x ≤ S₀` for all `x`,
* `|∇ scal(G t)|² ≤ β² S³ + Cn` with `Cn ≤ β² S₀²`.

Route.  Fix `η := min 1 (β²/(2K)) > 0` and apply the gradient estimate `hGE` to the fixed flow `G`
(all four of `hT`, `hflow`, `hF`, `hCurv` are exactly its hypotheses): get `C₂` with
`dRmNormSq (G t) x ≤ η |scalAt (G t) x|³ + C₂`.  At the time provided by `hbig` (with `N` chosen
below) the scalar curvature is nonnegative, so `|scalAt| = scalAt`, and the uniform bound `K` gives
`gradSq (G t) (scalAt (G t)) x ≤ (K η) S³ + K C₂ ≤ β² S³ + Cn` with `Cn := K C₂`, using
`K η ≤ β²/2 ≤ β²` and `S ≥ 0`.  Finally `Cn = K C₂ ≤ β² S₀²` follows from `S₀ ≥ √(C₂/(2η))`
(replace a possibly negative `C₂` by `max C₂ 0`), and `S₀ ≥ Θ`, `S₀ ≥ 1` are met by taking
`N := max Θ 1 (√(max C₂ 0 /(2η)))` in `hbig`. -/
theorem exists_spreadable_metric
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I (((⊤ : ℕ∞) : WithTop ℕ∞)) M] [T2Space M]
    (hdim : 2 ≤ Module.finrank ℝ E)
    (hGE : Submission.Diff.GradientEstimate I M)
    (F : Set (Submission.Diff.Alg.Curv4 (Module.finrank ℝ E)))
    (hF : Submission.Diff.Alg.IsPinchingSet F)
    {T : ℝ} (hT : 0 < T) {G : ℝ → Submission.Diff.SMet I M}
    (hflow : Submission.Diff.IsRicciFlow G T)
    (hCurv : ∀ t ∈ Set.Ico 0 T, Submission.Diff.CurvIn (G t) F)
    (hbig : ∀ N : ℝ, ∃ t ∈ Set.Ico 0 T, ∃ x₀ : M,
      (∀ x : M, 0 ≤ Submission.Diff.scalAt (G t) x) ∧
      N ≤ Submission.Diff.scalAt (G t) x₀ ∧
      ∀ x : M, Submission.Diff.scalAt (G t) x ≤ Submission.Diff.scalAt (G t) x₀)
    {K : ℝ} (hK : 0 < K)
    (hKb : ∀ (g : Submission.Diff.SMet I M) (x : M),
      Submission.Diff.gradSq g (Submission.Diff.scalAt g) x
        ≤ K * Submission.Diff.dRmNormSq g x) :
    ∀ Θ β : ℝ, 0 < Θ → 0 < β →
      ∃ (t : ℝ) (_ : t ∈ Set.Ico 0 T) (x₀ : M) (S₀ Cn : ℝ),
        (∀ x : M, 0 ≤ Submission.Diff.scalAt (G t) x) ∧
        Submission.Diff.scalAt (G t) x₀ = S₀ ∧ Θ ≤ S₀ ∧ 0 < S₀ ∧
        (∀ x : M, Submission.Diff.scalAt (G t) x ≤ S₀) ∧
        (∀ x : M, Submission.Diff.gradSq (G t) (Submission.Diff.scalAt (G t)) x
          ≤ β ^ 2 * (Submission.Diff.scalAt (G t) x) ^ 3 + Cn) ∧
        Cn ≤ β ^ 2 * S₀ ^ 2 := by
  intro Θ β hΘ hβ
  have hβ2 : 0 < β ^ 2 := pow_pos hβ 2
  have h2K : 0 < 2 * K := by linarith
  let η : ℝ := min 1 (β ^ 2 / (2 * K))
  have hηpos : 0 < η := lt_min one_pos (div_pos hβ2 h2K)
  have hηle : η ≤ β ^ 2 / (2 * K) := min_le_right _ _
  -- `2 K η ≤ β²` (and hence `K η ≤ β²`)
  have hKη2 : 2 * K * η ≤ β ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hηle h2K.le
    rw [div_mul_cancel₀ _ (ne_of_gt h2K)] at h
    linarith
  have hKη : K * η ≤ β ^ 2 := by linarith [hKη2, hηpos, hK]
  -- Hamilton's gradient estimate for this flow, with parameter `η`
  obtain ⟨C, hC⟩ := hGE G T F hT hflow hF hCurv η hηpos
  let C₂ : ℝ := max C 0
  have hC₂0 : 0 ≤ C₂ := le_max_right _ _
  have hCle : C ≤ C₂ := le_max_left _ _
  have h2η : 0 < 2 * η := by linarith
  -- the bound `N` we demand from `hbig`
  let N : ℝ := max (max Θ 1) (Real.sqrt (C₂ / (2 * η)))
  obtain ⟨t, ht, x₀, hnn, hNle, hmax⟩ := hbig N
  have hΘN : Θ ≤ N := le_trans (le_max_left Θ 1) (le_max_left _ _)
  have hsqrtN : Real.sqrt (C₂ / (2 * η)) ≤ N := le_max_right _ _
  have hS₀ge : Θ ≤ scalAt (G t) x₀ := le_trans hΘN hNle
  have hS₀pos : 0 < scalAt (G t) x₀ := lt_of_lt_of_le hΘ hS₀ge
  refine ⟨t, ht, x₀, scalAt (G t) x₀, K * C₂, hnn, rfl, hS₀ge, hS₀pos, hmax, ?_, ?_⟩
  · -- the pointwise gradient bound
    intro x
    have h1 : dRmNormSq (G t) x ≤ η * |scalAt (G t) x| ^ 3 + C := hC t ht x
    have h2 : dRmNormSq (G t) x ≤ η * |scalAt (G t) x| ^ 3 + C₂ := by linarith
    have h3 : gradSq (G t) (scalAt (G t)) x ≤ K * (η * |scalAt (G t) x| ^ 3 + C₂) :=
      (hKb (G t) x).trans (mul_le_mul_of_nonneg_left h2 hK.le)
    have habs : |scalAt (G t) x| = scalAt (G t) x := abs_of_nonneg (hnn x)
    rw [habs] at h3
    have hsp : 0 ≤ (scalAt (G t) x) ^ 3 := pow_nonneg (hnn x) 3
    have h4 : K * η * (scalAt (G t) x) ^ 3 ≤ β ^ 2 * (scalAt (G t) x) ^ 3 :=
      mul_le_mul_of_nonneg_right hKη hsp
    nlinarith [h3, h4]
  · -- the constant bound `K C₂ ≤ β² S₀²`
    have hsq : C₂ / (2 * η) ≤ (scalAt (G t) x₀) ^ 2 :=
      (Real.sqrt_le_iff.mp (le_trans hsqrtN hNle)).2
    have hC₂le : C₂ ≤ (scalAt (G t) x₀) ^ 2 * (2 * η) := (div_le_iff₀ h2η).mp hsq
    have hS₀sq : 0 ≤ (scalAt (G t) x₀) ^ 2 := sq_nonneg _
    have hm := mul_le_mul_of_nonneg_right hKη2 hS₀sq
    have h1 : K * C₂ ≤ K * ((scalAt (G t) x₀) ^ 2 * (2 * η)) :=
      mul_le_mul_of_nonneg_left hC₂le hK.le
    linarith [h1, hm]

end Work.Diff.L
