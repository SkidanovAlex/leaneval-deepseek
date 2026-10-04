import Mathlib
import Submission.Work.Final.DimOne.Defs
import Submission.ConjEnergy

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Final.DimOne

open scoped Manifold ContDiff Bundle Topology ENNReal
open LeanEval.Geometry.SphereTheorem
open CovariantDerivative
open Submission.GlobalExp

/-- **A periodic `GExp`-ray has a minimal positive period.**

Let `A` be the set of all (real) periods of the ray `s ↦ GExp p (s • u)`:

`A = {Q | ∀ s, GExp p ((s + Q) • u) = GExp p (s • u)}`.

Each of the sets `{Q | GExp p ((s + Q) • u) = GExp p (s • u)}` is the equaliser of the two
continuous maps `Q ↦ GExp p ((s + Q) • u)` (the ray, shifted) and `Q ↦ GExp p (s • u)`
(constant) into the Hausdorff space `M`, hence is closed; so `A = ⋂ s, …` is closed.  If `Q₀ > 0`
is a period and every positive period is `≥ ρ > 0`, then the compact window `A ∩ [ρ, Q₀]` is
nonempty, so it attains a minimum `P`.  Every positive period `Q` either lies in the window
(`P ≤ Q` by minimality) or exceeds `Q₀ ≥ P`; hence `P` is the smallest positive period. -/
theorem exists_minimal_period
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (p : M) (u : TangentSpace I p) (hu : u ≠ 0)
    (hex : ∃ Q : ℝ, 0 < Q ∧ ∀ s : ℝ,
      GExp (cov := cov) hmet p ((s + Q) • u) = GExp (cov := cov) hmet p (s • u))
    (hbd : ∃ ρ : ℝ, 0 < ρ ∧ ∀ Q : ℝ, 0 < Q →
      (∀ s : ℝ, GExp (cov := cov) hmet p ((s + Q) • u) = GExp (cov := cov) hmet p (s • u)) →
      ρ ≤ Q) :
    ∃ P : ℝ, 0 < P ∧
      (∀ s : ℝ, GExp (cov := cov) hmet p ((s + P) • u) = GExp (cov := cov) hmet p (s • u)) ∧
      ∀ Q : ℝ, 0 < Q →
        (∀ s : ℝ, GExp (cov := cov) hmet p ((s + Q) • u) = GExp (cov := cov) hmet p (s • u)) →
        P ≤ Q := by
  obtain ⟨Q₀, hQ₀pos, hQ₀per⟩ := hex
  obtain ⟨ρ, hρpos, hρ⟩ := hbd
  -- `ρ` is a lower bound for the periods, in particular `ρ ≤ Q₀`.
  have hρQ₀ : ρ ≤ Q₀ := hρ Q₀ hQ₀pos hQ₀per
  -- The ray `s ↦ GExp p (s • u)` is continuous (it is `C^∞`).
  have hcont : Continuous (fun t : ℝ => GExp (cov := cov) hmet p (t • u)) :=
    (Submission.ConjEnergy.contMDiff_GExp_smul (cov := cov) hmet p hu).continuous
  -- The set of periods is closed: it is an intersection of equalisers of continuous maps.
  have hAclosed : IsClosed
      {Q : ℝ | ∀ s : ℝ, GExp (cov := cov) hmet p ((s + Q) • u) =
        GExp (cov := cov) hmet p (s • u)} := by
    have hset : ({Q : ℝ | ∀ s : ℝ, GExp (cov := cov) hmet p ((s + Q) • u) =
          GExp (cov := cov) hmet p (s • u)} : Set ℝ)
        = ⋂ s : ℝ, {Q : ℝ | GExp (cov := cov) hmet p ((s + Q) • u) =
            GExp (cov := cov) hmet p (s • u)} := by
      ext Q
      simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    rw [hset]
    exact isClosed_iInter fun s =>
      isClosed_eq (hcont.comp (continuous_const.add continuous_id)) continuous_const
  -- The compact window of periods `A ∩ [ρ, Q₀]` is nonempty and compact.
  have hcp : IsCompact
      ({Q : ℝ | ∀ s : ℝ, GExp (cov := cov) hmet p ((s + Q) • u) =
          GExp (cov := cov) hmet p (s • u)} ∩ Set.Icc ρ Q₀) :=
    isCompact_Icc.of_isClosed_subset (hAclosed.inter isClosed_Icc) Set.inter_subset_right
  have hne : ({Q : ℝ | ∀ s : ℝ, GExp (cov := cov) hmet p ((s + Q) • u) =
          GExp (cov := cov) hmet p (s • u)} ∩ Set.Icc ρ Q₀).Nonempty :=
    ⟨Q₀, hQ₀per, hρQ₀, le_rfl⟩
  -- Hence the window attains a minimum `P`.
  obtain ⟨P, hPmem, hPmin⟩ := hcp.exists_isLeast hne
  refine ⟨P, lt_of_lt_of_le hρpos hPmem.2.1, hPmem.1, ?_⟩
  intro Q hQpos hQper
  by_cases hQle : Q ≤ Q₀
  · exact hPmin ⟨hQper, hρ Q hQpos hQper, hQle⟩
  · exact le_trans hPmem.2.2 (le_of_lt (not_le.mp hQle))

end Work.Final.DimOne
