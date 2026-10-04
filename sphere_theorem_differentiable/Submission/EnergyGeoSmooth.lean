import Submission.EnergyRaySmooth

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory
open Submission.Geodesic
open Submission.Jacobi
open Submission.ChartCurv
open Submission.Rauch
open Submission.RauchGlobal
open Submission.GExpFlow
open Submission.JacobiCoords
open Submission.IntrinsicVariation
open Submission.SecondVarGlobal
open Submission.IndexIntrinsic
open Submission.IndexIntrinsic2
open Submission.JacobiGlobal
open Submission.IndexScale
open Submission.BonnetMyers
open Submission.IndexCorner2
open Submission.GlobalExp
open Submission.GeodesicSpeed
open Submission.Length
open Submission.ChartConnection
open Submission.LensLoop
open Submission.EnergyRay
open Submission.SecondVarGeo
open Submission.EnergyPhase
open Submission.SmoothFieldCover

/-!
# Smoothness in `t` of the intrinsic geodesic variation along an arbitrary geodesic

`Submission.EnergyRaySmooth.contMDiffOn_ray_family` for an arbitrary `C^∞` geodesic with
non-vanishing velocity (the ray-specific inputs are replaced by hypotheses).  The per-piece lemma
`Submission.EnergyRaySmooth.contMDiffAt_piece_curve` is already general and is reused. -/

namespace Submission.EnergyRaySmooth

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

theorem contMDiffOn_geodesic_family (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {γ : ℝ → M} (hγsm : ContMDiffOn 𝓘(ℝ) I ∞ γ univ)
    {V : (t : ℝ) → TangentSpace I (γ t)}
    {a b : ℝ}
    (hVs : ∀ s ∈ Icc (a - 1) (b + 1), SmoothAlongAt (I := I) γ V s)
    (hab : a < b) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ d ∈ Set.Ioc (0 : ℝ) c₀, ∀ᶠ σ in 𝓝 (0 : ℝ),
      ContMDiffOn 𝓘(ℝ) I ∞ (fun t : ℝ => GExp (cov := cov) hmet
        (γ t) (σ • (d • V t))) (Icc a b) ∧
      ContinuousOn (fun t : ℝ => curveSpeed (I := I) (fun t' : ℝ => GExp (cov := cov) hmet
        (γ t') (σ • (d • V t'))) t) (Icc a b) := by
  classical
  have hγsm' : ContMDiffOn 𝓘(ℝ) I ∞ γ (Ioo (a - 1) (b + 1)) := hγsm.mono (Set.subset_univ _)
  obtain ⟨N, c, S, T, z, hc0, hcN, hmono, hSB, hsrc, hcdU, hcdV, hVfr, hroomA⟩ :=
    Submission.SmoothFieldCover.exists_partition_smoothField (I := I) hab.le hγsm'
      (fun s hs => hVs s ⟨by linarith [hs.1], by linarith [hs.2]⟩)
  have hNpos : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · exfalso
      rw [h] at hcN
      exact absurd (hc0 ▸ hcN : a = b) (ne_of_lt hab)
    · exact h
  have hZc : ∀ k < N, IsCompact (γ '' Icc (S k) (T k)) := by
    intro k hk
    have hγc : ContinuousOn γ (Icc (S k) (T k)) := hγsm.continuousOn.mono (Set.subset_univ _)
    exact isCompact_Icc.image_of_continuousOn hγc
  have hZs : ∀ k < N, γ '' Icc (S k) (T k) ⊆ (chartAt H (z k)).source := by
    rintro k hk _ ⟨t, ht, rfl⟩
    exact hsrc k hk t ht
  choose D _ using fun k hk =>
    exists_chartFlowData (cov := cov) (I := I) (z₀ := z k) (hZc k hk) (hZs k hk)
  -- per piece: the phase condition at radius `1`
  have hex : ∀ k (hk : k < N), ∃ e : ℝ, 0 < e ∧ ∀ d ∈ Set.Ioc (0 : ℝ) e,
      (∀ σ ∈ Ioo (-(1 / 2) : ℝ) (1 / 2), ∀ t ∈ Ioo (S k) (T k), ContMDiffAt 𝓘(ℝ) I ∞
        (fun t' : ℝ => GExp (cov := cov) hmet (γ t') (σ • (d • V t'))) t) ∧
      (∀ σ ∈ Ioo (-(1 / 2) : ℝ) (1 / 2), ContinuousOn (fun t' : ℝ =>
        (curveSpeed (I := I) (fun t'' : ℝ => GExp (cov := cov) hmet (γ t'')
          (σ • (d • V t''))) t') ^ 2) (Icc (c k) (c (k + 1)))) := by
    intro k hk
    obtain ⟨e, hepos, he⟩ := Submission.EnergyPhase.exists_pos_phase_condition (cov := cov)
      (D k hk) ((hSB k hk).1.le.trans ((hmono k hk).le.trans (hSB k hk).2.le))
      (hcdV k hk).continuousOn (fun t ht => ⟨t, ⟨ht.1, ht.2⟩, rfl⟩)
    refine ⟨e, hepos, fun d hd => ⟨?_, ?_⟩⟩
    · intro σ hσ t ht
      have hcdVd : ContDiffOn ℝ ∞ (chartCoords (I := I) (z k) γ (fun s => d • V s))
          (Icc (S k) (T k)) := by
        rw [chartCoords_smul]
        exact (hcdV k hk).const_smul d
      have hVfrd : ∀ t' ∈ Icc (S k) (T k), frameVector (I := I) (z k) (γ t')
          (chartCoords (I := I) (z k) γ (fun s => d • V s) t') = (fun s => d • V s) t' := by
        intro t' ht'
        rw [chartCoords_smul]
        show frameVector (I := I) (z k) (γ t') (d • chartCoords (I := I) (z k) γ V t')
          = d • V t'
        rw [Submission.GExpSmooth.frameVector_smul', hVfr k hk t' ht']
      exact contMDiffAt_piece_curve (cov := cov) hmet (D k hk) (S := S k) (T := T k) (δ := 1)
        (by norm_num)
        (fun t' ht' => hsrc k hk t' ht') (hcdU k hk) (hcdVd) (hVfrd)
        (fun t' ht' => ⟨t', ⟨ht'.1, ht'.2⟩, rfl⟩)
        (fun σ' hσ' t' ht' => he d hd σ' ⟨by linarith [hσ'.1], by linarith [hσ'.2]⟩ t' ht')
        σ ⟨by linarith [hσ.1], by linarith [hσ.2]⟩ t ht
    · intro σ hσ
      have hcdVd : ContDiffOn ℝ ∞ (chartCoords (I := I) (z k) γ (fun s => d • V s))
          (Icc (S k) (T k)) := by
        rw [chartCoords_smul]
        exact (hcdV k hk).const_smul d
      have hVfrd : ∀ t' ∈ Icc (S k) (T k), frameVector (I := I) (z k) (γ t')
          (chartCoords (I := I) (z k) γ (fun s => d • V s) t') = (fun s => d • V s) t' := by
        intro t' ht'
        rw [chartCoords_smul]
        show frameVector (I := I) (z k) (γ t') (d • chartCoords (I := I) (z k) γ V t')
          = d • V t'
        rw [Submission.GExpSmooth.frameVector_smul', hVfr k hk t' ht']
      exact (Submission.EnergyRayCover.continuousOn_piece_energy (cov := cov) hmet (D k hk)
        (hSB k hk).1 (hSB k hk).2 (hmono k hk).le (by norm_num)
        (fun t' ht' => hsrc k hk t' ht') (hcdU k hk) (hcdVd) (hVfrd)
        (fun t' ht' => ⟨t', ⟨ht'.1, ht'.2⟩, rfl⟩)
        (he d hd)) σ ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
  let e₀ : ℕ → ℝ := fun k => if hk : k < N then Classical.choose (hex k hk) else 1
  have he₀ : ∀ k (hk : k < N), 0 < e₀ k ∧ ∀ d ∈ Set.Ioc (0 : ℝ) (e₀ k),
      (∀ σ ∈ Ioo (-(1 / 2) : ℝ) (1 / 2), ∀ t ∈ Ioo (S k) (T k), ContMDiffAt 𝓘(ℝ) I ∞
        (fun t' : ℝ => GExp (cov := cov) hmet (γ t') (σ • (d • V t'))) t) ∧
      (∀ σ ∈ Ioo (-(1 / 2) : ℝ) (1 / 2), ContinuousOn (fun t' : ℝ =>
        (curveSpeed (I := I) (fun t'' : ℝ => GExp (cov := cov) hmet (γ t'')
          (σ • (d • V t''))) t') ^ 2) (Icc (c k) (c (k + 1)))) := by
    intro k hk
    have := Classical.choose_spec (hex k hk)
    simpa only [e₀, dif_pos hk] using this
  have hneF : ((Finset.range N).image e₀).Nonempty :=
    ⟨e₀ 0, Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hNpos, rfl⟩⟩
  refine ⟨((Finset.range N).image e₀).min' hneF, ?_, fun d hd => ?_⟩
  · have hmem : ((Finset.range N).image e₀).min' hneF ∈ (Finset.range N).image e₀ :=
      Finset.min'_mem _ hneF
    obtain ⟨k, hk, hk'⟩ := Finset.mem_image.mp hmem
    rw [← hk']
    by_cases h : k < N
    · exact (he₀ k h).1
    · have hval : e₀ k = 1 := by simp only [e₀, dif_neg h]
      rw [hval]; norm_num
  · have hle : ∀ k < N, d ≤ e₀ k := fun k hk => le_trans hd.2 (Finset.min'_le _ _
      (Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩))
    filter_upwards [isOpen_Ioo.mem_nhds (show (0 : ℝ) ∈ Ioo (-(1 / 2)) (1 / 2) from
      ⟨by norm_num, by norm_num⟩)] with σ hσ
    refine ⟨?_, ?_⟩
    · intro t ht
      have hσ' : σ ∈ Ioo (-(1 / 2) : ℝ) (1 / 2) := ⟨hσ.1, hσ.2⟩
      obtain ⟨k, hk, hck, hck1⟩ := exists_le_le_of_partition hc0 hcN
        (fun k hk => (hmono k hk).le) hab ht
      have hSt : S k < t := lt_of_lt_of_le (hSB k hk).1 hck
      have htT : t < T k := lt_of_le_of_lt hck1 (hSB k hk).2
      exact (((he₀ k hk).2 d ⟨hd.1, hle k hk⟩).1 σ hσ' t ⟨hSt, htT⟩).contMDiffWithinAt
    · have hsq : ContinuousOn (fun t : ℝ => (curveSpeed (I := I) (fun t' : ℝ =>
          GExp (cov := cov) hmet (γ t') (σ • (d • V t'))) t) ^ 2) (Icc a b) :=
        Commons.Topology.continuousOn_Icc_of_continuousOn_pieces hc0 hcN
          (fun k hk => (hmono k hk).le)
          (fun k hk => ((he₀ k hk).2 d ⟨hd.1, hle k hk⟩).2 σ ⟨hσ.1, hσ.2⟩)
      refine (hsq.sqrt).congr (fun t _ => ?_)
      exact (Real.sqrt_sq (curveSpeed_nonneg (I := I) _ t)).symm


end

end Submission.EnergyRaySmooth
