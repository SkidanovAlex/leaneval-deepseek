import Submission.EnergyGeo
import Submission.EnergyRayCover

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

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
open Submission.Length
open Submission.GlobalExp
open Submission.GeodesicSpeed
open Submission.IndexCorner2
open Submission.ChartConnection
open Submission.LensLoop
open Submission.EnergyRay
open Submission.SecondVarGeo
open Submission.SmoothFieldCover

/-!
# The per-piece second variation of the energy along an arbitrary geodesic

`Submission.EnergyRayCover.exists_pos_piece_second_deriv` runs the per-piece second-variation
machinery along a `GExp`-ray; this module proves the same statement for an arbitrary `C^∞` geodesic
with non-vanishing velocity.  The only change is that the two ray-specific inputs

* the smoothness of the curve (`LensLoop.contMDiffOn_GExp_smul_Ioo_symm`), and
* the chart geodesic equation (`GExpPieceData.hasDerivAt_psiW_GExp`)

are replaced by hypotheses and by `Submission.EnergyGeo.hasDerivAt_psiW_geodesic`.  The six auxiliary
lemmas and `Submission.EnergyRay.energy_second_deriv_piece_scaled` are *already* general and are
reused from `Submission.EnergyRayCover`. -/

namespace Submission.EnergyRayCover

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

theorem exists_pos_piece_second_deriv_geodesic (hmet : IsMetricCompatible cov)
    (htor : cov.torsion = 0)
    {γ : ℝ → M} (hγsm : ContMDiffOn 𝓘(ℝ) I ∞ γ univ)
    (hgeo : ∀ t : ℝ, IsGeodesicAt (I := I) cov γ t)
    (hne : ∀ t : ℝ, curveVelocity (I := I) γ t ≠ 0)
    {V : (t : ℝ) → TangentSpace I (γ t)}
    {a b : ℝ}
    (hVs : ∀ s ∈ Icc (a - 1) (b + 1), SmoothAlongAt (I := I) γ V s)
    (hab : a < b) :
    ∃ (N : ℕ) (c : ℕ → ℝ) (c₀ : ℝ), 0 < c₀ ∧ c 0 = a ∧ c N = b ∧
      (∀ k < N, c k < c (k + 1)) ∧
      ∀ d ∈ Set.Ioc (0 : ℝ) c₀,
        (∀ᶠ σ in 𝓝 (0 : ℝ), ∀ k < N, IntervalIntegrable (fun t : ℝ => (curveSpeed (I := I)
            (fun s : ℝ => GExp (cov := cov) hmet (γ s) (σ • (d • V s))) t) ^ 2) volume (c k) (c (k + 1))) ∧
        (∀ k < N, IntervalIntegrable (fun t : ℝ => idxAlong (cov := cov)
            γ (fun s => d • V s)
            (covAlong cov (fun s => d • V s)) t) volume (c k) (c (k + 1))) ∧
        ∀ k < N,
          (∀ᶠ σ in 𝓝 (0 : ℝ), DifferentiableAt ℝ (fun σ : ℝ =>
              ∫ t in (c k)..(c (k + 1)), (curveSpeed (I := I)
                (fun s : ℝ => GExp (cov := cov) hmet (γ s) (σ • (d • V s))) t) ^ 2) σ) ∧
          HasDerivAt (deriv (fun σ : ℝ => ∫ t in (c k)..(c (k + 1)), (curveSpeed (I := I)
              (fun s : ℝ => GExp (cov := cov) hmet (γ s) (σ • (d • V s))) t) ^ 2))
            (2 * ∫ t in (c k)..(c (k + 1)), idxAlong (cov := cov)
              γ (fun s => d • V s)
              (covAlong cov (fun s => d • V s)) t) 0 := by
  classical
  have hγsm' : ContMDiffOn 𝓘(ℝ) I ∞ γ (Ioo (a - 1) (b + 1)) := hγsm.mono (Set.subset_univ _)
  -- the cover
  obtain ⟨N, c, S, T, z, hc0, hcN, hmono, hSB, hsrc, hcdU, hcdV, hVfr, hroomA⟩ :=
    Submission.SmoothFieldCover.exists_partition_smoothField (I := I) hab.le hγsm'
      (fun s hs => hVs s ⟨by linarith [hs.1], by linarith [hs.2]⟩)
  have hNpos : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · exfalso
      rw [h] at hcN
      exact absurd (hc0 ▸ hcN : a = b) (ne_of_lt hab)
    · exact h
  have hchain : ∀ l ≤ N, ∀ k ≤ l, c k ≤ c l := by
    intro l hl k hkl
    induction l with
    | zero =>
      simp only [Nat.le_zero] at hkl
      rw [hkl]
    | succ j ih =>
      rcases Nat.eq_or_lt_of_le hkl with h | h
      · rw [h]
      · have hj : j < N := Nat.lt_of_succ_le hl
        exact le_trans (ih (le_of_lt hj) (Nat.lt_succ_iff.mp h)) (le_of_lt (hmono j hj))
  -- the compact flow sets and their flow data
  have hZc : ∀ k < N, IsCompact (γ '' Icc (S k) (T k)) := by
    intro k hk
    have hγc : ContinuousOn γ (Icc (S k) (T k)) :=
      hγsm.continuousOn.mono (Set.subset_univ _)
    exact isCompact_Icc.image_of_continuousOn hγc
  have hZs : ∀ k < N, γ '' Icc (S k) (T k) ⊆ (chartAt H (z k)).source := by
    rintro k hk _ ⟨t, ht, rfl⟩
    exact hsrc k hk t ht
  have hD : ∀ k < N, ∃ D : ChartFlowData (cov := cov) (I := I) (z k) (γ '' Icc (S k) (T k)), True :=
    fun k hk => exists_chartFlowData (cov := cov) (I := I) (z₀ := z k) (hZc k hk) (hZs k hk)
  choose D _ using hD
  have hγ1glob : ∀ k < N, ∀ t ∈ Icc (S k) (T k),
      ContMDiffOn 𝓘(ℝ) I ∞ γ (Ioo (t - 1) (t + 1)) :=
    fun k hk t ht => hγsm.mono (Set.subset_univ _)
  -- the local intervals are eventual membership sets for the image
  have hZev : ∀ k < N, ∀ t ∈ Ioo (S k) (T k), ∀ᶠ s in 𝓝 t, γ s ∈ γ '' Icc (S k) (T k) := by
    intro k hk t ht
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact ⟨s, ⟨hs.1.le, hs.2.le⟩, rfl⟩
  -- (1) the phase thresholds (in the *field* scale, at radius 1)
  have hex1 : ∀ k (hk : k < N), ∃ e : ℝ, 0 < e ∧ ∀ c ∈ Set.Ioc (0 : ℝ) e,
      ∀ σ ∈ Icc (-1 : ℝ) 1, ∀ t ∈ Icc (S k) (T k),
      (chartCoord (I := I) (z k) γ t,
          flowScale (D k hk) • (σ • chartCoords (I := I) (z k) γ (fun s => c • V s) t))
        ∈ chartData (I := I) (z k) (γ '' Icc (S k) (T k)) := by
    intro k hk
    exact Submission.EnergyPhase.exists_pos_phase_condition (cov := cov)
      (A := S k) (B := T k) (D k hk)
      (le_of_lt (lt_trans (hSB k hk).1 (lt_trans (hmono k hk) (hSB k hk).2)))
      (hcdV k hk).continuousOn (fun t ht => ⟨t, ⟨ht.1, ht.2⟩, rfl⟩)
  let e₁ : ℕ → ℝ := fun k => if hk : k < N then Classical.choose (hex1 k hk) else 1
  have he₁ : ∀ k (hk : k < N), 0 < e₁ k ∧ ∀ c ∈ Set.Ioc (0 : ℝ) (e₁ k),
      ∀ σ ∈ Icc (-1 : ℝ) 1, ∀ t ∈ Icc (S k) (T k),
      (chartCoord (I := I) (z k) γ t,
          flowScale (D k hk) • (σ • chartCoords (I := I) (z k) γ (fun s => c • V s) t))
        ∈ chartData (I := I) (z k) (γ '' Icc (S k) (T k)) := by
    intro k hk
    have := Classical.choose_spec (hex1 k hk)
    simpa only [e₁, dif_pos hk] using this
  -- (2) the energy thresholds
  have hex2 : ∀ k (hk : k < N), ∃ e : ℝ, 0 < e ∧ ∀ d ∈ Set.Ioc (0 : ℝ) e,
      HasDerivAt (deriv (fun σ : ℝ => ∫ t in (c k)..(c (k + 1)), (curveSpeed (I := I)
          (fun s : ℝ => GExp (cov := cov) hmet (γ s) (σ • (d • V s))) t) ^ 2))
        (2 * ∫ t in (c k)..(c (k + 1)), idxAlong (cov := cov) γ (fun s => d • V s)
          (covAlong cov (fun s => d • V s)) t) 0 := by
    intro k hk
    have hSk : S k < c k := (hSB k hk).1
    have hTk : c (k + 1) < T k := (hSB k hk).2
    have hak : c k < c (k + 1) := hmono k hk
    have hgeoB : ∀ t ∈ Icc (c k) (c (k + 1)), HasDerivAt
        (fun t' : ℝ => psiW (cov := cov) (D k hk) (chartCoord (I := I) (z k) γ)
          (chartCoords (I := I) (z k) γ V) 0 t')
        (chartGeodesicVectorField cov (z k) (chartCoord (I := I) (z k) γ t,
          psiW (cov := cov) (D k hk) (chartCoord (I := I) (z k) γ)
            (chartCoords (I := I) (z k) γ V) 0 t)) t := by
      set ε : ℝ := min (c k - S k) (T k - c (k + 1)) / 2 with hεdef
      have hε1 : ε ≤ c k - S k := by
        rw [hεdef]
        have h := min_le_left (c k - S k) (T k - c (k + 1))
        linarith
      have hε2 : ε ≤ T k - c (k + 1) := by
        rw [hεdef]
        have h := min_le_right (c k - S k) (T k - c (k + 1))
        linarith
      refine Submission.EnergyGeo.hasDerivAt_psiW_geodesic (cov := cov) (D k hk)
        (u := chartCoords (I := I) (z k) γ V) (ε := ε) ?_ (V := Set.univ) isOpen_univ
        (hγsm.mono (Set.subset_univ _)) (fun t _ => hgeo t) (fun t _ => hne t)
        (fun t _ => Set.subset_univ _) ?_ ?_
      · rw [hεdef]
        exact div_pos (lt_min (by linarith) (by linarith)) two_pos
      · intro t ht
        exact ⟨t, ⟨by linarith [ht.1, hε1], by linarith [ht.2, hε2]⟩, rfl⟩
      · intro t ht
        exact hsrc k hk t ⟨by linarith [ht.1, hε1], by linarith [ht.2, hε2]⟩
    have hck : a ≤ c k := hc0 ▸ hchain k (le_of_lt hk) 0 (Nat.zero_le k)
    have hck1 : c (k + 1) ≤ b := hcN ▸ hchain N le_rfl (k + 1) (Nat.succ_le_of_lt hk)
    exact energy_second_deriv_piece_scaled (cov := cov) hmet htor (D k hk) hSk hTk hak
      (fun t ht => hsrc k hk t ⟨by linarith [ht.1, hSk], by linarith [ht.2, hTk]⟩)
      (fun t ht => ⟨t, ⟨ht.1, ht.2⟩, rfl⟩)
      (hcdU k hk) (hcdV k hk) (hVfr k hk)
      (fun t ht => hγsm.mono (Set.subset_univ _))
      (fun t ht => hne t)
      (fun t ht => hVs t ⟨by linarith [hck, ht.1], by linarith [hck1, ht.2]⟩)
      hgeoB
  let e₂ : ℕ → ℝ := fun k => if hk : k < N then Classical.choose (hex2 k hk) else 1
  have he₂ : ∀ k (hk : k < N), 0 < e₂ k ∧ ∀ d ∈ Set.Ioc (0 : ℝ) (e₂ k),
      HasDerivAt (deriv (fun σ : ℝ => ∫ t in (c k)..(c (k + 1)), (curveSpeed (I := I)
          (fun s : ℝ => GExp (cov := cov) hmet (γ s) (σ • (d • V s))) t) ^ 2))
        (2 * ∫ t in (c k)..(c (k + 1)), idxAlong (cov := cov) γ (fun s => d • V s)
          (covAlong cov (fun s => d • V s)) t) 0 := by
    intro k hk
    have := Classical.choose_spec (hex2 k hk)
    simpa only [e₂, dif_pos hk] using this
  -- (3) the common scale and the assembly
  let d₀ : ℕ → ℝ := fun k => min (e₁ k) (e₂ k)
  have hd₀pos : ∀ k, 0 < d₀ k := by
    intro k
    by_cases hk : k < N
    · have hval : d₀ k = min (e₁ k) (e₂ k) := by simp only [d₀]
      rw [hval]
      exact lt_min (he₁ k hk).1 (he₂ k hk).1
    · have hval : d₀ k = 1 := by simp only [d₀, e₁, e₂, dif_neg hk, min_self]
      rw [hval]
      norm_num
  have hneF : ((Finset.range N).image d₀).Nonempty :=
    ⟨d₀ 0, Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hNpos, rfl⟩⟩
  refine ⟨N, c, ((Finset.range N).image d₀).min' hneF, ?_, hc0, hcN, hmono, ?_⟩
  · have hmem : ((Finset.range N).image d₀).min' hneF ∈ (Finset.range N).image d₀ :=
      Finset.min'_mem _ hneF
    obtain ⟨k, hk, hk'⟩ := Finset.mem_image.mp hmem
    rw [← hk']
    exact hd₀pos k
  · intro d hd
    have hle_of : ∀ k < N, d ≤ d₀ k := fun k hk => le_trans hd.2 (Finset.min'_le _ _
      (Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩))
    have hle1 : ∀ k < N, d ≤ e₁ k := fun k hk => le_trans (hle_of k hk) (min_le_left _ _)
    have hle2 : ∀ k < N, d ≤ e₂ k := fun k hk => le_trans (hle_of k hk) (min_le_right _ _)
    have hcdVs : ∀ k < N, ContDiffOn ℝ ∞ (chartCoords (I := I) (z k) γ (fun s => d • V s))
        (Icc (S k) (T k)) := by
      intro k hk
      rw [chartCoords_smul]
      exact (hcdV k hk).const_smul d
    have hVfrs : ∀ k < N, ∀ t ∈ Icc (S k) (T k), frameVector (I := I) (z k) (γ t)
        (chartCoords (I := I) (z k) γ (fun s => d • V s) t) = (fun s => d • V s) t := by
      intro k hk t ht
      rw [chartCoords_smul]
      show frameVector (I := I) (z k) (γ t) (d • chartCoords (I := I) (z k) γ V t) = d • V t
      rw [frameVector_smul, hVfr k hk t ht]
    have hZmem : ∀ k < N, ∀ t ∈ Icc (S k) (T k), γ t ∈ γ '' Icc (S k) (T k) :=
      fun k hk t ht => ⟨t, ⟨ht.1, ht.2⟩, rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · filter_upwards [isOpen_Ioo.mem_nhds (show (0 : ℝ) ∈ Ioo (-(1 / 2)) (1 / 2) from
        ⟨by norm_num, by norm_num⟩)] with σ hσ k hk
      exact intervalIntegrable_piece_energy (cov := cov) hmet (D k hk) (hSB k hk).1 (hSB k hk).2
        (hmono k hk).le (fun t ht => hsrc k hk t ht) (hcdU k hk) (hcdVs k hk) (hVfrs k hk)
        (hZmem k hk) ((he₁ k hk).2 d ⟨hd.1, hle1 k hk⟩) σ hσ
    · intro k hk
      exact intervalIntegrable_piece_idxAlong (cov := cov) htor (D k hk) (hSB k hk).1 (hSB k hk).2
        (hmono k hk).le (fun t ht => hsrc k hk t ht) (hcdU k hk) (hcdV k hk) (hVfr k hk)
        (hγ1glob k hk) (fun t ht => hne t)
        (fun t ht => hVs t ⟨(hroomA k hk ht).1.le, (hroomA k hk ht).2.le⟩) d
    · intro k hk
      exact ⟨eventually_differentiableAt_piece_energy (cov := cov) hmet (D k hk) (hSB k hk).1
        (hSB k hk).2 (hmono k hk).le one_pos (fun t ht => hsrc k hk t ht) (hcdU k hk) (hcdVs k hk)
        (hVfrs k hk) (hZev k hk) ((he₁ k hk).2 d ⟨hd.1, hle1 k hk⟩),
        (he₂ k hk).2 d ⟨hd.1, hle2 k hk⟩⟩

end

end Submission.EnergyRayCover
