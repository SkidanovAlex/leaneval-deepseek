import Submission.Work.RiemLib.EnergyRayCover
import Submission.Work.RiemLib.EnergyPhase

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
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
# Smoothness in `t` of the intrinsic geodesic variation along a `GExp`-ray

The shortening argument of the global `σ ≤ κ` (`ConjCut.CutConjInequality`) needs, besides the second
variation `E''(0) = 2 ∫ idxAlong` of `Submission.EnergyRayGlobal.energy_second_deriv_ray`, the
**lower bound** `L ≤ E(σ)` for the energy
`E(σ) = ∫_a^b (curveSpeed (fun t => GExp (γ t) (σ • (d • V t))))²` of the geodesic variation.  That
bound comes from `Manifold.riemannianEDist ≤ pathELength`, hence needs the *curve*
`t ↦ GExp (γ t) (σ • (d • V t))` to be `C¹` on `[a,b]`.

This module supplies the smoothness: per chart piece (`contMDiffAt_piece_curve`, stated for the
*open* local interval so that it gives a genuine `ContMDiffAt`), glued over the cover
(`contMDiffOn_ray_family`).
-/

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

/-! ## The combinatorial part: locating the piece containing a point -/

/-- A point of `[a,b]` lies in one of the intervals of a partition. -/
lemma exists_le_le_of_partition {a b : ℝ} {N : ℕ} {c : ℕ → ℝ}
    (hc0 : c 0 = a) (hcN : c N = b) (hmono : ∀ k < N, c k ≤ c (k + 1))
    (hab : a < b) {t : ℝ} (ht : t ∈ Icc a b) :
    ∃ k < N, c k ≤ t ∧ t ≤ c (k + 1) := by
  have hNpos : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · exfalso; rw [h] at hcN
      exact absurd (hc0 ▸ hcN : a = b) (ne_of_lt hab)
    · exact h
  have hchain : ∀ l ≤ N, ∀ k ≤ l, c k ≤ c l := by
    intro l hl k hkl
    induction l with
    | zero => simp only [Nat.le_zero] at hkl; rw [hkl]
    | succ j ih =>
      rcases Nat.eq_or_lt_of_le hkl with h | h
      · rw [h]
      · have hj : j < N := Nat.lt_of_succ_le hl
        exact le_trans (ih (le_of_lt hj) (Nat.lt_succ_iff.mp h)) (hmono j hj)
  have hne : (Finset.filter (fun k => c k ≤ t) (Finset.range (N + 1))).Nonempty := by
    refine ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.zero_lt_succ N), ?_⟩⟩
    rw [hc0]; exact ht.1
  let k : ℕ := (Finset.filter (fun k => c k ≤ t) (Finset.range (N + 1))).max' hne
  have hkmem : k ∈ Finset.filter (fun k => c k ≤ t) (Finset.range (N + 1)) :=
    Finset.max'_mem _ hne
  have hkmax : ∀ j ∈ Finset.filter (fun j => c j ≤ t) (Finset.range (N + 1)), j ≤ k :=
    fun j hj => Finset.le_max' _ _ hj
  have hklt : k < N + 1 := Finset.mem_range.mp (Finset.mem_filter.mp hkmem).1
  have hck : c k ≤ t := (Finset.mem_filter.mp hkmem).2
  rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hklt) with hlt | heq
  · refine ⟨k, hlt, hck, ?_⟩
    have hnotmem : k + 1 ∉ Finset.filter (fun j => c j ≤ t) (Finset.range (N + 1)) := by
      intro hmem
      have := hkmax (k + 1) hmem
      omega
    have hrange : k + 1 ∈ Finset.range (N + 1) := Finset.mem_range.mpr (by omega)
    have : ¬ (c (k + 1) ≤ t) := fun hc' => hnotmem (Finset.mem_filter.mpr ⟨hrange, hc'⟩)
    exact le_of_lt (lt_of_not_ge this)
  · rw [heq] at hck
    have htb : t = b := le_antisymm ht.2 (by rw [← hcN]; exact hck)
    refine ⟨N - 1, by omega, ?_, ?_⟩
    · rw [htb, ← hcN]
      exact hchain N le_rfl (N - 1) (by omega)
    · rw [htb, ← hcN, show N - 1 + 1 = N by omega]

/-! ## Smoothness on one chart piece -/

/-- **Smoothness in `t` of the piece curve of the intrinsic family.**  On a chart piece carrying the
`C^∞` data of `γ` and of the field `V`, and on which the phase condition holds for `|σ| ≤ δ`, the
curve `t ↦ GExp (γ t) (σ • V t)` is `C^∞` at every point of the *open* local interval. -/
lemma contMDiffAt_piece_curve (hmet : IsMetricCompatible cov)
    {γ : ℝ → M} {V : (t : ℝ) → TangentSpace I (γ t)} {z : M} {Z : Set M}
    (D : ChartFlowData (cov := cov) (I := I) z Z)
    {S T δ : ℝ} (hδ : 0 < δ)
    (hsrc : ∀ t ∈ Icc S T, γ t ∈ (chartAt H z).source)
    (hcdU : ContDiffOn ℝ ∞ (chartCoord (I := I) z γ) (Icc S T))
    (hcdV : ContDiffOn ℝ ∞ (chartCoords (I := I) z γ V) (Icc S T))
    (hVfr : ∀ t ∈ Icc S T, frameVector (I := I) z (γ t) (chartCoords (I := I) z γ V t) = V t)
    (hZ : ∀ t ∈ Icc S T, γ t ∈ Z)
    (hphase : ∀ σ ∈ Icc (-δ) δ, ∀ t ∈ Icc S T,
      (chartCoord (I := I) z γ t, flowScale D • (σ • chartCoords (I := I) z γ V t))
        ∈ chartData (I := I) z Z) :
    ∀ σ ∈ Ioo (-(δ / 2)) (δ / 2), ∀ t ∈ Ioo S T,
      ContMDiffAt 𝓘(ℝ) I ∞ (fun t : ℝ => GExp (cov := cov) hmet (γ t) (σ • V t)) t := by
  intro σ hσ t ht
  set x : ℝ → E := chartCoord (I := I) z γ with hxdef
  set u : ℝ → E := chartCoords (I := I) z γ V with hudef
  have hσδ : σ ∈ Icc (-δ) δ := ⟨by linarith [hσ.1, hδ], by linarith [hσ.2, hδ]⟩
  have hFcd : ContDiffOn ℝ ∞ (Fam (cov := cov) D x u) (Ioo (-δ) δ ×ˢ Ioo S T) :=
    Submission.SecondVarGlobal.contDiffOn_fam_Ioo (cov := cov) D
      (hcdU.mono (fun t ht => ⟨ht.1.le, ht.2.le⟩))
      (hcdV.mono (fun t ht => ⟨ht.1.le, ht.2.le⟩)) hphase
  have hslice : ContDiffOn ℝ ∞ (fun t : ℝ => (σ, t)) (Ioo S T) :=
    (contDiffOn_const (c := σ)).prodMk contDiffOn_id
  have hcomp : ContDiffOn ℝ ∞ (fun t : ℝ => Fam (cov := cov) D x u (σ, t)) (Ioo S T) :=
    hFcd.comp hslice (fun t ht' =>
      ⟨⟨by linarith [hσ.1, hδ], by linarith [hσ.2, hδ]⟩, ht'⟩)
  have hmemT : ∀ t ∈ Ioo S T, fam (cov := cov) D x u σ t ∈ (extChartAt I z).target := fun t ht' =>
    Submission.SecondVarGlobal.fam_mem_target' (cov := cov) D (x := x) (u := u) (σ := σ) (t := t)
      (D.hKO (hphase σ hσδ t ⟨ht'.1.le, ht'.2.le⟩))
  have hbase : ContMDiffOn 𝓘(ℝ) I ∞
      (fun t : ℝ => (extChartAt I z).symm (Fam (cov := cov) D x u (σ, t))) (Ioo S T) :=
    (contMDiffOn_extChartAt_symm (I := I) (n := ∞) z).comp
      (contMDiffOn_iff_contDiffOn.mpr hcomp)
      (fun t ht' => by rw [Set.mem_preimage, Fam_apply]; exact hmemT t ht')
  have hbaseAt : ContMDiffAt 𝓘(ℝ) I ∞
      (fun t : ℝ => (extChartAt I z).symm (Fam (cov := cov) D x u (σ, t))) t :=
    hbase.contMDiffAt (isOpen_Ioo.mem_nhds ht)
  have heq : (fun t : ℝ => GExp (cov := cov) hmet (γ t) (σ • V t))
      =ᶠ[𝓝 t] (fun t : ℝ => (extChartAt I z).symm (Fam (cov := cov) D x u (σ, t))) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    have hsS : s ∈ Icc S T := ⟨hs.1.le, hs.2.le⟩
    have hVs : frameVector (I := I) z (γ s) (u s) = V s := by
      rw [hudef]; exact hVfr s hsS
    have hsrc' : γ s ∈ (extChartAt I z).source := by
      rw [extChartAt_source]; exact hsrc s hsS
    have hphO : ((extChartAt I z) (γ s), flowScale D • (σ • u s)) ∈ D.O :=
      D.hKO (hphase σ hσδ s hsS)
    have h1 : GExp (cov := cov) hmet (γ s) (σ • V s)
        = GExp (cov := cov) hmet (γ s) (frameVector (I := I) z (γ s) (σ • u s)) := by
      rw [← hVs, ← Submission.GExpSmooth.frameVector_smul']
    rw [h1, Submission.UniformInj.GExp_eq_symm_Hfun (cov := cov) hmet D (hZ s hsS) hsrc' hphO,
      Fam_apply, fam_apply]
    rw [hxdef]
    rfl
  exact hbaseAt.congr_of_eventuallyEq heq

/-! ## The global smoothness along a `GExp`-ray -/

/-- **Smoothness in `t` of the intrinsic geodesic variation of a `GExp`-ray.**  There is a scale
`c₀ > 0` such that for every `d ∈ (0, c₀]` and all `σ` in a neighbourhood of `0` the curve
`t ↦ GExp (γ t) (σ • (d • V t))` is `C^∞` on `[a,b]` and its speed is continuous on `[a,b]`
(the two inputs of `Manifold.riemannianEDist ≤ pathELength`). -/
theorem contMDiffOn_ray_family (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {p : M} {ξ : TangentSpace I p} (hξ : ξ ≠ 0)
    {V : (t : ℝ) → TangentSpace I (GExp (cov := cov) hmet p (t • ξ))}
    {a b : ℝ}
    (hVs : ∀ s ∈ Icc (a - 1) (b + 1),
      SmoothAlongAt (I := I) (fun s : ℝ => GExp (cov := cov) hmet p (s • ξ)) V s)
    (hab : a < b) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ d ∈ Set.Ioc (0 : ℝ) c₀, ∀ᶠ σ in 𝓝 (0 : ℝ),
      ContMDiffOn 𝓘(ℝ) I ∞ (fun t : ℝ => GExp (cov := cov) hmet
        (GExp (cov := cov) hmet p (t • ξ)) (σ • (d • V t))) (Icc a b) ∧
      ContinuousOn (fun t : ℝ => curveSpeed (I := I) (fun t' : ℝ => GExp (cov := cov) hmet
        (GExp (cov := cov) hmet p (t' • ξ)) (σ • (d • V t'))) t) (Icc a b) := by
  classical
  set γ : ℝ → M := fun s : ℝ => GExp (cov := cov) hmet p (s • ξ) with hγdef
  have hγsm : ContMDiffOn 𝓘(ℝ) I ∞ γ (Ioo (a - 1) (b + 1)) := by
    rw [hγdef]
    refine (Submission.LensLoop.contMDiffOn_GExp_smul_Ioo_symm (cov := cov) hmet p hξ
      (max (b + 1) (1 - a) + 1)).mono ?_
    intro t ht
    refine ⟨?_, ?_⟩
    · linarith [ht.1, le_max_right (b + 1) (1 - a)]
    · linarith [ht.2, le_max_left (b + 1) (1 - a)]
  obtain ⟨N, c, S, T, z, hc0, hcN, hmono, hSB, hsrc, hcdU, hcdV, hVfr, hroomA⟩ :=
    Submission.SmoothFieldCover.exists_partition_smoothField (I := I) hab.le hγsm
      (fun s hs => hVs s ⟨by linarith [hs.1], by linarith [hs.2]⟩)
  have hNpos : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · exfalso
      rw [h] at hcN
      exact absurd (hc0 ▸ hcN : a = b) (ne_of_lt hab)
    · exact h
  have hZc : ∀ k < N, IsCompact (γ '' Icc (S k) (T k)) := by
    intro k hk
    have hγc : ContinuousOn γ (Icc (S k) (T k)) := by
      rw [hγdef]
      have h1 : ContinuousOn (fun s : ℝ => (extChartAt I (z k)).symm
          (chartCoord (I := I) (z k) γ s)) (Icc (S k) (T k)) :=
        continuousOn_chartCurve (I := I) (hcdU k hk).continuousOn
          (fun t ht => (extChartAt I (z k)).map_source (by
            rw [extChartAt_source]; exact hsrc k hk t ht))
      refine h1.congr ?_
      intro t ht
      rw [← hγdef]
      exact (PartialEquiv.left_inv (extChartAt I (z k)) (by
        rw [extChartAt_source]; exact hsrc k hk t ht)).symm
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
      (hcdV k hk).continuousOn (fun t ht => ⟨t, ⟨ht.1, ht.2⟩, by rw [hγdef]⟩)
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
        (fun t' ht' => ⟨t', ⟨ht'.1, ht'.2⟩, by rw [hγdef]⟩)
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
        (fun t' ht' => ⟨t', ⟨ht'.1, ht'.2⟩, by rw [hγdef]⟩)
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
  have hne : ((Finset.range N).image e₀).Nonempty :=
    ⟨e₀ 0, Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hNpos, rfl⟩⟩
  refine ⟨((Finset.range N).image e₀).min' hne, ?_, fun d hd => ?_⟩
  · have hmem : ((Finset.range N).image e₀).min' hne ∈ (Finset.range N).image e₀ :=
      Finset.min'_mem _ hne
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
