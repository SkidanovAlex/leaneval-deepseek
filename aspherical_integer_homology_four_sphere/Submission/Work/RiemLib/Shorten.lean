import Submission.Work.RiemLib.BrokenLength
import Submission.Work.RiemLib.CornerStrict
import Submission.Work.RiemLib.GExpTranslate
import Submission.Work.RiemLib.Distance
import Submission.Work.RiemLib.XuStep

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter MeasureTheory
open Submission.Geodesic
open Submission.GeodesicSpeed
open Submission.GlobalExp
open Submission.Length
open Submission.InjRadius

namespace Submission.Shorten

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

/-- **The length of a closed broken geodesic loop with one corner.**  Let `β` be a closed curve with
`β 0 = β T = q` which coincides with the `GExp`-ray in the unit direction `u₁` on `[0,ε]`, with the
ray in the direction `u₂` (run backwards) on `[T-ε, T]`, and has unit speed in between.  Then its
length is `T` — the two ray-pieces contribute `ε` each and the middle piece `T - 2ε`. -/
theorem curveLength_corner_loop (hmet : IsMetricCompatible cov) {q : M}
    {u₁ u₂ : TangentSpace I q} (h₁ : ‖u₁‖ = 1) (h₂ : ‖u₂‖ = 1)
    {ε T : ℝ} (hε : 0 < ε) (hTε : 2 * ε < T)
    {β : ℝ → M} (hstart : ∀ t ∈ Icc 0 ε, β t = GExp (cov := cov) hmet q (t • u₁))
    (hend : ∀ t ∈ Icc (T - ε) T, β t = GExp (cov := cov) hmet q ((t - T) • u₂))
    (hspeed : ∀ t ∈ Icc ε (T - ε), curveSpeed (I := I) β t = 1) :
    curveLength (I := I) β 0 T = T := by
  classical
  have h₁ne : u₁ ≠ 0 := by
    intro h0; rw [h0, norm_zero] at h₁; norm_num at h₁
  have h₂ne : u₂ ≠ 0 := by
    intro h0; rw [h0, norm_zero] at h₂; norm_num at h₂
  have hT : 0 < T := by linarith
  have hraymd₁ : ∀ r : ℝ, MDifferentiableAt 𝓘(ℝ) I
      (fun r : ℝ => GExp (cov := cov) hmet q (r • u₁)) r := fun r =>
    ((Submission.LensLoop.contMDiffOn_GExp_smul (cov := cov) hmet q h₁ne).contMDiffAt
      Filter.univ_mem).mdifferentiableAt (by simp)
  have hraymd₂ : ∀ r : ℝ, MDifferentiableAt 𝓘(ℝ) I
      (fun r : ℝ => GExp (cov := cov) hmet q (r • u₂)) r := fun r =>
    ((Submission.LensLoop.contMDiffOn_GExp_smul (cov := cov) hmet q h₂ne).contMDiffAt
      Filter.univ_mem).mdifferentiableAt (by simp)
  -- the speed is `1` at every point of `(0,T)`
  have hgood : ∀ t ∈ Ioo (0 : ℝ) T, curveSpeed (I := I) β t = 1 := by
    intro t ht
    rcases lt_or_ge t ε with hlt | hge
    · have hev : β =ᶠ[𝓝 t] (fun s : ℝ => GExp (cov := cov) hmet q (s • u₁)) := by
        filter_upwards [Ioo_mem_nhds ht.1 hlt] with s hs
        exact hstart s ⟨hs.1.le, hs.2.le⟩
      rw [curveSpeed_congr_of_eventuallyEq (I := I) hev,
        Submission.BrokenLength.curveSpeed_GExp_ray (cov := cov) hmet q h₁ne t, h₁]
    · rcases le_or_gt t (T - ε) with hle | hgt
      · exact hspeed t ⟨hge, hle⟩
      · have hev : β =ᶠ[𝓝 t] (fun s : ℝ => GExp (cov := cov) hmet q ((s - T) • u₂)) := by
          filter_upwards [Ioo_mem_nhds hgt ht.2] with s hs
          exact hend s ⟨hs.1.le, hs.2.le⟩
        rw [curveSpeed_congr_of_eventuallyEq (I := I) hev]
        rw [show (fun s : ℝ => GExp (cov := cov) hmet q ((s - T) • u₂))
            = (fun s : ℝ => (fun r : ℝ => GExp (cov := cov) hmet q (r • u₂))
                (1 * s + (-T))) from by
          funext s; rw [one_mul, sub_eq_add_neg]]
        rw [Submission.LensLoop.curveSpeed_comp_mul_add_abs (I := I) (c := 1) (d := -T) (t := t)
          (by norm_num) (hraymd₂ (1 * t + (-T)))]
        rw [show |(1 : ℝ)| = 1 from by norm_num, one_mul,
          Submission.BrokenLength.curveSpeed_GExp_ray (cov := cov) hmet q h₂ne (1 * t + (-T)), h₂]
  -- hence the integral of the speed is the integral of the constant `1`
  rw [curveLength_def]
  have hcongr : (∫ t in (0 : ℝ)..T, curveSpeed (I := I) β t) = ∫ _t in (0 : ℝ)..T, (1 : ℝ) := by
    refine intervalIntegral.integral_congr_ae ?_
    rw [MeasureTheory.ae_iff]
    refine MeasureTheory.measure_mono_null (fun t ht => ?_)
      (measure_union_null (measure_singleton 0) (measure_singleton T))
    rw [Set.mem_ofPred_eq, Classical.not_imp] at ht
    obtain ⟨htmem, htspeed⟩ := ht
    by_contra hcon
    rw [Set.mem_union, Set.mem_singleton_iff, Set.mem_singleton_iff, not_or] at hcon
    have htIoc : t ∈ Set.Ioc (0 : ℝ) T := by
      rwa [uIoc_of_le hT.le] at htmem
    exact htspeed (hgood t ⟨htIoc.1, lt_of_le_of_ne htIoc.2 hcon.2⟩)
  rw [hcongr, intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero]

/-- **The length of a `GExp`-ray over `[a,b]`** (including the degenerate direction `v = 0`). -/
theorem curveLength_GExp_ray_all (hmet : IsMetricCompatible cov) (p : M) (v : TangentSpace I p)
    {a b : ℝ} (hab : a ≤ b) :
    curveLength (I := I) (fun s : ℝ => GExp (cov := cov) hmet p (s • v)) a b = ‖v‖ * (b - a) := by
  rcases eq_or_ne v 0 with hv0 | hv
  · subst hv0
    have hconst : (fun s : ℝ => GExp (cov := cov) hmet p (s • (0 : TangentSpace I p)))
        = fun _ : ℝ => p := by
      funext s; rw [smul_zero, GExp_zero]
    rw [hconst, curveLength_const, norm_zero, zero_mul]
  · exact Submission.BrokenLength.curveLength_GExp_ray (cov := cov) hmet p hv hab

/-- **Cutting a corner: a lens loop is never length-minimising.**  Let `ξ ≠ η`-style* data be given by
a *lens*: two unit directions `ξ, η` at `p` whose rays of length `m` meet again at
`q = GExp p (m • ξ) = GExp p (m • η)` (so the broken loop `p → q → p` has length `2m`).  If the two
points at distance `ε < m` from `q` along the two geodesics — `A' = GExp p ((m-ε) • ξ)` and
`B' = GExp p ((m-ε) • η)` — are strictly closer than `2ε` (i.e. the corner at `q` is not already
straight, cf. `CornerStrict.edist_GExp_lt_of_unit_ne_neg`), then there is a **closed piecewise smooth
path at `p` of length `< 2m`**: traverse the `ξ`-ray up to `A'`, cross over to `B'` by a minimising
geodesic, and come back to `p` along the `η`-ray.

(*) The hypothesis is stated as the strict inequality rather than as an inequality of the two
velocities at `q`, because those two velocities live in the tangent spaces at
`GExp p (m • ξ)` and `GExp p (m • η)`, which are only *propositionally* equal. -/
theorem exists_shorter_loop_of_lt (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M]
    (p : M) {ξ η : TangentSpace I p} (hξ : ‖ξ‖ = 1) (hη : ‖η‖ = 1)
    {m ε : ℝ} (hm : 0 < m) (hε : 0 < ε) (hεm : ε < m)
    (hstrict : Manifold.riemannianEDist I (GExp (cov := cov) hmet p ((m - ε) • ξ))
      (GExp (cov := cov) hmet p ((m - ε) • η)) < ENNReal.ofReal (2 * ε)) :
    ∃ P : Submission.Distance.PwPath I p p, P.length < 2 * m := by
  classical
  have hξne : ξ ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hξ; norm_num at hξ
  have hηne : η ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hη; norm_num at hη
  have honele : (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := WithTop.coe_le_coe.mpr le_top
  -- the two points at distance `ε` from the corner
  set A' : M := GExp (cov := cov) hmet p ((m - ε) • ξ) with hA'def
  set B' : M := GExp (cov := cov) hmet p ((m - ε) • η) with hB'def
  obtain ⟨v, hvG, hvd⟩ :=
    Submission.HopfRinow.exists_geodesic_riemannianEDist_eq (cov := cov) hmet htor A' B'
  have hvnorm : ‖v‖ < 2 * ε := by
    have h : ENNReal.ofReal ‖v‖ < ENNReal.ofReal (2 * ε) := by
      rw [← hvd, hA'def, hB'def]; exact hstrict
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (norm_nonneg v)).mp h
  -- the three pieces
  let piece : ℕ → ℝ → M := fun i =>
    match i with
    | 0 => fun s : ℝ => GExp (cov := cov) hmet p (s • ξ)
    | 1 => fun s : ℝ => GExp (cov := cov) hmet A' (s • v)
    | _ => fun s : ℝ => GExp (cov := cov) hmet p ((m - ε - s) • η)
  let bb : ℕ → ℝ := fun i => match i with
    | 0 => m - ε
    | 1 => 1
    | _ => m - ε
  have hraymd : ∀ (x : M) (w : TangentSpace I x) (r : ℝ), MDifferentiableAt 𝓘(ℝ) I
      (fun r' : ℝ => GExp (cov := cov) hmet x (r' • w)) r := by
    intro x w r
    by_cases hw : w = 0
    · subst hw
      have hconst : (fun r : ℝ => GExp (cov := cov) hmet x (r • (0 : TangentSpace I x)))
          = fun _ : ℝ => x := by
        funext r; rw [smul_zero, GExp_zero]
      rw [hconst]
      exact mdifferentiableAt_const
    · exact ((Submission.LensLoop.contMDiffOn_GExp_smul (cov := cov) hmet x hw).contMDiffAt
        Filter.univ_mem).mdifferentiableAt (by simp)
  have hpiece1 : ∀ s : ℝ, curveSpeed (I := I) (fun r : ℝ => GExp (cov := cov) hmet A' (r • v)) s
      = ‖v‖ := by
    intro s
    rcases eq_or_ne v 0 with hv0 | hv
    · rw [hv0, norm_zero]
      have hconst : (fun r : ℝ => GExp (cov := cov) hmet A' (r • (0 : TangentSpace I A')))
          =ᶠ[𝓝 s] (fun _ : ℝ => A') := by
        filter_upwards with r; rw [smul_zero, GExp_zero]
      rw [curveSpeed_congr_of_eventuallyEq (I := I) hconst, curveSpeed_const]
    · exact Submission.BrokenLength.curveSpeed_GExp_ray (cov := cov) hmet A' hv s
  have hpiece2 : ∀ s : ℝ, curveSpeed (I := I)
      (fun r : ℝ => GExp (cov := cov) hmet p ((m - ε - r) • η)) s = 1 := by
    intro s
    rw [show (fun r : ℝ => GExp (cov := cov) hmet p ((m - ε - r) • η))
        = (fun r : ℝ => (fun r' : ℝ => GExp (cov := cov) hmet p (r' • η))
            ((-1) * r + (m - ε))) from by
      funext r
      congr 1
      ring]
    rw [Submission.LensLoop.curveSpeed_comp_mul_add_abs (I := I) (c := -1) (d := m - ε) (t := s)
      (by norm_num) (hraymd p η (-1 * s + (m - ε)))]
    rw [show |(-1 : ℝ)| = 1 from by norm_num, one_mul,
      Submission.BrokenLength.curveSpeed_GExp_ray (cov := cov) hmet p hηne (-1 * s + (m - ε)), hη]
  -- the integrals of the three pieces
  have hI0 : (∫ s in (0 : ℝ)..(bb 0), curveSpeed (I := I) (piece 0) s) = m - ε := by
    show curveLength (I := I) (fun s : ℝ => GExp (cov := cov) hmet p (s • ξ)) 0 (m - ε) = m - ε
    rw [curveLength_GExp_ray_all (cov := cov) hmet p ξ (by linarith), hξ, one_mul]
    ring
  have hI1 : (∫ s in (0 : ℝ)..(bb 1), curveSpeed (I := I) (piece 1) s) = ‖v‖ := by
    show curveLength (I := I) (fun r : ℝ => GExp (cov := cov) hmet A' (r • v)) 0 1 = ‖v‖
    rw [Submission.BrokenLength.curveLength_eq_mul_of_curveSpeed_eq (by norm_num : (0:ℝ) ≤ 1)
      (fun t _ => hpiece1 t)]
    ring
  have hI2 : (∫ s in (0 : ℝ)..(bb 2), curveSpeed (I := I) (piece 2) s) = m - ε := by
    show curveLength (I := I) (fun r : ℝ => GExp (cov := cov) hmet p ((m - ε - r) • η)) 0 (m - ε)
      = m - ε
    rw [Submission.BrokenLength.curveLength_eq_sub_of_curveSpeed_eq_one (by linarith)
      (fun t _ => hpiece2 t)]
    ring
  refine ⟨⟨2, piece, fun _ => 0, bb, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro i
    rcases i with _ | _ | i
    · show (0 : ℝ) ≤ m - ε
      linarith
    · show (0 : ℝ) ≤ 1
      norm_num
    · show (0 : ℝ) ≤ m - ε
      linarith
  · intro i
    rcases i with _ | _ | i
    · show ContMDiff 𝓘(ℝ) I 1 (fun s : ℝ => GExp (cov := cov) hmet p (s • ξ))
      exact ContMDiff.of_le (contMDiffOn_univ.mp
        (Submission.LensLoop.contMDiffOn_GExp_smul (cov := cov) hmet p hξne)) honele
    · show ContMDiff 𝓘(ℝ) I 1 (fun s : ℝ => GExp (cov := cov) hmet A' (s • v))
      by_cases hv : v = 0
      · subst hv
        have hconst : (fun s : ℝ => GExp (cov := cov) hmet A' (s • (0 : TangentSpace I A')))
            = fun _ : ℝ => A' := by
          funext s; rw [smul_zero, GExp_zero]
        rw [show (fun s : ℝ => GExp (cov := cov) hmet A' (s • (0 : TangentSpace I A')))
            = (fun _ : ℝ => A') from hconst]
        exact ContMDiff.of_le contMDiff_const honele
      · exact ContMDiff.of_le (contMDiffOn_univ.mp
          (Submission.LensLoop.contMDiffOn_GExp_smul (cov := cov) hmet A' hv)) honele
    · show ContMDiff 𝓘(ℝ) I 1 (fun s : ℝ => GExp (cov := cov) hmet p ((m - ε - s) • η))
      exact ContMDiff.of_le ((contMDiffOn_univ.mp
        (Submission.LensLoop.contMDiffOn_GExp_smul (cov := cov) hmet p hηne)).comp
          (contDiff_const.sub contDiff_id).contMDiff) honele
  · intro i hi
    rcases i with _ | _ | i
    · show GExp (cov := cov) hmet p ((m - ε) • ξ) = GExp (cov := cov) hmet A' (0 • v)
      rw [zero_smul, GExp_zero, hA'def]
    · show GExp (cov := cov) hmet A' (1 • v) = GExp (cov := cov) hmet p ((m - ε - 0) • η)
      rw [one_smul, hvG, hB'def]
      norm_num
    · exact absurd hi (by omega)
  · show GExp (cov := cov) hmet p (0 • ξ) = p
    rw [zero_smul, GExp_zero]
  · show GExp (cov := cov) hmet p ((m - ε - (m - ε)) • η) = p
    rw [sub_self, zero_smul, GExp_zero]
  · show (∑ i ∈ Finset.range (2 + 1), (∫ s in (0 : ℝ)..bb i, curveSpeed (I := I) (piece i) s))
      < 2 * m
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    show (∫ s in (0 : ℝ)..bb 0, curveSpeed (I := I) (piece 0) s)
      + (∫ s in (0 : ℝ)..bb 1, curveSpeed (I := I) (piece 1) s)
      + (∫ s in (0 : ℝ)..bb 2, curveSpeed (I := I) (piece 2) s) < 2 * m
    rw [hI0, hI1, hI2]
    linarith

end

end Submission.Shorten
