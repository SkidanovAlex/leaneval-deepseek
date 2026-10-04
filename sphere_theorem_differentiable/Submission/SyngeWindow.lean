import Submission.SyngePackage
import Submission.SyngeShorten

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The window bridge: `SmoothAlongAt`/`covAlong` for the periodic extension of the Synge field

`Submission.SyngeShorten.exists_shorter_closed_curve` (Synge's shortening lemma) needs the field data
on `Icc (0 - 1) (1 + 1)`, while `Submission.HolDet.exists_synge_field` produces them on the cover of the
loop, i.e. on `Icc 0 1`.  This module supplies the bridge: for a **`1`-periodic** geodesic `γ`
(`γ (t + 1) = γ t`), the *periodic extension*
`X̃ s := X (s+1)` for `s < 0`, `X s` for `s ∈ [0,1]`, `X (s-1)` for `s > 1`
of the Synge field has the same three properties (smooth along `γ`, parallel, unit, normal) on the
whole window `Icc (-1) 2`, and is `1`-periodic as well (`X̃ 1 = X̃ 0`).

The points `s ∈ (0,1)`, `(1,2)`, `(-1,0)` are handled by *shift lemmas* (the chart coordinates of the
shifted field are the shifted chart coordinates, because the chart `γ s` is `1`-periodic), and the two
junction points `s = 0, 1` by the chart-free uniqueness of parallel fields
(`Submission.ParallelRoom.eqOn_of_parallel`) applied to the two *room solutions* that meet there.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.JacobiGlobal
open Submission.JacobiCoords
open Submission.ChartConnection
open Submission.IntrinsicVariation
open Submission.BonnetMyers
open Submission.GlobalExp
open Submission.ParallelGlobal
open Submission.OrientSign
open Submission.ParallelRoom
open Submission.CurvatureVec
open Submission.GeodesicSpeed
open Submission.Length

namespace Submission.SyngeWindow

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
variable {γ : ℝ → M}

/-- **The periodic extension** of a field along a `1`-periodic curve. -/
noncomputable def pext (X : (t : ℝ) → TangentSpace I (γ t)) : (t : ℝ) → TangentSpace I (γ t) :=
  fun s => if s < 0 then X (s + 1) else if s ≤ 1 then X s else X (s - 1)

theorem pext_of_mem {X : (t : ℝ) → TangentSpace I (γ t)} {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    pext (I := I) X s = X s := by
  rw [pext, if_neg (not_lt.mpr h0), if_pos h1]

theorem pext_of_neg {X : (t : ℝ) → TangentSpace I (γ t)} {s : ℝ} (h : s < 0) :
    pext (I := I) X s = X (s + 1) := by
  rw [pext, if_pos h]

theorem pext_of_one_lt {X : (t : ℝ) → TangentSpace I (γ t)} {s : ℝ} (h : 1 < s) :
    pext (I := I) X s = X (s - 1) := by
  rw [pext, if_neg (not_lt.mpr (by linarith : (0 : ℝ) ≤ s)), if_neg (not_le.mpr h)]

/-- The velocity of a `1`-periodic curve is `1`-periodic. -/
theorem curveVelocity_periodic (hper : ∀ t : ℝ, γ (t + 1) = γ t) (hγsm : ContMDiff 𝓘(ℝ) I ∞ γ)
    (t : ℝ) : curveVelocity (I := I) γ (t + 1) = curveVelocity (I := I) γ t := by
  have h1 := Submission.SecondVarGlobal.curveVelocity_comp_add_right (I := I) γ 1 t
    (hγsm.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0))
  have h2 : (fun x : ℝ => γ (x + 1)) = γ := by funext x; exact hper x
  rw [h2] at h1
  simpa using h1.symm

/-! ## Shift lemmas

For a `1`-periodic `γ`, the chart at `γ s` and the chart at `γ (s ± 1)` are the same, so the chart
coordinates of a shifted field are the shifted chart coordinates. -/

/-- The chart coordinates of the field shifted by `+1` are the shifted chart coordinates. -/
theorem chartCoords_shift_one (hper : ∀ t : ℝ, γ (t + 1) = γ t)
    (V : (t : ℝ) → TangentSpace I (γ t)) (x : M) :
    chartCoords (I := I) x γ (fun s => V (s + 1))
      = fun s => chartCoords (I := I) x γ V (s + 1) := by
  funext s
  show (trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ (γ s) (V (s + 1))
    = (trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ (γ (s + 1)) (V (s + 1))
  rw [hper s]

/-- The chart coordinates of the field shifted by `-1` are the shifted chart coordinates. -/
theorem chartCoords_shift_minus (hper : ∀ t : ℝ, γ (t + 1) = γ t)
    (V : (t : ℝ) → TangentSpace I (γ t)) (x : M) :
    chartCoords (I := I) x γ (fun s => V (s - 1))
      = fun s => chartCoords (I := I) x γ V (s - 1) := by
  funext s
  show (trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ (γ s) (V (s - 1))
    = (trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ (γ (s - 1)) (V (s - 1))
  have h := hper (s - 1)
  simp only [sub_add_cancel] at h
  rw [h]

/-- **Shift lemma (`SmoothAlongAt`, `+1`).** -/
theorem smoothAlongAt_shift_one (hper : ∀ t : ℝ, γ (t + 1) = γ t)
    {V : (t : ℝ) → TangentSpace I (γ t)} {t : ℝ}
    (h : SmoothAlongAt (I := I) γ V (t + 1)) :
    SmoothAlongAt (I := I) γ (fun s => V (s + 1)) t := by
  obtain ⟨U, hUo, htU, hUsrc, hUcd⟩ := h
  refine ⟨{s : ℝ | s + 1 ∈ U}, ?_, ?_, ?_, ?_⟩
  · exact hUo.preimage (continuous_id.add continuous_const)
  · show t + 1 ∈ U; exact htU
  · intro s hs
    have h2 : γ (t + 1) = γ t := hper t
    rw [← h2, ← hper s]
    exact hUsrc (s + 1) hs
  · have h1 : (fun s : ℝ => chartCoords (I := I) (γ (t + 1)) γ V (s + 1))
        = fun s => chartCoords (I := I) (γ t) γ V (s + 1) := by
      rw [hper t]
    have h2 : (fun s : ℝ => chartCoords (I := I) (γ t) γ V (s + 1))
        = chartCoords (I := I) (γ t) γ (fun s => V (s + 1)) :=
      (chartCoords_shift_one (I := I) hper V (γ t)).symm
    have h3 : ContDiffOn ℝ ∞ (fun s : ℝ => chartCoords (I := I) (γ (t + 1)) γ V (s + 1))
        {s : ℝ | s + 1 ∈ U} :=
      (hUcd.comp (contDiffOn_id.add contDiffOn_const) (fun s hs => hs))
    rw [h1, h2] at h3
    exact h3

/-- **Shift lemma (`covAlong`, `+1`)**`, proved through the *intrinsic* characterisation
`covAlong_eq_cov` (which avoids the chart-velocity bookkeeping of the `DtQ` formula). -/
theorem covAlong_shift_one (htor : cov.torsion = 0)
    (hper : ∀ t : ℝ, γ (t + 1) = γ t) (hγsm : ContMDiff 𝓘(ℝ) I ∞ γ)
    (hne : ∀ t : ℝ, curveVelocity (I := I) γ t ≠ 0)
    {V : (t : ℝ) → TangentSpace I (γ t)} {t : ℝ}
    (hV : SmoothAlongAt (I := I) γ V (t + 1))
    (hVs : SmoothAlongAt (I := I) γ (fun s => V (s + 1)) t) :
    covAlong (γ := γ) cov (fun s => V (s + 1)) t = covAlong (γ := γ) cov V (t + 1) := by
  have hγ1 : ∀ u : ℝ, ContMDiffOn 𝓘(ℝ) I ∞ γ (Set.Ioo (u - 1) (u + 1)) :=
    fun u => (hγsm.contMDiffOn).mono (Set.subset_univ _)
  obtain ⟨𝒱, h𝒱sm, h𝒱ev⟩ :=
    Submission.JacobiGlobal.exists_section_of_smoothAlongAt (I := I) (hγ1 (t + 1)) (hne (t + 1)) hV
  have h𝒱ev' : ∀ᶠ s in 𝓝 t, 𝒱 (γ s) = V (s + 1) := by
    have hcont : Tendsto (fun s : ℝ => s + 1) (𝓝 t) (𝓝 (t + 1)) := tendsto_id.add_const 1
    filter_upwards [hcont.eventually h𝒱ev] with s hs
    have hs' : γ s = γ (s + 1) := (hper s).symm
    rw [hs', hs]
  rw [Submission.JacobiGlobal.covAlong_eq_cov (cov := cov) htor (hγ1 t) (hne t) hVs h𝒱sm h𝒱ev',
    Submission.JacobiGlobal.covAlong_eq_cov (cov := cov) htor (hγ1 (t + 1)) (hne (t + 1)) hV
      h𝒱sm h𝒱ev]
  have hpt : γ (t + 1) = γ t := hper t
  have hvel : curveVelocity (I := I) γ (t + 1) = curveVelocity (I := I) γ t :=
    curveVelocity_periodic (I := I) hper hγsm t
  rw [hpt, hvel]

/-- **Shift lemma (`SmoothAlongAt`, `-1`).** -/
theorem smoothAlongAt_shift_minus (hper : ∀ t : ℝ, γ (t + 1) = γ t)
    {V : (t : ℝ) → TangentSpace I (γ t)} {t : ℝ}
    (h : SmoothAlongAt (I := I) γ V (t - 1)) :
    SmoothAlongAt (I := I) γ (fun s => V (s - 1)) t := by
  obtain ⟨U, hUo, htU, hUsrc, hUcd⟩ := h
  refine ⟨{s : ℝ | s - 1 ∈ U}, ?_, ?_, ?_, ?_⟩
  · exact hUo.preimage (continuous_id.sub continuous_const)
  · show t - 1 ∈ U; exact htU
  · intro s hs
    have h2 : γ (t - 1) = γ t := (by
      have hh := hper (t - 1); simpa using hh : γ t = γ (t - 1)).symm
    have h3 : γ s = γ (s - 1) :=
      (by have hh := hper (s - 1); simpa using hh : γ s = γ (s - 1))
    rw [h3, ← h2]
    exact hUsrc (s - 1) hs
  · have h1 : (fun s : ℝ => chartCoords (I := I) (γ (t - 1)) γ V (s - 1))
        = fun s => chartCoords (I := I) (γ t) γ V (s - 1) := by
      have hh : γ (t - 1) = γ t := (by
        have h2 := hper (t - 1); simpa using h2 : γ t = γ (t - 1)).symm
      rw [hh]
    have h2 : (fun s : ℝ => chartCoords (I := I) (γ t) γ V (s - 1))
        = chartCoords (I := I) (γ t) γ (fun s => V (s - 1)) :=
      (chartCoords_shift_minus (I := I) hper V (γ t)).symm
    have h3 : ContDiffOn ℝ ∞ (fun s : ℝ => chartCoords (I := I) (γ (t - 1)) γ V (s - 1))
        {s : ℝ | s - 1 ∈ U} :=
      (hUcd.comp (contDiffOn_id.sub contDiffOn_const) (fun s hs => hs))
    rw [h1, h2] at h3
    exact h3

/-- **Shift lemma (`covAlong`, `-1`)**. -/
theorem covAlong_shift_minus (htor : cov.torsion = 0)
    (hper : ∀ t : ℝ, γ (t + 1) = γ t) (hγsm : ContMDiff 𝓘(ℝ) I ∞ γ)
    (hne : ∀ t : ℝ, curveVelocity (I := I) γ t ≠ 0)
    {V : (t : ℝ) → TangentSpace I (γ t)} {t : ℝ}
    (hV : SmoothAlongAt (I := I) γ V (t - 1))
    (hVs : SmoothAlongAt (I := I) γ (fun s => V (s - 1)) t) :
    covAlong (γ := γ) cov (fun s => V (s - 1)) t = covAlong (γ := γ) cov V (t - 1) := by
  have hγ1 : ∀ u : ℝ, ContMDiffOn 𝓘(ℝ) I ∞ γ (Set.Ioo (u - 1) (u + 1)) :=
    fun u => (hγsm.contMDiffOn).mono (Set.subset_univ _)
  obtain ⟨𝒱, h𝒱sm, h𝒱ev⟩ :=
    Submission.JacobiGlobal.exists_section_of_smoothAlongAt (I := I) (hγ1 (t - 1)) (hne (t - 1)) hV
  have h𝒱ev' : ∀ᶠ s in 𝓝 t, 𝒱 (γ s) = V (s - 1) := by
    have hcont : Tendsto (fun s : ℝ => s - 1) (𝓝 t) (𝓝 (t - 1)) := tendsto_id.sub_const 1
    filter_upwards [hcont.eventually h𝒱ev] with s hs
    have hs' : γ s = γ (s - 1) := (by have h := hper (s - 1); simpa using h : γ s = γ (s - 1))
    rw [hs', hs]
  rw [Submission.JacobiGlobal.covAlong_eq_cov (cov := cov) htor (hγ1 t) (hne t) hVs h𝒱sm h𝒱ev',
    Submission.JacobiGlobal.covAlong_eq_cov (cov := cov) htor (hγ1 (t - 1)) (hne (t - 1)) hV
      h𝒱sm h𝒱ev]
  have hpt : γ (t - 1) = γ t :=
    (by have h := hper (t - 1); simpa using h : γ t = γ (t - 1)).symm
  have hvel : curveVelocity (I := I) γ (t - 1) = curveVelocity (I := I) γ t := by
    have h := curveVelocity_periodic (I := I) hper hγsm (t - 1)
    rw [sub_add_cancel] at h
    exact h.symm
  rw [hpt, hvel]

/-! ## §3 The germ of the global parallel field at the two ends of a cover -/

/-- **The germ of `parallelFieldR` at the right end of the cover is the last piece field.** -/
theorem parallelFieldR_germ_last {a b : ℝ} (htor : cov.torsion = 0)
    (C : GeodesicCover cov γ a b) (hN : 0 < C.N) (v₀ : E) :
    parallelFieldR (cov := cov) (γ := γ) (a := a) (b := b) htor C hN v₀ =ᶠ[𝓝 (C.c C.N)]
      pieceFieldR (cov := cov) (γ := γ) (a := a) (b := b) htor C (C.N - 1)
        (datumAtR (cov := cov) htor C v₀ (C.N - 1)) := by
  have hlt : C.c (C.N - 1) < C.c C.N := c_mono_lt (cov := cov) C (by omega) le_rfl
  refine Filter.eventually_of_mem (isOpen_Ioo.mem_nhds (show C.c C.N ∈
    Ioo (C.c (C.N - 1)) (C.c C.N + 1) from ⟨hlt, by linarith⟩)) (fun s hs => ?_)
  have hk : C.N - 1 < C.N := by omega
  have hsub : C.N - 1 + 1 = C.N := Nat.sub_add_cancel hN
  show pieceFieldR (cov := cov) (γ := γ) (a := a) (b := b) htor C (kOf (cov := cov) C hN s)
      (datumAtR (cov := cov) htor C v₀ (kOf (cov := cov) C hN s)) s
    = pieceFieldR (cov := cov) (γ := γ) (a := a) (b := b) htor C (C.N - 1)
      (datumAtR (cov := cov) htor C v₀ (C.N - 1)) s
  rcases le_total s (C.c C.N) with hs' | hs'
  · rw [kOf_eq_of_mem (cov := cov) C hN (t := s) hk hs.1 (by rw [hsub]; exact hs')]
  · rw [kOf_eq_last (cov := cov) C hN hs.1]

/-- The chart coordinate `t ↦ (extChartAt I z) (γ t)` of a `1`-periodic curve is `1`-periodic. -/
theorem deriv_chartCoord_periodic (hper : ∀ t : ℝ, γ (t + 1) = γ t)
    (z : M) (t : ℝ) :
    deriv (fun s : ℝ => (extChartAt I z) (γ s)) (t + 1)
      = deriv (fun s : ℝ => (extChartAt I z) (γ s)) t := by
  have h1 : (fun s : ℝ => (extChartAt I z) (γ (s + 1))) = (fun s : ℝ => (extChartAt I z) (γ s)) := by
    funext s
    rw [hper s]
  rw [← deriv_comp_add_const (fun u : ℝ => (extChartAt I z) (γ u)) 1 t, h1]

/-- **Rewriting the argument of a field along `γ`.**  The types `TangentSpace I (γ t)` are all
definitionally `E`, so the argument of a field may be rewritten at the level of `E`. -/
theorem fieldArg_eq {V : (t : ℝ) → TangentSpace I (γ t)} {a b : ℝ} (h : a = b) :
    V a = V b := by
  change (show E from V a) = (show E from V b)
  exact congrArg (fun t : ℝ => (show E from V t)) h

/-- **`covAlong` only depends on the germ of the field.** -/
theorem covAlong_congr {V W : (t : ℝ) → TangentSpace I (γ t)} {t : ℝ}
    (htor : cov.torsion = 0)
    (hγ : ContMDiffOn 𝓘(ℝ) I ∞ γ (Ioo (t - 1) (t + 1)))
    (hne : curveVelocity (I := I) γ t ≠ 0)
    (hV : SmoothAlongAt (I := I) γ V t) (hW : SmoothAlongAt (I := I) γ W t)
    (h : V =ᶠ[𝓝 t] W) : covAlong cov V t = covAlong cov W t := by
  obtain ⟨𝒱, h𝒱sm, h𝒱ev⟩ :=
    Submission.JacobiGlobal.exists_section_of_smoothAlongAt (I := I) hγ hne hV
  have h𝒱ev' : ∀ᶠ s in 𝓝 t, 𝒱 (γ s) = W s := by
    filter_upwards [h𝒱ev, h] with s hs hs'
    rw [hs, hs']
  rw [Submission.JacobiGlobal.covAlong_eq_cov (cov := cov) htor hγ hne hV h𝒱sm h𝒱ev,
    Submission.JacobiGlobal.covAlong_eq_cov (cov := cov) htor hγ hne hW h𝒱sm h𝒱ev']

/-! ## §4 The periodic extension of the Synge field -/

/-- **The periodic extension of a parallel field with a periodic datum is smooth and parallel on
the window `[-1,2]`.**

This is the bridge between the two languages: `Submission.HolDet.exists_synge_field` produces a
parallel field `X` along a closed geodesic `γ` on the cover of the loop `[0,1]`, with
`X 1 = X 0`.  The shortening argument of `Submission.SyngeShorten` needs the field on the window
`Icc (-1) 2`, i.e. the *periodic extension* `pext X`.  The extension is automatic in the interior of
the three intervals `(-1,0)`, `(0,1)`, `(1,2)` (the shift lemmas above); at the two junctions
`s = 0` and `s = 1` the two one-sided pieces are the germ of the first and of the last room solution
of the cover, and the *uniqueness of the parallel field* (`ParallelRoom.eqOn_of_parallel`) shows that
the two room solutions agree on the overlap, so that `pext X` agrees with a single room solution near
each junction. -/
theorem pext_spec (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (hper : ∀ t : ℝ, γ (t + 1) = γ t) (hγsm : ContMDiff 𝓘(ℝ) I ∞ γ)
    (hne : ∀ t : ℝ, curveVelocity (I := I) γ t ≠ 0)
    (C : GeodesicCover cov γ 0 1) (hN : 0 < C.N) (v₀ : E)
    (hperX : parallelFieldR (cov := cov) htor C hN v₀ 1
      = parallelFieldR (cov := cov) htor C hN v₀ 0) :
    (∀ s ∈ Icc (-1) 2, SmoothAlongAt (I := I) γ
        (pext (I := I) (parallelFieldR (cov := cov) htor C hN v₀)) s) ∧
    (∀ s ∈ Icc (-1) 2, covAlong (γ := γ) cov
        (pext (I := I) (parallelFieldR (cov := cov) htor C hN v₀)) s = 0) := by
  classical
  set X : (t : ℝ) → TangentSpace I (γ t) := parallelFieldR (cov := cov) htor C hN v₀ with hXdef
  set U : (t : ℝ) → TangentSpace I (γ t) := pieceFieldR (cov := cov) htor C 0 v₀ with hUdef
  set W : (t : ℝ) → TangentSpace I (γ t) :=
    pieceFieldR (cov := cov) htor C (C.N - 1) (datumAtR (cov := cov) htor C v₀ (C.N - 1))
    with hWdef
  change (∀ s ∈ Icc (-1) 2, SmoothAlongAt (I := I) γ (pext (M := M) (γ := γ) (I := I) X) s) ∧
    (∀ s ∈ Icc (-1) 2, covAlong (γ := γ) cov (pext (M := M) (γ := γ) (I := I) X) s = 0)
  have hγ1 : ∀ t : ℝ, ContMDiffOn 𝓘(ℝ) I ∞ γ (Ioo (t - 1) (t + 1)) :=
    fun t => (hγsm.contMDiffOn).mono (Set.subset_univ _)
  have hkN : C.N - 1 < C.N := by omega
  have hc0 : C.c 0 = 0 := C.c_zero
  have hcN : C.c C.N = 1 := C.c_last
  -- the cover data on `[0,1]`
  have hX01 := parallelFieldR_spec (cov := cov) hmet htor C hN v₀
    (fun k hk t ht => hγ1 t) (fun k hk t ht => hne t)
  have hXs : ∀ t ∈ Icc (0:ℝ) 1, SmoothAlongAt (I := I) γ X t := fun t ht => hX01.1 t ht
  have hXpar : ∀ t ∈ Icc (0:ℝ) 1, covAlong cov X t = 0 := fun t ht => hX01.2 t ht
  -- the two germ facts at the two ends
  have hX0g : X =ᶠ[𝓝 0] U := by
    have h := parallelFieldR_eventuallyEq_piece_zero (cov := cov) (γ := γ) htor C hN v₀
    rw [hc0] at h
    exact h
  have hX1g : X =ᶠ[𝓝 1] W := by
    have h := parallelFieldR_germ_last (cov := cov) (γ := γ) htor C hN v₀
    rw [hcN] at h
    exact h
  -- the two room solutions meeting at the junction `0`
  have hU_sm : ∀ t ∈ Ioo (roomA C 0) (roomB C 0), SmoothAlongAt (I := I) γ U t :=
    fun t ht => smoothAlongAt_pieceFieldR (cov := cov) htor C hN v₀ ht
  have hU_par : ∀ t ∈ Ioo (roomA C 0) (roomB C 0), covAlong cov U t = 0 :=
    fun t ht => covAlong_eq_zero_of_germ (cov := cov) htor C hN v₀ ht (hγ1 t) (hne t)
      (hU_sm t ht) (Filter.EventuallyEq.refl _ _)
  have hW0_sm : ∀ t ∈ Ioo (roomA C (C.N - 1)) (roomB C (C.N - 1)),
      SmoothAlongAt (I := I) γ W t :=
    fun t ht => smoothAlongAt_pieceFieldR (cov := cov) htor C hkN
      (datumAtR (cov := cov) htor C v₀ (C.N - 1)) ht
  have hW0_par : ∀ t ∈ Ioo (roomA C (C.N - 1)) (roomB C (C.N - 1)), covAlong cov W t = 0 :=
    fun t ht => covAlong_eq_zero_of_germ (cov := cov) htor C hkN
      (datumAtR (cov := cov) htor C v₀ (C.N - 1)) ht (hγ1 t) (hne t) (hW0_sm t ht)
      (Filter.EventuallyEq.refl _ _)
  -- the shifted last room solution
  have hWsh_sm : ∀ t ∈ Ioo (roomA C (C.N - 1) - 1) (roomB C (C.N - 1) - 1),
      SmoothAlongAt (I := I) γ (fun s : ℝ => W (s + 1)) t := by
    intro t ht
    have h1 : t + 1 ∈ Ioo (roomA C (C.N - 1)) (roomB C (C.N - 1)) :=
      ⟨by linarith [ht.1], by linarith [ht.2]⟩
    exact smoothAlongAt_shift_one (I := I) hper (hW0_sm (t + 1) h1)
  have hWsh_par : ∀ t ∈ Ioo (roomA C (C.N - 1) - 1) (roomB C (C.N - 1) - 1),
      covAlong (γ := γ) cov (fun s : ℝ => W (s + 1)) t = 0 := by
    intro t ht
    have h1 : t + 1 ∈ Ioo (roomA C (C.N - 1)) (roomB C (C.N - 1)) :=
      ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hstep := covAlong_shift_one (cov := cov) htor hper hγsm hne (hW0_sm (t + 1) h1)
      (hWsh_sm t ht)
    exact hstep.trans (hW0_par (t + 1) h1)
  -- the overlap interval of the two room solutions
  have hα0 : max (roomA C 0) (roomA C (C.N - 1) - 1) < 0 := by
    refine max_lt ?_ ?_
    · have h1 : roomA C 0 < C.c 0 := roomA_lt_c C hN
      rw [hc0] at h1; exact h1
    · have h1 : roomA C (C.N - 1) < C.c (C.N - 1) := roomA_lt_c C hkN
      have h2 : C.c (C.N - 1) < 1 := by
        have h3 : C.c (C.N - 1) < C.c C.N := c_mono_lt C (by omega) le_rfl
        rw [hcN] at h3; exact h3
      linarith
  have h0_roomB : (0 : ℝ) < roomB C 0 := by
    have h1 : C.c 1 < roomB C 0 := c_succ_lt_roomB C hN
    have h2 : C.c 0 < C.c 1 := C.mono 0 hN
    rw [hc0] at h2
    linarith
  have h0β : (0 : ℝ) < min (roomB C 0) (roomB C (C.N - 1) - 1) := by
    refine lt_min h0_roomB ?_
    have h1 : C.c C.N < roomB C (C.N - 1) := by
      have h := c_succ_lt_roomB C hkN
      rwa [Nat.sub_add_cancel hN] at h
    rw [hcN] at h1; linarith
  have hmem0 : (0 : ℝ) ∈ Ioo (max (roomA C 0) (roomA C (C.N - 1) - 1))
      (min (roomB C 0) (roomB C (C.N - 1) - 1)) :=
    ⟨hα0, h0β⟩
  -- the two room solutions agree on the overlap
  have hU_sm' : ∀ t ∈ Ioo (max (roomA C 0) (roomA C (C.N - 1) - 1))
      (min (roomB C 0) (roomB C (C.N - 1) - 1)), SmoothAlongAt (I := I) γ U t :=
    fun t ht => hU_sm t ⟨lt_of_le_of_lt (le_max_left _ _) ht.1,
      lt_of_lt_of_le ht.2 (min_le_left _ _)⟩
  have hU_par' : ∀ t ∈ Ioo (max (roomA C 0) (roomA C (C.N - 1) - 1))
      (min (roomB C 0) (roomB C (C.N - 1) - 1)), covAlong cov U t = 0 :=
    fun t ht => hU_par t ⟨lt_of_le_of_lt (le_max_left _ _) ht.1,
      lt_of_lt_of_le ht.2 (min_le_left _ _)⟩
  have hWsh_sm' : ∀ t ∈ Ioo (max (roomA C 0) (roomA C (C.N - 1) - 1))
      (min (roomB C 0) (roomB C (C.N - 1) - 1)),
      SmoothAlongAt (I := I) γ (fun s : ℝ => W (s + 1)) t :=
    fun t ht => hWsh_sm t ⟨lt_of_le_of_lt (le_max_right _ _) ht.1,
      lt_of_lt_of_le ht.2 (min_le_right _ _)⟩
  have hWsh_par' : ∀ t ∈ Ioo (max (roomA C 0) (roomA C (C.N - 1) - 1))
      (min (roomB C 0) (roomB C (C.N - 1) - 1)),
      covAlong (γ := γ) cov (fun s : ℝ => W (s + 1)) t = 0 :=
    fun t ht => hWsh_par t ⟨lt_of_le_of_lt (le_max_right _ _) ht.1,
      lt_of_lt_of_le ht.2 (min_le_right _ _)⟩
  have hagree : U 0 = (fun s : ℝ => W (s + 1)) 0 := by
    change U 0 = W (0 + 1)
    have h1 : U 0 = X 0 := (hX0g.eq_of_nhds).symm
    have h2 : X 1 = W 1 := hX1g.eq_of_nhds
    rw [show (0 : ℝ) + 1 = 1 from by norm_num]
    exact h1.trans (hperX.symm.trans h2)
  have hUW : ∀ s ∈ Ioo (max (roomA C 0) (roomA C (C.N - 1) - 1))
      (min (roomB C 0) (roomB C (C.N - 1) - 1)), U s = (fun s : ℝ => W (s + 1)) s :=
    eqOn_of_parallel (cov := cov) (γ := γ) hmet htor (lt_trans hα0 h0β) hmem0
      (fun t ht => hγ1 t) (fun t ht => hne t) hU_sm' hWsh_sm' hU_par' hWsh_par' hagree
  -- shifting eventual statements across the junctions
  have htend1 : Tendsto (fun s : ℝ => s + 1) (𝓝 (0 : ℝ)) (𝓝 (1 : ℝ)) := by
    have h : Tendsto (fun s : ℝ => s + 1) (𝓝 (0 : ℝ)) (𝓝 ((0 : ℝ) + 1)) :=
      tendsto_id.add_const 1
    rwa [show (0 : ℝ) + 1 = 1 from by norm_num] at h
  have htend0 : Tendsto (fun s : ℝ => s - 1) (𝓝 (1 : ℝ)) (𝓝 (0 : ℝ)) := by
    have h : Tendsto (fun s : ℝ => s - 1) (𝓝 (1 : ℝ)) (𝓝 ((1 : ℝ) - 1)) :=
      tendsto_id.sub_const 1
    rwa [show (1 : ℝ) - 1 = 0 from by norm_num] at h
  -- the germ of `pext X` at the left junction
  have hpext0 : pext (M := M) (γ := γ) (I := I) X =ᶠ[𝓝 0] U := by
    have hmem : ∀ᶠ s in 𝓝 (0 : ℝ),
        s ∈ Ioo (max (roomA C 0) (roomA C (C.N - 1) - 1))
          (min (min (roomB C 0) (roomB C (C.N - 1) - 1)) 1) :=
      isOpen_Ioo.mem_nhds ⟨hα0, lt_min h0β zero_lt_one⟩
    filter_upwards [hmem, hX0g, htend1.eventually hX1g] with s hs hXs hXsh
    have hsα : s ∈ Ioo (max (roomA C 0) (roomA C (C.N - 1) - 1))
        (min (roomB C 0) (roomB C (C.N - 1) - 1)) :=
      ⟨hs.1, lt_of_lt_of_le hs.2 (min_le_left _ _)⟩
    rcases lt_trichotomy s 0 with hlt | heqs | hgt
    · rw [pext_of_neg hlt, hXsh]
      exact (hUW s hsα).symm
    · subst heqs
      rw [pext_of_mem le_rfl zero_le_one, hXs]
    · rw [pext_of_mem hgt.le (le_of_lt (lt_of_lt_of_le hs.2 (min_le_right _ _))), hXs]
  -- the germ of `pext X` at the right junction
  have hpext1 : pext (M := M) (γ := γ) (I := I) X =ᶠ[𝓝 1] W := by
    have hmem : ∀ᶠ s in 𝓝 (1 : ℝ),
        s ∈ Ioo (max (max (roomA C 0) (roomA C (C.N - 1) - 1) + 1) 0)
          (min (roomB C 0) (roomB C (C.N - 1) - 1) + 1) :=
      isOpen_Ioo.mem_nhds ⟨max_lt (by linarith [hα0]) zero_lt_one, by linarith [h0β]⟩
    filter_upwards [hmem, hX1g, htend0.eventually hX0g] with s hs hXs hXsm
    rcases le_or_gt s 1 with hle | hlt
    · have h0s : 0 ≤ s := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hs.1)
      rw [pext_of_mem h0s hle, hXs]
    · rw [pext_of_one_lt hlt, hXsm]
      have hsα : s - 1 ∈ Ioo (max (roomA C 0) (roomA C (C.N - 1) - 1))
          (min (roomB C 0) (roomB C (C.N - 1) - 1)) :=
        ⟨by linarith [lt_of_le_of_lt (le_max_left _ _) hs.1], by linarith [hs.2]⟩
      exact (hUW (s - 1) hsα).trans
        (fieldArg_eq (V := W) (by ring : s - 1 + 1 = s))
  -- the room conditions at the two junctions
  have h0U : (0 : ℝ) ∈ Ioo (roomA C 0) (roomB C 0) := by
    refine ⟨?_, h0_roomB⟩
    have h1 : roomA C 0 < C.c 0 := roomA_lt_c C hN
    rw [hc0] at h1; exact h1
  have h1W : (1 : ℝ) ∈ Ioo (roomA C (C.N - 1)) (roomB C (C.N - 1)) := by
    refine ⟨?_, ?_⟩
    · have h3 : C.c (C.N - 1) < C.c C.N := c_mono_lt C (by omega) le_rfl
      have h4 : roomA C (C.N - 1) < C.c (C.N - 1) := roomA_lt_c C hkN
      rw [hcN] at h3; linarith
    · have h := c_succ_lt_roomB C hkN
      rwa [Nat.sub_add_cancel hN, hcN] at h
  have hsmooth : ∀ s ∈ Icc (-1) 2, SmoothAlongAt (I := I) γ (pext (M := M) (γ := γ) (I := I) X) s := by
    intro s hs
    rcases lt_trichotomy s 0 with hlt | heqs | hgt
    · have hs' : s + 1 ∈ Icc (0:ℝ) 1 := ⟨by linarith [hs.1], by linarith⟩
      refine SmoothAlongAt_congr (smoothAlongAt_shift_one (I := I) hper (hXs (s + 1) hs')) ?_
      refine Filter.eventually_of_mem (isOpen_Ioo.mem_nhds (show s ∈ Ioo (s - 1) 0 from
        ⟨by linarith, hlt⟩)) (fun u hu => ?_)
      exact (pext_of_neg hu.2).symm
    · rw [heqs]
      exact SmoothAlongAt_congr (smoothAlongAt_pieceFieldR (cov := cov) htor C hN v₀ h0U)
        hpext0.symm
    · rcases lt_trichotomy s 1 with hlt1 | heqs1 | hgt1
      · have hs' : s ∈ Icc (0:ℝ) 1 := ⟨hgt.le, hlt1.le⟩
        refine SmoothAlongAt_congr (hXs s hs') ?_
        refine Filter.eventually_of_mem (isOpen_Ioo.mem_nhds (show s ∈ Ioo 0 1 from
          ⟨hgt, hlt1⟩)) (fun u hu => ?_)
        exact (pext_of_mem hu.1.le hu.2.le).symm
      · rw [heqs1]
        exact SmoothAlongAt_congr (smoothAlongAt_pieceFieldR (cov := cov) htor C hkN
          (datumAtR (cov := cov) htor C v₀ (C.N - 1)) h1W) hpext1.symm
      · have hs' : s - 1 ∈ Icc (0:ℝ) 1 := ⟨by linarith [hgt1.le], by linarith [hs.2]⟩
        refine SmoothAlongAt_congr (smoothAlongAt_shift_minus (I := I) hper (hXs (s - 1) hs')) ?_
        refine Filter.eventually_of_mem (isOpen_Ioo.mem_nhds (show s ∈ Ioo 1 (s + 1) from
          ⟨hgt1, by linarith⟩)) (fun u hu => ?_)
        exact (pext_of_one_lt hu.1).symm
  refine ⟨hsmooth, fun s hs => ?_⟩
  rcases lt_trichotomy s 0 with hlt | heqs | hgt
  · -- `s < 0`: the shifted field
    have hs' : s + 1 ∈ Icc (0:ℝ) 1 := ⟨by linarith [hs.1], by linarith⟩
    have hshift : SmoothAlongAt (I := I) γ (fun u : ℝ => X (u + 1)) s :=
      smoothAlongAt_shift_one (I := I) hper (hXs (s + 1) hs')
    have hgerm : pext (M := M) (γ := γ) (I := I) X =ᶠ[𝓝 s] (fun u : ℝ => X (u + 1)) := by
      refine Filter.eventually_of_mem (isOpen_Ioo.mem_nhds (show s ∈ Ioo (s - 1) 0 from
        ⟨by linarith, hlt⟩)) (fun u hu => ?_)
      exact pext_of_neg hu.2
    rw [covAlong_congr (cov := cov) (γ := γ) (V := pext (M := M) (γ := γ) (I := I) X)
        (W := fun u : ℝ => X (u + 1)) htor (hγ1 s) (hne s) (hsmooth s hs) hshift hgerm,
      covAlong_shift_one (cov := cov) htor hper hγsm hne (hXs (s + 1) hs') hshift]
    exact hXpar (s + 1) hs'
  · subst heqs
    exact covAlong_eq_zero_of_germ (cov := cov) htor C hN v₀ h0U (hγ1 0) (hne 0)
      (hsmooth 0 hs) hpext0
  · rcases lt_trichotomy s 1 with hlt1 | heqs1 | hgt1
    · have hs' : s ∈ Icc (0:ℝ) 1 := ⟨hgt.le, hlt1.le⟩
      have hgerm : pext (M := M) (γ := γ) (I := I) X =ᶠ[𝓝 s] X := by
        refine Filter.eventually_of_mem (isOpen_Ioo.mem_nhds (show s ∈ Ioo 0 1 from
          ⟨hgt, hlt1⟩)) (fun u hu => ?_)
        exact pext_of_mem hu.1.le hu.2.le
      rw [covAlong_congr (cov := cov) (γ := γ) (V := pext (M := M) (γ := γ) (I := I) X)
        (W := X) htor (hγ1 s) (hne s) (hsmooth s hs) (hXs s hs') hgerm]
      exact hXpar s hs'
    · rw [heqs1]
      exact covAlong_eq_zero_of_germ (cov := cov) htor C hkN
        (datumAtR (cov := cov) htor C v₀ (C.N - 1)) h1W (hγ1 1) (hne 1)
        (hsmooth 1 ⟨by norm_num, by norm_num⟩) hpext1
    · have hs' : s - 1 ∈ Icc (0:ℝ) 1 := ⟨by linarith [hgt1.le], by linarith [hs.2]⟩
      have hshift : SmoothAlongAt (I := I) γ (fun u : ℝ => X (u - 1)) s :=
        smoothAlongAt_shift_minus (I := I) hper (hXs (s - 1) hs')
      have hgerm : pext (M := M) (γ := γ) (I := I) X =ᶠ[𝓝 s] (fun u : ℝ => X (u - 1)) := by
        refine Filter.eventually_of_mem (isOpen_Ioo.mem_nhds (show s ∈ Ioo 1 (s + 1) from
          ⟨hgt1, by linarith⟩)) (fun u hu => ?_)
        exact pext_of_one_lt hu.1
      rw [covAlong_congr (cov := cov) (γ := γ) (V := pext (M := M) (γ := γ) (I := I) X)
          (W := fun u : ℝ => X (u - 1)) htor (hγ1 s) (hne s) (hsmooth s hs) hshift hgerm,
        covAlong_shift_minus (cov := cov) htor hper hγsm hne (hXs (s - 1) hs') hshift]
      exact hXpar (s - 1) hs'

/-- **Synge's shortening step, in the form needed for Klingenberg's even-dimensional estimate.**

On a `1`-periodic unit-speed geodesic `γ` whose chart loop has `loopSign = 1` (which for a simply
connected manifold is automatic, see `Submission.OrientSign`), on an even-dimensional manifold, and
with a positive lower bound `δ > 0` for the sectional curvature, there is a **periodic, unit, normal
parallel field `Z`** along `γ` and a scaling `d > 0` such that the closed curves
`t ↦ GExp (γ t) (σ • (d • Z t))` are **shorter than `γ`** for all small `σ ≥ 0` (or all small
`σ ≤ 0`).

The field `Z` is the *periodic extension* of the Synge field produced by
`Submission.HolDet.exists_synge_field` (the fixed vector of the normal holonomy, which exists because
the holonomy lies in `SO(n-1)` with `n-1` odd), extended to the window `[-1,2]` by
`Submission.SyngeWindow.pext_spec`.  The shortening itself is
`Submission.SyngeShorten.exists_shorter_closed_curve`. -/
theorem exists_shorter_closed_curve_of_synge (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {γ : ℝ → M} (hper : ∀ t : ℝ, γ (t + 1) = γ t) (hγsm : ContMDiff 𝓘(ℝ) I ∞ γ)
    (hgeo : ∀ t : ℝ, IsGeodesicAt (I := I) cov γ t)
    (hnev : ∀ t : ℝ, curveVelocity (I := I) γ t ≠ 0)
    (hunit : ∀ t ∈ Icc (0 : ℝ) 1, curveSpeed (I := I) γ t = 1)
    {P : Partition 0 1} {z : ℕ → M} (hP : IsChartLoop (H := H) P γ z)
    (hloopSign : loopSignOf (I := I) P γ z = 1) (hEven : Even (Module.finrank ℝ E))
    {δ : ℝ} (hδ : 0 < δ)
    (hcurv : ∀ t ∈ Icc (0 : ℝ) 1, ∀ u v : TangentSpace I (γ t), ‖u‖ = 1 → ‖v‖ = 1 →
      inner ℝ u v = 0 → δ ≤ inner ℝ (curvVec cov (γ t) u v v) u) :
    ∃ (Z : (t : ℝ) → TangentSpace I (γ t)) (d : ℝ), 0 < d ∧ Z 1 = Z 0 ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ‖Z t‖ = 1) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, inner ℝ (Z t) (curveVelocity (I := I) γ t) = 0) ∧
      (∀ s ∈ Icc ((0 : ℝ) - 1) ((1 : ℝ) + 1), SmoothAlongAt (I := I) γ Z s) ∧
      (∀ s ∈ Icc ((0 : ℝ) - 1) ((1 : ℝ) + 1), covAlong (γ := γ) cov Z s = 0) ∧
      (((∀ᶠ σ in 𝓝[>] (0 : ℝ),
          curveLength (I := I) (fun t : ℝ => GExp (cov := cov) hmet (γ t) (σ • (d • Z t))) 0 1 < 1 ∧
          GExp (cov := cov) hmet (γ 1) (σ • (d • Z 1))
            = GExp (cov := cov) hmet (γ 0) (σ • (d • Z 0))) ∨
        (∀ᶠ σ in 𝓝[<] (0 : ℝ),
          curveLength (I := I) (fun t : ℝ => GExp (cov := cov) hmet (γ t) (σ • (d • Z t))) 0 1 < 1 ∧
          GExp (cov := cov) hmet (γ 1) (σ • (d • Z 1))
            = GExp (cov := cov) hmet (γ 0) (σ • (d • Z 0))))) := by
  classical
  have hloop : γ (P.t P.N) = γ (P.t 0) := by
    rw [P.t_last, P.t_zero]
    simpa using hper 0
  have hvelper : deriv (Submission.HolDet.coordC (I := I) (z := z) (γ := γ) P.N) (P.t P.N)
      = deriv (Submission.HolDet.coordC (I := I) (z := z) (γ := γ) 0) (P.t 0) := by
    have h1 : Submission.HolDet.coordC (I := I) (z := z) (γ := γ) P.N
        = Submission.HolDet.coordC (I := I) (z := z) (γ := γ) 0 := by
      funext t
      show (extChartAt I (z P.N)) (γ t) = (extChartAt I (z 0)) (γ t)
      rw [hP.2.2]
    rw [h1, P.t_last, P.t_zero]
    show deriv (fun s : ℝ => (extChartAt I (z 0)) (γ s)) 1
      = deriv (fun s : ℝ => (extChartAt I (z 0)) (γ s)) 0
    simpa using deriv_chartCoord_periodic (I := I) hper (z 0) 0
  obtain ⟨C, hN, v, hCN, hCc, hCx, hv0, hXs, hXpar, hXper, hX1, hXnorm⟩ :=
    Submission.HolDet.exists_synge_field (cov := cov) hmet htor hγsm hgeo hnev hP hloop hvelper
      hloopSign hEven
  -- the cover, with the endpoints `0` and `1`
  have hC0 : C.c 0 = 0 := by rw [hCc, P.t_zero]
  have hCN1 : C.c C.N = 1 := by rw [hCc, hCN, P.t_last]
  let Cs : GeodesicCover cov γ 0 1 :=
    { N := C.N, c := C.c, x := C.x, A := C.A, B := C.B, c_zero := hC0, c_last := hCN1,
      mono := C.mono, room := C.room, src := C.src, ode := C.ode }
  have hCsN : Cs.N = C.N := rfl
  -- the periodicity of the datum, in the `0`/`1` language
  have hperX : parallelFieldR (cov := cov) htor Cs hN v 1
      = parallelFieldR (cov := cov) htor Cs hN v 0 := by
    have h1 : parallelFieldR (cov := cov) htor Cs hN v 1
        = parallelFieldR (cov := cov) htor Cs hN v (C.c C.N) :=
      (fieldArg_eq (V := parallelFieldR (cov := cov) htor Cs hN v) hCN1).symm
    have h2 : parallelFieldR (cov := cov) htor Cs hN v (C.c 0)
        = parallelFieldR (cov := cov) htor Cs hN v 0 :=
      fieldArg_eq (V := parallelFieldR (cov := cov) htor Cs hN v) hC0
    exact h1.trans (hXper.trans h2)
  -- the two facts on `[0,1]`, in the language of `Cs`
  have hX1' : ∀ t ∈ Icc (0 : ℝ) 1, ‖parallelFieldR (cov := cov) htor Cs hN v t‖ = 1 := by
    rw [hC0, hCN1] at hX1
    intro t ht
    exact hX1 t ht
  have hXnorm' : ∀ t ∈ Icc (0 : ℝ) 1,
      inner ℝ (parallelFieldR (cov := cov) htor Cs hN v t) (curveVelocity (I := I) γ t) = 0 := by
    rw [hC0, hCN1] at hXnorm
    intro t ht
    exact hXnorm t ht
  -- the periodic extension
  have hspec := pext_spec (cov := cov) (γ := γ) hmet htor hper hγsm hnev Cs hN v hperX
  have hZper : pext (M := M) (γ := γ) (I := I) (parallelFieldR (cov := cov) htor Cs hN v) 1
      = pext (M := M) (γ := γ) (I := I) (parallelFieldR (cov := cov) htor Cs hN v) 0 := by
    rw [pext_of_mem (I := I) (X := parallelFieldR (cov := cov) htor Cs hN v) zero_le_one le_rfl,
      pext_of_mem (I := I) (X := parallelFieldR (cov := cov) htor Cs hN v) le_rfl zero_le_one]
    exact hperX
  have hZ1 : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖pext (M := M) (γ := γ) (I := I) (parallelFieldR (cov := cov) htor Cs hN v) t‖ = 1 := by
    intro t ht
    rw [pext_of_mem (I := I) (X := parallelFieldR (cov := cov) htor Cs hN v) ht.1 ht.2]
    exact hX1' t ht
  have hZnorm : ∀ t ∈ Icc (0 : ℝ) 1,
      inner ℝ (pext (M := M) (γ := γ) (I := I) (parallelFieldR (cov := cov) htor Cs hN v) t)
        (curveVelocity (I := I) γ t) = 0 := by
    intro t ht
    rw [pext_of_mem (I := I) (X := parallelFieldR (cov := cov) htor Cs hN v) ht.1 ht.2]
    exact hXnorm' t ht
  have hZsm : ∀ s ∈ Icc ((0 : ℝ) - 1) ((1 : ℝ) + 1),
      SmoothAlongAt (I := I) γ
        (pext (M := M) (γ := γ) (I := I) (parallelFieldR (cov := cov) htor Cs hN v)) s :=
    fun s hs => hspec.1 s (by
      rw [Set.mem_Icc] at hs ⊢; exact ⟨by linarith [hs.1], by linarith [hs.2]⟩)
  have hZpar : ∀ s ∈ Icc ((0 : ℝ) - 1) ((1 : ℝ) + 1),
      covAlong (γ := γ) cov
        (pext (M := M) (γ := γ) (I := I) (parallelFieldR (cov := cov) htor Cs hN v)) s = 0 :=
    fun s hs => hspec.2 s (by
      rw [Set.mem_Icc] at hs ⊢; exact ⟨by linarith [hs.1], by linarith [hs.2]⟩)
  -- the shortening
  obtain ⟨d, hdpos, hd⟩ := Submission.SyngeShorten.exists_shorter_closed_curve (cov := cov) hmet htor
    hγsm hgeo hnev (by norm_num : (0 : ℝ) < 1) (by simpa using hper 0) hunit
    hZsm hZpar hZper hZ1 hZnorm hδ hcurv
  exact ⟨_, d, hdpos, hZper, hZ1, hZnorm, hZsm, hZpar, hd⟩

end

end Submission.SyngeWindow
