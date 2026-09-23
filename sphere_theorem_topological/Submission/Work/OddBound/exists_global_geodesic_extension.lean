import Mathlib
import Submission.Work.OddBound.RayKit
import Submission.BrokenLength

namespace Work.OddBound

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory Interval
open Submission.Geodesic Submission.GlobalExp Submission.Length Submission.JacobiGlobal

/-!
# Extending a geodesic segment on a compact manifold to a global geodesic

On a compact Riemannian manifold (here: `[CompactSpace M]` with a complete model space `E` and a
smooth, metric-compatible covariant derivative `cov`) every geodesic segment extends to a geodesic
defined for all time.  Concretely, if `γ` is `C^∞` on `[a,b]`, satisfies the geodesic equation at
every interior time and has non-vanishing velocity there, then there is a globally defined `C^∞`
geodesic `γ' : ℝ → M` with non-vanishing velocity everywhere which agrees with `γ` on `[a,b]`.

The construction is the classical one.  Pick an interior time `t₀ ∈ (a,b)` and let `x = γ t₀`,
`v = γ̇(t₀) ≠ 0`.  The *global exponential ray*

`γ' t = GExp cov hmet x ((t - t₀) • v)`

is `C^∞` on `ℝ` (`Submission.ConjEnergy.contMDiff_GExp_smul`), satisfies the geodesic equation at
every time (`Submission.GExpRayZero.isGeodesicAt_GExp_smul_all`) and never has vanishing velocity
(`Submission.RayChart.curveVelocity_GExp_ne_zero`), all after time-translation
(`Submission.GeodesicGlobal2.isGeodesicAt_comp_sub`, `…curveVelocity_comp_sub`).  Its velocity at
`t₀` is `v` (`Submission.GExpVelocity.curveVelocity_GExp_smul_zero`), so by the uniqueness theorem
for geodesics with the same initial data (`Submission.GlobalExp.eqOn_Ioo_of_isGeodesicAt_of_eq`) it
agrees with `γ` on `(a,b)`; continuity extends the agreement to `[a,b]`.
-/

theorem exists_global_geodesic_extension
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov)
    {a b : ℝ} (hab : a < b) {γ : ℝ → M}
    (hsm : ContMDiffOn 𝓘(ℝ) I ∞ γ (Set.Icc a b))
    (hgeo : ∀ t ∈ Set.Ioo a b, Submission.Geodesic.IsGeodesicAt (I := I) cov γ t)
    (hne : ∀ t ∈ Set.Ioo a b, Submission.Geodesic.curveVelocity (I := I) γ t ≠ 0)
    (hunit : ∀ t ∈ Set.Icc a b, Submission.Length.curveSpeed (I := I) γ t = 1) :
    ∃ γ' : ℝ → M, ContMDiff 𝓘(ℝ) I ∞ γ' ∧
      (∀ t : ℝ, Submission.Geodesic.IsGeodesicAt (I := I) cov γ' t) ∧
      (∀ t : ℝ, Submission.Geodesic.curveVelocity (I := I) γ' t ≠ 0) ∧
      (∀ t : ℝ, Submission.Length.curveSpeed (I := I) γ' t = 1) ∧
      (∀ t ∈ Set.Icc a b, γ' t = γ t) := by
  classical
  -- initial data at an interior time
  set t₀ : ℝ := (a + b) / 2 with ht₀def
  have ht₀mem : t₀ ∈ Set.Ioo a b := by
    refine ⟨?_, ?_⟩ <;> rw [ht₀def] <;> linarith
  set x : M := γ t₀ with hxdef
  set v : TangentSpace I x := curveVelocity (I := I) γ t₀ with hvdef
  have hv : v ≠ 0 := by rw [hvdef]; exact hne t₀ ht₀mem
  -- the global geodesic ray based at `x` with velocity `v`
  set γ' : ℝ → M := fun t : ℝ => GExp (cov := cov) hmet x ((t - t₀) • v) with hγ'def
  have hγ'sm : ContMDiff 𝓘(ℝ) I ∞ γ' := by
    rw [hγ'def]
    have hσ : ContMDiff 𝓘(ℝ) I ∞ (fun s : ℝ => GExp (cov := cov) hmet x (s • v)) :=
      Submission.ConjEnergy.contMDiff_GExp_smul (cov := cov) hmet x hv
    have hshift : ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞ (fun t : ℝ => t - t₀) := by
      have h1 : ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞ (fun t : ℝ => t) := contMDiff_id
      have h2 : ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞ (fun _ : ℝ => t₀) := contMDiff_const
      simpa using h1.sub h2
    exact hσ.comp hshift
  have hσsm : ContMDiff 𝓘(ℝ) I ∞ (fun s : ℝ => GExp (cov := cov) hmet x (s • v)) :=
    Submission.ConjEnergy.contMDiff_GExp_smul (cov := cov) hmet x hv
  have hmd : ∀ r : ℝ,
      MDifferentiableAt 𝓘(ℝ) I (fun s : ℝ => GExp (cov := cov) hmet x (s • v)) r :=
    fun r => (hσsm r).mdifferentiableAt (by simp)
  have hγ'geo : ∀ t : ℝ, Submission.Geodesic.IsGeodesicAt (I := I) cov γ' t := by
    intro t
    rw [hγ'def]
    have h := Submission.GeodesicGlobal2.isGeodesicAt_comp_sub (cov := cov)
      (σ := fun s : ℝ => GExp (cov := cov) hmet x (s • v)) (t := t - t₀) (T := t₀)
      (Filter.Eventually.of_forall hmd)
      (Submission.GExpRayZero.isGeodesicAt_GExp_smul_all (cov := cov) hmet x hv (t - t₀))
    simpa [sub_add_cancel] using h
  have hγ'ne : ∀ t : ℝ, Submission.Geodesic.curveVelocity (I := I) γ' t ≠ 0 := by
    intro t
    rw [hγ'def]
    have h := Submission.GeodesicGlobal2.curveVelocity_comp_sub (I := I)
      (σ := fun s : ℝ => GExp (cov := cov) hmet x (s • v)) (t := t - t₀) (T := t₀)
      (hmd (t - t₀))
    rw [sub_add_cancel] at h
    rw [h]
    exact Submission.RayChart.curveVelocity_GExp_ne_zero (cov := cov) hmet x hv (t - t₀)
  have hγ'v0 : Submission.Geodesic.curveVelocity (I := I) γ' t₀ = v := by
    rw [hγ'def]
    have h := Submission.GeodesicGlobal2.curveVelocity_comp_sub (I := I)
      (σ := fun s : ℝ => GExp (cov := cov) hmet x (s • v)) (t := 0) (T := t₀) (hmd 0)
    rw [zero_add] at h
    rw [h]
    exact Submission.GExpVelocity.curveVelocity_GExp_smul_zero (cov := cov) hmet x hv
  -- the initial data of `γ` and `γ'` at `t₀` agree
  have hpt : γ t₀ = γ' t₀ := by
    rw [hγ'def]
    show γ t₀ = GExp (cov := cov) hmet x ((t₀ - t₀) • v)
    rw [sub_self, zero_smul, GExp_zero]
  have hvel : Submission.Geodesic.curveVelocity (I := I) γ t₀
      = Submission.Geodesic.curveVelocity (I := I) γ' t₀ := by
    rw [hγ'v0, hvdef]
  -- uniqueness of geodesics with the same initial data
  have hEqOn : EqOn γ γ' (Set.Ioo a b) :=
    Submission.GlobalExp.eqOn_Ioo_of_isGeodesicAt_of_eq (cov := cov)
      (hsm.mono Set.Ioo_subset_Icc_self) hγ'sm.contMDiffOn hgeo
      (fun t _ => hγ'geo t) hne (fun t _ => hγ'ne t) ht₀mem hpt hvel
  -- continuity extends the agreement to the closed interval
  have hagree : ∀ t ∈ Set.Icc a b, γ' t = γ t := by
    intro t ht
    have h := Set.EqOn.of_subset_closure hEqOn hsm.continuousOn (hγ'sm.contMDiffOn).continuousOn
      Set.Ioo_subset_Icc_self (by rw [closure_Ioo (ne_of_lt hab)])
    exact (h ht).symm
  -- the speed of `γ'` is constant and equals the speed of `γ` at `t₀`
  have hγ'speed : ∀ t : ℝ, Submission.Length.curveSpeed (I := I) γ' t = 1 := by
    intro t
    have hfun : γ'
        = fun r : ℝ => (fun s : ℝ => GExp (cov := cov) hmet x (s • v)) (1 * r + (-t₀)) := by
      funext r
      rw [hγ'def]
      congr 1
      ring
    rw [hfun, Submission.Length.curveSpeed_comp_mul_add (I := I) (c := 1) (d := -t₀)
      (by norm_num) (hmd (1 * t + (-t₀)))]
    simp only [one_mul]
    rw [Submission.BrokenLength.curveSpeed_GExp_ray (cov := cov) hmet x hv (t + -t₀)]
    have hv1 : ‖v‖ = 1 := by
      rw [hvdef, ← Submission.GeodesicSpeed.curveSpeed_eq_norm (I := I) γ t₀]
      exact hunit t₀ ⟨ht₀mem.1.le, ht₀mem.2.le⟩
    exact hv1
  exact ⟨γ', hγ'sm, hγ'geo, hγ'ne, hγ'speed, hagree⟩

end Work.OddBound
