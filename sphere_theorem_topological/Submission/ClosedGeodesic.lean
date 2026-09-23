import Submission.HopfRinow2
import Submission.InjRadius

/-!
# Closed geodesics

A **closed geodesic** is a geodesic `γ : ℝ → M` which is periodic, `γ (t + T) = γ t`, with
`T > 0`.  Equivalently (and this is the form used here): a geodesic that returns to its starting
point **with the same velocity**.

This file proves the elementary equivalence used throughout the injectivity-radius estimates
(`Submission/Roadmap.lean` §68): if `γ` is a geodesic on an interval around `0` and `T > 0` with
`γ T = γ 0` and `curveVelocity γ T = curveVelocity γ 0`, then `γ` is `T`-periodic wherever both
sides are defined.  The proof is the uniqueness of geodesics with prescribed initial data
(`eqOn_Ioo_of_isGeodesicAt_of_eq`): the shifted curve `t ↦ γ (t + T)` has the same initial
position and velocity at `0` as `γ`.
-/

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.GlobalExp
open Submission.HopfRinow

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.ClosedGeodesic

noncomputable section

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- **A geodesic that closes up with the same velocity is periodic.**  If `γ` is a `C^∞` geodesic
on the open interval `Ioo a b`, `T > 0`, and `γ T = γ 0` together with
`curveVelocity γ T = curveVelocity γ 0`, then `γ` is `T`-periodic on the intersection of `Ioo a b`
with its shift `Ioo (a - T) (b - T)`. -/
theorem eq_add_of_isGeodesicAt_of_curveVelocity
    {γ : ℝ → M} {a b : ℝ}
    (hsm : ContMDiffOn 𝓘(ℝ) I ∞ γ (Ioo a b))
    (hgeo : ∀ t ∈ Ioo a b, IsGeodesicAt cov γ t)
    (hne : ∀ t ∈ Ioo a b, curveVelocity (I := I) γ t ≠ 0)
    {T : ℝ} (hT : 0 < T) (ha0 : a < 0) (h0b : 0 < b) (hTmem : T ∈ Ioo a b)
    (hpos : γ T = γ 0) (hvel : curveVelocity (I := I) γ T = curveVelocity (I := I) γ 0) :
    ∀ t ∈ Ioo (max a (a - T)) (min b (b - T)), γ (t + T) = γ t := by
  classical
  -- the shifted curve and its basic properties
  set γ' : ℝ → M := fun t => γ (t + T) with hγ'def
  have hsubT : ∀ t ∈ Ioo (a - T) (b - T), t + T ∈ Ioo a b := by
    intro t ht
    exact Set.mem_Ioo.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hfun : (fun s : ℝ => γ (1 * s + T)) = γ' := by
    rw [hγ'def]; funext s; rw [one_mul]
  have hγ'sm : ContMDiffOn 𝓘(ℝ) I ∞ γ' (Ioo (a - T) (b - T)) := by
    rw [hγ'def]
    exact hsm.comp (contDiff_id.add contDiff_const).contMDiff.contMDiffOn
      (fun t ht => hsubT t ht)
  have hγ'geo : ∀ t ∈ Ioo (a - T) (b - T), IsGeodesicAt cov γ' t := by
    intro t ht
    rw [hγ'def]
    have h := isGeodesicAt_comp_affine (cov := cov) (σ := γ) (a := 1) (b := T) one_ne_zero
      hsm hgeo (r := t) (by simpa using hsubT t ht)
    simpa using h
  have hγ'ne : ∀ t ∈ Ioo (a - T) (b - T), curveVelocity (I := I) γ' t ≠ 0 := by
    intro t ht h0
    have hmd : MDifferentiableAt 𝓘(ℝ) I γ (t + T) :=
      (hsm.contMDiffAt (isOpen_Ioo.mem_nhds (hsubT t ht))).mdifferentiableAt (by simp)
    have hv := Submission.Length.curveVelocity_comp_mul_add (I := I) (γ := γ) (c := 1) (d := T)
      (t := t) (by simpa using hmd)
    rw [hfun, one_mul] at hv
    rw [h0, one_smul] at hv
    exact hne (t + T) (hsubT t ht) hv.symm
  -- the comparison interval, which contains `0`
  set A : ℝ := max a (a - T) with hAdef
  set B : ℝ := min b (b - T) with hBdef
  have hA0 : A < 0 := by
    rw [hAdef]; exact max_lt ha0 (by linarith)
  have h0B : 0 < B := by
    rw [hBdef]; exact lt_min h0b (by linarith [hTmem.2])
  have hsubA : Ioo A B ⊆ Ioo a b := by
    intro t ht
    exact Set.mem_Ioo.mpr ⟨lt_of_le_of_lt (le_max_left _ _) ht.1,
      lt_of_lt_of_le ht.2 (min_le_left _ _)⟩
  have hsubB : Ioo A B ⊆ Ioo (a - T) (b - T) := by
    intro t ht
    exact Set.mem_Ioo.mpr ⟨lt_of_le_of_lt (le_max_right _ _) ht.1,
      lt_of_lt_of_le ht.2 (min_le_right _ _)⟩
  -- position and velocity at `0`
  have hpt : γ 0 = γ' 0 := by rw [hγ'def]; simpa using hpos.symm
  have hvt : curveVelocity (I := I) γ 0 = curveVelocity (I := I) γ' 0 := by
    rw [hγ'def]
    have hmd : MDifferentiableAt 𝓘(ℝ) I γ (0 + T) :=
      by simpa using (hsm.contMDiffAt (isOpen_Ioo.mem_nhds hTmem)).mdifferentiableAt (by simp)
    have hv := Submission.Length.curveVelocity_comp_mul_add (I := I) (γ := γ) (c := 1) (d := T)
      (t := 0) (by simpa using hmd)
    rw [hfun, one_mul, zero_add, one_smul] at hv
    rw [hv]
    exact hvel.symm
  have hEqOn := eqOn_Ioo_of_isGeodesicAt_of_eq (cov := cov) (a := A) (b := B)
    (hsm.mono hsubA) (hγ'sm.mono hsubB)
    (fun t ht => hgeo t (hsubA ht)) (fun t ht => hγ'geo t (hsubB ht))
    (fun t ht => hne t (hsubA ht)) (fun t ht => hγ'ne t (hsubB ht))
    (t₀ := 0) (Set.mem_Ioo.mpr ⟨hA0, h0B⟩) hpt hvt
  intro t ht
  have := hEqOn ht
  rw [hγ'def] at this
  exact this.symm

end

end Submission.ClosedGeodesic
