import Submission.Work.ValueClosed.Defs
import Submission.Work.ValueClosed.Periodic
import Submission.Work.ValueClosed.exists_chart_convergent_subseq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The shortest value-closed geodesic loop exists

This file assembles the compactness half of Klingenberg's structure theorem for the value-closed
predicate, `Work.ValueClosed.loopLengthInf_attained`: the infimum `ℓ` of the lengths of value-closed
geodesic loops (`Work.ValueClosed.loopLengthInf`) is attained, provided it is positive.

The ingredients are

* the tangent-data extraction `Work.ValueClosed.exists_chart_convergent_subseq` (a subsequence of the
  base points and unit initial velocities converges in a compact chart piece);
* `Submission.GExpJointPt.tendsto_GExp_ray_length` (continuity of `GExp` in the base point, the
  direction and the length), packaged as `Work.ValueClosed.GExp_return_of_raySeq_tendsto`;
* `Submission.GeodesicLoop.isGeodesicLoopAt_GExp_smul_of_returns` (the limit ray is a value-closed
  geodesic loop of length `ℓ`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.GlobalExp
open Submission.InjRadius

namespace Work.ValueClosed

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

/-- **The shortest value-closed geodesic loop exists.**  If `ℓ = loopLengthInf hmet > 0` (so that
there is at least one value-closed geodesic loop), the infimum `ℓ` is attained: there is a
value-closed geodesic loop of length exactly `ℓ`. -/
theorem loopLengthInf_attained (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M]
    (hpos : 0 < loopLengthInf (I := I) (cov := cov) hmet) :
    ∃ (p : M) (γ : ℝ → M),
      Submission.GeodesicLoop.IsGeodesicLoopAt (I := I) (cov := cov) hmet p
        (loopLengthInf (I := I) (cov := cov) hmet) γ := by
  classical
  set ℓ : ℝ := loopLengthInf (I := I) (cov := cov) hmet with hℓ
  have hne : (loopLengthSet (I := I) (cov := cov) hmet).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have h0 : loopLengthInf (I := I) (cov := cov) hmet = 0 := by
      unfold loopLengthInf
      rw [h, Real.sInf_empty]
    linarith
  -- a minimising sequence of lengths
  have hex : ∀ n : ℕ, ∃ T ∈ loopLengthSet (I := I) (cov := cov) hmet,
      T < ℓ + 1 / (n + 1 : ℝ) := fun n =>
    exists_lt_of_csInf_lt hne (by rw [hℓ]; exact lt_add_of_pos_right _ (by positivity))
  choose T hTmem hTlt using hex
  have hTle : ∀ n, ℓ ≤ T n := fun n => loopLengthInf_le_of_mem (hTmem n)
  have hTlim : Tendsto T atTop (𝓝 ℓ) := by
    refine tendsto_order.2 ⟨?_, ?_⟩
    · intro b hb
      filter_upwards with n
      linarith [hTle n]
    · intro b hb
      have hb0 : 0 < b - ℓ := by linarith
      have hev : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < b - ℓ :=
        tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ) (eventually_lt_nhds hb0)
      filter_upwards [hev] with n hn
      linarith [hTlt n]
  -- the loops and their initial data
  choose p γ hloop using fun n => mem_loopLengthSet_iff.mp (hTmem n)
  have hunit : ∀ n, ‖curveVelocity (I := I) (γ n) 0‖ = 1 :=
    fun n => (hloop n).2.2.2.2.2 0
  have hray : ∀ n (t : ℝ),
      γ n t = GExp (cov := cov) hmet (γ n 0) (t • curveVelocity (I := I) (γ n) 0) := by
    intro n t
    have hVne : curveVelocity (I := I) (γ n) 0 ≠ 0 := by
      intro h0
      have h1 := hunit n
      rw [h0, norm_zero] at h1
      norm_num at h1
    have hγne : ∀ s : ℝ, curveVelocity (I := I) (γ n) s ≠ 0 := by
      intro s h0
      have h1 := (hloop n).2.2.2.2.2 s
      rw [h0, norm_zero] at h1
      norm_num at h1
    exact Submission.KlingenbergEven.eq_GExp_of_isGeodesicAt (cov := cov) hmet (q := γ n 0)
      (V := curveVelocity (I := I) (γ n) 0) (σ := γ n) hVne
      (contMDiffOn_univ.mp (hloop n).2.2.2.1) (hloop n).2.2.2.2.1 hγne rfl rfl t
  -- extraction of a convergent subsequence of the tangent data
  obtain ⟨z₀, pstar, y₀, φ, hφmono, hpstar, hpconv, y, hyconv, hcoord, hunitlim⟩ :=
    exists_chart_convergent_subseq (I := I) (fun n => γ n 0)
      (fun n => curveVelocity (I := I) (γ n) 0) hunit
  have hTconv : Tendsto (fun k => T (φ k)) atTop (𝓝 ℓ) :=
    hTlim.comp (hφmono.tendsto_atTop)
  have hunit' : ∀ k, ‖frameVector (I := I) z₀ (γ (φ k) 0) (y k)‖ = 1 := by
    intro k
    rw [← hcoord k]
    exact hunit (φ k)
  have hret : ∀ k, GExp (cov := cov) hmet (γ (φ k) 0)
      (T (φ k) • frameVector (I := I) z₀ (γ (φ k) 0) (y k)) = γ (φ k) 0 := by
    intro k
    have h1 : GExp (cov := cov) hmet (γ (φ k) 0)
        (T (φ k) • curveVelocity (I := I) (γ (φ k)) 0) = γ (φ k) (T (φ k)) :=
      (hray (φ k) (T (φ k))).symm
    have h2 : γ (φ k) (T (φ k)) = γ (φ k) 0 :=
      ((hloop (φ k)).2.2.1).trans ((hloop (φ k)).2.1).symm
    rw [← hcoord k]
    exact h1.trans h2
  have hLnpos : ∀ k, 0 ≤ T (φ k) := fun k => by
    obtain ⟨p', γ', hl⟩ := mem_loopLengthSet_iff.mp (hTmem (φ k))
    exact hl.1.le
  have hmain := GExp_return_of_raySeq_tendsto (I := I) (cov := cov) hmet htor hpstar hpconv
    hyconv hunit' hunitlim hTconv hLnpos (by rw [hℓ]; exact hpos) hret
  exact ⟨pstar, fun s : ℝ => GExp (cov := cov) hmet pstar (s • frameVector (I := I) z₀ pstar y₀),
    Submission.GeodesicLoop.isGeodesicLoopAt_GExp_smul_of_returns (I := I) (cov := cov) hmet
      pstar hunitlim (by rw [hℓ]; exact hpos) hmain⟩

end

end Work.ValueClosed
