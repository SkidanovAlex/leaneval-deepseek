import Mathlib
import Submission.Work.RiemLib.Work.OddBound.LiftKit

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Work.OddBound.longHomotopy

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory Interval
open LeanEval.Geometry.SphereTheorem Submission.Geodesic Submission.JacobiGlobal Submission.GlobalExp Submission.Length Submission.InjRadius

/-!
# The open-and-closed ("clopen") step of the long homotopy argument

Given the data of Klingenberg's long homotopy argument -- a family `c s t` of closed curves, two
lifts `Wp`, `Wm` of the two halves `c s ·` and `c (1-s) ·` under the exponential map at `p`, whose
values all lie in the open ball of radius `π/√K`, which agree at `t = 1` and whose values at `t = 0`
are the two straight segments `± s • (L • γ'(0))` -- there is a contradiction.

The mechanism is the classical open-and-closed argument: below the conjugate radius `π/√K` the
exponential map is a local diffeomorphism, so the set

  `A = {(s,t) | Wp s t = Wm (1-s) t}`

is *open* (near a point of `A` both values lie in a neighbourhood on which `GExp p` is injective,
and they have the same `GExp p`-image) and *closed* (it is the zero set of a continuous map), hence
is all of `ℝ × ℝ` by connectedness.  At `(1/2, 1)` the agreement is the hypothesis `hW1`, and at
`(1/2, 0)` the conclusion `Wp (1/2) 0 = Wm (1/2) 0`, together with the straight-ray data `hstr`,
forces `(1/2) • (L • γ'(0)) = -(1/2) • (L • γ'(0))`, i.e. `γ'(0) = 0`, contradicting the
non-vanishing of the velocity of `γ`.
-/

/-- **Local injectivity of `GExp p` on the conjugate-free ball.**  For `sec ≤ K`, `0 < K`, the
exponential map at `p` is injective on a neighbourhood of every vector of norm `< π/√K`.  (The
non-zero vectors are handled by Rauch's conjugate radius bound; the origin by `d GExp_0 = id`.) -/
theorem locallyInjectiveAtGExp_of_norm_lt_pi_div_sqrt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {K : ℝ} (hK : 0 < K) (hcurv : Submission.RauchK.CurvLe cov K)
    {p : M} {v : TangentSpace I p}
    (hv : ‖v‖ < Real.pi / Real.sqrt K) :
    Submission.CutStep2.LocallyInjectiveAtGExp (I := I) hmet p v := by
  by_cases hv0 : v = 0
  · subst hv0
    refine Submission.GExpLocalInj.locallyInjectiveAtGExp_of_injective_mfderiv
      (cov := cov) hmet ?_
    rw [show (show E from (0 : TangentSpace I p)) = (0 : E) from rfl,
      Submission.GExpLocalInj.mfderiv_GExp_zero (cov := cov) hmet p]
    exact Function.injective_id
  · exact Submission.RayConj.locallyInjectiveAtGExp_of_norm_lt_pi_div_sqrt
      (cov := cov) hmet htor hcurv hK hv0 hv

theorem clopen_step
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {K : ℝ} (hK : 0 < K) (hcurv : Submission.RauchK.CurvLe cov K)
    {p : M} {L : ℝ} (hL : 0 < L) {γ : ℝ → M}
    (hne : ∀ t : ℝ, Submission.Geodesic.curveVelocity (I := I) γ t ≠ 0)
    {c : ℝ → ℝ → M} (hcsm : ContMDiff (𝓘(ℝ, ℝ × ℝ)) I ∞ (fun u : ℝ × ℝ => c u.1 u.2))
    (hcper : ∀ s t : ℝ, c (s + 1) t = c s t)
    {Wp Wm : ℝ → ℝ → TangentSpace I p}
    (hWpc : Continuous fun u : ℝ × ℝ => Wp u.1 u.2) (hWp0 : ∀ t : ℝ, Wp 0 t = 0)
    (hWpG : ∀ s t : ℝ, Submission.GlobalExp.GExp (cov := cov) hmet p (Wp s t) = c s t)
    (hWpb : ∀ s t : ℝ, ‖Wp s t‖ < Real.pi / Real.sqrt K)
    (hWmc : Continuous fun u : ℝ × ℝ => Wm u.1 u.2) (hWm0 : ∀ t : ℝ, Wm 0 t = 0)
    (hWmG : ∀ s t : ℝ, Submission.GlobalExp.GExp (cov := cov) hmet p (Wm s t) = c (1 - s) t)
    (hWmb : ∀ s t : ℝ, ‖Wm s t‖ < Real.pi / Real.sqrt K)
    (hW1 : ∀ s : ℝ, Wp s 1 = Wm s 1)
    (hstr : ∀ s ∈ Set.Icc (0 : ℝ) (1 / 2),
      Wp s 0 = s • (L • Submission.Geodesic.curveVelocity (I := I) γ 0) ∧
      Wm s 0 = s • (-(L • Submission.Geodesic.curveVelocity (I := I) γ 0))) :
    False := by
  classical
  -- ## 1. `GExp p` is locally injective on the open ball of radius `π/√K`
  have hloc : ∀ v : TangentSpace I p, ‖v‖ < Real.pi / Real.sqrt K →
      Submission.CutStep2.LocallyInjectiveAtGExp (I := I) hmet p v :=
    fun v hv => locallyInjectiveAtGExp_of_norm_lt_pi_div_sqrt (cov := cov) hmet htor hK hcurv hv
  -- ## 2. The agreement set `A = {(s,t) | Wp s t = Wm (1-s) t}`
  set A : Set (ℝ × ℝ) := {u : ℝ × ℝ | Wp u.1 u.2 = Wm (1 - u.1) u.2} with hA
  have hWmC : Continuous fun u : ℝ × ℝ => Wm (1 - u.1) u.2 :=
    hWmc.comp ((continuous_const.sub continuous_fst).prodMk continuous_snd)
  -- `A` is closed: it is the zero set of a continuous `T_pM`-valued map
  have hAclosed : IsClosed A := by
    have hpre : A = (fun u : ℝ × ℝ => Wp u.1 u.2 - Wm (1 - u.1) u.2) ⁻¹' {0} := by
      ext u
      rw [hA]
      simp [sub_eq_zero]
    rw [hpre]
    exact isClosed_singleton.preimage (hWpc.sub hWmC)
  -- `A` is open: near a point of `A` both values lie where `GExp p` is injective
  have hAopen : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    intro u hu
    rw [hA] at hu
    obtain ⟨V, hV, hVinj⟩ := hloc (Wp u.1 u.2) (hWpb u.1 u.2)
    have hux : Wp u.1 u.2 = Wm (1 - u.1) u.2 := hu
    have h1 : {u : ℝ × ℝ | Wp u.1 u.2 ∈ V} ∈ 𝓝 u :=
      hWpc.continuousAt.preimage_mem_nhds hV
    have h2 : {u : ℝ × ℝ | Wm (1 - u.1) u.2 ∈ V} ∈ 𝓝 u :=
      hWmC.continuousAt.preimage_mem_nhds (hux ▸ hV)
    refine Filter.mem_of_superset (Filter.inter_mem h1 h2) ?_
    rintro u' ⟨h1', h2'⟩
    rw [hA]
    refine hVinj _ h1' _ h2' ?_
    rw [hWpG (u'.1) (u'.2), hWmG (1 - u'.1) (u'.2),
      show (1 : ℝ) - (1 - u'.1) = u'.1 by ring]
  -- `A` is nonempty by the hypothesis `hW1` at `s = 1/2`
  have hAne : A.Nonempty := ⟨((1/2 : ℝ), 1), by
    rw [hA]
    show Wp (1/2) 1 = Wm (1 - 1/2) 1
    rw [show (1 : ℝ) - 1/2 = 1/2 by norm_num]
    exact hW1 (1/2)⟩
  have hAuniv : A = Set.univ := IsClopen.eq_univ ⟨hAclosed, hAopen⟩ hAne
  -- ## 3. The contradiction at `(s,t) = (1/2, 0)`
  have hkey : Wp (1/2) 0 = Wm (1/2) 0 := by
    have hmem : Wp (1/2) 0 = Wm (1 - 1/2) 0 := by
      have hmem' : ((1/2 : ℝ), (0 : ℝ)) ∈ A := by rw [hAuniv]; exact Set.mem_univ _
      rw [hA] at hmem'
      exact hmem'
    rw [show (1 : ℝ) - 1/2 = 1/2 by norm_num] at hmem
    exact hmem
  obtain ⟨hp0, hm0⟩ := hstr (1/2) ⟨by norm_num, le_rfl⟩
  -- the two straight rays of `hstr` at `s = 1/2` are identified through `hkey`
  have hsm : (1/2 : ℝ) • (L • Submission.Geodesic.curveVelocity (I := I) γ 0)
      = (1/2 : ℝ) • (-(L • Submission.Geodesic.curveVelocity (I := I) γ 0)) := by
    rw [← hp0, hkey, hm0]
  have hLv : L • Submission.Geodesic.curveVelocity (I := I) γ 0 = 0 := by
    have h1 : L • Submission.Geodesic.curveVelocity (I := I) γ 0
        = -(L • Submission.Geodesic.curveVelocity (I := I) γ 0) := by
      calc L • Submission.Geodesic.curveVelocity (I := I) γ 0
          = (1/2 : ℝ)⁻¹ • ((1/2 : ℝ) • (L • Submission.Geodesic.curveVelocity (I := I) γ 0)) :=
            (inv_smul_smul₀ (show (1/2 : ℝ) ≠ 0 by norm_num) _).symm
        _ = (1/2 : ℝ)⁻¹ •
              ((1/2 : ℝ) • (-(L • Submission.Geodesic.curveVelocity (I := I) γ 0))) := by
            rw [hsm]
        _ = -(L • Submission.Geodesic.curveVelocity (I := I) γ 0) :=
            inv_smul_smul₀ (show (1/2 : ℝ) ≠ 0 by norm_num) _
    have h3 : (2 : ℝ) • (L • Submission.Geodesic.curveVelocity (I := I) γ 0) = 0 := by
      rw [two_smul]
      nth_rewrite 1 [h1]
      exact neg_add_cancel _
    calc L • Submission.Geodesic.curveVelocity (I := I) γ 0
        = (1/2 : ℝ) • ((2 : ℝ) • (L • Submission.Geodesic.curveVelocity (I := I) γ 0)) := by
          rw [smul_smul, show (1/2 : ℝ) * 2 = 1 by norm_num, one_smul]
      _ = 0 := by rw [h3, smul_zero]
  have hvzero : Submission.Geodesic.curveVelocity (I := I) γ 0 = 0 := by
    calc Submission.Geodesic.curveVelocity (I := I) γ 0
        = L⁻¹ • (L • Submission.Geodesic.curveVelocity (I := I) γ 0) := by
          rw [smul_smul, inv_mul_cancel₀ (ne_of_gt hL), one_smul]
      _ = 0 := by rw [hLv, smul_zero]
  exact hne 0 hvzero

end Work.OddBound.longHomotopy
