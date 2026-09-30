import Submission.Work.RiemLib.RayConj
import Submission.Work.RiemLib.LensLoop
import Submission.Work.RiemLib.InjRadius

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.GlobalExp
open Submission.HopfRinow
open Submission.InjRadius
open Submission.CutStep2

namespace Submission.InjHalf

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

/-- **Two distinct vectors of the same norm with the same image bound the injectivity radius.**
This is the abstract form of the `inj ≤ ½ℓ` half of the Cheeger–Ebin decomposition: two distinct
tangent vectors of norm `m` at `S` with the same exponential image produce a closed loop of length
`2m` through `S`, so the injectivity radius of `S` is at most `m`, i.e. half the loop's length. -/
theorem le_of_two_vectors_eq_GExp (hmet : IsMetricCompatible cov)
    {S : M} {m r : ℝ} (hm : 0 < m)
    {u v : TangentSpace I S} (hu : ‖u‖ = m) (hv : ‖v‖ = m) (huv : u ≠ v)
    (hG : GExp (cov := cov) hmet S u = GExp (cov := cov) hmet S v)
    (hinj : InjAtLeast hmet S r) : r ≤ m := by
  by_contra hcon
  rw [not_le] at hcon
  exact huv (hinj u v (by rw [hu]; exact hcon) (by rw [hv]; exact hcon) hG)

/-- **`inj ≤ ½ℓ` at the corner of a broken minimising loop.**  Let `G₁`, `G₂` be two unit-speed
geodesics of length `m` starting at `p`, meeting again at `q = G₁ m = G₂ m`, with a genuine corner
at `q` (their velocities at `q` differ, i.e. the loop is not traversed back and forth).  Then the two
*backward* rays from `q` give two distinct vectors of norm `m` with the same image `p`, so
`InjAtLeast hmet q r → r ≤ m`: the injectivity radius at the corner is at most half the length `2m`
of the broken loop. -/
theorem injAtLeast_le_corner_of_broken_loop
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {p : M} {m : ℝ} (hm : 0 < m)
    {ξ η : TangentSpace I p} (hξ : ‖ξ‖ = 1) (hη : ‖η‖ = 1)
    (hmeet : (geodCurve (cov := cov) hmet m (le_of_lt hm) p ξ hξ) m
      = (geodCurve (cov := cov) hmet m (le_of_lt hm) p η hη) m)
    (hvel : curveVelocity (I := I) (geodCurve (cov := cov) hmet m (le_of_lt hm) p ξ hξ) m
      ≠ curveVelocity (I := I) (geodCurve (cov := cov) hmet m (le_of_lt hm) p η hη) m)
    {r : ℝ} (hinj : InjAtLeast hmet ((geodCurve (cov := cov) hmet m (le_of_lt hm) p ξ hξ) m) r) :
    r ≤ m := by
  classical
  set G₁ : ℝ → M := geodCurve (cov := cov) hmet m (le_of_lt hm) p ξ hξ with hG₁
  set G₂ : ℝ → M := geodCurve (cov := cov) hmet m (le_of_lt hm) p η hη with hG₂
  obtain ⟨h01, -, -, -, hsp1⟩ := geodCurve_spec (cov := cov) hmet m (le_of_lt hm) p ξ hξ
  obtain ⟨h02, -, -, -, hsp2⟩ := geodCurve_spec (cov := cov) hmet m (le_of_lt hm) p η hη
  have hδ := geodDelta_pos (cov := cov) hmet
  have hmm : m ∈ Ioo (-(geodDelta (cov := cov) hmet)) (m + geodDelta (cov := cov) hmet) :=
    Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩
  have hsp₁ : ‖curveVelocity (I := I) G₁ m‖ = 1 := hsp1 m hmm
  have hsp₂ : ‖curveVelocity (I := I) G₂ m‖ = 1 := hsp2 m hmm
  rw [← hmeet] at hsp₂
  set v₁ : TangentSpace I (G₁ m) := (-m) • curveVelocity (I := I) G₁ m with hv₁def
  set v₂ : TangentSpace I (G₁ m) := (-m) • curveVelocity (I := I) G₂ m with hv₂def
  -- the two backward rays from the corner reach `p`
  have himg₁ : GExp (cov := cov) hmet (G₁ m) v₁ = p := by
    have h := GExp_neg_smul_curveVelocity_geodCurve (cov := cov) hmet p hξ (le_of_lt hm)
      (t := m) (s := m) (by linarith) le_rfl (by linarith) le_rfl
    rw [sub_self] at h
    rw [h01] at h
    rw [← hG₁] at h
    rw [hv₁def]
    exact h
  have himg₂ : GExp (cov := cov) hmet (G₁ m) v₂ = p := by
    have h := GExp_neg_smul_curveVelocity_geodCurve (cov := cov) hmet p hη (le_of_lt hm)
      (t := m) (s := m) (by linarith) le_rfl (by linarith) le_rfl
    rw [sub_self] at h
    rw [h02] at h
    rw [← hG₂] at h
    rw [← hmeet] at h
    rw [hv₂def]
    exact h
  -- the two vectors are distinct and of norm `m`
  have hv₁ : ‖v₁‖ = m := by
    rw [hv₁def, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hm, hsp₁, mul_one]
  have hv₂ : ‖v₂‖ = m := by
    rw [hv₂def, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hm, hsp₂, mul_one]
  have hne : v₁ ≠ v₂ := by
    intro h
    refine hvel ?_
    have h' := congrArg (fun z => ((-m)⁻¹ : ℝ) • z) h
    simp only [hv₁def, hv₂def, smul_smul, inv_mul_cancel₀ (neg_ne_zero.mpr hm.ne'), one_smul] at h'
    exact h'
  by_contra hcon
  rw [not_le] at hcon
  exact hne (hinj v₁ v₂ (by rw [hv₁]; exact hcon) (by rw [hv₂]; exact hcon)
    (by rw [himg₁, himg₂]))


/-- **The `GExp`-ray is the canonical `geodCurve`.**  For a unit `ξ` and `0 < m`, the exponential of
`m • ξ` is the point at time `m` of the length-`m` unit-speed geodesic through `p` with velocity `ξ`.
Proved by geodesic *uniqueness* (`eqOn_Ioo_of_isGeodesicAt_of_eq`): both curves are smooth geodesics
with unit speed and the same initial data `(p, ξ)`. -/
theorem GExp_eq_geodCurve (hmet : IsMetricCompatible cov) {p : M} {ξ : TangentSpace I p}
    (hξ : ‖ξ‖ = 1) {m : ℝ} (hm : 0 < m) :
    GExp (cov := cov) hmet p (m • ξ)
      = (geodCurve (cov := cov) hmet m hm.le p ξ hξ) m := by
  have hξ0 : ξ ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hξ
    norm_num at hξ
  obtain ⟨h0G, hvG, hsmG, hgeoG, hspG⟩ := geodCurve_spec (cov := cov) hmet m hm.le p ξ hξ
  have h0mem : (0 : ℝ) ∈ Ioo (-(geodDelta (cov := cov) hmet)) (m + geodDelta (cov := cov) hmet) :=
    Set.mem_Ioo.mpr ⟨by linarith [geodDelta_pos (cov := cov) hmet],
      by linarith [geodDelta_pos (cov := cov) hmet]⟩
  have hmmem : m ∈ Ioo (-(geodDelta (cov := cov) hmet)) (m + geodDelta (cov := cov) hmet) :=
    Set.mem_Ioo.mpr ⟨by linarith [geodDelta_pos (cov := cov) hmet, hm],
      by linarith [geodDelta_pos (cov := cov) hmet]⟩
  have hsmγ : ContMDiffOn 𝓘(ℝ) I ∞ (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ))
      (Ioo (-(geodDelta (cov := cov) hmet)) (m + geodDelta (cov := cov) hmet)) :=
    (Submission.LensLoop.contMDiffOn_GExp_smul (cov := cov) hmet p hξ0).mono (Set.subset_univ _)
  have hgeoγ : ∀ t ∈ Ioo (-(geodDelta (cov := cov) hmet)) (m + geodDelta (cov := cov) hmet),
      IsGeodesicAt cov (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) t :=
    fun t _ => Submission.GExpRayZero.isGeodesicAt_GExp_smul_all (cov := cov) hmet p hξ0 t
  have hneγ : ∀ t ∈ Ioo (-(geodDelta (cov := cov) hmet)) (m + geodDelta (cov := cov) hmet),
      curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) t ≠ 0 :=
    fun t _ => Submission.RayChart.curveVelocity_GExp_ne_zero (cov := cov) hmet p hξ0 t
  have hneG : ∀ t ∈ Ioo (-(geodDelta (cov := cov) hmet)) (m + geodDelta (cov := cov) hmet),
      curveVelocity (I := I) (geodCurve (cov := cov) hmet m hm.le p ξ hξ) t ≠ 0 := by
    intro t ht hzero
    have h := hspG t ht
    rw [hzero, norm_zero] at h
    norm_num at h
  have hEq := eqOn_Ioo_of_isGeodesicAt_of_eq (cov := cov) hsmγ hsmG hgeoγ hgeoG hneγ hneG h0mem
    (by rw [zero_smul, GExp_zero, h0G])
    (by rw [Submission.GExpVelocity.curveVelocity_GExp_smul_zero (cov := cov) hmet p hξ0, hvG])
  exact hEq hmmem

/-- **`inj ≤ ½ℓ` at the corner of the broken minimising loop, in exponential-map form.**  Two
distinct unit directions `ξ`, `η` at `p` whose rays of length `m` meet again, with a genuine corner
at the meeting point (velocities there distinct), give `InjAtLeast hmet (GExp p (m•ξ)) r → r ≤ m`. -/
theorem injAtLeast_le_corner_of_GExp_broken_loop
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {p : M} {m : ℝ} (hm : 0 < m)
    {ξ η : TangentSpace I p} (hξ : ‖ξ‖ = 1) (hη : ‖η‖ = 1)
    (hmeet : GExp (cov := cov) hmet p (m • ξ) = GExp (cov := cov) hmet p (m • η))
    (hvel : curveVelocity (I := I) (geodCurve (cov := cov) hmet m hm.le p ξ hξ) m
      ≠ curveVelocity (I := I) (geodCurve (cov := cov) hmet m hm.le p η hη) m)
    {r : ℝ} (hinj : InjAtLeast hmet (GExp (cov := cov) hmet p (m • ξ)) r) :
    r ≤ m := by
  have hmeet' : (geodCurve (cov := cov) hmet m hm.le p ξ hξ) m
      = (geodCurve (cov := cov) hmet m hm.le p η hη) m := by
    rw [← GExp_eq_geodCurve (cov := cov) hmet hξ hm,
      ← GExp_eq_geodCurve (cov := cov) hmet hη hm, hmeet]
  have hinj' : InjAtLeast hmet ((geodCurve (cov := cov) hmet m hm.le p ξ hξ) m) r := by
    rw [← GExp_eq_geodCurve (cov := cov) hmet hξ hm]
    exact hinj
  exact injAtLeast_le_corner_of_broken_loop (cov := cov) hmet htor hm hξ hη hmeet' hvel hinj'

end

end Submission.InjHalf
