import Submission.GExpTwoSided

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The ray of the global exponential map is *the* geodesic with the given initial data

`GExpGlob.exists_pos_eq_GExp_of_isGeodesicAt` shows that a geodesic `γ` with `γ 0 = p` and
`γ̇(0) = V ≠ 0` agrees with the `GExp`-ray `ρ s = GExp p (s • V)` on a *right-neighbourhood* of `0`.
This file upgrades that to an arbitrary closed interval `[0,T]`:

* `contMDiffOn_GExp_smul_Ioo`: the ray `s ↦ GExp x (s • v)` (`v ≠ 0`) is `C^∞` on `Ioo 0 b`
  (it is a reparametrised chosen geodesic segment `geodCurve`);
* `eqOn_Icc_GExp_of_isGeodesicAt`: **if `γ` is a geodesic on an open interval `Ioo a b`
  containing `0` in its interior and `[0,T]` with `T < b`, with `γ 0 = p` and `γ̇(0) = V ≠ 0`, then
  `γ t = GExp p (t • V)` for every `t ∈ [0,T]`.**

The proof is the classical one: the initial agreement
(`exists_pos_eq_GExp_of_isGeodesicAt`) together with `eqOn_Ioo_right_of_isGeodesicAt_of_eq`
applied on the interval `Ioo 0 b` — the point `t₁` of the initial agreement is an *interior* point
of `Ioo 0 b`, so the two curves agree on a genuine two-sided neighbourhood of it, their velocities
there agree, and uniqueness of geodesics propagates the agreement to all of `Ioo t₁ b`.

This is the tool that identifies the `GExp`-ray with any geodesic through `p` with the same initial
data — in particular with the flow lines of the chart geodesic spray, which is what the
continuation of the ray beyond the first cut point needs.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.GlobalExp
open Submission.HopfRinow
open Submission.ChartBounds
open Submission.GeodesicExtend
open Submission.GExpTwoSided
open Submission.GExpGlob

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.GExpRayIdent

noncomputable section

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-! ## Smoothness of the ray away from the base point -/

/-- **The ray of `GExp` is `C^∞` on `Ioo 0 b`.**  On that interval the ray is the fixed chosen
geodesic segment `geodCurve` in the direction of `unitOf v`, reparametrised by arclength. -/
theorem contMDiffOn_GExp_smul_Ioo (hmet : IsMetricCompatible cov) (x : M)
    {v : TangentSpace I x} (hv : v ≠ 0) (b : ℝ) :
    ContMDiffOn 𝓘(ℝ) I ∞ (fun s : ℝ => GExp (cov := cov) hmet x (s • v)) (Ioo 0 b) := by
  by_cases hb : 0 < b
  · have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hgd := geodDelta_pos (cov := cov) hmet
    set T : ℝ := max ‖v‖ (b * ‖v‖) with hTdef
    have hTnn : 0 ≤ T := le_trans (norm_nonneg v) (le_max_left _ _)
    set ξ : TangentSpace I x := unitOf v hv with hξdef
    have hξnorm : ‖ξ‖ = 1 := unitOf_norm v hv
    obtain ⟨-, -, hgcsm, -, -⟩ := geodCurve_spec (cov := cov) hmet T hTnn x ξ hξnorm
    have hmem : ∀ s ∈ Ioo (0 : ℝ) b,
        ‖v‖ * s ∈ Ioo (-(geodDelta (cov := cov) hmet)) (T + geodDelta (cov := cov) hmet) := by
      intro s hs
      refine Set.mem_Ioo.mpr ⟨by linarith [hgd, mul_pos hvpos hs.1], ?_⟩
      have h1 : s * ‖v‖ < b * ‖v‖ := mul_lt_mul_of_pos_right hs.2 hvpos
      have h2 : b * ‖v‖ ≤ T := by rw [hTdef]; exact le_max_right _ _
      nlinarith [h1, h2, hgd]
    have hm : ∀ s ∈ Ioo (0:ℝ) b,
        GExp (cov := cov) hmet x (s • v)
          = (geodCurve (cov := cov) hmet T hTnn x ξ hξnorm) (‖v‖ * s) := by
      intro s hs
      rw [GExp_smul (cov := cov) hmet x hv hs.1.le, mul_comm ‖v‖ s]
      refine geodCurve_agree (cov := cov) hmet (T₁ := max ‖v‖ (s * ‖v‖)) (T₂ := T)
        (le_trans (norm_nonneg v) (le_max_left _ _)) hTnn ?_ x ξ hξnorm ?_
      · exact max_le (le_max_left _ _) (by
          have h1 : s * ‖v‖ ≤ b * ‖v‖ := mul_le_mul_of_nonneg_right hs.2.le (norm_nonneg v)
          rw [hTdef]; exact le_trans h1 (le_max_right _ _))
      · exact ⟨by linarith [hgd, mul_pos hs.1 hvpos],
          by linarith [hgd, le_max_right ‖v‖ (s * ‖v‖)]⟩
    have hlin : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun s : ℝ => ‖v‖ * s) (Ioo (0:ℝ) b) :=
      (contMDiff_const.mul contMDiff_id).contMDiffOn
    have hsm : ContMDiffOn 𝓘(ℝ) I ∞
        (fun s : ℝ => (geodCurve (cov := cov) hmet T hTnn x ξ hξnorm) (‖v‖ * s))
        (Ioo (0:ℝ) b) :=
      hgcsm.comp hlin hmem
    exact hsm.congr hm
  · rw [Ioo_eq_empty hb]
    exact contMDiffOn_empty

/-! ## The ray identification -/

/-- **The `GExp`-ray is the unique geodesic with the given initial data.**  Let `γ` be a geodesic on
an open interval `Ioo a b` containing `0` in its interior, with `γ 0 = p`, `γ̇(0) = V ≠ 0`, and let
`T < b` (so that `[0,T]` is an interval inside `Ioo a b` starting at `0`).  Then `γ` agrees with the
`GExp`-ray of `V` on all of `[0,T]`. -/
theorem eqOn_Icc_GExp_of_isGeodesicAt (hmet : IsMetricCompatible cov)
    {p : M} {V : TangentSpace I p} (hV : V ≠ 0)
    {a b T : ℝ} (ha : a < 0) (hTnn : 0 ≤ T) (hTb : T < b) {γ : ℝ → M}
    (hsm : ContMDiffOn 𝓘(ℝ) I ∞ γ (Ioo a b))
    (hgeo : ∀ t ∈ Ioo a b, IsGeodesicAt cov γ t)
    (hne : ∀ t ∈ Ioo a b, curveVelocity (I := I) γ t ≠ 0)
    (h0 : γ 0 = p) (hvel : curveVelocity (I := I) γ 0 = V) :
    ∀ t ∈ Icc (0 : ℝ) T, γ t = GExp (cov := cov) hmet p (t • V) := by
  have hbpos : 0 < b := lt_of_le_of_lt hTnn hTb
  set ρ : ℝ → M := fun s : ℝ => GExp (cov := cov) hmet p (s • V) with hρdef
  -- the initial agreement
  set ε : ℝ := min (-a) b with hεdef
  have hεpos : 0 < ε := lt_min (by linarith) hbpos
  have hεsub : Ioo (-ε) ε ⊆ Ioo a b := by
    intro t ht
    refine ⟨?_, ?_⟩
    · have h1 : a ≤ -ε := by
        have h := min_le_left (-a) b
        rw [hεdef]
        linarith
      linarith [ht.1]
    · have h2 : ε ≤ b := by rw [hεdef]; exact min_le_right _ _
      linarith [ht.2]
  obtain ⟨ε', hε'pos, hε'le, hagree⟩ :=
    exists_pos_eq_GExp_of_isGeodesicAt (cov := cov) hmet hV hεpos
      (hsm.mono hεsub) (fun t ht => hgeo t (hεsub ht))
      (fun t ht => hne t (hεsub ht)) h0 hvel
  set t₁ : ℝ := ε' / 2 with ht₁def
  have ht₁pos : 0 < t₁ := by rw [ht₁def]; linarith
  have ht₁lt : t₁ < ε' := by rw [ht₁def]; linarith
  -- the two curves agree on a two-sided neighbourhood of `t₁`
  have hev : γ =ᶠ[𝓝 t₁] ρ := by
    filter_upwards [isOpen_Ioo.mem_nhds (show t₁ ∈ Ioo (0:ℝ) ε' from ⟨ht₁pos, ht₁lt⟩)]
      with s hs
    exact hagree s hs.1 hs.2
  -- uniqueness of geodesics on `Ioo 0 b`
  have hρsm : ContMDiffOn 𝓘(ℝ) I ∞ ρ (Ioo (0:ℝ) b) := contMDiffOn_GExp_smul_Ioo (cov := cov) hmet p hV b
  have hγsm : ContMDiffOn 𝓘(ℝ) I ∞ γ (Ioo (0:ℝ) b) :=
    hsm.mono (fun t ht => ⟨lt_of_lt_of_le ha ht.1.le, ht.2⟩)
  have hρgeo : ∀ t ∈ Ioo (0:ℝ) b, IsGeodesicAt cov ρ t :=
    fun t ht => isGeodesicAt_GExp_smul (cov := cov) hmet p hV ht.1
  have hγgeo : ∀ t ∈ Ioo (0:ℝ) b, IsGeodesicAt cov γ t :=
    fun t ht => hgeo t ⟨lt_of_lt_of_le ha ht.1.le, ht.2⟩
  have hρne : ∀ t ∈ Ioo (0:ℝ) b, curveVelocity (I := I) ρ t ≠ 0 := by
    intro t ht hzero
    have h := norm_curveVelocity_GExp_smul (cov := cov) hmet p hV ht.1
    rw [hzero, norm_zero] at h
    exact (norm_pos_iff.mpr hV).ne' h.symm
  have hγne : ∀ t ∈ Ioo (0:ℝ) b, curveVelocity (I := I) γ t ≠ 0 :=
    fun t ht => hne t ⟨lt_of_lt_of_le ha ht.1.le, ht.2⟩
  have hεb : ε ≤ b := by rw [hεdef]; exact min_le_right _ _
  have ht₁mem : t₁ ∈ Ioo (0:ℝ) b := ⟨ht₁pos, lt_of_lt_of_le ht₁lt (le_trans hε'le hεb)⟩
  have hpt : γ t₁ = ρ t₁ := hev.eq_of_nhds
  have hvel' : curveVelocity (I := I) γ t₁ = curveVelocity (I := I) ρ t₁ :=
    curveVelocity_congr_of_eventuallyEq (I := I) hev
  have hright : EqOn γ ρ (Ioo t₁ b) :=
    eqOn_Ioo_right_of_isGeodesicAt_of_eq hγsm hρsm hγgeo hρgeo hγne hρne ht₁mem hpt hvel'
  intro t ht
  rcases lt_or_ge t t₁ with hlt | hle
  · rcases eq_or_lt_of_le ht.1 with h0t | h0t
    · rw [← h0t, h0, zero_smul, GExp_zero]
    · exact hagree t h0t (lt_of_lt_of_le hlt (le_of_lt ht₁lt))
  · rcases eq_or_lt_of_le hle with heq | hlt'
    · rw [← heq]; exact hpt
    · exact hright ⟨hlt', lt_of_le_of_lt ht.2 hTb⟩

end

end Submission.GExpRayIdent
