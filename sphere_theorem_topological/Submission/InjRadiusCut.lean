import Submission.CutTime
import Submission.LensSync
import Submission.GExpTwoSided
import Submission.GExpRayVelocity

/-!
# The injectivity radius as the minimum of the cut times

The two notions of "the exponential map is injective below `m`" and "no ray stops being minimising
before `m`" coincide:

> `InjAtLeast hmet p m ↔ ∀ ξ, ‖ξ‖ = 1 → m ≤ cutTime hmet p ξ`.

The forward implication is `Submission.CutTime.injAtLeast_le_cutTime` (a ray minimising up to the
injectivity radius).  The converse is the content of this file, and it is the classical statement
that **the injectivity radius is the minimum of the cut times** (`inj(p) = min_ξ τ(ξ)`, see
Xu, arXiv:1401.5549).  Its proof uses the *sync lemma*
(`Submission.LensSync.eq_GExp_of_minimising_pair`): two minimising rays of the same length meeting
again must *merge* from the meeting point on, and two geodesics agreeing on a non-degenerate
interval are the same geodesic, whence the two directions coincide.

## Contents

* `cutTime_lt_of_not_minimising`: if a ray is not minimising at `t ≥ 0` then its cut time is `< t`;
* `injAtLeast_of_forall_cutTime_le`: `∀ ξ, m ≤ τ(ξ) → InjAtLeast hmet p m`;
* `injAtLeast_iff_forall_cutTime_le`: the equivalence.
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
open Submission.InjRadius
open Submission.CutTime
open Submission.CutWitness
open Submission.GExpRay
open Submission.GExpRay2
open Submission.GExpRayIdent
open Submission.GExpTwoSided
open Submission.LensSync
open Submission.GeodesicExtend

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.InjRadiusCut

noncomputable section

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]
variable [PathConnectedSpace M] [RegularSpace M]

/-- **A non-minimising time lies beyond the cut time.** -/
theorem cutTime_lt_of_not_minimising (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {p : M} {ξ : TangentSpace I p} (hξ : ‖ξ‖ = 1) {t : ℝ} (ht : 0 ≤ t)
    (h : Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (t • ξ))
      ≠ ENNReal.ofReal t) :
    cutTime (I := I) hmet p ξ < t := by
  by_contra hcon
  rw [not_lt] at hcon
  refine h ?_
  have hmem : t ∈ minimisingSet (I := I) hmet p ξ := by
    rw [mem_minimisingSet_iff (I := I) (cov := cov) hmet htor hξ]
    exact ⟨ht, hcon⟩
  exact hmem.2

/-- **The injectivity radius is at most the minimum of the cut times**: if every ray is minimising
up to `m`, the exponential map is injective on the open ball of radius `m`.

Indeed, a witness pair `u ≠ v` with `‖u‖, ‖v‖ < m` and `GExp p u = GExp p v` would consist of two
*minimising* rays of the same length (a shorter ray than `‖u‖` would contradict the cut-time
hypothesis), and the sync lemma would make the two rays merge from their meeting point on; two
geodesics agreeing on a non-degenerate interval are equal, so the two directions — and hence `u`
and `v` — would be equal. -/
theorem injAtLeast_of_forall_cutTime_le (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {p : M} {m : ℝ} (hcut : ∀ ξ : TangentSpace I p, ‖ξ‖ = 1 →
      m ≤ cutTime (I := I) hmet p ξ) :
    InjAtLeast hmet p m := by
  intro u v hu hv hG
  by_contra huv
  -- (1) no vector with the same image has a strictly smaller norm than `u`
  have hkey : ∀ w₁ w₂ : TangentSpace I p,
      GExp (cov := cov) hmet p w₁ = GExp (cov := cov) hmet p w₂ → ‖w₁‖ < m → ‖w₂‖ < m →
      ¬ (‖w₁‖ < ‖w₂‖) := by
    intro w₁ w₂ hw hw₁m hw₂m hwlt
    have h0 : 0 < ‖w₂‖ := lt_of_le_of_lt (norm_nonneg w₁) hwlt
    have hune : w₂ ≠ 0 := norm_pos_iff.mp h0
    set ξ : TangentSpace I p := unitOf w₂ hune with hξdef
    have hξ : ‖ξ‖ = 1 := unitOf_norm w₂ hune
    have hscale : ‖w₂‖ • ξ = w₂ := by
      rw [hξdef]
      show ‖w₂‖ • unitOf w₂ hune = w₂
      rw [unitOf, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hune), one_smul]
    have hlt : Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (‖w₂‖ • ξ))
        < ENNReal.ofReal ‖w₂‖ := by
      calc Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (‖w₂‖ • ξ))
          = Manifold.riemannianEDist I p (GExp (cov := cov) hmet p w₂) := by rw [hscale]
        _ = Manifold.riemannianEDist I p (GExp (cov := cov) hmet p w₁) := by rw [hw]
        _ ≤ ENNReal.ofReal ‖w₁‖ := edist_GExp_le_norm (cov := cov) hmet w₁
        _ < ENNReal.ofReal ‖w₂‖ :=
            (ENNReal.ofReal_lt_ofReal_iff' (p := ‖w₁‖) (q := ‖w₂‖)).mpr ⟨hwlt, h0⟩
    have hcutlt : cutTime (I := I) hmet p ξ < ‖w₂‖ :=
      cutTime_lt_of_not_minimising (I := I) (cov := cov) hmet htor hξ (norm_nonneg w₂)
        (ne_of_lt hlt)
    have := hcut ξ hξ
    linarith
  -- (2) the two norms are equal
  have hnorm : ‖u‖ = ‖v‖ := by
    refine le_antisymm ?_ ?_
    · exact not_lt.mp (hkey v u hG.symm hv hu)
    · exact not_lt.mp (hkey u v hG hu hv)
  have huv0 : 0 < ‖u‖ := by
    rcases eq_or_lt_of_le (norm_nonneg u) with h0 | h0
    · exfalso
      have hu0 : u = 0 := norm_eq_zero.mp h0.symm
      have hv0 : v = 0 := norm_eq_zero.mp (by rw [← hnorm]; exact h0.symm)
      exact huv (by rw [hu0, hv0])
    · exact h0
  -- (3) the common point is minimising for both rays
  have hmin : Manifold.riemannianEDist I p (GExp (cov := cov) hmet p u) = ENNReal.ofReal ‖u‖ := by
    refine le_antisymm (edist_GExp_le_norm (cov := cov) hmet u) ?_
    by_contra hcon
    rw [not_le] at hcon
    have hune : u ≠ 0 := norm_pos_iff.mp huv0
    set ξ : TangentSpace I p := unitOf u hune with hξdef
    have hξ : ‖ξ‖ = 1 := unitOf_norm u hune
    have hscale : ‖u‖ • ξ = u := by
      rw [hξdef]
      show ‖u‖ • unitOf u hune = u
      rw [unitOf, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hune), one_smul]
    have hlt : Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (‖u‖ • ξ))
        < ENNReal.ofReal ‖u‖ := by rw [hscale]; exact hcon
    have hcutlt : cutTime (I := I) hmet p ξ < ‖u‖ :=
      cutTime_lt_of_not_minimising (I := I) (cov := cov) hmet htor hξ (norm_nonneg u)
        (ne_of_lt hlt)
    have := hcut ξ hξ
    linarith [hu]
  -- (4) the sync lemma: the two rays agree on `[‖u‖, m)`
  have hune : u ≠ 0 := norm_pos_iff.mp huv0
  have hvne : v ≠ 0 := by
    intro h0
    have h1 : ‖u‖ = 0 := by rw [hnorm, h0, norm_zero]
    exact absurd h1 (ne_of_gt huv0)
  set ξ : TangentSpace I p := unitOf u hune with hξdef
  set η : TangentSpace I p := unitOf v hvne with hηdef
  have hξ : ‖ξ‖ = 1 := unitOf_norm u hune
  have hη : ‖η‖ = 1 := unitOf_norm v hvne
  have hscaleu : ‖u‖ • ξ = u := by
    rw [hξdef]
    show ‖u‖ • unitOf u hune = u
    rw [unitOf, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hune), one_smul]
  have hscalev : ‖u‖ • η = v := by
    rw [show ‖u‖ = ‖v‖ from hnorm, hηdef]
    show ‖v‖ • unitOf v hvne = v
    rw [unitOf, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hvne), one_smul]
  have hξη : ξ ≠ η := by
    intro h
    apply huv
    rw [← hscaleu, ← hscalev, h]
  have hmeet : GExp (cov := cov) hmet p (‖u‖ • ξ) = GExp (cov := cov) hmet p (‖u‖ • η) := by
    rw [hscaleu, hscalev]
    exact hG
  have hminℓ : Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (‖u‖ • ξ))
      = ENNReal.ofReal ‖u‖ := by rw [hscaleu]; exact hmin
  have hsync : ∀ t : ℝ, ‖u‖ ≤ t → t < m →
      GExp (cov := cov) hmet p (t • ξ) = GExp (cov := cov) hmet p (t • η) := by
    intro t hρt htm
    refine eq_GExp_of_minimising_pair (cov := cov) hmet htor hξ hη hξη huv0 hρt hmeet hminℓ ?_
    have hmem : t ∈ minimisingSet (I := I) hmet p ξ := by
      rw [mem_minimisingSet_iff (I := I) (cov := cov) hmet htor hξ]
      exact ⟨le_trans (norm_nonneg u) hρt, le_trans htm.le (hcut ξ hξ)⟩
    exact hmem.2
  -- (5) hence the two rays are the same geodesic on `(0, m)`
  set γ : ℝ → M := fun s : ℝ => GExp (cov := cov) hmet p (s • ξ) with hγdef
  set δ : ℝ → M := fun s : ℝ => GExp (cov := cov) hmet p (s • η) with hδdef
  have hzero : (0 : ℝ) < ‖u‖ := huv0
  have hposm : 0 < m := lt_trans huv0 hu
  have hξne : ξ ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hξ; norm_num at hξ
  have hηne : η ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hη; norm_num at hη
  have hsmγ : ContMDiffOn 𝓘(ℝ) I ∞ γ (Ioo (0 : ℝ) m) :=
    contMDiffOn_GExp_smul_Ioo (cov := cov) hmet p hξne m
  have hsmδ : ContMDiffOn 𝓘(ℝ) I ∞ δ (Ioo (0 : ℝ) m) :=
    contMDiffOn_GExp_smul_Ioo (cov := cov) hmet p hηne m
  have hgeoγ : ∀ t ∈ Ioo (0 : ℝ) m, IsGeodesicAt cov γ t :=
    fun t ht => isGeodesicAt_GExp_smul (cov := cov) hmet p hξne ht.1
  have hgeoδ : ∀ t ∈ Ioo (0 : ℝ) m, IsGeodesicAt cov δ t :=
    fun t ht => isGeodesicAt_GExp_smul (cov := cov) hmet p hηne ht.1
  have hneγ : ∀ t ∈ Ioo (0 : ℝ) m, curveVelocity (I := I) γ t ≠ 0 := by
    intro t ht h0
    have h := norm_curveVelocity_GExp_smul (cov := cov) hmet p hξne ht.1
    rw [h0, norm_zero, hξ] at h
    norm_num at h
  have hneδ : ∀ t ∈ Ioo (0 : ℝ) m, curveVelocity (I := I) δ t ≠ 0 := by
    intro t ht h0
    have h := norm_curveVelocity_GExp_smul (cov := cov) hmet p hηne ht.1
    rw [h0, norm_zero, hη] at h
    norm_num at h
  have hmid : (‖u‖ + m) / 2 ∈ Ioo (0 : ℝ) m :=
    ⟨by linarith, by linarith⟩
  have hmidρ : ‖u‖ < (‖u‖ + m) / 2 := by linarith
  have hevent : γ =ᶠ[𝓝 ((‖u‖ + m) / 2)] δ := by
    filter_upwards [isOpen_Ioo.mem_nhds (show (‖u‖ + m) / 2 ∈ Ioo ‖u‖ m from
      ⟨hmidρ, by linarith⟩)] with s hs
    exact hsync s hs.1.le hs.2
  have hpt : γ ((‖u‖ + m) / 2) = δ ((‖u‖ + m) / 2) := hevent.eq_of_nhds
  have hvel : curveVelocity (I := I) γ ((‖u‖ + m) / 2) = curveVelocity (I := I) δ ((‖u‖ + m) / 2) :=
    curveVelocity_congr_of_eventuallyEq (I := I) hevent
  have hEqOn : EqOn γ δ (Ioo (0 : ℝ) m) :=
    eqOn_Ioo_of_isGeodesicAt_of_eq hsmγ hsmδ hgeoγ hgeoδ hneγ hneδ hmid hpt hvel
  -- (6) `GExp p` is injective on a small ball (in the fibre norm), and the equality holds there
  obtain ⟨ρ, hρ, hInj⟩ := exists_pos_injAtLeast (cov := cov) hmet htor p
  set s : ℝ := min ρ m / 2 with hsdef
  have hspos : 0 < s := by
    rw [hsdef]
    have h : 0 < min ρ m := lt_min hρ hposm
    linarith
  have hsρ : s < ρ := by
    rw [hsdef]
    have h : min ρ m ≤ ρ := min_le_left _ _
    linarith
  have hsm : s < m := by
    rw [hsdef]
    have h : min ρ m ≤ m := min_le_right _ _
    linarith
  have hsmall : GExp (cov := cov) hmet p (s • ξ) = GExp (cov := cov) hmet p (s • η) :=
    hEqOn ⟨hspos, hsm⟩
  have hnξ : ‖s • ξ‖ < ρ := by
    have h : ‖s • ξ‖ = s := by rw [norm_smul, Real.norm_of_nonneg hspos.le, hξ, mul_one]
    rw [h]; exact hsρ
  have hnη : ‖s • η‖ < ρ := by
    have h : ‖s • η‖ = s := by rw [norm_smul, Real.norm_of_nonneg hspos.le, hη, mul_one]
    rw [h]; exact hsρ
  have hsne : s ≠ 0 := ne_of_gt hspos
  exact hξη (smul_right_injective (TangentSpace I p) hsne
    (hInj (s • ξ) (s • η) hnξ hnη hsmall))

/-- **The injectivity radius is the minimum of the cut times.** -/
theorem injAtLeast_iff_forall_cutTime_le (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {p : M} {m : ℝ} :
    InjAtLeast hmet p m ↔
      ∀ ξ : TangentSpace I p, ‖ξ‖ = 1 → m ≤ cutTime (I := I) hmet p ξ :=
  ⟨fun h ξ hξ => injAtLeast_le_cutTime (I := I) (cov := cov) hmet htor h hξ,
   fun h => injAtLeast_of_forall_cutTime_le (cov := cov) hmet htor h⟩

/-- The cut-time form of the failure of injectivity. -/
theorem exists_cutTime_lt_of_not_injAtLeast (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {p : M} {m : ℝ} (h : ¬ InjAtLeast hmet p m) :
    ∃ ξ : TangentSpace I p, ‖ξ‖ = 1 ∧ cutTime (I := I) hmet p ξ < m := by
  by_contra hcon
  push Not at hcon
  exact h (injAtLeast_of_forall_cutTime_le (cov := cov) hmet htor (fun ξ hξ => hcon ξ hξ))

/-! ## The sharpness of the meeting time of two minimising rays

The sync lemma (`Submission.LensSync.eq_GExp_of_minimising_pair`) says that two distinct minimising
rays which meet again *stay* together as long as either of them is minimising.  Here we draw the
sharp conclusion: they meet **exactly at their cut times**.  This is the classical statement that a
cut point reached by two minimising geodesics is reached at the cut time. -/

/-- **The meeting time of two distinct minimising rays is the cut time.** -/
theorem cutTime_eq_of_minimising_pair (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {p : M} {ξ η : TangentSpace I p} (hξ : ‖ξ‖ = 1) (hη : ‖η‖ = 1) (hne : ξ ≠ η)
    {ℓ : ℝ} (hℓ : 0 < ℓ)
    (heq : GExp (cov := cov) hmet p (ℓ • ξ) = GExp (cov := cov) hmet p (ℓ • η))
    (hminℓ : Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (ℓ • ξ)) = ENNReal.ofReal ℓ) :
    cutTime (I := I) hmet p ξ = ℓ := by
  have hmem : ℓ ∈ minimisingSet (I := I) hmet p ξ := ⟨hℓ.le, hminℓ⟩
  have hge : ℓ ≤ cutTime (I := I) hmet p ξ :=
    ((mem_minimisingSet_iff (I := I) (cov := cov) hmet htor hξ).mp hmem).2
  by_contra hcon
  have hgt : ℓ < cutTime (I := I) hmet p ξ := lt_of_le_of_ne hge (Ne.symm hcon)
  -- the two rays agree on `[ℓ, cutTime]`
  have hsync : ∀ t : ℝ, ℓ ≤ t → t ≤ cutTime (I := I) hmet p ξ →
      GExp (cov := cov) hmet p (t • ξ) = GExp (cov := cov) hmet p (t • η) := by
    intro t hℓt htτ
    refine eq_GExp_of_minimising_pair (cov := cov) hmet htor hξ hη hne hℓ hℓt heq hminℓ ?_
    have hmemt : t ∈ minimisingSet (I := I) hmet p ξ := by
      rw [mem_minimisingSet_iff (I := I) (cov := cov) hmet htor hξ]
      exact ⟨le_trans hℓ.le hℓt, htτ⟩
    exact hmemt.2
  -- hence the two rays are the same geodesic on `(0, cutTime)`
  set Mcut : ℝ := cutTime (I := I) hmet p ξ with hMdef
  have hMpos : 0 < Mcut := lt_trans hℓ hgt
  set γ : ℝ → M := fun s : ℝ => GExp (cov := cov) hmet p (s • ξ) with hγdef
  set δ : ℝ → M := fun s : ℝ => GExp (cov := cov) hmet p (s • η) with hδdef
  have hξne : ξ ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hξ; norm_num at hξ
  have hηne : η ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hη; norm_num at hη
  have hsmγ : ContMDiffOn 𝓘(ℝ) I ∞ γ (Ioo (0 : ℝ) Mcut) :=
    contMDiffOn_GExp_smul_Ioo (cov := cov) hmet p hξne Mcut
  have hsmδ : ContMDiffOn 𝓘(ℝ) I ∞ δ (Ioo (0 : ℝ) Mcut) :=
    contMDiffOn_GExp_smul_Ioo (cov := cov) hmet p hηne Mcut
  have hgeoγ : ∀ t ∈ Ioo (0 : ℝ) Mcut, IsGeodesicAt cov γ t :=
    fun t ht => isGeodesicAt_GExp_smul (cov := cov) hmet p hξne ht.1
  have hgeoδ : ∀ t ∈ Ioo (0 : ℝ) Mcut, IsGeodesicAt cov δ t :=
    fun t ht => isGeodesicAt_GExp_smul (cov := cov) hmet p hηne ht.1
  have hneγ : ∀ t ∈ Ioo (0 : ℝ) Mcut, curveVelocity (I := I) γ t ≠ 0 := by
    intro t ht h0
    have h := norm_curveVelocity_GExp_smul (cov := cov) hmet p hξne ht.1
    rw [h0, norm_zero, hξ] at h
    norm_num at h
  have hneδ : ∀ t ∈ Ioo (0 : ℝ) Mcut, curveVelocity (I := I) δ t ≠ 0 := by
    intro t ht h0
    have h := norm_curveVelocity_GExp_smul (cov := cov) hmet p hηne ht.1
    rw [h0, norm_zero, hη] at h
    norm_num at h
  have hmid : (ℓ + Mcut) / 2 ∈ Ioo (0 : ℝ) Mcut := ⟨by linarith, by linarith⟩
  have hevent : γ =ᶠ[𝓝 ((ℓ + Mcut) / 2)] δ := by
    filter_upwards [isOpen_Ioo.mem_nhds (show (ℓ + Mcut) / 2 ∈ Ioo ℓ Mcut from
      ⟨by linarith, by linarith⟩)] with s hs
    exact hsync s hs.1.le (le_of_lt hs.2)
  have hpt : γ ((ℓ + Mcut) / 2) = δ ((ℓ + Mcut) / 2) := hevent.eq_of_nhds
  have hvel : curveVelocity (I := I) γ ((ℓ + Mcut) / 2) = curveVelocity (I := I) δ ((ℓ + Mcut) / 2) :=
    curveVelocity_congr_of_eventuallyEq (I := I) hevent
  have hEqOn : EqOn γ δ (Ioo (0 : ℝ) Mcut) :=
    eqOn_Ioo_of_isGeodesicAt_of_eq hsmγ hsmδ hgeoγ hgeoδ hneγ hneδ hmid hpt hvel
  -- injectivity on a small ball forces the two directions (and hence the two vectors) to agree
  obtain ⟨ρ, hρ, hInj⟩ := exists_pos_injAtLeast (cov := cov) hmet htor p
  set s : ℝ := min ρ Mcut / 2 with hsdef
  have hspos : 0 < s := by
    rw [hsdef]
    have h : 0 < min ρ Mcut := lt_min hρ hMpos
    linarith
  have hsρ : s < ρ := by
    rw [hsdef]
    have h : min ρ Mcut ≤ ρ := min_le_left _ _
    linarith
  have hsM : s < Mcut := by
    rw [hsdef]
    have h : min ρ Mcut ≤ Mcut := min_le_right _ _
    linarith
  have hsmall : GExp (cov := cov) hmet p (s • ξ) = GExp (cov := cov) hmet p (s • η) :=
    hEqOn ⟨hspos, hsM⟩
  have hnξ : ‖s • ξ‖ < ρ := by
    have h : ‖s • ξ‖ = s := by rw [norm_smul, Real.norm_of_nonneg hspos.le, hξ, mul_one]
    rw [h]; exact hsρ
  have hnη : ‖s • η‖ < ρ := by
    have h : ‖s • η‖ = s := by rw [norm_smul, Real.norm_of_nonneg hspos.le, hη, mul_one]
    rw [h]; exact hsρ
  exact hne (smul_right_injective (TangentSpace I p) (ne_of_gt hspos)
    (hInj (s • ξ) (s • η) hnξ hnη hsmall))

/-- **Both cut times equal the meeting time.** -/
theorem cutTime_eq_cutTime_of_minimising_pair (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {p : M} {ξ η : TangentSpace I p} (hξ : ‖ξ‖ = 1) (hη : ‖η‖ = 1) (hne : ξ ≠ η)
    {ℓ : ℝ} (hℓ : 0 < ℓ)
    (heq : GExp (cov := cov) hmet p (ℓ • ξ) = GExp (cov := cov) hmet p (ℓ • η))
    (hminℓ : Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (ℓ • ξ)) = ENNReal.ofReal ℓ) :
    cutTime (I := I) hmet p ξ = ℓ ∧ cutTime (I := I) hmet p η = ℓ :=
  ⟨cutTime_eq_of_minimising_pair (cov := cov) hmet htor hξ hη hne hℓ heq hminℓ,
   cutTime_eq_of_minimising_pair (cov := cov) hmet htor hη hξ (Ne.symm hne) hℓ heq.symm
     (by rw [← heq]; exact hminℓ)⟩

/-- **The witness-pair form of the sharpness.**  If `u ≠ v` are two minimising vectors of the same
norm `ℓ` with the same image, then the *unit directions* of `u` and `v` have cut time exactly `ℓ`:
a minimising lens always ends at the cut time of its two geodesics.

In particular, applied to the two minimising vectors of norm `inj(p)` produced by the cut-point step,
this shows that the injectivity radius **is attained as a cut time**. -/
theorem cutTime_eq_of_witness_pair (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {p : M} {u v : TangentSpace I p} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hnu : ‖u‖ = ℓ) (hnv : ‖v‖ = ℓ) (huv : u ≠ v)
    (hG : GExp (cov := cov) hmet p u = GExp (cov := cov) hmet p v)
    (hminu : Manifold.riemannianEDist I p (GExp (cov := cov) hmet p u) = ENNReal.ofReal ℓ) :
    cutTime (I := I) hmet p (unitOf u (norm_pos_iff.mp (by rw [hnu]; exact hℓ))) = ℓ ∧
    cutTime (I := I) hmet p (unitOf v (norm_pos_iff.mp (by rw [hnv]; exact hℓ))) = ℓ := by
  have hu0 : u ≠ 0 := by rw [← norm_pos_iff, hnu]; exact hℓ
  have hv0 : v ≠ 0 := by rw [← norm_pos_iff, hnv]; exact hℓ
  have hξ : ‖unitOf u hu0‖ = 1 := unitOf_norm u hu0
  have hη : ‖unitOf v hv0‖ = 1 := unitOf_norm v hv0
  have hξu : ℓ • unitOf u hu0 = u := by
    show ℓ • unitOf u hu0 = u
    rw [unitOf, smul_smul, ← hnu, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hu0), one_smul]
  have hηv : ℓ • unitOf v hv0 = v := by
    show ℓ • unitOf v hv0 = v
    rw [unitOf, smul_smul, ← hnv, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv0), one_smul]
  have hne : unitOf u hu0 ≠ unitOf v hv0 := by
    intro h
    exact huv (by rw [← hξu, ← hηv, h])
  have heq : GExp (cov := cov) hmet p (ℓ • unitOf u hu0)
      = GExp (cov := cov) hmet p (ℓ • unitOf v hv0) := by rw [hξu, hηv]; exact hG
  have hminℓ : Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (ℓ • unitOf u hu0))
      = ENNReal.ofReal ℓ := by rw [hξu]; exact hminu
  exact cutTime_eq_cutTime_of_minimising_pair (cov := cov) hmet htor hξ hη hne hℓ heq hminℓ


/-- **Continuity of a fixed-time slice of the exponential map**, below the injectivity radius: if
`ξₙ → ξ₀` and `‖t • ξ₀‖ ≤ m` with `InjAtLeast hmet p m`, then `GExp p (t • ξₙ) → GExp p (t • ξ₀)`.

This packages `GExpBoundary.tendsto_GExp_of_tendsto_of_norm_le` in the form needed for propagation
arguments along a ray (the slice `t` is fixed, only the direction varies). -/
theorem tendsto_GExp_smul_of_tendsto (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {p : M} {m : ℝ} (hinj : InjAtLeast hmet p m)
    {ξ : ℕ → TangentSpace I p} {ξ₀ : TangentSpace I p} (hξ : Tendsto ξ atTop (𝓝 ξ₀))
    {t : ℝ} (ht : ‖t • ξ₀‖ ≤ m) :
    Tendsto (fun n : ℕ => GExp (cov := cov) hmet p (t • ξ n)) atTop
      (𝓝 (GExp (cov := cov) hmet p (t • ξ₀))) :=
  Submission.GExpBoundary.tendsto_GExp_of_tendsto_of_norm_le (cov := cov) hmet htor hinj
    (tendsto_const_nhds.smul hξ) ht


/-- **The initial velocity of the reversed curve** `s ↦ γ(T - s)`: it is `(-1) • γ̇(T)`.  (The
scalar form `(-1) • ·` is kept rather than the negation because the `SMul` on `TangentSpace I x` is
the `RiemannianBundle` instance, for which `neg_one_smul` does not apply.) -/
theorem revVelocity (hmet : IsMetricCompatible cov) {a b T : ℝ} (ha : a < 0) (hT : 0 < T)
    (hTb : T < b) {γ : ℝ → M} (hsm : ContMDiffOn 𝓘(ℝ) I ∞ γ (Ioo a b)) :
    curveVelocity (I := I) (fun s : ℝ => γ (T - s)) 0
      = (-1 : ℝ) • curveVelocity (I := I) γ T := by
  have hTmem : T ∈ Ioo a b := ⟨lt_trans ha hT, hTb⟩
  have hmd : MDifferentiableAt 𝓘(ℝ) I γ T :=
    (hsm.contMDiffAt (isOpen_Ioo.mem_nhds hTmem)).mdifferentiableAt (by simp)
  have hev : (fun s : ℝ => γ (T - s)) =ᶠ[𝓝 (0 : ℝ)] (fun s : ℝ => γ ((-1 : ℝ) * s + T)) :=
    Filter.Eventually.of_forall (fun s => by
      show γ (T - s) = γ ((-1 : ℝ) * s + T)
      rw [show (-1 : ℝ) * s + T = T - s from by ring])
  have h2 := Submission.Length.curveVelocity_comp_mul_add (I := I) (γ := γ) (c := -1) (d := T)
    (t := 0) (by simpa using hmd)
  have h3 : (-1 : ℝ) • curveVelocity (I := I) γ ((-1 : ℝ) * 0 + T)
      = (-1 : ℝ) • curveVelocity (I := I) γ T := by
    rw [show (-1 : ℝ) * 0 + T = T from by ring]
  exact (curveVelocity_congr_of_eventuallyEq (I := I) hev).trans (h2.trans h3)


/-- **Norm of `(-1) • v`.** -/
theorem norm_neg_one_smul_tangent {x : M} (v : TangentSpace I x) :
    ‖(-1 : ℝ) • v‖ = ‖v‖ := by
  simp

/-- **Norm of the negative of a tangent vector.**  (`norm_neg` does not apply to the
`RiemannianBundle` norm instance; `simp` does.) -/
theorem norm_neg_tangent {x : M} (v : TangentSpace I x) : ‖-v‖ = ‖v‖ := by
  have h : (-1 : ℝ) • v = -v := by simp
  rw [← h]
  exact norm_neg_one_smul_tangent v


/-! ## A geodesic loop bounds the injectivity radius (pointwise at the midpoint)

`Submission/InjRadius.two_mul_le_of_injAllAtLeast_of_geodCurve_loop` proves that a geodesic loop of
length `T` forces `2 inj(M) ≤ T`, using injectivity of the exponential map at the **midpoint** of the
loop.  Here is the same argument with the *pointwise* hypothesis at the midpoint only, which is the
form the structure theorem needs (no uniformity in the base point). -/

/-- **A geodesic loop bounds the injectivity radius at its midpoint.** -/
theorem two_mul_le_of_injAtLeast_midpoint
    (hmet : IsMetricCompatible cov) {x : M} {ξ : TangentSpace I x} (hξ : ‖ξ‖ = 1)
    {T : ℝ} (hT : 0 ≤ T) (hTpos : 0 < T)
    (hloop : (geodCurve (cov := cov) hmet T hT x ξ hξ) T = x)
    {r : ℝ}
    (h : InjAtLeast hmet ((geodCurve (cov := cov) hmet T hT x ξ hξ) (T / 2)) r) :
    2 * r ≤ T := by
  classical
  by_cases hr : r ≤ 0
  · linarith
  have hrpos : 0 < r := not_le.mp hr
  by_contra hcon
  rw [not_le] at hcon
  have hhalf_nn : 0 ≤ T / 2 := by linarith
  have hhalf_le : T / 2 ≤ T := by linarith
  have hhalf_lt : T / 2 < r := by linarith
  have hδ := geodDelta_pos (cov := cov) hmet
  have hmid_mem : T / 2 ∈ Ioo (-(geodDelta (cov := cov) hmet))
      (T + geodDelta (cov := cov) hmet) :=
    Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩
  set G : ℝ → M := geodCurve (cov := cov) hmet T hT x ξ hξ with hGdef
  have hspec := geodCurve_spec (cov := cov) hmet T hT x ξ hξ
  have hG0 : G 0 = x := by rw [hGdef]; exact hspec.1
  have hGT : G T = x := by rw [hGdef]; exact hloop
  have hGsp : ‖curveVelocity (I := I) G (T / 2)‖ = 1 := by
    rw [hGdef]; exact hspec.2.2.2.2 (T / 2) hmid_mem
  have hfwd : GExp (cov := cov) hmet (G (T / 2))
      ((T / 2) • curveVelocity (I := I) G (T / 2)) = G T := by
    rw [hGdef]
    have hh := GExp_geodCurve_add (cov := cov) hmet x hξ hT (t := T / 2) (s := T / 2)
      hhalf_nn hhalf_le hhalf_nn (le_of_eq (by ring : T / 2 + T / 2 = T))
    rw [show T / 2 + T / 2 = T from by ring] at hh
    exact hh
  have hbwd : GExp (cov := cov) hmet (G (T / 2))
      ((-(T / 2)) • curveVelocity (I := I) G (T / 2)) = G 0 := by
    rw [hGdef]
    have hh := GExp_neg_smul_curveVelocity_geodCurve (cov := cov) hmet x hξ hT
      (t := T / 2) (s := T / 2) hhalf_nn hhalf_le hhalf_nn (le_refl (T / 2))
    rw [show T / 2 - T / 2 = 0 from by ring] at hh
    exact hh
  have hu1 : ‖(T / 2) • curveVelocity (I := I) G (T / 2)‖ < r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hhalf_nn, hGsp, mul_one]
    exact hhalf_lt
  have hu2 : ‖(-(T / 2)) • curveVelocity (I := I) G (T / 2)‖ < r := by
    rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hhalf_nn, hGsp, mul_one]
    exact hhalf_lt
  have heq : (T / 2) • curveVelocity (I := I) G (T / 2)
      = (-(T / 2)) • curveVelocity (I := I) G (T / 2) := by
    refine h _ _ hu1 hu2 ?_
    rw [hfwd, hbwd, hGT, hG0]
  have hz : curveVelocity (I := I) G (T / 2) = 0 := by
    have hsub : ((T / 2) - (-(T / 2))) • curveVelocity (I := I) G (T / 2) = 0 := by
      rw [sub_smul, heq, sub_self]
    rw [show (T / 2) - (-(T / 2)) = T from by ring] at hsub
    exact (smul_eq_zero.mp hsub).resolve_left (ne_of_gt hTpos)
  rw [hz, norm_zero] at hGsp
  norm_num at hGsp

/-- **Norm of `0` in a tangent space.**  (`rw [norm_zero]` does not fire on the `RiemannianBundle`
norm instance; `simp` does.) -/
theorem norm_zero_tangent {x : M} : ‖(0 : TangentSpace I x)‖ = 0 := by
  simp

/-- **Transporting a tangent vector along an equality of base points does not change it.**  (The
`TangentSpace I x` are all the same type `E`; only the instances depend on `x`.) -/
theorem cast_tangent_eq {x y : M} (h : x = y) (w : TangentSpace I x) : h ▸ w = w := by
  cases h
  rfl

/-- **Norm is preserved by transporting a tangent vector along an equality of base points.** -/
theorem norm_cast_tangent {x y : M} (h : x = y) (w : TangentSpace I x) :
    ‖(h ▸ w)‖ = ‖w‖ := by
  cases h
  rfl

/-- **The exponential map is preserved by transporting a tangent vector along an equality of base
points.** -/
theorem GExp_cast_tangent (hmet : IsMetricCompatible cov) {x y : M} (h : x = y)
    (w : TangentSpace I x) :
    GExp (cov := cov) hmet y (h ▸ w) = GExp (cov := cov) hmet x w := by
  cases h
  rfl

/-- **A geodesic loop bounds the injectivity radius at its base point.**  Let `γ` be a unit-speed
geodesic on `Ioo a b ∋ [0,T]` with `γ 0 = γ T` (a loop), whose initial velocity is not the initial
velocity of the reversed curve (**the loop does not reverse at the base point**).  Then
`InjAtLeast hmet (γ 0) r` forces `2r ≤ T`.

The two witness vectors live at the *base point*: `u = (T/2) • γ̇(0)`, and
`v =` the transport of `(T/2) • curveVelocity (fun s => γ (T - s)) 0` along `γ (T - 0) = γ 0`; both
have norm `T/2` and both map to `γ(T/2)` (the first by the ray identity for `γ`, the second by the
ray identity for the reversed curve plus `GExp_cast_tangent`).  See `two_mul_le_of_injAtLeast_midpoint`
for the (uniform-hypothesis-free) midpoint version, which needs no transport. -/
theorem two_mul_le_of_isGeodesicAt_loop
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {a b T r : ℝ} (ha : a < 0) (hT : 0 < T) (hTb : T < b)
    {γ : ℝ → M} (hsm : ContMDiffOn 𝓘(ℝ) I ∞ γ (Ioo a b))
    (hgeo : ∀ t ∈ Ioo a b, IsGeodesicAt cov γ t)
    (hne : ∀ t ∈ Ioo a b, curveVelocity (I := I) γ t ≠ 0)
    (hspeed : ∀ t ∈ Ioo a b, ‖curveVelocity (I := I) γ t‖ = 1)
    (hloop : γ T = γ 0)
    (hbase : γ (T - 0) = γ 0)
    (hvelne : (T / 2) • curveVelocity (I := I) γ 0
      ≠ hbase ▸ ((T / 2) • curveVelocity (I := I) (fun s : ℝ => γ (T - s)) 0))
    (hinj : InjAtLeast hmet (γ 0) r) :
    2 * r ≤ T := by
  by_contra hcon
  rw [not_le] at hcon
  have hhalf : T / 2 < r := by linarith
  have hbpos : 0 < b := lt_trans hT hTb
  have h0mem : (0 : ℝ) ∈ Ioo a b := ⟨ha, hbpos⟩
  have hTmem : T ∈ Ioo a b := ⟨lt_trans ha hT, hTb⟩
  have hb0 : T - b < 0 := by linarith
  have h0a : 0 < T - a := by linarith
  -- the reversed curve
  have hrev_sm : ContMDiffOn 𝓘(ℝ) I ∞ (fun s : ℝ => γ (T - s)) (Ioo (T - b) (T - a)) := by
    have hneg : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ) ∞ (fun s : ℝ => T - s) (Ioo (T - b) (T - a)) := by
      have h : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ) ∞ (fun s : ℝ => T + (-1 : ℝ) * s) (Ioo (T - b) (T - a)) :=
        (contMDiff_const.add (contMDiff_const.mul contMDiff_id)).contMDiffOn
      have hfun : (fun s : ℝ => T + (-1 : ℝ) * s) = fun s : ℝ => T - s := by
        funext s; ring
      rwa [hfun] at h
    exact hsm.comp hneg (fun s hs => ⟨by linarith [hs.2], by linarith [hs.1]⟩)
  have hmem' : ∀ t ∈ Ioo (T - b) (T - a), (-1 : ℝ) * t + T ∈ Ioo a b := by
    intro t ht
    exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hrev_geo : ∀ t ∈ Ioo (T - b) (T - a), IsGeodesicAt cov (fun s : ℝ => γ (T - s)) t := by
    intro t ht
    have h := isGeodesicAt_comp_affine (cov := cov) (σ := γ) (c := a) (d := b) (a := -1) (b := T)
      (by norm_num) hsm hgeo (by simpa using hmem' t ht)
    simpa [sub_eq_add_neg, add_comm, mul_comm] using h
  have hrev_norm : ∀ t ∈ Ioo (T - b) (T - a),
      ‖curveVelocity (I := I) (fun s : ℝ => γ (T - s)) t‖ = 1 := by
    intro t ht
    have hmd : MDifferentiableAt 𝓘(ℝ) I γ ((-1 : ℝ) * t + T) :=
      (hsm.contMDiffAt (isOpen_Ioo.mem_nhds (hmem' t ht))).mdifferentiableAt (by simp)
    have h2 := Submission.Length.curveVelocity_comp_mul_add (I := I) (γ := γ) (c := -1) (d := T)
      (t := t) hmd
    have h3 : (-1 : ℝ) • curveVelocity (I := I) γ ((-1 : ℝ) * t + T)
        = (-1 : ℝ) • curveVelocity (I := I) γ (T - t) := by
      rw [show (-1 : ℝ) * t + T = T - t from by ring]
    have hev : (fun s : ℝ => γ (T - s)) =ᶠ[𝓝 t] (fun s : ℝ => γ ((-1 : ℝ) * s + T)) :=
      Filter.Eventually.of_forall (fun s => by
        show γ (T - s) = γ ((-1 : ℝ) * s + T)
        rw [show (-1 : ℝ) * s + T = T - s from by ring])
    rw [(curveVelocity_congr_of_eventuallyEq (I := I) hev).trans (h2.trans h3),
      norm_neg_one_smul_tangent]
    exact hspeed (T - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hVne : curveVelocity (I := I) (fun s : ℝ => γ (T - s)) 0 ≠ 0 := by
    intro hzero
    have h' : (1 : ℝ) = 0 := by
      have h := hrev_norm 0 ⟨hb0, h0a⟩
      rw [hzero] at h
      rw [norm_zero_tangent] at h
      exact h.symm
    norm_num at h'
  -- the two witness vectors at the base point
  set w : TangentSpace I (γ (T - 0)) :=
    (T / 2) • curveVelocity (I := I) (fun s : ℝ => γ (T - s)) 0 with hwdef
  set u : TangentSpace I (γ 0) := (T / 2) • curveVelocity (I := I) γ 0 with hudef
  set v : TangentSpace I (γ 0) := hbase ▸ w with hvdef
  -- the ray identity for `γ`
  have hγ : ∀ t ∈ Icc (0 : ℝ) T,
      γ t = GExp (cov := cov) hmet (γ 0) (t • curveVelocity (I := I) γ 0) :=
    eqOn_Icc_GExp_of_isGeodesicAt (cov := cov) (p := γ 0) hmet (hne 0 h0mem)
      ha hT.le hTb hsm hgeo hne rfl rfl
  -- the ray identity for the reversed curve, at its own base point `γ (T - 0)`
  have hrev : ∀ t ∈ Icc (0 : ℝ) T,
      γ (T - t) = GExp (cov := cov) hmet (γ (T - 0))
        (t • curveVelocity (I := I) (fun s : ℝ => γ (T - s)) 0) := by
    have h := eqOn_Icc_GExp_of_isGeodesicAt (cov := cov) (p := γ (T - 0)) hmet hVne hb0 hT.le
      (by linarith : T < T - a) hrev_sm hrev_geo
      (fun t ht hzero => by
        have h' : (1 : ℝ) = 0 := by
          have hh := hrev_norm t ht
          rw [hzero] at hh
          rw [norm_zero_tangent] at hh
          exact hh.symm
        norm_num at h')
      (by show γ (T - 0) = γ (T - 0); rfl) rfl
    intro t ht
    exact h t ht
  -- the two images
  have hT2 : T / 2 ∈ Icc (0 : ℝ) T := ⟨by linarith, by linarith⟩
  have hGu : GExp (cov := cov) hmet (γ 0) u = γ (T / 2) := by
    rw [hudef]
    exact (hγ (T / 2) hT2).symm
  have hGv : GExp (cov := cov) hmet (γ 0) v = γ (T / 2) := by
    rw [hvdef, GExp_cast_tangent]
    have h := hrev (T / 2) hT2
    rw [show T - T / 2 = T / 2 from by ring] at h
    exact h.symm
  -- the norms
  have hu : ‖u‖ = T / 2 := by
    rw [hudef, norm_smul, hspeed 0 h0mem, mul_one, Real.norm_of_nonneg (by linarith)]
  have hv : ‖v‖ = T / 2 := by
    rw [hvdef, norm_cast_tangent, norm_smul, hrev_norm 0 ⟨hb0, h0a⟩, mul_one,
      Real.norm_of_nonneg (by linarith)]
  -- distinctness
  have huv : u ≠ v := by
    rw [hudef, hvdef, hwdef]
    exact hvelne
  exact huv (hinj u v (by rw [hu]; exact hhalf) (by rw [hv]; exact hhalf) (by rw [hGu, hGv]))

end

end Submission.InjRadiusCut
