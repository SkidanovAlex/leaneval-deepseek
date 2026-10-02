import Mathlib
import Submission.Work.PTGeometric.SourceRegionPhiInterior
import Submission.Work.PTGeometric.SourceZero
import Submission.Work.PTGeometric.SourceFamily
import Submission.Work.PTGeometric.exists_coreDefiningFunction
import Submission.Work.PTGeometric.sourceRegionPhiFn_false
import Submission.Work.PTGeometric.exists_sourceDefiningFunction
import Submission.Work.PTGeometric.exists_regular_shift
import Submission.Work.PTGeometric.exists_regular_shift_surj
import Submission.Work.PTGeometric.mfderiv_sourceRegionPhi_boundary
import Submission.Work.PTGeometric.mfderiv_flat_of_ray
import Submission.Work.PTGeometric.mem_sourceZeroSet_of_collarRay
import Submission.Work.PTGeometric.isSubmersionAt_of_surjective_mfderiv_real

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# PTGEOMETRIC: the defining function of the source region, with submersivity at the *interior* zeros

This file proves `Work.PTGeometric.exists_sourceRegionPhiInterior`: for a genuine tube geometry `G`,
a multiplicity `m` with `(∏ i, tubeAlpha (G.rep i)) ^ m = 1`, and a *closed* set `T` disjoint from the
zero set `Z = sourceZeroSet G m hpow`, there is a `C^∞` function `Φ` on the half-space with

1. `Z ⊆ {Φ ≤ 0}` and `{Φ ≤ 0} ∩ T = ∅` and `{Φ ≤ 0}` compact,
2. `Z ∩ {Φ = 0} ⊆ ∂A`,
3. `IsSubmersionAt Φ x` at every *interior* zero `x`,
4. at every *boundary* zero `x`, `mfderiv Φ x = c • mfderiv (boundary chart coordinate) x` with
   `c < 0` (the one-sided/tangency clause).

## The construction

Let `ρ` be the smooth Urysohn function of the pair `(Z, T)` from
`Work.PTGeometric.exists_sourceDefiningFunction` (`ρ = 0` exactly on `Z`, `ρ ≥ 1` on `T`, `ρ ≥ 1` off
a compact set `K`), and put

  `Φ x := ρ x - srPsi (x.1 0) - s * srChi (x.1 0)`,

where

* `srPsi t = t / (1 + t ^ 2)`: nonnegative on `t ≥ 0`, vanishing exactly at `t = 0`, with
  `deriv srPsi 0 = 1` (this supplies the strictly negative normal derivative `-1` at a boundary
  zero: `Φ = ρ` on the boundary, so the boundary zeros are exactly `Z ∩ ∂A = {u | u ∈ B}` and the
  tangential part of `dΦ` vanishes because `ρ` is locally flat there, cf.
  `Work.PTGeometric.mfderiv_flat_of_ray` and `Work.PTGeometric.mfderiv_sourceRegionPhi_boundary`);
* `srChi t = t ^ 2 / (1 + t ^ 2) ^ 2`: nonnegative, vanishing exactly at `t = 0`, with
  `deriv srChi 0 = 0` — its coefficient `s` is chosen so that the level `0` of
  `x ↦ (ρ x - srPsi (x.1 0)) - s * srChi (x.1 0)` is *regular* on the interior.  This is the
  parametric Sard statement `Work.PTGeometric.exists_regular_shift` (a transfer of
  `.../TransversalApproximation/badSetEuclid.lean`): the set of `s` admitting a critical interior zero
  is Lebesgue-null, hence there is a good `s` in `(0, 1/8)`.

## Main result

* `Work.PTGeometric.exists_sourceRegionPhiInterior`
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter

namespace Work.PTGeometric

noncomputable section

open Work.ThomBordism
open Work.ThomBordism.PontryaginThom

variable {k : ℕ} {D : ThomTarget k} {ι : Type} [Fintype ι] {Fam : ι → Man8}

/-! ## The two profiles and their elementary properties -/

/-- The tangential profile `t ↦ t / (1 + t²)`. -/
def srPsi (t : ℝ) : ℝ := t / (1 + t ^ 2)

/-- The shift profile `t ↦ t² / (1 + t²)²`. -/
def srChi (t : ℝ) : ℝ := t ^ 2 / (1 + t ^ 2) ^ 2

theorem contDiff_srPsi : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) srPsi := by
  unfold srPsi
  exact contDiff_id.div (by fun_prop) (fun t => by positivity)

theorem contDiff_srChi : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) srChi := by
  unfold srChi
  exact (contDiff_id.pow 2).div
    ((by fun_prop : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => 1 + t ^ 2)).pow 2)
    (fun t => by positivity)

theorem srPsi_zero : srPsi 0 = 0 := by simp [srPsi]

theorem srChi_zero : srChi 0 = 0 := by simp [srChi]

theorem srPsi_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ srPsi t := by
  unfold srPsi
  exact div_nonneg ht (by positivity)

theorem srChi_nonneg (t : ℝ) : 0 ≤ srChi t := by
  unfold srChi
  exact div_nonneg (sq_nonneg t) (by positivity)

theorem srChi_pos {t : ℝ} (ht : t ≠ 0) : 0 < srChi t := by
  simp only [srChi]
  positivity

theorem srChi_eq_zero {t : ℝ} : srChi t = 0 ↔ t = 0 := by
  constructor
  · intro h
    have hnum : t ^ 2 = 0 := by
      have hden : (1 + t ^ 2) ^ 2 ≠ 0 := by positivity
      have h1 : t ^ 2 / (1 + t ^ 2) ^ 2 = 0 := h
      rcases div_eq_zero_iff.mp h1 with h2 | h2
      · exact h2
      · exact absurd h2 hden
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hnum
  · rintro rfl
    simp [srChi]

theorem srPsi_eq_zero {t : ℝ} (ht : 0 ≤ t) : srPsi t = 0 ↔ t = 0 := by
  constructor
  · intro h
    have hden : (1 : ℝ) + t ^ 2 ≠ 0 := by positivity
    have h1 : t / (1 + t ^ 2) = 0 := h
    have h2 : t = 0 := by
      rcases div_eq_zero_iff.mp h1 with h3 | h3
      · exact h3
      · exact absurd h3 hden
    exact h2
  · rintro rfl
    simp [srPsi]

theorem srPsi_le_half {t : ℝ} (ht : 0 ≤ t) : srPsi t ≤ 1 / 2 := by
  have hpos : (0:ℝ) < 1 + t^2 := by positivity
  rw [srPsi, div_le_iff₀ hpos]
  nlinarith [sq_nonneg (t - 1)]

theorem srChi_le_quarter (t : ℝ) : srChi t ≤ 1 / 4 := by
  have hpos : (0:ℝ) < (1 + t^2)^2 := by positivity
  rw [srChi, div_le_iff₀ hpos]
  nlinarith [sq_nonneg (t^2 - 1)]

theorem deriv_srPsi_zero : deriv srPsi 0 = 1 := by
  have hsq : HasDerivAt (fun t : ℝ => t ^ 2) 0 0 := by
    have h : HasDerivAt ((id : ℝ → ℝ) ^ 2) (↑2 * (id 0) ^ (2 - 1) * 1) 0 :=
      (hasDerivAt_id (0 : ℝ)).pow 2
    convert h using 1
    all_goals first | simp | (funext t; simp)
  have hnum : HasDerivAt (fun t : ℝ => t) 1 0 := hasDerivAt_id 0
  have hden : HasDerivAt (fun t : ℝ => 1 + t ^ 2) 0 0 := by
    have h : HasDerivAt ((fun _ : ℝ => (1 : ℝ)) + fun t : ℝ => t ^ 2) (0 + 0) 0 :=
      (hasDerivAt_const (0 : ℝ) (1 : ℝ)).add hsq
    convert h using 1
    all_goals first | simp | (funext t; simp)
  have hdiv := hnum.div hden (by norm_num : (1 + (0 : ℝ) ^ 2) ≠ 0)
  have hval : (1 * (1 + (0 : ℝ) ^ 2) - 0 * 0) / (1 + (0 : ℝ) ^ 2) ^ 2 = 1 := by norm_num
  rw [hval] at hdiv
  have hfun : srPsi = (fun t : ℝ => t) / (fun t : ℝ => 1 + t ^ 2) := by
    funext t; simp [srPsi, Pi.div_apply]
  rw [hfun]
  exact hdiv.deriv

theorem deriv_srChi_zero : deriv srChi 0 = 0 := by
  have hsq : HasDerivAt (fun t : ℝ => t ^ 2) 0 0 := by
    have h : HasDerivAt ((id : ℝ → ℝ) ^ 2) (↑2 * (id 0) ^ (2 - 1) * 1) 0 :=
      (hasDerivAt_id (0 : ℝ)).pow 2
    convert h using 1
    all_goals first | simp | (funext t; simp)
  have hbase : HasDerivAt (fun t : ℝ => 1 + t ^ 2) 0 0 := by
    have h : HasDerivAt ((fun _ : ℝ => (1 : ℝ)) + fun t : ℝ => t ^ 2) (0 + 0) 0 :=
      (hasDerivAt_const (0 : ℝ) (1 : ℝ)).add hsq
    convert h using 1
    all_goals first | simp | (funext t; simp)
  have hsq2 : HasDerivAt (fun t : ℝ => (1 + t ^ 2) ^ 2) 0 0 := by
    have h : HasDerivAt (((fun t : ℝ => 1 + t ^ 2)) ^ 2)
        (↑2 * ((fun t : ℝ => 1 + t ^ 2) 0) ^ (2 - 1) * 0) 0 := hbase.pow 2
    convert h using 1
    all_goals first | simp | (funext t; simp)
  have hdiv := hsq.div hsq2 (by norm_num : ((1 + (0 : ℝ) ^ 2) ^ 2) ≠ 0)
  have hval : (0 * (1 + (0 : ℝ) ^ 2) ^ 2 - (0 : ℝ) ^ 2 * 0) / ((1 + (0 : ℝ) ^ 2) ^ 2) ^ 2 = 0 := by
    norm_num
  rw [hval] at hdiv
  have hfun : srChi = (fun t : ℝ => t ^ 2) / (fun t : ℝ => (1 + t ^ 2) ^ 2) := by
    funext t; simp [srChi, Pi.div_apply]
  rw [hfun]
  exact hdiv.deriv

/-! ## The main theorem -/

theorem exists_sourceRegionPhiInterior {k : ℕ} {D : Work.ThomBordism.PontryaginThom.ThomTarget k}
    {ι : Type} [Fintype ι] {Fam : ι → Work.ThomBordism.Man8}
    (G : Work.PTGeometric.GenuineTubeGeometry k D ι Fam) (m : ℕ)
    (hpow : (∏ i, Work.PTGeometric.tubeAlpha (G.rep i)) ^ m = 1)
    (T : Set (EuclideanHalfSpace ((8 + k) + 1))) (hTcl : IsClosed T)
    (hdisj : Disjoint (Work.PTGeometric.sourceZeroSet G m hpow) T) :
    Work.PTGeometric.SourceRegionPhiInterior k (Work.PTGeometric.sourceZeroSet G m hpow) T := by
  haveI : NeZero ((8 + k) + 1) := ⟨by omega⟩
  obtain ⟨ρ, hρsm, hρ0, hρzero, hρT, K, hKc, hK⟩ :=
    Work.PTGeometric.exists_sourceDefiningFunction ((8 + k) + 1)
      (Work.PTGeometric.sourceZeroSet G m hpow) T
      (Work.PTGeometric.isClosed_sourceZeroSet G m hpow)
      (Work.PTGeometric.isCompact_sourceZeroSet G m hpow) hTcl hdisj
  obtain ⟨s, hs, hsreg⟩ :=
    Work.PTGeometric.exists_regular_shift_surj ρ hρsm hρ0 srPsi contDiff_srPsi srChi contDiff_srChi
      srChi_nonneg (fun t ht => srChi_pos (ne_of_gt ht)) 1 one_pos (1 / 8) (by norm_num)
  have hs0 : 0 < s := hs.1
  have hs8 : s < 1 / 8 := hs.2
  have hcoord : ContMDiff (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : EuclideanHalfSpace ((8 + k) + 1) => x.1 0) := by
    have h := (𝓡∂ ((8 + k) + 1)).contMDiff (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
    have h2 := (PiLp.proj 2 (fun _ : Fin ((8 + k) + 1) => ℝ) 0 :
        EuclideanSpace ℝ (Fin ((8 + k) + 1)) →L[ℝ] ℝ).contMDiff
        (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
    exact h2.comp h
  have h1 : ContMDiff (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞)
      ((fun _ : EuclideanHalfSpace ((8 + k) + 1) => (1 : ℝ))
        * (srPsi ∘ fun x : EuclideanHalfSpace ((8 + k) + 1) => x.1 0)) :=
    (contMDiff_const (c := (1 : ℝ))).mul
      ((contDiff_srPsi.contMDiff (n := ((⊤ : ℕ∞) : WithTop ℕ∞))).comp hcoord)
  have h2 : ContMDiff (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞)
      ((fun _ : EuclideanHalfSpace ((8 + k) + 1) => s)
        * (srChi ∘ fun x : EuclideanHalfSpace ((8 + k) + 1) => x.1 0)) :=
    (contMDiff_const (c := s)).mul
      ((contDiff_srChi.contMDiff (n := ((⊤ : ℕ∞) : WithTop ℕ∞))).comp hcoord)
  have hΦsm : ContMDiff (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : EuclideanHalfSpace ((8 + k) + 1) =>
        ρ x - 1 * srPsi (x.1 0) - s * srChi (x.1 0)) := by
    have h3 := (hρsm.sub h1).sub h2
    convert h3 using 2 with x
    simp only [Pi.sub_apply, Pi.mul_apply, Function.comp_apply]
  have hbound : ∀ x : EuclideanHalfSpace ((8 + k) + 1),
      1 * srPsi (x.1 0) + s * srChi (x.1 0) ≤ 1 / 2 + (1 / 8) * (1 / 4) := by
    intro x
    have h1 := srPsi_le_half (t := x.1 0) x.2
    have h2 := srChi_le_quarter (x.1 0)
    have h3 := srChi_nonneg (x.1 0)
    nlinarith [hs0, hs8]
  have hkey : ∀ x : EuclideanHalfSpace ((8 + k) + 1),
      ρ x - 1 * srPsi (x.1 0) - s * srChi (x.1 0) ≤ 0 → ρ x < 1 := by
    intro x hx
    have := hbound x
    linarith
  refine ⟨fun x => ρ x - 1 * srPsi (x.1 0) - s * srChi (x.1 0), hΦsm, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (2) the zero set lies in the sublevel set
    intro x hx
    have hρx : ρ x = 0 := (hρzero x).mpr hx
    have h1 := srPsi_nonneg (t := x.1 0) x.2
    have h2 := srChi_nonneg (x.1 0)
    simp only [Set.mem_ofPred_eq]
    rw [hρx]
    nlinarith [hs0]
  · -- (3) the sublevel set avoids `T`
    refine Set.eq_empty_iff_forall_notMem.mpr ?_
    rintro x ⟨hx1, hxT⟩
    have hρx : 1 ≤ ρ x := hρT x hxT
    have := hbound x
    simp only [Set.mem_ofPred_eq] at hx1
    linarith
  · -- (4) the sublevel set is compact
    refine IsCompact.of_isClosed_subset hKc
      (isClosed_le hΦsm.continuous continuous_const) ?_
    intro x hx
    by_contra hxK
    have hρx : 1 ≤ ρ x := hK x hxK
    have := hkey x hx
    linarith
  · -- (5) the zero set of `Φ` in `Z` lies on the boundary
    rintro x ⟨hxZ, hx0⟩
    have hρx : ρ x = 0 := (hρzero x).mpr hxZ
    have h1 : srPsi (x.1 0) = 0 := by
      have h2 : 0 ≤ srPsi (x.1 0) := srPsi_nonneg (t := x.1 0) x.2
      have h3 : 0 ≤ s * srChi (x.1 0) := mul_nonneg (le_of_lt hs0) (srChi_nonneg _)
      simp only [Set.mem_ofPred_eq] at hx0
      rw [hρx] at hx0
      linarith
    exact (srPsi_eq_zero (t := x.1 0) x.2).mp h1
  · -- (6) submersivity at the interior zeros
    intro x hx0 hxne
    have hxpos : 0 < x.1 0 := lt_of_le_of_ne x.2 (Ne.symm hxne)
    have hxint : (𝓡∂ ((8 + k) + 1)).IsInteriorPoint x := by
      rw [(𝓡∂ ((8 + k) + 1)).isInteriorPoint_iff_not_isBoundaryPoint]
      intro hb
      have h0 : x.1 0 = 0 := (Work.PTGeometric.sourceRegionPhiFn_mem_boundary).mp hb
      linarith
    have hsurj : Function.Surjective (mfderiv (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, ℝ))
        (fun y : EuclideanHalfSpace ((8 + k) + 1) =>
          ρ y - 1 * srPsi (y.1 0) - s * srChi (y.1 0)) x) := hsreg x hx0 hxpos
    exact Work.PTGeometric.isSubmersionAt_of_surjective_mfderiv_real (𝓡∂ ((8 + k) + 1))
      hΦsm hxint hx0 hsurj
  · -- (7) the tangency clause at the boundary zeros
    intro x hxb hx0
    have hxbdry : x.1 0 = 0 := (Work.PTGeometric.sourceRegionPhiFn_mem_boundary).mp hxb
    have hρx : ρ x = 0 := by
      have h : ρ x - 1 * srPsi (x.1 0) - s * srChi (x.1 0) = 0 := hx0
      rw [hxbdry, srPsi_zero, srChi_zero] at h
      simp at h
      linarith
    have hxZ : x ∈ Work.PTGeometric.sourceZeroSet G m hpow := (hρzero x).mp hρx
    have hflat : mfderiv (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, ℝ)) ρ x = 0 := by
      refine Work.PTGeometric.mfderiv_flat_of_ray ρ hρsm hρ0 x hxbdry hρx ?_
      intro y hy hyt
      exact (hρzero y).mpr
        (Work.PTGeometric.mem_sourceZeroSet_of_collarRay G m hpow hxZ
          (by rw [hxbdry]; norm_num) hy hyt)
    have htang : mfderiv (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, ℝ))
          (fun y : EuclideanHalfSpace ((8 + k) + 1) =>
            ρ y - 1 * srPsi (y.1 0) - s * srChi (y.1 0)) x
        = (-1 : ℝ) • mfderiv (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, ℝ))
            (fun y : EuclideanHalfSpace ((8 + k) + 1) => y.1 0) x :=
      Work.PTGeometric.mfderiv_sourceRegionPhi_boundary ρ hρsm srPsi srChi
        contDiff_srPsi contDiff_srChi deriv_srPsi_zero deriv_srChi_zero 1 s hxbdry hflat
    refine ⟨chartAt (EuclideanHalfSpace ((8 + k) + 1)) x, -1,
      IsManifold.chart_mem_maximalAtlas (I := 𝓡∂ ((8 + k) + 1)) x,
      mem_chart_source _ x, by norm_num, ?_, ?_⟩
    · intro y _
      rw [chartAt_self_eq]
      simpa using (Work.PTGeometric.sourceRegionPhiFn_mem_boundary (x := y)).symm
    · rw [htang]
      congr 1

end

end Work.PTGeometric
