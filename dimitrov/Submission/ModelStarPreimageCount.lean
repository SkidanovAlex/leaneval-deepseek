import Mathlib
import Submission.ModelStarExterior
import Submission.ModelStarStruct
import Submission.ModelStarDisk
import Submission.ModelStarImageSeg
import Submission.ModelStarShell
import Submission.Commons.Analysis.Complex.eventually_ncard_preimage_eq_of_deriv_ne_zero

/-!
# ModelStarPreimageCount -- `N(w) = 1` for every `w` outside the model star

STATUS: work in progress (research isolate; NOT imported by `Submission.lean`).

For the model map `F = modelF z₀ r` (junctions `z₀ k = eAngle (φ k)`,
`φ` monotone injective, `0 ≤ φ k < 2π`, `Σ r k = 1`, `0 < r k`) and
`M := modelStarImage z₀ r = F '' unitCircle`, put

    `N(w) := (F ⁻¹' {w} ∩ {z | 1 < ‖z‖}).ncard`

(the number of exterior preimages of `w`).  This module proves

  * `exists_unique_preimage` (from `ModelStarDisk`): `N(w) = 1` for
    `4 < ‖w‖`,
  * `eventually_ncard_eq`: `N` is locally constant on `ℂ ∖ M` (via the
    unit-disk model, Jensen-free: the count of zeros of
    `diskPhi z₀ r - w·id` in the unit disk, plus the derivative
    computation `deriv (diskPhi z₀ r - w·id) u = -deriv F u⁻¹/u`),
  * `mem_of_smul_mem` (`ModelStarImageSeg`): the outward radial ray from
    `w ∉ M` stays outside `M`,
  * **`ncard_eq_one`**: `N(w) = 1` for EVERY `w ∉ M`.

-/

noncomputable section

open scoped Real BigOperators Topology
open Filter Set Complex

namespace Submission.ModelStarPreimageCount

open Submission.ModelStarMap
open Submission.ModelStarExterior (unitCircle mem_circle modelStarImage)
open Submission.ModelStarImageSeg

variable {s : ℕ} {z₀ : Fin s → ℂ} {r φ : Fin s → ℝ}

/-- The exterior of the unit circle. -/
def extSet : Set ℂ := {z : ℂ | 1 < ‖z‖}

/-- The open unit disk. -/
def disk : Set ℂ := Metric.ball (0 : ℂ) 1

/-- The `u`-variable companion of the model map: `Ψ u = diskPhi z₀ r u / u`,
equal to `modelF z₀ r u⁻¹` for `u ≠ 0`. -/
def psi (z₀ : Fin s → ℂ) (r : Fin s → ℝ) (u : ℂ) : ℂ :=
  Submission.ModelStarDisk.diskPhi z₀ r u / u

lemma psi_eq_modelF_inv (z₀ : Fin s → ℂ) (r : Fin s → ℝ) {u : ℂ} (hu : u ≠ 0) :
    psi z₀ r u = modelF z₀ r u⁻¹ := by
  rw [show psi z₀ r u = Submission.ModelStarDisk.diskPhi z₀ r u / u from rfl, div_eq_iff hu,
    mul_comm]
  exact (Submission.ModelStarDisk.mul_modelF_inv_eq z₀ r hu).symm

lemma diskPhi_sub_eq_mul_psi (z₀ : Fin s → ℂ) (r : Fin s → ℝ) {u w : ℂ} (hu : u ≠ 0) :
    Submission.ModelStarDisk.diskPhi z₀ r u - w * u = u * (psi z₀ r u - w) := by
  unfold psi
  field_simp

/-! ## Derivatives in the `u`-variable -/

/-- `Ψ` has derivative `-F'(u⁻¹)/u²` on the open unit disk. -/
lemma hasDerivAt_psi (z₀ : Fin s → ℂ) (r : Fin s → ℝ) (hunit : ∀ k, ‖z₀ k‖ = 1)
    {u : ℂ} (hu : u ≠ 0) (hu1 : ‖u‖ < 1) :
    HasDerivAt (psi z₀ r) (-(deriv (modelF z₀ r) u⁻¹) / u ^ 2) u := by
  have hFinv : 1 < ‖u⁻¹‖ := by
    rw [norm_inv]
    exact one_lt_inv_iff₀.mpr ⟨norm_pos_iff.mpr hu, hu1⟩
  have hF : DifferentiableAt ℂ (modelF z₀ r) u⁻¹ :=
    Submission.ModelStarShell.modelF_differentiableAt z₀ r
      (fun k => lt_of_le_of_lt (le_of_eq (hunit k)) hFinv)
  have heq : (fun v : ℂ => modelF z₀ r v⁻¹) =ᶠ[𝓝 u] psi z₀ r := by
    filter_upwards [eventually_ne_nhds hu] with v hv
    exact (psi_eq_modelF_inv z₀ r hv).symm
  have hinv : HasDerivAt (fun v : ℂ => v⁻¹) (-(u ^ 2)⁻¹) u := hasDerivAt_inv hu
  have hcomp : HasDerivAt (fun v : ℂ => modelF z₀ r v⁻¹)
      (deriv (modelF z₀ r) u⁻¹ * (-(u ^ 2)⁻¹)) u :=
    hF.hasDerivAt.comp u hinv
  have hval : deriv (modelF z₀ r) u⁻¹ * (-(u ^ 2)⁻¹)
      = -(deriv (modelF z₀ r) u⁻¹) / u ^ 2 := by
    ring_nf
  rw [hval] at hcomp
  exact hcomp.congr_of_eventuallyEq heq.symm

/-- At a zero of the disk model the derivative of `diskPhi z₀ r - w·id` is
`-F'(u⁻¹)/u ≠ 0`. -/
lemma hasDerivAt_diskPhi_sub (z₀ : Fin s → ℂ) (r : Fin s → ℝ) (hunit : ∀ k, ‖z₀ k‖ = 1)
    {u w : ℂ} (hu : u ≠ 0) (hu1 : ‖u‖ < 1) (hpsi : psi z₀ r u = w) :
    HasDerivAt (fun v : ℂ => Submission.ModelStarDisk.diskPhi z₀ r v - w * v)
      (-(deriv (modelF z₀ r) u⁻¹) / u) u := by
  have heq : (fun v : ℂ => Submission.ModelStarDisk.diskPhi z₀ r v - w * v)
      =ᶠ[𝓝 u] (fun v => v * (psi z₀ r v - w)) := by
    filter_upwards [eventually_ne_nhds hu] with v hv
    exact diskPhi_sub_eq_mul_psi z₀ r hv
  have hd : HasDerivAt (fun v : ℂ => v * (psi z₀ r v - w))
      (1 * (psi z₀ r u - w) + u * (-(deriv (modelF z₀ r) u⁻¹) / u ^ 2)) u :=
    (hasDerivAt_id u).mul ((hasDerivAt_psi z₀ r hunit hu hu1).sub_const w)
  have hval : 1 * (psi z₀ r u - w) + u * (-(deriv (modelF z₀ r) u⁻¹) / u ^ 2)
      = -(deriv (modelF z₀ r) u⁻¹) / u := by
    rw [hpsi]
    field_simp
    ring
  rw [hval] at hd
  exact hd.congr_of_eventuallyEq heq

/-! ## The count of exterior preimages equals the count of disk zeros -/

/-- The number of exterior preimages of `w` (the function `N`). -/
def ncardPre (z₀ : Fin s → ℂ) (r : Fin s → ℝ) (w : ℂ) : ℕ :=
  (modelF z₀ r ⁻¹' {w} ∩ extSet).ncard

lemma ncard_preimage_eq_ncard_zeros (z₀ : Fin s → ℂ) (r : Fin s → ℝ) (w : ℂ) :
    ncardPre z₀ r w
      = ((fun u : ℂ => Submission.ModelStarDisk.diskPhi z₀ r u - w * u) ⁻¹' {0}
          ∩ disk).ncard := by
  have hset : ((fun u : ℂ => u⁻¹) '' ((fun u : ℂ => Submission.ModelStarDisk.diskPhi z₀ r u
      - w * u) ⁻¹' {0} ∩ disk)) = (modelF z₀ r ⁻¹' {w} ∩ extSet) := by
    ext z
    constructor
    · rintro ⟨u, ⟨hu1, hu2⟩, rfl⟩
      rw [Set.mem_preimage, Set.mem_singleton_iff] at hu1
      have hud : ‖u‖ < 1 := by
        rw [disk, Metric.mem_ball, dist_zero_right] at hu2
        exact hu2
      have hu_ne : u ≠ 0 := by
        intro h0
        rw [h0, Submission.ModelStarDisk.diskPhi_zero, mul_zero, sub_zero] at hu1
        exact one_ne_zero hu1
      have hFinv : modelF z₀ r u⁻¹ = w := by
        have h := Submission.ModelStarDisk.mul_modelF_inv_eq z₀ r hu_ne
        rw [← h] at hu1
        rw [mul_comm w u, ← mul_sub, mul_eq_zero] at hu1
        rcases hu1 with h0 | h0
        · exact absurd h0 hu_ne
        · exact sub_eq_zero.mp h0
      refine ⟨hFinv, ?_⟩
      rw [extSet, Set.mem_setOf_eq, norm_inv]
      exact one_lt_inv_iff₀.mpr ⟨norm_pos_iff.mpr hu_ne, hud⟩
    · rintro ⟨hz1, hz2⟩
      rw [extSet, Set.mem_setOf_eq] at hz2
      have hz0 : z ≠ 0 := by
        intro h0
        rw [h0, norm_zero] at hz2
        exact absurd hz2 (by norm_num)
      refine ⟨z⁻¹, ⟨?_, ?_⟩, inv_inv z⟩
      · rw [Set.mem_preimage, Set.mem_singleton_iff]
        have h := Submission.ModelStarDisk.mul_modelF_inv_eq z₀ r (inv_ne_zero hz0)
        rw [inv_inv, hz1] at h
        rw [← h]
        ring
      · rw [disk, Metric.mem_ball, dist_zero_right, norm_inv]
        exact inv_lt_one_of_one_lt₀ hz2
  rw [ncardPre, ← hset, Set.ncard_image_of_injective _ inv_injective]

/-- `N(w) = 1` for `4 < ‖w‖`. -/
theorem ncardPre_eq_one_of_four_lt (z₀ : Fin s → ℂ) (r : Fin s → ℝ)
    (hunit : ∀ k, ‖z₀ k‖ = 1) (hr : ∀ k, 0 < r k) (hsum : (∑ k : Fin s, r k) = 1)
    {w : ℂ} (hw : 4 < ‖w‖) : ncardPre z₀ r w = 1 := by
  obtain ⟨ζ, hζ, huniq⟩ :=
    Submission.ModelStarDisk.exists_unique_preimage z₀ r hunit hr hsum hw
  unfold ncardPre
  rw [Set.ncard_eq_one]
  refine ⟨ζ, ?_⟩
  ext z
  simp only [ncardPre, extSet, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨hz1, hz2⟩
    exact huniq z ⟨hz2, hz1⟩
  · rintro rfl
    exact ⟨hζ.2, hζ.1⟩

/-! ## Radial propagation of the value `N = 1` -/

/-- **Radial propagation.**  If `N` is locally constant off the model star `M`
and equals `1` far out, then `N ≡ 1` on `ℂ ∖ M`.  (The outward radial ray
from a point off `M` never meets `M`: `mem_of_smul_mem`.) -/
theorem ncardPre_eq_one_of_notMem {s : ℕ} {z₀ : Fin s → ℂ} {r φ : Fin s → ℝ}
    (hs : 0 < s) (hz₀e : ∀ k, z₀ k = Submission.ModelStarBoundary2.eAngle (φ k))
    (hunit : ∀ k, ‖z₀ k‖ = 1) (hr : ∀ k, 0 < r k) (hsum : (∑ k : Fin s, r k) = 1)
    (hmono : Monotone φ) (hφinj : Function.Injective φ)
    (hφlo : ∀ k, 0 ≤ φ k) (hφhi : ∀ k, φ k < 2 * Real.pi)
    (hN1 : ∀ w : ℂ, 4 < ‖w‖ → ncardPre z₀ r w = 1)
    (hloc : ∀ w : ℂ, w ∉ modelStarImage z₀ r →
      ∀ᶠ w' in 𝓝 w, ncardPre z₀ r w' = ncardPre z₀ r w)
    {w : ℂ} (hw : w ∉ modelStarImage z₀ r) : ncardPre z₀ r w = 1 := by
  have hw0 : w ≠ 0 := by
    intro h0
    refine hw ?_
    rw [h0]
    exact zero_mem_modelStarImage hs hz₀e hr
  set f : ℝ → ℂ := fun t => ((max 1 (1 + t) : ℝ) : ℂ) * w with hfdef
  have hf0 : f 0 = w := by
    simp [hfdef]
  have hfnotM : ∀ t : ℝ, f t ∉ modelStarImage z₀ r := by
    intro t ht
    have h1 : (1 : ℝ) ≤ max 1 (1 + t) := le_max_left _ _
    exact hw (mem_of_smul_mem hs hz₀e hφlo hφhi hsum hmono hφinj hr h1 ht)
  set T : Set ℝ := {t : ℝ | ncardPre z₀ r (f t) = ncardPre z₀ r w} with hTdef
  have hT0 : (0 : ℝ) ∈ T := by
    simp only [hTdef, Set.mem_setOf_eq, hf0]
  have hfcont : Continuous f := by
    simp only [hfdef]
    fun_prop
  have hTopen : IsOpen T := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    have hlt : ∀ᶠ t' in 𝓝 t, ncardPre z₀ r (f t') = ncardPre z₀ r (f t) :=
      (hfcont.continuousAt.tendsto).eventually (hloc (f t) (hfnotM t))
    filter_upwards [hlt] with t' ht'
    simp only [hTdef, Set.mem_setOf_eq]
    rw [ht', ht]
  have hTclosed : IsClosed T := by
    refine IsSeqClosed.isClosed ?_
    intro u p hu hlim
    have hev : ∀ᶠ t' in 𝓝 p, ncardPre z₀ r (f t') = ncardPre z₀ r (f p) :=
      (hfcont.continuousAt.tendsto).eventually (hloc (f p) (hfnotM p))
    obtain ⟨n, hn⟩ := (hlim.eventually hev).exists
    simp only [hTdef, Set.mem_setOf_eq] at hu ⊢
    rw [← hn, hu n]
  have hTuniv : T = Set.univ := by
    rcases (isPreconnected_iff_subset_of_disjoint_closed.mp isPreconnected_univ T Tᶜ
      hTclosed hTopen.isClosed_compl (by simp) (by simp)) with h | h
    · exact eq_univ_of_univ_subset h
    · exact absurd (h (Set.mem_univ (0 : ℝ))) (by simpa using hT0)
  have hTmem : ∀ t : ℝ, ncardPre z₀ r (f t) = ncardPre z₀ r w := fun t =>
    (show t ∈ T from by rw [hTuniv]; trivial)
  have hwnorm : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  obtain ⟨t, ht⟩ : ∃ t : ℝ, 4 < (max 1 (1 + t) : ℝ) * ‖w‖ :=
    ⟨4 / ‖w‖, by
      have h1 : (1 : ℝ) + 4 / ‖w‖ ≤ max 1 (1 + 4 / ‖w‖) := le_max_right _ _
      have h2 : ((1 : ℝ) + 4 / ‖w‖) * ‖w‖ = ‖w‖ + 4 := by
        field_simp
      nlinarith [hwnorm]⟩
  have hft : 4 < ‖f t‖ := by
    have hnorm : ‖(((max 1 (1 + t) : ℝ)) : ℂ)‖ = max 1 (1 + t) := by
      rw [show ‖(((max 1 (1 + t) : ℝ)) : ℂ)‖ = |max 1 (1 + t)| from
        RCLike.norm_ofReal (max 1 (1 + t)),
        abs_of_nonneg (le_trans zero_le_one (le_max_left 1 (1 + t)))]
    have heq : f t = (((max 1 (1 + t) : ℝ)) : ℂ) * w := rfl
    rw [heq, norm_mul, hnorm]
    exact ht
  rw [← hTmem t]
  exact hN1 (f t) hft

/-! ## Local constancy of the preimage count off the model star -/

lemma continuousOn_diskPhi_sub (z₀ : Fin s → ℂ) (r : Fin s → ℝ) (hunit : ∀ k, ‖z₀ k‖ = 1)
    (hr : ∀ k, 0 < r k) (w : ℂ) :
    ContinuousOn (fun u : ℂ => Submission.ModelStarDisk.diskPhi z₀ r u - w * u)
      (closure disk) := by
  rw [show disk = Metric.ball (0 : ℂ) 1 from rfl, closure_ball 0 one_ne_zero]
  exact ((Submission.ModelStarDisk.continuousOn_diskPhi_closedBall z₀ r hunit hr).sub
    (continuousOn_const.mul continuousOn_id))

lemma deriv_diskPhi_sub_ne_zero {s : ℕ} {z₀ : Fin s → ℂ} {r : Fin s → ℝ}
    (hs : 0 < s) (hunit : ∀ k, ‖z₀ k‖ = 1) (hr : ∀ k, 0 < r k) (hsum : (∑ k : Fin s, r k) = 1)
    {u w : ℂ} (hud : u ∈ disk) (hfz : Submission.ModelStarDisk.diskPhi z₀ r u - w * u = 0) :
    deriv (fun v : ℂ => Submission.ModelStarDisk.diskPhi z₀ r v - w * v) u ≠ 0 := by
  have hu1 : ‖u‖ < 1 := by
    rw [disk, Metric.mem_ball, dist_zero_right] at hud
    exact hud
  have hu0 : u ≠ 0 := by
    intro h0
    rw [h0, Submission.ModelStarDisk.diskPhi_zero, mul_zero, sub_zero] at hfz
    exact one_ne_zero hfz
  have hpsi : psi z₀ r u = w := by
    rw [psi, div_eq_iff hu0]
    exact sub_eq_zero.mp hfz
  have hder := (hasDerivAt_diskPhi_sub z₀ r hunit hu0 hu1 hpsi).deriv
  rw [hder]
  have hne1 : deriv (modelF z₀ r) u⁻¹ ≠ 0 := by
    haveI : NeZero s := ⟨hs.ne'⟩
    have hz1 : ‖u⁻¹‖ ≠ 1 := by
      rw [norm_inv]
      intro hcon
      have h2 : ‖u‖ = 1 := inv_eq_one.mp hcon
      linarith
    have hH : Submission.ModelStarStruct.H z₀ r u⁻¹ ≠ 0 :=
      Submission.ModelStarStruct.H_ne_zero z₀ r hunit hr hz1
    intro hcon
    exact hH ((Submission.ModelStarStruct.deriv_modelF_eq_zero_iff z₀ r (z := u⁻¹)
      (inv_ne_zero hu0) (fun k => by
        intro hk
        have h2 : ‖u⁻¹‖ = 1 := by rw [hk]; exact hunit k
        exact hz1 h2)
      (fun k => Submission.ModelStarMap.factor_mem_slitPlane
        (lt_of_le_of_lt (le_of_eq (hunit k)) (by
          rw [norm_inv]
          exact one_lt_inv_iff₀.mpr ⟨norm_pos_iff.mpr hu0, hu1⟩)))
      hsum).mp hcon)
  exact div_ne_zero (neg_ne_zero.mpr hne1) hu0

/-- A uniform lower bound for `‖diskPhi‖` near `0`. -/
lemma exists_pos_forall_norm_le_diskPhi (z₀ : Fin s → ℂ) (r : Fin s → ℝ)
    (hunit : ∀ k, ‖z₀ k‖ = 1) (hr : ∀ k, 0 < r k) :
    ∃ d : ℝ, 0 < d ∧ ∀ u : ℂ, ‖u‖ ≤ d → (1 / 2 : ℝ) ≤ ‖Submission.ModelStarDisk.diskPhi z₀ r u‖ := by
  have hcont : ContinuousAt (Submission.ModelStarDisk.diskPhi z₀ r) 0 :=
    Submission.ModelStarDisk.continuousAt_diskPhi z₀ r hunit hr (by simp)
  have hmem : Metric.ball (Submission.ModelStarDisk.diskPhi z₀ r 0) (1 / 2) ∈
      𝓝 (Submission.ModelStarDisk.diskPhi z₀ r 0) := Metric.ball_mem_nhds _ (by norm_num)
  obtain ⟨d, hd, hsub⟩ := Metric.mem_nhds_iff.mp (hcont hmem)
  refine ⟨d / 2, by linarith, fun u hu => ?_⟩
  have h1 : Submission.ModelStarDisk.diskPhi z₀ r u ∈
      Metric.ball (Submission.ModelStarDisk.diskPhi z₀ r 0) (1 / 2) :=
    hsub (by rw [Metric.mem_ball, dist_zero_right]; linarith)
  rw [Submission.ModelStarDisk.diskPhi_zero] at h1
  have h2 : ‖Submission.ModelStarDisk.diskPhi z₀ r u - 1‖ < 1 / 2 := by
    simpa [Metric.mem_ball, dist_eq_norm] using h1
  have h3 : (1 : ℝ) - ‖Submission.ModelStarDisk.diskPhi z₀ r u - 1‖ ≤
      ‖Submission.ModelStarDisk.diskPhi z₀ r u‖ := by
    have h4 := abs_norm_sub_norm_le (Submission.ModelStarDisk.diskPhi z₀ r u) (1 : ℂ)
    rw [norm_one] at h4
    have h5 : -‖Submission.ModelStarDisk.diskPhi z₀ r u - 1‖ ≤
        ‖Submission.ModelStarDisk.diskPhi z₀ r u‖ - 1 := (abs_le.mp h4).1
    linarith
  linarith

/-- **Key separation fact.**  If `‖w'‖ ≤ 2‖w‖` then every zero of
`diskPhi z₀ r - w'·id` is at distance `> δ` from the origin, where `δ` is any
number below both `d0/2` (`d0` a uniform lower bound radius) and `1/(8‖w‖)`. -/
lemma delta_lt_norm_of_zero {s : ℕ} {z₀ : Fin s → ℂ} {r : Fin s → ℝ} {w : ℂ}
    {d0 δ : ℝ} (hwpos : 0 < ‖w‖) (hδpos : 0 ≤ δ) (hδd0 : δ ≤ d0 / 2)
    (hδle : δ ≤ 1 / (8 * ‖w‖))
    (hd0 : ∀ u : ℂ, ‖u‖ ≤ d0 → (1 / 2 : ℝ) ≤ ‖Submission.ModelStarDisk.diskPhi z₀ r u‖)
    {w' u : ℂ} (hw'le : ‖w'‖ ≤ 2 * ‖w‖)
    (hzero : Submission.ModelStarDisk.diskPhi z₀ r u = w' * u) : δ < ‖u‖ := by
  by_contra hcon
  rw [not_lt] at hcon
  rcases le_or_gt (‖u‖) d0 with hcase | hcase
  · have h1 : (1 / 2 : ℝ) ≤ ‖w'‖ * ‖u‖ := by
      have h2 := hd0 u hcase
      rwa [hzero, norm_mul] at h2
    have h3 : ‖w'‖ * ‖u‖ ≤ 2 * ‖w‖ * δ := by
      have h4 : ‖w'‖ * ‖u‖ ≤ ‖w'‖ * δ := mul_le_mul_of_nonneg_left hcon (norm_nonneg w')
      have h5 : ‖w'‖ * δ ≤ (2 * ‖w‖) * δ := mul_le_mul_of_nonneg_right hw'le hδpos
      linarith
    have h6 : 2 * ‖w‖ * δ ≤ 1 / 4 := by
      have h7 : 2 * ‖w‖ * δ ≤ 2 * ‖w‖ * (1 / (8 * ‖w‖)) :=
        mul_le_mul_of_nonneg_left hδle (by positivity)
      have h8 : 2 * ‖w‖ * (1 / (8 * ‖w‖)) = 1 / 4 := by
        field_simp
        norm_num
      linarith
    linarith
  · linarith [hδd0]

/-- `deriv Ψ u ≠ 0` on the unit disk. -/
lemma deriv_psi_ne_zero {s : ℕ} {z₀ : Fin s → ℂ} {r : Fin s → ℝ} (hs : 0 < s)
    (hunit : ∀ k, ‖z₀ k‖ = 1) (hr : ∀ k, 0 < r k) (hsum : (∑ k : Fin s, r k) = 1)
    {u : ℂ} (hu0 : u ≠ 0) (hu1 : ‖u‖ < 1) : deriv (psi z₀ r) u ≠ 0 := by
  have hder := (hasDerivAt_psi z₀ r hunit hu0 hu1).deriv
  rw [hder]
  refine div_ne_zero (neg_ne_zero.mpr ?_) (pow_ne_zero 2 hu0)
  haveI : NeZero s := ⟨hs.ne'⟩
  have hne : ‖u⁻¹‖ ≠ 1 := by
    rw [norm_inv]
    intro hcon
    have h2 : ‖u‖ = 1 := inv_eq_one.mp hcon
    linarith
  have hH : Submission.ModelStarStruct.H z₀ r u⁻¹ ≠ 0 :=
    Submission.ModelStarStruct.H_ne_zero z₀ r hunit hr hne
  intro hcon
  refine hH ((Submission.ModelStarStruct.deriv_modelF_eq_zero_iff z₀ r (z := u⁻¹)
    (inv_ne_zero hu0) (fun k => by
      intro hk
      have h2 : ‖u⁻¹‖ = 1 := by rw [hk]; exact hunit k
      exact hne h2)
    (fun k => Submission.ModelStarMap.factor_mem_slitPlane
      (lt_of_le_of_lt (le_of_eq (hunit k)) (by
        rw [norm_inv]
        exact one_lt_inv_iff₀.mpr ⟨norm_pos_iff.mpr hu0, hu1⟩)))
    hsum).mp hcon)

/-- **Local constancy of `N` off the model star.** -/
theorem eventually_ncardPre_eq {s : ℕ} {z₀ : Fin s → ℂ} {r φ : Fin s → ℝ}
    (hs : 0 < s) (hz₀e : ∀ k, z₀ k = Submission.ModelStarBoundary2.eAngle (φ k))
    (hunit : ∀ k, ‖z₀ k‖ = 1) (hr : ∀ k, 0 < r k) (hsum : (∑ k : Fin s, r k) = 1)
    {w : ℂ} (hw : w ∉ modelStarImage z₀ r) :
    ∀ᶠ w' in 𝓝 w, ncardPre z₀ r w' = ncardPre z₀ r w := by
  have hw0 : w ≠ 0 := by
    intro h0
    refine hw ?_
    rw [h0]
    exact zero_mem_modelStarImage hs hz₀e hr
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  obtain ⟨d0, hd0pos, hd0⟩ := exists_pos_forall_norm_le_diskPhi z₀ r hunit hr
  set δ : ℝ := min (d0 / 2) (1 / (8 * ‖w‖)) with hδdef
  have hδd0 : δ ≤ d0 / 2 := by rw [hδdef]; exact min_le_left _ _
  have hδle : δ ≤ 1 / (8 * ‖w‖) := by rw [hδdef]; exact min_le_right _ _
  have hδpos : 0 < δ := by
    rw [hδdef]
    exact lt_min (by linarith) (by positivity)
  set A : Set ℂ := {u : ℂ | δ < ‖u‖ ∧ ‖u‖ < 1} with hAdef
  have hzero_sep : ∀ {w' u : ℂ}, ‖w'‖ ≤ 2 * ‖w‖ →
      Submission.ModelStarDisk.diskPhi z₀ r u = w' * u → δ < ‖u‖ :=
    fun hw'le hzero => delta_lt_norm_of_zero (w := w) hwpos (le_of_lt hδpos) hδd0 hδle hd0
      hw'le hzero
  -- bookkeeping: zeros of `diskPhi - w'·id` in the disk are exactly the zeros in `A`
  have hbook : ∀ w' : ℂ, ‖w'‖ ≤ 2 * ‖w‖ →
      ((fun u : ℂ => Submission.ModelStarDisk.diskPhi z₀ r u - w' * u) ⁻¹' {0} ∩ disk)
        = ((fun u : ℂ => Submission.ModelStarDisk.diskPhi z₀ r u / u) ⁻¹' {w'} ∩ A) := by
    intro w' hw'le
    ext u
    constructor
    · rintro ⟨hu1, hu2⟩
      rw [Set.mem_preimage, Set.mem_singleton_iff] at hu1
      have hud : ‖u‖ < 1 := by
        rw [disk, Metric.mem_ball, dist_zero_right] at hu2; exact hu2
      have hu_ne : u ≠ 0 := by
        intro h0
        rw [h0, Submission.ModelStarDisk.diskPhi_zero, mul_zero, sub_zero] at hu1
        exact one_ne_zero hu1
      have hzero : Submission.ModelStarDisk.diskPhi z₀ r u = w' * u := sub_eq_zero.mp hu1
      have hpsiu : Submission.ModelStarDisk.diskPhi z₀ r u / u = w' := by
        rw [div_eq_iff hu_ne]; exact hzero
      exact ⟨hpsiu, ⟨hzero_sep hw'le hzero, hud⟩⟩
    · rintro ⟨hu1, ⟨hu2, hu3⟩⟩
      rw [Set.mem_preimage, Set.mem_singleton_iff] at hu1
      have hu_ne : u ≠ 0 := by
        intro h0
        rw [h0] at hu2
        exact absurd hu2 (by rw [norm_zero]; linarith)
      refine ⟨?_, ?_⟩
      · simp only [Set.mem_preimage, Set.mem_singleton_iff]
        rw [diskPhi_sub_eq_mul_psi z₀ r hu_ne]
        rw [show psi z₀ r u = w' from hu1]
        ring
      · rw [disk, Metric.mem_ball, dist_zero_right]; exact hu3
  -- the annulus is open with compact closure
  have hAopen : IsOpen A := by
    have hset : A = Metric.ball (0 : ℂ) 1 ∩ (Metric.closedBall (0 : ℂ) δ)ᶜ := by
      rw [hAdef]
      ext u
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Metric.mem_ball, Metric.mem_closedBall,
        dist_zero_right, Set.mem_compl_iff, not_le]
      tauto
    rw [hset]
    exact Metric.isOpen_ball.inter (Metric.isClosed_closedBall.isOpen_compl)
  have hAcl : closure A ⊆ Metric.closedBall (0 : ℂ) 1 := by
    rw [hAdef]
    refine closure_minimal ?_ Metric.isClosed_closedBall
    rintro u ⟨_, h2⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact le_of_lt h2
  have hAcpt : IsCompact (closure A) :=
    (isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset isClosed_closure hAcl
  have hAcδ : closure A ⊆ {u : ℂ | δ ≤ ‖u‖} := by
    refine closure_minimal ?_ (isClosed_Ici.preimage continuous_norm)
    rintro u ⟨h1, _⟩
    exact le_of_lt h1
  have hfront : frontier A ⊆ Metric.sphere (0 : ℂ) 1 ∪ Metric.sphere (0 : ℂ) δ := by
    have hset : A = Metric.ball (0 : ℂ) 1 ∩ (Metric.closedBall (0 : ℂ) δ)ᶜ := by
      rw [hAdef]
      ext u
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Metric.mem_ball, Metric.mem_closedBall,
        dist_zero_right, Set.mem_compl_iff, not_le]
      tauto
    calc frontier A ⊆ frontier (Metric.ball (0 : ℂ) 1) ∪ frontier ((Metric.closedBall (0 : ℂ) δ)ᶜ) := by
          rw [hset]
          refine (frontier_inter_subset _ _).trans ?_
          rintro z (⟨hz1, _⟩ | ⟨_, hz2⟩)
          · exact Or.inl hz1
          · exact Or.inr hz2
      _ ⊆ Metric.sphere (0 : ℂ) 1 ∪ Metric.sphere (0 : ℂ) δ := by
          rw [frontier_compl]
          rintro z (hz | hz)
          · exact Or.inl (Metric.frontier_ball_subset_sphere hz)
          · exact Or.inr (Metric.frontier_closedBall_subset_sphere hz)
  have hPsi_cont : ContinuousOn (fun u : ℂ => Submission.ModelStarDisk.diskPhi z₀ r u / u)
      (closure A) := by
    refine ContinuousOn.div ?_ continuousOn_id (fun u hu => ?_)
    · exact (Submission.ModelStarDisk.continuousOn_diskPhi_closedBall z₀ r hunit hr).mono hAcl
    · have hge : δ ≤ ‖u‖ := hAcδ hu
      exact norm_ne_zero_iff.mp (ne_of_gt (lt_of_lt_of_le hδpos hge))
  have hno : w ∉ (fun u : ℂ => Submission.ModelStarDisk.diskPhi z₀ r u / u) '' frontier A := by
    rintro ⟨u, hu, huz⟩
    have hu0 : u ≠ 0 := by
      have h1 : δ ≤ ‖u‖ := hAcδ (frontier_subset_closure hu)
      intro h0
      rw [h0, norm_zero] at h1
      linarith
    have hzero : Submission.ModelStarDisk.diskPhi z₀ r u = w * u := (div_eq_iff hu0).mp huz
    rcases hfront hu with h1 | h1
    · have hu1 : ‖u‖ = 1 := by simpa using h1
      exact Submission.ModelStarDisk.diskPhi_sub_ne_zero_sphere z₀ r hu1 hzero hw
    · have hu1 : ‖u‖ = δ := by simpa using h1
      exact absurd (hzero_sep (by linarith [norm_nonneg w]) hzero) (by rw [hu1]; exact lt_irrefl _)
  have hder : ∀ u ∈ A, (fun u : ℂ => Submission.ModelStarDisk.diskPhi z₀ r u / u) u = w →
      deriv (fun u : ℂ => Submission.ModelStarDisk.diskPhi z₀ r u / u) u ≠ 0 := by
    intro u hu _
    exact deriv_psi_ne_zero hs hunit hr hsum (by
      intro h0
      rw [h0] at hu
      exact absurd hu.1 (by rw [norm_zero]; linarith)) hu.2
  have hloc := Commons.Analysis.Complex.eventually_ncard_preimage_eq_of_deriv_ne_zero
    (U := A) (f := fun u : ℂ => Submission.ModelStarDisk.diskPhi z₀ r u / u)
    hAopen hAcpt hPsi_cont
    (fun u hu => (Submission.ModelStarDisk.analyticAt_diskPhi z₀ r hunit hu.2).div
      analyticAt_id (by
        intro h0
        rw [h0] at hu
        exact absurd hu.1 (by rw [norm_zero]; linarith)))
    (w₀ := w) hno hder
  have hnorm_nbhd : ∀ᶠ w' in 𝓝 w, ‖w'‖ ≤ 2 * ‖w‖ := by
    filter_upwards [Metric.closedBall_mem_nhds w hwpos] with w' hw'
    rw [Metric.mem_closedBall, dist_eq_norm] at hw'
    calc ‖w'‖ = ‖(w' - w) + w‖ := by ring_nf
      _ ≤ ‖w' - w‖ + ‖w‖ := norm_add_le _ _
      _ ≤ ‖w‖ + ‖w‖ := by linarith
      _ = 2 * ‖w‖ := by ring
  filter_upwards [hloc, hnorm_nbhd] with w' hw'1 hw'2
  rw [ncard_preimage_eq_ncard_zeros, ncard_preimage_eq_ncard_zeros, hbook w' hw'2,
    hbook w (by linarith [norm_nonneg w])]
  exact hw'1

/-- **`N(w) = 1` for every `w` outside the model star.** -/
theorem ncardPre_eq_one {s : ℕ} {z₀ : Fin s → ℂ} {r φ : Fin s → ℝ}
    (hs : 0 < s) (hz₀e : ∀ k, z₀ k = Submission.ModelStarBoundary2.eAngle (φ k))
    (hunit : ∀ k, ‖z₀ k‖ = 1) (hr : ∀ k, 0 < r k) (hsum : (∑ k : Fin s, r k) = 1)
    (hmono : Monotone φ) (hφinj : Function.Injective φ)
    (hφlo : ∀ k, 0 ≤ φ k) (hφhi : ∀ k, φ k < 2 * Real.pi)
    {w : ℂ} (hw : w ∉ modelStarImage z₀ r) : ncardPre z₀ r w = 1 :=
  ncardPre_eq_one_of_notMem (φ := φ) hs hz₀e hunit hr hsum hmono hφinj hφlo hφhi
    (fun w' hw' => ncardPre_eq_one_of_four_lt z₀ r hunit hr hsum hw')
    (fun w' hw' => eventually_ncardPre_eq (z₀ := z₀) (r := r) (φ := φ) hs hz₀e hunit hr hsum hw')
    hw

end Submission.ModelStarPreimageCount
