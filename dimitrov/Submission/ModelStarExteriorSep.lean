import Mathlib
import Submission.ModelStarPreimageCount
import Submission.ModelStarImageSeg
import Submission.ModelStarStruct
import Submission.ModelStarShell
import Submission.Commons.Analysis.Calculus.injOn_nhds_of_hasStrictDerivAt

/-!
# ModelStarExteriorSep -- (P3): the exterior of the model map misses the model star

STATUS: work in progress (research isolate; NOT imported by `Submission.lean`).

For the model map `F = modelF z₀ r` (junctions `z₀ k = eAngle (φ k)`, `φ`
monotone injective, `0 ≤ φ k < 2π`, `Σ r k = 1`, `0 < r k`) with model star
`M = modelStarImage z₀ r = F '' unitCircle`, this module proves

    `F '' {z | 1 < ‖z‖} ∩ M = ∅`,

i.e. no exterior point of the model map maps to a boundary point of the model
star -- statement (P3) of `Submission/Work/STATUS_dimitrov.md` §120.

PROOF.  By `Submission.ModelStarPreimageCount.ncardPre_eq_one`, `N(w) = 1`
for every `w ∉ M` (the number of exterior preimages).  Suppose
`w ∈ F '' {1 < ‖·‖} ∩ M` and `w` is NOT a critical value of the boundary map
(`H z₀ r ζ ≠ 0` for every circle preimage `ζ` of `w`).  Pick a circle
preimage `ζ` (not a junction, since `w ≠ 0`) and an exterior preimage `x₀`,
put `u₀ := x₀⁻¹`, `a := ζ⁻¹` and `Ψ u := diskPhi z₀ r u / u = F(u⁻¹)`.
Both `u₀` and `a` are simple zeros of `Ψ - w` (`Ψ' ≠ 0` there), so the
inverse function theorem gives a local branch `G` of `Ψ` at `u₀` with
`Ψ (G y) = y` near `w`.  Since `Ψ` is a local biholomorphism at the unit
point `a` and the unit disk has empty interior in `ℂ`... precisely:
`Ψ '' (ball a ε ∩ ball 0 1) ∩ ball w δ` is a nonempty open set, so it
contains a point `w' ∉ M` (`interior M = ∅`); for that `w'` the unit-disk
model `diskPhi z₀ r - w'·id` has the two distinct zeros `u` (with
`Ψ u = w'`, `‖u‖ < 1`) and `G w'` (near `u₀`), contradicting `N(w') = 1`.
So `F '' {1 < ‖·‖} ∩ M ⊆ {critical values}`, a FINITE set; but
`F '' {1 < ‖·‖}` is open, so `F '' {1 < ‖·‖} ∩ M` is relatively open in `M`,
and a finite relatively open nonempty subset of a preconnected continuum
forces `M` to be finite, contradicting `modelStarImage_two`.

-/

noncomputable section

open scoped Real BigOperators Topology
open Filter Set Complex

namespace Submission.ModelStarExteriorSep

open Submission.ModelStarMap
open Submission.ModelStarExterior (unitCircle mem_circle modelStarImage)
open Submission.ModelStarPreimageCount
open Submission.ModelStarImageSeg

variable {s : ℕ} {z₀ : Fin s → ℂ} {r φ : Fin s → ℝ}

/-! ## Helper lemmas -/

/-- `1 - a·u` is in the slit plane for unit `a, u` with `a·u ≠ 1`. -/
lemma one_sub_mul_mem_slitPlane {a u : ℂ} (ha : ‖a‖ = 1) (hu : ‖u‖ = 1)
    (h : 1 - a * u ≠ 0) : 1 - a * u ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  left
  have hnorm : ‖a * u‖ = 1 := by rw [norm_mul, ha, hu, one_mul]
  have hre : (1 - a * u).re = 1 - (a * u).re := by simp
  have hle : (a * u).re ≤ 1 := by
    calc (a * u).re ≤ ‖a * u‖ := Complex.re_le_norm _
      _ = 1 := hnorm
  have hlt : (a * u).re < 1 := lt_of_le_of_ne hle (by
    intro hcon
    apply h
    have hsq : (a * u).re ^ 2 + (a * u).im ^ 2 = 1 := by
      have h1 : Complex.normSq (a * u) = (a * u).re ^ 2 + (a * u).im ^ 2 := by
        rw [Complex.normSq_apply]; ring
      rw [← h1, Complex.normSq_eq_norm_sq, hnorm]
      norm_num
    have him : (a * u).im = 0 := by nlinarith [sq_nonneg (a * u).im]
    have hau1 : a * u = 1 := Complex.ext (by rw [hcon]; simp) (by rw [him]; simp)
    rw [hau1, sub_self])
  rw [hre]
  linarith

/-- Analyticity of a disk factor at a point where the base is in the slit plane. -/
lemma analyticAt_diskFactor_of {a : ℂ} {t : ℝ} {u : ℂ}
    (h : 1 - a * u ∈ Complex.slitPlane) :
    AnalyticAt ℂ (fun u : ℂ => Submission.ModelStarDisk.diskFactor a t u) u := by
  have han : AnalyticAt ℂ (fun u : ℂ => 1 - a * u) u := by fun_prop
  have hres := AnalyticAt.cpow han (analyticAt_const (v := ((t : ℂ)))) h
  simpa [Submission.ModelStarDisk.diskFactor] using hres

/-- Analyticity of the disk model at a point where all bases are in the slit plane. -/
lemma analyticAt_diskPhi_of {u : ℂ}
    (h : ∀ k : Fin s, 1 - z₀ k * u ∈ Complex.slitPlane) :
    AnalyticAt ℂ (Submission.ModelStarDisk.diskPhi z₀ r) u := by
  have hfac : ∀ k ∈ (Finset.univ : Finset (Fin s)), AnalyticAt ℂ
      (fun u : ℂ => Submission.ModelStarDisk.diskFactor (z₀ k) (2 * r k) u) u :=
    fun k _ => analyticAt_diskFactor_of (h k)
  have hres := Finset.analyticAt_fun_prod (𝕜 := ℂ) (E := ℂ) (A := ℂ)
    (f := fun k : Fin s => fun u : ℂ =>
      Submission.ModelStarDisk.diskFactor (z₀ k) (2 * r k) u)
    (Finset.univ : Finset (Fin s)) hfac
  exact hres

/-- `Ψ` has derivative `-F'(u⁻¹)/u²` wherever `F` is differentiable at `u⁻¹`. -/
lemma hasDerivAt_psi_of {u : ℂ} (hu : u ≠ 0)
    (hF : DifferentiableAt ℂ (modelF z₀ r) u⁻¹) :
    HasDerivAt (psi z₀ r) (-(deriv (modelF z₀ r) u⁻¹) / u ^ 2) u := by
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

/-- `Ψ` is analytic at the interior point `u` of the unit disk. -/
lemma analyticAt_psi_of (hunit : ∀ k : Fin s, ‖z₀ k‖ = 1) {u : ℂ}
    (hu : ‖u‖ < 1) (hu0 : u ≠ 0) : AnalyticAt ℂ (psi z₀ r) u := by
  have h1 : AnalyticAt ℂ (Submission.ModelStarDisk.diskPhi z₀ r) u :=
    analyticAt_diskPhi_of (fun k => Submission.ModelStarDisk.mem_slitPlane_one_sub
      (le_of_eq (hunit k)) hu)
  exact h1.div analyticAt_id hu0

/-- `F` does not vanish on the exterior. -/
lemma modelF_ne_zero_of_mem_ext (hunit : ∀ k : Fin s, ‖z₀ k‖ = 1) {x : ℂ}
    (hx : x ∈ extSet) : modelF z₀ r x ≠ 0 := by
  have hx' : 1 < ‖x‖ := hx
  refine Submission.ModelStarStruct.modelF_ne_zero z₀ r ?_ ?_
  · intro h0
    rw [h0, norm_zero] at hx'
    exact absurd hx' (by norm_num)
  · intro k hk
    rw [hk, hunit k] at hx'
    exact absurd hx' (by norm_num)

lemma isOpen_extSet : IsOpen (extSet : Set ℂ) := by
  have : extSet = (Metric.closedBall (0 : ℂ) 1)ᶜ := by
    ext z
    rw [extSet, Set.mem_setOf_eq, Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right,
      not_le]
  rw [this]
  exact Metric.isClosed_closedBall.isOpen_compl

/-- The exterior of `F` in the `u`-variable: `Ψ` is nonzero-differentiable
at points of the unit disk. -/
lemma deriv_psi_ne_zero_of {s : ℕ} {z₀ : Fin s → ℂ} {r : Fin s → ℝ} (hs : 0 < s)
    (hunit : ∀ k, ‖z₀ k‖ = 1) (hr : ∀ k, 0 < r k) (hsum : (∑ k : Fin s, r k) = 1)
    {u : ℂ} (hu : u ≠ 0) (hu1 : ‖u‖ < 1) : deriv (psi z₀ r) u ≠ 0 :=
  Submission.ModelStarPreimageCount.deriv_psi_ne_zero hs hunit hr hsum hu hu1


/-- An open set with nonempty interior-meeting property: if `O` is a nonempty
open set and `interior M = ∅` then `O` contains a point outside `M`. -/
lemma exists_notMem_of_isOpen {O M : Set ℂ} (hO : IsOpen O) (hne : O.Nonempty)
    (hint : interior M = ∅) : ∃ x ∈ O, x ∉ M := by
  by_contra hcon
  have hsub : O ⊆ interior M := by
    intro y hy
    rw [mem_interior_iff_mem_nhds]
    refine Filter.mem_of_superset (hO.mem_nhds hy) ?_
    intro z hz
    by_contra hzM
    exact hcon ⟨z, hz, hzM⟩
  rw [hint] at hsub
  exact hne.ne_empty (Set.eq_empty_iff_forall_notMem.mpr fun x hx => hsub hx)

/-- The exterior image `F '' {1 < ‖·‖}` is open. -/
lemma isOpen_image_extSet {z₀ : Fin s → ℂ} {r : Fin s → ℝ} (hs : 0 < s)
    (hunit : ∀ k, ‖z₀ k‖ = 1) (hr : ∀ k, 0 < r k) (hsum : (∑ k : Fin s, r k) = 1) :
    IsOpen (modelF z₀ r '' extSet) := by
  haveI : NeZero s := ⟨hs.ne'⟩
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨x, hxU, rfl⟩
  have hx1 : 1 < ‖x‖ := hxU
  have hx0 : x ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hx1; exact absurd hx1 (by norm_num)
  have hxne : ∀ k, x ≠ z₀ k := by
    intro k hk
    rw [hk, hunit k] at hx1
    exact absurd hx1 (by norm_num)
  have hdiff : DifferentiableOn ℂ (modelF z₀ r) extSet :=
    Submission.ModelStarShell.modelF_differentiableOn_exterior z₀ r (fun k => le_of_eq (hunit k))
  have han : AnalyticAt ℂ (modelF z₀ r) x :=
    hdiff.analyticAt (show extSet ∈ 𝓝 x from (isOpen_extSet).mem_nhds hxU)
  have hH : Submission.ModelStarStruct.H z₀ r x ≠ 0 :=
    Submission.ModelStarStruct.H_ne_zero z₀ r hunit hr hx1.ne'
  have hder : deriv (modelF z₀ r) x ≠ 0 := by
    intro h0
    exact hH ((Submission.ModelStarStruct.deriv_modelF_eq_zero_iff z₀ r (z := x) hx0 hxne
      (fun k => Submission.ModelStarMap.factor_mem_slitPlane
        (lt_of_le_of_lt (le_of_eq (hunit k)) hx1)) hsum).mp h0)
  have hmap : Filter.map (modelF z₀ r) (𝓝 x) = 𝓝 (modelF z₀ r x) :=
    han.hasStrictDerivAt.map_nhds_eq hder
  have hmem : extSet ∈ 𝓝 x := (isOpen_extSet).mem_nhds hxU
  rw [← hmap]
  exact Filter.image_mem_map hmem

/-- A finite preconnected set has no two distinct points. -/
lemma not_finite_preconnected_two {s : Set ℂ} (hpre : IsPreconnected s) (hfin : s.Finite)
    {p q : ℂ} (hp : p ∈ s) (hq : q ∈ s) (hpq : p ≠ q) : False := by
  have h1 : IsClosed ({p} : Set ℂ) := isClosed_singleton
  have h2 : IsClosed (s \ {p}) := hfin.diff.isClosed
  have hcov : s ⊆ ({p} : Set ℂ) ∪ (s \ {p}) := by
    intro y hy
    by_cases h : y = p
    · exact Or.inl h
    · exact Or.inr ⟨hy, h⟩
  have hdisj : s ∩ (({p} : Set ℂ) ∩ (s \ {p})) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro y ⟨-, hy1, -, hy3⟩
    exact hy3 hy1
  rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hpre _ _ h1 h2 hcov hdisj) with h | h
  · exact hpq ((Set.mem_singleton_iff.mp (h hq)).symm)
  · exact (h hp).2 rfl

/-- **Main theorem (P3).**  The exterior of the model map misses the model star. -/
theorem image_ext_inter_image_eq_empty {s : ℕ} {z₀ : Fin s → ℂ} {r φ : Fin s → ℝ}
    (hs : 0 < s) (hz₀e : ∀ k, z₀ k = Submission.ModelStarBoundary2.eAngle (φ k))
    (hunit : ∀ k, ‖z₀ k‖ = 1) (hr : ∀ k, 0 < r k) (hsum : (∑ k : Fin s, r k) = 1)
    (hmono : Monotone φ) (hφinj : Function.Injective φ)
    (hφlo : ∀ k, 0 ≤ φ k) (hφhi : ∀ k, φ k < 2 * Real.pi) :
    (modelF z₀ r '' extSet) ∩ modelStarImage z₀ r = ∅ := by
  haveI : NeZero s := ⟨hs.ne'⟩
  set CV : Set ℂ := modelF z₀ r '' {u : ℂ | ‖u‖ = 1 ∧ Submission.ModelStarStruct.H z₀ r u = 0}
    with hCVdef
  have hCVfin : CV.Finite :=
    (Submission.ModelStarStruct.finite_critical_set z₀ r hunit hsum).image _
  have hN : ∀ w : ℂ, w ∉ modelStarImage z₀ r → ncardPre z₀ r w = 1 :=
    fun w hw => ncardPre_eq_one hs hz₀e hunit hr hsum hmono hφinj hφlo hφhi hw
  have hint : interior (modelStarImage z₀ r) = ∅ :=
    interior_modelStarImage_eq_empty hs hz₀e hφlo hφhi hsum hmono hφinj hr
  -- Step 1: every non-critical point of `F '' extSet ∩ M` leads to a contradiction
  have hsub : (modelF z₀ r '' extSet) ∩ modelStarImage z₀ r ⊆ CV := by
    rintro w ⟨hwU, hwM⟩
    by_contra hwCV
    obtain ⟨x, hxU, hxw⟩ := hwU
    have hx1 : 1 < ‖x‖ := hxU
    have hx0 : x ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hx1
      exact absurd hx1 (by norm_num)
    have hw0 : w ≠ 0 := by
      rw [← hxw]
      exact modelF_ne_zero_of_mem_ext hunit hxU
    obtain ⟨ζ, hζS, hζF⟩ := hwM
    have hζ1 : ‖ζ‖ = 1 := mem_circle.mp hζS
    have hζ0 : ζ ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hζ1
      exact absurd hζ1 (by norm_num)
    have hζne : ∀ k, ζ ≠ z₀ k := by
      intro k hk
      exact hw0 (by
        rw [← hζF, hk]
        exact Submission.ModelStarExterior.modelF_junction_eq_zero z₀ r hunit hr k)
    have hHζ : Submission.ModelStarStruct.H z₀ r ζ ≠ 0 := by
      intro hH
      exact hwCV ⟨ζ, ⟨hζ1, hH⟩, hζF⟩
    set u₀ : ℂ := x⁻¹ with hu₀def
    set a : ℂ := ζ⁻¹ with hadef
    have hu₀norm : ‖u₀‖ < 1 := by
      rw [hu₀def, norm_inv]
      exact inv_lt_one_of_one_lt₀ hx1
    have hu₀0 : u₀ ≠ 0 := inv_ne_zero hx0
    have hanorm : ‖a‖ = 1 := by rw [hadef, norm_inv, hζ1, inv_one]
    have hpsiu₀ : psi z₀ r u₀ = w := by
      rw [hu₀def, psi_eq_modelF_inv z₀ r (inv_ne_zero hx0), inv_inv, hxw]
    have hpsia : psi z₀ r a = w := by
      rw [hadef, psi_eq_modelF_inv z₀ r (inv_ne_zero hζ0), inv_inv, hζF]
    have hua : u₀ ≠ a := by
      intro hcon
      have : ‖u₀‖ = 1 := by rw [hcon]; exact hanorm
      linarith
    -- the local branch of `Ψ` at `u₀`
    have hanu₀ : AnalyticAt ℂ (psi z₀ r) u₀ := analyticAt_psi_of hunit hu₀norm hu₀0
    have hderu₀ : deriv (psi z₀ r) u₀ ≠ 0 :=
      deriv_psi_ne_zero_of hs hunit hr hsum hu₀0 hu₀norm
    have hstrictu₀ : HasStrictDerivAt (psi z₀ r) (deriv (psi z₀ r) u₀) u₀ :=
      hanu₀.hasStrictDerivAt
    set G : ℂ → ℂ := HasStrictDerivAt.localInverse (psi z₀ r) (deriv (psi z₀ r) u₀) u₀
      hstrictu₀ hderu₀ with hGdef
    have hGright : ∀ᶠ y in 𝓝 w, psi z₀ r (G y) = y := by
      have h := hstrictu₀.eventually_right_inverse hderu₀
      rw [hpsiu₀] at h
      simpa [hGdef] using h
    have hGcont : ContinuousAt G w := by
      have h2 := (hstrictu₀.to_localInverse hderu₀).hasDerivAt
      rw [hGdef]
      simpa [hpsiu₀] using h2.continuousAt
    -- geometry constants
    have hdist : 0 < ‖u₀ - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hua)
    have hu₀pos : 0 < ‖u₀‖ := norm_pos_iff.mpr hu₀0
    set δ : ℝ := min (min (‖u₀ - a‖ / 4) (‖u₀‖ / 2)) ((1 - ‖u₀‖) / 2) with hδdef
    have hδpos : 0 < δ := lt_min (lt_min (by linarith) (by linarith)) (by linarith)
    have hδa : δ ≤ ‖u₀ - a‖ / 4 := le_trans (min_le_left _ _) (min_le_left _ _)
    have hδu : δ ≤ ‖u₀‖ / 2 := le_trans (min_le_left _ _) (min_le_right _ _)
    have hδ1u : δ ≤ (1 - ‖u₀‖) / 2 := min_le_right _ _
    set ε : ℝ := min (‖u₀ - a‖ / 4) (1 / 2) with hεdef
    have hεpos : 0 < ε := lt_min (by linarith) (by norm_num)
    have hεa : ε ≤ ‖u₀ - a‖ / 4 := min_le_left _ _
    have hεhalf : ε ≤ 1 / 2 := min_le_right _ _
    obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := Metric.mem_nhds_iff.mp hGright
    have hGu₀ : G w = u₀ := by
      have h := hstrictu₀.eventually_left_inverse hderu₀
      have h' : G (psi z₀ r u₀) = u₀ := h.self_of_nhds
      simpa [hGdef, hpsiu₀] using h'
    obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := Metric.mem_nhds_iff.mp
      (hGcont.eventually (show ∀ᶠ y in 𝓝 (G w), y ∈ Metric.ball u₀ δ from by
        rw [hGu₀]; exact Metric.ball_mem_nhds u₀ hδpos))
    set m : ℝ := min (min δ₁ δ₂) δ with hmdef
    have hmpos : 0 < m := lt_min (lt_min hδ₁pos hδ₂pos) hδpos
    have hmδ₁ : m ≤ δ₁ := le_trans (min_le_left _ _) (min_le_left _ _)
    have hmδ₂ : m ≤ δ₂ := le_trans (min_le_left _ _) (min_le_right _ _)
    have hmδ : m ≤ δ := min_le_right _ _
    -- `D = Ψ '' (ball a ε ∩ disk)` is open
    have hDopen : IsOpen (psi z₀ r '' (Metric.ball a ε ∩ Metric.ball (0 : ℂ) 1)) := by
      rw [isOpen_iff_mem_nhds]
      rintro _ ⟨u, hu, rfl⟩
      have hu1 : ‖u‖ < 1 := by
        have := hu.2
        rw [Metric.mem_ball, dist_zero_right] at this
        exact this
      have hu0 : u ≠ 0 := by
        intro h0
        have h2 : ‖a‖ < ε := by
          have h3 : (0 : ℂ) ∈ Metric.ball a ε := h0 ▸ hu.1
          rw [Metric.mem_ball, dist_comm, dist_eq_norm, sub_zero] at h3
          exact h3
        rw [hanorm] at h2
        linarith [hεhalf]
      have han : AnalyticAt ℂ (psi z₀ r) u := analyticAt_psi_of hunit hu1 hu0
      have hder : deriv (psi z₀ r) u ≠ 0 := deriv_psi_ne_zero_of hs hunit hr hsum hu0 hu1
      have hmap : Filter.map (psi z₀ r) (𝓝 u) = 𝓝 (psi z₀ r u) :=
        han.hasStrictDerivAt.map_nhds_eq hder
      have hmem : Metric.ball a ε ∩ Metric.ball (0 : ℂ) 1 ∈ 𝓝 u :=
        (Metric.isOpen_ball.inter Metric.isOpen_ball).mem_nhds hu
      rw [← hmap]
      exact Filter.image_mem_map hmem
    -- `D` meets every neighbourhood of `w`
    have ha0 : a ≠ 0 := inv_ne_zero hζ0
    have hcont_a : ContinuousAt (psi z₀ r) a := by
      have h1 : ContinuousAt (Submission.ModelStarDisk.diskPhi z₀ r) a :=
        (analyticAt_diskPhi_of (fun k => one_sub_mul_mem_slitPlane (hunit k) hanorm (by
          intro hcon
          refine hζne k ?_
          have h2 : z₀ k * a = 1 := (sub_eq_zero.mp hcon).symm
          have h4 : z₀ k = 1 * a⁻¹ := by rw [← h2, mul_assoc, mul_inv_cancel₀ ha0, mul_one]
          rw [h4, one_mul, hadef, inv_inv]))).continuousAt
      exact h1.div continuousAt_id ha0
    obtain ⟨η, hηpos, hη⟩ := Metric.mem_nhds_iff.mp
      (hcont_a.tendsto.eventually (show ∀ᶠ y in 𝓝 (psi z₀ r a), y ∈ Metric.ball w m from by
        rw [hpsia]; exact Metric.ball_mem_nhds w hmpos))
    -- the explicit interior point of `D ∩ ball w m`
    set c : ℝ := min ε η / 2 with hcdef
    have hcpos : 0 < c := by rw [hcdef]; linarith [lt_min hεpos hηpos]
    have hcle : c < ε := by rw [hcdef]; linarith [min_le_left ε η, hεpos]
    have hclt1 : c < 1 := by rw [hcdef]; linarith [min_le_left ε η, hεhalf]
    have hcη : c < η := by rw [hcdef]; linarith [min_le_right ε η, hηpos]
    have hu_ball : a * (1 - (c : ℂ)) ∈ Metric.ball a ε ∩ Metric.ball (0 : ℂ) 1 := by
      constructor
      · rw [Metric.mem_ball, dist_eq_norm]
        have h1 : a * (1 - (c : ℂ)) - a = -(a * (c : ℂ)) := by ring
        rw [h1, norm_neg, norm_mul, hanorm, one_mul]
        have h2 : ‖(c : ℂ)‖ = c := by
          rw [show ‖(c : ℂ)‖ = |c| from RCLike.norm_ofReal c, abs_of_nonneg hcpos.le]
        rw [h2]
        exact hcle
      · rw [Metric.mem_ball, dist_zero_right]
        have h1 : a * (1 - (c : ℂ)) = a * (((1 - c : ℝ)) : ℂ) := by push_cast; ring
        rw [h1, norm_mul, hanorm, one_mul]
        have h2 : ‖(((1 - c : ℝ)) : ℂ)‖ = 1 - c := by
          rw [show ‖(((1 - c : ℝ)) : ℂ)‖ = |1 - c| from RCLike.norm_ofReal (1 - c),
            abs_of_nonneg (by linarith)]
        rw [h2]
        linarith
    have hu_eta : ‖psi z₀ r (a * (1 - (c : ℂ))) - w‖ < m := by
      have hmem : a * (1 - (c : ℂ)) ∈ Metric.ball a η := by
        rw [Metric.mem_ball, dist_eq_norm]
        have h1 : a * (1 - (c : ℂ)) - a = -(a * (c : ℂ)) := by ring
        rw [h1, norm_neg, norm_mul, hanorm, one_mul]
        have h2 : ‖(c : ℂ)‖ = c := by
          rw [show ‖(c : ℂ)‖ = |c| from RCLike.norm_ofReal c, abs_of_nonneg hcpos.le]
        rw [h2]
        exact hcη
      have h3 : psi z₀ r (a * (1 - (c : ℂ))) ∈ Metric.ball w m := hη hmem
      rw [Metric.mem_ball, dist_eq_norm] at h3
      exact h3
    have hDne : (psi z₀ r '' (Metric.ball a ε ∩ Metric.ball (0 : ℂ) 1) ∩
        Metric.ball w m).Nonempty :=
      ⟨psi z₀ r (a * (1 - (c : ℂ))), ⟨⟨_, hu_ball, rfl⟩, by
        simpa [Metric.mem_ball, dist_eq_norm] using hu_eta⟩⟩
    -- pick `w' ∉ M` in the (open, nonempty) set
    obtain ⟨w', hw'D, hw'm⟩ := exists_notMem_of_isOpen
      (hDopen.inter Metric.isOpen_ball) hDne hint
    obtain ⟨u, hu_ball', hPsiu⟩ := hw'D.1
    have hu1' : ‖u‖ < 1 := by
      have h := hu_ball'.2
      rwa [Metric.mem_ball, dist_zero_right] at h
    have hu0' : u ≠ 0 := by
      intro h0
      have h2 : (0 : ℂ) ∈ Metric.ball a ε := h0 ▸ hu_ball'.1
      rw [Metric.mem_ball, dist_comm, dist_eq_norm, sub_zero] at h2
      rw [hanorm] at h2
      linarith [hεhalf]
    -- the two zeros of `diskPhi - w'·id` in the disk
    have hz₁ : u ∈ (fun u : ℂ => Submission.ModelStarDisk.diskPhi z₀ r u - w' * u) ⁻¹' {0} ∩
        disk := by
      refine ⟨?_, ?_⟩
      · have h1 : Submission.ModelStarDisk.diskPhi z₀ r u - w' * u = 0 := by
          rw [diskPhi_sub_eq_mul_psi z₀ r hu0', hPsiu]
          ring
        simpa using h1
      · rw [disk, Metric.mem_ball, dist_zero_right]; exact hu1'
    have hw'dist : dist w' w < m := by
      have h := hw'D.2
      rwa [Metric.mem_ball] at h
    have hGw'₁ : psi z₀ r (G w') = w' := by
      refine hδ₁ ?_
      rw [Metric.mem_ball]
      exact lt_of_lt_of_le hw'dist hmδ₁
    have hGw'₂ : ‖G w' - u₀‖ < δ := by
      have h := hδ₂ (by
        rw [Metric.mem_ball]
        exact lt_of_lt_of_le hw'dist hmδ₂)
      have h' : G w' ∈ Metric.ball u₀ δ := h
      rw [Metric.mem_ball, dist_eq_norm] at h'
      exact h'
    have hG0 : G w' ≠ 0 := by
      intro h0
      have h2 : ‖G w' - u₀‖ = ‖u₀‖ := by rw [h0, zero_sub, norm_neg]
      linarith [hδu, hGw'₂]
    have hG1 : ‖G w'‖ < 1 := by
      have h2 : ‖G w'‖ ≤ ‖G w' - u₀‖ + ‖u₀‖ := by
        have h3 : (G w' - u₀) + u₀ = G w' := sub_add_cancel _ _
        calc ‖G w'‖ = ‖(G w' - u₀) + u₀‖ := by rw [h3]
          _ ≤ ‖G w' - u₀‖ + ‖u₀‖ := norm_add_le _ _
      linarith [hδ1u]
    have hz₂ : G w' ∈ (fun u : ℂ => Submission.ModelStarDisk.diskPhi z₀ r u - w' * u) ⁻¹' {0} ∩
        disk := by
      refine ⟨?_, ?_⟩
      · have h1 : Submission.ModelStarDisk.diskPhi z₀ r (G w') - w' * (G w') = 0 := by
          rw [diskPhi_sub_eq_mul_psi z₀ r hG0, hGw'₁]
          ring
        simpa using h1
      · rw [disk, Metric.mem_ball, dist_zero_right]; exact hG1
    have hne : u ≠ G w' := by
      intro hcon
      have h1 : ‖u - a‖ < ε := by
        have h := hu_ball'.1
        rw [Metric.mem_ball] at h
        rwa [dist_eq_norm] at h
      have h5 : ‖u₀ - G w'‖ < δ := by
        rw [norm_sub_rev]
        exact hGw'₂
      have h2 : ‖u₀ - a‖ ≤ ‖u₀ - u‖ + ‖u - a‖ := by
        have h3 : u₀ - a = (u₀ - u) + (u - a) := by ring
        calc ‖u₀ - a‖ = ‖(u₀ - u) + (u - a)‖ := by rw [h3]
          _ ≤ ‖u₀ - u‖ + ‖u - a‖ := norm_add_le _ _
      rw [hcon] at h1 h2
      linarith [h2, h5, h1, hδa, hεa]
    -- contradiction with `N w' = 1`
    have hNw' : ncardPre z₀ r w' = 1 := hN w' hw'm
    rw [ncard_preimage_eq_ncard_zeros] at hNw'
    obtain ⟨c₀, hc₀⟩ := Set.ncard_eq_one.mp hNw'
    have huc : u = c₀ := by
      have : u ∈ (fun u : ℂ => Submission.ModelStarDisk.diskPhi z₀ r u - w' * u) ⁻¹' {0} ∩ disk := hz₁
      rw [hc₀] at this
      simpa using this
    have hGc : G w' = c₀ := by
      have : G w' ∈ (fun u : ℂ => Submission.ModelStarDisk.diskPhi z₀ r u - w' * u) ⁻¹' {0} ∩
          disk := hz₂
      rw [hc₀] at this
      simpa using this
    exact hne (huc.trans hGc.symm)
  -- Step 2: the intersection is a relatively open subset of the continuum `M`
  -- contained in the finite set `CV`, hence empty
  rw [Set.eq_empty_iff_forall_notMem]
  intro y hy
  have hpre : IsPreconnected (modelStarImage z₀ r) :=
    Submission.ModelStarExterior.isPreconnected_modelStarImage z₀ r hunit hr
  have hOopen : IsOpen (modelF z₀ r '' extSet) := isOpen_image_extSet hs hunit hr hsum
  have hAfin : ((modelF z₀ r '' extSet) ∩ modelStarImage z₀ r).Finite :=
    Set.Finite.subset hCVfin hsub
  have hAc : IsClosed ((modelF z₀ r '' extSet) ∩ modelStarImage z₀ r) := hAfin.isClosed
  have hcov : modelStarImage z₀ r ⊆ (modelF z₀ r '' extSet) ∪
      ((modelF z₀ r '' extSet) ∩ modelStarImage z₀ r)ᶜ := by
    intro z hz
    by_cases h : z ∈ modelF z₀ r '' extSet
    · exact Or.inl h
    · exact Or.inr fun hcon => h hcon.1
  have hdisj : modelStarImage z₀ r ∩ ((modelF z₀ r '' extSet) ∩
      ((modelF z₀ r '' extSet) ∩ modelStarImage z₀ r)ᶜ) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro z hz
    exact hz.2.2 ⟨hz.2.1, hz.1⟩
  rcases (isPreconnected_iff_subset_of_disjoint.mp hpre _ _ hOopen hAc.isOpen_compl hcov hdisj)
    with hM | hM
  · -- `M ⊆ F '' extSet`: then the intersection is all of `M`, which is finite
    obtain ⟨p, hpM, q, hqM, hpq⟩ :=
      Submission.ModelStarExterior.modelStarImage_two z₀ r hunit hr hs
    have hAeq : (modelF z₀ r '' extSet) ∩ modelStarImage z₀ r = modelStarImage z₀ r := by
      apply Subset.antisymm
      · exact inter_subset_right
      · intro z hz
        exact ⟨hM hz, hz⟩
    exact not_finite_preconnected_two hpre (by rw [← hAeq]; exact hAfin) hpM hqM hpq
  · exact hM hy.2 hy

