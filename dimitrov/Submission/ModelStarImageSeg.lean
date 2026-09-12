import Mathlib
import Submission.ModelStarExterior
import Submission.ModelStarBoundary2
import Submission.ModelStarBoundary3
import Submission.ModelStarBoundary4
import Submission.ModelStarBoundary5
import Submission.ModelStarBoundary6
import Submission.ModelStarBoundary7

/-!
# ModelStarImageSeg -- the model star as a finite union of segments

STATUS: work in progress (research isolate; NOT imported by `Submission.lean`).

For the model map `F = modelF z₀ r` with junctions `z₀ k = eAngle (φ k)`,
`φ` monotone injective, `0 ≤ φ k < 2π`, `Σ r k = 1` and `0 < r k`, the
circle is split by the `s` junctions into `s` arcs; on each arc `F` maps
onto a segment `[0, m]·u` (this file's `ArcGood`), so

  * `M := modelStarImage z₀ r = F '' unitCircle` is contained in a finite
    union of segments through the origin (with the corresponding
    `mem_seg` converse),
  * `M` has empty interior,
  * the outward radial ray from a point outside `M` never meets `M`
    (the property that propagates local constancy of preimage counts to
    all of `ℂ ∖ M`).

-/

noncomputable section

open scoped Real BigOperators Topology
open Filter Set Complex MeasureTheory

namespace Submission.ModelStarImageSeg

open Submission.ModelStarMap
open Submission.ModelStarBoundary2 (eAngle)
open Submission.ModelStarBoundary3 (rho)
open Submission.ModelStarExterior
open Submission.ModelStarBoundary7 (wrapA wrapB wrapFirst wrapLast)

variable {s : ℕ}

/-! ## Basic `rho` facts -/

lemma rho_nonneg (φ r : Fin s → ℝ) (t : ℝ) : 0 ≤ rho φ r t := by
  unfold Submission.ModelStarBoundary3.rho
  exact Finset.prod_nonneg fun k _ => Real.rpow_nonneg (norm_nonneg _) _

lemma rho_le_four {φ r : Fin s → ℝ} (hsum : (∑ k : Fin s, r k) = 1)
    (hr : ∀ k : Fin s, 0 ≤ r k) (t : ℝ) : rho φ r t ≤ 4 := by
  refine le_trans (Submission.ModelStarBoundary5.rho_le_uniform_bound φ r hr t) ?_
  rw [← Real.rpow_sum_of_pos (by norm_num : (0:ℝ) < 2)]
  have h2 : (∑ k : Fin s, 2 * r k) = 2 := by
    rw [← Finset.mul_sum, hsum, mul_one]
  rw [h2, Real.rpow_two]
  norm_num

/-! ## The arcs of the junction decomposition -/

/-- The angle of the junction following `φ j` cyclically (lifted above `2π`
for the last one). -/
def nextJunction (φ : Fin s → ℝ) (hs : 0 < s) (j : Fin s) : ℝ :=
  if h : j.val + 1 < s then φ ⟨j.val + 1, h⟩ else φ ⟨0, hs⟩ + 2 * Real.pi

lemma nextJunction_of_lt {φ : Fin s → ℝ} {hs : 0 < s} {j : Fin s}
    (h : j.val + 1 < s) : nextJunction φ hs j = φ ⟨j.val + 1, h⟩ := dif_pos h

lemma nextJunction_of_not_lt {φ : Fin s → ℝ} {hs : 0 < s} {j : Fin s}
    (h : ¬ j.val + 1 < s) : nextJunction φ hs j = φ ⟨0, hs⟩ + 2 * Real.pi := dif_neg h

lemma eq_wrapLast_of_not_lt {j : Fin s} (hs : 0 < s) (h : ¬ j.val + 1 < s) :
    j = wrapLast s hs := by
  apply Fin.ext
  have h1 : j.val = s - 1 := by omega
  have h2 : (wrapLast s hs).val = s - 1 := rfl
  rw [h1, h2]

lemma nextJunction_gt {φ : Fin s → ℝ} (hs : 0 < s) (hmono : Monotone φ)
    (hφinj : Function.Injective φ) (hφlo : ∀ k, 0 ≤ φ k) (hφhi : ∀ k, φ k < 2 * Real.pi)
    (j : Fin s) : φ j < nextJunction φ hs j := by
  by_cases h : j.val + 1 < s
  · rw [nextJunction_of_lt h]
    exact Submission.ModelStarBoundary5.consecutive_lt φ hmono hφinj h
  · rw [nextJunction_of_not_lt h]
    have h1 : φ j < 2 * Real.pi := hφhi j
    have h2 : 0 ≤ φ ⟨0, hs⟩ := hφlo _
    linarith

/-! ## The per-arc data -/

/-- The statement that the `j`-th arc of the junction decomposition sweeps
the segment `[0,m]·u`. -/
def ArcGood (z₀ : Fin s → ℂ) (r φ : Fin s → ℝ) (hs : 0 < s) (j : Fin s)
    (u : ℂ) (m : ℝ) : Prop :=
  ‖u‖ = 1 ∧ 0 ≤ m ∧
  (∀ t : ℝ, t ∈ Ioo (φ j) (nextJunction φ hs j) →
      modelF z₀ r (eAngle t) = (rho φ r t : ℂ) * u) ∧
  (∀ t : ℝ, t ∈ Icc (φ j) (nextJunction φ hs j) → rho φ r t ≤ m) ∧
  (∀ x : ℝ, x ∈ Icc 0 m → (x : ℂ) * u ∈ modelStarImage z₀ r)


/-! ## Zero lies in the model star -/

lemma zero_mem_modelStarImage {z₀ : Fin s → ℂ} {r φ : Fin s → ℝ} (hs : 0 < s)
    (hz₀e : ∀ k : Fin s, z₀ k = eAngle (φ k)) (hr : ∀ k : Fin s, 0 < r k) :
    (0 : ℂ) ∈ modelStarImage z₀ r := by
  refine ⟨eAngle (φ ⟨0, hs⟩), ?_, ?_⟩
  · rw [mem_circle]
    exact Submission.ModelStarBoundary4.eAngle_norm _
  · exact Submission.ModelStarBoundary6.modelF_junction_value_zero z₀ r φ hz₀e (hr ⟨0, hs⟩)

/-! ## Generic segment-sweep helper -/

/-- If the model boundary map equals `rho · u` on a junction-free interval
`(a,b)`, `rho` is continuous there with zero limits at the endpoints and
attains its supremum `m` at an interior point, then the whole segment
`[0,m]·u` lies in the model star. -/
lemma mem_seg_aux {z₀ : Fin s → ℂ} {r φ : Fin s → ℝ} {u : ℂ} {a b : ℝ} (hab : a < b)
    (hu2 : ∀ t : ℝ, t ∈ Ioo a b →
      modelF z₀ r (eAngle t) = (rho φ r t : ℂ) * u)
    (hcont : ContinuousOn (fun t : ℝ => rho φ r t) (Ioo a b))
    (hBdd : BddAbove ((fun t : ℝ => rho φ r t) '' Ioo a b))
    (hpa : Tendsto (fun t : ℝ => rho φ r t) (𝓝[>] a) (𝓝 0))
    (hpb : Tendsto (fun t : ℝ => rho φ r t) (𝓝[<] b) (𝓝 0))
    (hmax : ∃ t₀ : ℝ, t₀ ∈ Ioo a b ∧
      (∀ t : ℝ, t ∈ Icc a b → rho φ r t ≤ rho φ r t₀) ∧
      rho φ r t₀ = sSup ((fun t : ℝ => rho φ r t) '' Ioo a b))
    (hzero : (0 : ℂ) ∈ modelStarImage z₀ r)
    {x : ℝ} (hx : x ∈ Icc 0 (sSup ((fun t : ℝ => rho φ r t) '' Ioo a b))) :
    (x : ℂ) * u ∈ modelStarImage z₀ r := by
  rcases hmax with ⟨t₀, ht₀, ht₀max, ht₀sup⟩
  have hx0 : 0 ≤ x := hx.1
  have hxm : x ≤ sSup ((fun t : ℝ => rho φ r t) '' Ioo a b) := hx.2
  rcases eq_or_lt_of_le hx0 with hx_zero | hx_pos
  · rw [← hx_zero]
    simpa using hzero
  · rcases eq_or_lt_of_le hxm with hxm_eq | hxm_lt
    · refine ⟨eAngle t₀, ?_, ?_⟩
      · rw [mem_circle]
        exact Submission.ModelStarBoundary4.eAngle_norm _
      · rw [hu2 t₀ ht₀, hxm_eq, ← ht₀sup]
    · obtain ⟨t, ht, hrt⟩ :=
        Commons.Analysis.Interval.surjOn_Ioo_zero_sSup (p := fun t : ℝ => rho φ r t)
          hab hcont hBdd hpa hpb x hx_pos hxm_lt
      refine ⟨eAngle t, ?_, ?_⟩
      · rw [mem_circle]
        exact Submission.ModelStarBoundary4.eAngle_norm _
      · rw [hu2 t ht, hrt]


/-! ## The per-arc data: consecutive arc -/

lemma rho_continuous (φ r : Fin s → ℝ) (hr : ∀ k, 0 ≤ r k) :
    Continuous (fun t : ℝ => rho φ r t) :=
  continuous_iff_continuousAt.2 fun t => Submission.ModelStarBoundary3.rho_continuousAt φ r hr t

lemma rho_bddAbove {φ r : Fin s → ℝ} (hr : ∀ k : Fin s, 0 ≤ r k) (a b : ℝ) :
    BddAbove ((fun t : ℝ => rho φ r t) '' Ioo a b) := by
  refine ⟨∏ k : Fin s, (2 : ℝ) ^ (2 * r k), ?_⟩
  rintro y ⟨t, _, rfl⟩
  exact Submission.ModelStarBoundary5.rho_le_uniform_bound φ r hr t

lemma arcGood_consec {z₀ : Fin s → ℂ} {r φ : Fin s → ℝ} (hs : 0 < s)
    (hz₀e : ∀ k : Fin s, z₀ k = eAngle (φ k))
    (hφlo : ∀ k : Fin s, 0 ≤ φ k) (hφhi : ∀ k : Fin s, φ k < 2 * Real.pi)
    (hsum : (∑ k : Fin s, r k) = 1) (hmono : Monotone φ)
    (hφinj : Function.Injective φ) (hr : ∀ k : Fin s, 0 < r k)
    {j : Fin s} (hj : j.val + 1 < s) :
    ∃ u m, ArcGood z₀ r φ hs j u m := by
  let j1 : Fin s := ⟨j.val + 1, hj⟩
  have hnext : nextJunction φ hs j = φ j1 :=
    nextJunction_of_lt (φ := φ) (hs := hs) (j := j) hj
  have hab : φ j < φ j1 := by
    simpa [j1] using Submission.ModelStarBoundary5.consecutive_lt φ hmono hφinj hj
  have hjf : ∀ k : Fin s, φ k ∉ Ioo (φ j) (φ j1) := by
    simpa [j1] using Submission.ModelStarBoundary5.no_junction_between_consecutive φ hmono hj
  have hI : Ioo (φ j) (φ j1) ⊆ Ioo 0 (2 * Real.pi) := by
    intro t ht
    exact ⟨lt_of_le_of_lt (hφlo j) ht.1, lt_trans ht.2 (hφhi j1)⟩
  obtain ⟨u, hu1, hu2⟩ := Submission.ModelStarBoundary4.boundaryMap_on_junctionFree_interval
    z₀ r φ hz₀e hφlo hφhi hsum hab hI hjf
  obtain ⟨t₀, ht₀, ht₀max, ht₀sup⟩ := Submission.ModelStarBoundary6.rho_max_on_closedArc
    φ r hφlo hφhi (fun k => (hr k).le) hmono hφinj hj (hr j) (hr j1)
  have hmid : (φ j + φ j1) / 2 ∈ Ioo (φ j) (φ j1) := ⟨by linarith, by linarith⟩
  have hm_nonneg : 0 ≤ sSup ((fun t : ℝ => rho φ r t) '' Ioo (φ j) (φ j1)) :=
    le_trans (rho_nonneg φ r _)
      (le_csSup (rho_bddAbove (fun k => (hr k).le) _ _) ⟨_, hmid, rfl⟩)
  refine ⟨u, sSup ((fun t : ℝ => rho φ r t) '' Ioo (φ j) (φ j1)),
    hu1, hm_nonneg, ?_, ?_, ?_⟩
  · intro t ht
    rw [hnext] at ht
    exact hu2 t ht
  · intro t ht
    rw [hnext] at ht
    exact le_trans (ht₀max t ht) (le_of_eq ht₀sup)
  · intro x hx
    exact mem_seg_aux (z₀ := z₀) (r := r) (φ := φ) hab hu2
      (rho_continuous φ r (fun k => (hr k).le)).continuousOn
      (rho_bddAbove (fun k => (hr k).le) _ _)
      ((Submission.ModelStarBoundary3.rho_tendsto_junction_zero φ r (fun k => (hr k).le)
        (j := j) (hr j)).mono_left nhdsWithin_le_nhds)
      ((Submission.ModelStarBoundary3.rho_tendsto_junction_zero φ r (fun k => (hr k).le)
        (j := j1) (hr j1)).mono_left nhdsWithin_le_nhds)
      ⟨t₀, ht₀, ht₀max, ht₀sup⟩ (zero_mem_modelStarImage hs hz₀e hr) hx

/-! ## The per-arc data: wrap arc -/

lemma arcGood_wrap {z₀ : Fin s → ℂ} {r φ : Fin s → ℝ} (hs : 0 < s)
    (hz₀e : ∀ k : Fin s, z₀ k = eAngle (φ k))
    (hφlo : ∀ k : Fin s, 0 ≤ φ k) (hφhi : ∀ k : Fin s, φ k < 2 * Real.pi)
    (hsum : (∑ k : Fin s, r k) = 1) (hmono : Monotone φ)
    (hr : ∀ k : Fin s, 0 < r k)
    {j : Fin s} (hj : ¬ j.val + 1 < s) :
    ∃ u m, ArcGood z₀ r φ hs j u m := by
  have hjlast : j = wrapLast s hs := eq_wrapLast_of_not_lt hs hj
  have hnext : nextJunction φ hs j = wrapB φ hs := by
    rw [nextJunction_of_not_lt hj]
  subst hjlast
  obtain ⟨u, hu1, hu2⟩ := Submission.ModelStarBoundary7.wrap_ray hs z₀ r φ hz₀e hφlo hφhi
    hsum hmono (fun k => (hr k).le)
  obtain ⟨t₀, ht₀, ht₀max, ht₀sup⟩ := Submission.ModelStarBoundary7.rho_max_on_wrap hs φ r
    hφlo hφhi hmono (fun k => (hr k).le) (hr _) (hr _)
  have hab : wrapA φ hs < wrapB φ hs :=
    Submission.ModelStarBoundary7.wrapA_lt_wrapB (s := s) hs (φ := φ) hφlo hφhi
  have hmid : (wrapA φ hs + wrapB φ hs) / 2 ∈ Ioo (wrapA φ hs) (wrapB φ hs) :=
    ⟨by linarith, by linarith⟩
  have hm_nonneg : 0 ≤ sSup ((fun t : ℝ => rho φ r t) '' Ioo (wrapA φ hs) (wrapB φ hs)) :=
    le_trans (rho_nonneg φ r _)
      (le_csSup (rho_bddAbove (fun k => (hr k).le) _ _) ⟨_, hmid, rfl⟩)
  refine ⟨u, sSup ((fun t : ℝ => rho φ r t) '' Ioo (wrapA φ hs) (wrapB φ hs)),
    hu1, hm_nonneg, ?_, ?_, ?_⟩
  · intro t ht
    rw [hnext] at ht
    exact hu2 t ht
  · intro t ht
    rw [hnext] at ht
    exact le_trans (ht₀max t ht) (le_of_eq ht₀sup)
  · intro x hx
    exact mem_seg_aux (z₀ := z₀) (r := r) (φ := φ) hab hu2
      (rho_continuous φ r (fun k => (hr k).le)).continuousOn
      (rho_bddAbove (fun k => (hr k).le) _ _)
      (Submission.ModelStarBoundary7.rho_tendsto_wrapA hs r (fun k => (hr k).le) (hr _))
      (Submission.ModelStarBoundary7.rho_tendsto_wrapB hs r (fun k => (hr k).le) (hr _))
      ⟨t₀, ht₀, ht₀max, ht₀sup⟩ (zero_mem_modelStarImage hs hz₀e hr) hx


/-! ## Covering the circle by the arcs -/

/-- Every `t ∈ [φ 0, φ 0 + 2π]` lies in one of the closed arcs
`[φ j, nextJunction φ hs j]`. -/
lemma exists_arc_of_mem_Icc {φ : Fin s → ℝ} (hs : 0 < s) (hmono : Monotone φ)
    (hφlo : ∀ k : Fin s, 0 ≤ φ k) (hφhi : ∀ k : Fin s, φ k < 2 * Real.pi)
    {t : ℝ} (ht : t ∈ Icc (φ ⟨0, hs⟩) (φ ⟨0, hs⟩ + 2 * Real.pi)) :
    ∃ j : Fin s, φ j ≤ t ∧ t ≤ nextJunction φ hs j := by
  classical
  let S : Finset (Fin s) := Finset.univ.filter (fun j : Fin s => φ j ≤ t)
  have h0 : (⟨0, hs⟩ : Fin s) ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ht.1
  have hSne : S.Nonempty := ⟨_, h0⟩
  refine ⟨S.max' hSne, ?_, ?_⟩
  · exact (Finset.mem_filter.mp (Finset.max'_mem S hSne)).2
  · by_cases hlt : (S.max' hSne).val + 1 < s
    · rw [nextJunction_of_lt hlt]
      by_contra hcon
      rw [not_le] at hcon
      have hmem : (⟨(S.max' hSne).val + 1, hlt⟩ : Fin s) ∈ S := by
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hcon.le
      have hle := Finset.le_max' S _ hmem
      simp only [Fin.le_def] at hle
      omega
    · rw [nextJunction_of_not_lt hlt]
      exact ht.2

/-- Every circle point is a value of `eAngle` at a point of one of the
closed arcs, up to the `2π`-periodicity of `eAngle`. -/
lemma exists_arc_of_mem_Icc_lift {φ : Fin s → ℝ} (hs : 0 < s) (hmono : Monotone φ)
    (hφlo : ∀ k : Fin s, 0 ≤ φ k) (hφhi : ∀ k : Fin s, φ k < 2 * Real.pi)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 2 * Real.pi) :
    ∃ j : Fin s, ∃ t' : ℝ, eAngle t' = eAngle t ∧ φ j ≤ t' ∧ t' ≤ nextJunction φ hs j := by
  by_cases h : t < φ ⟨0, hs⟩
  · have ht' : t + 2 * Real.pi ∈ Icc (φ ⟨0, hs⟩) (φ ⟨0, hs⟩ + 2 * Real.pi) := by
      refine ⟨?_, by linarith⟩
      have h2 : φ ⟨0, hs⟩ < 2 * Real.pi := hφhi _
      linarith
    obtain ⟨j, hj1, hj2⟩ := exists_arc_of_mem_Icc hs hmono hφlo hφhi ht'
    exact ⟨j, t + 2 * Real.pi, by rw [Submission.ModelStarBoundary7.eAngle_add_two_pi], hj1, hj2⟩
  · have ht' : t ∈ Icc (φ ⟨0, hs⟩) (φ ⟨0, hs⟩ + 2 * Real.pi) := by
      refine ⟨le_of_not_gt h, by linarith [hφlo ⟨0, hs⟩]⟩
    obtain ⟨j, hj1, hj2⟩ := exists_arc_of_mem_Icc hs hmono hφlo hφhi ht'
    exact ⟨j, t, rfl, hj1, hj2⟩

lemma modelF_eAngle_nextJunction_eq_zero {z₀ : Fin s → ℂ} {r φ : Fin s → ℝ} (hs : 0 < s)
    (hz₀e : ∀ k : Fin s, z₀ k = eAngle (φ k)) (hr : ∀ k : Fin s, 0 < r k) (j : Fin s) :
    modelF z₀ r (eAngle (nextJunction φ hs j)) = 0 := by
  by_cases h : j.val + 1 < s
  · rw [nextJunction_of_lt h]
    exact Submission.ModelStarBoundary6.modelF_junction_value_zero z₀ r φ hz₀e (hr _)
  · rw [nextJunction_of_not_lt h, Submission.ModelStarBoundary7.eAngle_add_two_pi]
    exact Submission.ModelStarBoundary6.modelF_junction_value_zero z₀ r φ hz₀e (hr _)

/-- Every point of the unit circle is a value of `eAngle` at some real `t`
with `0 ≤ t ≤ 2π`. -/
lemma exists_eAngle_eq_of_mem_circle {z : ℂ} (hz : z ∈ unitCircle) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 2 * Real.pi ∧ eAngle t = z := by
  have hz1 : ‖z‖ = 1 := mem_circle.mp hz
  have harg : eAngle (Complex.arg z) = z := by
    have h := Complex.norm_mul_exp_arg_mul_I z
    rw [hz1] at h
    simp only [Complex.ofReal_one, one_mul] at h
    simpa [Submission.ModelStarBoundary2.eAngle] using h
  rcases le_or_gt 0 (Complex.arg z) with h0 | h0
  · exact ⟨Complex.arg z, h0, le_trans (Complex.arg_le_pi z) (by linarith [Real.pi_pos]), harg⟩
  · refine ⟨Complex.arg z + 2 * Real.pi, by linarith [Complex.neg_pi_lt_arg z], by
      linarith, ?_⟩
    rw [Submission.ModelStarBoundary7.eAngle_add_two_pi, harg]

/-! ## The main structural statements -/

theorem exists_arcGood {z₀ : Fin s → ℂ} {r φ : Fin s → ℝ} (hs : 0 < s)
    (hz₀e : ∀ k : Fin s, z₀ k = eAngle (φ k))
    (hφlo : ∀ k : Fin s, 0 ≤ φ k) (hφhi : ∀ k : Fin s, φ k < 2 * Real.pi)
    (hsum : (∑ k : Fin s, r k) = 1) (hmono : Monotone φ)
    (hφinj : Function.Injective φ) (hr : ∀ k : Fin s, 0 < r k) (j : Fin s) :
    ∃ u m, ArcGood z₀ r φ hs j u m := by
  by_cases h : j.val + 1 < s
  · exact arcGood_consec hs hz₀e hφlo hφhi hsum hmono hφinj hr h
  · exact arcGood_wrap hs hz₀e hφlo hφhi hsum hmono hr h

/-- **The model star is a finite union of segments through the origin.** -/
theorem modelStarImage_subset_segments {z₀ : Fin s → ℂ} {r φ : Fin s → ℝ} (hs : 0 < s)
    (hz₀e : ∀ k : Fin s, z₀ k = eAngle (φ k))
    (hφlo : ∀ k : Fin s, 0 ≤ φ k) (hφhi : ∀ k : Fin s, φ k < 2 * Real.pi)
    (hsum : (∑ k : Fin s, r k) = 1) (hmono : Monotone φ)
    (hφinj : Function.Injective φ) (hr : ∀ k : Fin s, 0 < r k) :
    ∃ (u : Fin s → ℂ) (m : Fin s → ℝ),
      (∀ j : Fin s, ArcGood z₀ r φ hs j (u j) (m j)) ∧
      modelStarImage z₀ r ⊆
        ⋃ j : Fin s, {w : ℂ | ∃ c : ℝ, 0 ≤ c ∧ c ≤ m j ∧ w = (c : ℂ) * u j} := by
  choose u m hgood using fun j => exists_arcGood hs hz₀e hφlo hφhi hsum hmono hφinj hr j
  refine ⟨u, m, hgood, ?_⟩
  rintro w ⟨z, hz, rfl⟩
  obtain ⟨t, ht0, ht1, hte⟩ := exists_eAngle_eq_of_mem_circle hz
  obtain ⟨j, t', ht'e, ht'1, ht'2⟩ := exists_arc_of_mem_Icc_lift hs hmono hφlo hφhi ht0 ht1
  have hF : modelF z₀ r z = modelF z₀ r (eAngle t') := by rw [← hte, ht'e]
  rcases eq_or_lt_of_le ht'1 with heq | hlt
  · -- left endpoint: value 0
    refine Set.mem_iUnion.mpr ⟨j, 0, le_refl 0, (hgood j).2.1, ?_⟩
    rw [hF, ← heq, Complex.ofReal_zero, zero_mul]
    exact Submission.ModelStarBoundary6.modelF_junction_value_zero z₀ r φ hz₀e (hr j)
  · rcases lt_or_eq_of_le ht'2 with hlt2 | heq2
    · -- interior
      refine Set.mem_iUnion.mpr ⟨j, rho φ r t', rho_nonneg φ r t', ?_, ?_⟩
      · exact (hgood j).2.2.2.1 t' ⟨le_of_lt hlt, le_of_lt hlt2⟩
      · rw [hF]
        exact (hgood j).2.2.1 t' ⟨hlt, hlt2⟩
    · -- right endpoint: value 0
      refine Set.mem_iUnion.mpr ⟨j, 0, le_refl 0, (hgood j).2.1, ?_⟩
      rw [hF, heq2, Complex.ofReal_zero, zero_mul]
      exact modelF_eAngle_nextJunction_eq_zero hs hz₀e hr j

/-- **Radial monotonicity.**  If `c ≥ 1` and `c·a` lies in the model star
then so does `a`. -/
theorem mem_of_smul_mem {z₀ : Fin s → ℂ} {r φ : Fin s → ℝ} (hs : 0 < s)
    (hz₀e : ∀ k : Fin s, z₀ k = eAngle (φ k))
    (hφlo : ∀ k : Fin s, 0 ≤ φ k) (hφhi : ∀ k : Fin s, φ k < 2 * Real.pi)
    (hsum : (∑ k : Fin s, r k) = 1) (hmono : Monotone φ)
    (hφinj : Function.Injective φ) (hr : ∀ k : Fin s, 0 < r k)
    {a : ℂ} {c : ℝ} (hc : 1 ≤ c) (h : (c : ℂ) * a ∈ modelStarImage z₀ r) :
    a ∈ modelStarImage z₀ r := by
  obtain ⟨u, m, hgood, hsub⟩ := modelStarImage_subset_segments hs hz₀e hφlo hφhi hsum hmono
    hφinj hr
  obtain ⟨j, d, hd0, hdm, hdeq⟩ := Set.mem_iUnion.mp (hsub h)
  have hcpos : (0 : ℝ) < c := lt_of_lt_of_le zero_lt_one hc
  have hc0 : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hcpos.ne'
  have ha : a = ((d / c : ℝ) : ℂ) * u j := by
    have h1 : a = (c : ℂ)⁻¹ * ((d : ℂ) * u j) := by
      rw [← hdeq, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul]
    rw [h1, ← mul_assoc, ← Complex.ofReal_inv, ← Complex.ofReal_mul, inv_mul_eq_div]
  have hle : d / c ≤ m j := by
    have hdc : d / c ≤ d := by
      rw [div_le_iff₀ (lt_of_lt_of_le zero_lt_one hc)]
      nlinarith
    linarith
  rw [ha]
  exact (hgood j).2.2.2.2 (d / c) ⟨div_nonneg hd0 (by linarith), hle⟩

/-- **The model star is Lebesgue-null** (it is a finite union of segments). -/
theorem volume_modelStarImage {z₀ : Fin s → ℂ} {r φ : Fin s → ℝ} (hs : 0 < s)
    (hz₀e : ∀ k : Fin s, z₀ k = eAngle (φ k))
    (hφlo : ∀ k : Fin s, 0 ≤ φ k) (hφhi : ∀ k : Fin s, φ k < 2 * Real.pi)
    (hsum : (∑ k : Fin s, r k) = 1) (hmono : Monotone φ)
    (hφinj : Function.Injective φ) (hr : ∀ k : Fin s, 0 < r k) :
    volume (modelStarImage z₀ r) = 0 := by
  obtain ⟨u, m, hgood, hsub⟩ := modelStarImage_subset_segments hs hz₀e hφlo hφhi hsum hmono
    hφinj hr
  refine MeasureTheory.measure_mono_null hsub ?_
  rw [MeasureTheory.measure_iUnion_null_iff]
  intro j
  have hu : u j ≠ 0 := by
    intro h0
    have := (hgood j).1
    rw [h0, norm_zero] at this
    exact one_ne_zero this.symm
  refine MeasureTheory.measure_mono_null ?_ (MeasureTheory.Measure.addHaar_submodule (volume : Measure ℂ)
    (Submodule.span ℝ ({u j} : Set ℂ)) ?_)
  · rintro w ⟨c, hc0, hcm, rfl⟩
    rw [← Complex.real_smul]
    exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self (u j))
  · intro htop
    have hI : (Complex.I * u j) ∈ Submodule.span ℝ ({u j} : Set ℂ) := by
      rw [htop]; trivial
    rw [Submodule.mem_span_singleton] at hI
    obtain ⟨c, hc⟩ := hI
    have hcu : (c : ℂ) = Complex.I := by
      have := congrArg (fun z : ℂ => z * (u j)⁻¹) hc
      rw [Complex.real_smul] at this
      simpa [mul_assoc, hu] using this
    have := congrArg Complex.im hcu
    simp at this

/-- **The model star has empty interior.** -/
theorem interior_modelStarImage_eq_empty {z₀ : Fin s → ℂ} {r φ : Fin s → ℝ} (hs : 0 < s)
    (hz₀e : ∀ k : Fin s, z₀ k = eAngle (φ k))
    (hφlo : ∀ k : Fin s, 0 ≤ φ k) (hφhi : ∀ k : Fin s, φ k < 2 * Real.pi)
    (hsum : (∑ k : Fin s, r k) = 1) (hmono : Monotone φ)
    (hφinj : Function.Injective φ) (hr : ∀ k : Fin s, 0 < r k) :
    interior (modelStarImage z₀ r) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  rw [mem_interior_iff_mem_nhds] at hx
  obtain ⟨eps, heps0, hepssub⟩ := Metric.mem_nhds_iff.mp hx
  have hpos : 0 < volume (Metric.ball x eps) :=
    Metric.measure_ball_pos (volume : Measure ℂ) x heps0
  have hle : volume (Metric.ball x eps) ≤ volume (modelStarImage z₀ r) :=
    MeasureTheory.measure_mono hepssub
  rw [volume_modelStarImage (z₀ := z₀) (r := r) (φ := φ) hs hz₀e hφlo hφhi hsum hmono
    hφinj hr] at hle
  exact absurd hle (not_le.mpr hpos)

end Submission.ModelStarImageSeg
