import Mathlib
import Submission.FeketeLim
import Submission.FeketeDecayOfLimsup
import Submission.Step3Scaling
import Submission.XTransfer
import Submission.Step3Defs

/-!
# Step3Bridge -- the L-scaling reduction for `Step3.sym_maximality`

`sym_maximality` (Dubinin's hedgehog inequality, `Submission.Step3`) is
homogeneous of degree 1 in the spike length `L`:

    limsup_n (feketeNumber (dirStar u L) (n+1))^(2/((n+1)·n))  =  L · [same with L := 1]

for every real `L ≥ 0` (`Step3Scaling.feketeRoot_scaling`, since
`dirStar u L = homot L (dirStar u 1)` and the root exponent is the exact
pair-count reciprocal).  Consequently the whole statement reduces to its
unit-length instance: this module proves

    `sym_maximality_of_unit`:  the L = 1 case of `Step3.sym_maximality`
    (stated as the hypothesis `h1`, since the L = 1 case is exactly the deep
    Dubinin content) implies the full statement for every `0 ≤ L`.

Also proved here, for the eventual proof's use: pointwise nonnegativity and
uniform bounds of the root sequence (`rootSeq_nonneg`, `rootSeq_bounded`),
the pointwise scaling identity (`rootSeq_scaling`), boundedness and
nonemptiness of the `dirStar` sets, and the homothety identity
(`dirStar_eq_homot`).

Unimported research-isolate module (imports `Submission.Step3`, which still
carries the single deep `sorry` of the whole tree; do not import this module
into the proof chain until `Step3.sym_maximality` is proved).
-/

noncomputable section

open scoped Real Topology BigOperators
open Set Filter Metric

namespace Submission.Step3Bridge

open Submission.Step3
open Submission.Step3Scaling
open Submission.XTransfer

/-- Real scalar action on `ℂ` is complex multiplication by the cast. -/
private lemma smul_complex (t : ℝ) (z : ℂ) : t • z = (t : ℂ) * z := by rfl

/-- `(L : ℂ) · (t • ((1 : ℂ) · w)) = t • ((L : ℂ) · w)`: scaling commutes
with the segment parametrisation (unit directions are `(1 : ℂ) * w`). -/
private lemma mul_smul_one_mul (L : ℝ) (w : ℂ) (t : ℝ) :
    (L : ℂ) * (t • ((1 : ℂ) * w)) = t • ((L : ℂ) * w) := by
  rw [smul_complex, smul_complex]
  ring

/-- The root sequence of `Step3.sym_maximality` (mirrors its definition). -/
def rootSeq (u : Finset ℂ) (L : ℝ) (n : ℕ) : ℝ :=
  (Submission.FeketeLim.feketeNumber (dirStar u L) (n + 1)) ^
    (2 / (((n + 1 : ℝ)) * (n : ℝ)))

/-- `dirStar u L` is the `L`-homothetic image of `dirStar u 1`. -/
lemma dirStar_eq_homot (u : Finset ℂ) (L : ℝ) :
    dirStar u L = (fun z : ℂ => (L : ℂ) * z) '' (dirStar u 1) := by
  unfold dirStar
  ext X
  constructor
  · rintro ⟨w, hw, hseg⟩
    rcases (mem_segment_zero_iff ((L : ℂ) * w) X).1 hseg with ⟨t, ht, hXt⟩
    refine ⟨t • ((1 : ℂ) * w), ?mem, ?eq⟩
    · refine ⟨w, hw, (mem_segment_zero_iff ((1 : ℂ) * w) (t • ((1 : ℂ) * w))).2 ⟨t, ht, rfl⟩⟩
    · change (L : ℂ) * (t • ((1 : ℂ) * w)) = X
      rw [hXt]
      exact mul_smul_one_mul L w t
  · rintro ⟨z, hz, hX⟩
    rcases hz with ⟨w, hw, hseg⟩
    rcases (mem_segment_zero_iff ((1 : ℂ) * w) z).1 hseg with ⟨t, ht, hzt⟩
    refine ⟨w, hw, (mem_segment_zero_iff ((L : ℂ) * w) X).2 ⟨t, ht, ?_⟩⟩
    rw [← hX]
    change (L : ℂ) * z = t • ((L : ℂ) * w)
    rw [hzt]
    exact mul_smul_one_mul L w t

/-- Points of `dirStar u L` have norm at most `max L 1` when the directions
are unit and `L ≥ 0` (for `L ≤ 1` this says: inside the unit ball). -/
lemma dirStar_norm_le (u : Finset ℂ) (hu : ∀ w ∈ u, ‖w‖ = 1) (L : ℝ) (hL : 0 ≤ L)
    {X : ℂ} (hX : X ∈ dirStar u L) : ‖X‖ ≤ max L 1 := by
  rcases hX with ⟨w, hw, hseg⟩
  rcases (mem_segment_zero_iff ((L : ℂ) * w) X).1 hseg with ⟨t, ht, hXt⟩
  rcases ht with ⟨ht0, ht1⟩
  rw [hXt]
  rw [norm_smul]
  have htn : ‖t‖ = t := by rw [Real.norm_eq_abs, abs_of_nonneg ht0]
  have hLn : ‖(L : ℂ)‖ = L := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg hL
  have hwn : ‖w‖ = 1 := hu w hw
  calc
    ‖t‖ * ‖((L : ℂ) * w)‖ = t * (L * 1) := by
      rw [htn, norm_mul, hLn, hwn]
    _ = t * L := by ring
    _ ≤ L := by
      calc t * L ≤ 1 * L := mul_le_mul_of_nonneg_right ht1 hL
        _ = L := by ring
    _ ≤ max L 1 := le_max_left L 1

/-- `dirStar u L` is nonempty when `u` is nonempty (it contains `0`). -/
lemma dirStar_nonempty {u : Finset ℂ} (hu : u.Nonempty) (L : ℝ) :
    (dirStar u L).Nonempty := by
  rcases hu with ⟨w, hw⟩
  refine ⟨0, w, hw, ?_⟩
  exact (mem_segment_zero_iff ((L : ℂ) * w) 0).2 ⟨0, ⟨le_rfl, by norm_num⟩, by simp⟩

/-- `dirStar u L` is bounded for `0 ≤ L` (directions unit). -/
lemma dirStar_isBounded (u : Finset ℂ) (hu : ∀ w ∈ u, ‖w‖ = 1) (L : ℝ) (hL : 0 ≤ L) :
    Bornology.IsBounded (dirStar u L) := by
  refine (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).2 ⟨max L 1, ?_⟩
  intro X hX
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
  exact dirStar_norm_le u hu L hL hX

/-- The root sequence is pointwise nonnegative. -/
lemma rootSeq_nonneg (u : Finset ℂ) (L : ℝ) (n : ℕ) : 0 ≤ rootSeq u L n := by
  unfold rootSeq
  exact Real.rpow_nonneg (Submission.FeketeDecayOfLimsup.feketeNumber_nonneg_all (dirStar u L) (n + 1)) _

/-- The root sequence of the unit-length star is uniformly bounded by
`(max 1 2)^4 = 16`. -/
lemma rootSeq_bounded (u : Finset ℂ) (hu : ∀ w ∈ u, ‖w‖ = 1) (hs : 1 ≤ u.card)
    (n : ℕ) : rootSeq u 1 n ≤ (max 1 2) ^ 4 := by
  have hne : (dirStar u 1).Nonempty := dirStar_nonempty (Finset.card_pos.mp hs) 1
  have hb : Bornology.IsBounded (dirStar u 1) := dirStar_isBounded u hu 1 (by norm_num)
  have hsub : ∀ z ∈ dirStar u 1, ‖z‖ ≤ 1 := by
    intro z hz
    have hnz := dirStar_norm_le u hu 1 (by norm_num) hz
    simpa using hnz
  unfold rootSeq
  have hbdd := Submission.FeketeLim.feketeRoot_bounded (K := dirStar u 1) hne hb (R := 1)
    (by norm_num) hsub n
  have hsim : (max 1 (2 * (1 : ℝ))) ^ 4 = (max 1 2) ^ 4 := by norm_num
  rwa [← hsim]

/-- Pointwise scaling identity of the root sequence (n ≥ 1; the n = 0 term
of `rootSeq` is the degenerate pair-count zero). -/
lemma rootSeq_scaling (u : Finset ℂ) (hu : ∀ w ∈ u, ‖w‖ = 1) (hs : 1 ≤ u.card)
    {L : ℝ} (hL : 0 ≤ L) {n : ℕ} (hn : 1 ≤ n) :
    rootSeq u L n = (L : ℝ) * rootSeq u 1 n := by
  have hne : (dirStar u 1).Nonempty := dirStar_nonempty (Finset.card_pos.mp hs) 1
  have hb : Bornology.IsBounded (dirStar u 1) := dirStar_isBounded u hu 1 (by norm_num)
  have hnorm : ‖(L : ℂ)‖ = L := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg hL
  have hEq := Submission.Step3Scaling.feketeRoot_scaling (K := dirStar u 1) hne hb
    (a := (L : ℂ)) (n := n) hn
  have hEq2 : (Submission.FeketeLim.feketeNumber ((fun z : ℂ => (L : ℂ) * z) '' (dirStar u 1))
        (n + 1)) ^ (2 / (((n + 1 : ℝ)) * (n : ℝ)))
        = ‖(L : ℂ)‖ * (Submission.FeketeLim.feketeNumber (dirStar u 1) (n + 1)) ^
            (2 / (((n + 1 : ℝ)) * (n : ℝ))) := by
    simpa [Submission.Step3Scaling.homot] using hEq
  have hEq' : (Submission.FeketeLim.feketeNumber ((fun z : ℂ => (L : ℂ) * z) '' (dirStar u 1))
        (n + 1)) ^ (2 / (((n + 1 : ℝ)) * (n : ℝ)))
        = (L : ℝ) * (Submission.FeketeLim.feketeNumber (dirStar u 1) (n + 1)) ^
            (2 / (((n + 1 : ℝ)) * (n : ℝ))) := by
    rw [hnorm] at hEq2
    exact hEq2
  unfold rootSeq
  rw [dirStar_eq_homot u L]
  exact hEq'

/-- **L-scaling bridge.**  The L = 1 instance of `Step3.sym_maximality`
(assumed as `h1`) implies the full statement for every `0 ≤ L`. -/
theorem sym_maximality_of_unit (u : Finset ℂ) (hu : ∀ w ∈ u, ‖w‖ = 1)
    (hs : 1 ≤ u.card) {L : ℝ} (hL : 0 ≤ L)
    (h1 : Filter.limsup (rootSeq u 1) Filter.atTop ≤
        (4 : ℝ) ^ (-1 / (u.card : ℝ))) :
    Filter.limsup (rootSeq u L) Filter.atTop ≤
      (L : ℝ) * (4 : ℝ) ^ (-1 / (u.card : ℝ)) := by
  classical
  let B : ℝ := (4 : ℝ) ^ (-1 / (u.card : ℝ))
  by_cases hL0 : L = 0
  · -- degenerate case: every spike has length 0, so the root terms are 0
    -- from index 1 on
    subst L
    have hu0 : u.Nonempty := Finset.card_pos.mp hs
    have hseg0 : dirStar u 0 = ({0} : Set ℂ) := by
      ext X
      constructor
      · intro hX
        rcases hX with ⟨w, hw, hseg⟩
        rcases (mem_segment_zero_iff ((0 : ℂ) * w) X).1 hseg with ⟨t, ht, hXt⟩
        rw [hXt]
        simp
      · intro hX
        have hX0 : X = 0 := hX
        rcases hu0 with ⟨w, hw⟩
        refine ⟨w, hw, ?_⟩
        rw [hX0]
        exact (mem_segment_zero_iff ((0 : ℂ) * w) 0).2 ⟨0, ⟨le_rfl, by norm_num⟩, by simp⟩
    have hfe : ∀ n : ℕ, 1 ≤ n → Submission.FeketeLim.feketeNumber (dirStar u 0) (n + 1) = 0 := by
      intro n hn
      have hfe0 : Submission.FeketeLim.feketeNumber ({0} : Set ℂ) (n + 1) = 0 := by
        have hf : ({0} : Set ℂ).Finite := by simp
        have hne0 : ({0} : Set ℂ).Nonempty := by simp
        have hcard : (hf.toFinset).card < n + 1 := by
          simp
          omega
        exact Submission.FeketeLim.feketeNumber_eq_zero_of_finite hne0 hf hcard
      rw [hseg0]
      exact hfe0
    have hz : ∀ n : ℕ, 1 ≤ n → rootSeq u 0 n = 0 := by
      intro n hn
      unfold rootSeq
      rw [hfe n hn]
      have he0 : 2 / (((n + 1 : ℝ)) * (n : ℝ)) ≠ 0 := by
        have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
        have hnn : (((n + 1 : ℝ)) * (n : ℝ)) ≠ 0 := by positivity
        exact div_ne_zero (by norm_num) hnn
      exact Real.zero_rpow he0
    have hev : ∀ᶠ n : ℕ in Filter.atTop, rootSeq u 0 n = 0 := by
      exact (Filter.eventually_ge_atTop 1).mono (fun n hn => hz n hn)
    have hlim : Filter.limsup (rootSeq u 0) Filter.atTop = 0 := by
      calc
        Filter.limsup (rootSeq u 0) Filter.atTop
            = Filter.limsup (fun _ : ℕ => (0 : ℝ)) Filter.atTop := Filter.limsup_congr hev
        _ = 0 := Filter.limsup_const (0 : ℝ)
    rw [hlim]
    simp
  · have hLpos : 0 < L := lt_of_le_of_ne hL (Ne.symm hL0)
    -- the unit-star root sequence is bounded (for the limsup manipulation)
    have hbdd1 : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop (rootSeq u 1) := by
      exact Submission.FeketeDecayOfLimsup.isBoundedUnder_atTop_of_le
        ⟨(max 1 2) ^ 4, rootSeq_bounded u hu hs⟩
    have hcobL : Filter.IsCoboundedUnder (· ≤ ·) Filter.atTop (rootSeq u L) := by
      unfold Filter.IsCoboundedUnder Filter.IsCobounded
      refine ⟨0, ?_⟩
      intro a ha
      rw [Filter.eventually_map] at ha
      rcases (Filter.eventually_atTop).1 ha with ⟨N, hN⟩
      have huN : 0 ≤ rootSeq u L N := rootSeq_nonneg u L N
      have huNa : rootSeq u L N ≤ a := hN N le_rfl
      linarith
    -- ε-argument: for every η > 0 the limsup is ≤ L·B + η
    apply le_of_forall_pos_le_add
    intro η hη
    let ε : ℝ := η / L
    have hε : 0 < ε := div_pos hη hLpos
    have hεL : (L : ℝ) * ε = η := by
      dsimp [ε]
      field_simp [ne_of_gt hLpos]
    have hρgt : B < B + ε := by linarith
    -- eventually rootSeq u 1 n < B + ε
    have hEv1 : ∀ᶠ n : ℕ in Filter.atTop, rootSeq u 1 n < B + ε := by
      have hlt : Filter.limsup (rootSeq u 1) Filter.atTop < B + ε := by
        exact lt_of_le_of_lt h1 hρgt
      exact Filter.eventually_lt_of_limsup_lt hlt hbdd1
    have hEvsc : ∀ᶠ n : ℕ in Filter.atTop, rootSeq u L n < (L : ℝ) * B + (L : ℝ) * ε := by
      exact (hEv1.and (Filter.eventually_ge_atTop 1)).mono (fun n h => by
        rcases h with ⟨h1n, hn⟩
        have hsc := rootSeq_scaling u hu hs hL hn
        calc
          rootSeq u L n = (L : ℝ) * rootSeq u 1 n := hsc
          _ < (L : ℝ) * (B + ε) := (mul_lt_mul_of_pos_left h1n hLpos)
          _ = (L : ℝ) * B + (L : ℝ) * ε := by ring)
    have hEvle : ∀ᶠ n : ℕ in Filter.atTop, rootSeq u L n ≤ (L : ℝ) * B + (L : ℝ) * ε := by
      exact hEvsc.mono (fun n h => le_of_lt h)
    have hfin : Filter.limsup (rootSeq u L) Filter.atTop ≤ (L : ℝ) * B + (L : ℝ) * ε := by
      exact Filter.limsup_le_of_le hcobL hEvle
    rwa [hεL] at hfin

end Submission.Step3Bridge

end
