import Mathlib
import Submission.Work.Drive.oFatDefs
import Submission.Work.Drive.quadrisecantSpreadDefs
import Submission.Work.Drive.genericFullDefs
import Submission.Work.Drive.tangentChordLocallyFinite

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant
open Filter Topology

set_option maxHeartbeats 1000000

noncomputable section

/-!
## Elementary pieces: the cell index, reduction modulo the period, distances on the circle
-/

/-- The **cell index** of a parameter `u` relative to the slab centre `t₀`: the integer `k` with
`t₀ + k·period ≤ u < t₀ + (k+1)·period`. -/
def cellOf (t₀ u : ℝ) : ℤ := ⌊(u - t₀) / period⌋

lemma cellOf_le (t₀ u : ℝ) : t₀ + (cellOf t₀ u : ℝ) * period ≤ u := by
  have hP : 0 < period := period_pos
  have h : ((cellOf t₀ u : ℤ) : ℝ) ≤ (u - t₀) / period := Int.floor_le _
  have := mul_le_mul_of_nonneg_right h hP.le
  rw [div_mul_cancel₀ _ hP.ne'] at this
  linarith

lemma cellOf_lt (t₀ u : ℝ) : u < t₀ + ((cellOf t₀ u : ℝ) + 1) * period := by
  have hP : 0 < period := period_pos
  have h : (u - t₀) / period < ((cellOf t₀ u : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  have := mul_lt_mul_of_pos_right h hP
  rw [div_mul_cancel₀ _ hP.ne'] at this
  linarith

lemma cellOf_eq_iff {t₀ u : ℝ} {k : ℤ} :
    cellOf t₀ u = k ↔ t₀ + (k : ℝ) * period ≤ u ∧ u < t₀ + ((k : ℝ) + 1) * period := by
  have hP : 0 < period := period_pos
  constructor
  · intro h
    rw [← h]
    exact ⟨cellOf_le t₀ u, cellOf_lt t₀ u⟩
  · intro h
    rw [cellOf, Int.floor_eq_iff]
    constructor
    · rw [le_div_iff₀ hP]; linarith [h.1]
    · rw [div_lt_iff₀ hP]; linarith [h.2]

/-- The slab condition, in the form used below: if `η` is a lower bound for the distance of `u` to
*every* slab centre and `u` lies in the cell `k`, then `u` is at distance `> η` from both endpoints
of the cell. -/
lemma cellOf_core {u t₀ η : ℝ} (hη : 0 < η) {k : ℤ} (hk : cellOf t₀ u = k)
    (hslab : η < |u - (t₀ + (k : ℝ) * period)|)
    (hslab' : η < |u - (t₀ + ((k : ℝ) + 1) * period)|) :
    t₀ + (k : ℝ) * period + η < u ∧ u < t₀ + ((k : ℝ) + 1) * period - η := by
  have h1 := cellOf_le t₀ u
  have h2 := cellOf_lt t₀ u
  rw [hk] at h1 h2
  have h3 : |u - (t₀ + (k : ℝ) * period)| = u - (t₀ + (k : ℝ) * period) :=
    abs_of_nonneg (by linarith)
  have h4 : |u - (t₀ + ((k : ℝ) + 1) * period)| =
      (t₀ + ((k : ℝ) + 1) * period) - u := by
    rw [abs_of_nonpos (show u - (t₀ + ((k : ℝ) + 1) * period) ≤ 0 by linarith), neg_sub]
  rw [h3] at hslab
  rw [h4] at hslab'
  constructor <;> linarith

/-- Reduction of a real parameter modulo the period, into `[0, period)`. -/
def pmod (t : ℝ) : ℝ := t - (⌊t / period⌋ : ℝ) * period

lemma pmod_nonneg (t : ℝ) : 0 ≤ pmod t := by
  have hP : 0 < period := period_pos
  have h : ((⌊t / period⌋ : ℤ) : ℝ) ≤ t / period := Int.floor_le _
  have h2 : ((⌊t / period⌋ : ℤ) : ℝ) * period ≤ t := by
    have := mul_le_mul_of_nonneg_right h hP.le
    rwa [div_mul_cancel₀ _ hP.ne'] at this
  rw [pmod]; linarith

lemma pmod_lt (t : ℝ) : pmod t < period := by
  have hP : 0 < period := period_pos
  have h : t / period < ((⌊t / period⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  have h2 : t < (((⌊t / period⌋ : ℤ) : ℝ) + 1) * period := by
    have := mul_lt_mul_of_pos_right h hP
    rwa [div_mul_cancel₀ _ hP.ne'] at this
  rw [pmod]; nlinarith

lemma pmod_mem (t : ℝ) : pmod t ∈ Set.Ico (0 : ℝ) period := ⟨pmod_nonneg t, pmod_lt t⟩

lemma coe_int_mul_period (n : ℤ) : (((n : ℝ) * period : ℝ) : AddCircle period) = 0 := by
  have h : (n : ℝ) * period = n • period := by simp [zsmul_eq_mul]
  rw [h, AddCircle.coe_zsmul, AddCircle.coe_period, smul_zero]

lemma pmod_coe (t : ℝ) : ((pmod t : ℝ) : AddCircle period) = (t : AddCircle period) := by
  rw [pmod, sub_eq_add_neg, AddCircle.coe_add, AddCircle.coe_neg, coe_int_mul_period, neg_zero,
    add_zero]

lemma circSep_comm (x y : ℝ) : circSep x y = circSep y x := dist_comm _ _

lemma circSep_pmod (x y : ℝ) : circSep (pmod x) (pmod y) = circSep x y := by
  rw [circSep, circSep, pmod_coe, pmod_coe]

lemma circSep_pmod_left (x y : ℝ) : circSep (pmod x) y = circSep x y := by
  rw [circSep, circSep, pmod_coe]

lemma circSep_pmod_right (x y : ℝ) : circSep x (pmod y) = circSep x y := by
  rw [circSep, circSep, pmod_coe]

/-- Two reals have the same class in `AddCircle period` iff they differ by an integer multiple of
the period. -/
lemma coe_eq_coe_iff_exists_int (x y : ℝ) :
    ((x : ℝ) : AddCircle period) = ((y : ℝ) : AddCircle period) ↔
      ∃ n : ℤ, x = y + n * period := by
  constructor
  · intro h
    have h0 : ((x - y : ℝ) : AddCircle period) = 0 := by
      rw [AddCircle.coe_sub, h, sub_self]
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff period).mp h0
    refine ⟨n, ?_⟩
    have hn' : (n : ℝ) * period = x - y := by rw [← hn]; simp [zsmul_eq_mul]
    linarith
  · rintro ⟨n, rfl⟩
    rw [AddCircle.coe_add, coe_int_mul_period n, add_zero]

/-- **The key distance estimate on the parameter circle.**  If `0 < e < period` and `lo` is a lower
bound for both the direct distance `e` and the complementary distance `period - e`, then `‖(e)‖` on
the circle is at least `lo`. -/
lemma le_norm_coe_of_le_of_le {e lo : ℝ} (hlo : 0 ≤ lo) (he0 : 0 < e) (heP : e < period)
    (h1 : lo ≤ e) (h2 : lo ≤ period - e) : lo ≤ ‖(e : AddCircle period)‖ := by
  have hP : 0 < period := period_pos
  rcases le_or_gt e (period / 2) with hle | hgt
  · have habs : |e| ≤ |period| / 2 := by
      rw [abs_of_pos he0, abs_of_pos hP]; linarith
    have := (AddCircle.norm_coe_eq_abs_iff period hP.ne').mpr habs
    rw [this, abs_of_pos he0]; exact h1
  · have hcoe : (e : AddCircle period) = ((e - period : ℝ) : AddCircle period) := by
      rw [AddCircle.coe_sub, AddCircle.coe_period, sub_zero]
    have hlt : e - period < 0 := by linarith
    have habs : |e - period| ≤ |period| / 2 := by
      rw [abs_of_neg hlt, abs_of_pos hP]; linarith
    have := (AddCircle.norm_coe_eq_abs_iff period hP.ne').mpr habs
    rw [hcoe, this, abs_of_neg hlt]
    linarith

lemma circSep_eq_norm_sub (x y : ℝ) : circSep x y = ‖((x - y : ℝ) : AddCircle period)‖ := by
  rw [circSep, dist_eq_norm, ← AddCircle.coe_sub]

/-- **A lower bound for the circular separation.**  If `ρ ≤ u - x ≤ period - ρ` (and `ρ > 0`),
then the classes of `u` and `x` are at distance at least `ρ` on the parameter circle. -/
lemma circSep_ge_of_sub_mem {x u ρ : ℝ} (hρ : 0 < ρ)
    (h1 : ρ ≤ u - x) (h2 : u - x ≤ period - ρ) : ρ ≤ circSep u x := by
  have he0 : 0 < u - x := lt_of_lt_of_le hρ h1
  have heP : u - x < period := by linarith
  have h2' : ρ ≤ period - (u - x) := by linarith
  have h := le_norm_coe_of_le_of_le (e := u - x) (lo := ρ) hρ.le he0 heP h1 h2'
  rw [circSep_eq_norm_sub]
  exact h

/-- **A point of a segment that is not an endpoint lies in the *open* segment.** -/
lemma segment_mem_openSegment_of_ne {x y z : Space} (hz : z ∈ segment ℝ x y) (hx : z ≠ x)
    (hy : z ≠ y) : z ∈ openSegment ℝ x y := by
  rw [segment_eq_image_lineMap] at hz
  obtain ⟨t, ht, hzt⟩ := hz
  have ht0 : t ≠ 0 := by
    intro h
    exact hx (by rw [← hzt, h, AffineMap.lineMap_apply_zero])
  have ht1 : t ≠ 1 := by
    intro h
    exact hy (by rw [← hzt, h, AffineMap.lineMap_apply_one])
  rw [openSegment_eq_image_lineMap]
  exact ⟨t, ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩, hzt⟩

/-- **Distances add along a segment**: if `z` lies in the open segment from `x` to `y`, the two
sub-distances sum to the total distance. -/
lemma norm_add_norm_sub_eq_of_mem_openSegment {x y z : Space}
    (hz : z ∈ openSegment ℝ x y) : ‖x - z‖ + ‖z - y‖ = ‖x - y‖ := by
  rw [openSegment_eq_image_lineMap] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  rw [AffineMap.lineMap_apply_module]
  have h1 : x - ((1 - t) • x + t • y) = t • (x - y) := by module
  have h2 : (1 - t) • x + t • y - y = (1 - t) • (x - y) := by module
  rw [h1, h2, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg ht.1.le, abs_of_nonneg (by linarith [ht.2] : (0:ℝ) ≤ 1 - t)]
  ring

/-- The circle-level and the real form of "middle on chord" agree (for a smooth knot). -/
lemma isMiddleOnChord_iff_real {r : ℝ → Space} (hr : IsSmoothKnot r) (A B M : ℝ) :
    IsMiddleOnChord r (A : KnotParam) (B : KnotParam) (M : KnotParam) ↔
      r M ∈ openSegment ℝ (r A) (r B) := by
  dsimp [IsMiddleOnChord]
  rw [knotMap_eq_r hr A, knotMap_eq_r hr B, knotMap_eq_r hr M]


/-!
## 1. Limits of middles
-/

/-- An integer multiple of the period whose absolute value is `< period` is zero. -/
lemma int_eq_zero_of_abs_mul_period_lt {n : ℤ} (h : |(n : ℝ) * period| < period) : n = 0 := by
  have hP : 0 < period := period_pos
  have h1 : |(n : ℝ)| * period < period := by
    rwa [abs_mul, abs_of_pos hP] at h
  have h2 : |(n : ℝ)| < 1 := by nlinarith
  have h3 : |n| < (1 : ℤ) := by
    rw [← Int.cast_lt (R := ℝ), Int.cast_abs, Int.cast_one]
    exact h2
  have h4 := abs_lt.mp h3
  omega

/-- The class of a convergent sequence of reals converges in `AddCircle period`. -/
lemma tendsto_coe_period {f : ℕ → ℝ} {x : ℝ} (h : Tendsto f atTop (𝓝 x)) :
    Tendsto (fun n => ((f n : ℝ) : AddCircle period)) atTop (𝓝 ((x : ℝ) : AddCircle period)) :=
  ((AddCircle.continuous_mk' period).tendsto x).comp h

/-- **Limit of a sequence of middles.**  Let `qₙ → q` with `0 < q.2 < period`, and let `uₙ` be
parameters with `qₙ.1 + ρ ≤ uₙ ≤ qₙ.1 + qₙ.2 - ρ` whose images lie in the *open* segment of the
chord of `qₙ`.  Then some subsequence of `uₙ` converges, and the limit `v` is a middle parameter of
the chord of `q`, again at distance at least `ρ` from both endpoints of that chord. -/
theorem exists_middle_limit {r : ℝ → Space} (hr : IsSmoothKnot r) {ρ : ℝ} (hρ : 0 < ρ)
    {q : ℝ × ℝ} (hq0 : 0 < q.2) (hq1 : q.2 < period)
    {qs : ℕ → ℝ × ℝ} (hqs : Tendsto qs atTop (𝓝 q))
    {u : ℕ → ℝ} (hu1 : ∀ n, (qs n).1 + ρ ≤ u n) (hu2 : ∀ n, u n ≤ (qs n).1 + (qs n).2 - ρ)
    (hu3 : ∀ n, r (u n) ∈ openSegment ℝ (r (qs n).1) (r ((qs n).1 + (qs n).2))) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v : ℝ, Tendsto (fun n => u (φ n)) atTop (𝓝 v) ∧
      q.1 + ρ ≤ v ∧ v ≤ q.1 + q.2 - ρ ∧ r v ∈ openSegment ℝ (r q.1) (r (q.1 + q.2)) := by
  have hP : 0 < period := period_pos
  have hqs1 : Tendsto (fun n => (qs n).1) atTop (𝓝 q.1) :=
    (continuous_fst.tendsto q).comp hqs
  have hqs2 : Tendsto (fun n => (qs n).2) atTop (𝓝 q.2) :=
    (continuous_snd.tendsto q).comp hqs
  -- eventual box bounds on `qₙ`
  have hev1 : ∀ᶠ n in atTop, |(qs n).1 - q.1| < 1 := by
    have h := Metric.tendsto_nhds.mp hqs1 (1 : ℝ) one_pos
    simpa [Real.dist_eq] using h
  have hev2 : ∀ᶠ n in atTop, |(qs n).2 - q.2| < 1 := by
    have h := Metric.tendsto_nhds.mp hqs2 (1 : ℝ) one_pos
    simpa [Real.dist_eq] using h
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hev1.and hev2)
  -- shift the sequence so that the box bounds hold everywhere
  set qs' : ℕ → ℝ × ℝ := fun k => qs (k + N) with hqs'def
  set u' : ℕ → ℝ := fun k => u (k + N) with hu'def
  have hshift : Tendsto (fun k : ℕ => k + N) atTop atTop := Filter.tendsto_add_atTop_nat N
  have hqs' : Tendsto qs' atTop (𝓝 q) := hqs.comp hshift
  have hu'1 : ∀ k, (qs' k).1 + ρ ≤ u' k := fun k => hu1 (k + N)
  have hu'2 : ∀ k, u' k ≤ (qs' k).1 + (qs' k).2 - ρ := fun k => hu2 (k + N)
  have hu'3 : ∀ k, r (u' k) ∈ openSegment ℝ (r (qs' k).1) (r ((qs' k).1 + (qs' k).2)) :=
    fun k => hu3 (k + N)
  -- the shifted middles lie in a compact interval
  have hmem : ∀ k : ℕ, u' k ∈ Set.Icc (q.1 - 1 + ρ) (q.1 + q.2 + 2 - ρ) := by
    intro k
    obtain ⟨h1, h2⟩ := hN (k + N) (by omega)
    obtain ⟨h1l, h1u⟩ := abs_lt.mp h1
    obtain ⟨h2l, h2u⟩ := abs_lt.mp h2
    have h1'' := hu1 (k + N)
    have h2'' := hu2 (k + N)
    simp only [hu'def, hqs'def]
    exact ⟨by linarith, by linarith⟩
  obtain ⟨v, -, ψ, hψ, hψt⟩ :=
    isCompact_Icc.tendsto_subseq (s := Set.Icc (q.1 - 1 + ρ) (q.1 + q.2 + 2 - ρ))
      (x := u') hmem
  have hφ : StrictMono fun k => ψ k + N := fun a b hab => Nat.add_lt_add_right (hψ hab) N
  have hψ1 : Tendsto (fun k => (qs' (ψ k)).1) atTop (𝓝 q.1) :=
    ((continuous_fst.tendsto q).comp hqs').comp hψ.tendsto_atTop
  have hψ2 : Tendsto (fun k => (qs' (ψ k)).2) atTop (𝓝 q.2) :=
    ((continuous_snd.tendsto q).comp hqs').comp hψ.tendsto_atTop
  -- bounds on the limit
  have hv_lo : q.1 + ρ ≤ v :=
    le_of_tendsto_of_tendsto' (hψ1.add tendsto_const_nhds) hψt (fun k => hu'1 (ψ k))
  have hv_hi : v ≤ q.1 + q.2 - ρ :=
    le_of_tendsto_of_tendsto' hψt ((hψ1.add hψ2).sub tendsto_const_nhds)
      (fun k => hu'2 (ψ k))
  -- the limit is a closed middle of the limit chord
  have t1 := tendsto_coe_period hψ1
  have t2 := tendsto_coe_period (hψ1.add hψ2)
  have t3 := tendsto_coe_period hψt
  have htriple := t1.prodMk_nhds (t2.prodMk_nhds t3)
  have hev : ∀ᶠ k in atTop,
      ((((qs' (ψ k)).1 : ℝ) : KnotParam),
        (((((qs' (ψ k)).1 + (qs' (ψ k)).2 : ℝ) : KnotParam), (((u' (ψ k)) : ℝ) : KnotParam))))
        ∈ closedMiddleData r := by
    refine Eventually.of_forall (fun k => ?_)
    refine openMiddleData_subset_closedMiddleData r ?_
    simp only [openMiddleData, IsMiddleOnOpenChord, Set.mem_ofPred_eq, knotMap_eq_r hr]
    exact hu'3 (ψ k)
  have hcl : IsMiddleOnClosedChord r ((q.1 : ℝ) : KnotParam) (((q.1 + q.2 : ℝ)) : KnotParam)
      ((v : ℝ) : KnotParam) :=
    (mem_closedMiddleData_iff r).mp
      (IsClosed.mem_of_tendsto (isClosed_closedMiddleData hr) htriple hev)
  have hseg : r v ∈ segment ℝ (r q.1) (r (q.1 + q.2)) := by
    have := hcl
    simp only [IsMiddleOnClosedChord, knotMap_eq_r hr] at this
    exact this
  -- the limit is not an endpoint of the chord
  have hvne1 : r v ≠ r q.1 := by
    intro h
    have hclass : ((v : ℝ) : KnotParam) = ((q.1 : ℝ) : KnotParam) :=
      knotMap_injective hr (by rw [knotMap_eq_r hr v, knotMap_eq_r hr q.1]; exact h)
    obtain ⟨n, hn⟩ := (coe_eq_coe_iff_exists_int v q.1).mp hclass
    have h1 : 0 < (n : ℝ) * period := by linarith
    have h2 : (n : ℝ) * period < period := by linarith
    have hn0 : n = 0 :=
      int_eq_zero_of_abs_mul_period_lt (by rw [abs_of_pos h1]; exact h2)
    rw [hn0, Int.cast_zero, zero_mul, add_zero] at hn
    linarith
  have hvne2 : r v ≠ r (q.1 + q.2) := by
    intro h
    have hclass : ((v : ℝ) : KnotParam) = ((q.1 + q.2 : ℝ) : KnotParam) :=
      knotMap_injective hr (by rw [knotMap_eq_r hr v, knotMap_eq_r hr (q.1 + q.2)]; exact h)
    obtain ⟨n, hn⟩ := (coe_eq_coe_iff_exists_int v (q.1 + q.2)).mp hclass
    have h1 : -period < (n : ℝ) * period := by linarith
    have h2 : (n : ℝ) * period < 0 := by linarith
    have habs : |(n : ℝ) * period| < period := by
      rw [abs_of_neg h2]
      linarith
    have hn0 : n = 0 := int_eq_zero_of_abs_mul_period_lt habs
    rw [hn0, Int.cast_zero, zero_mul, add_zero] at hn
    linarith
  exact ⟨fun k => ψ k + N, hφ, v, hψt, hv_lo, hv_hi,
    segment_mem_openSegment_of_ne hseg hvne1 hvne2⟩



/-!
## 2. The crux: all middles of a fat chord lie in the same cell
-/

/-- **The chord-length bound.**  If `q ∈ OFatR r ρ` and `u` is a middle of its chord, then each of
the two sub-chords has length at least `s`, so the whole chord has length at least `2s`. -/
lemma two_mul_s_le_norm_sub {r : ℝ → Space} (hr : IsSmoothKnot r) {ρ s : ℝ} (hρ : 0 < ρ)
    (hsep : ∀ a b : KnotParam, ρ ≤ dist a b → s ≤ ‖knotMap r a - knotMap r b‖)
    {q : ℝ × ℝ} (hq : q ∈ OFatR r ρ)
    {u : ℝ} (hu1 : q.1 + ρ ≤ u) (hu2 : u ≤ q.1 + q.2 - ρ)
    (hu3 : r u ∈ openSegment ℝ (r q.1) (r (q.1 + q.2))) :
    2 * s ≤ ‖r q.1 - r (q.1 + q.2)‖ := by
  obtain ⟨hq0, hq1, -⟩ := hq
  have hca : ρ ≤ circSep q.1 u := by
    rw [circSep_comm]
    exact circSep_ge_of_sub_mem hρ (by linarith) (by linarith)
  have hcb' : ρ ≤ dist (u : KnotParam) ((q.1 + q.2 : ℝ) : KnotParam) := by
    rw [dist_comm, ← circSep]
    exact circSep_ge_of_sub_mem hρ (by linarith) (by linarith)
  have h1 : s ≤ ‖r q.1 - r u‖ := by
    have h := hsep (q.1 : KnotParam) (u : KnotParam) hca
    simpa only [knotMap_eq_r hr] using h
  have h2 : s ≤ ‖r u - r (q.1 + q.2)‖ := by
    have h := hsep (u : KnotParam) ((q.1 + q.2 : ℝ) : KnotParam) hcb'
    simpa only [knotMap_eq_r hr] using h
  have hsum := norm_add_norm_sub_eq_of_mem_openSegment hu3
  have hrev : ‖r (q.1 + q.2) - r u‖ = ‖r u - r (q.1 + q.2)‖ := norm_sub_rev _ _
  linarith

/-- Two parameters in strictly increasing cells, each at distance `> η` from the endpoints of its
cell, are at distance `> 2η`. -/
lemma two_eta_lt_sub_of_cell_lt {t₀ η : ℝ} {k k' : ℤ} (h : k < k') {u u' : ℝ}
    (h1 : t₀ + (k' : ℝ) * period + η < u')
    (h2 : u < t₀ + ((k : ℝ) + 1) * period - η) : 2 * η < u' - u := by
  have hP : 0 < period := period_pos
  have h3 : (k : ℝ) + 1 ≤ (k' : ℝ) := by
    have : k + 1 ≤ k' := by omega
    exact_mod_cast this
  have h4 : t₀ + ((k : ℝ) + 1) * period ≤ t₀ + (k' : ℝ) * period := by nlinarith
  linarith

/-- If `|e| < period` and `lo` is a lower bound for both `|e|` and `period - |e|`, then `lo` is a
lower bound for `‖(e)‖` on the parameter circle. -/
lemma le_norm_coe_of_abs_bounds {e lo : ℝ} (hlo : 0 ≤ lo) (he : |e| < period)
    (h1 : lo ≤ |e|) (h2 : lo ≤ period - |e|) : lo ≤ ‖(e : AddCircle period)‖ := by
  rcases lt_trichotomy e 0 with h | h | h
  · have hneg : |e| = -e := abs_of_neg h
    have hnorm : ‖(e : AddCircle period)‖ = ‖((-e : ℝ) : AddCircle period)‖ := by
      rw [AddCircle.coe_neg, norm_neg]
    rw [hnorm]
    refine le_norm_coe_of_le_of_le hlo (by linarith) (by linarith) ?_ ?_
    · rwa [hneg] at h1
    · rwa [hneg] at h2
  · simpa [h] using h1
  · have hpos : |e| = e := abs_of_pos h
    rw [hpos] at h1 h2
    exact le_norm_coe_of_le_of_le hlo h (by linarith) h1 h2

/-- **The cell of a middle is independent of the middle.**  If `q ∈ OFatR r ρ` and `u`, `u'` are
two middle parameters of its chord, then they lie in the same cell.  Otherwise the four parameters
`q.1`, `q.1 + q.2`, `u`, `u'` form a `δ`-spread quadrisecant with `δ = min ρ (min (2η) (2s/V))`,
contradicting `hnq`. -/
theorem cellOf_eq_of_middle {r : ℝ → Space} (hr : IsSmoothKnot r) {ρ : ℝ} (hρ : 0 < ρ)
    {t₀ η : ℝ} (hη : 0 < η)
    (hslab : ∀ u : ℝ, FatMiddle r ρ u → ∀ k : ℤ,
      η < |u - (t₀ + (k : ℝ) * period)|)
    {s V : ℝ} (hs : 0 < s) (hV : 0 < V)
    (hsep : ∀ a b : KnotParam, ρ ≤ dist a b → s ≤ ‖knotMap r a - knotMap r b‖)
    (hlip : ∀ a b : KnotParam, ‖knotMap r a - knotMap r b‖ ≤ V * dist a b)
    (hnq : ∀ a b z w : ℝ, SpreadQuad (min ρ (min (2 * η) (2 * s / V))) a b z w →
      ¬ (IsMiddleOnChord r (a : KnotParam) (b : KnotParam) (z : KnotParam) ∧
         IsMiddleOnChord r (a : KnotParam) (b : KnotParam) (w : KnotParam)))
    {q : ℝ × ℝ} (hq : q ∈ OFatR r ρ)
    {u u' : ℝ} (hu1 : q.1 + ρ ≤ u) (hu2 : u ≤ q.1 + q.2 - ρ)
    (hu3 : r u ∈ openSegment ℝ (r q.1) (r (q.1 + q.2)))
    (hv1 : q.1 + ρ ≤ u') (hv2 : u' ≤ q.1 + q.2 - ρ)
    (hv3 : r u' ∈ openSegment ℝ (r q.1) (r (q.1 + q.2))) :
    cellOf t₀ u = cellOf t₀ u' := by
  have hq0 : 0 < q.2 := hq.1
  have hq1 : q.2 < period := hq.2.1
  have hfm_u : FatMiddle r ρ u := ⟨q.1, q.2, hq0, hq1, hu1, hu2, hu3⟩
  have hfm_v : FatMiddle r ρ u' := ⟨q.1, q.2, hq0, hq1, hv1, hv2, hv3⟩
  -- every fat middle is at distance `> η` from the two endpoints of its cell
  have key : ∀ {v : ℝ}, FatMiddle r ρ v →
      t₀ + (cellOf t₀ v : ℝ) * period + η < v ∧
        v < t₀ + ((cellOf t₀ v : ℝ) + 1) * period - η := by
    intro v hv
    have h2 : η < |v - (t₀ + ((cellOf t₀ v : ℝ) + 1) * period)| := by
      have := hslab v hv (cellOf t₀ v + 1)
      simpa [Int.cast_add, Int.cast_one] using this
    exact cellOf_core hη rfl (hslab v hv (cellOf t₀ v)) h2
  by_contra hne
  have hu_core := key hfm_u
  have hv_core := key hfm_v
  -- the two middles are at distance `> 2η`
  have hsep2 : 2 * η < |u - u'| := by
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have h := two_eta_lt_sub_of_cell_lt (t₀ := t₀) (η := η) hlt hv_core.1 hu_core.2
      rw [abs_sub_comm, abs_of_pos (by linarith : (0:ℝ) < u' - u)]
      exact h
    · have h := two_eta_lt_sub_of_cell_lt (t₀ := t₀) (η := η) hlt hu_core.1 hv_core.2
      rw [abs_of_pos (by linarith : (0:ℝ) < u - u')]
      exact h
  have hd_le : |u - u'| ≤ q.2 - 2 * ρ := by
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  -- the six circular separations
  have hδpos : 0 < min ρ (min (2 * η) (2 * s / V)) :=
    lt_min hρ (lt_min (by linarith) (by positivity))
  have hδle_ρ : min ρ (min (2 * η) (2 * s / V)) ≤ ρ := min_le_left _ _
  have hδle_2η : min ρ (min (2 * η) (2 * s / V)) ≤ 2 * η :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have hδle_2s : min ρ (min (2 * η) (2 * s / V)) ≤ 2 * s / V :=
    le_trans (min_le_right _ _) (min_le_right _ _)
  have hδ_ab : min ρ (min (2 * η) (2 * s / V)) ≤ circSep q.1 (q.1 + q.2) := by
    have hchord := two_mul_s_le_norm_sub hr hρ hsep hq hu1 hu2 hu3
    have hlip' : ‖r q.1 - r (q.1 + q.2)‖ ≤ V * circSep q.1 (q.1 + q.2) := by
      have := hlip (q.1 : KnotParam) ((q.1 + q.2 : ℝ) : KnotParam)
      simpa only [knotMap_eq_r hr, circSep] using this
    have h2 : 2 * s ≤ circSep q.1 (q.1 + q.2) * V :=
      le_trans hchord (by rwa [mul_comm] at hlip')
    have h3 := (div_le_iff₀ hV).mpr h2
    linarith
  have hδ_au : min ρ (min (2 * η) (2 * s / V)) ≤ circSep q.1 u := by
    have hca : ρ ≤ circSep q.1 u := by
      rw [circSep_comm]
      exact circSep_ge_of_sub_mem hρ (by linarith) (by linarith)
    linarith
  have hδ_au' : min ρ (min (2 * η) (2 * s / V)) ≤ circSep q.1 u' := by
    have hca : ρ ≤ circSep q.1 u' := by
      rw [circSep_comm]
      exact circSep_ge_of_sub_mem hρ (by linarith) (by linarith)
    linarith
  have hδ_bu : min ρ (min (2 * η) (2 * s / V)) ≤ circSep (q.1 + q.2) u := by
    have hcb : ρ ≤ circSep (q.1 + q.2) u :=
      circSep_ge_of_sub_mem hρ (by linarith) (by linarith)
    linarith
  have hδ_bu' : min ρ (min (2 * η) (2 * s / V)) ≤ circSep (q.1 + q.2) u' := by
    have hcb : ρ ≤ circSep (q.1 + q.2) u' :=
      circSep_ge_of_sub_mem hρ (by linarith) (by linarith)
    linarith
  have hδ_uu' : min ρ (min (2 * η) (2 * s / V)) ≤ circSep u u' := by
    rw [circSep_eq_norm_sub]
    refine le_norm_coe_of_abs_bounds hδpos.le ?_ ?_ ?_
    · have : |u - u'| ≤ q.2 - 2 * ρ := hd_le
      linarith
    · linarith
    · linarith
  -- the spread quadrisecant
  have hspread : SpreadQuad (min ρ (min (2 * η) (2 * s / V))) (pmod q.1) (pmod (q.1 + q.2))
      (pmod u) (pmod u') := by
    refine ⟨pmod_mem _, pmod_mem _, pmod_mem _, pmod_mem _, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [circSep_pmod] using hδ_ab
    · simpa [circSep_pmod] using hδ_au
    · simpa [circSep_pmod] using hδ_au'
    · simpa [circSep_pmod] using hδ_bu
    · simpa [circSep_pmod] using hδ_bu'
    · simpa [circSep_pmod] using hδ_uu'
  have hm1 : IsMiddleOnChord r ((pmod q.1 : ℝ) : KnotParam)
      ((pmod (q.1 + q.2) : ℝ) : KnotParam) ((pmod u : ℝ) : KnotParam) := by
    rw [pmod_coe q.1, pmod_coe (q.1 + q.2), pmod_coe u]
    exact (isMiddleOnChord_iff_real hr q.1 (q.1 + q.2) u).mpr hu3
  have hm2 : IsMiddleOnChord r ((pmod q.1 : ℝ) : KnotParam)
      ((pmod (q.1 + q.2) : ℝ) : KnotParam) ((pmod u' : ℝ) : KnotParam) := by
    rw [pmod_coe q.1, pmod_coe (q.1 + q.2), pmod_coe u']
    exact (isMiddleOnChord_iff_real hr q.1 (q.1 + q.2) u').mpr hv3
  exact (hnq (pmod q.1) (pmod (q.1 + q.2)) (pmod u) (pmod u') hspread ⟨hm1, hm2⟩).elim



/-!
## 3. The cell index of a point of `OFatR`, closedness, and the assembly
-/

lemma cellOf_eq_of_mem {t₀ u : ℝ} {k : ℤ} (h1 : t₀ + (k : ℝ) * period ≤ u)
    (h2 : u < t₀ + ((k : ℝ) + 1) * period) : cellOf t₀ u = k :=
  cellOf_eq_iff.mpr ⟨h1, h2⟩

/-- A point of the obstruction set lies in the strip `0 < q.2 < period`. -/
lemma strip_of_mem_obstruction {r : ℝ → Space} {ρ : ℝ} {q : ℝ × ℝ}
    (hq : q ∈ OFatObstruction r ρ) : 0 < q.2 ∧ q.2 < period := by
  rcases hq with h | h
  · exact ⟨h.1, h.2.1⟩
  · exact ⟨h.1, h.2.1⟩

/-- A chosen middle parameter of the chord of a point of `OFatR` (junk if there is none). -/
noncomputable def midOf (r : ℝ → Space) (ρ : ℝ) (q : ℝ × ℝ) : ℝ := by
  classical
  exact if h : ∃ u : ℝ, q.1 + ρ ≤ u ∧ u ≤ q.1 + q.2 - ρ ∧
      r u ∈ openSegment ℝ (r q.1) (r (q.1 + q.2)) then Classical.choose h else 0

lemma midOf_spec {r : ℝ → Space} {ρ : ℝ} {q : ℝ × ℝ}
    (h : ∃ u : ℝ, q.1 + ρ ≤ u ∧ u ≤ q.1 + q.2 - ρ ∧
      r u ∈ openSegment ℝ (r q.1) (r (q.1 + q.2))) :
    q.1 + ρ ≤ midOf r ρ q ∧ midOf r ρ q ≤ q.1 + q.2 - ρ ∧
      r (midOf r ρ q) ∈ openSegment ℝ (r q.1) (r (q.1 + q.2)) := by
  rw [midOf, dif_pos h]
  exact Classical.choose_spec h

lemma exists_mid_of_mem_OFatR {r : ℝ → Space} {ρ : ℝ} {q : ℝ × ℝ}
    (hq : q ∈ OFatR r ρ) :
    ∃ u : ℝ, q.1 + ρ ≤ u ∧ u ≤ q.1 + q.2 - ρ ∧
      r u ∈ openSegment ℝ (r q.1) (r (q.1 + q.2)) := hq.2.2

/-- The **cell index** of a point of `OFatR r ρ`: the common cell of all the middles of its chord
(see `cellOf_eq_of_middle`). -/
noncomputable def cellAt (t₀ : ℝ) (r : ℝ → Space) (ρ : ℝ) (q : ℝ × ℝ) : ℤ :=
  cellOf t₀ (midOf r ρ q)

/-- **Local constancy of the cell index along `OFatR`.** -/
lemma cellAt_eventually_eq_of_tendsto {r : ℝ → Space} (hr : IsSmoothKnot r) {ρ : ℝ} (hρ : 0 < ρ)
    {t₀ η : ℝ} (hη : 0 < η)
    (hslab : ∀ u : ℝ, FatMiddle r ρ u → ∀ k : ℤ,
      η < |u - (t₀ + (k : ℝ) * period)|)
    {s V : ℝ} (hs : 0 < s) (hV : 0 < V)
    (hsep : ∀ a b : KnotParam, ρ ≤ dist a b → s ≤ ‖knotMap r a - knotMap r b‖)
    (hlip : ∀ a b : KnotParam, ‖knotMap r a - knotMap r b‖ ≤ V * dist a b)
    (hnq : ∀ a b z w : ℝ, SpreadQuad (min ρ (min (2 * η) (2 * s / V))) a b z w →
      ¬ (IsMiddleOnChord r (a : KnotParam) (b : KnotParam) (z : KnotParam) ∧
         IsMiddleOnChord r (a : KnotParam) (b : KnotParam) (w : KnotParam)))
    {qs : ℕ → ℝ × ℝ} {q : ℝ × ℝ} (hqs : Tendsto qs atTop (𝓝 q))
    (hqn : ∀ n, qs n ∈ OFatR r ρ) (hq : q ∈ OFatR r ρ) :
    ∀ᶠ n in atTop, cellAt t₀ r ρ (qs n) = cellAt t₀ r ρ q := by
  have hq0 : 0 < q.2 := hq.1
  have hq1 : q.2 < period := hq.2.1
  have hmid : q.1 + ρ ≤ midOf r ρ q ∧ midOf r ρ q ≤ q.1 + q.2 - ρ ∧
      r (midOf r ρ q) ∈ openSegment ℝ (r q.1) (r (q.1 + q.2)) :=
    midOf_spec (exists_mid_of_mem_OFatR hq)
  by_contra hcon
  obtain ⟨φ, hφ, hφne⟩ := Filter.extraction_of_frequently_atTop (Filter.not_eventually.mp hcon)
  obtain ⟨ψ, hψ, v, hv_tend, hv_lo, hv_hi, hv_open⟩ :=
    exists_middle_limit (u := fun n => midOf r ρ (qs (φ n))) hr hρ hq0 hq1
      (hqs.comp hφ.tendsto_atTop)
      (fun n => (midOf_spec (exists_mid_of_mem_OFatR (hqn (φ n)))).1)
      (fun n => (midOf_spec (exists_mid_of_mem_OFatR (hqn (φ n)))).2.1)
      (fun n => (midOf_spec (exists_mid_of_mem_OFatR (hqn (φ n)))).2.2)
  -- the limit is a middle of `q`, hence lies in the cell of `q`
  have hfv : FatMiddle r ρ v := ⟨q.1, q.2, hq0, hq1, hv_lo, hv_hi, hv_open⟩
  have hcellv : cellOf t₀ v = cellAt t₀ r ρ q :=
    cellOf_eq_of_middle hr hρ hη hslab hs hV hsep hlip hnq hq hv_lo hv_hi hv_open
      hmid.1 hmid.2.1 hmid.2.2
  -- `v` is in the interior of its own cell
  have hcore : t₀ + (cellOf t₀ v : ℝ) * period + η < v ∧
      v < t₀ + ((cellOf t₀ v : ℝ) + 1) * period - η := by
    have h2 : η < |v - (t₀ + ((cellOf t₀ v : ℝ) + 1) * period)| := by
      have := hslab v hfv (cellOf t₀ v + 1)
      simpa [Int.cast_add, Int.cast_one] using this
    exact cellOf_core hη rfl (hslab v hfv (cellOf t₀ v)) h2
  have hev : ∀ᶠ n in atTop, cellOf t₀ (midOf r ρ (qs (φ (ψ n)))) = cellOf t₀ v := by
    have hdist : ∀ᶠ n in atTop, |midOf r ρ (qs (φ (ψ n))) - v| < η := by
      have h := Metric.tendsto_nhds.mp hv_tend η hη
      simpa [Real.dist_eq] using h
    filter_upwards [hdist] with n hn
    have hn' := abs_lt.mp hn
    exact cellOf_eq_of_mem (by linarith [hcore.1, hn'.1]) (by linarith [hcore.2, hn'.2])
  obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp hev
  refine hφne (ψ n) ?_
  show cellOf t₀ (midOf r ρ (qs (φ (ψ n)))) = cellAt t₀ r ρ q
  rw [hn n le_rfl, hcellv]

/-- `OFatR r ρ` is closed at the points of the strip: a limit of fat-middle strip points lying in
the strip is again a fat-middle strip point. -/
lemma closure_OFatR_subset_of_strip {r : ℝ → Space} (hr : IsSmoothKnot r) {ρ : ℝ} (hρ : 0 < ρ)
    {q : ℝ × ℝ} (hq : q ∈ closure (OFatR r ρ)) (hq0 : 0 < q.2) (hq1 : q.2 < period) :
    q ∈ OFatR r ρ := by
  obtain ⟨qs, hqs_mem, hqs⟩ := mem_closure_iff_seq_limit.mp hq
  obtain ⟨φ, -, v, -, hv_lo, hv_hi, hv_open⟩ :=
    exists_middle_limit (u := fun n => midOf r ρ (qs n)) hr hρ hq0 hq1 hqs
      (fun n => (midOf_spec (exists_mid_of_mem_OFatR (hqs_mem n))).1)
      (fun n => (midOf_spec (exists_mid_of_mem_OFatR (hqs_mem n))).2.1)
      (fun n => (midOf_spec (exists_mid_of_mem_OFatR (hqs_mem n))).2.2)
  exact ⟨hq0, hq1, v, hv_lo, hv_hi, hv_open⟩

/-- **A locally finite set is closed.** -/
lemma isClosed_of_locallyFinite {S : Set (ℝ × ℝ)}
    (h : ∀ z : ℝ × ℝ, ∃ U : Set (ℝ × ℝ), IsOpen U ∧ z ∈ U ∧ (S ∩ U).Finite) :
    IsClosed S := by
  rw [← closure_subset_iff_isClosed]
  intro x hx
  by_contra hxS
  obtain ⟨U, hUo, hxU, hUfin⟩ := h x
  have hcl : IsClosed (S ∩ U) := hUfin.isClosed
  have hxnb : x ∈ U ∩ (S ∩ U)ᶜ := ⟨hxU, fun h => hxS h.1⟩
  obtain ⟨y, hy⟩ := mem_closure_iff.mp hx (U ∩ (S ∩ U)ᶜ) (hUo.inter hcl.isOpen_compl) hxnb
  exact hy.1.2 ⟨hy.2, hy.1.1⟩

/-- The tangent-chord set is locally finite (by `tangentChordLocallyFinite`), hence closed. -/
lemma isClosed_TCset {r : ℝ → Space} (hr : IsSmoothKnot r)
    (hinfl : ∀ t : ℝ, LinearIndependent ℝ ![deriv r t, deriv (deriv r) t])
    (htc : TangentChordGP r) : IsClosed (TCset r) := by
  refine isClosed_of_locallyFinite (fun z => ?_)
  obtain ⟨U, hUo, hzU, hUfin⟩ := tangentChordLocallyFinite hr hinfl htc z
  exact ⟨U, hUo, hzU,
    Set.Finite.subset hUfin (fun x hx => ⟨by simpa only [TCset] using hx.1, hx.2⟩)⟩

/-- The set `TCset r \ OFatR r ρ` is a subset of the locally finite set `TCset r`, hence closed. -/
lemma isClosed_TCset_sdiff_OFatR {r : ℝ → Space} (hr : IsSmoothKnot r)
    (hinfl : ∀ t : ℝ, LinearIndependent ℝ ![deriv r t, deriv (deriv r) t])
    (htc : TangentChordGP r) (ρ : ℝ) : IsClosed (TCset r \ OFatR r ρ) := by
  refine isClosed_of_locallyFinite (fun z => ?_)
  obtain ⟨U, hUo, hzU, hUfin⟩ := tangentChordLocallyFinite hr hinfl htc z
  refine ⟨U, hUo, hzU, Set.Finite.subset hUfin ?_⟩
  rintro x ⟨hx, hxU⟩
  exact ⟨by simpa only [TCset] using hx.1, hxU⟩

/-- **Points of `TCset \ OFatR` are isolated in the obstruction set.** -/
lemma exists_isOpen_inter_eq_singleton {r : ℝ → Space} (hr : IsSmoothKnot r) {ρ : ℝ} (hρ : 0 < ρ)
    (hinfl : ∀ t : ℝ, LinearIndependent ℝ ![deriv r t, deriv (deriv r) t])
    (htc : TangentChordGP r) {z : ℝ × ℝ} (hzA : z ∈ OFatObstruction r ρ)
    (hz : z ∉ OFatR r ρ) :
    ∃ U : Set (ℝ × ℝ), IsOpen U ∧ z ∈ U ∧ U ∩ OFatObstruction r ρ = {z} := by
  have hstrip := strip_of_mem_obstruction hzA
  have hzT : z ∈ TCset r \ OFatR r ρ := by
    rcases hzA with h | h
    · exact absurd h hz
    · exact ⟨h, hz⟩
  -- a neighbourhood of `z` avoiding `OFatR`
  have hznotclos : z ∉ closure (OFatR r ρ) :=
    fun h => hz (closure_OFatR_subset_of_strip hr hρ h hstrip.1 hstrip.2)
  have hU₁ : IsOpen (closure (OFatR r ρ))ᶜ := isClosed_closure.isOpen_compl
  have hzU₁ : z ∈ (closure (OFatR r ρ))ᶜ := hznotclos
  have hU₁disj : (closure (OFatR r ρ))ᶜ ∩ OFatR r ρ = ∅ :=
    Set.eq_empty_iff_forall_notMem.mpr (fun x hx => hx.1 (subset_closure hx.2))
  -- a neighbourhood of `z` meeting `TCset \ OFatR` only at `z`
  obtain ⟨U₂, hU₂o, hzU₂, hU₂fin⟩ :
      ∃ U₂ : Set (ℝ × ℝ), IsOpen U₂ ∧ z ∈ U₂ ∧ ((TCset r \ OFatR r ρ) ∩ U₂).Finite := by
    obtain ⟨U, hUo, hzU, hUfin⟩ := tangentChordLocallyFinite hr hinfl htc z
    exact ⟨U, hUo, hzU,
      Set.Finite.subset hUfin (fun x hx => ⟨by simpa only [TCset] using hx.1.1, hx.2⟩)⟩
  set F : Set (ℝ × ℝ) := ((TCset r \ OFatR r ρ) ∩ U₂) \ {z} with hF
  have hFfin : F.Finite := hU₂fin.sdiff
  set U : Set (ℝ × ℝ) := (closure (OFatR r ρ))ᶜ ∩ (U₂ \ F) with hU
  refine ⟨U, ?_, ?_, ?_⟩
  · rw [hU]; exact hU₁.inter (hU₂o.sdiff hFfin.isClosed)
  · rw [hU]
    refine ⟨hzU₁, hzU₂, ?_⟩
    intro hzF
    exact hzF.2 rfl
  · rw [hU]
    refine Set.Subset.antisymm ?_ ?_
    · rintro x ⟨hxU, hxA⟩
      have hxnotO : x ∉ OFatR r ρ := fun h => hxU.1 (subset_closure h)
      have hxnotF : x ∉ F := hxU.2.2
      have hxT : x ∈ TCset r := by
        rcases hxA with h | h
        · exact absurd h hxnotO
        · exact h
      have hxz : x = z := by
        by_contra hxz
        have : x ∈ F := ⟨⟨⟨hxT, hxnotO⟩, hxU.2.1⟩, hxz⟩
        exact hxnotF this
      rw [hxz]
      exact Set.mem_singleton z
    · intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact ⟨⟨hzU₁, hzU₂, fun h => h.2 rfl⟩, hzA⟩



/-!
## 4. The components of the obstruction set are bounded in the strip coordinate
-/

theorem components_bounded_of_no_spreadQuad
    {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r)
    {ρ : ℝ} (hρ : 0 < ρ)
    {t₀ η : ℝ} (hη : 0 < η) (hηP : 2 * η < LeanEval.KnotTheory.Quadrisecant.period)
    (hslab : ∀ u : ℝ, Work.Drive.FatMiddle r ρ u → ∀ k : ℤ,
      η < |u - (t₀ + (k : ℝ) * LeanEval.KnotTheory.Quadrisecant.period)|)
    {s V : ℝ} (hs : 0 < s) (hV : 0 < V)
    (hsep : ∀ a b : LeanEval.KnotTheory.Quadrisecant.KnotParam, ρ ≤ dist a b →
      s ≤ ‖LeanEval.KnotTheory.Quadrisecant.knotMap r a -
        LeanEval.KnotTheory.Quadrisecant.knotMap r b‖)
    (hlip : ∀ a b : LeanEval.KnotTheory.Quadrisecant.KnotParam,
      ‖LeanEval.KnotTheory.Quadrisecant.knotMap r a -
        LeanEval.KnotTheory.Quadrisecant.knotMap r b‖ ≤ V * dist a b)
    (htc : Work.Drive.TangentChordGP r)
    (hinfl : ∀ t : ℝ, LinearIndependent ℝ ![deriv r t, deriv (deriv r) t])
    (hnq : ∀ a b z w : ℝ, Work.Drive.SpreadQuad (min ρ (min (2 * η) (2 * s / V))) a b z w →
      ¬ (LeanEval.KnotTheory.Quadrisecant.IsMiddleOnChord r
            (a : LeanEval.KnotTheory.Quadrisecant.KnotParam)
            (b : LeanEval.KnotTheory.Quadrisecant.KnotParam)
            (z : LeanEval.KnotTheory.Quadrisecant.KnotParam) ∧
         LeanEval.KnotTheory.Quadrisecant.IsMiddleOnChord r
            (a : LeanEval.KnotTheory.Quadrisecant.KnotParam)
            (b : LeanEval.KnotTheory.Quadrisecant.KnotParam)
            (w : LeanEval.KnotTheory.Quadrisecant.KnotParam))) :
    ∀ z : ℝ × ℝ, z ∈ Work.Drive.OFatObstruction r ρ →
      Bornology.IsBounded (Prod.fst '' connectedComponentIn (Work.Drive.OFatObstruction r ρ) z) := by
  intro z hz
  classical
  by_cases hzOF : z ∈ OFatR r ρ
  · -- #### Case 1: the point has a fat middle
    set k : ℤ := cellAt t₀ r ρ z with hk
    set S : Set (ℝ × ℝ) := {q | q ∈ OFatR r ρ ∧ cellAt t₀ r ρ q = k} with hS
    -- the two relative closedness statements for `S`
    have hcl₁ : closure S ∩ OFatObstruction r ρ ⊆ S := by
      rintro q ⟨hqcl, hqA⟩
      have hqcl' : q ∈ closure (OFatR r ρ) := closure_mono (fun x hx => hx.1) hqcl
      have hstrip := strip_of_mem_obstruction hqA
      have hqOF : q ∈ OFatR r ρ := closure_OFatR_subset_of_strip hr hρ hqcl' hstrip.1 hstrip.2
      obtain ⟨qs, hqs_mem, hqs⟩ := mem_closure_iff_seq_limit.mp hqcl
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
        (cellAt_eventually_eq_of_tendsto hr hρ hη hslab hs hV hsep hlip hnq hqs
          (fun n => (hqs_mem n).1) hqOF)
      exact ⟨hqOF, by rw [← hN N le_rfl, (hqs_mem N).2]⟩
    have hcl₂ : closure (OFatObstruction r ρ \ S) ∩ OFatObstruction r ρ ⊆
        OFatObstruction r ρ \ S := by
      rintro q ⟨hqcl, hqA⟩
      refine ⟨hqA, ?_⟩
      rintro ⟨hqOF, hqk⟩
      obtain ⟨qs, hqs_mem, hqs⟩ := mem_closure_iff_seq_limit.mp hqcl
      by_cases hfin : ∀ᶠ n in atTop, qs n ∈ OFatR r ρ
      · obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hfin
        obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp
          (cellAt_eventually_eq_of_tendsto hr hρ hη hslab hs hV hsep hlip hnq
            (hqs.comp (Filter.tendsto_add_atTop_nat N)) (fun n => hN (n + N) (by omega)) hqOF)
        have hbad : cellAt t₀ r ρ (qs (M + N)) ≠ k := fun hc =>
          (hqs_mem (M + N)).2 ⟨hN (M + N) (by omega), hc⟩
        have h1 : cellAt t₀ r ρ (qs (M + N)) = cellAt t₀ r ρ q := hM M le_rfl
        exact hbad (by rw [h1, hqk])
      · obtain ⟨φ, hφ, hφT⟩ :=
          Filter.extraction_of_frequently_atTop (Filter.not_eventually.mp hfin)
        have hφmem : ∀ n, qs (φ n) ∈ TCset r \ OFatR r ρ := by
          intro n
          refine ⟨?_, hφT n⟩
          rcases (hqs_mem (φ n)).1 with h | h
          · exact absurd h (hφT n)
          · exact h
        have hqT : q ∈ TCset r \ OFatR r ρ :=
          (isClosed_TCset_sdiff_OFatR hr hinfl htc ρ).closure_subset
            (mem_closure_iff_seq_limit.mpr ⟨fun n => qs (φ n), hφmem,
              hqs.comp hφ.tendsto_atTop⟩)
        exact hqT.2 hqOF
    -- the component is contained in `S`
    have hA_sub : OFatObstruction r ρ ⊆ closure S ∪ closure (OFatObstruction r ρ \ S) := by
      intro x hx
      by_cases hxS : x ∈ S
      · exact Or.inl (subset_closure hxS)
      · exact Or.inr (subset_closure ⟨hx, hxS⟩)
    have hdisj : connectedComponentIn (OFatObstruction r ρ) z ∩
        (closure S ∩ closure (OFatObstruction r ρ \ S)) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro x ⟨hxK, hxScl, hxDScl⟩
      have hxA : x ∈ OFatObstruction r ρ := connectedComponentIn_subset _ _ hxK
      exact (hcl₂ ⟨hxDScl, hxA⟩).2 (hcl₁ ⟨hxScl, hxA⟩)
    have hKsub : connectedComponentIn (OFatObstruction r ρ) z ⊆ S := by
      have hzK : z ∈ connectedComponentIn (OFatObstruction r ρ) z := mem_connectedComponentIn hz
      have hzS : z ∈ S := ⟨hzOF, rfl⟩
      rcases (isPreconnected_iff_subset_of_disjoint_closed.mp
        isPreconnected_connectedComponentIn (closure S)
        (closure (OFatObstruction r ρ \ S)) isClosed_closure isClosed_closure
        (fun x hx => hA_sub (connectedComponentIn_subset _ _ hx)) hdisj) with h | h
      · exact fun x hx => hcl₁ ⟨h hx, connectedComponentIn_subset _ _ hx⟩
      · exact absurd ((hcl₂ ⟨h hzK, hz⟩).2 hzS) (absurd · (by simp))
    -- boundedness of `S` in the strip coordinate
    refine Bornology.IsBounded.subset (Metric.isBounded_Icc
      (t₀ + ((k : ℝ) - 1) * period + ρ) (t₀ + ((k : ℝ) + 1) * period - ρ)) ?_
    rintro x ⟨q, hqK, rfl⟩
    obtain ⟨hqOF, hqk⟩ := hKsub hqK
    have hspec := midOf_spec (exists_mid_of_mem_OFatR hqOF)
    have hcell : cellOf t₀ (midOf r ρ q) = k := hqk
    have hc := cellOf_eq_iff.mp hcell
    have hq2 : q.2 < period := hqOF.2.1
    constructor <;> linarith [hspec.1, hspec.2.1, hc.1, hc.2, hq2]
  · -- #### Case 2: the point is an isolated point of the obstruction set
    obtain ⟨U, hUo, hzU, hUeq⟩ := exists_isOpen_inter_eq_singleton hr hρ hinfl htc hz hzOF
    have hzK : z ∈ connectedComponentIn (OFatObstruction r ρ) z := mem_connectedComponentIn hz
    have hK : connectedComponentIn (OFatObstruction r ρ) z = {z} := by
      have hsub : OFatObstruction r ρ ⊆ ({z} : Set (ℝ × ℝ)) ∪ Uᶜ := by
        intro x hx
        by_cases h : x ∈ U
        · exact Or.inl (by have := (show x ∈ U ∩ OFatObstruction r ρ from ⟨h, hx⟩); rwa [hUeq] at this)
        · exact Or.inr h
      have hdisj : connectedComponentIn (OFatObstruction r ρ) z ∩
          (({z} : Set (ℝ × ℝ)) ∩ Uᶜ) = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro x ⟨-, hx, hxU⟩
        rw [Set.mem_singleton_iff] at hx
        rw [hx] at hxU
        exact hxU hzU
      rcases (isPreconnected_iff_subset_of_disjoint_closed.mp
        isPreconnected_connectedComponentIn {z} Uᶜ isClosed_singleton hUo.isClosed_compl
        (fun x hx => hsub (connectedComponentIn_subset _ _ hx)) hdisj) with h | h
      · exact Set.Subset.antisymm h (fun x hx => by
          rw [Set.mem_singleton_iff] at hx; rw [hx]; exact hzK)
      · exact absurd (h hzK) (fun hh => hh hzU)
    rw [hK, Set.image_singleton]
    exact Bornology.isBounded_singleton


end

end Work.Drive
