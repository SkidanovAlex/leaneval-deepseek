import Mathlib
import Submission.Work.OddVolterra.WinData.win_data
import Submission.Work.OddVolterra.Existence.krad_pos_state_region

/-!
# Support and regularity of the clamped data

The explicit diagonal form `diagForm` of the state datum is smooth on the region where the two
Abel radicands stay positive, and the cut-offs of `Work.OddVolterra.WinData.win_data` have their
support inside that region.  This file sets up the regions and the "cut-off times
smooth-on-a-neighbourhood" argument which makes the clamped data globally continuous.
-/

namespace Work.OddVolterra.WinData

open Work.OddVolterra
open scoped Topology ContDiff

noncomputable section

/-! ## The good slopes and states -/

/-- The slopes on which the diagonal form of the state datum has positive radicands: the support
interval of the slope cut-off, with `h`, `h'` strictly small. -/
def goodSlope (K : ℝ) (h : ℝ → ℝ) : Set ℝ :=
  {s : ℝ | s ∈ Set.Ioo (9 / 40 : ℝ) 1 ∧ |h s| < K ∧ |deriv h s| < K}

/-- The good states for the diagonal form: the first two coordinates are bounded away from `0`. -/
def goodG (K : ℝ) (h : ℝ → ℝ) : Set (ℝ × St) :=
  {p : ℝ × St | p.1 ∈ goodSlope K h ∧ (1 / 6 : ℝ) < |p.2 0| ∧ (1 / 6 : ℝ) < |p.2 1|}

lemma isOpen_goodSlope {K : ℝ} {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) :
    IsOpen (goodSlope K h) := by
  have h1 : IsOpen (Set.Ioo (9 / 40 : ℝ) 1) := isOpen_Ioo
  have h2 : IsOpen {s : ℝ | |h s| < K} :=
    isOpen_lt (continuous_abs.comp hh.continuous) continuous_const
  have h3 : IsOpen {s : ℝ | |deriv h s| < K} :=
    isOpen_lt (continuous_abs.comp (hh.continuous_deriv (by simp))) continuous_const
  have heq : goodSlope K h = Set.Ioo (9 / 40 : ℝ) 1 ∩ {s : ℝ | |h s| < K}
      ∩ {s : ℝ | |deriv h s| < K} := by
    ext s
    simp only [goodSlope, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_Ioo]
    tauto
  rw [heq]
  exact (h1.inter h2).inter h3

lemma isOpen_goodG {K : ℝ} {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) :
    IsOpen (goodG K h) := by
  have h0 : IsOpen (goodSlope K h) := isOpen_goodSlope hh
  have h1 : IsOpen {p : ℝ × St | p.1 ∈ goodSlope K h} := h0.preimage continuous_fst
  have h2 : IsOpen {p : ℝ × St | (1 / 6 : ℝ) < |p.2 0|} :=
    isOpen_lt continuous_const (continuous_abs.comp ((continuous_apply 0).comp continuous_snd))
  have h3 : IsOpen {p : ℝ × St | (1 / 6 : ℝ) < |p.2 1|} :=
    isOpen_lt continuous_const (continuous_abs.comp ((continuous_apply 1).comp continuous_snd))
  have heq : goodG K h = {p : ℝ × St | p.1 ∈ goodSlope K h}
      ∩ {p : ℝ × St | (1 / 6 : ℝ) < |p.2 0|} ∩ {p : ℝ × St | (1 / 6 : ℝ) < |p.2 1|} := by
    ext p
    simp only [goodG, Set.mem_setOf_eq, Set.mem_inter_iff]
    tauto
  rw [heq]
  exact (h1.inter h2).inter h3

/-! ## The chord function on the slope window -/

lemma profileX_unfold (s : ℝ) :
    Commons.Geometry.Ulam.profileX s = 1 / Real.sqrt (1 + s ^ 2) := rfl

lemma seven_tenths_le_profileX {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 1) :
    (7 / 10 : ℝ) ≤ Commons.Geometry.Ulam.profileX s := by
  rw [profileX_unfold]
  have hsq : s ^ 2 ≤ (1 : ℝ) ^ 2 := by nlinarith
  have h1 : Real.sqrt (1 + s ^ 2) ≤ Real.sqrt 2 := by
    refine Real.sqrt_le_sqrt ?_
    nlinarith
  have h2 : 0 < Real.sqrt (1 + s ^ 2) := Real.sqrt_pos.mpr (by nlinarith [sq_nonneg s])
  have h3 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h4 : 1 / Real.sqrt 2 ≤ 1 / Real.sqrt (1 + s ^ 2) := one_div_le_one_div_of_le h2 h1
  have h5 : (7 / 10 : ℝ) ≤ 1 / Real.sqrt 2 := by
    rw [le_div_iff₀ h3]
    have h6 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg 2]
  linarith

lemma mem_goodG_of_mem_support {K K' : ℝ} {h : ℝ → ℝ} (hK' : K' ≤ 1 / 100) (hKK' : K < K')
    (hjet : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ K)
    {s : ℝ} (hs : |s - 3 / 5| ≤ wCs.rOut) {z : St} (hz : ‖z - baseState s‖ ≤ wCzR) :
    (s, z) ∈ goodG K' h := by
  have h0 : |h s| ≤ K := by simpa using hjet 0 (by norm_num) s
  have h1 : |deriv h s| ≤ K := by simpa [iteratedDeriv_one] using hjet 1 (by norm_num) s
  have h0' : |h s| < K' := lt_of_le_of_lt h0 hKK'
  have h1' : |deriv h s| < K' := lt_of_le_of_lt h1 hKK'
  have hrmax : wCs.rOut = 7 / 20 + 1 / 100 := wCs_rOut
  rw [hrmax] at hs
  obtain ⟨hsa, hsb⟩ := abs_le.mp hs
  have hs0 : 9 / 40 < s := by linarith
  have hs1 : s < 1 := by linarith
  have hcoord : ∀ i : Fin 4, |z i - baseState s i| ≤ wCzR := by
    intro i
    have h := dist_le_pi_dist z (baseState s) i
    rw [Real.dist_eq, dist_eq_norm] at h
    exact le_trans h hz
  have hprof : (7 / 10 : ℝ) ≤ Commons.Geometry.Ulam.profileX s :=
    seven_tenths_le_profileX (by linarith) (by linarith)
  have hlow : (1 / 6 : ℝ) < Commons.Geometry.Ulam.profileX s - wCzR := by
    rw [wCzR]; linarith
  have hz0 : (1 / 6 : ℝ) < |z 0| := by
    have h := hcoord 0
    have hb : baseState s 0 = Commons.Geometry.Ulam.profileX s := rfl
    rw [hb] at h
    have h2 : Commons.Geometry.Ulam.profileX s - wCzR ≤ z 0 := by linarith [(abs_le.mp h).1]
    rw [abs_of_pos (by linarith)]
    linarith
  have hz1 : (1 / 6 : ℝ) < |z 1| := by
    have h := hcoord 1
    have hb : baseState s 1 = Commons.Geometry.Ulam.profileX s := rfl
    rw [hb] at h
    have h2 : Commons.Geometry.Ulam.profileX s - wCzR ≤ z 1 := by linarith [(abs_le.mp h).1]
    rw [abs_of_pos (by linarith)]
    linarith
  exact ⟨⟨⟨hs0, hs1⟩, h0', h1'⟩, hz0, hz1⟩

lemma support_wChiG_subset {K K' : ℝ} {h : ℝ → ℝ} (hK' : K' ≤ 1 / 100) (hKK' : K < K')
    (hjet : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ K) :
    Function.support (fun p : ℝ × St => wChiG p.1 p.2) ⊆ goodG K' h := by
  intro p hp
  rw [Function.mem_support] at hp
  have hcs : (wCs : ℝ → ℝ) p.1 ≠ 0 := fun h0 => hp (by rw [wChiG, h0, zero_mul])
  have hcz : (wCz : St → ℝ) (p.2 - baseState p.1) ≠ 0 :=
    fun h0 => hp (by rw [wChiG, h0, mul_zero])
  have hs : |p.1 - 3 / 5| ≤ wCs.rOut := by
    have h : p.1 ∈ Function.support (wCs : ℝ → ℝ) := Function.mem_support.mpr hcs
    rw [ContDiffBump.support_eq, Metric.mem_ball, Real.dist_eq] at h
    exact le_of_lt h
  have hz : ‖p.2 - baseState p.1‖ ≤ wCzR := by
    have h : (p.2 - baseState p.1) ∈ Function.support (wCz : St → ℝ) :=
      Function.mem_support.mpr hcz
    rw [ContDiffBump.support_eq, wCz_rOut, Metric.mem_ball, dist_zero_right] at h
    exact le_of_lt h
  exact mem_goodG_of_mem_support hK' hKK' hjet hs hz

/-! ## Positivity of the diagonal radicand -/

lemma diag_radicand_pos {K : ℝ} {h : ℝ → ℝ} (hK : K ≤ 1 / 100)
    {s t : ℝ} (hs : s ∈ goodSlope K h) (ht : (1 / 6 : ℝ) < |t|) :
    0 < (t + deriv h s) * (2 * line h s t) := by
  obtain ⟨⟨hs0, hs1⟩, hhs, hhd⟩ := hs
  have hlt1 : |deriv h s| < 1 / 100 := lt_of_lt_of_le hhd hK
  have hlt0 : |h s| < 1 / 100 := lt_of_lt_of_le hhs hK
  have hspos : (0 : ℝ) < s := by linarith
  rcases lt_trichotomy t 0 with htneg | ht0 | htpos
  · have htlt : t < -(1 / 6) := by
      rw [abs_of_neg htneg] at ht
      linarith
    have h1 : t + deriv h s < 0 := by
      have := (abs_lt.mp hlt1).2
      linarith
    have h2 : line h s t < 0 := by
      have hm : s * t < s * (-(1 / 6)) := mul_lt_mul_of_pos_left htlt hspos
      have hs' : s * (-(1 / 6)) < (9 / 40) * (-(1 / 6)) := by nlinarith
      have hh : h s < 1 / 100 := (abs_lt.mp hlt0).2
      have hsum : s * t + h s < 0 := by nlinarith
      simpa only [line] using hsum
    exact mul_pos_of_neg_of_neg h1 (by linarith)
  · rw [ht0] at ht; norm_num at ht
  · have htgt : (1 / 6 : ℝ) < t := by
      rw [abs_of_pos htpos] at ht
      exact ht
    have h1 : 0 < t + deriv h s := by
      have := (abs_lt.mp hlt1).1
      linarith
    have h2 : 0 < line h s t := by
      have hm : s * (1 / 6) < s * t := mul_lt_mul_of_pos_left htgt hspos
      have hs' : (9 / 40) * (1 / 6) < s * (1 / 6) := by nlinarith
      have hh : -(1 / 100) < h s := (abs_lt.mp hlt0).1
      have hsum : 0 < s * t + h s := by nlinarith
      simpa only [line] using hsum
    exact mul_pos h1 (by linarith)

end

end Work.OddVolterra.WinData
