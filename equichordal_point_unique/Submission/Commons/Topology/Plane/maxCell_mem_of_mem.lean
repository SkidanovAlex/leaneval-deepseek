import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Data.Int.Star
import Submission.Commons.Topology.Plane.exists_dyadic_exhaustion_of_isOpen_complex

namespace Commons.Topology.Plane

/-- The real-slice form of "a fine dyadic interval lies inside its coarse parent".
If `x` lies in the slice `[a/2^(m+1), (a+1)/2^(m+1)]`, then `x` lies in the slice
`[(a/2)/2^m, ((a/2)+1)/2^m]`. -/
lemma dyadicSlice_parent (a : ℤ) (m : ℕ) (x : ℝ)
    (h : (a:ℝ)/2^(m+1) ≤ x ∧ x ≤ ((a:ℝ)+1)/2^(m+1)) :
    ((a/2:ℤ):ℝ)/2^m ≤ x ∧ x ≤ (((a/2:ℤ):ℝ)+1)/2^m := by
  set q : ℤ := a / 2 with hq
  set s : ℤ := a % 2 with hs
  have hdec : 2 * q + s = a := by rw [hq, hs]; exact Int.mul_ediv_add_emod a 2
  have hs0 : 0 ≤ s := by rw [hs]; exact Int.emod_nonneg a (by norm_num)
  have hs2 : s < 2 := by rw [hs]; exact Int.emod_lt_of_pos a (by norm_num)
  have hdecR : (a:ℝ) = 2*(q:ℝ) + (s:ℝ) := by exact_mod_cast hdec.symm
  have hs0R : (0:ℝ) ≤ (s:ℝ) := by exact_mod_cast hs0
  have hs2R : (s:ℝ) ≤ 1 := by
    have : s ≤ 1 := by omega
    exact_mod_cast this
  have hpow : (2:ℝ)^(m+1) = 2 * (2:ℝ)^m := by rw [pow_succ]; ring
  have h2m : (0:ℝ) < 2^m := by positivity
  have h2m1 : (0:ℝ) < 2^(m+1) := by positivity
  refine ⟨?_, ?_⟩
  · have hkey : (q:ℝ)/2^m ≤ (a:ℝ)/2^(m+1) := by
      rw [div_le_iff₀ h2m, div_mul_eq_mul_div, le_div_iff₀ h2m1, hpow]
      nlinarith [hdecR, h2m, hs0R]
    linarith [hkey, h.1]
  · have hkey : ((a:ℝ)+1)/2^(m+1) ≤ ((q:ℝ)+1)/2^m := by
      rw [div_le_iff₀ h2m1, div_mul_eq_mul_div, le_div_iff₀ h2m, hpow]
      nlinarith [hdecR, h2m, hs2R]
    linarith [hkey, h.2]

lemma dyadicCell_subset_parent (m : ℕ) (p : ℤ × ℤ) :
    dyadicCell (m+1) p ⊆ dyadicCell m (p.1/2, p.2/2) := by
  intro z hz
  obtain ⟨hr1, hr2, hi1, hi2⟩ := hz
  obtain ⟨h1, h2⟩ := dyadicSlice_parent p.1 m z.re ⟨hr1, hr2⟩
  obtain ⟨h3, h4⟩ := dyadicSlice_parent p.2 m z.im ⟨hi1, hi2⟩
  exact ⟨h1, h2, h3, h4⟩

lemma dyadicCell_subset_parent' {n : ℕ} (hn : 0 < n) (p : ℤ × ℤ) :
    dyadicCell n p ⊆ dyadicCell (n-1) (p.1/2, p.2/2) := by
  have h : n = (n-1)+1 := by omega
  rw [h]
  exact dyadicCell_subset_parent (n-1) p

theorem maxCell_mem_of_mem (U : Set ℂ) (hU : IsOpen U) {z : ℂ} (hz : z ∈ U) : ∃ (n : ℕ) (p : ℤ × ℤ), z ∈ Commons.Topology.Plane.dyadicCell n p ∧ Commons.Topology.Plane.dyadicCell n p ⊆ U ∧ (n = 0 ∨ ¬ Commons.Topology.Plane.dyadicCell (n - 1) (p.1 / 2, p.2 / 2) ⊆ U) := by
  classical
  -- the set of admissible levels is nonempty: a sufficiently fine cell around `z` is in `U`
  have hex : ∃ n, ∃ p : ℤ × ℤ, z ∈ dyadicCell n p ∧ dyadicCell n p ⊆ U := by
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU z hz
    obtain ⟨N, hN⟩ := exists_nat_gt (Real.sqrt 2 / r)
    have h2N : (N:ℝ) ≤ (2:ℝ)^N := by
      have hlt : N < 2^N := Nat.lt_two_pow_self
      have hcast : (N:ℝ) < ((2:ℕ)^N : ℝ) := by exact_mod_cast hlt
      push_cast at hcast
      linarith
    have hpow : (Real.sqrt 2 / r) < (2:ℝ)^N := lt_of_lt_of_le hN h2N
    have hsqrt : Real.sqrt 2 < r * (2:ℝ)^N := by
      rw [div_lt_iff₀ hr] at hpow
      linarith
    have hcell : Real.sqrt 2 / 2^N < r := by
      rw [div_lt_iff₀ (by positivity : (0:ℝ) < 2^N)]
      linarith
    obtain ⟨p, hzp⟩ := dyadicCell_grid_cover N z
    refine ⟨N, p, hzp, fun w hw => hball ?_⟩
    rw [Metric.mem_ball]
    exact lt_of_le_of_lt (dyadicCell_dist_le hw hzp) hcell
  let P : ℕ → Prop := fun n => ∃ p : ℤ × ℤ, z ∈ dyadicCell n p ∧ dyadicCell n p ⊆ U
  have hP : ∃ n, P n := hex
  have hspec : P (Nat.find hP) := Nat.find_spec hP
  obtain ⟨p, hzp, hpU⟩ := hspec
  refine ⟨Nat.find hP, p, hzp, hpU, ?_⟩
  by_cases h0 : Nat.find hP = 0
  · exact Or.inl h0
  · refine Or.inr ?_
    intro hpar
    have hpos : 0 < Nat.find hP := Nat.pos_of_ne_zero h0
    have hsub := dyadicCell_subset_parent' hpos p
    have hzpar : z ∈ dyadicCell (Nat.find hP - 1) (p.1/2, p.2/2) := hsub hzp
    have hPm : P (Nat.find hP - 1) := ⟨(p.1/2, p.2/2), hzpar, hpar⟩
    exact Nat.find_min hP (Nat.sub_one_lt h0) hPm

end Commons.Topology.Plane