import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBoxFock.farK0_defs
import Submission.Work.BoseBoxFock.lattice_sum_inv_fourth_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

open Finset

noncomputable section

/-- The sup-norm `K m = max_i |m i|` of an integer multi-index is at most the Euclidean norm of
the lattice vector `latVec m`. -/
lemma K_le_norm_latVec (m : Fin 3 → ℤ) : (K m : ℝ) ≤ ‖latVec m‖ := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin 3))
    ⟨0, Finset.mem_univ 0⟩ (fun j => (m j).natAbs)
  have hKsq : ((K m : ℕ) : ℝ) ^ 2 ≤ ‖latVec m‖ ^ 2 := by
    rw [latVec_norm_sq, nSq_cast]
    have h1 : ((K m : ℕ) : ℝ) ^ 2 = ((m i : ℤ) : ℝ) ^ 2 := by
      rw [show K m = (m i).natAbs from hi]
      exact cast_natAbs_sq (m i)
    rw [h1]
    exact Finset.single_le_sum (fun j _ => sq_nonneg (((m j : ℤ) : ℝ))) (Finset.mem_univ i)
  have h0 : (0 : ℝ) ≤ ((K m : ℕ) : ℝ) := Nat.cast_nonneg _
  have h1 : ((K m : ℕ) : ℝ) = Real.sqrt (((K m : ℕ) : ℝ) ^ 2) := (Real.sqrt_sq h0).symm
  rw [h1]
  calc Real.sqrt (((K m : ℕ) : ℝ) ^ 2) ≤ Real.sqrt (‖latVec m‖ ^ 2) := Real.sqrt_le_sqrt hKsq
    _ = ‖latVec m‖ := Real.sqrt_sq (norm_nonneg _)

/-- The `m = 0` term of the kernel vanishes (division by zero) and every other term is at most
`1`: for `m ≠ 0` the lattice vector has Euclidean norm `≥ 1`. -/
lemma inv_norm_latVec_pow_four_le_one (m : Fin 3 → ℤ) : ((‖latVec m‖ ^ 4)⁻¹) ≤ 1 := by
  rcases eq_or_ne m 0 with rfl | hm
  · rw [show latVec (0 : Fin 3 → ℤ) = 0 by ext i; simp [latVec]]
    simp
  · have h1 : (1 : ℝ) ≤ (nSq m : ℝ) := by
      have hne : nSq m ≠ 0 := fun h => hm ((nSq_eq_zero_iff m).mp h)
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne
    have h2 : (1 : ℝ) ≤ ‖latVec m‖ := by
      rw [← Real.sqrt_sq (norm_nonneg (latVec m)), latVec_norm_sq]
      exact Real.one_le_sqrt.mpr h1
    refine inv_le_one_of_one_le₀ ?_
    simpa using pow_le_pow_left₀ zero_le_one h2 4

/-- **Uniform bound on the finite partial sums** of the lattice kernel: for every finite set `u` of
multi-indices, `∑_{m ∈ u} (‖latVec m‖⁴)⁻¹ ≤ 227`. -/
lemma sum_inv_norm_latVec_le (u : Finset (Fin 3 → ℤ)) :
    (∑ m ∈ u, ((‖latVec m‖ ^ 4)⁻¹)) ≤ 227 := by
  rw [← Finset.sum_filter_add_sum_filter_not (s := u) (p := fun m => 2 ≤ K m)
        (f := fun m => ((‖latVec m‖ ^ 4)⁻¹))]
  have hbig : (∑ m ∈ u.filter (fun m => 2 ≤ K m), ((‖latVec m‖ ^ 4)⁻¹)) ≤ 200 := by
    calc (∑ m ∈ u.filter (fun m => 2 ≤ K m), ((‖latVec m‖ ^ 4)⁻¹))
        ≤ ∑ m ∈ u.filter (fun m => 2 ≤ K m), ((K m : ℝ) - 1) ^ (-(4 : ℝ)) := by
          refine Finset.sum_le_sum (fun m hm => ?_)
          have hk : 2 ≤ K m := (Finset.mem_filter.mp hm).2
          have hK2 : (2 : ℝ) ≤ (K m : ℝ) := by exact_mod_cast hk
          have hpos1 : (0 : ℝ) < (K m : ℝ) - 1 := by linarith
          have hle : (K m : ℝ) - 1 ≤ ‖latVec m‖ := le_trans (by linarith) (K_le_norm_latVec m)
          have hpos2 : (0 : ℝ) < ‖latVec m‖ := by linarith
          have h4 : ((K m : ℝ) - 1) ^ 4 ≤ ‖latVec m‖ ^ 4 :=
            pow_le_pow_left₀ (le_of_lt hpos1) hle 4
          have h := (inv_le_inv₀ (pow_pos hpos2 4) (pow_pos hpos1 4)).mpr h4
          rw [Real.rpow_neg (le_of_lt hpos1) 4, Real.rpow_ofNat]
          exact h
      _ = ∑ m ∈ u, (if 2 ≤ K m then ((K m : ℝ) - 1) ^ (-(4 : ℝ)) else 0) :=
          Finset.sum_filter _ _
      _ = ∑ m ∈ u, (if (2 : ℝ) ≤ ‖m‖ then (‖m‖ - 1) ^ (-(4 : ℝ)) else 0) := by
          refine Finset.sum_congr rfl (fun m _ => ?_)
          rw [NormEqKcast m]
          by_cases h : 2 ≤ K m
          · rw [if_pos h, if_pos (by exact_mod_cast h)]
          · rw [if_neg h, if_neg (by exact_mod_cast h)]
      _ ≤ 200 := lattice_sum_inv_fourth_le u
  have hsmall : (∑ m ∈ u.filter (fun m => ¬ 2 ≤ K m), ((‖latVec m‖ ^ 4)⁻¹)) ≤ 27 := by
    calc (∑ m ∈ u.filter (fun m => ¬ 2 ≤ K m), ((‖latVec m‖ ^ 4)⁻¹))
        ≤ ∑ m ∈ u.filter (fun m => ¬ 2 ≤ K m), (1 : ℝ) :=
          Finset.sum_le_sum (fun m _ => inv_norm_latVec_pow_four_le_one m)
      _ = ((u.filter (fun m => ¬ 2 ≤ K m)).card : ℝ) := by simp
      _ ≤ 27 := by
          have hsub : u.filter (fun m => ¬ 2 ≤ K m) ⊆ box 1 := by
            intro m hm
            rw [Finset.mem_filter] at hm
            rw [mem_box_iff]
            intro i
            have hK : K m ≤ 1 := by omega
            exact le_trans (K_spec m i) hK
          calc ((u.filter (fun m => ¬ 2 ≤ K m)).card : ℝ)
              ≤ ((box 1).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
            _ = 27 := by rw [shellCard_box_card]; norm_num
  linarith

theorem farK0_summable_lattice_inv_fourth :
    Summable fun m : Fin 3 → ℤ => ((‖Work.BoseBoxFock.latVec m‖ ^ 4)⁻¹) := by
  refine summable_of_sum_le (c := 227) (fun m => ?_) (fun u => ?_)
  · exact inv_nonneg.mpr (pow_nonneg (norm_nonneg _) 4)
  · exact sum_inv_norm_latVec_le u

end

end Work.BoseBoxFock
