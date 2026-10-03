import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

namespace Commons.Analysis.Hilbert

open scoped BigOperators ENNReal

/-- Membership in the symmetric integer ball of radius `s`. -/
lemma natAbs_le_iff_int (t : ℤ) (s : ℕ) : t.natAbs ≤ s ↔ -(s : ℤ) ≤ t ∧ t ≤ (s : ℤ) := by
  constructor
  · intro h
    have h' : |t| ≤ ((s : ℕ) : ℤ) := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast h
    exact abs_le.mp h'
  · intro h
    have h' : |t| ≤ ((s : ℕ) : ℤ) := abs_le.mpr h
    rw [← Int.natCast_natAbs] at h'
    exact_mod_cast h'

/-- Telescoping of the increments of an antitone `ℝ≥0∞`-valued sequence. -/
lemma sum_Ico_tsub_add {w : ℕ → ℝ≥0∞} (hw : Antitone w) {j N : ℕ} (h : j ≤ N) :
    ∑ s ∈ Finset.Ico j N, (w s - w (s + 1)) + w N = w j := by
  induction N, h using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
    rw [Finset.sum_Ico_succ_top hN, add_assoc,
        tsub_add_cancel_of_le (hw (Nat.le_succ N)), ih]

/-- Reindexing a symmetric integer interval along `t ↦ n - t`. -/
lemma sum_Icc_neg_symm_shift (f : ℤ → ℝ≥0∞) (n : ℤ) (S : ℕ) :
    ∑ t ∈ Finset.Icc (-(S : ℤ)) (S : ℤ), f (n - t)
      = ∑ k ∈ Finset.Icc (n - (S : ℤ)) (n + (S : ℤ)), f k := by
  have hinj : Set.InjOn (fun t : ℤ => n - t) ↑(Finset.Icc (-(S : ℤ)) (S : ℤ)) := by
    intro a _ b _ h
    simp only at h
    omega
  rw [← Finset.sum_image hinj]
  congr 1
  ext k
  simp only [Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro ⟨t, ⟨h1, h2⟩, hk⟩
    omega
  · intro hk
    exact ⟨n - k, by omega, by omega⟩

/-- The number of integers in a symmetric ball, in `ℝ≥0∞`. -/
lemma sum_one_Icc_neg_symm (S : ℕ) :
    (∑ _t ∈ Finset.Icc (-(S : ℤ)) (S : ℤ), (1 : ℝ≥0∞)) = ((2 * S + 1 : ℕ) : ℝ≥0∞) := by
  rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  congr 1
  rw [Int.card_Icc]
  have h : (S : ℤ) + 1 - (-(S : ℤ)) = ((2 * S + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [h, Int.toNat_natCast]

/-- **Layer-cake decomposition over a symmetric integer ball.**  For an antitone weight `w`,
the weighted sum over the ball of radius `S` is the sum of the weighted ball sums of `f`,
with weights the increments `w s - w (s+1)` of `w`. -/
lemma layered_ball_sum {w : ℕ → ℝ≥0∞} (hw : Antitone w) (f : ℤ → ℝ≥0∞) (S : ℕ) :
    ∑ t ∈ Finset.Icc (-(S : ℤ)) (S : ℤ), w t.natAbs * f t
      = (∑ s ∈ Finset.range (S + 1),
          (w s - w (s + 1)) * (∑ t ∈ Finset.Icc (-(s : ℤ)) (s : ℤ), f t))
        + w (S + 1) * (∑ t ∈ Finset.Icc (-(S : ℤ)) (S : ℤ), f t) := by
  -- pointwise layer-cake identity
  have hpt : ∀ t ∈ Finset.Icc (-(S : ℤ)) (S : ℤ),
      w t.natAbs
        = (∑ s ∈ Finset.range (S + 1),
            (if t.natAbs ≤ s then (w s - w (s + 1)) else 0)) + w (S + 1) := by
    intro t ht
    have htS : t.natAbs ≤ S := by
      rw [Finset.mem_Icc] at ht
      exact (natAbs_le_iff_int t S).mpr ht
    rw [← Finset.sum_filter]
    have hfil : (Finset.range (S + 1)).filter (fun s => t.natAbs ≤ s)
        = Finset.Ico t.natAbs (S + 1) := by
      ext s
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      omega
    rw [hfil]
    exact (sum_Ico_tsub_add hw (Nat.le_succ_of_le htS)).symm
  have hfilB : ∀ s ≤ S, (Finset.Icc (-(S : ℤ)) (S : ℤ)).filter (fun t => t.natAbs ≤ s)
      = Finset.Icc (-(s : ℤ)) (s : ℤ) := by
    intro s hs
    ext t
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨_, h2⟩
      exact (natAbs_le_iff_int t s).mp h2
    · intro h
      refine ⟨⟨?_, ?_⟩, (natAbs_le_iff_int t s).mpr h⟩ <;> omega
  calc ∑ t ∈ Finset.Icc (-(S : ℤ)) (S : ℤ), w t.natAbs * f t
      = ∑ t ∈ Finset.Icc (-(S : ℤ)) (S : ℤ),
          ((∑ s ∈ Finset.range (S + 1),
            (if t.natAbs ≤ s then (w s - w (s + 1)) else 0)) + w (S + 1)) * f t := by
        apply Finset.sum_congr rfl
        intro t ht
        rw [hpt t ht]
    _ = (∑ t ∈ Finset.Icc (-(S : ℤ)) (S : ℤ),
          (∑ s ∈ Finset.range (S + 1),
            (if t.natAbs ≤ s then (w s - w (s + 1)) else 0)) * f t)
        + ∑ t ∈ Finset.Icc (-(S : ℤ)) (S : ℤ), w (S + 1) * f t := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro t _
        rw [add_mul]
    _ = (∑ s ∈ Finset.range (S + 1),
          (w s - w (s + 1)) * (∑ t ∈ Finset.Icc (-(s : ℤ)) (s : ℤ), f t))
        + w (S + 1) * (∑ t ∈ Finset.Icc (-(S : ℤ)) (S : ℤ), f t) := by
        congr 1
        · calc ∑ t ∈ Finset.Icc (-(S : ℤ)) (S : ℤ),
                (∑ s ∈ Finset.range (S + 1),
                  (if t.natAbs ≤ s then (w s - w (s + 1)) else 0)) * f t
              = ∑ t ∈ Finset.Icc (-(S : ℤ)) (S : ℤ),
                  ∑ s ∈ Finset.range (S + 1),
                    (if t.natAbs ≤ s then (w s - w (s + 1)) else 0) * f t := by
                apply Finset.sum_congr rfl
                intro t _
                rw [Finset.sum_mul]
            _ = ∑ s ∈ Finset.range (S + 1),
                  ∑ t ∈ Finset.Icc (-(S : ℤ)) (S : ℤ),
                    (if t.natAbs ≤ s then (w s - w (s + 1)) else 0) * f t :=
                Finset.sum_comm
            _ = ∑ s ∈ Finset.range (S + 1),
                  (w s - w (s + 1)) * (∑ t ∈ Finset.Icc (-(s : ℤ)) (s : ℤ), f t) := by
                apply Finset.sum_congr rfl
                intro s hs
                have hsS : s ≤ S := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
                rw [show (∑ t ∈ Finset.Icc (-(S : ℤ)) (S : ℤ),
                      (if t.natAbs ≤ s then (w s - w (s + 1)) else 0) * f t)
                    = ∑ t ∈ Finset.Icc (-(S : ℤ)) (S : ℤ),
                        (if t.natAbs ≤ s then (w s - w (s + 1)) * f t else 0) from by
                      apply Finset.sum_congr rfl
                      intro t _
                      by_cases hc : t.natAbs ≤ s <;> simp [hc]]
                rw [← Finset.sum_filter, hfilB s hsS, Finset.mul_sum]
        · rw [Finset.mul_sum]

/-- **Layer-cake bound on a symmetric integer interval.**  If the symmetric ball sums of `f`
grow at most like `(2S+1) * M`, then the weighted ball sums with an antitone weight obey the
same bound with the weight's total mass. -/
lemma radial_ball_sum_le_aux {w : ℕ → ℝ≥0∞} (hw : Antitone w) {f : ℤ → ℝ≥0∞} {M : ℝ≥0∞}
    (hf : ∀ S : ℕ, ∑ t ∈ Finset.Icc (-(S : ℤ)) (S : ℤ), f t ≤ ((2 * S + 1 : ℕ) : ℝ≥0∞) * M)
    (S : ℕ) :
    ∑ t ∈ Finset.Icc (-(S : ℤ)) (S : ℤ), w t.natAbs * f t
      ≤ (∑ t ∈ Finset.Icc (-(S : ℤ)) (S : ℤ), w t.natAbs) * M := by
  have hone : (∑ t ∈ Finset.Icc (-(S : ℤ)) (S : ℤ), w t.natAbs)
      = (∑ s ∈ Finset.range (S + 1),
          (w s - w (s + 1)) * (∑ _t ∈ Finset.Icc (-(s : ℤ)) (s : ℤ), (1 : ℝ≥0∞)))
        + w (S + 1) * (∑ _t ∈ Finset.Icc (-(S : ℤ)) (S : ℤ), (1 : ℝ≥0∞)) := by
    have h1 : (∑ t ∈ Finset.Icc (-(S : ℤ)) (S : ℤ), w t.natAbs)
        = ∑ t ∈ Finset.Icc (-(S : ℤ)) (S : ℤ), w t.natAbs * (1 : ℝ≥0∞) := by simp
    rw [h1, layered_ball_sum hw (fun _ => (1 : ℝ≥0∞)) S]
  have hA : ∀ s : ℕ, (∑ t ∈ Finset.Icc (-(s : ℤ)) (s : ℤ), f t)
      ≤ (∑ _t ∈ Finset.Icc (-(s : ℤ)) (s : ℤ), (1 : ℝ≥0∞)) * M := by
    intro s
    rw [sum_one_Icc_neg_symm s]
    exact hf s
  rw [layered_ball_sum hw f S, hone]
  calc (∑ s ∈ Finset.range (S + 1),
          (w s - w (s + 1)) * (∑ t ∈ Finset.Icc (-(s : ℤ)) (s : ℤ), f t))
        + w (S + 1) * (∑ t ∈ Finset.Icc (-(S : ℤ)) (S : ℤ), f t)
      ≤ (∑ s ∈ Finset.range (S + 1),
          (w s - w (s + 1))
            * ((∑ _t ∈ Finset.Icc (-(s : ℤ)) (s : ℤ), (1 : ℝ≥0∞)) * M))
        + w (S + 1) * ((∑ _t ∈ Finset.Icc (-(S : ℤ)) (S : ℤ), (1 : ℝ≥0∞)) * M) := by
        apply add_le_add
        · exact Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left (hA s) (by simp))
        · exact mul_le_mul_of_nonneg_left (hA S) (by simp)
    _ = (∑ s ∈ Finset.range (S + 1),
          (w s - w (s + 1)) * (∑ _t ∈ Finset.Icc (-(s : ℤ)) (s : ℤ), (1 : ℝ≥0∞))) * M
        + w (S + 1) * (∑ _t ∈ Finset.Icc (-(S : ℤ)) (S : ℤ), (1 : ℝ≥0∞)) * M := by
        congr 1
        · rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro s _
          rw [mul_assoc]
        · rw [mul_assoc]
    _ = ((∑ s ∈ Finset.range (S + 1),
          (w s - w (s + 1)) * (∑ _t ∈ Finset.Icc (-(s : ℤ)) (s : ℤ), (1 : ℝ≥0∞)))
        + w (S + 1) * (∑ _t ∈ Finset.Icc (-(S : ℤ)) (S : ℤ), (1 : ℝ≥0∞))) * M := by
        rw [add_mul]

/-- **Convolution with a radially decreasing probability kernel is dominated by the discrete
Hardy--Littlewood maximal function.** -/
theorem radial_kernel_tsum_le_maximal (w : ℕ → ℝ≥0∞) (hw : Antitone w) (g : ℤ → ℂ) (n : ℤ) :
    ∑' t : ℤ, w t.natAbs * ‖g (n - t)‖ₑ
      ≤ (∑' t : ℤ, w t.natAbs) *
        (⨆ (p : {p : ℤ × ℤ // p.1 ≤ n ∧ n ≤ p.2}),
          ((p.1.2 - p.1.1 + 1).toNat : ℝ≥0∞)⁻¹ * ∑ k ∈ Finset.Icc p.1.1 p.1.2, ‖g k‖ₑ) := by
  set M : ℝ≥0∞ := ⨆ (p : {p : ℤ × ℤ // p.1 ≤ n ∧ n ≤ p.2}),
      ((p.1.2 - p.1.1 + 1).toNat : ℝ≥0∞)⁻¹ * ∑ k ∈ Finset.Icc p.1.1 p.1.2, ‖g k‖ₑ
    with hM
  have hsum_le : ∀ a b : ℤ, a ≤ n → n ≤ b →
      ∑ k ∈ Finset.Icc a b, ‖g k‖ₑ ≤ ((b - a + 1).toNat : ℝ≥0∞) * M := by
    intro a b ha hb
    have hle : ((b - a + 1).toNat : ℝ≥0∞)⁻¹ * ∑ k ∈ Finset.Icc a b, ‖g k‖ₑ ≤ M := by
      rw [hM]
      exact le_iSup
        (fun p : {p : ℤ × ℤ // p.1 ≤ n ∧ n ≤ p.2} =>
          ((p.1.2 - p.1.1 + 1).toNat : ℝ≥0∞)⁻¹ * ∑ k ∈ Finset.Icc p.1.1 p.1.2, ‖g k‖ₑ)
        ⟨(a, b), ⟨ha, hb⟩⟩
    have ht0 : ((b - a + 1).toNat : ℝ≥0∞) ≠ 0 := by
      rw [Nat.cast_ne_zero]
      have hge : (0 : ℤ) ≤ b - a + 1 := by omega
      have hto : (((b - a + 1).toNat : ℕ) : ℤ) = b - a + 1 := Int.toNat_of_nonneg hge
      omega
    have httop : ((b - a + 1).toNat : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
    have hmul : ((b - a + 1).toNat : ℝ≥0∞)
        * (((b - a + 1).toNat : ℝ≥0∞)⁻¹ * ∑ k ∈ Finset.Icc a b, ‖g k‖ₑ)
        = ∑ k ∈ Finset.Icc a b, ‖g k‖ₑ := by
      rw [← mul_assoc, ENNReal.mul_inv_cancel ht0 httop, one_mul]
    calc ∑ k ∈ Finset.Icc a b, ‖g k‖ₑ
        = ((b - a + 1).toNat : ℝ≥0∞)
            * (((b - a + 1).toNat : ℝ≥0∞)⁻¹ * ∑ k ∈ Finset.Icc a b, ‖g k‖ₑ) :=
          hmul.symm
      _ ≤ ((b - a + 1).toNat : ℝ≥0∞) * M :=
          mul_le_mul_of_nonneg_left hle (by simp)
  have hball : ∀ s : ℕ,
      ∑ t ∈ Finset.Icc (-(s : ℤ)) (s : ℤ), ‖g (n - t)‖ₑ
        ≤ ((2 * s + 1 : ℕ) : ℝ≥0∞) * M := by
    intro s
    rw [sum_Icc_neg_symm_shift (fun k => ‖g k‖ₑ) n s]
    have h := hsum_le (n - (s : ℤ)) (n + (s : ℤ)) (by omega) (by omega)
    have h2 : (n + (s : ℤ) - (n - (s : ℤ)) + 1).toNat = 2 * s + 1 := by
      have hcast : n + (s : ℤ) - (n - (s : ℤ)) + 1 = ((2 * s + 1 : ℕ) : ℤ) := by
        push_cast; ring
      rw [hcast, Int.toNat_natCast]
    rwa [h2] at h
  have hmain : ∀ S : ℕ,
      ∑ t ∈ Finset.Icc (-(S : ℤ)) (S : ℤ), w t.natAbs * ‖g (n - t)‖ₑ
        ≤ (∑' t : ℤ, w t.natAbs) * M := by
    intro S
    refine (radial_ball_sum_le_aux hw hball S).trans ?_
    exact mul_le_mul_left
      (ENNReal.sum_le_tsum (s := Finset.Icc (-(S : ℤ)) (S : ℤ))
        (f := fun t : ℤ => w t.natAbs)) M
  have hfin : ∑' t : ℤ, w t.natAbs * ‖g (n - t)‖ₑ ≤ (∑' t : ℤ, w t.natAbs) * M := by
    rw [ENNReal.tsum_eq_iSup_sum]
    refine iSup_le (fun s => ?_)
    let S' : ℕ := s.sup (fun t : ℤ => t.natAbs)
    have hsub : s ⊆ Finset.Icc (-(S' : ℤ)) (S' : ℤ) := by
      intro t ht
      have h1 : t.natAbs ≤ S' := Finset.le_sup ht
      exact Finset.mem_Icc.mpr ((natAbs_le_iff_int t S').mp h1)
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by simp)).trans
      (hmain S')
  exact hfin

end Commons.Analysis.Hilbert