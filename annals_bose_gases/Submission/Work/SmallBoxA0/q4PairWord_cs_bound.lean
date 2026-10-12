import ChallengeDeps
import Submission.Work.SmallBoxA0.pair_kernel_L2
import Submission.Work.SmallBoxA0.pair_slot_cs_bound
import Submission.Work.SmallBoxKinBridge
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxA0

open MeasureTheory Metric
open scoped ContDiff Topology Real BigOperators
open Submission BoseGases
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

lemma pairSet_card (N : ℕ) : (pairSet N).card = N * (N - 1) := by
  have h : pairSet N = Finset.offDiag (Finset.univ : Finset (Fin N)) := by
    ext x
    simp [pairSet, Finset.mem_offDiag]
  rw [h, Finset.offDiag_card, Finset.card_univ, Fintype.card_fin]
  have : N * N - N = N * (N - 1) := by
    rw [Nat.mul_sub_left_distrib, Nat.mul_one]
  exact this

lemma q4PairWord_cs_bound {N : ℕ} {s R : ℝ} (hs : 0 < s) (hR : 0 < R)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRs : R ≤ s * chiR0)
    (hW2 : MemLp (fun p : X 2 => wPairC s (g0 v h) (p 0) (p 1)) 2
      (volume.restrict (abox 2 s)))
    {Φ : X N → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    (hnorm : (∫ x in abox N s, (Φ x) ^ 2) = 1) :
    -((N : ℝ) * ((N : ℝ) - 1) * (s ^ 3)⁻¹ *
        Real.sqrt (∫ p in abox 2 s, (wPairC s (g0 v h) (p 0) (p 1)) ^ 2))
      ≤ q4PairWord (ℓ := s) (v := v) h (Φ := Φ) := by
  classical
  -- the kernel as a function of the pair of coordinates, and the transfer data
  obtain ⟨hw1m, hw1sq, hMeq⟩ :=
    pair_kernel_L2 (s := s) hs (W := fun y z => wPairC s (g0 v h) y z) hW2
  have hcardR : ((pairSet N).card : ℝ) = (N : ℝ) * ((N : ℝ) - 1) := by
    rw [pairSet_card]
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN; norm_num
    · rw [Nat.cast_mul, Nat.cast_sub hN, Nat.cast_one]
  rcases Nat.lt_or_ge N 2 with hN | hN
  · -- N = 0 or N = 1
    interval_cases N
    · have hempty : pairSet 0 = ∅ := by
        apply Finset.card_eq_zero.mp
        have := pairSet_card 0
        simpa using this
      simp [q4PairWord, hempty]
    · have hempty : pairSet 1 = ∅ := by
        apply Finset.card_eq_zero.mp
        have := pairSet_card 1
        simpa using this
      simp [q4PairWord, hempty]
  · -- N ≥ 2
    obtain ⟨p, rfl⟩ : ∃ p, N = p + 2 := ⟨N - 2, by omega⟩
    have hcardR' : ((pairSet (p + 2)).card : ℝ) = ((p + 2 : ℕ) : ℝ) * (((p + 2 : ℕ) : ℝ) - 1) := hcardR
    set S : Fin (p + 2) × Fin (p + 2) → ℝ := fun p0 =>
      ∫ x in abox (p + 2) s,
        (aP s p0.1 (aP s p0.2 Φ) x) * (aQ s p0.2 (aQ s p0.1 Φ) x)
          * wPairC s (g0 v h) (x p0.1) (x p0.2) with hS
    have hterm : ∀ p0 ∈ pairSet (p + 2), -((s ^ 3)⁻¹ *
        Real.sqrt (∫ q in abox 2 s, (wPairC s (g0 v h) (q 0) (q 1)) ^ 2)) ≤ S p0 := by
      intro p0 hp0
      have hpne : p0.1 ≠ p0.2 := by simpa [pairSet] using hp0
      have hAcont : Continuous (aP s p0.2 Φ) := aP_continuous hs p0.2 hΦ.continuous
      have hcs := pair_slot_cs_bound (p := p) (s := s) hs p0.1 p0.2 hpne (Φ := Φ)
        hΦ.continuous (w1 := fun q : ℝ³ × ℝ³ => wPairC s (g0 v h) q.1 q.2) hw1m hw1sq
      have hsq : Real.sqrt (∫ q in acube s ×ˢ acube s, (wPairC s (g0 v h) q.1 q.2) ^ 2)
          = Real.sqrt (∫ q in abox 2 s, (wPairC s (g0 v h) (q 0) (q 1)) ^ 2) := by
        rw [hMeq]
      rw [hsq] at hcs
      have hA : Real.sqrt (∫ x in abox (p + 2) s, (aP s p0.1 (aP s p0.2 Φ) x) ^ 2) ≤ 1 := by
        rw [Real.sqrt_le_one]
        have h1 : (∫ x in abox (p + 2) s, (aP s p0.1 (aP s p0.2 Φ) x) ^ 2)
            ≤ (∫ x in abox (p + 2) s, (aP s p0.2 Φ x) ^ 2) := aP_sq_le hs p0.1 hAcont
        have h2 : (∫ x in abox (p + 2) s, (aP s p0.2 Φ x) ^ 2)
            ≤ (∫ x in abox (p + 2) s, (Φ x) ^ 2) := aP_sq_le hs p0.2 hΦ.continuous
        linarith [h1, h2, hnorm]
      have hC : Real.sqrt (∫ x in abox (p + 2) s, (aQ s p0.2 (aQ s p0.1 Φ) x) ^ 2) ≤ 1 := by
        rw [Real.sqrt_le_one]
        have hQcont : Continuous (aQ s p0.1 Φ) := hΦ.continuous.sub (aP_continuous hs p0.1 hΦ.continuous)
        have h1 : (∫ x in abox (p + 2) s, (aQ s p0.2 (aQ s p0.1 Φ) x) ^ 2)
            ≤ (∫ x in abox (p + 2) s, (aQ s p0.1 Φ x) ^ 2) :=
          integral_aQ_sq_le hs p0.2 hQcont
        have h2 : (∫ x in abox (p + 2) s, (aQ s p0.1 Φ x) ^ 2)
            ≤ (∫ x in abox (p + 2) s, (Φ x) ^ 2) :=
          integral_aQ_sq_le hs p0.1 hΦ.continuous
        linarith [h1, h2, hnorm]
      have hbound : |∫ x in abox (p + 2) s,
            (aP s p0.1 (aP s p0.2 Φ) x) * (aQ s p0.2 (aQ s p0.1 Φ) x)
              * wPairC s (g0 v h) (x p0.1) (x p0.2)|
          ≤ (s ^ 3)⁻¹ * Real.sqrt (∫ q in abox 2 s, (wPairC s (g0 v h) (q 0) (q 1)) ^ 2) := by
        refine hcs.trans ?_
        calc (s ^ 3)⁻¹
              * Real.sqrt (∫ x in abox (p + 2) s, (aP s p0.1 (aP s p0.2 Φ) x) ^ 2)
              * Real.sqrt (∫ x in abox (p + 2) s, (aQ s p0.2 (aQ s p0.1 Φ) x) ^ 2)
              * Real.sqrt (∫ q in abox 2 s, (wPairC s (g0 v h) (q 0) (q 1)) ^ 2)
            ≤ (s ^ 3)⁻¹ * 1 * 1
              * Real.sqrt (∫ q in abox 2 s, (wPairC s (g0 v h) (q 0) (q 1)) ^ 2) := by
              gcongr
          _ = (s ^ 3)⁻¹ * Real.sqrt (∫ q in abox 2 s, (wPairC s (g0 v h) (q 0) (q 1)) ^ 2) := by
              ring
      have := (abs_le.mp hbound).1
      simpa [hS] using this
    have hsum := Finset.sum_le_sum hterm
    have hconst : (∑ p0 ∈ pairSet (p + 2), -((s ^ 3)⁻¹ *
          Real.sqrt (∫ q in abox 2 s, (wPairC s (g0 v h) (q 0) (q 1)) ^ 2)))
        = -(((pairSet (p + 2)).card : ℝ) * ((s ^ 3)⁻¹ *
            Real.sqrt (∫ q in abox 2 s, (wPairC s (g0 v h) (q 0) (q 1)) ^ 2))) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      ring
    have hq4 : q4PairWord (ℓ := s) (v := v) h (Φ := Φ) = ∑ p0 ∈ pairSet (p + 2), S p0 := by
      unfold q4PairWord
      simp only [hS]
    rw [hq4]
    calc -(((p + 2 : ℕ) : ℝ) * (((p + 2 : ℕ) : ℝ) - 1) * (s ^ 3)⁻¹
            * Real.sqrt (∫ q in abox 2 s, (wPairC s (g0 v h) (q 0) (q 1)) ^ 2))
        = -(((pairSet (p + 2)).card : ℝ) * ((s ^ 3)⁻¹ *
            Real.sqrt (∫ q in abox 2 s, (wPairC s (g0 v h) (q 0) (q 1)) ^ 2))) := by
          rw [hcardR']; ring
      _ = ∑ p0 ∈ pairSet (p + 2), -((s ^ 3)⁻¹ *
            Real.sqrt (∫ q in abox 2 s, (wPairC s (g0 v h) (q 0) (q 1)) ^ 2)) := hconst.symm
      _ ≤ ∑ p0 ∈ pairSet (p + 2), S p0 := hsum

end Work.SmallBoxA0
