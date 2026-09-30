import Submission.Work.BMF.adi_all_defs
import Submission.Work.BMF.primesIn_card_le_pi0
import Submission.Work.BMF.fam_card_le
import Submission.Work.BMF.tuple_setup

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# N5 `adi_cycles`: elementary counting lemmas

The double counting of the edge prime sets over `q ∈ [P₂/2, P₂]`, the Chebyshev bound for the
number of those primes, and the size of the family.
-/

namespace Work.BMF

open Polynomial Finset Real

variable {k : ℕ} {f : ℕ → ℂ} {c C X L P₁ P₂ : ℝ}

/-- **Double counting.**  Summing the prime sets of the edges of `D` over all primes of
`[P₂/2, P₂]` counts every prime of every edge once, hence is at least
`c π₀(P₂) · #(edges)`. -/
theorem edgeS_sum_le (D : QuadData k f c C X L P₁ P₂) (hP₂ : 0 < P₂) :
    c * pi0 P₂ * (D.edges.card : ℝ) ≤
      ∑ q ∈ primesIn (P₂ / 2) P₂,
        ((D.edges.filter (fun e => q ∈ edgeS D e)).card : ℝ) := by
  classical
  have hsub : ∀ e ∈ D.edges, edgeS D e ⊆ primesIn (P₂ / 2) P₂ := by
    intro e he p hp
    have h := edgeS_subset D he hp
    rw [mem_primesIn_iff hP₂.le]
    exact ⟨h.1, h.2.1, h.2.2⟩
  have hone : ∀ e : Edge,
      (∑ q ∈ primesIn (P₂ / 2) P₂, (if q ∈ edgeS D e then (1 : ℝ) else 0))
        = ((edgeS D e).card : ℝ) := by
    intro e
    have key : (∑ q ∈ primesIn (P₂ / 2) P₂, (if q ∈ edgeS D e then (1 : ℝ) else 0))
        = (((primesIn (P₂ / 2) P₂).filter (fun q => q ∈ edgeS D e)).card : ℝ) := by
      rw [Finset.card_filter, Nat.cast_sum]
      exact Finset.sum_congr rfl (fun q _ => by by_cases h : q ∈ edgeS D e <;> simp [h])
    rw [key]
    by_cases he : e ∈ D.edges
    · rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr (hsub e he)]
    · have hempty : edgeS D e = ∅ := by simp [edgeS, he]
      rw [hempty]
      simp
  have htwo : ∀ q : ℕ, ((D.edges.filter (fun e => q ∈ edgeS D e)).card : ℝ)
      = ∑ e ∈ D.edges, (if q ∈ edgeS D e then (1 : ℝ) else 0) := by
    intro q
    rw [Finset.card_filter, Nat.cast_sum]
    exact Finset.sum_congr rfl (fun e _ => by by_cases h : q ∈ edgeS D e <;> simp [h])
  calc c * pi0 P₂ * (D.edges.card : ℝ)
      = ∑ _e ∈ D.edges, c * pi0 P₂ := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ ∑ e ∈ D.edges, ((edgeS D e).card : ℝ) :=
        Finset.sum_le_sum (fun e he => edgeS_card D he)
    _ = ∑ e ∈ D.edges, ∑ q ∈ primesIn (P₂ / 2) P₂,
          (if q ∈ edgeS D e then (1 : ℝ) else 0) :=
        Finset.sum_congr rfl (fun e _ => (hone e).symm)
    _ = ∑ q ∈ primesIn (P₂ / 2) P₂, ∑ e ∈ D.edges,
          (if q ∈ edgeS D e then (1 : ℝ) else 0) := Finset.sum_comm
    _ = ∑ q ∈ primesIn (P₂ / 2) P₂,
          ((D.edges.filter (fun e => q ∈ edgeS D e)).card : ℝ) :=
        Finset.sum_congr rfl (fun q _ => (htwo q).symm)

/-- Chebyshev bound for the number of primes in `[P/2, P]`. -/
theorem primesIn_half_card_le : ∃ C P₀ : ℝ, 0 < C ∧ ∀ P : ℝ, P₀ ≤ P →
    ((primesIn (P / 2) P).card : ℝ) ≤ C * pi0 P := by
  obtain ⟨C₀, Q₀, hC₀, hbound⟩ := primesIn_card_le_pi0
  refine ⟨8 * C₀, max (2 * Q₀) 16, by positivity, ?_⟩
  intro P hP
  have hQ₀ : Q₀ ≤ P / 2 := by
    have h2 : 2 * Q₀ ≤ P := le_trans (le_max_left _ _) hP
    linarith
  have hPpos : 0 < P := by
    have h2 : (16 : ℝ) ≤ max (2 * Q₀) 16 := le_max_right _ _
    linarith
  have hP8 : 8 ≤ P := by
    have h2 : (16 : ℝ) ≤ max (2 * Q₀) 16 := le_max_right _ _
    linarith
  have hb := hbound (P / 2) hQ₀
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogP : 0 < Real.log P := Real.log_pos (by linarith)
  have hloghalf : 0 < Real.log (P / 2) := Real.log_pos (by linarith)
  have hlog4 : Real.log 4 ≤ Real.log (P / 2) := Real.log_le_log (by norm_num) (by linarith)
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    have h := Real.log_mul (x := (2:ℝ)) (y := (2:ℝ)) (by norm_num) (by norm_num)
    rw [show (2:ℝ) * 2 = 4 by norm_num] at h
    linarith
  have hlog_le : Real.log P ≤ 16 * Real.log (P / 2) := by
    have hsplit : Real.log P = Real.log 2 + Real.log (P / 2) := by
      have h := Real.log_mul (x := (2:ℝ)) (y := P / 2) (by norm_num) (by linarith)
      rwa [show (2:ℝ) * (P / 2) = P by ring] at h
    have h15 : Real.log 2 ≤ 15 * Real.log (P / 2) := by
      have h1 : 2 * Real.log 2 ≤ Real.log (P / 2) := by rw [← h4]; exact hlog4
      linarith
    linarith
  have htail : pi0 (P / 2) ≤ 8 * pi0 P := by
    unfold pi0
    rw [div_le_iff₀ hloghalf]
    have h9 : 8 * (P / Real.log P) * Real.log (P / 2)
        = 8 * P * Real.log (P / 2) / Real.log P := by
      field_simp
    rw [h9, le_div_iff₀ hlogP]
    have h1 : P / 2 * Real.log P ≤ P / 2 * (16 * Real.log (P / 2)) :=
      mul_le_mul_of_nonneg_left hlog_le (by linarith)
    linarith
  have h2 : 2 * (P / 2) = P := by ring
  rw [h2] at hb
  calc ((primesIn (P / 2) P).card : ℝ) ≤ C₀ * pi0 (P / 2) := hb
    _ ≤ C₀ * (8 * pi0 P) := mul_le_mul_of_nonneg_left htail hC₀.le
    _ = 8 * C₀ * pi0 P := by ring

/-- The number of vertices of the quadruple graph is at most `10X/(500L) + 1`. -/
theorem fam_card_le_N (D : QuadData k f c C X L P₁ P₂) (hX : 0 < X) (hL : 0 < L) :
    ((D.fam.card : ℝ)) ≤ 10 * X / (500 * L) + 1 :=
  fam_card_le X L hX hL D.fam D.isFam

end Work.BMF
