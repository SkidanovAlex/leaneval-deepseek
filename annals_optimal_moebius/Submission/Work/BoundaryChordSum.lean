import Submission.Work.BendArcFacts

open OptimalMoebius Topology ContDiff
open scoped BigOperators Matrix Topology Metric
set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# The boundary chord-sum bound (elementary, needed for the Lemma-G apex)

For a straight pre-bend chord `[P, Q]` of the band with preimage endpoints
`(0,α)` and `(1,β)` (`α ≤ β`) and ANY boundary point `f (1,s)`:

    ‖f (1,s) − P‖ + ‖f (1,s) − Q‖ ≤ a + (β − α).

Modulo the `2a`-periodicity of `s ↦ f (1,s)` one may assume
`s ∈ [α − a, α + a)`; then for `s ∈ [α−a, β]` use the representative
`f (0,α) = f (1, α−a)` (chords `≤ s−α+a` and `≤ β−s`), and for
`s ∈ [β, α+a)` use `f (0,α) = f (1, α+a)` (chords `≤ α+a−s` and `≤ s−β`).

This is exactly the input that lets the apex of the Figure-2 triangle be
ANY boundary point (`LemmaG4.relation4_of_points`).

Build: `lake build Submission.Work.BoundaryChordSum` (rc=0 target).
-/

noncomputable section
namespace Submission

open Submission.PaperBand

/-- The right-edge image is `2a`-periodic: `f (1, s + 2a) = f (1, s)`. -/
lemma rightEdge_period_two {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) (s : ℝ) :
    f !₂[1, s + 2 * a] = f !₂[1, s] := by
  have h := hf.periodic (!₂[0, s + a] : ℝ²) (leftEdge_mem_unitStrip (s + a))
  rw [period_leftEdge] at h
  have harg : s + a + a = s + 2 * a := by ring
  rw [harg] at h
  have h2 : f !₂[0, s + a] = f !₂[1, s] := by
    have hh := (f_leftEdge_eq_rightEdge_minus hf (s + a)).symm
    have harg2 : s + a - a = s := by ring
    rwa [harg2] at hh
  exact h.trans h2

/-- **The boundary chord-sum bound.** -/
theorem boundary_chord_sum_le {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {α β s : ℝ} (hαβ : α ≤ β) :
    ‖f !₂[1, s] - f !₂[0, α]‖ + ‖f !₂[1, s] - f !₂[1, β]‖ ≤ a + (β - α) := by
  have h2a : (0 : ℝ) < 2 * a := by linarith
  obtain ⟨k, hk1, hk2⟩ : ∃ k : ℤ, α - a ≤ s - k • (2 * a) ∧ s - k • (2 * a) < α + a := by
    refine ⟨⌊(s - α + a) / (2 * a)⌋, ?_, ?_⟩
    · have hsmul : (⌊(s - α + a) / (2 * a)⌋ : ℤ) • (2 * a)
          = (⌊(s - α + a) / (2 * a)⌋ : ℝ) * (2 * a) := zsmul_eq_mul _ _
      rw [hsmul]
      have hle : ((⌊(s - α + a) / (2 * a)⌋ : ℤ) : ℝ) ≤ (s - α + a) / (2 * a) := Int.floor_le _
      have h := mul_le_mul_of_nonneg_right hle (le_of_lt h2a)
      rw [div_mul_cancel₀ _ (ne_of_gt h2a)] at h
      linarith
    · have hsmul : (⌊(s - α + a) / (2 * a)⌋ : ℤ) • (2 * a)
          = (⌊(s - α + a) / (2 * a)⌋ : ℝ) * (2 * a) := zsmul_eq_mul _ _
      rw [hsmul]
      have hlt : (s - α + a) / (2 * a) < ((⌊(s - α + a) / (2 * a)⌋ : ℤ) : ℝ) + 1 :=
        Int.lt_floor_add_one _
      have h := mul_lt_mul_of_pos_right hlt h2a
      rw [div_mul_cancel₀ _ (ne_of_gt h2a), add_mul, one_mul] at h
      linarith
  set t : ℝ := s - k • (2 * a) with htdef
  have htwin : α - a ≤ t ∧ t < α + a := ⟨hk1, hk2⟩
  have hper : Function.Periodic (fun u : ℝ => f !₂[1, u]) (2 * a) :=
    fun u => rightEdge_period_two hf u
  have hfs : f !₂[1, s] = f !₂[1, t] := by
    have h := hper.sub_zsmul_eq (x := s) k
    rw [htdef]
    exact h.symm
  rw [hfs]
  have hP1 : f !₂[1, α - a] = f !₂[0, α] := f_leftEdge_eq_rightEdge_minus hf α
  have hP2 : f !₂[1, α + a] = f !₂[0, α] := f_leftEdge_eq_rightEdge_plus hf α
  by_cases htβ : t ≤ β
  · have h1 : ‖f !₂[1, t] - f !₂[0, α]‖ ≤ t - (α - a) := by
      rw [← hP1]
      have hL := embedding_lipschitz hf (rightEdge_mem_unitStrip t)
        (rightEdge_mem_unitStrip (α - a))
      calc ‖f !₂[1, t] - f !₂[1, α - a]‖ ≤ ‖(!₂[1, α - a] : ℝ²) - !₂[1, t]‖ := by
            simpa [norm_sub_rev] using hL
        _ = |(α - a) - t| := dist_rightEdge (α - a) t
        _ = t - (α - a) := by rw [abs_of_nonpos (by linarith [htwin.1])]; ring
    have h2 : ‖f !₂[1, t] - f !₂[1, β]‖ ≤ β - t := by
      have hL := embedding_lipschitz hf (rightEdge_mem_unitStrip t)
        (rightEdge_mem_unitStrip β)
      calc ‖f !₂[1, t] - f !₂[1, β]‖ ≤ ‖(!₂[1, β] : ℝ²) - !₂[1, t]‖ := by
            simpa [norm_sub_rev] using hL
        _ = |β - t| := dist_rightEdge β t
        _ = β - t := by rw [abs_of_nonneg (by linarith)]
    linarith
  · have hβt : β < t := lt_of_not_ge htβ
    have h1 : ‖f !₂[1, t] - f !₂[0, α]‖ ≤ (α + a) - t := by
      rw [← hP2]
      have hL := embedding_lipschitz hf (rightEdge_mem_unitStrip t)
        (rightEdge_mem_unitStrip (α + a))
      calc ‖f !₂[1, t] - f !₂[1, α + a]‖ ≤ ‖(!₂[1, α + a] : ℝ²) - !₂[1, t]‖ := by
            simpa [norm_sub_rev] using hL
        _ = |(α + a) - t| := dist_rightEdge (α + a) t
        _ = (α + a) - t := by rw [abs_of_nonneg (by linarith [htwin.2])]
    have h2 : ‖f !₂[1, t] - f !₂[1, β]‖ ≤ t - β := by
      have hL := embedding_lipschitz hf (rightEdge_mem_unitStrip t)
        (rightEdge_mem_unitStrip β)
      calc ‖f !₂[1, t] - f !₂[1, β]‖ ≤ ‖(!₂[1, β] : ℝ²) - !₂[1, t]‖ := by
            simpa [norm_sub_rev] using hL
        _ = |β - t| := dist_rightEdge β t
        _ = t - β := by rw [abs_of_nonpos (by linarith)]; ring
    linarith


/-- **The boundary chord-sum bound, sign-free form**:
`‖f(1,s) − f(0,α)‖ + ‖f(1,s) − f(1,β)‖ ≤ a + |β − α|` for every `s`. -/
theorem boundary_chord_sum_le_abs {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) (α β s : ℝ) :
    ‖f !₂[1, s] - f !₂[0, α]‖ + ‖f !₂[1, s] - f !₂[1, β]‖ ≤ a + |β - α| := by
  by_cases hαβ : α ≤ β
  · have h := boundary_chord_sum_le hf ha (α := α) (β := β) (s := s) hαβ
    have hle : (a : ℝ) + (β - α) ≤ a + |β - α| := by linarith [le_abs_self (β - α)]
    linarith
  · have hβα : β ≤ α := le_of_lt (lt_of_not_ge hαβ)
    have h := boundary_chord_sum_le hf ha (α := β - a) (β := α - a) (s := s) (by linarith)
    have hw : ((α - a) - (β - a) : ℝ) = α - β := by ring
    rw [hw] at h
    have e1 : f !₂[0, β - a] = f !₂[1, β] := by
      have h1 := (f_leftEdge_eq_rightEdge_minus hf (β - a)).symm
      have h2 := (rightEdge_period_two hf (β - 2 * a)).symm
      have h2' : f !₂[1, β - 2 * a] = f !₂[1, β] := by
        have h3 : β - 2 * a + 2 * a = β := by ring
        rwa [h3] at h2
      calc f !₂[0, β - a] = f !₂[1, (β - a) - a] := h1
        _ = f !₂[1, β - 2 * a] := by congr 1; ring
        _ = f !₂[1, β] := h2'
    have e2 : f !₂[1, α - a] = f !₂[0, α] := f_leftEdge_eq_rightEdge_minus hf α
    rw [e1, e2] at h
    have hle : (a : ℝ) + (α - β) ≤ a + |β - α| := by
      have := neg_le_abs (β - α); linarith
    linarith

end Submission
