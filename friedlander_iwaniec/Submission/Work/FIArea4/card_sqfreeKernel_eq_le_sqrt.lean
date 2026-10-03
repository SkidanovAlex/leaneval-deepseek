import Mathlib
import Submission.Work.FIArea4.SqfreeKernel
import Submission.Work.FIArea4.sqfree_kernel

namespace Work.FIArea4

/-- For `d ≥ 1` and any `N`, the number of `r ∈ [1, N]` with squarefree kernel `d` is at most
`√(N / d)`.  Proof: for such an `r` one has `r = d * (sqPart r) ^ 2` with `sqPart r ≥ 1` and
`d * (sqPart r) ^ 2 ≤ N`, so `sqPart r ≤ ⌊√(N/d)⌋`; the map `r ↦ sqPart r` is injective on this set
because `d ≥ 1`, so the count is at most `⌊√(N/d)⌋ ≤ √(N/d)`. -/
theorem card_sqfreeKernel_eq_le_sqrt (N d : ℕ) (hd : 1 ≤ d) :
    (((Finset.Icc 1 N).filter (fun r => Work.FIArea4.sqfreeKernel r = d)).card : ℝ)
      ≤ Real.sqrt ((N : ℝ) / (d : ℝ)) := by
  -- The `r ∈ [1,N]` with `sqfreeKernel r = d` map injectively, via `r ↦ sqPart r`, into the
  -- range `1 ≤ m ≤ ⌊√(N/d)⌋` of possible values of `sqPart r`.
  set S := (Finset.Icc 1 N).filter (fun r => Work.FIArea4.sqfreeKernel r = d) with hS
  set T := Finset.Icc 1 (Nat.sqrt (N / d)) with hT
  have hd0 : 0 < d := hd
  -- `sqPart` sends `S` into `T`.
  have hmap : Set.MapsTo Work.FIArea4.sqPart ↑S ↑T := by
    intro r hr
    rw [hS] at hr
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_coe] at hr
    obtain ⟨⟨hr1, hrN⟩, hrd⟩ := hr
    obtain ⟨hP, hmax, hsq, hdvd, hsf⟩ := Work.FIArea4.sqfree_kernel r (by omega)
    -- `d * (sqPart r)^2 = r ≤ N`.
    have hr_eq : d * Work.FIArea4.sqPart r ^ 2 = r := by
      rw [← hrd]; exact hsq
    -- hence `(sqPart r)^2 ≤ N / d`.
    have hm2le : Work.FIArea4.sqPart r ^ 2 ≤ N / d := by
      rw [Nat.le_div_iff_mul_le hd0]
      calc Work.FIArea4.sqPart r ^ 2 * d = d * Work.FIArea4.sqPart r ^ 2 := by ring
        _ = r := hr_eq
        _ ≤ N := hrN
    have hone : 1 ≤ Work.FIArea4.sqPart r := by
      have := hmax 1 (by simp)
      exact this
    rw [hT]
    simp only [Finset.mem_Icc, Finset.mem_coe]
    refine ⟨hone, ?_⟩
    rw [Nat.le_sqrt]
    simpa [pow_two] using hm2le
  -- `sqPart` is injective on `S` since `r = d * (sqPart r)^2`.
  have hinj : Set.InjOn Work.FIArea4.sqPart ↑S := by
    intro r1 hr1 r2 hr2 h
    rw [hS] at hr1 hr2
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_coe] at hr1 hr2
    obtain ⟨⟨hr1a, hr1b⟩, hd1⟩ := hr1
    obtain ⟨⟨hr2a, hr2b⟩, hd2⟩ := hr2
    have h1 : d * Work.FIArea4.sqPart r1 ^ 2 = r1 := by
      rw [← hd1]; exact (Work.FIArea4.sqfree_kernel r1 (by omega)).2.2.1
    have h2 : d * Work.FIArea4.sqPart r2 ^ 2 = r2 := by
      rw [← hd2]; exact (Work.FIArea4.sqfree_kernel r2 (by omega)).2.2.1
    rw [← h1, ← h2, h]
  have hcard : S.card ≤ T.card := Finset.card_le_card_of_injOn _ hmap hinj
  have hTcard : T.card = Nat.sqrt (N / d) := by
    rw [hT, Nat.card_Icc]
    omega
  -- `⌊√(N/d)⌋ ≤ √(N/d)`.
  have hstep : (Nat.sqrt (N / d) : ℝ) ≤ Real.sqrt ((N : ℝ) / (d : ℝ)) := by
    have h1 : (Nat.sqrt (N / d) : ℝ) ≤ Real.sqrt ((N / d : ℕ) : ℝ) := by
      rw [Real.le_sqrt (by positivity) (by positivity)]
      exact_mod_cast Nat.sqrt_le' (N / d)
    have h2 : Real.sqrt ((N / d : ℕ) : ℝ) ≤ Real.sqrt ((N : ℝ) / (d : ℝ)) :=
      Real.sqrt_le_sqrt Nat.cast_div_le
    linarith
  have hfin : ((S.card : ℕ) : ℝ) ≤ Real.sqrt ((N : ℝ) / (d : ℝ)) := by
    have h' : (S.card : ℝ) ≤ (T.card : ℝ) := by exact_mod_cast hcard
    rw [hTcard] at h'
    linarith
  simpa [hS] using hfin

end Work.FIArea4
