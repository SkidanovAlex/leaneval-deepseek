import Mathlib
import Submission.Work.KMTAreas.A4.sivEvalBd

namespace Work.KMTAreas.A4

/-- **The support of the local dual function.**  The local dual function of the `i`-th block is
supported in the window `Ω_i = [α_i, β_i]`: a non-zero value of
`Ã*_N(h · 1_{Ω_i}, g · 1_{B_i})` at `x` forces a nonzero summand, whose `g`-factor then gives
`x + P(n) - n ∈ B_i`, and `|P(n) - n| ≤ winBd P N` for `0 < n ≤ N` gives `x ∈ Ω_i`. -/
theorem blkDual_support (P : Polynomial ℤ) (hP : 1 ≤ P.natDegree) {N : ℕ} (hN : 1 ≤ N) :
    ∀ (h g : ℤ → ℂ) (i x : ℤ), blkDual P N h g i x ≠ 0 →
      blkAlpha P N i ≤ x ∧ x ≤ blkBeta P N i := by
  intro h g i x hx
  rw [blkDual, Work.Analysis.InverseTheory.AhalfTranspose] at hx
  have hsum : ∑ n ∈ Finset.Ioc (N / 2) N,
      winPiece P N h i (x - (n : ℤ)) * blkPiece P N g i (x + P.eval (n : ℤ) - (n : ℤ)) ≠ 0 := by
    intro h0
    exact hx (by rw [h0, mul_zero])
  obtain ⟨n, hn, hterm⟩ : ∃ n ∈ Finset.Ioc (N / 2) N,
      winPiece P N h i (x - (n : ℤ)) * blkPiece P N g i (x + P.eval (n : ℤ) - (n : ℤ)) ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hsum (Finset.sum_eq_zero fun n hn => hc n hn)
  have hpiece : blkPiece P N g i (x + P.eval (n : ℤ) - (n : ℤ)) ≠ 0 :=
    fun h0 => hterm (by rw [h0, mul_zero])
  obtain ⟨hs1, hs2⟩ := blkPiece_support hpiece
  have hnpos : 0 < n := by have := (Finset.mem_Ioc.mp hn).1; omega
  have hn1 : (0 : ℤ) < (n : ℤ) := by exact_mod_cast hnpos
  have hn2 : (n : ℤ) ≤ (N : ℤ) := by exact_mod_cast (Finset.mem_Ioc.mp hn).2
  have hbd := abs_le.mp (eval_sub_self_abs_le_winBd (P := P) hP hN hn1 hn2)
  constructor
  · rw [blkAlpha]
    linarith [hs1, hbd.2]
  · rw [blkBeta]
    linarith [hs2, hbd.1]

/-- **The window piece of `h` is invisible to the local dual function.**  Only the values of `h` on
the window `Ω_i` matter for the `i`-th local dual function: `winPiece P N h i` and `h` give the same
dual function of the `i`-th block piece.  Indeed, a nonzero summand forces
`x - n = (x + P(n) - n) - P(n)` with `x + P(n) - n ∈ [iL, (i+1)L)` and `|P.eval n| ≤ winBd P N`, so
`x - n ∈ Ω_i`. -/
theorem blkDual_eq_ahalfTranspose (P : Polynomial ℤ) {N : ℕ} (hN : 1 ≤ N) :
    ∀ (h g : ℤ → ℂ) (i : ℤ),
      blkDual P N h g i = Work.Analysis.InverseTheory.AhalfTranspose N P h (blkPiece P N g i) := by
  intro h g i
  funext x
  simp only [blkDual, Work.Analysis.InverseTheory.AhalfTranspose]
  congr 1
  refine Finset.sum_congr rfl fun n hn => ?_
  by_cases hz : blkPiece P N g i (x + P.eval (n : ℤ) - (n : ℤ)) = 0
  · rw [hz, mul_zero, mul_zero]
  · have hnpos : 0 < n := by have := (Finset.mem_Ioc.mp hn).1; omega
    have hn1 : (0 : ℤ) < (n : ℤ) := by exact_mod_cast hnpos
    have hn2 : (n : ℤ) ≤ (N : ℤ) := by exact_mod_cast (Finset.mem_Ioc.mp hn).2
    obtain ⟨hs1, hs2⟩ := blkPiece_support hz
    have hb := abs_le.mp (eval_abs_le_winBd (P := P) hN hn1 hn2)
    have hmem : blkAlpha P N i ≤ x - (n : ℤ) ∧ x - (n : ℤ) ≤ blkBeta P N i := by
      rw [blkAlpha, blkBeta]
      constructor <;> linarith [hs1, hs2, hb.1, hb.2]
    rw [winPiece, if_pos hmem]

theorem sivBlocksGeom (P : Polynomial ℤ) (hP : 1 ≤ P.natDegree) (N : ℕ) (hN : 1 ≤ N) : (∀ n : ℤ, 0 < n → n ≤ (N : ℤ) → |P.eval n - n| ≤ (Work.KMTAreas.A4.winBd P N : ℤ)) ∧ (∀ n : ℤ, 0 < n → n ≤ (N : ℤ) → |P.eval n| ≤ (Work.KMTAreas.A4.winBd P N : ℤ)) ∧ (0 < Work.KMTAreas.A4.blkLen P N) ∧ (∀ (g : ℤ → ℂ) (i x : ℤ), Work.KMTAreas.A4.blkPiece P N g i x ≠ 0 → i * (Work.KMTAreas.A4.blkLen P N : ℤ) ≤ x ∧ x < (i + 1) * (Work.KMTAreas.A4.blkLen P N : ℤ)) ∧ (∀ i j : ℤ, i + 2 ≤ j → (j - i) * ((N : ℤ) ^ P.natDegree) ≤ Work.KMTAreas.A4.blkAlpha P N j - Work.KMTAreas.A4.blkBeta P N i) ∧ (∀ (h g : ℤ → ℂ) (i x : ℤ), Work.KMTAreas.A4.blkDual P N h g i x ≠ 0 → Work.KMTAreas.A4.blkAlpha P N i ≤ x ∧ x ≤ Work.KMTAreas.A4.blkBeta P N i) ∧ (∀ (h g : ℤ → ℂ) (i : ℤ), Work.KMTAreas.A4.blkDual P N h g i = Work.Analysis.InverseTheory.AhalfTranspose N P h (Work.KMTAreas.A4.blkPiece P N g i)) := by
  refine ⟨fun n hn1 hn2 => eval_sub_self_abs_le_winBd (P := P) hP hN hn1 hn2,
    fun n hn1 hn2 => eval_abs_le_winBd (P := P) hN hn1 hn2,
    blkLen_pos P hN,
    fun g i x hx => blkPiece_support hx,
    fun i j hij => blkAlpha_beta_gap P N i j hij,
    fun h g i x hx => blkDual_support P hP hN h g i x hx,
    fun h g i => blkDual_eq_ahalfTranspose P hN h g i⟩

end Work.KMTAreas.A4
