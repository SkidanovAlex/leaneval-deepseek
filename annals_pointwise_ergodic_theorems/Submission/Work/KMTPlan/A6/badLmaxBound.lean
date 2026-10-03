/-
# The non-Farey regime of area A6 has bounded height

`Work.KMTPlan.A6.MdlSliceBadPart` (the "bad scales" of the frozen-`t` slice) needs the elementary
arithmetic fact that the *complement* of the quantitative Shannon / Farey-gap hypothesis

  `goodScale (arithQ ρ (max l₁ l₂)) (lcL l₁ l₂ k₁ k₂) N`,  i.e.  `8·Q·2^{L+1} ≤ N`,
  `Q = arithQ ρ (max l₁ l₂)`, `L = lcL l₁ l₂ k₁ k₂ = max(max l₁ l₂)(max k₁ k₂)`,

contains only *boundedly many* values of `L`: if a scale `N` lies in the admissible range
`splitCut ρ L < N` but fails the Farey gap, then `L ≤ B(ρ)`.

This is the analogue of `Work.KMTAreas.A7.lmax_le_of_not_farey`, with the arithmetic denominator
taken at `max l₁ l₂` and the exponent `L + 1` (the form in which `goodScale` is stated in area A6).
The proof is the same: `arithQ ρ l ≤ 2^{C·2^l}` (`arithQ_le_rpow`), so a bad scale satisfies
`splitCut ρ L < N < 8·arithQ ρ (max l₁ l₂)·2^{L+1} ≤ 16·2^L·2^{C·2^L} ≤ 8·2^L·2^{(C+1)·2^L}`,
which contradicts the eventual domination `splitCut_dominates` for `L` large.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.MdlAdelicDefs
import Submission.Work.KMTAreas.A7.lmax_le_of_not_farey

namespace Work.KMTPlan.A6

/-- **Arithmetic core of the bound.**  If `arithQ ρ l ≤ 2^{C·2^l}` for every `l` and `l ≤ L`, then
the Farey-gap scale `8·arithQ ρ l·2^{L+1}` is dominated by `8·2^L·2^{(C+1)·2^L}`, the quantity that
`splitCut_dominates` bounds by `splitCut ρ L`.  (The `+1` in the exponent of the base `2` costs the
replacement of `C` by `C + 1`.) -/
lemma eight_arithQ_le (ρ : ℝ) (C : ℝ) (hC : 0 < C)
    (hCq : ∀ l : ℕ, (Work.KMTAreas.A7.arithQ ρ l : ℝ) ≤ (2 : ℝ) ^ (C * (2 : ℝ) ^ l))
    {l L : ℕ} (hl : l ≤ L) :
    8 * (Work.KMTAreas.A7.arithQ ρ l : ℝ) * (2 : ℝ) ^ (L + 1)
      ≤ 8 * (2 : ℝ) ^ L * (2 : ℝ) ^ ((C + 1) * (2 : ℝ) ^ L) := by
  have hlR : (l : ℝ) ≤ (L : ℝ) := by exact_mod_cast hl
  have hpow : (2 : ℝ) ^ l ≤ (2 : ℝ) ^ L := by
    rw [← Real.rpow_natCast (2 : ℝ) l, ← Real.rpow_natCast (2 : ℝ) L]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hlR
  have harithQ : (Work.KMTAreas.A7.arithQ ρ l : ℝ) ≤ (2 : ℝ) ^ (C * (2 : ℝ) ^ L) :=
    le_trans (hCq l) (Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (mul_le_mul_of_nonneg_left hpow hC.le))
  have h2powL : (2 : ℝ) ^ (L + 1) = 2 * (2 : ℝ) ^ L := by rw [pow_succ]; ring
  have h2L1 : (1 : ℝ) ≤ (2 : ℝ) ^ L := one_le_pow₀ (by norm_num)
  have hkey : 2 * (2 : ℝ) ^ (C * (2 : ℝ) ^ L) ≤ (2 : ℝ) ^ ((C + 1) * (2 : ℝ) ^ L) := by
    have hsum : (C + 1) * (2 : ℝ) ^ L = C * (2 : ℝ) ^ L + (2 : ℝ) ^ L := by ring
    rw [hsum, Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    have hge : (2 : ℝ) ≤ (2 : ℝ) ^ ((2 : ℝ) ^ L) := by
      have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) h2L1
      simpa using this
    calc 2 * (2 : ℝ) ^ (C * (2 : ℝ) ^ L) = (2 : ℝ) ^ (C * (2 : ℝ) ^ L) * 2 := by ring
      _ ≤ (2 : ℝ) ^ (C * (2 : ℝ) ^ L) * (2 : ℝ) ^ ((2 : ℝ) ^ L) :=
          mul_le_mul_of_nonneg_left hge (Real.rpow_nonneg (by norm_num) _)
  calc 8 * (Work.KMTAreas.A7.arithQ ρ l : ℝ) * (2 : ℝ) ^ (L + 1)
      = 8 * (Work.KMTAreas.A7.arithQ ρ l : ℝ) * (2 * (2 : ℝ) ^ L) := by rw [h2powL]
    _ ≤ 8 * (2 : ℝ) ^ (C * (2 : ℝ) ^ L) * (2 * (2 : ℝ) ^ L) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left harithQ (by norm_num)
    _ = 8 * (2 : ℝ) ^ L * (2 * (2 : ℝ) ^ (C * (2 : ℝ) ^ L)) := by ring
    _ ≤ 8 * (2 : ℝ) ^ L * (2 : ℝ) ^ ((C + 1) * (2 : ℝ) ^ L) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)

/-- In the non-Farey regime the height `L = lcL l₁ l₂ k₁ k₂` is bounded in terms of `ρ` alone. -/
theorem badLmaxBound (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∃ B : ℕ, ∀ (l₁ l₂ k₁ k₂ N : ℕ),
      Work.KMTAreas.A7.splitCut ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) < N →
      N < 8 * Work.KMTAreas.A7.arithQ ρ (max l₁ l₂) * 2 ^ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ + 1) →
      Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ ≤ B := by
  obtain ⟨C, hCpos, hC⟩ := Work.KMTAreas.A7.arithQ_le_rpow ρ hρ hρ1
  obtain ⟨L₀, hL₀⟩ := Work.KMTAreas.A7.splitCut_dominates ρ hρ (C + 1) (by linarith)
  refine ⟨max L₀ 1, ?_⟩
  intro l₁ l₂ k₁ k₂ N hsplit hN
  set L : ℕ := Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ with hL
  by_contra hcon
  have hLt : max L₀ 1 < L := lt_of_not_ge hcon
  have hMle : L₀ ≤ L := le_trans (le_max_left _ _) hLt.le
  have hlmax : max l₁ l₂ ≤ L := by
    rw [hL]
    show max l₁ l₂ ≤ max (max l₁ l₂) (max k₁ k₂)
    exact le_max_left _ _
  have hsplit' : (Work.KMTAreas.A7.splitCut ρ L : ℝ) < (N : ℝ) := by
    exact_mod_cast hsplit
  have hN' : (N : ℝ) < 8 * (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂) : ℝ) * (2 : ℝ) ^ (L + 1) := by
    exact_mod_cast hN
  have hkey : 8 * (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂) : ℝ) * (2 : ℝ) ^ (L + 1)
      ≤ 8 * (2 : ℝ) ^ L * (2 : ℝ) ^ ((C + 1) * (2 : ℝ) ^ L) :=
    eight_arithQ_le ρ C hCpos hC hlmax
  have hdom : 8 * (2 : ℝ) ^ L * (2 : ℝ) ^ ((C + 1) * (2 : ℝ) ^ L)
      < (Work.KMTAreas.A7.splitCut ρ L : ℝ) :=
    hL₀ L hMle
  linarith

end Work.KMTPlan.A6
