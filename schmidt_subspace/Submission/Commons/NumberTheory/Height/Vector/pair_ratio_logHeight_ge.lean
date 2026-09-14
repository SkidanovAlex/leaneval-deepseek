import Mathlib.NumberTheory.Height.NumberField
import Submission.Commons.NumberTheory.Height.LogHeight.logHeight_le_sum_logHeight1

namespace Commons.NumberTheory.Height.Vector

open scoped BigOperators

/-- Given a nonzero integer vector `b : Fin N → ℤ` with `N ≥ 2`, there exist two distinct
indices `a`, `j` with `b a ≠ 0` such that the logarithmic height of the rational point
represented by `b` is at most `(N - 1)` times the height of the single ratio `b j / b a`.

The proof normalises by the coordinate `a`, turning the point into `c` with `c a = 1`,
and then uses that the height of a tuple is at most the sum of the heights of its
coordinates (`logHeight_le_sum_logHeight1`); all summands except the one at `a` survive,
and there are `N - 1` of them. -/
theorem pair_ratio_logHeight_ge {N : ℕ} (hN : 2 ≤ N) (b : Fin N → ℤ) (hb : b ≠ 0) :
    ∃ a j : Fin N, a ≠ j ∧ b a ≠ 0 ∧
      Height.logHeight (fun i => ((b i : ℤ) : ℚ)) ≤
        ((N - 1 : ℕ) : ℝ) * Height.logHeight₁ (((b j : ℤ) : ℚ) / ((b a : ℤ) : ℚ)) := by
  classical
  -- Pick an index `a` at which `b` is nonzero.
  obtain ⟨a, ha⟩ : ∃ a : Fin N, b a ≠ 0 := by
    by_contra h
    exact hb (funext fun i => by
      by_contra hi
      exact h ⟨i, hi⟩)
  let x : Fin N → ℚ := fun i => ((b i : ℤ) : ℚ)
  have hxa : x a ≠ 0 := by
    simp only [x]
    exact_mod_cast ha
  -- Normalise so that the `a`-th coordinate of `c` is `1`.
  let c : Fin N → ℚ := (x a)⁻¹ • x
  have hca : c a = 1 := by simp [c, hxa]
  have hlog : Height.logHeight c = Height.logHeight x :=
    Height.logHeight_smul_eq_logHeight x (inv_ne_zero hxa)
  -- Height of a tuple is at most the sum of the heights of its coordinates.
  have hsum : Height.logHeight c ≤ ∑ i : Fin N, Height.logHeight₁ (c i) :=
    Commons.NumberTheory.Height.LogHeight.logHeight_le_sum_logHeight1 c
  -- The index set `{i | i ≠ a}` is nonempty because `N ≥ 2`.
  have hnonempty : (Finset.univ.erase a).Nonempty := by
    have hcard_univ : 1 < (Finset.univ : Finset (Fin N)).card := by
      rw [Finset.card_univ, Fintype.card_fin]
      omega
    obtain ⟨j₀, hj₀mem, hj₀ne⟩ := Finset.exists_mem_ne hcard_univ a
    exact ⟨j₀, Finset.mem_erase.mpr ⟨hj₀ne, hj₀mem⟩⟩
  -- Take `j` to be an index `≠ a` maximising the coordinate height.
  obtain ⟨j, hjs, hjmax⟩ :=
    Finset.exists_max_image (Finset.univ.erase a) (fun i => Height.logHeight₁ (c i)) hnonempty
  have hja : j ≠ a := (Finset.mem_erase.mp hjs).1
  -- The sum loses only the vanishing term at `a`.
  have hsplit : ∑ i : Fin N, Height.logHeight₁ (c i)
      = ∑ i ∈ Finset.univ.erase a, Height.logHeight₁ (c i) := by
    have h := Finset.sum_erase_add (Finset.univ : Finset (Fin N))
      (fun i => Height.logHeight₁ (c i)) (Finset.mem_univ a)
    rw [hca, Height.logHeight₁_one, add_zero] at h
    simpa using h.symm
  -- Bound the remaining `N - 1` summands by the maximal one.
  have hbound : ∑ i ∈ Finset.univ.erase a, Height.logHeight₁ (c i)
      ≤ ((N - 1 : ℕ) : ℝ) * Height.logHeight₁ (c j) := by
    have h1 : ∑ i ∈ Finset.univ.erase a, Height.logHeight₁ (c i)
        ≤ ∑ i ∈ Finset.univ.erase a, Height.logHeight₁ (c j) :=
      Finset.sum_le_sum fun i hi => hjmax i hi
    rw [Finset.sum_const, nsmul_eq_mul] at h1
    have hcard : (Finset.univ.erase a : Finset (Fin N)).card = N - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, Fintype.card_fin]
    rwa [hcard] at h1
  refine ⟨a, j, hja.symm, ha, ?_⟩
  calc Height.logHeight (fun i => ((b i : ℤ) : ℚ)) = Height.logHeight x := rfl
    _ = Height.logHeight c := hlog.symm
    _ ≤ ∑ i : Fin N, Height.logHeight₁ (c i) := hsum
    _ = ∑ i ∈ Finset.univ.erase a, Height.logHeight₁ (c i) := hsplit
    _ ≤ ((N - 1 : ℕ) : ℝ) * Height.logHeight₁ (c j) := hbound
    _ = ((N - 1 : ℕ) : ℝ)
          * Height.logHeight₁ (((b j : ℤ) : ℚ) / ((b a : ℤ) : ℚ)) := by
        congr 1
        simp only [c, x, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]

end Commons.NumberTheory.Height.Vector