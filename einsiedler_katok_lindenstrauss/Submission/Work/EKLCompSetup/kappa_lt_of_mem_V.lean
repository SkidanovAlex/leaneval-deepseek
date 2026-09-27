import Mathlib
import Submission.Work.EKLComp.C8Defs

/-!
# `κ` is small on the displacement neighbourhood `V δ`

EKL Lemma 4.4 (`e:findkappa`): if the displacement `g` is δ-close to the identity in the
max-entry sense, i.e. `g ∈ V δ` with `δ < 1/4`, then

  `κ(g) = max(|g₁₁ - g₀₀|, max(√|g₁₀|, |g₂₀|, |g₁₂|)) < 2 √δ`.

Indeed every entry of `g` differs from the corresponding entry of `1` by at most `δ`, so
`κ_a(g) ≤ 2δ`, `κ_u(g) ≤ √δ`, and `max(2δ, √δ) < 2√δ` for `0 < δ < 1`.
-/

namespace Work.EKLCompSetup

theorem kappa_lt_of_mem_V {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 4)
    {g : Work.EKLContract.SL3} (hg : g ∈ Work.EKLContract.V δ) :
    Work.EKLC8Core.kappa ((g : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) <
      2 * δ ^ (1 / 2 : ℝ) := by
  have hδ1' : δ < 1 := by linarith
  set M : Matrix (Fin 3) (Fin 3) ℝ := (g : Matrix (Fin 3) (Fin 3) ℝ) with hM
  -- every entry of `M` is within `δ` of the corresponding entry of `1`
  have hmem : ∀ i j, |M i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < δ := by
    intro i j
    rw [hM]
    exact hg i j
  have hd : ∀ i : Fin 3, |M i i - 1| < δ := fun i => by simpa using hmem i i
  have ho : ∀ {i j : Fin 3}, i ≠ j → |M i j| < δ := fun {i j} hij => by
    simpa [Matrix.one_apply_ne hij] using hmem i j
  have hsqrtpos : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ0
  have hsqrt_lt : δ < Real.sqrt δ := (Real.lt_sqrt (le_of_lt hδ0)).mpr (by nlinarith)
  have hδ_lt_2sqrt : δ < 2 * Real.sqrt δ := by linarith
  have h2sqrt : Real.sqrt δ < 2 * Real.sqrt δ := by linarith
  -- the `U`-component
  have hU : Work.EKLC8Core.kappaU M < 2 * Real.sqrt δ := by
    rw [Work.EKLC8Core.kappaU]
    apply max_lt
    · exact lt_trans (Real.sqrt_lt_sqrt (abs_nonneg _)
        (ho (show (1 : Fin 3) ≠ 0 by decide))) h2sqrt
    · apply max_lt
      · exact lt_trans (ho (show (2 : Fin 3) ≠ 0 by decide)) hδ_lt_2sqrt
      · exact lt_trans (ho (show (1 : Fin 3) ≠ 2 by decide)) hδ_lt_2sqrt
  -- the `A`-component
  have hA : Work.EKLC8Core.kappaA M < 2 * Real.sqrt δ := by
    rw [Work.EKLC8Core.kappaA]
    have h1 := hd 1
    have h0 := hd 0
    have ht : |M 1 1 - M 0 0| ≤ |M 1 1 - 1| + |M 0 0 - 1| := by
      have h := dist_triangle (M 1 1) (1 : ℝ) (M 0 0)
      rw [Real.dist_eq, Real.dist_eq, Real.dist_eq] at h
      rwa [abs_sub_comm 1 (M 0 0)] at h
    linarith
  have hk : Work.EKLC8Core.kappa M < 2 * Real.sqrt δ := by
    rw [Work.EKLC8Core.kappa]
    exact max_lt hA hU
  simpa [Real.sqrt_eq_rpow] using hk

end Work.EKLCompSetup
