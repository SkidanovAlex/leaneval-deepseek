import Mathlib

/-!
# Conjugation symmetry of the even completed Hurwitz zeta function

`completedHurwitzZetaEven₀ a` is (up to the factor `1/2`) the Mellin transform `Λ₀` of the
modified even Hurwitz kernel of the weak FE-pair `hurwitzEvenFEPair a`. All the data entering
that kernel (`f`, the constants `f₀`, `g₀`, the root number `ε`) are fixed by complex
conjugation, so the Mellin transform inherits the Schwarz reflection symmetry

`conj (completedHurwitzZetaEven₀ a (conj s)) = completedHurwitzZetaEven₀ a s`.

The key analytic ingredient is `conj_mellin_of_conj_self`: the Mellin transform of a
conjugation-invariant function `f : ℝ → ℂ` satisfies
`conj (mellin f (conj s)) = mellin f s`. This holds unconditionally, i.e. also at points where
the Mellin integral is not (absolutely) convergent, because the identity is proved at the level
of the integral itself (Bochner integrals of pointwise equal functions, and `integral_conj`).
-/

namespace Work.A7

open MeasureTheory

/-- Conjugation symmetry of the Mellin transform of a conjugation-invariant function.

For `f : ℝ → ℂ` with `starRingEnd ℂ (f x) = f x` for every real `x` (i.e. `f` takes real
values), and every `s : ℂ`,
`conj (mellin f (conj s)) = mellin f s`. -/
lemma conj_mellin_of_conj_self (f : ℝ → ℂ) (hf : ∀ x, starRingEnd ℂ (f x) = f x) (s : ℂ) :
    starRingEnd ℂ (mellin f (starRingEnd ℂ s)) = mellin f s := by
  rw [mellin, mellin, ← integral_conj]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  rw [smul_eq_mul, map_mul, hf t]
  congr 1
  have harg : (t : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg ht.le]
    exact Real.pi_ne_zero.symm
  have h := Complex.cpow_conj (t : ℂ) (s - 1) harg
  rw [map_sub, map_one, Complex.conj_ofReal] at h
  have h2 := congrArg (starRingEnd ℂ) h
  rw [h2]
  simp

/-- The modified kernel `f_modif` of a weak FE-pair whose data are all fixed by complex
conjugation is itself fixed by complex conjugation. -/
lemma WeakFEPair.conj_f_modif (P : WeakFEPair ℂ)
    (hf : ∀ x, starRingEnd ℂ (P.f x) = P.f x)
    (hf₀ : starRingEnd ℂ P.f₀ = P.f₀)
    (hg₀ : starRingEnd ℂ P.g₀ = P.g₀)
    (hε : starRingEnd ℂ P.ε = P.ε) (x : ℝ) :
    starRingEnd ℂ (P.f_modif x) = P.f_modif x := by
  rw [WeakFEPair.f_modif, Pi.add_apply, map_add]
  congr 1
  · by_cases hx : x ∈ Set.Ioi 1
    · rw [Set.indicator_of_mem hx, map_sub, hf, hf₀]
    · rw [Set.indicator_of_notMem hx, map_zero]
  · by_cases hx : x ∈ Set.Ioo 0 1
    · rw [Set.indicator_of_mem hx, map_sub, hf]
      congr 1
      rw [smul_eq_mul, map_mul, map_mul, hε, Complex.conj_ofReal, hg₀]
    · rw [Set.indicator_of_notMem hx, map_zero]

theorem completedHurwitzZetaEven_entire_star (a : UnitAddCircle) (s : ℂ) :
    (starRingEnd ℂ) (HurwitzZeta.completedHurwitzZetaEven₀ a ((starRingEnd ℂ) s)) =
      HurwitzZeta.completedHurwitzZetaEven₀ a s := by
  have hf : ∀ x, starRingEnd ℂ ((HurwitzZeta.hurwitzEvenFEPair a).f x)
      = (HurwitzZeta.hurwitzEvenFEPair a).f x := by
    intro x
    show starRingEnd ℂ (↑(HurwitzZeta.evenKernel a x)) = ↑(HurwitzZeta.evenKernel a x)
    exact Complex.conj_ofReal _
  have hf₀ : starRingEnd ℂ ((HurwitzZeta.hurwitzEvenFEPair a).f₀)
      = (HurwitzZeta.hurwitzEvenFEPair a).f₀ := by
    rw [HurwitzZeta.hurwitzEvenFEPair]; split_ifs <;> simp
  have hg₀ : starRingEnd ℂ ((HurwitzZeta.hurwitzEvenFEPair a).g₀)
      = (HurwitzZeta.hurwitzEvenFEPair a).g₀ := by
    rw [HurwitzZeta.hurwitzEvenFEPair]; simp
  have hε : starRingEnd ℂ ((HurwitzZeta.hurwitzEvenFEPair a).ε)
      = (HurwitzZeta.hurwitzEvenFEPair a).ε := by
    rw [HurwitzZeta.hurwitzEvenFEPair]; simp
  have hmodif : ∀ x, starRingEnd ℂ ((HurwitzZeta.hurwitzEvenFEPair a).f_modif x)
      = (HurwitzZeta.hurwitzEvenFEPair a).f_modif x :=
    WeakFEPair.conj_f_modif _ hf hf₀ hg₀ hε
  have hmellin : starRingEnd ℂ
      (mellin (HurwitzZeta.hurwitzEvenFEPair a).f_modif (starRingEnd ℂ (s / 2)))
      = mellin (HurwitzZeta.hurwitzEvenFEPair a).f_modif (s / 2) :=
    conj_mellin_of_conj_self _ hmodif (s / 2)
  unfold HurwitzZeta.completedHurwitzZetaEven₀ WeakFEPair.Λ₀
  have h2 : starRingEnd ℂ (s / 2) = starRingEnd ℂ s / 2 := by rw [map_div₀, map_ofNat]
  rw [← h2, map_div₀ (starRingEnd ℂ), map_ofNat, hmellin]

end Work.A7
