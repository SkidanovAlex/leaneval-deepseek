import Mathlib

namespace Work.Holonomy3

open scoped BigOperators

/-- A nonzero polynomial in the "Fourier form" `∑ t ∈ T, a t * z^t` has a zero set of measure
zero along the parameter `u ↦ exp (2 * π * I * u)` on `[0,1]`.

The function `u ↦ ∑ t ∈ T, a t * (exp (2 * π * I * u))^t` is the evaluation at `exp (2 * π * I * u)`
of the polynomial `p = ∑ t ∈ T, a t * X^t`, which is nonzero because `T` has no repeated exponents
and some `a t ≠ 0`.  A nonzero polynomial has finitely many roots, the map `u ↦ exp (2 * π * I * u)`
is injective on `[0,1)`, and a finite set has measure zero. -/
theorem exp_trig_null {T : Finset ℕ} {a : ℕ → ℂ} (ha : ∃ t ∈ T, a t ≠ 0) :
    (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
      {u : ℝ | ∑ t ∈ T, a t * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (u : ℂ))) ^ t = 0} = 0 := by
  let φ : ℝ → ℂ := fun u => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (u : ℂ))
  let p : Polynomial ℂ := ∑ t ∈ T, Polynomial.C (a t) * Polynomial.X ^ t
  change (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
      {u : ℝ | ∑ t ∈ T, a t * φ u ^ t = 0} = 0
  -- The polynomial `p` is nonzero.
  have hp : p ≠ 0 := by
    obtain ⟨t₀, ht₀, ha₀⟩ := ha
    intro h
    have hcoeff : p.coeff t₀ = a t₀ := by
      show (∑ t ∈ T, Polynomial.C (a t) * Polynomial.X ^ t : Polynomial ℂ).coeff t₀ = a t₀
      rw [Polynomial.finsetSum_coeff]
      simp only [Polynomial.coeff_C_mul_X_pow]
      rw [Finset.sum_ite_eq]
      simp [ht₀]
    rw [h] at hcoeff
    simp at hcoeff
    exact ha₀ hcoeff.symm
  -- Its root set is finite.
  have hR : ({z : ℂ | p.IsRoot z}).Finite := p.finite_setOfPred_isRoot hp
  -- Evaluation identity: `p.eval z = ∑ t ∈ T, a t * z^t`.
  have heval : ∀ z : ℂ, p.eval z = ∑ t ∈ T, a t * z ^ t := by
    intro z
    show Polynomial.eval z (∑ t ∈ T, Polynomial.C (a t) * Polynomial.X ^ t : Polynomial ℂ) = _
    rw [Polynomial.eval_finsetSum]
    apply Finset.sum_congr rfl
    intro t ht
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  -- The parameterisation is injective on `[0,1)`.
  have hinj : Set.InjOn φ (Set.Ico (0:ℝ) 1) := by
    intro u hu v hv huv
    change Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (u : ℂ))
        = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (v : ℂ)) at huv
    obtain ⟨n, hn⟩ := (Complex.exp_eq_exp_iff_exists_int).mp huv
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hc : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero hpi) Complex.I_ne_zero
    have hcancel : (u : ℂ) = (v : ℂ) + (n : ℂ) := by
      apply mul_left_cancel₀ hc
      linear_combination hn
    have hsub : (u : ℂ) - (v : ℂ) = (n : ℂ) := by rw [hcancel]; ring
    have hreal : u - v = (n : ℝ) := by
      have h1 : ((u - v : ℝ) : ℂ) = ((n : ℝ) : ℂ) := by
        rw [Complex.ofReal_sub, hsub]; push_cast; ring
      exact Complex.ofReal_inj.mp h1
    have hlt1 : u - v < 1 := by linarith [hu.2, hv.1]
    have hgt1 : -1 < u - v := by linarith [hu.1, hv.2]
    rw [hreal] at hlt1 hgt1
    have hn_lt : n < 1 := by
      have h : (n : ℝ) < ((1 : ℤ) : ℝ) := by simpa using hlt1
      exact Int.cast_lt.mp h
    have hn_gt : -1 < n := by
      have h : ((-1 : ℤ) : ℝ) < (n : ℝ) := by simpa using hgt1
      exact Int.cast_lt.mp h
    have hn0 : n = 0 := by omega
    have : u - v = 0 := by rw [hreal, hn0]; norm_num
    linarith
  -- The zero set is closed, hence measurable.
  have hcontφ : Continuous φ := by
    rw [show φ = (fun u : ℝ => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (u : ℂ))) from rfl]
    fun_prop
  have hmeasS : MeasurableSet {u : ℝ | ∑ t ∈ T, a t * φ u ^ t = 0} := by
    have hcont : Continuous (fun u : ℝ => ∑ t ∈ T, a t * φ u ^ t) := by
      apply continuous_finsetSum
      intro t ht
      exact (continuous_const : Continuous (fun _ : ℝ => a t)).mul (hcontφ.pow t)
    exact (isClosed_eq hcont continuous_const).measurableSet
  -- Maps the zero set into the finite root set, and is injective there.
  have hmaps : Set.MapsTo φ ({u : ℝ | ∑ t ∈ T, a t * φ u ^ t = 0} ∩ Set.Ico (0:ℝ) 1)
      {z : ℂ | p.IsRoot z} := by
    intro u hu
    show p.IsRoot (φ u)
    rw [Polynomial.IsRoot.def, heval]
    exact hu.1
  have hinj' : Set.InjOn φ ({u : ℝ | ∑ t ∈ T, a t * φ u ^ t = 0} ∩ Set.Ico (0:ℝ) 1) :=
    hinj.mono Set.inter_subset_right
  have hfin₁ : ({u : ℝ | ∑ t ∈ T, a t * φ u ^ t = 0} ∩ Set.Ico (0:ℝ) 1).Finite :=
    Set.Finite.of_injOn hmaps hinj' hR
  have hfin₂ : ({u : ℝ | ∑ t ∈ T, a t * φ u ^ t = 0} ∩ Set.Icc (0:ℝ) 1).Finite := by
    refine (hfin₁.union (Set.finite_singleton (1:ℝ))).subset ?_
    intro u hu
    rcases hu with ⟨huS, h0, h1⟩
    rcases lt_or_eq_of_le h1 with h | h
    · exact Or.inl ⟨huS, h0, h⟩
    · exact Or.inr (by simpa using h)
  rw [MeasureTheory.Measure.restrict_apply hmeasS]
  exact hfin₂.measure_zero MeasureTheory.volume

end Work.Holonomy3
