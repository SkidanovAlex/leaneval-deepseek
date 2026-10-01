import Mathlib

namespace Work.LinnikAreas.Density4

open scoped BigOperators

/-- Conjugating a finite complex family preserves the sum of squared norms. -/
private lemma sum_normSq_conj {α : Type*} [Fintype α] (f : α → ℂ) :
    (∑ i, ‖(starRingEnd ℂ) (f i)‖ ^ 2) = ∑ i, ‖f i‖ ^ 2 := by
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Complex.norm_conj]

/-- `∑ᵢ conj(fᵢ)·fᵢ` is the (real) sum of squared norms, viewed as a complex number. -/
private lemma sum_conj_mul_self {α : Type*} [Fintype α] (f : α → ℂ) :
    (∑ i, (starRingEnd ℂ) (f i) * f i) = ((∑ i, ‖f i‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Complex.conj_mul']
  push_cast
  ring

/-- **The duality principle of Heath-Brown §11 (HB (11.15), see also Iwaniec–Kowalski p. 170).**
If a finite matrix `A : ι → κ → ℂ` satisfies
`Σ_n ‖Σ_χ A n χ · C χ‖² ≤ B · Σ_χ ‖C χ‖²` for every coefficient family `C`, then it also satisfies
`Σ_χ ‖Σ_n A n χ · b n‖² ≤ B · Σ_n ‖b n‖²` for every `b`: the transposed matrix has the same `ℓ²`
operator norm.  In HB §11 this is applied with `A n χ = w_χ^{1/2}(Σ_{d|n}θ_d)χ(n)n^{1/2-ρ(χ)}(…)^{1/2}`
and `b_n = (Σ_{d|n}ψ_d)n^{-1/2}(…)^{1/2}` to convert the operator bound (11.15) into a bound for
`Σ_n b_n²`. -/
theorem duality_principle {ι κ : Type*} [Fintype ι] [Fintype κ] (A : ι → κ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (h : ∀ C : κ → ℂ, (∑ n, ‖∑ χ, A n χ * C χ‖ ^ 2) ≤ B * ∑ χ, ‖C χ‖ ^ 2) :
    ∀ b : ι → ℂ, (∑ χ, ‖∑ n, A n χ * b n‖ ^ 2) ≤ B * ∑ n, ‖b n‖ ^ 2 := by
  intro b
  classical
  -- `u` is the image of `b` under the transposed matrix; it is the vector whose `ℓ²` norm we bound.
  let u : κ → ℂ := fun χ => ∑ n, A n χ * b n
  -- `v` is the image of `conj u` under the original matrix `A`.
  let v : ι → ℂ := fun n => ∑ χ, A n χ * (starRingEnd ℂ) (u χ)
  change (∑ χ, ‖u χ‖ ^ 2) ≤ B * ∑ n, ‖b n‖ ^ 2
  have hSnn : 0 ≤ ∑ χ, ‖u χ‖ ^ 2 := Finset.sum_nonneg (fun _ _ => by positivity)
  have hTnn : 0 ≤ ∑ n, ‖b n‖ ^ 2 := Finset.sum_nonneg (fun _ _ => by positivity)
  -- The hypothesis, applied to the test family `C = conj u`.
  have hcv : ∑ n, ‖v n‖ ^ 2 ≤ B * ∑ χ, ‖u χ‖ ^ 2 := by
    have hh := h (fun χ => (starRingEnd ℂ) (u χ))
    rw [sum_normSq_conj] at hh
    exact hh
  -- The duality identity: `∑ₙ bₙ vₙ = ∑χ conj(uχ) uχ = ∑χ ‖uχ‖²`, a nonnegative real.
  have hid : ∑ n, b n * v n = ((∑ χ, ‖u χ‖ ^ 2 : ℝ) : ℂ) := by
    rw [← sum_conj_mul_self u]
    have key : ∀ n, b n * v n = ∑ χ, (A n χ * b n) * (starRingEnd ℂ) (u χ) := by
      intro n
      show b n * (∑ χ, A n χ * (starRingEnd ℂ) (u χ)) =
        ∑ χ, (A n χ * b n) * (starRingEnd ℂ) (u χ)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun χ _ => ?_)
      ring
    rw [Finset.sum_congr rfl (fun n _ => key n), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun χ _ => ?_)
    rw [← Finset.sum_mul]
    change (∑ n, A n χ * b n) * (starRingEnd ℂ) (u χ) =
      (starRingEnd ℂ) (u χ) * (∑ n, A n χ * b n)
    ring
  -- Hence `∑χ ‖uχ‖² = ‖∑ₙ bₙ vₙ‖`.
  have hSeq : ∑ χ, ‖u χ‖ ^ 2 = ‖∑ n, b n * v n‖ := by
    rw [hid, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hSnn]
  -- Triangle inequality and Cauchy–Schwarz.
  have htri : ∑ χ, ‖u χ‖ ^ 2 ≤ ∑ n, ‖b n‖ * ‖v n‖ := by
    rw [hSeq]
    calc ‖∑ n, b n * v n‖ ≤ ∑ n, ‖b n * v n‖ := norm_sum_le _ _
      _ = ∑ n, ‖b n‖ * ‖v n‖ := by
            refine Finset.sum_congr rfl (fun n _ => ?_)
            rw [norm_mul]
  have hcs : (∑ n, ‖b n‖ * ‖v n‖) ^ 2 ≤ (∑ n, ‖b n‖ ^ 2) * (∑ n, ‖v n‖ ^ 2) := by
    simpa using
      Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι) (fun n => ‖b n‖) (fun n => ‖v n‖)
  -- Combine: `(∑χ ‖uχ‖²)² ≤ B (∑ₙ ‖bₙ‖²) (∑χ ‖uχ‖²)`.
  have hsq : (∑ χ, ‖u χ‖ ^ 2) ^ 2 ≤ B * (∑ n, ‖b n‖ ^ 2) * ∑ χ, ‖u χ‖ ^ 2 := by
    have h1 : (∑ χ, ‖u χ‖ ^ 2) ^ 2 ≤ (∑ n, ‖b n‖ * ‖v n‖) ^ 2 := by
      simpa [pow_two] using mul_self_le_mul_self hSnn htri
    calc (∑ χ, ‖u χ‖ ^ 2) ^ 2 ≤ (∑ n, ‖b n‖ * ‖v n‖) ^ 2 := h1
      _ ≤ (∑ n, ‖b n‖ ^ 2) * (∑ n, ‖v n‖ ^ 2) := hcs
      _ ≤ (∑ n, ‖b n‖ ^ 2) * (B * ∑ χ, ‖u χ‖ ^ 2) := mul_le_mul_of_nonneg_left hcv hTnn
      _ = B * (∑ n, ‖b n‖ ^ 2) * ∑ χ, ‖u χ‖ ^ 2 := by ring
  -- Divide by `∑χ ‖uχ‖²` (positive unless it vanishes, in which case the claim is trivial).
  by_cases h0 : ∑ χ, ‖u χ‖ ^ 2 = 0
  · rw [h0]; exact mul_nonneg hB hTnn
  · have hpos : 0 < ∑ χ, ‖u χ‖ ^ 2 := lt_of_le_of_ne hSnn (Ne.symm h0)
    nlinarith [hsq]

end Work.LinnikAreas.Density4
