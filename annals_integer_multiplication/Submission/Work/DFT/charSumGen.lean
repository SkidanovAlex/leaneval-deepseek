import Mathlib
import Submission.Work.DFT.dftDefs
import Submission.Work.DFT.rootSum
import Submission.Work.DFT.charExpSplit

/-!
# The general character-orthogonality sum for the multidimensional DFT

`charSumGen` evaluates the full `Fin ts.prod`-sum of the character
`charExp ts c k = exp(2πi · Σᵢ cᵢ kᵢ/tᵢ)`: it is `∏ᵢ tᵢ` when every component
`tᵢ` divides `cᵢ`, and `0` otherwise.  Specialising `c` to the componentwise
digit difference `digits ts j - digits ts a` recovers the orthogonality
relations `charSumSub` / `charSumConv` used for DFT inversion and convolution.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.DFT

/-- Reindexing a sum over `Fin (m * n)` as a double sum using the mixed-radix
decomposition `k = r + n*q` (`q : Fin m`, `r : Fin n`). -/
theorem sumFinMul (m n : ℕ) (f : ℕ → ℂ) :
    (∑ k : Fin (m * n), f k) = ∑ q : Fin m, ∑ r : Fin n, f (r + n * q) := by
  rw [← Equiv.sum_comp (finProdFinEquiv (m := m) (n := n)) (fun k : Fin (m * n) => f k)]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl; intro x _
  apply Finset.sum_congr rfl; intro y _
  congr 1

/-- The divisibility condition `∀ i < ts.length, tsᵢ ∣ cᵢ` splits off its head. -/
theorem getDDvdCons (t : ℕ) (ts : List ℕ) (c₀ : ℤ) (cs : List ℤ) :
    (∀ i < (t :: ts).length, (((t :: ts).getD i 0 : ℤ) ∣ (c₀ :: cs).getD i 0)) ↔
      ((t : ℤ) ∣ c₀ ∧ ∀ i < ts.length, ((ts.getD i 0 : ℤ) ∣ cs.getD i 0)) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have h0 := h 0 (by simp)
      simpa using h0
    · intro i hi
      have h1 := h (i + 1) (by simp [List.length_cons]; omega)
      simpa using h1
  · rintro ⟨h0, hrest⟩ i hi
    rcases i with _ | i
    · simpa using h0
    · have hi' : i < ts.length := by simp [List.length_cons] at hi; omega
      simpa using hrest i hi'

/-- Product of two "indicator" factors with a common default `0`. -/
theorem iteMulIteZero (p q : Prop) [Decidable p] [Decidable q] (m n : ℂ) :
    (if p then m else 0) * (if q then n else 0) = if p ∧ q then m * n else 0 := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

private theorem charSumGen_aux (ts : List ℕ) :
    ∀ (c : List ℤ), c.length = ts.length → (∀ t ∈ ts, 0 < t) →
      (∑ k : Fin ts.prod, charExp ts c k) =
        if (∀ i < ts.length, (ts.getD i 0 : ℤ) ∣ c.getD i 0) then (ts.prod : ℂ) else 0 := by
  induction ts with
  | nil =>
      intro c hc hpos
      have hc0 : c = [] := List.eq_nil_of_length_eq_zero (by simpa using hc)
      subst hc0
      rw [show ([] : List ℕ).prod = 1 from rfl, Fin.sum_univ_one]
      simp [charExp, myPhase]
  | cons t ts' ih =>
      intro c hc hpos
      have ht : 0 < t := hpos t (by simp)
      have hpos' : ∀ x ∈ ts', 0 < x := fun x hx => hpos x (by simp [hx])
      have hT : 0 < ts'.prod := List.prod_pos hpos'
      obtain ⟨c₀, cs, rfl⟩ : ∃ c₀ cs, c = c₀ :: cs := by
        cases c with
        | nil => simp at hc
        | cons c₀ cs => exact ⟨c₀, cs, rfl⟩
      have hcs : cs.length = ts'.length := by simpa [List.length_cons] using hc
      rw [List.prod_cons]
      rw [sumFinMul t ts'.prod (fun k => charExp (t :: ts') (c₀ :: cs) k)]
      have hsplit : (∑ q : Fin t, ∑ r : Fin ts'.prod,
            charExp (t :: ts') (c₀ :: cs) (r + ts'.prod * q))
          = ∑ q : Fin t, ∑ r : Fin ts'.prod,
              Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
                  (((c₀ : ℝ) * (q : ℝ)) / (t : ℝ) : ℝ)) * charExp ts' cs r :=
        Finset.sum_congr rfl (fun q _ => Finset.sum_congr rfl (fun r _ =>
          charExpSplit t ts' hT c₀ cs (q : ℕ) (r : ℕ) q.isLt r.isLt))
      rw [hsplit]
      rw [show (∑ q : Fin t, ∑ r : Fin ts'.prod,
              Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
                  (((c₀ : ℝ) * (q : ℝ)) / (t : ℝ) : ℝ)) * charExp ts' cs r)
            = (∑ q : Fin t, Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
                  (((c₀ : ℝ) * (q : ℝ)) / (t : ℝ) : ℝ))) *
              (∑ r : Fin ts'.prod, charExp ts' cs r) from by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl; intro q _
          rw [Finset.mul_sum]]
      rw [rootSum t c₀ ht, ih cs hcs hpos']
      have hP := getDDvdCons t ts' c₀ cs
      have hiteP : (if (∀ i < (t :: ts').length,
              (((t :: ts').getD i 0 : ℤ) ∣ (c₀ :: cs).getD i 0))
            then ((t * ts'.prod : ℕ) : ℂ) else 0)
          = if ((t : ℤ) ∣ c₀ ∧ ∀ i < ts'.length, ((ts'.getD i 0 : ℤ) ∣ cs.getD i 0))
              then ((t * ts'.prod : ℕ) : ℂ) else 0 := by
        by_cases h : ((t : ℤ) ∣ c₀ ∧ ∀ i < ts'.length, ((ts'.getD i 0 : ℤ) ∣ cs.getD i 0))
        · rw [ite_eq_left (hP.mpr h), ite_eq_left h]
        · rw [ite_eq_right (fun hp => h (hP.mp hp)), ite_eq_right h]
      rw [hiteP, show ((t * ts'.prod : ℕ) : ℂ) = (t : ℂ) * (ts'.prod : ℂ) by push_cast; ring]
      exact iteMulIteZero ((t : ℤ) ∣ c₀)
        (∀ i < ts'.length, ((ts'.getD i 0 : ℤ) ∣ cs.getD i 0)) (t : ℂ) (ts'.prod : ℂ)

theorem charSumGen (ts : List ℕ) (hpos : ∀ t ∈ ts, 0 < t) (c : List ℤ) (hc : c.length = ts.length) :
    (∑ k : Fin ts.prod, charExp ts c k) =
      if (∀ i < ts.length, (ts.getD i 0 : ℤ) ∣ c.getD i 0) then (ts.prod : ℂ) else 0 :=
  charSumGen_aux ts c hc hpos

end Work.DFT
