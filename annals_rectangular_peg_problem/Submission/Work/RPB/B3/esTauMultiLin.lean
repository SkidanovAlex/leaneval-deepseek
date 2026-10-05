import Mathlib
import Submission.Work.RPB.B3.EsTauAux

/-!
# The multilinear "reflection" identity

We work on `M = ℝ × (ℝ × ℝ)` and with the linear maps
`reflLin c (τ,t,r) = (c * τ, t, r)` of `Work.RPB.B3.EsTauAux`.

Given coefficients `a j` and parameters `c j` satisfying the moment conditions
`∑ j, a j * (c j)^m = 1` for `m = 0, …, k`, the corresponding linear combination of
"reflected" versions of a `k`-multilinear map `P` is `P` itself:
`∑ j, a j • P ∘ (reflLin (c j))^k = P`.

The proof expands `reflLin c` along the `c`-direction.  Writing
`reflLin c z = A z + c • B z` with `A z = (0, z.2)` and `B z = (z.1, 0)`, multilinearity
gives, for every `x : Fin k → M`,

`P (fun i => A (x i) + c • B (x i)) = ∑ s : Finset (Fin k), c ^ (sᶜ).card • P (s.piecewise A B)`

(`A`, `B` here meaning the pointwise versions of `A`, `B` on `x`).  Each summand is a
monomial in `c` of degree `(sᶜ).card ≤ k`, so the moment conditions collapse the outer
`∑ j, a j • _` sum, and at `c = 1` the same expansion reproduces `P x`.
-/

namespace Work.RPB.B3

/-- Coordinate form of `reflLin`: `reflLin c z = (c * z.1, z.2)`. -/
private lemma reflLin_apply_prod (c : ℝ) (z : ℝ × (ℝ × ℝ)) :
    reflLin c z = (c * z.1, z.2) := by
  obtain ⟨τ, t, r⟩ := z
  simp [reflLin_apply]

/-- Multilinear expansion of `f` at the family `fun i => A i + c • B i`: it is a polynomial
in `c` of degree at most the number of coordinates, whose monomials are indexed by the
subsets on which the `B`-part is used. -/
private lemma multilinear_add_smul_expansion {E : Type*} [AddCommMonoid E] [Module ℝ E]
    {k : ℕ} (f : MultilinearMap ℝ (fun _ : Fin k => ℝ × (ℝ × ℝ)) E)
    (A B : Fin k → ℝ × (ℝ × ℝ)) (c : ℝ) :
    f (fun i => A i + c • B i) = ∑ s : Finset (Fin k), c ^ (sᶜ).card • f (s.piecewise A B) := by
  rw [show (fun i => A i + c • B i) = (A + fun i => c • B i) from rfl,
      MultilinearMap.map_add_univ]
  refine Finset.sum_congr rfl fun s _ => ?_
  set m : Fin k → ℝ × (ℝ × ℝ) := s.piecewise A B with hm
  have hpiece : s.piecewise A (fun i => c • B i) = sᶜ.piecewise (fun i => c • m i) m := by
    funext i
    by_cases h : i ∈ s
    · rw [Finset.piecewise_eq_of_mem _ _ _ h, Finset.piecewise_eq_of_notMem _ _ _ (by simp [h])]
      simp only [hm, Finset.piecewise_eq_of_mem _ _ _ h]
    · rw [Finset.piecewise_eq_of_notMem _ _ _ h, Finset.piecewise_eq_of_mem _ _ _ (by simp [h])]
      simp only [hm, Finset.piecewise_eq_of_notMem _ _ _ h]
  rw [hpiece, MultilinearMap.map_piecewise_smul, Finset.prod_const]

/-- The same expansion for a continuous multilinear map. -/
private lemma continuous_expansion {E : Type*} [AddCommMonoid E] [Module ℝ E]
    [TopologicalSpace E] {k : ℕ}
    (P : ContinuousMultilinearMap ℝ (fun _ : Fin k => ℝ × (ℝ × ℝ)) E)
    (A B : Fin k → ℝ × (ℝ × ℝ)) (c : ℝ) :
    P (A + fun i => c • B i) = ∑ s : Finset (Fin k), c ^ (sᶜ).card • P (s.piecewise A B) :=
  multilinear_add_smul_expansion P.toMultilinearMap A B c

theorem esTauMultiLin {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n k : ℕ} (c a : Fin n → ℝ)
    (hid : ∀ m : ℕ, m ≤ k → ∑ j, a j * (c j)^m = 1)
    (P : ContinuousMultilinearMap ℝ (fun _ : Fin k => ℝ × (ℝ × ℝ)) E) :
    ∑ j : Fin n, a j • P.compContinuousLinearMap (fun _ : Fin k => reflLin (c j)) = P := by
  ext x
  simp only [sum_apply, smul_apply, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  -- Split `x` into the part fixed by `reflLin c` and the part scaled by it.
  set A : Fin k → ℝ × (ℝ × ℝ) := fun i => (0, (x i).2) with hA
  set B : Fin k → ℝ × (ℝ × ℝ) := fun i => ((x i).1, 0) with hB
  have hx : x = A + B := by
    funext i; simp [hA, hB]
  have hrefl : ∀ j, (fun i => reflLin (c j) (x i)) = A + fun i => c j • B i := by
    intro j; funext i
    rw [reflLin_apply_prod, hA, hB]; simp
  have hcard : ∀ s : Finset (Fin k), (sᶜ).card ≤ k := fun s => by
    simpa using Finset.card_le_univ (sᶜ)
  -- The main computation: the moment conditions collapse the sum over `j`.
  have hmain : (∑ j : Fin n, a j • P (A + fun i => c j • B i))
      = ∑ s : Finset (Fin k), P (s.piecewise A B) := by
    have h1 : ∀ j, a j • P (A + fun i => c j • B i)
        = ∑ s : Finset (Fin k), (a j * (c j)^(sᶜ).card) • P (s.piecewise A B) := by
      intro j
      rw [continuous_expansion P A B (c j), Finset.smul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [smul_smul]
    simp only [h1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← Finset.sum_smul, hid (sᶜ).card (hcard s), one_smul]
  -- At `c = 1` the expansion recovers `P x`.
  have hPx : P x = ∑ s : Finset (Fin k), P (s.piecewise A B) := by
    rw [hx]
    exact MultilinearMap.map_add_univ P.toMultilinearMap A B
  simp only [hrefl]
  rw [hmain, hPx]

end Work.RPB.B3
