import Mathlib
import Submission.Work.WilG4c.PolyCombBasic

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilG4c

open WilkiesDesign
open Work.WilG0 Work.WilG1
open PolyComb

/-- **`Ω`-definability of polynomial combinations.**  If the graphs of `k` functions
`H i : ℝ^m → ℝ` are `Ω`-definable at formats `F i` and degrees `D i`, then the graph of
`x ↦ P.eval (fun i => H i x)` (for any `P : MvPolynomial (Fin k) ℝ`) is `Ω`-definable with a
format that is (up to an additive constant depending only on `m, k`) the sum of the `F i`, and
a degree linear in `Σ i, D i` and in `P.totalDegree` with coefficients depending only on `k`.
Construction: work in `ℝ^{m+1+k}` with coordinates `(x, value, y)`, pull back `graphOf (H i)`
along the coordinate substitution sending `(x, last)` to `(x, y_i)` (so that `y_i = H i x`),
intersect with the hypersurface `value = P (y_0,…,y_{k-1})`, and project the trailing `k`
coordinates away. -/
theorem FamGraphPolyComb (S : WilkiesDesign.SOMin) (m k : ℕ) : ∃ (A C : ℕ),
    ∀ (F D : Fin k → ℕ) (H : Fin k → (Fin m → ℝ) → ℝ) (P : MvPolynomial (Fin k) ℝ),
      (∀ i, WilkiesDesign.graphOf (H i) ∈ S.Ω (F i) (D i) (m + 1)) →
      WilkiesDesign.graphOf (fun x : Fin m → ℝ => MvPolynomial.eval (fun i => H i x) P) ∈
        S.Ω ((∑ i, F i) + A) (C * ((∑ i, D i) + P.totalDegree) + C) (m + 1) := by
  refine ⟨2 * ((m + 1 + k) + (m + 1)) + 1 + 1 + 1 + k + (m + 1), 2 * k + 2, ?_⟩
  intro F D H P hH
  -- the `k` pullbacks of the graphs of the `H i`
  have hpull : ∀ i : Fin k,
      {z : Fin (m + 1 + k) → ℝ | z ∘ sigY m k i ∈ graphOf (H i)} ∈
        S.Ω (F i + 2 * ((m + 1 + k) + (m + 1)) + 1) (D i + 2) (m + 1 + k) :=
    fun i => GraphComp.subst_mem S (sigY m k i) (hH i)
  -- the hypersurface `value = P (y)`
  have hhyp : {z : Fin (m + 1 + k) → ℝ | MvPolynomial.eval z (combPoly m k P) = 0} ∈
      S.Ω (m + 1 + k) (combPoly m k P).totalDegree (m + 1 + k) :=
    S.hyp (m + 1 + k) (combPoly m k P)
  have hFi : ∀ i : Fin k, F i ≤ ∑ j, F j := fun i => by
    have := Finset.single_le_sum (f := F) (fun j _ => Nat.zero_le (F j)) (Finset.mem_univ i)
    simpa using this
  -- raise all formats to a common value
  have hpull' : ∀ i : Fin k,
      {z : Fin (m + 1 + k) → ℝ | z ∘ sigY m k i ∈ graphOf (H i)} ∈
        S.Ω ((∑ j, F j) + (2 * ((m + 1 + k) + (m + 1)) + 1)) (D i + 2) (m + 1 + k) :=
    fun i => Omega.mono (hpull i) (by have := hFi i; omega) le_rfl
  have hInter : (⋂ i : Fin k, {z : Fin (m + 1 + k) → ℝ | z ∘ sigY m k i ∈ graphOf (H i)}) ∈
      S.Ω ((∑ j, F j) + (2 * ((m + 1 + k) + (m + 1)) + 1) + 1)
        (∑ i : Fin k, (D i + 2)) (m + 1 + k) :=
    S.inter (fun i : Fin k => D i + 2)
      (fun i : Fin k => {z : Fin (m + 1 + k) → ℝ | z ∘ sigY m k i ∈ graphOf (H i)}) hpull'
  have hhyp' : {z : Fin (m + 1 + k) → ℝ | MvPolynomial.eval z (combPoly m k P) = 0} ∈
      S.Ω ((∑ j, F j) + (2 * ((m + 1 + k) + (m + 1)) + 1) + 1)
        (combPoly m k P).totalDegree (m + 1 + k) :=
    Omega.mono hhyp (by omega) le_rfl
  -- intersect and project the trailing `k` coordinates away
  have hInt2 := Omega_inter2 hInter hhyp'
  have hProj := projLastIter_mem S (m + 1) k
      ((∑ j, F j) + (2 * ((m + 1 + k) + (m + 1)) + 1) + 1 + 1)
      ((∑ i : Fin k, (D i + 2)) + (combPoly m k P).totalDegree) _ hInt2
  rw [projLastIter_eq_graph m k H P] at hProj
  refine Omega.mono hProj ?_ ?_
  · omega
  · have hsumD : (∑ i : Fin k, (D i + 2)) = (∑ i : Fin k, D i) + k * 2 := by
      rw [Finset.sum_add_distrib]
      congr 1
      simp [Finset.sum_const]
    rw [hsumD]
    set Tt : ℕ := (∑ i : Fin k, D i) + P.totalDegree with hTt
    have hSd : (∑ i : Fin k, D i) ≤ Tt := by omega
    have htd : (combPoly m k P).totalDegree ≤ Tt + 1 := by
      have := combPoly_totalDegree_le m k P; omega
    have hmul : 2 * Tt ≤ (2 * k + 2) * Tt := by
      have h : (2 : ℕ) ≤ 2 * k + 2 := by omega
      exact Nat.mul_le_mul_right Tt h
    omega

end Work.WilG4c
