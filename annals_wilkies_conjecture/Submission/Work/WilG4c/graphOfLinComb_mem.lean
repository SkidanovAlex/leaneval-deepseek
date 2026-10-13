import Mathlib
import Submission.Work.WilG4c.GraphOfComp
import Submission.Work.WilG4c.PolyCombBasic

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG
open Work.WilG0 Work.WilG1 PolyComb

/-!
## `Ω`-definability of the graph of `x ↦ A x + T x * (B x - A x)`

If the graphs of three functions `A, B, T : ℝ^M → ℝ` are `Ω`-definable with formats `F₁, F₂, F₃`
and degrees `D₁, D₂, D₃`, then the graph of the pointwise combination
`x ↦ A x + T x * (B x - A x)` is `Ω`-definable with format `F₁ + F₂ + F₃ + C₁` and degree
`D₁ + D₂ + D₃ + C₂`, for constants `C₁, C₂` depending only on `M`.

The argument is the standard one: introduce the three values `A x`, `B x`, `T x` as fresh
coordinates in `ℝ^{(M+1)+3}` with layout `(x, y, a, b, t)`, pull the three graphs back along the
coordinate substitutions `sigY M 3 i` (`(x, y) ↦ (x, y_i)`), impose the single hypersurface
`y = a + t * (b - a)`, and project the three fresh coordinates away.  Each pullback costs
`Dᵢ + 2` in degree (`GraphComp.subst_mem`), the hypersurface costs its total degree `3`, and the
projection costs nothing in degree — so the degree stays *linear with coefficient one* in each
`Dᵢ`, which is what the statement asks for, and which the cruder packaged lemma
`FamGraphPolyComb` (degree `C * (Σ Dᵢ + P.totalDegree) + C`) does not provide.

The projection identity carrying the combinatorial content is
`PolyComb.projLastIter_eq_graph` (`Submission/Work/WilG4c/PolyCombBasic.lean`).
The same identity, for the specific four sets of this construction and in the equivalent
vocabulary of `Submission/Work/WilG4c/LinCombDefs.lean`, is verified independently in
`Work.WilG4c.lcProjEq` (`Submission/Work/WilG4c/lcProjEq.lean`).
-/

/-- The polynomial `a + t * (b - a)` in the three variables `(a, b, t)`; total degree `≤ 2`. -/
def linCombPoly : MvPolynomial (Fin 3) ℝ :=
  MvPolynomial.X (0 : Fin 3) +
    MvPolynomial.X (2 : Fin 3) * (MvPolynomial.X (1 : Fin 3) - MvPolynomial.X (0 : Fin 3))

theorem linCombPoly_eval (a b t : ℝ) :
    MvPolynomial.eval ![a, b, t] linCombPoly = a + t * (b - a) := by
  simp [linCombPoly]

theorem linCombPoly_totalDegree_le : linCombPoly.totalDegree ≤ 2 := by
  simp only [linCombPoly]
  refine le_trans (MvPolynomial.totalDegree_add _ _) (max_le ?_ ?_)
  · exact le_trans (le_of_eq (MvPolynomial.totalDegree_X (R := ℝ) _)) (by omega)
  · refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
    have h1 : (MvPolynomial.X (2 : Fin 3) : MvPolynomial (Fin 3) ℝ).totalDegree ≤ 1 :=
      le_of_eq (MvPolynomial.totalDegree_X (R := ℝ) _)
    have h2 : ((MvPolynomial.X (1 : Fin 3) : MvPolynomial (Fin 3) ℝ) -
        MvPolynomial.X (0 : Fin 3)).totalDegree ≤ 1 :=
      le_trans (MvPolynomial.totalDegree_sub _ _)
        (max_le (le_of_eq (MvPolynomial.totalDegree_X (R := ℝ) _))
          (le_of_eq (MvPolynomial.totalDegree_X (R := ℝ) _)))
    omega

/-- The polynomial combination of the triple `(A, B, T)` is the requested combination. -/
theorem fun_linComb (M : ℕ) (A B T : (Fin M → ℝ) → ℝ) :
    (fun x : Fin M → ℝ => MvPolynomial.eval (fun i : Fin 3 => ![A, B, T] i x) linCombPoly) =
      (fun x : Fin M → ℝ => A x + T x * (B x - A x)) := by
  funext x
  rw [show (fun i : Fin 3 => ![A, B, T] i x) = ![A x, B x, T x] from by
    funext i; fin_cases i <;> simp]
  exact linCombPoly_eval (A x) (B x) (T x)

theorem graphOfLinComb_mem (S : WilkiesDesign.SOMin) (M : ℕ) :
    ∃ (C₁ C₂ : ℕ), ∀ (F₁ F₂ F₃ D₁ D₂ D₃ : ℕ) (A B T : (Fin M → ℝ) → ℝ),
      WilkiesDesign.graphOf A ∈ S.Ω F₁ D₁ (M+1) →
      WilkiesDesign.graphOf B ∈ S.Ω F₂ D₂ (M+1) →
      WilkiesDesign.graphOf T ∈ S.Ω F₃ D₃ (M+1) →
      WilkiesDesign.graphOf (fun x => A x + T x * (B x - A x)) ∈
        S.Ω (F₁ + F₂ + F₃ + C₁) (D₁ + D₂ + D₃ + C₂) (M+1) := by
  refine ⟨2 * ((M + 1 + 3) + (M + 1)) + 1 + 1 + 1 + 3 + (M + 1), 9, ?_⟩
  intro F₁ F₂ F₃ D₁ D₂ D₃ A B T hA hB hT
  -- the triple as a `Fin 3`-indexed family of formats, degrees and functions
  have hH : ∀ i : Fin 3, WilkiesDesign.graphOf (![A, B, T] i) ∈
      S.Ω (![F₁, F₂, F₃] i) (![D₁, D₂, D₃] i) (M + 1) := by
    intro i
    fin_cases i
    · simpa using hA
    · simpa using hB
    · simpa using hT
  -- Step 1: pull the three graphs back to the coordinates `(x, value, y_i)`
  have hpull : ∀ i : Fin 3,
      {z : Fin (M + 1 + 3) → ℝ | z ∘ sigY M 3 i ∈ WilkiesDesign.graphOf (![A, B, T] i)} ∈
        S.Ω (![F₁, F₂, F₃] i + 2 * ((M + 1 + 3) + (M + 1)) + 1)
          (![D₁, D₂, D₃] i + 2) (M + 1 + 3) :=
    fun i => GraphComp.subst_mem S (sigY M 3 i) (hH i)
  -- Step 2: raise the three formats to their common sum
  have hFi : ∀ i : Fin 3, ![F₁, F₂, F₃] i ≤ ∑ j : Fin 3, ![F₁, F₂, F₃] j := by
    intro i
    fin_cases i <;> simp [Fin.sum_univ_three] <;> omega
  have hpull' : ∀ i : Fin 3,
      {z : Fin (M + 1 + 3) → ℝ | z ∘ sigY M 3 i ∈ WilkiesDesign.graphOf (![A, B, T] i)} ∈
        S.Ω ((∑ j : Fin 3, ![F₁, F₂, F₃] j) + (2 * ((M + 1 + 3) + (M + 1)) + 1))
          (![D₁, D₂, D₃] i + 2) (M + 1 + 3) :=
    fun i => Omega.mono (hpull i) (by have := hFi i; omega) le_rfl
  have hPull : (⋂ i : Fin 3,
      {z : Fin (M + 1 + 3) → ℝ | z ∘ sigY M 3 i ∈ WilkiesDesign.graphOf (![A, B, T] i)}) ∈
      S.Ω ((∑ j : Fin 3, ![F₁, F₂, F₃] j) + (2 * ((M + 1 + 3) + (M + 1)) + 1) + 1)
        (∑ i : Fin 3, (![D₁, D₂, D₃] i + 2)) (M + 1 + 3) :=
    S.inter (fun i : Fin 3 => ![D₁, D₂, D₃] i + 2)
      (fun i : Fin 3 =>
        {z : Fin (M + 1 + 3) → ℝ | z ∘ sigY M 3 i ∈ WilkiesDesign.graphOf (![A, B, T] i)})
      hpull'
  -- Step 3: the hypersurface `value = a + t * (b - a)`
  have htd : (combPoly M 3 linCombPoly).totalDegree ≤ 3 := by
    have h1 := combPoly_totalDegree_le M 3 linCombPoly
    have h2 := linCombPoly_totalDegree_le
    omega
  have hhyp : {z : Fin (M + 1 + 3) → ℝ |
        MvPolynomial.eval z (combPoly M 3 linCombPoly) = 0} ∈
      S.Ω ((∑ j : Fin 3, ![F₁, F₂, F₃] j) + (2 * ((M + 1 + 3) + (M + 1)) + 1) + 1)
        3 (M + 1 + 3) :=
    Omega.mono (S.hyp (M + 1 + 3) (combPoly M 3 linCombPoly)) (by omega) htd
  -- Step 4: intersect, then project the three fresh coordinates away
  have hInt := Omega_inter2 hPull hhyp
  have hProj := projLastIter_mem S (M + 1) 3 _ _ _ hInt
  rw [projLastIter_eq_graph M 3 ![A, B, T] linCombPoly] at hProj
  rw [fun_linComb M A B T] at hProj
  -- Step 5: arithmetic bookkeeping
  have hsumF : (∑ j : Fin 3, ![F₁, F₂, F₃] j) = F₁ + F₂ + F₃ := by
    simp [Fin.sum_univ_three]
  have hsumD : (∑ i : Fin 3, (![D₁, D₂, D₃] i + 2)) = D₁ + D₂ + D₃ + 6 := by
    simp [Fin.sum_univ_three]
    omega
  exact Omega.mono hProj (by rw [hsumF]; omega) (by rw [hsumD])

end Work.WilG4c
