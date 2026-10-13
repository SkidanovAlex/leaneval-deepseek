import Mathlib
import Submission.Work.WilE7.coreLT_succ.fiberCut_subset_closure
import Submission.Work.WilE7.E6closure
import Submission.Work.CoreStep.fiberCut_len

namespace Work.WilE7.coreLT_succ

/-- Evaluation of a `ℕ`-polynomial is monotone in the argument (local copy so that this
file is independent of the `Deg` bookkeeping modules). -/
theorem poly_eval_mono (p : Polynomial ℕ) {a b : ℕ} (h : a ≤ b) : p.eval a ≤ p.eval b := by
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range]
  exact Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h i)

/-- Composition of polynomials evaluates by substitution. -/
theorem poly_eval_comp (p q : Polynomial ℕ) (D : ℕ) :
    (p.comp q).eval D = p.eval (q.eval D) := by rw [Polynomial.eval_comp]

/-- **Refined cut family.**  The fibre-cutting lemma of BV, taken over the *topological closure*
of the input family: `E6` (`Work.WilE7.E6closure`) first presents `closure X.set` as a
semi-Pfaffian set `W` of the same ambient dimension, format `≤ a₆` and degree `≤ b₆ X.deg`; the
fibre cut of `W` (`Work.CoreStep.fiberCut_len`) then produces the list `L` of pieces.

Each piece `Z` of `L` is contained in `closure W.set = closure (closure X.set) = closure X.set`,
so the extra containment clause holds, and the degree/length bookkeeping is the substitution
`b = b_fc ∘ b₆` (monotonicity of `p.eval` on `ℕ`). -/
theorem refinedCutFamily
    (hE2 : ∀ F : ℕ, ∃ p : Polynomial ℕ, ∀ (k : ℕ) (X : WilkiesDesign.E.SemiPf k), X.fmt ≤ F →
      ∃ s : Finset (Fin k → ℝ), s.card ≤ p.eval X.deg ∧ (↑s : Set (Fin k → ℝ)) ⊆ X.set ∧
        ∀ x ∈ X.set, ∃ y ∈ s,
          connectedComponentIn X.set x = connectedComponentIn X.set y)
    (hE5 : ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ),
      ∀ (p q : ℕ) (X : WilkiesDesign.E.SemiPf (p + q)), X.fmt ≤ F →
        ∃ L : List (WilkiesDesign.E.Stratum p q), L.length ≤ b.eval X.deg ∧
          (∀ S ∈ L, S.X.fmt ≤ a ∧ S.deg ≤ b.eval X.deg ∧ S.Good) ∧
          X.set = (⋃ S ∈ L, S.X.set) ∧
          L.Pairwise (fun S T => Disjoint S.X.set T.X.set))
    (hE6 : ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (p q : ℕ)
      (X : WilkiesDesign.E.SemiPf (p + q)), X.fmt ≤ F →
      ∃ Y Y' : WilkiesDesign.E.SemiPf (p + q), Y.fmt ≤ a ∧ Y.deg ≤ b.eval X.deg ∧ Y'.fmt ≤ a ∧
        Y'.deg ≤ b.eval X.deg ∧ Y.set = WilkiesDesign.E.fiberClosure X.set ∧
        Y'.set = WilkiesDesign.E.fiberClosure X.set \ X.set)
    (F : ℕ) :
    ∃ (a : ℕ) (b : Polynomial ℕ),
      ∀ (n m : ℕ) (X : WilkiesDesign.E.SemiPf (n + (m + 1))), X.fmt ≤ F →
        ∃ L : List (WilkiesDesign.E.SemiPf (n + (m + 1))),
          L.length ≤ b.eval X.deg ∧
          (∀ Y ∈ L, Y.fmt ≤ a ∧ Y.deg ≤ b.eval X.deg ∧ Y.set ⊆ closure X.set ∧
            ∀ x, (WilkiesDesign.E.fiber Y.set x).Finite) ∧
          WilkiesDesign.E.projFirst n (m + 1) '' closure X.set =
            ⋃ Y ∈ L, WilkiesDesign.E.projFirst n (m + 1) '' Y.set := by
  -- Step 1: `E6` presents the *topological* closure of `X` as a semi-Pfaffian set `W`
  -- of format `≤ a₆` and degree `≤ b₆ X.deg`.
  obtain ⟨a₆, b₆, h₆⟩ := Work.WilE7.E6closure hE6 F
  -- Step 2: the fibre cut (`Work.CoreStep.fiberCut_len`) of a set of format `≤ a₆`,
  -- with its format and degree bounds `(a_fc, b_fc)`.
  obtain ⟨a, b, hb⟩ := Work.CoreStep.fiberCut_len hE2 hE5 hE6 a₆
  refine ⟨a, b.comp b₆, ?_⟩
  intro n m X hX
  obtain ⟨W, -, hWf, hWd, -, -, hWs, -⟩ := h₆ (n + (m + 1)) X hX
  obtain ⟨L, hlen, hpieces, hcov⟩ := hb n (m + 1) W hWf
  refine ⟨L, ?_, ?_, ?_⟩
  · -- length: `|L| ≤ b_fc(W.deg) ≤ b_fc(b₆(X.deg)) = (b_fc ∘ b₆)(X.deg)`
    rw [poly_eval_comp]
    exact le_trans hlen (poly_eval_mono b hWd)
  · intro Z hZ
    obtain ⟨hsub, hf, hd, hfin⟩ := hpieces Z hZ
    refine ⟨hf, ?_, ?_, hfin⟩
    · -- degree of a piece
      rw [poly_eval_comp]
      exact le_trans hd (poly_eval_mono b hWd)
    · -- containment in `closure X.set`
      calc Z.set ⊆ closure W.set := hsub
        _ = closure (closure X.set) := by rw [hWs]
        _ = closure X.set := closure_closure
  · -- the covering equality
    rw [← hWs]
    exact hcov

end Work.WilE7.coreLT_succ
