import Mathlib
import Submission.Work.WilE7.MainDesignDefs
import Submission.Work.WilE7.coreLT_succ.gcase_strata
import Submission.Work.WilE7.semiPf_normalize_exists

namespace Work.WilE7.coreLT_succ

open Work.WilE7.MainDesign

/-- **Frontier family.**  Over the trivial base (`p = 0`), `E6` produces the *ambient* frontier
`closure X \ X` of a semi-Pfaffian set as a `SemiPf` set of uniformly bounded format and degree
(`fiberClosure_zero` identifies the fibrewise closure with the topological closure at `p = 0`).
Stratifying that frontier with `E5` yields a family of `Good` absolute strata covering exactly
`closure T.X.set \ T.X.set`, of format `≤ A` and with degrees and length bounded by `B.eval D`
uniformly in the stratum `T` (only through its format `≤ F`) and in `D ≥ T.X.deg`. -/
theorem frontierFamily {n m : ℕ}
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
    ∃ (A : ℕ) (B : Polynomial ℕ),
      ∀ (T : WilkiesDesign.E.Stratum 0 (n + (m + 1))) (hT : T.Good) (hF : T.X.fmt ≤ F) (D : ℕ),
        T.X.deg ≤ D →
        ∃ L : List (WilkiesDesign.E.Stratum 0 (n + (m + 1))),
          (∀ S ∈ L, S.Good) ∧
          (∀ S ∈ L, S.X.fmt ≤ A ∧ S.deg ≤ B.eval D) ∧
          (∀ S ∈ L, S.X.set ⊆ closure T.X.set \ T.X.set) ∧
          ((closure T.X.set \ T.X.set) ⊆ ⋃ S ∈ L, S.X.set) ∧
          L.length ≤ B.eval D := by
  -- `E6` and `E5` with the format thresholds at which we will use them.
  obtain ⟨a₆, b₆, hE6'⟩ := hE6 F
  obtain ⟨a₅, b₅, hE5'⟩ := hE5 a₆
  refine ⟨a₅, b₅.comp b₆, ?_⟩
  intro T _hT hF D hD
  -- The ambient frontier `closure T.X.set \ T.X.set` is the `Y'` of `E6` over the trivial base.
  obtain ⟨Y, Y', _hYfmt, _hYdeg, hY'fmt, hY'deg, _hYset, hY'set⟩ :=
    hE6' 0 (n + (m + 1)) T.X hF
  have hfc : WilkiesDesign.E.fiberClosure T.X.set = closure T.X.set := fiberClosure_zero T.X.set
  have hY' : Y'.set = closure T.X.set \ T.X.set := by rw [hY'set, hfc]
  have hY'degD : Y'.deg ≤ b₆.eval D := le_trans hY'deg (eval_mono_nat b₆ hD)
  -- Stratify that frontier: `E5` at `p = 0`.
  obtain ⟨L, hLlen, hLprops, hLcov, _hLdisj⟩ := hE5' 0 (n + (m + 1)) Y' hY'fmt
  refine ⟨L, ?_, ?_, ?_, ?_, ?_⟩
  · intro S hS
    exact (hLprops S hS).2.2
  · intro S hS
    refine ⟨(hLprops S hS).1, ?_⟩
    calc S.deg ≤ b₅.eval Y'.deg := (hLprops S hS).2.1
      _ ≤ b₅.eval (b₆.eval D) := eval_mono_nat b₅ hY'degD
      _ = (b₅.comp b₆).eval D := by rw [Polynomial.eval_comp]
  · intro S hS z hz
    have h1 : z ∈ Y'.set := by
      rw [hLcov]
      exact Set.mem_iUnion₂.mpr ⟨S, hS, hz⟩
    rwa [hY'] at h1
  · intro z hz
    have h1 : z ∈ Y'.set := by rwa [hY']
    rwa [← hLcov]
  · calc L.length ≤ b₅.eval Y'.deg := hLlen
      _ ≤ b₅.eval (b₆.eval D) := eval_mono_nat b₅ hY'degD
      _ = (b₅.comp b₆).eval D := by rw [Polynomial.eval_comp]

end Work.WilE7.coreLT_succ
