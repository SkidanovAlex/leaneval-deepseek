import Mathlib
import Submission.Work.ZeroEst.defs
import Submission.Work.ZeroEst.fg_order_bound
import Submission.Work.ZeroEst.combination_mem_span

namespace Work.ZeroEst

/-- **Lang's Lemma 2.1 (fixed degree bound).**  For a fixed degree bound `d`, the order of a
nonzero combination `Σ_i P_i f_i` with `deg P_i ≤ d` is bounded by a constant depending only on
`f` and `d`.

The combination `Σ_i P_i f_i` lies in the finitely generated `ℚ`-submodule
`E = span {X^j · f i : j ≤ d, i}` of `ℚ⟦X⟧`, and `Work.ZeroEst.fg_order_bound` bounds the order
of every nonzero element of such a submodule. -/
theorem fixed_deg_order_bound (m : ℕ) (f : Fin m → PowerSeries ℚ) (d : ℕ) :
    ∃ N : ℕ, ∀ (P : Fin m → Polynomial ℚ), (∀ i, (P i).degree ≤ (d : WithBot ℕ)) →
      (∑ i, (P i : PowerSeries ℚ) * f i) ≠ 0 →
      (∑ i, (P i : PowerSeries ℚ) * f i).order ≤ (N : ℕ∞) := by
  have hE : (Submodule.span ℚ (Set.range (fun (ij : Fin m × Fin (d + 1)) =>
        (PowerSeries.X : PowerSeries ℚ) ^ (ij.2 : ℕ) * f ij.1))).FG :=
    Submodule.fg_def.mpr ⟨_, Set.finite_range _, rfl⟩
  obtain ⟨N, hN⟩ := fg_order_bound _ hE
  exact ⟨N, fun P hP hne => hN _ (combination_mem_span m f d P hP) hne⟩

end Work.ZeroEst
