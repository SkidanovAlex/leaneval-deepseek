import Mathlib
import Submission.Work.WilE9G.Assembly.ambOf

namespace Work.WilE9G.Assembly

open WilkiesDesign WilkiesDesign.E

/-- Membership in a semi-Pfaffian set reindexed along the *inverse* of a coordinate equivalence:
`reindex e.symm X` is `X` read through the relabelling `e`, so evaluating at `fun j => z (e j)`
is evaluation at `z`. -/
theorem mem_reindex_symm {k K : ℕ} (e : Fin K ≃ Fin k) (X : SemiPf k) (z : Fin k → ℝ) :
    (fun j : Fin K => z (e j)) ∈ (Work.WilE7.SemiPf.reindex e.symm X).set ↔ z ∈ X.set := by
  rw [Work.WilE7.sp_reindex_set, Set.mem_ofPred_eq]
  have hcomp : (fun j : Fin k => (fun j : Fin K => z (e j)) (e.symm j)) = z := by
    funext j
    exact congrArg z (Equiv.apply_symm_apply e j)
  rw [hcomp]

theorem reindex_castEquiv_symm {N : ℕ} (X : WilkiesDesign.E.SemiPf N) :
    (∀ z : Fin N → ℝ,
        (fun i : Fin (0 + N) => z (Work.WilE9G.Amb.castEquiv N i)) ∈
          (Work.WilE7.SemiPf.reindex (Work.WilE9G.Amb.castEquiv N).symm X).set ↔ z ∈ X.set) ∧
      (Work.WilE7.SemiPf.reindex (Work.WilE9G.Amb.castEquiv N).symm X).fmt = X.fmt ∧
      (Work.WilE7.SemiPf.reindex (Work.WilE9G.Amb.castEquiv N).symm X).deg = X.deg ∧
      (Work.WilE7.SemiPf.reindex (Work.WilE9G.Amb.castEquiv N).symm X).basics.length =
        X.basics.length := by
  refine ⟨fun z => mem_reindex_symm (Work.WilE9G.Amb.castEquiv N) X z, ?_, ?_, ?_⟩
  · rw [Work.WilE8.Star.semipf_fmt_reindex]
    simp only [WilkiesDesign.E.SemiPf.fmt, Nat.zero_add]
  · exact Work.WilE8.Star.semipf_deg_reindex (Work.WilE9G.Amb.castEquiv N).symm X
  · change (List.map (Work.WilE7.Basic.reindex (Work.WilE9G.Amb.castEquiv N).symm) X.basics).length =
      X.basics.length
    exact List.length_map _

end Work.WilE9G.Assembly
