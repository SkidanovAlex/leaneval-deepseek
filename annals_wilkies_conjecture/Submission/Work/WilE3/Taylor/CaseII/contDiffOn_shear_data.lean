import Mathlib
import Submission.Work.WilE3.Taylor.CaseII.PertShear

namespace Work.WilE3.Taylor.CaseII

open WilkiesDesign.E

/-- `eaEval c Q` is `C¹` (indeed analytic) on any set, since it is analytic everywhere. -/
lemma contDiffOn_eaEval {k r : ℕ} (c : EAChain k r) (Q : EAPoly k r) (s : Set (Fin k → ℝ)) :
    ContDiffOn ℝ 1 (fun x : Fin k → ℝ => eaEval c Q x) s :=
  fun x _ => (Work.WilE3.eaEval_analytic c Q x).contDiffAt.contDiffWithinAt

/-- The shear data `aSh`, `bSh` and the pivot `eaEval c Φ` are `C¹` on the open set `Ush` where the
common denominator `G · ∂_{i₀}Φ` does not vanish (`aSh`, `bSh` are quotients of `eaEval`s of
polynomials; all of them are analytic by `Work.WilE3.eaEval_analytic`). -/
theorem contDiffOn_shear_data {k r : ℕ} (c : WilkiesDesign.E.EAChain k r)
    (Φ : WilkiesDesign.E.EAPoly k r) (i₀ : Fin k) :
    ContDiffOn ℝ 1 (Work.WilE3.Taylor.CaseII.aSh c Φ i₀) (Work.WilE3.Taylor.CaseII.Ush c Φ i₀)
      ∧ ContDiffOn ℝ 1 (Work.WilE3.Taylor.CaseII.bSh c Φ i₀) (Work.WilE3.Taylor.CaseII.Ush c Φ i₀)
      ∧ ContDiffOn ℝ 1 (fun x : Fin k → ℝ => WilkiesDesign.E.eaEval c Φ x)
          (Work.WilE3.Taylor.CaseII.Ush c Φ i₀) := by
  refine ⟨?_, ?_, ?_⟩
  · -- `aSh`: each component is either the constant `0` (slot `i₀`) or a quotient of `eaEval`s.
    rw [contDiffOn_pi]
    intro i
    by_cases hi : i = i₀
    · exact (contDiffOn_const (c := (0 : ℝ)) (s := Ush c Φ i₀)).congr
        (fun x _ => by simp [aSh, hi])
    · refine (ContDiffOn.div (contDiffOn_eaEval c (aNumP c Φ i₀ i) _)
        (contDiffOn_eaEval c (denP c Φ i₀) _) (fun x hx => hx)).congr ?_
      intro x _
      simp [aSh, hi]
  · -- `bSh`: same structure.
    rw [contDiffOn_pi]
    intro i
    by_cases hi : i = i₀
    · exact (contDiffOn_const (c := (0 : ℝ)) (s := Ush c Φ i₀)).congr
        (fun x _ => by simp [bSh, hi])
    · refine (ContDiffOn.div (contDiffOn_eaEval c (bNumP c Φ i) _)
        (contDiffOn_eaEval c (denP c Φ i₀) _) (fun x hx => hx)).congr ?_
      intro x _
      simp [bSh, hi]
  · exact contDiffOn_eaEval c Φ (Ush c Φ i₀)

end Work.WilE3.Taylor.CaseII
