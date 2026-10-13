import Mathlib
import Submission.Work.WilE7.Defs
import Submission.Work.WilE7.sections_of_covering
import Submission.Work.WilE7.Prop9_dim_one
import Submission.Work.WilE7.singleton_cylDecomp
import Submission.Work.WilE7.decomp_of_sections
import Submission.Work.WilE7.Endgame.Assembly

namespace Work.WilE7

theorem E7_prop_main_proved
    (hFC : ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (n m : ℕ) (X : WilkiesDesign.E.SemiPf (n + m)),
      X.fmt ≤ F →
      ∃ L : List (WilkiesDesign.E.SemiPf (n + m)), L.length ≤ b.eval X.deg ∧
        (∀ Xh ∈ L, Xh.fmt ≤ a ∧ Xh.deg ≤ b.eval X.deg ∧
          ∀ x, (WilkiesDesign.E.fiber Xh.set x).Finite) ∧
        WilkiesDesign.E.projFirst n m '' X.set =
          ⋃ Xh ∈ L, WilkiesDesign.E.projFirst n m '' Xh.set)
    (hE2 : ∀ F : ℕ, ∃ p : Polynomial ℕ, ∀ (k : ℕ) (X : WilkiesDesign.E.SemiPf k), X.fmt ≤ F →
      ∃ s : Finset (Fin k → ℝ), s.card ≤ p.eval X.deg ∧ (↑s : Set (Fin k → ℝ)) ⊆ X.set ∧
        ∀ x ∈ X.set, ∃ y ∈ s,
          connectedComponentIn X.set x = connectedComponentIn X.set y)
    (hE5 : ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (p q : ℕ) (X : WilkiesDesign.E.SemiPf (p + q)),
      X.fmt ≤ F →
      ∃ L : List (WilkiesDesign.E.Stratum p q), L.length ≤ b.eval X.deg ∧
        (∀ S ∈ L, S.X.fmt ≤ a ∧ S.deg ≤ b.eval X.deg ∧ S.Good) ∧
        X.set = (⋃ S ∈ L, S.X.set) ∧
        L.Pairwise (fun S T => Disjoint S.X.set T.X.set))
    (hE6 : ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (p q : ℕ) (X : WilkiesDesign.E.SemiPf (p + q)),
      X.fmt ≤ F →
      ∃ Y Y' : WilkiesDesign.E.SemiPf (p + q), Y.fmt ≤ a ∧ Y.deg ≤ b.eval X.deg ∧ Y'.fmt ≤ a ∧
        Y'.deg ≤ b.eval X.deg ∧ Y.set = WilkiesDesign.E.fiberClosure X.set ∧
        Y'.set = WilkiesDesign.E.fiberClosure X.set \ X.set) :
    ∀ F n : ℕ, ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ) (c : Polynomial ℕ),
      ∀ (D k m : ℕ) (X : Fin k → WilkiesDesign.E.SemiPf (n + m)),
        (∀ i, (X i).fmt ≤ F ∧ (X i).deg ≤ D) →
        ∃ C : Finset (Set (Fin n → ℝ)),
          WilkiesDesign.E.IsCylDecompOn n (WilkiesDesign.E.cubeC n) C ∧
          (∀ i, ∀ κ ∈ C,
            κ ⊆ WilkiesDesign.E.projFirst n m '' (X i).set ∨
              Disjoint κ (WilkiesDesign.E.projFirst n m '' (X i).set)) ∧
          C.card ≤ MvPolynomial.eval ![D, k] b ∧
          ∀ κ ∈ C, WilkiesDesign.E.Star a (c.eval D) n κ ∧ WilkiesDesign.E.SubPf n κ :=
  Work.WilE7.Endgame.E7_prop_main_proved_of_hyp hFC hE2 hE5 hE6

end Work.WilE7
