/-
  Area E7: `Work.WilE7.cover_cut_deg` — BV's fibre-cutting Lemma 8 *with the degree and count
  bookkeeping* (the counterpart of `Work.WilE7.cover_cut`, which tracks only the format).

  The recursion itself is `Work.WilE7.cover_cut_aux` (`Submission.Work.WilE7.Deg.Recursion`), whose
  bookkeeping data (the chosen `E5`/`E6` bounds, the iterated format/degree sequences, the child
  bound `brB` and the accumulated count bound `Kb`) live in `Submission.Work.WilE7.Deg.Seq` and
  whose elementary properties are in `Submission.Work.WilE7.Deg.SeqLemmas`.  This file only
  instantiates it: `a := Fb 0` (the iterated format bound) and `b := Kb k₀ + Pb 0`.
-/
import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE7.FiberCutDefs
import Submission.Work.WilE7.FiberCutInputs
import Submission.Work.WilE7.FiberCutCover
import Submission.Work.WilE7.Deg.Recursion

set_option autoImplicit false
noncomputable section
open Classical Topology
open scoped Topology
namespace Work.WilE7
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

theorem cover_cut_deg
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
        Y'.set = WilkiesDesign.E.fiberClosure X.set \ X.set)
    (hPC : Work.WilE7.ClosureProj) (hFD : Work.WilE7.FrontierDrop)
    (hCD : Work.WilE7.CritDrop) (hCW : Work.WilE7.CritWitness) (A₀ k₀ : ℕ) :
    ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (k A : ℕ) (n m : ℕ) (Ys : List (WilkiesDesign.E.Stratum n m))
      (D : ℕ),
      A ≤ A₀ → k ≤ k₀ → (∀ S ∈ Ys, S.Good) → (∀ S ∈ Ys, S.X.fmt ≤ A) →
      (∀ S ∈ Ys, S.deg ≤ D) → (∀ S ∈ Ys, S.j < m → m - S.j ≤ k) →
      ∃ L : List (WilkiesDesign.E.SemiPf (n + m)), L.length ≤ Ys.length * b.eval D ∧
        (∀ Xh ∈ L, Xh.fmt ≤ a ∧ Xh.deg ≤ b.eval D ∧ ∀ x, (WilkiesDesign.E.fiber Xh.set x).Finite) ∧
        (⋃ S ∈ Ys, WilkiesDesign.E.projFirst n m '' S.X.set) ⊆
          (⋃ Xh ∈ L, WilkiesDesign.E.projFirst n m '' Xh.set) ∧
        (⋃ Xh ∈ L, WilkiesDesign.E.projFirst n m '' Xh.set) ⊆
          (⋃ S ∈ Ys, WilkiesDesign.E.projFirst n m '' (WilkiesDesign.E.fiberClosure S.X.set)) := by
  refine ⟨Fb hE5 hE6 A₀ k₀ 0,
    Kb hE5 hE6 A₀ k₀ k₀ + Pb hE5 hE6 A₀ k₀ 0, ?_⟩
  intro k A n m Ys D hA hk hgood hfmt hdeg hbud
  by_cases hYs : Ys = []
  · subst hYs
    exact ⟨[], by simp, by simp, by simp, by simp⟩
  · obtain ⟨S₀, hS₀⟩ := List.exists_mem_of_ne_nil Ys hYs
    have hm : m ≤ A₀ := by
      have h1 : n + m ≤ S₀.X.fmt := by simp [SemiPf.fmt]
      have h2 : S₀.X.fmt ≤ A := hfmt S₀ hS₀
      omega
    have hfmt' : ∀ S ∈ Ys, S.X.fmt ≤ Fb hE5 hE6 A₀ k₀ k := by
      intro S hS
      exact le_trans (hfmt S hS) (le_trans hA (Fb_ge_A₀ hE5 hE6 A₀ k₀ k))
    have hdeg' : ∀ S ∈ Ys, S.deg ≤ (Pb hE5 hE6 A₀ k₀ k).eval D := by
      intro S hS
      exact le_trans (hdeg S hS) (degSeq_eval_ge hE5 hE6 A₀ D (k₀ - k))
    obtain ⟨L, hLen, hPieces, hCov, hSub⟩ :=
      cover_cut_aux hE5 hE6 A₀ k₀ hE2 hFD hCD hCW D k hk n m hm Ys hgood hfmt' hdeg' hbud
    refine ⟨L, ?_, ?_, hCov, hSub⟩
    · refine le_trans hLen (Nat.mul_le_mul_left _ ?_)
      rw [Polynomial.eval_add]
      exact le_trans (Kb_eval_mono hE5 hE6 A₀ k₀ D hk) (Nat.le_add_right _ _)
    · intro Xh hXh
      obtain ⟨h1, h2, h3⟩ := hPieces Xh hXh
      refine ⟨h1, ?_, h3⟩
      rw [Polynomial.eval_add]
      exact le_trans h2 (Nat.le_add_left _ _)

end Work.WilE7
