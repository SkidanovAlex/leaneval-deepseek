/-
  `Work.CoreStep.piFamilyTopSingle`: the **per-index** form of `Work.CoreStep.piFamilyTop`.

  `piFamilyTop` gives, for a whole family `X : Fin k → SemiPf ((n+1)+m)`, a list `Pi` of absolute
  `Good` pieces such that

  * `⋃ i, π_{n+1}(X i) = ⋃ T ∈ Pi, π_{n+1}(absSet T)` (the **global** coverage), and
  * each `T ∈ Pi` has `π_{n+1}(absSet T) ⊆ π_{n+1}(X i_T)` for **some** `i_T` (provenance).

  The `Π_{K+1}`-compatibility argument of the `CoreLT_succ` assembly needs the **per-index**
  coverage: for each fixed `i`, the pieces with provenance `i` cover `π_{n+1}(X i)` *and* have
  their images inside it.  Both are obtained here by applying `piFamilyTop` to the one-element
  family `{X}`: the provenance becomes `π_{n+1}(T) ⊆ π_{n+1}(X)` and the coverage becomes
  `π_{n+1}(X) = ⋃ T ∈ Pi, π_{n+1}(T)`.

  Applying this to each member `X i` of a family and concatenating the lists therefore gives the
  per-index covering sub-lists of the assembly.
-/
import Mathlib
import Submission.Work.CoreStep.piFamilyTop

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.CoreStep

open WilkiesDesign WilkiesDesign.E

theorem piFamilyTopSingle
    (hFC : ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ),
      ∀ (n m : ℕ) (X : WilkiesDesign.E.SemiPf (n + m)), X.fmt ≤ F →
        ∃ L : List (WilkiesDesign.E.SemiPf (n + m)), L.length ≤ b.eval X.deg ∧
          (∀ Xh ∈ L, Xh.fmt ≤ a ∧ Xh.deg ≤ b.eval X.deg ∧
            ∀ x, (WilkiesDesign.E.fiber Xh.set x).Finite) ∧
          WilkiesDesign.E.projFirst n m '' X.set =
            ⋃ Xh ∈ L, WilkiesDesign.E.projFirst n m '' Xh.set)
    (hE5 : ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ),
      ∀ (p q : ℕ) (X : WilkiesDesign.E.SemiPf (p + q)), X.fmt ≤ F →
        ∃ L : List (WilkiesDesign.E.Stratum p q), L.length ≤ b.eval X.deg ∧
          (∀ S ∈ L, S.X.fmt ≤ a ∧ S.deg ≤ b.eval X.deg ∧ S.Good) ∧
          X.set = (⋃ S ∈ L, S.X.set) ∧
          L.Pairwise (fun S T => Disjoint S.X.set T.X.set))
    (F : ℕ) :
    ∃ (A : ℕ) (B : Polynomial ℕ) (N : MvPolynomial (Fin 2) ℕ),
      ∀ (D n m : ℕ) (X : WilkiesDesign.E.SemiPf ((n + 1) + m)),
        X.fmt ≤ F → X.deg ≤ D →
        ∃ Pi : List (WilkiesDesign.E.Stratum 0 ((n + 1) + m)),
          Pi.length ≤ MvPolynomial.eval ![D, 1] N ∧
          (∀ T ∈ Pi, T.Good ∧ T.X.fmt ≤ A ∧ T.deg ≤ B.eval D ∧
            (∀ x : Fin (n + 1) → ℝ,
              (WilkiesDesign.E.fiber (Work.WilE7.MainDesign.absSet T) x).Finite) ∧
            (∀ z ∈ T.X.set,
              Work.WilE7.MainDesign.projRank T z = (n + 1) + m - T.j) ∧
            WilkiesDesign.E.projFirst (n + 1) m '' (Work.WilE7.MainDesign.absSet T) ⊆
              WilkiesDesign.E.projFirst (n + 1) m '' X.set) ∧
          WilkiesDesign.E.projFirst (n + 1) m '' X.set =
            ⋃ T ∈ Pi, WilkiesDesign.E.projFirst (n + 1) m ''
              (Work.WilE7.MainDesign.absSet T) := by
  classical
  obtain ⟨A, B, N, hN⟩ := piFamilyTop hFC hE5 F
  refine ⟨A, B, N, ?_⟩
  intro D n m X hfmt hdeg
  obtain ⟨Pi, hlen, hgood, hcov⟩ :=
    hN D 1 n m (fun _ : Fin 1 => X) (fun _ => ⟨hfmt, hdeg⟩)
  refine ⟨Pi, hlen, ?_, ?_⟩
  · intro T hT
    obtain ⟨h1, h2, h3, h4, h5, i, hi⟩ := hgood T hT
    exact ⟨h1, h2, h3, h4, h5, by simpa using hi⟩
  · refine le_antisymm ?_ ?_
    · intro y hy
      rw [← hcov]
      exact Set.mem_iUnion.mpr ⟨0, by simpa using hy⟩
    · intro y hy
      rw [← hcov] at hy
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
      simpa using hi

end Work.CoreStep
