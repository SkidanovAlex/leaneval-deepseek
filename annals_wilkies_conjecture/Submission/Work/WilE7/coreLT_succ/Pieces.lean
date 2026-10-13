/-
  Area E7 / `CoreLT_succ`: the **transported piece family**.

  `Work.CoreStep.piPiecesIdx` gives, for a family `X : Fin k → SemiPf ((n+1)+m)` of format `≤ F`
  and degree `≤ D`, a list of absolute `Good` strata in the `((n+1), m)` frame, each of
  `π_{n+1}`-rank `= dim`, with per-index provenance and per-index coverage
  `π_{n+1}(X i) = ⋃_{p.1 = i} π_{n+1}(absSet p.2)`.

  All the cell machinery of the case analysis (`gcase_strata`, `sigmaFamily_len`,
  `sheets_over_cell_of_hrank`, `multiStrata_cells_sorted`, …) is stated in the `(n, m+1)` frame,
  where the vertical coordinate is the LAST fibre coordinate and the projection to the cells is
  `Work.CoreStep.projTop n m`.  `Work.WilE7.coreLT_succ.stratReindex_projTop` moves a single
  stratum across the frame change, preserving `j`, `X.r`, `deg`, `Good` and the `projTop`-image.

  This file performs that transport for the whole indexed list, giving the piece family in the
  form the rest of the `CoreLT_succ` assembly consumes.
-/
import Mathlib
import Submission.Work.CoreStep.piPiecesIdx
import Submission.Work.WilE7.coreLT_succ.stratReindex_projTop
import Submission.Work.WilE7.CoreStep.ProjTopDefs

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7.coreLT_succ

open WilkiesDesign WilkiesDesign.E
open Work.WilE7.MainDesign
open Work.WilE7.CoreStep (projTop)

/-- **The piece family in the `(n, m+1)` frame.**  Every member is absolute `Good` with
`π_{n+1}`-rank `= dim`, bounded format `≤ A` and degree `≤ B.eval D`, its `projTop`-image lies in
`π_{n+1}(X i)` for its own index `i`, and the pieces of index `i` cover `π_{n+1}(X i)` exactly. -/
theorem piecesFrame
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
      ∀ (D k n m : ℕ) (X : Fin k → WilkiesDesign.E.SemiPf (n + 1 + m)),
        (∀ i, (X i).fmt ≤ F ∧ (X i).deg ≤ D) →
        ∃ Pi : List (Fin k × WilkiesDesign.E.Stratum 0 (n + (m + 1))),
          Pi.length ≤ MvPolynomial.eval ![D, k] N ∧
          (∀ p ∈ Pi,
              (p.2).Good ∧ (p.2).X.fmt ≤ A ∧ (p.2).deg ≤ B.eval D ∧
              (∀ z' ∈ (p.2).X.set,
                Module.finrank ℝ
                    ↥(Submodule.map (Work.WilE7.CoreStep.projTopLin n m ∘ₗ
                        Work.WilE7.CoreStep.absPtLin (n + (m + 1)))
                      (MainDesign.jac (p.2) z').ker) =
                  n + (m + 1) - (p.2).j) ∧
              projTop n m '' MainDesign.absSet (p.2) ⊆
                WilkiesDesign.E.projFirst (n + 1) m '' (X p.1).set) ∧
          (∀ i : Fin k, WilkiesDesign.E.projFirst (n + 1) m '' (X i).set =
            ⋃ p ∈ Pi.filter (fun p => p.1 = i),
              projTop n m '' MainDesign.absSet (p.2)) := by
  classical
  obtain ⟨A₀, B₀, N, hN⟩ := Work.CoreStep.piPiecesIdx hFC hE5 F
  refine ⟨A₀, B₀, N, ?_⟩
  intro D k n m X hX
  obtain ⟨Pi₀, hlen₀, hgood₀, hcov₀⟩ := hN D k n m X hX
  -- the π_{n+1}-rank hypothesis of `stratReindex_projTop` for a member of `Pi₀`
  have hrankeq : ∀ (p : Fin k × WilkiesDesign.E.Stratum 0 ((n + 1) + m)),
      p ∈ Pi₀ → ∀ z ∈ (p.2).X.set, MainDesign.projRank (p.2) z = (n + 1) + m - (p.2).j :=
    fun p hp => (hgood₀ p hp).2.2.2.2.1
  have hex : ∀ p : {p // p ∈ Pi₀},
      ∃ T' : WilkiesDesign.E.Stratum 0 (n + (m + 1)),
        T'.j = p.1.2.j ∧ T'.X.r = p.1.2.X.r ∧ T'.deg = p.1.2.deg ∧
        (T'.Good ↔ p.1.2.Good) ∧
        projTop n m '' MainDesign.absSet T' =
          WilkiesDesign.E.projFirst (n + 1) m '' MainDesign.absSet p.1.2 ∧
        (∀ z' ∈ T'.X.set,
          Module.finrank ℝ
              ↥(Submodule.map (Work.WilE7.CoreStep.projTopLin n m ∘ₗ
                  Work.WilE7.CoreStep.absPtLin (n + (m + 1))) (MainDesign.jac T' z').ker) =
            n + (m + 1) - T'.j) :=
    fun p => stratReindex_projTop p.1.2 (hrankeq p.1 p.2)
  choose res hres using hex
  let Pi : List (Fin k × WilkiesDesign.E.Stratum 0 (n + (m + 1))) :=
    Pi₀.attach.map (fun p => (p.1.1, res p))
  have hmem : ∀ q : Fin k × WilkiesDesign.E.Stratum 0 (n + (m + 1)),
      q ∈ Pi ↔ ∃ p : {p // p ∈ Pi₀}, (p.1.1, res p) = q := by
    intro q
    simp only [Pi, List.mem_map, List.mem_attach, true_and]
  have hsnd : ∀ p : {p // p ∈ Pi₀}, (p.1.1, res p) ∈ Pi :=
    fun p => (hmem _).mpr ⟨p, rfl⟩
  refine ⟨Pi, ?_, ?_, ?_⟩
  · -- length
    have h1 : Pi.length = Pi₀.length := by
      simp only [Pi, List.length_map, List.length_attach]
    rw [h1]
    exact hlen₀
  · -- the per-piece properties
    intro q hq
    rw [hmem] at hq
    obtain ⟨p, rfl⟩ := hq
    obtain ⟨hpGood, hpFmt, hpDeg, -, -, hpSub⟩ := hgood₀ p.1 p.2
    obtain ⟨hj, hr, hdeg, hgood, himg, hrank⟩ := hres p
    refine ⟨hgood.mpr hpGood, ?_, ?_, hrank, ?_⟩
    · -- format
      have hfmt : (res p).X.fmt = p.1.2.X.fmt := by
        unfold WilkiesDesign.E.SemiPf.fmt
        rw [hr]
        omega
      rw [hfmt]
      exact hpFmt
    · -- degree
      rw [hdeg]
      exact hpDeg
    · -- provenance
      rw [himg]
      exact hpSub
  · -- per-index coverage
    intro i
    rw [hcov₀ i]
    apply Set.Subset.antisymm
    · intro y hy
      obtain ⟨⟨i₀, T₀⟩, hT, hyT⟩ := Set.mem_iUnion₂.mp hy
      rw [List.mem_filter] at hT
      obtain ⟨hTPi, hTi⟩ := hT
      refine Set.mem_iUnion₂.mpr ⟨(i₀, res ⟨(i₀, T₀), hTPi⟩), ?_, ?_⟩
      · rw [List.mem_filter]
        exact ⟨hsnd ⟨(i₀, T₀), hTPi⟩, hTi⟩
      · rw [hres ⟨(i₀, T₀), hTPi⟩ |>.2.2.2.2.1]
        exact hyT
    · intro y hy
      obtain ⟨q, hq, hyq⟩ := Set.mem_iUnion₂.mp hy
      rw [List.mem_filter] at hq
      obtain ⟨hqPi, hqi⟩ := hq
      obtain ⟨p, hp⟩ := (hmem q).mp hqPi
      have hq1 : q.1 = p.1.1 := by rw [← hp]
      have hq2 : q.2 = res p := by rw [← hp]
      have hbase : p.1.1 = i := by
        rw [← hq1]
        exact of_decide_eq_true hqi
      refine Set.mem_iUnion₂.mpr ⟨p.1, ?_, ?_⟩
      · rw [List.mem_filter]
        exact ⟨p.2, by simp [hbase]⟩
      · rw [← hres p |>.2.2.2.2.1, ← hq2]
        exact hyq

end Work.WilE7.coreLT_succ
