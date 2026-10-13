/-
  Area E7: the four holes of the area other than `E7_fiber_cut` and `E7_prop_main`,
  proved from BV Proposition 9 (`Work.WilE7.Prop9`, the frozen `E7_prop_main`
  verbatim) together with the vocabulary in `Submission.Work.WilE7.Defs` and the
  assembly lemma `Work.WilE7.star_central`.

  The `_proved` statements are in namespace `WilkiesDesign.E` (at the end of the file);
  the `_gen` lemmas in namespace `Work.WilE7` are the same proofs with the assembly
  lemma passed as the explicit hypothesis `StarCentral`.

  Two interfaces are provided for each of the four holes below:
  * `E7_bv_main_proved (h9 : Work.WilE7.Prop9)` etc., from BV's Proposition 9 — this is the
    shape the downstream consumers (`Submission.Work.WilFinal.WireOfProp9`, and the areas
    E8/E9 via their own hypothesis parameters) are wired against;
  * `E7_bv_main_proved_hyp (hE2) (hE5) (hE6)` etc., with the two other areas' statements
    `E2_components`, `E5_strat`, `E6_fiber_closure` copied verbatim as leading hypotheses.
  The translation is `Work.WilE7.Prop9_of_hyp` (also exported as
  `WilkiesDesign.E.Prop9_proved`), which derives `Prop9` from `E2`/`E5`/`E6` through
  `Work.WilE7.E7_fiber_cut_proved` and `Work.WilE7.E7_prop_main_proved`.
-/
import Mathlib
import Submission.Work.WilE7.Defs
import Submission.Work.WilE7.Prop9
import Submission.Work.WilE7.cells_select
import Submission.Work.WilE7.cells
import Submission.Work.WilE7.subPf_algebra
import Submission.Work.WilE7.s_union_tools
import Submission.Work.WilE7.star_central
import Submission.Work.WilE7.set_glue
import Submission.Work.WilE7.star_algebra
import Submission.Work.WilE7.star_proj
import Submission.Work.WilE7.list_filter
import Submission.Work.WilE7.list_sum_tools
import Submission.Work.WilE7.poly_bound
import Submission.Work.WilE7.E7_fiber_cut_proved
import Submission.Work.WilE7.E7_prop_main_proved

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Classical
namespace Work.WilE7
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

/-- The conclusion of the one-stop assembly lemma `star_central`. -/
def StarCentral : Prop :=
  ∀ (F n : ℕ), ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ) (c : Polynomial ℕ),
    ∀ (D : ℕ) (L : List (StarPiece n)),
      (∀ P ∈ L, P.X.fmt ≤ F) → (∀ P ∈ L, P.X.deg ≤ D) →
      ∃ C : Finset (Set (Fin n → ℝ)), IsCylDecompOn n (cubeC n) C ∧
        (∀ P ∈ L, ∀ κ ∈ C, κ ⊆ P.set ∨ Disjoint κ P.set) ∧
        C.card ≤ MvPolynomial.eval ![D, L.length] b ∧
        ∀ κ ∈ C, Star a (c.eval D) n κ

/-! ### The three inputs of BV's Proposition 9, as `Prop`

These are `abbrev`s only so that the plumbing below is readable; the public theorems at the end of
the file carry the frozen statements *verbatim* as their hypotheses. -/

/-- The frozen `WilkiesDesign.E.E2_components` (BV via Khovanskii/Morse). -/
abbrev E2_stmt : Prop :=
  ∀ F : ℕ, ∃ p : Polynomial ℕ, ∀ (k : ℕ) (X : SemiPf k), X.fmt ≤ F →
    ∃ s : Finset (Fin k → ℝ), s.card ≤ p.eval X.deg ∧ (↑s : Set (Fin k → ℝ)) ⊆ X.set ∧
      ∀ x ∈ X.set, ∃ y ∈ s,
        connectedComponentIn X.set x = connectedComponentIn X.set y

/-- The frozen `WilkiesDesign.E.E5_strat`. -/
abbrev E5_stmt : Prop :=
  ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (p q : ℕ) (X : SemiPf (p + q)), X.fmt ≤ F →
    ∃ L : List (Stratum p q), L.length ≤ b.eval X.deg ∧
      (∀ S ∈ L, S.X.fmt ≤ a ∧ S.deg ≤ b.eval X.deg ∧ S.Good) ∧
      X.set = (⋃ S ∈ L, S.X.set) ∧
      L.Pairwise (fun S T => Disjoint S.X.set T.X.set)

/-- The frozen `WilkiesDesign.E.E6_fiber_closure`. -/
abbrev E6_stmt : Prop :=
  ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (p q : ℕ) (X : SemiPf (p + q)), X.fmt ≤ F →
    ∃ Y Y' : SemiPf (p + q), Y.fmt ≤ a ∧ Y.deg ≤ b.eval X.deg ∧ Y'.fmt ≤ a ∧
      Y'.deg ≤ b.eval X.deg ∧ Y.set = fiberClosure X.set ∧
      Y'.set = fiberClosure X.set \ X.set

/-- **BV Proposition 9** from the three inputs: fibre cutting (`E7_fiber_cut`, itself from
`E2`/`E5`/`E6`) turns `Prop9` into a theorem. -/
theorem Prop9_of_hyp (hE2 : E2_stmt) (hE5 : E5_stmt) (hE6 : E6_stmt) : Prop9 :=
  Work.WilE7.E7_prop_main_proved (Work.WilE7.E7_fiber_cut_proved hE2 hE5 hE6) hE2 hE5 hE6

/-! ### E7f: Gabrielov's complement theorem, from Proposition 9 -/

theorem subpf_compl_gen (h9 : Prop9) :
    ∀ {n : ℕ} (Y : Set (Fin n → ℝ)), SubPf n Y → SubPf n (cubeC n \ Y) := by
  intro n Y hY
  obtain ⟨m, X, rfl⟩ := hY
  obtain ⟨a, b, c, h9'⟩ := h9 X.fmt n
  obtain ⟨C, hCyl, hcompat, -, hcell⟩ :=
    h9' X.deg 1 m (fun _ => X) (fun _ => ⟨le_rfl, le_rfl⟩)
  obtain ⟨-, -, hsublem, hcovlem, -⟩ := Work.WilE7.cells
  have hsub : ∀ κ ∈ C, κ ⊆ cubeC n := hsublem hCyl
  have hcov : cubeC n ⊆ ⋃₀ (C : Set (Set (Fin n → ℝ))) := by
    rw [hcovlem hCyl]
  have hcomp : ∀ κ ∈ C,
      κ ⊆ projFirst n m '' X.set ∨ Disjoint κ (projFirst n m '' X.set) :=
    fun κ hκ => hcompat 0 κ hκ
  have hsel := Work.WilE7.cells_select.1 (C := C) (Y := projFirst n m '' X.set) hsub hcov hcomp
  have hsubPf : ∀ κ ∈ Work.WilE7.cellsOutside C (projFirst n m '' X.set), SubPf n κ := by
    intro κ hκ
    exact (hcell κ (Work.WilE7.mem_cellsOutside.mp hκ).1).2
  have := Work.WilE7.s_union_tools.2 (Work.WilE7.cellsOutside C (projFirst n m '' X.set)) hsubPf
  rwa [hsel] at this

/-! ### E7d: the complement of a *-set (BV Theorem 2, ¬-case) -/

theorem star_compl_gen (hsc : StarCentral) :
    ∀ F n : ℕ, ∃ (a : ℕ) (p : Polynomial ℕ),
      ∀ (D : ℕ) (Y : Set (Fin n → ℝ)), Star F D n Y →
        Star a (p.eval D) n (cubeC n \ Y) := by
  intro F n
  obtain ⟨a, b, c, hsc'⟩ := hsc F n
  obtain ⟨q, hq⟩ := (Work.WilE7.poly_bound b).2.1
  refine ⟨a, q * c, ?_⟩
  intro D Y hStar
  obtain ⟨L, hYL, hfmt, hdeg⟩ := hStar
  have hKsub : ∀ P ∈ L.filter (fun P => P.X.deg ≠ 0), P ∈ L :=
    fun P hP => List.mem_of_mem_filter hP
  have hKfmt : ∀ P ∈ L.filter (fun P => P.X.deg ≠ 0), P.X.fmt ≤ F :=
    fun P hP => hfmt P (hKsub P hP)
  have hKdeg : ∀ P ∈ L.filter (fun P => P.X.deg ≠ 0), P.X.deg ≤ D := by
    intro P hP
    have h2 := Work.WilE7.list_sum_tools.2.1 (L.filter (fun P => P.X.deg ≠ 0)) P hP
    have h3 := Work.WilE7.list_sum_tools.1 L
    omega
  have hKlen : (L.filter (fun P => P.X.deg ≠ 0)).length ≤ D + 1 := by
    have h1 := (Work.WilE7.list_filter.1 L).2
    have h2 := Work.WilE7.list_sum_tools.1 L
    omega
  obtain ⟨C, hCyl, hcompatK, hcard, hstar⟩ := hsc' D _ hKfmt hKdeg
  have htriv : ∀ P ∈ L, P ∉ L.filter (fun P => P.X.deg ≠ 0) →
      P.set = ∅ ∨ P.set = cubeC n := (Work.WilE7.list_filter.1 L).1
  obtain ⟨-, -, hsublem, hcovlem, -⟩ := Work.WilE7.cells
  have hsub : ∀ κ ∈ C, κ ⊆ cubeC n := hsublem hCyl
  have hcov : cubeC n ⊆ ⋃₀ (C : Set (Set (Fin n → ℝ))) := by rw [hcovlem hCyl]
  have hcompatU : ∀ κ ∈ C, κ ⊆ (⋃ P ∈ L, P.set) ∨ Disjoint κ (⋃ P ∈ L, P.set) :=
    Work.WilE7.cells_select.2.2.1 hsub hKsub htriv hcompatK
  have hcompatY : ∀ κ ∈ C, κ ⊆ Y ∨ Disjoint κ Y := by
    intro κ hκ
    rw [hYL]
    exact hcompatU κ hκ
  have hsel := Work.WilE7.cells_select.1 (C := C) (Y := Y) hsub hcov hcompatY
  have hselStar : ∀ κ ∈ Work.WilE7.cellsOutside C Y, Star a (c.eval D) n κ :=
    fun κ hκ => hstar κ (Work.WilE7.mem_cellsOutside.mp hκ).1
  have hunion := Work.WilE7.s_union_tools.1 (Work.WilE7.cellsOutside C Y) a (c.eval D) hselStar
  rw [hsel] at hunion
  have hcardB : (Work.WilE7.cellsOutside C Y).card ≤ b.eval ![D, D + 1] := by
    refine le_trans (le_trans (Work.WilE7.card_cellsOutside_le C Y) hcard) ?_
    exact (Work.WilE7.poly_bound b).2.2.2 D _ (D + 1) hKlen
  have hbound : (Work.WilE7.cellsOutside C Y).card * c.eval D ≤ (q * c).eval D := by
    rw [Polynomial.eval_mul, hq D]
    exact Nat.mul_le_mul_right _ hcardB
  exact Work.WilE7.star_algebra.2.1 le_rfl hbound hunion

/-! ### E7e: the intersection of *-sets (BV Theorem 2, ∧-case) -/

theorem star_inter_gen (hsc : StarCentral) :
    ∀ F n : ℕ, ∃ (a : ℕ) (p : Polynomial ℕ),
      ∀ (k : ℕ) (D : Fin k → ℕ) (Y : Fin k → Set (Fin n → ℝ)),
        (∀ i, Star F (D i) n (Y i)) →
        Star a (p.eval (∑ i, D i)) n (cubeC n ∩ ⋂ i, Y i) := by
  intro F n
  obtain ⟨a, b, c, hsc'⟩ := hsc F n
  obtain ⟨q, hq⟩ := (Work.WilE7.poly_bound b).1
  refine ⟨a, q * c, ?_⟩
  intro k D Y hY
  choose L hL using hY
  have hKsub : ∀ i, ∀ P ∈ (L i).filter (fun P => P.X.deg ≠ 0), P ∈ L i :=
    fun i P hP => List.mem_of_mem_filter hP
  have htriv : ∀ i, ∀ P ∈ L i, P ∉ (L i).filter (fun P => P.X.deg ≠ 0) →
      P.set = ∅ ∨ P.set = cubeC n := fun i => (Work.WilE7.list_filter.1 (L i)).1
  have hmemTot : ∀ (i : Fin k) (P : StarPiece n),
      P ∈ (L i).filter (fun P => P.X.deg ≠ 0) →
      P ∈ List.flatten (List.ofFn fun i => (L i).filter (fun P => P.X.deg ≠ 0)) := by
    intro i P hP
    rw [(Work.WilE7.list_filter.2.2 (fun i => (L i).filter (fun P => P.X.deg ≠ 0)) P)]
    exact ⟨i, hP⟩
  have hfmtTot : ∀ P ∈ List.flatten (List.ofFn fun i => (L i).filter (fun P => P.X.deg ≠ 0)),
      P.X.fmt ≤ F := by
    intro P hP
    rw [(Work.WilE7.list_filter.2.2 (fun i => (L i).filter (fun P => P.X.deg ≠ 0)) P)] at hP
    obtain ⟨i, hiP⟩ := hP
    exact (hL i).2.1 P (hKsub i P hiP)
  have hdegTot : ∀ P ∈ List.flatten (List.ofFn fun i => (L i).filter (fun P => P.X.deg ≠ 0)),
      P.X.deg ≤ ∑ i, D i := by
    intro P hP
    rw [(Work.WilE7.list_filter.2.2 (fun i => (L i).filter (fun P => P.X.deg ≠ 0)) P)] at hP
    obtain ⟨i, hiP⟩ := hP
    have h2 := Work.WilE7.list_sum_tools.2.1 ((L i).filter (fun P => P.X.deg ≠ 0)) P hiP
    have h3 := Work.WilE7.list_sum_tools.1 (L i)
    have h4 := (hL i).2.2
    have h5 : D i ≤ ∑ j, D j := Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
  have hlenTot : (List.flatten (List.ofFn fun i => (L i).filter (fun P => P.X.deg ≠ 0))).length
      ≤ ∑ i, D i := by
    have h1 := Work.WilE7.list_filter.2.1 (fun i => (L i).filter (fun P => P.X.deg ≠ 0))
    have h2 : ∑ i, ((L i).filter (fun P => P.X.deg ≠ 0)).length ≤
        ∑ i, ((L i).map fun P => P.X.deg).sum :=
      Finset.sum_le_sum fun i _ => (Work.WilE7.list_filter.1 (L i)).2
    have h3 : ∑ i, ((L i).map fun P => P.X.deg).sum ≤ ∑ i, D i :=
      Finset.sum_le_sum fun i _ => (hL i).2.2
    omega
  obtain ⟨C, hCyl, hcompatTot, hcard, hstar⟩ := hsc' (∑ i, D i) _ hfmtTot hdegTot
  obtain ⟨-, -, hsublem, hcovlem, -⟩ := Work.WilE7.cells
  have hsub : ∀ κ ∈ C, κ ⊆ cubeC n := hsublem hCyl
  have hcov : cubeC n ⊆ ⋃₀ (C : Set (Set (Fin n → ℝ))) := by rw [hcovlem hCyl]
  have hcompatK : ∀ i, ∀ P ∈ (L i).filter (fun P => P.X.deg ≠ 0), ∀ κ ∈ C,
      κ ⊆ P.set ∨ Disjoint κ P.set := by
    intro i P hP κ hκ
    exact hcompatTot P (hmemTot i P hP) κ hκ
  have hcompatI := Work.WilE7.cells_select.2.2.2 (C := C) (L := L)
    (K := fun i => (L i).filter (fun P => P.X.deg ≠ 0)) hsub hKsub htriv hcompatK
  have hcompatY : ∀ i, ∀ κ ∈ C, κ ⊆ Y i ∨ Disjoint κ (Y i) := by
    intro i κ hκ
    have := hcompatI i κ hκ
    rwa [← (hL i).1] at this
  have hsel := Work.WilE7.cells_select.2.1 (C := C) (k := k) Y hsub hcov hcompatY
  have hselStar : ∀ κ ∈ Work.WilE7.cellsInside C Y, Star a (c.eval (∑ i, D i)) n κ :=
    fun κ hκ => hstar κ (Work.WilE7.mem_cellsInside.mp hκ).1
  have hunion := Work.WilE7.s_union_tools.1 (Work.WilE7.cellsInside C Y) a (c.eval (∑ i, D i))
    hselStar
  rw [hsel] at hunion
  have hcardD : (Work.WilE7.cellsInside C Y).card ≤ b.eval ![∑ i, D i, ∑ i, D i] := by
    refine le_trans (le_trans (Work.WilE7.card_cellsInside_le C Y) hcard) ?_
    exact (Work.WilE7.poly_bound b).2.2.2 (∑ i, D i) _ (∑ i, D i) (by omega)
  have hbound : (Work.WilE7.cellsInside C Y).card * c.eval (∑ i, D i) ≤ (q * c).eval (∑ i, D i) := by
    rw [Polynomial.eval_mul, hq (∑ i, D i)]
    exact Nat.mul_le_mul_right _ hcardD
  exact Work.WilE7.star_algebra.2.1 le_rfl hbound hunion

/-! ### E7c: sharp cell decomposition of *-sets (BV Theorem 1) -/

theorem bv_main_gen (hsc : StarCentral) :
    ∀ F n : ℕ, ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ) (c : Polynomial ℕ),
      ∀ (D k : ℕ) (Y : Fin k → Set (Fin n → ℝ)),
        (∀ i, Star F D n (Y i)) →
        ∃ C : Finset (Set (Fin n → ℝ)),
          IsCylDecompOn n (cubeC n) C ∧
          (∀ i, ∀ κ ∈ C, κ ⊆ Y i ∨ Disjoint κ (Y i)) ∧
          C.card ≤ MvPolynomial.eval ![D, k] b ∧
          ∀ κ ∈ C, Star a (c.eval D) n κ := by
  intro F n
  obtain ⟨a, b, c, hsc'⟩ := hsc F n
  obtain ⟨b', hb'⟩ := (Work.WilE7.poly_bound b).2.2.1
  refine ⟨a, b', c, ?_⟩
  intro D k Y hY
  choose L hL using hY
  have hKsub : ∀ i, ∀ P ∈ (L i).filter (fun P => P.X.deg ≠ 0), P ∈ L i :=
    fun i P hP => List.mem_of_mem_filter hP
  have htriv : ∀ i, ∀ P ∈ L i, P ∉ (L i).filter (fun P => P.X.deg ≠ 0) →
      P.set = ∅ ∨ P.set = cubeC n := fun i => (Work.WilE7.list_filter.1 (L i)).1
  have hmemTot : ∀ (i : Fin k) (P : StarPiece n),
      P ∈ (L i).filter (fun P => P.X.deg ≠ 0) →
      P ∈ List.flatten (List.ofFn fun i => (L i).filter (fun P => P.X.deg ≠ 0)) := by
    intro i P hP
    rw [(Work.WilE7.list_filter.2.2 (fun i => (L i).filter (fun P => P.X.deg ≠ 0)) P)]
    exact ⟨i, hP⟩
  have hfmtTot : ∀ P ∈ List.flatten (List.ofFn fun i => (L i).filter (fun P => P.X.deg ≠ 0)),
      P.X.fmt ≤ F := by
    intro P hP
    rw [(Work.WilE7.list_filter.2.2 (fun i => (L i).filter (fun P => P.X.deg ≠ 0)) P)] at hP
    obtain ⟨i, hiP⟩ := hP
    exact (hL i).2.1 P (hKsub i P hiP)
  have hdegTot : ∀ P ∈ List.flatten (List.ofFn fun i => (L i).filter (fun P => P.X.deg ≠ 0)),
      P.X.deg ≤ D := by
    intro P hP
    rw [(Work.WilE7.list_filter.2.2 (fun i => (L i).filter (fun P => P.X.deg ≠ 0)) P)] at hP
    obtain ⟨i, hiP⟩ := hP
    have h2 := Work.WilE7.list_sum_tools.2.1 ((L i).filter (fun P => P.X.deg ≠ 0)) P hiP
    have h3 := Work.WilE7.list_sum_tools.1 (L i)
    have h4 := (hL i).2.2
    omega
  have hlenTot : (List.flatten (List.ofFn fun i => (L i).filter (fun P => P.X.deg ≠ 0))).length
      ≤ k * (D + 1) := by
    have h1 := Work.WilE7.list_filter.2.1 (fun i => (L i).filter (fun P => P.X.deg ≠ 0))
    have h2 : ∑ i, ((L i).filter (fun P => P.X.deg ≠ 0)).length ≤
        ∑ i, ((L i).map fun P => P.X.deg).sum :=
      Finset.sum_le_sum fun i _ => (Work.WilE7.list_filter.1 (L i)).2
    have h3 : ∑ i, ((L i).map fun P => P.X.deg).sum ≤ ∑ _ : Fin k, D :=
      Finset.sum_le_sum fun i _ => (hL i).2.2
    have h4 : (∑ _ : Fin k, D) = k * D := by
      simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have h5 : (List.flatten (List.ofFn fun i => (L i).filter (fun P => P.X.deg ≠ 0))).length
        ≤ k * D := by
      rw [← h4]
      exact le_trans h1 (le_trans h2 h3)
    exact le_trans h5 (Nat.mul_le_mul_left k (Nat.le_succ D))
  obtain ⟨C, hCyl, hcompatTot, hcard, hstar⟩ := hsc' D _ hfmtTot hdegTot
  obtain ⟨-, -, hsublem, hcovlem, -⟩ := Work.WilE7.cells
  have hsub : ∀ κ ∈ C, κ ⊆ cubeC n := hsublem hCyl
  have hcompatK : ∀ i, ∀ P ∈ (L i).filter (fun P => P.X.deg ≠ 0), ∀ κ ∈ C,
      κ ⊆ P.set ∨ Disjoint κ P.set := by
    intro i P hP κ hκ
    exact hcompatTot P (hmemTot i P hP) κ hκ
  have hcompatI := Work.WilE7.cells_select.2.2.2 (C := C) (L := L)
    (K := fun i => (L i).filter (fun P => P.X.deg ≠ 0)) hsub hKsub htriv hcompatK
  refine ⟨C, hCyl, ?_, ?_, hstar⟩
  · intro i κ hκ
    have := hcompatI i κ hκ
    rwa [← (hL i).1] at this
  · calc C.card ≤ b.eval ![D,
        (List.flatten (List.ofFn fun i => (L i).filter (fun P => P.X.deg ≠ 0))).length] := hcard
      _ ≤ b.eval ![D, k * (D + 1)] :=
        (Work.WilE7.poly_bound b).2.2.2 D _ (k * (D + 1)) hlenTot
      _ = b'.eval ![D, k] := hb' D k

end Work.WilE7

namespace WilkiesDesign.E

open WilkiesConjecture WilkiesDesign

/-- **E7b** (the frozen `E7_prop_main` statement) from the three inputs `E2`, `E5`, `E6`, with
`E7_fiber_cut` absorbed: BV's Proposition 9. -/
theorem E7_prop_main_proved
    (hE2 : ∀ F : ℕ, ∃ p : Polynomial ℕ, ∀ (k : ℕ) (X : SemiPf k), X.fmt ≤ F →
      ∃ s : Finset (Fin k → ℝ), s.card ≤ p.eval X.deg ∧ (↑s : Set (Fin k → ℝ)) ⊆ X.set ∧
        ∀ x ∈ X.set, ∃ y ∈ s,
          connectedComponentIn X.set x = connectedComponentIn X.set y)
    (hE5 : ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (p q : ℕ) (X : SemiPf (p + q)), X.fmt ≤ F →
      ∃ L : List (Stratum p q), L.length ≤ b.eval X.deg ∧
        (∀ S ∈ L, S.X.fmt ≤ a ∧ S.deg ≤ b.eval X.deg ∧ S.Good) ∧
        X.set = (⋃ S ∈ L, S.X.set) ∧
        L.Pairwise (fun S T => Disjoint S.X.set T.X.set))
    (hE6 : ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (p q : ℕ) (X : SemiPf (p + q)), X.fmt ≤ F →
      ∃ Y Y' : SemiPf (p + q), Y.fmt ≤ a ∧ Y.deg ≤ b.eval X.deg ∧ Y'.fmt ≤ a ∧
        Y'.deg ≤ b.eval X.deg ∧ Y.set = fiberClosure X.set ∧
        Y'.set = fiberClosure X.set \ X.set) :
    ∀ F n : ℕ, ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ) (c : Polynomial ℕ),
      ∀ (D k m : ℕ) (X : Fin k → SemiPf (n + m)), (∀ i, (X i).fmt ≤ F ∧ (X i).deg ≤ D) →
      ∃ C : Finset (Set (Fin n → ℝ)), IsCylDecompOn n (cubeC n) C ∧
        (∀ i, ∀ κ ∈ C, κ ⊆ projFirst n m '' (X i).set ∨
          Disjoint κ (projFirst n m '' (X i).set)) ∧
        C.card ≤ MvPolynomial.eval ![D, k] b ∧
        ∀ κ ∈ C, Star a (c.eval D) n κ ∧ SubPf n κ :=
  Work.WilE7.E7_prop_main_proved (Work.WilE7.E7_fiber_cut_proved hE2 hE5 hE6) hE2 hE5 hE6

/-- `Prop9` (the frozen `E7_prop_main`), in the frozen namespace, from `E2`, `E5`, `E6`. -/
theorem Prop9_proved
    (hE2 : ∀ F : ℕ, ∃ p : Polynomial ℕ, ∀ (k : ℕ) (X : SemiPf k), X.fmt ≤ F →
      ∃ s : Finset (Fin k → ℝ), s.card ≤ p.eval X.deg ∧ (↑s : Set (Fin k → ℝ)) ⊆ X.set ∧
        ∀ x ∈ X.set, ∃ y ∈ s,
          connectedComponentIn X.set x = connectedComponentIn X.set y)
    (hE5 : ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (p q : ℕ) (X : SemiPf (p + q)), X.fmt ≤ F →
      ∃ L : List (Stratum p q), L.length ≤ b.eval X.deg ∧
        (∀ S ∈ L, S.X.fmt ≤ a ∧ S.deg ≤ b.eval X.deg ∧ S.Good) ∧
        X.set = (⋃ S ∈ L, S.X.set) ∧
        L.Pairwise (fun S T => Disjoint S.X.set T.X.set))
    (hE6 : ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (p q : ℕ) (X : SemiPf (p + q)), X.fmt ≤ F →
      ∃ Y Y' : SemiPf (p + q), Y.fmt ≤ a ∧ Y.deg ≤ b.eval X.deg ∧ Y'.fmt ≤ a ∧
        Y'.deg ≤ b.eval X.deg ∧ Y.set = fiberClosure X.set ∧
        Y'.set = fiberClosure X.set \ X.set) :
    Work.WilE7.Prop9 :=
  Work.WilE7.Prop9_of_hyp hE2 hE5 hE6

/-- **E7c.** BV Theorem 1 (sharp CD for `*`-sets), from BV Proposition 9 (the frozen
`E7_prop_main`). This is the interface used by the area's downstream consumers (`WilE8`, the
final wiring); the `_hyp` variant below takes `E2`/`E5`/`E6` directly. -/
theorem E7_bv_main_proved (h9 : Work.WilE7.Prop9) :
    ∀ F n : ℕ, ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ) (c : Polynomial ℕ),
      ∀ (D k : ℕ) (Y : Fin k → Set (Fin n → ℝ)),
        (∀ i, Star F D n (Y i)) →
        ∃ C : Finset (Set (Fin n → ℝ)), IsCylDecompOn n (cubeC n) C ∧
          (∀ i, ∀ κ ∈ C, κ ⊆ Y i ∨ Disjoint κ (Y i)) ∧
          C.card ≤ MvPolynomial.eval ![D, k] b ∧
          ∀ κ ∈ C, Star a (c.eval D) n κ :=
  Work.WilE7.bv_main_gen (fun F n => Work.WilE7.star_central h9 F n)

/-- **E7c** with `E2`, `E5`, `E6` as the leading hypotheses. -/
theorem E7_bv_main_proved_hyp
    (hE2 : Work.WilE7.E2_stmt) (hE5 : Work.WilE7.E5_stmt) (hE6 : Work.WilE7.E6_stmt) :
    ∀ F n : ℕ, ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ) (c : Polynomial ℕ),
      ∀ (D k : ℕ) (Y : Fin k → Set (Fin n → ℝ)),
        (∀ i, Star F D n (Y i)) →
        ∃ C : Finset (Set (Fin n → ℝ)), IsCylDecompOn n (cubeC n) C ∧
          (∀ i, ∀ κ ∈ C, κ ⊆ Y i ∨ Disjoint κ (Y i)) ∧
          C.card ≤ MvPolynomial.eval ![D, k] b ∧
          ∀ κ ∈ C, Star a (c.eval D) n κ :=
  E7_bv_main_proved (Work.WilE7.Prop9_of_hyp hE2 hE5 hE6)

/-- **E7d.** BV Theorem 2, ¬-case, from BV Proposition 9. -/
theorem E7_star_compl_proved (h9 : Work.WilE7.Prop9) :
    ∀ F n : ℕ, ∃ (a : ℕ) (p : Polynomial ℕ),
      ∀ (D : ℕ) (Y : Set (Fin n → ℝ)), Star F D n Y →
        Star a (p.eval D) n (cubeC n \ Y) :=
  Work.WilE7.star_compl_gen (fun F n => Work.WilE7.star_central h9 F n)

/-- **E7d** with `E2`, `E5`, `E6` as the leading hypotheses. -/
theorem E7_star_compl_proved_hyp
    (hE2 : Work.WilE7.E2_stmt) (hE5 : Work.WilE7.E5_stmt) (hE6 : Work.WilE7.E6_stmt) :
    ∀ F n : ℕ, ∃ (a : ℕ) (p : Polynomial ℕ),
      ∀ (D : ℕ) (Y : Set (Fin n → ℝ)), Star F D n Y →
        Star a (p.eval D) n (cubeC n \ Y) :=
  E7_star_compl_proved (Work.WilE7.Prop9_of_hyp hE2 hE5 hE6)

/-- **E7e.** BV Theorem 2, ∧-case, from BV Proposition 9. -/
theorem E7_star_inter_proved (h9 : Work.WilE7.Prop9) :
    ∀ F n : ℕ, ∃ (a : ℕ) (p : Polynomial ℕ),
      ∀ (k : ℕ) (D : Fin k → ℕ) (Y : Fin k → Set (Fin n → ℝ)),
        (∀ i, Star F (D i) n (Y i)) →
        Star a (p.eval (∑ i, D i)) n (cubeC n ∩ ⋂ i, Y i) :=
  Work.WilE7.star_inter_gen (fun F n => Work.WilE7.star_central h9 F n)

/-- **E7e** with `E2`, `E5`, `E6` as the leading hypotheses. -/
theorem E7_star_inter_proved_hyp
    (hE2 : Work.WilE7.E2_stmt) (hE5 : Work.WilE7.E5_stmt) (hE6 : Work.WilE7.E6_stmt) :
    ∀ F n : ℕ, ∃ (a : ℕ) (p : Polynomial ℕ),
      ∀ (k : ℕ) (D : Fin k → ℕ) (Y : Fin k → Set (Fin n → ℝ)),
        (∀ i, Star F (D i) n (Y i)) →
        Star a (p.eval (∑ i, D i)) n (cubeC n ∩ ⋂ i, Y i) :=
  E7_star_inter_proved (Work.WilE7.Prop9_of_hyp hE2 hE5 hE6)

/-- **E7f.** Gabrielov's complement theorem, from BV Proposition 9. -/
theorem E7_subpf_compl_proved (h9 : Work.WilE7.Prop9) :
    ∀ {n : ℕ} (Y : Set (Fin n → ℝ)), SubPf n Y → SubPf n (cubeC n \ Y) :=
  Work.WilE7.subpf_compl_gen h9

/-- **E7f** with `E2`, `E5`, `E6` as the leading hypotheses. -/
theorem E7_subpf_compl_proved_hyp
    (hE2 : Work.WilE7.E2_stmt) (hE5 : Work.WilE7.E5_stmt) (hE6 : Work.WilE7.E6_stmt) :
    ∀ {n : ℕ} (Y : Set (Fin n → ℝ)), SubPf n Y → SubPf n (cubeC n \ Y) :=
  E7_subpf_compl_proved (Work.WilE7.Prop9_of_hyp hE2 hE5 hE6)

/-- **E7a** (list form, after the lead's 2026-10-09 ruling), re-exported in the frozen
namespace so that a caller finds it next to the other holes of the area. -/
theorem E7_fiber_cut_proved
    (hE2 : ∀ F : ℕ, ∃ p : Polynomial ℕ, ∀ (k : ℕ) (X : SemiPf k), X.fmt ≤ F →
      ∃ s : Finset (Fin k → ℝ), s.card ≤ p.eval X.deg ∧ (↑s : Set (Fin k → ℝ)) ⊆ X.set ∧
        ∀ x ∈ X.set, ∃ y ∈ s,
          connectedComponentIn X.set x = connectedComponentIn X.set y)
    (hE5 : ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (p q : ℕ) (X : SemiPf (p + q)), X.fmt ≤ F →
      ∃ L : List (Stratum p q), L.length ≤ b.eval X.deg ∧
        (∀ S ∈ L, S.X.fmt ≤ a ∧ S.deg ≤ b.eval X.deg ∧ S.Good) ∧
        X.set = (⋃ S ∈ L, S.X.set) ∧
        L.Pairwise (fun S T => Disjoint S.X.set T.X.set))
    (hE6 : ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (p q : ℕ) (X : SemiPf (p + q)), X.fmt ≤ F →
      ∃ Y Y' : SemiPf (p + q), Y.fmt ≤ a ∧ Y.deg ≤ b.eval X.deg ∧ Y'.fmt ≤ a ∧
        Y'.deg ≤ b.eval X.deg ∧ Y.set = fiberClosure X.set ∧
        Y'.set = fiberClosure X.set \ X.set) :
    ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (n m : ℕ) (X : SemiPf (n + m)), X.fmt ≤ F →
      ∃ L : List (SemiPf (n + m)), L.length ≤ b.eval X.deg ∧
        (∀ Xh ∈ L, Xh.fmt ≤ a ∧ Xh.deg ≤ b.eval X.deg ∧ ∀ x, (fiber Xh.set x).Finite) ∧
        projFirst n m '' X.set = ⋃ Xh ∈ L, projFirst n m '' Xh.set :=
  Work.WilE7.E7_fiber_cut_proved hE2 hE5 hE6

end WilkiesDesign.E
