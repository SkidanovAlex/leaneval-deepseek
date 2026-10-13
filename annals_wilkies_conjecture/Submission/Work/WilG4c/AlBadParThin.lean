import Mathlib
import Submission.Work.Wilkies.Defs
import Submission.Work.WilG4c.AlBadParDefs
import Submission.Work.WilG4c.AlBadParAux
import Submission.Work.WilG4c.FibCellBackup
import Submission.Work.WilG1.Cell.thin_closure

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign

/-!
# The parameter projection of a thin family of "bad fibres" is thin

`BadFib p q V` is the set of parameters `l ∈ ℝ^p` whose fibre `V_l ⊆ ℝ^q` contains a ball.
We prove that if `V ∈ S.Ω F D (p+q)` has empty interior then `BadFib p q V` is nowhere dense,
by induction on `q`.  The induction step cell-decomposes `V` (using `S.SharpCD`), writes `V`
as the union of the cells contained in it, and uses that the fibre of a cell is again a cell
(`fibSet_isCellOrEmpty`) to transfer "contains a ball" to a single cell; a band cell reduces to
its projected base (`BadFib_projLast_subset`), and graph cells have no bad parameters at all.
-/

/-- **The main induction.**  For `V ∈ S.Ω F D (p+q)` with empty interior, the set of parameters
whose fibre contains a ball is nowhere dense. -/
theorem BadFib_isNowhereDense (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) :
    ∀ (q : ℕ) (p F D : ℕ) (V : Set (Fin (p + q) → ℝ)),
      V ∈ S.Ω F D (p + q) → interior V = ∅ → IsNowhereDense (BadFib p q V) := by
  intro q
  induction q with
  | zero =>
    intro p F D V hV hint
    rw [BadFib_zero]
    exact Work.WilG1.Cell.thin_closure hcd (b := Polynomial.X) (by simpa using hV) hint
  | succ q ih =>
    intro p F D V hV hint
    classical
    obtain ⟨a, b, c, H⟩ := hcd F (p + (q + 1))
    obtain ⟨C, hCyc, hsep, _hcard, hOm⟩ := H D 1 (fun _ : Fin 1 => V) (fun _ => hV)
    have hcell : ∀ κ ∈ C, IsCell (p + (q + 1)) κ := fun κ hκ =>
      Work.WilG1.Cell.isCell_of_mem_cylDecomp hCyc hκ
    have hcover : ∀ z : Fin (p + (q + 1)) → ℝ, ∃ κ ∈ C, z ∈ κ := fun z =>
      Work.WilG1.Cell.exists_mem_of_cylDecomp hCyc z
    set T : Finset (Set (Fin (p + (q + 1)) → ℝ)) := C.filter (fun κ => κ ⊆ V) with hT
    -- ### Step A: a bad parameter belongs to some cell contained in `V`
    have hstepA : BadFib p (q + 1) V ⊆ ⋃ κ ∈ T, BadFib p (q + 1) κ := by
      intro l hl
      obtain ⟨y₀, ε, hε, hball⟩ := hl
      have hcov : Metric.ball y₀ ε ⊆ ⋃ κ ∈ T, fibSet p (q + 1) κ l := by
        intro y hy
        have hyV : Fin.append l y ∈ V := hball y hy
        obtain ⟨κ, hκC, hyκ⟩ := hcover (Fin.append l y)
        have hκsub : κ ⊆ V := by
          rcases hsep 0 κ hκC with h | h
          · exact h
          · exact absurd hyV (Set.disjoint_left.mp h hyκ)
        exact Set.mem_iUnion.mpr ⟨κ, Set.mem_iUnion.mpr
          ⟨Finset.mem_filter.mpr ⟨hκC, hκsub⟩, hyκ⟩⟩
      have hgood : ∀ κ ∈ T, interior (fibSet p (q + 1) κ l) = ∅ →
          IsNowhereDense (fibSet p (q + 1) κ l) := by
        intro κ hκT hintκ
        rw [hT] at hκT
        have hκC : κ ∈ C := (Finset.mem_filter.mp hκT).1
        rcases fibSet_isCellOrEmpty_aux p (q + 1) κ l (hcell κ hκC) with hemp | hcell'
        · rw [hemp]; exact isNowhereDense_empty
        · exact Work.WilG1.Cell.isCell_isNowhereDense hcell' hintκ
      obtain ⟨κ, hκT, hκint⟩ := exists_mem_interior_nonempty_of_cover
        (B := Metric.ball y₀ ε) (u := T) (s := fun κ => fibSet p (q + 1) κ l)
        Metric.isOpen_ball ⟨y₀, Metric.mem_ball_self hε⟩ hcov hgood
      refine Set.mem_iUnion.mpr ⟨κ, Set.mem_iUnion.mpr ⟨hκT, ?_⟩⟩
      obtain ⟨w, hw⟩ := hκint
      rw [mem_interior_iff_mem_nhds] at hw
      obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hw
      exact ⟨w, δ, hδ, fun y hy => hδsub (Metric.mem_ball.mpr hy)⟩
    -- ### Step B: each cell contained in `V` has nowhere dense bad parameters
    have hstepB : ∀ κ ∈ T, IsNowhereDense (BadFib p (q + 1) κ) := by
      intro κ hκT
      rw [hT] at hκT
      obtain ⟨hκC, hκV⟩ := Finset.mem_filter.mp hκT
      have hintκ : interior κ = ∅ :=
        Set.eq_empty_of_subset_empty (by rw [← hint]; exact interior_mono hκV)
      rcases Work.WilG1.Cell.cell_cases (hcell κ hκC) with
        ⟨C', f, hf, hiff⟩ | ⟨C', a', b', ha', hb', hab', hiff⟩
      · rw [BadFib_empty_of_graph (g := f) (fun z hz => ((hiff z).mp hz).2)]
        exact isNowhereDense_empty
      · have hproj : projLast κ ∈ S.Ω (a + 1) (c.eval D) (p + q) := S.proj (hOm κ hκC)
        have hsub : projLast κ ⊆ C' := by
          rintro x ⟨t, ht⟩
          have h1 := ((hiff (Fin.snoc x t)).mp ht).1
          rwa [Fin.init_snoc] at h1
        have hbaseC : interior C' = ∅ := by
          refine band_base_interior_empty ha' hb' hab' ?_
          rw [Set.ext (fun z => (hiff z).symm)]
          exact hintκ
        have hbase : interior (projLast κ) = ∅ :=
          Set.eq_empty_of_subset_empty (by rw [← hbaseC]; exact interior_mono hsub)
        exact IsNowhereDense.mono BadFib_projLast_subset
          (ih p (a + 1) (c.eval D) (projLast κ) hproj hbase)
    -- ### Step C: assemble
    exact IsNowhereDense.mono hstepA (IsNowhereDense.biUnion (fun κ hκ => hstepB κ hκ))

/-- `Work.WilG4c.AlBadParThin`: the parameter projection of a thin `Ω`-set is thin. -/
theorem AlBadParThin (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) (p n : ℕ) :
    ∀ {F D : ℕ} {V : Set (Fin (p + (n + 1)) → ℝ)},
      V ∈ S.Ω F D (p + (n + 1)) → interior V = ∅ →
      interior {l : Fin p → ℝ | ∃ (y₀ : Fin (n + 1) → ℝ) (ε : ℝ), 0 < ε ∧
        ∀ y : Fin (n + 1) → ℝ, dist y y₀ < ε → Fin.append l y ∈ V} = ∅ := by
  intro F D V hV hint
  have h := BadFib_isNowhereDense S hcd (n + 1) p F D V hV hint
  rw [IsNowhereDense] at h
  have hsub : interior {l : Fin p → ℝ | ∃ (y₀ : Fin (n + 1) → ℝ) (ε : ℝ), 0 < ε ∧
      ∀ y : Fin (n + 1) → ℝ, dist y y₀ < ε → Fin.append l y ∈ V}
      ⊆ interior (closure (BadFib p (n + 1) V)) := interior_mono subset_closure
  rw [h] at hsub
  exact Set.subset_empty_iff.mp hsub

end Work.WilG4c
