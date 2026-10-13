/-
  WilE6 / Compl: **the effective complement of a restricted semi-Pfaffian set.**

  This is the missing ingredient of the *frontier* conjunct of the frozen
  `WilkiesDesign.E.E6_fiber_closure`.  Given a list of basic sets `basics` over a chain `c`
  (so that `X := ⟨r, c, basics⟩` is a restricted semi-Pfaffian set), the complement of `X.set`
  inside the cube is again a union of basic sets over the *same* chain `c`, with degree bounded
  by a polynomial in `X.deg` (for fixed format `k + r ≤ F`).

  The construction is the sign-cell decomposition of `X` (`Work.WilE5.Cells`):

  * the sign cells `cellSemiPf X σ` (`σ : Fin (atomsOf X).length → Sign`) cover the cube, and
    two points with the same sign assignment lie in the same cell;
  * `X.set` is exactly the union of the *good* cells, i.e. of those cells with nonempty
    `cellSemiPf X σ` contained in `X.set` (`Work.WilE5.signAssign_mem_goodCells`,
    `Work.WilE5.cellSemiPf_subset`);
  * a cell that meets a disjunct `B` of `X` is contained in `B` (`cell_holds_of_meets`,
    delegated), so a cell either lies in `X.set` or is disjoint from it;
  * hence `cubeC \ X.set = ⋃ {cell X σ : cellSemiPf X σ ⊄ X.set}`;
  * the number of cells appearing here is polynomial in `X.deg`, because it is at most the number
    of *nonempty* cells, which is bounded by Khovanskii's component count (`cellCountAll`,
    delegated, from the frozen `E2_components`).

  Both facts are taken here as explicit hypotheses, so that this file depends only on the
  already delivered `Work.WilE5.Cells` API; the final `Work.WilE6.Compl.saCompl_proved`
  (in `SaCompl.lean`) instantiates them.
-/
import Mathlib
import Submission.Work.WilE5.Cells.cellBasic
import Submission.Work.WilE5.Basic

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE6.Compl
open WilkiesDesign WilkiesDesign.E

/-- **The counter of sign cells.**  `cellCountAll` (Khovanskii + intermediate value, from the
frozen `E2_components`) bounds the number of *nonempty* sign cells of a `SemiPf` set of format
`≤ F` by a polynomial in its degree. -/
def CellCountHyp (F : ℕ) : Prop :=
  ∃ b : Polynomial ℕ, ∀ (k : ℕ) (X : SemiPf k), X.fmt ≤ F →
    ∀ T : Finset (Fin (Work.WilE5.atomsOf X).length → Work.WilE5.Sign),
      (∀ σ ∈ T, (Work.WilE5.cellSemiPf X σ).set.Nonempty) → T.card ≤ b.eval X.deg

/-- **The compatibility of a sign cell with a disjunct.**  If a cell meets the basic set `B` at a
point `w`, then the whole cell satisfies `B` (delegated as `cell_holds_of_meets`). -/
def CellMeetHyp : Prop :=
  ∀ {k : ℕ} (X : SemiPf k) (σ : Fin (Work.WilE5.atomsOf X).length → Work.WilE5.Sign)
    {B : Basic k X.r}, B ∈ X.basics → ∀ {w : Fin k → ℝ},
      (Work.WilE5.cell X σ).holds X.c w → B.holds X.c w →
      ∀ x : Fin k → ℝ, (Work.WilE5.cell X σ).holds X.c x → B.holds X.c x

/-- **The effective complement of a `SemiPf`-set, from the two hypotheses above.** -/
theorem saCompl_of (F : ℕ) (hCount : CellCountHyp F) (hMeet : CellMeetHyp) :
    ∃ p : Polynomial ℕ, ∀ (k r : ℕ) (c : EAChain k r) (basics : List (Basic k r)),
      k + r ≤ F → ∃ basics' : List (Basic k r),
        (basics'.map Basic.deg).sum ≤ p.eval ((basics.map Basic.deg).sum) ∧
        {x : Fin k → ℝ | x ∈ cubeC k ∧ ∃ B ∈ basics', B.holds c x} =
          cubeC k \ {x : Fin k → ℝ | x ∈ cubeC k ∧ ∃ B ∈ basics, B.holds c x} := by
  obtain ⟨b, hb⟩ := hCount
  refine ⟨b * Polynomial.X, ?_⟩
  intro k r c basics hF
  let X : SemiPf k := ⟨r, c, basics⟩
  have hfmt : X.fmt ≤ F := hF
  -- the sign cells whose set is *not* contained in `X.set`
  let L : List (Fin (Work.WilE5.atomsOf X).length → Work.WilE5.Sign) :=
    (Work.WilE5.allSigns X).filter
      (fun σ => decide (¬ ((Work.WilE5.cellSemiPf X σ).set ⊆ X.set)))
  -- membership in a sign cell
  have memCell : ∀ {σ : Fin (Work.WilE5.atomsOf X).length → Work.WilE5.Sign} {x : Fin k → ℝ},
      (x ∈ (Work.WilE5.cellSemiPf X σ).set ↔
        x ∈ cubeC k ∧ (Work.WilE5.cell X σ).holds X.c x) := by
    intro σ x
    constructor
    · intro h
      exact ⟨h.1, Work.WilE5.holds_of_mem_cellSemiPf h⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, ⟨Work.WilE5.cell X σ, List.mem_singleton.mpr rfl, h2⟩⟩
  -- the list of cells is duplicate-free
  have hall_nodup : (Work.WilE5.allSigns X).Nodup := by
    show ((Finset.univ : Finset
      (Fin (Work.WilE5.atomsOf X).length → Work.WilE5.Sign)).toList).Nodup
    exact Finset.nodup_toList _
  have hLnodup : L.Nodup := by
    change ((Work.WilE5.allSigns X).filter
      (fun σ => decide (¬ ((Work.WilE5.cellSemiPf X σ).set ⊆ X.set)))).Nodup
    exact List.Nodup.filter _ hall_nodup
  -- a truncated cell is nonempty
  have hLnotsub : ∀ σ ∈ L, ¬ ((Work.WilE5.cellSemiPf X σ).set ⊆ X.set) := by
    intro σ hσ
    have h' : σ ∈ (Work.WilE5.allSigns X).filter
        (fun σ => decide (¬ ((Work.WilE5.cellSemiPf X σ).set ⊆ X.set))) := hσ
    exact of_decide_eq_true (List.mem_filter.mp h').2
  -- the number of cells used
  have hLlen : L.length ≤ b.eval X.deg := by
    have hT : ∀ σ ∈ L.toFinset, (Work.WilE5.cellSemiPf X σ).set.Nonempty := by
      intro σ hσ
      by_contra hemp
      exact hLnotsub σ (List.mem_toFinset.mp hσ) fun z hz => absurd ⟨z, hz⟩ hemp
    have hcard := hb k X hfmt L.toFinset hT
    rwa [List.toFinset_card_of_nodup hLnodup] at hcard
  refine ⟨L.map (fun σ => Work.WilE5.cell X σ), ?_, ?_⟩
  · -- the degree bound
    have h1 : (List.map Basic.deg (L.map (fun σ => Work.WilE5.cell X σ))).sum
        = (L.map (fun σ => (Work.WilE5.cell X σ).deg)).sum := by
      rw [List.map_map]; rfl
    rw [h1, Polynomial.eval_mul, Polynomial.eval_X]
    calc (L.map (fun σ => (Work.WilE5.cell X σ).deg)).sum
        ≤ L.length * X.deg := by
          have h := List.sum_le_length_nsmul
            (L.map (fun σ => (Work.WilE5.cell X σ).deg)) X.deg ?_
          · simpa using h
          · intro d hd
            obtain ⟨σ, -, rfl⟩ := List.mem_map.mp hd
            exact Work.WilE5.cell_deg_le X σ
      _ ≤ b.eval X.deg * X.deg := Nat.mul_le_mul_right _ hLlen
  · -- the set equality
    ext x
    constructor
    · rintro ⟨hx, B, hB, hBx⟩
      obtain ⟨σ, hσL, rfl⟩ := List.mem_map.mp hB
      have hcellx : (Work.WilE5.cell X σ).holds X.c x := hBx
      refine ⟨hx, ?_⟩
      intro hxX
      obtain ⟨-, B₀, hB₀, hB₀x⟩ := hxX
      exact hLnotsub σ hσL fun z hz =>
        ⟨(memCell.mp hz).1, B₀, hB₀,
          hMeet X σ (B := B₀) hB₀ hcellx hB₀x z (memCell.mp hz).2⟩
    · rintro ⟨hx, hxX⟩
      refine ⟨hx, ?_⟩
      have hcellmem : x ∈ (Work.WilE5.cellSemiPf X (Work.WilE5.signAssign X x)).set :=
        Work.WilE5.mem_cellSemiPf_self X hx
      have hnot : ¬ ((Work.WilE5.cellSemiPf X (Work.WilE5.signAssign X x)).set ⊆ X.set) :=
        fun hsub => hxX (hsub hcellmem)
      have hmemL : Work.WilE5.signAssign X x ∈ L := by
        change Work.WilE5.signAssign X x ∈ (Work.WilE5.allSigns X).filter
          (fun σ => decide (¬ ((Work.WilE5.cellSemiPf X σ).set ⊆ X.set)))
        refine List.mem_filter.mpr ⟨?_, decide_eq_true hnot⟩
        rw [Work.WilE5.allSigns]
        exact Finset.mem_toList.mpr (Finset.mem_univ _)
      exact ⟨Work.WilE5.cell X (Work.WilE5.signAssign X x),
        List.mem_map.mpr ⟨_, hmemL, rfl⟩, (memCell.mp hcellmem).2⟩

end Work.WilE6.Compl
