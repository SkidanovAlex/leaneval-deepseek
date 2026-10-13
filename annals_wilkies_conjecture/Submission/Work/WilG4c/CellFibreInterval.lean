import Mathlib
import Submission.Work.WilG4c.FiberEndsDefs
import Submission.Work.WilG4c.FiberEndsLo
import Submission.Work.WilG4c.FiberEndsHi

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG

/-! ## The fibre of a cell is an interval

A cylindrical cell `Z ⊆ ℝ^{n+1}` of the frozen vocabulary `WilkiesDesign.IsCell` is either the
graph of a function over a base cell `C ⊆ ℝⁿ`, or the band between two `EReal`-valued boundary
functions `a < b` over `C`.  Accordingly its fibre `Z_l = {x | Fin.snoc l x ∈ Z}` over a base
point `l` is either a single point (`{f l}`, empty off `C`) or an open interval
(`(a l, b l) ∩ ℝ`, empty off `C`).  Both kinds are order-convex, which is the structural input
behind `CellFibreInterval`. -/

/-- The fibre of a cylindrical cell is an order-convex subset of `ℝ`. -/
theorem ordConnected_fibre_of_isCell {n : ℕ} {Z : Set (Fin (n + 1) → ℝ)}
    (hZ : IsCell (n + 1) Z) (l : Fin n → ℝ) : (fibre n Z l).OrdConnected := by
  cases hZ with
  | graph hC f hf =>
      rw [Set.ordConnected_iff]
      intro x hx y hy hxy
      simp only [fibre, Set.mem_ofPred_eq, Fin.init_snoc, Fin.snoc_last] at hx hy
      intro z hz
      simp only [fibre, Set.mem_ofPred_eq, Fin.init_snoc, Fin.snoc_last]
      rw [Set.mem_Icc] at hz
      exact ⟨hx.1, le_antisymm (by rw [← hy.2]; exact hz.2) (by rw [← hx.2]; exact hz.1)⟩
  | band hC a b ha hb hab =>
      rw [Set.ordConnected_iff]
      intro x hx y hy hxy
      simp only [fibre, Set.mem_ofPred_eq, Fin.init_snoc, Fin.snoc_last] at hx hy
      intro z hz
      simp only [fibre, Set.mem_ofPred_eq, Fin.init_snoc, Fin.snoc_last]
      rw [Set.mem_Icc] at hz
      exact ⟨hx.1, lt_of_lt_of_le hx.2.1 (EReal.coe_le_coe_iff.mpr hz.1),
        lt_of_le_of_lt (EReal.coe_le_coe_iff.mpr hz.2) hy.2.2⟩

/-- For a cell `Z ⊆ ℝ^{m+1}` all of whose values in the fibre coordinate lie in `(0,1)`, the
fibre `Z_l` over a base point `l` with non-empty fibre is sandwiched between its own `sInf` and
`sSup`, and conversely contains the whole open interval between them: it is exactly the interval
between its two ends (possibly with the ends included or not). -/
theorem isCell_fibre_sInf_sSup (m : ℕ) (Z : Set (Fin (m + 1) → ℝ)) (hZ : IsCell (m + 1) Z)
    (hI : ∀ z ∈ Z, z (Fin.last m) ∈ Set.Ioo (0 : ℝ) 1) (l : Fin m → ℝ)
    (hne : (fibre m Z l).Nonempty) :
    (∀ x : ℝ, x ∈ fibre m Z l → sInf (fibre m Z l) ≤ x ∧ x ≤ sSup (fibre m Z l)) ∧
      (∀ x : ℝ, sInf (fibre m Z l) < x → x < sSup (fibre m Z l) → x ∈ fibre m Z l) := by
  have hord := ordConnected_fibre_of_isCell hZ l
  have hbB := bddBelow_fibre m Z hI l
  have hbA := bddAbove_fibre m Z hI l
  refine ⟨fun x hx => ⟨csInf_le hbB hx, le_csSup hbA hx⟩, ?_⟩
  -- `sInf` resp. `sSup` are attained in the limit: elements of the fibre lie below resp. above
  intro x h1 h2
  obtain ⟨y, hy, hyx⟩ := (csInf_lt_iff hbB hne).mp h1
  obtain ⟨z, hz, hxz⟩ := (lt_csSup_iff hbA hne).mp h2
  exact hord.out hy hz ⟨le_of_lt hyx, le_of_lt hxz⟩

/-- **The fibre of a cell is the interval between its fibre ends.**  For a cell `κ` of a
cylindrical decomposition of `ℝ^{m+1}` whose fibre coordinate lies in `(0,1)`, the fibre of `κ`
over any base point with non-empty fibre is contained in `[lo, hi]` and contains `(lo, hi)`,
where `lo`, `hi` are the pointwise infimum and supremum of the fibre.  Consequently both ends
lie in `[0,1]`, their midpoint lies in `(0,1)` and their difference in `[0,1]`. -/
theorem CellFibreInterval (S : SOMin) (m : ℕ) (C : Finset (Set (Fin (m + 1) → ℝ)))
    (hC : IsCylDecomp (m + 1) C) (κ : Set (Fin (m + 1) → ℝ)) (hκ : κ ∈ C)
    (hI : ∀ z ∈ κ, z (Fin.last m) ∈ Set.Ioo (0 : ℝ) 1) :
    ∀ l : Fin m → ℝ, (Work.WilG4c.fibre m κ l).Nonempty →
      (∀ x : ℝ, x ∈ Work.WilG4c.fibre m κ l →
        Work.WilG4c.loOf m κ l ≤ x ∧ x ≤ Work.WilG4c.hiOf m κ l) ∧
      (∀ x : ℝ, Work.WilG4c.loOf m κ l < x → x < Work.WilG4c.hiOf m κ l →
        x ∈ Work.WilG4c.fibre m κ l) ∧
      (0 ≤ Work.WilG4c.loOf m κ l ∧ Work.WilG4c.loOf m κ l ≤ 1) ∧
      (0 ≤ Work.WilG4c.hiOf m κ l ∧ Work.WilG4c.hiOf m κ l ≤ 1) ∧
      (0 < (Work.WilG4c.loOf m κ l + Work.WilG4c.hiOf m κ l) / 2 ∧
        (Work.WilG4c.loOf m κ l + Work.WilG4c.hiOf m κ l) / 2 < 1) ∧
      (0 ≤ Work.WilG4c.hiOf m κ l - Work.WilG4c.loOf m κ l ∧
        Work.WilG4c.hiOf m κ l - Work.WilG4c.loOf m κ l ≤ 1) := by
  -- the cell `κ` is an `IsCell`, hence its fibres are order-convex
  have hcell : IsCell (m + 1) κ := (hC.1 κ hκ).1
  intro l hl
  obtain ⟨hb1, hb2⟩ := isCell_fibre_sInf_sSup m κ hcell hI l hl
  -- every value in the fibre coordinate lies in `(0,1)`
  have hsub : fibre m κ l ⊆ Set.Ioo (0 : ℝ) 1 := fibre_subset_Ioo m κ hI l
  have hne : (fibre m κ l).Nonempty := hl
  obtain ⟨x0, hx0⟩ := hl
  have hx0I : x0 ∈ Set.Ioo (0 : ℝ) 1 := hsub hx0
  -- `loOf` and `hiOf` are the `sInf` and `sSup` of the (non-empty) fibre
  have hlo : loOf m κ l ≤ x0 := by
    rw [loOf_eq_sInf m κ l hne]; exact (hb1 x0 hx0).1
  have hhi : x0 ≤ hiOf m κ l := by
    rw [hiOf_eq_sSup m κ l hne]; exact (hb1 x0 hx0).2
  have hlo0 : 0 ≤ loOf m κ l := by
    rw [loOf_eq_sInf m κ l hne]
    exact le_csInf hne (fun x hx => le_of_lt (hsub hx).1)
  have hhi1 : hiOf m κ l ≤ 1 := by
    rw [hiOf_eq_sSup m κ l hne]
    exact csSup_le hne (fun x hx => le_of_lt (hsub hx).2)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx; rw [loOf_eq_sInf m κ l hne, hiOf_eq_sSup m κ l hne]; exact hb1 x hx
  · intro x h1 h2
    rw [loOf_eq_sInf m κ l hne] at h1
    rw [hiOf_eq_sSup m κ l hne] at h2
    exact hb2 x h1 h2
  · exact ⟨hlo0, le_of_lt (lt_of_le_of_lt hlo hx0I.2)⟩
  · exact ⟨le_of_lt (lt_of_lt_of_le hx0I.1 hhi), hhi1⟩
  · constructor <;> linarith [hx0I.1, hx0I.2, hlo, hhi, hlo0, hhi1]
  · constructor <;> linarith [hx0I.1, hx0I.2, hlo, hhi, hlo0, hhi1]

end Work.WilG4c
