/-
  WilG4a : the fibre of a cell inside the strip, when it is not a subsingleton, is the open
  interval spanned by its own infimum and supremum.

  This is the `n = 1` "interval" half of the cell dichotomy of BNZ §5.1: a cell of the sharp
  decomposition is a graph or a band over its base, so its fibre over a parameter `l` is either
  a single point (subsingleton) or the interval cut out by the two boundary functions.  Inside
  the strip `{z | z(last) ∈ I}` the fibre lies in `I = (0,1)`, which bounds it; hence the
  `EReal`-interval description produced by `isCell_fiber` has finite endpoints, and the fibre is
  literally `(sInf fibre, sSup fibre)`.

  The file deliberately imports `f1affine1_defs` (rather than the competing definition of
  `strip` in `LipChartsDefs`, with which it cannot coexist in one environment) so that the
  lemma is usable together with `fibre_endpoints_bounds`, which consumes exactly the shape
  `fibre κ l = Set.Ioo (lo l) (hi l)`.
-/
import Mathlib
import Submission.Work.WilG4a.Defs
import Submission.Work.WilG4a.Cells
import Submission.Work.WilG4a.isCell_fiber
import Submission.Work.WilG4a.f1affine1_defs

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilG4a
open WilkiesConjecture WilkiesDesign

/-- **The `EReal`-interval of `isCell_fiber`, inside the strip, is a real interval.**
The strip hypothesis `κ ⊆ {z | z(last) ∈ I}` forces the fibre into `I = (0,1)`, which is
bounded; together with nonemptiness this excludes all four endpoint infinities, so the
`EReal`-interval cut out by `a` and `b` can be read off as a real open interval. -/
theorem fibre_eq_Ioo_of_EReal_band {p : ℕ} {κ : Set (Fin (p + 1) → ℝ)}
    (hstrip : κ ⊆ Work.WilG4a.strip p) {l : Fin p → ℝ} {a b : EReal}
    (hband : Work.WilG4a.fibre κ l = {y : ℝ | a < (y : EReal) ∧ (y : EReal) < b})
    (hne : (Work.WilG4a.fibre κ l).Nonempty) :
    ∃ A B : ℝ, Work.WilG4a.fibre κ l = Set.Ioo A B := by
  obtain ⟨y₀, hy₀⟩ := hne
  have hy₀' : a < (y₀ : EReal) ∧ (y₀ : EReal) < b := by
    rw [hband] at hy₀
    exact hy₀
  obtain ⟨hy₀a, hy₀b⟩ := hy₀'
  -- the fibre sits inside `I = (0,1)`
  have hy₀I : y₀ ∈ I := (strip_mem_iff_snoc l y₀).mp (hstrip hy₀)
  have ha_ne_top : a ≠ ⊤ := ne_of_lt (lt_of_lt_of_le hy₀a le_top)
  have hb_ne_bot : b ≠ ⊥ := (ne_of_lt (lt_of_le_of_lt bot_le hy₀b)).symm
  have ha_ne_bot : a ≠ ⊥ := by
    intro hbot
    have hmem : y₀ - 1 ∈ Work.WilG4a.fibre κ l := by
      rw [hband]
      refine ⟨?_, ?_⟩
      · rw [hbot]; exact EReal.bot_lt_coe _
      · calc ((y₀ - 1 : ℝ) : EReal) < (y₀ : EReal) :=
            EReal.coe_lt_coe_iff.2 (by linarith)
          _ < b := hy₀b
    have hI := (strip_mem_iff_snoc l (y₀ - 1)).mp (hstrip hmem)
    linarith [hy₀I.1, hy₀I.2, hI.1]
  have hb_ne_top : b ≠ ⊤ := by
    intro htop
    have hmem : y₀ + 1 ∈ Work.WilG4a.fibre κ l := by
      rw [hband]
      refine ⟨?_, ?_⟩
      · calc a < (y₀ : EReal) := hy₀a
          _ < ((y₀ + 1 : ℝ) : EReal) := EReal.coe_lt_coe_iff.2 (by linarith)
      · rw [htop]; exact EReal.coe_lt_top _
    have hI := (strip_mem_iff_snoc l (y₀ + 1)).mp (hstrip hmem)
    linarith [hy₀I.1, hy₀I.2, hI.2]
  refine ⟨a.toReal, b.toReal, ?_⟩
  rw [hband]
  ext y
  simp only [Set.mem_ofPred_eq, Set.mem_Ioo]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨EReal.coe_lt_coe_iff.1 (by rwa [← EReal.coe_toReal ha_ne_top ha_ne_bot] at h1),
      EReal.coe_lt_coe_iff.1 (by rwa [← EReal.coe_toReal hb_ne_top hb_ne_bot] at h2)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by rw [← EReal.coe_toReal ha_ne_top ha_ne_bot, EReal.coe_lt_coe_iff]; exact h1,
      by rw [← EReal.coe_toReal hb_ne_top hb_ne_bot, EReal.coe_lt_coe_iff]; exact h2⟩

theorem fibre_eq_Ioo_of_nonSubsingleton {p : ℕ} {κ : Set (Fin (p + 1) → ℝ)} (hcell : WilkiesDesign.IsCell (p + 1) κ) (hstrip : κ ⊆ Work.WilG4a.strip p) {l : Fin p → ℝ} (h : ¬ (Work.WilG4a.fibre κ l).Subsingleton) : Work.WilG4a.fibre κ l = Set.Ioo (sInf (Work.WilG4a.fibre κ l)) (sSup (Work.WilG4a.fibre κ l)) := by
  obtain ⟨y, hy, -⟩ := Set.not_subsingleton_iff.mp h
  rcases isCell_fiber p hcell l with ⟨x, hx⟩ | ⟨a, b, hab⟩
  · -- graph case: the fibre is a single point, hence a subsingleton.
    have hx' : Work.WilG4a.fibre κ l = {x} := hx
    exact absurd (hx' ▸ Set.subsingleton_singleton) h
  · -- band case: the fibre is a real open interval.
    obtain ⟨A, B, hAB⟩ := fibre_eq_Ioo_of_EReal_band hstrip hab ⟨y, hy⟩
    -- a non-subsingleton interval `(A,B)` is nondegenerate
    have hAB' : A < B := by
      by_contra hle
      rw [hAB, Set.Ioo_eq_empty hle] at hy
      exact absurd hy (Set.notMem_empty y)
    rw [hAB, csInf_Ioo hAB', csSup_Ioo hAB']

end Work.WilG4a
