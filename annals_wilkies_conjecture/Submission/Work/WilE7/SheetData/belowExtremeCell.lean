import Mathlib
import Submission.Work.WilE7.SheetData.belowBandX
import Submission.Work.WilE7.SheetData.belowBandSubPfX
import Submission.Work.WilE7.SheetData.bandCell_bd
import Submission.Work.WilE7.SheetData.multiStrata_cellsX_aux

-- the hypotheses of the target live inside the `∀` of an `∃ … ∀ …` statement; the unused-variable
-- linter mis-reports such binders, which cannot be renamed without changing the statement
set_option linter.unusedVariables false
noncomputable section
open Classical

namespace Work.WilE7.SheetData

/-- The open band `{y | π y ∈ C, -1 < y_last < g (π y)}` depends on the level function `g` only
through its values on `C`. -/
theorem extremeBandSet_eq {p m : ℕ} {C : Set (Fin p → ℝ)} {k : ℕ}
    {s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ)} (i : Fin k)
    {f : (Fin p → ℝ) → ℝ} (hf : ∀ x ∈ C, f x = (s i x) (Fin.last m)) :
    {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ -1 < y (Fin.last p) ∧
        y (Fin.last p) < f (Fin.init y)}
      = {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ -1 < y (Fin.last p) ∧
        y (Fin.last p) < (s i (Fin.init y)) (Fin.last m)} := by
  ext y
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, by rwa [hf (Fin.init y) h1] at h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, by rwa [← hf (Fin.init y) h1] at h3⟩

/-- **The extreme below-band is a single `*`-piece and sub-Pfaffian.**

Sheet data of a semi-Pfaffian set `X ⊆ ℝ^{p+(m+1)}` over the cell
`C = π_p (connectedComponentIn Z.set u₀)`: `k > 0` continuous sheets `s j : C → ℝ^{m+1}` whose
graphs over `C` are exactly the fibre of `X.set` (`hsub` + `hcov`) and which are pairwise distinct
over `C` (`hinj`), with levels non-decreasing in `j` on `C` (`hmono`).

Let `f : ℝ^p → ℝ` be
* the level of one of the sheets on `C` (`hwit`),
* strictly above `-1` on `C` (`hlt`),
* a lower bound on `C` for every sheet level that is not identically `-1` (`hmin`).

Then the open band `{y : π_p y ∈ C, -1 < y (last p) < f (π_p y)}` below `f` is the set of a single
`*`-piece with format `≤ A` and `*`-degree `≤ Cb.eval D` whenever `X.fmt, Z.fmt ≤ F` and
`X.deg, Z.deg ≤ D`, and it is sub-Pfaffian.

Proof sketch: if some sheet is identically `-1` on `C`, the band is the band between two sheets of
the same stratum and `bandCell_bd`/`bandSubPfX` apply; if no sheet is identically `-1`, `hmin`
forces the *first* sheet to have level exactly `f`, and `belowBandX`/`belowBandSubPfX` (index `0`)
apply.  For the sub-Pfaffian half no case split is needed: `belowBandSubPfX` at the witness index
of `hwit` already gives `SubPf` of the right set. -/
theorem belowExtremeCell (F : ℕ) :
    ∃ (A : ℕ) (Cb : Polynomial ℕ),
      ∀ (p m : ℕ) (X : WilkiesDesign.E.SemiPf (p + (m + 1)))
        (Z : WilkiesDesign.E.SemiPf (p + (m + 1))) (u₀ : Fin (p + (m + 1)) → ℝ)
        (hu₀ : u₀ ∈ Z.set) (C : Set (Fin p → ℝ))
        (hC : C = Set.image (WilkiesDesign.E.projFirst p (m + 1))
          (connectedComponentIn Z.set u₀))
        (hCpf : WilkiesDesign.E.SubPf p C)
        (k : ℕ) (hk : 0 < k) (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
        (hcont : ∀ j : Fin k, ContinuousOn (s j) C)
        (hinj : ∀ x ∈ C, Function.Injective fun j : Fin k => s j x)
        (hsub : ∀ j : Fin k, ∀ x ∈ C, Fin.append x (s j x) ∈ X.set)
        (hcov : ∀ z ∈ X.set, WilkiesDesign.E.projFirst p (m + 1) z ∈ C →
          ∃ j : Fin k, s j (WilkiesDesign.E.projFirst p (m + 1) z) =
            WilkiesDesign.E.projSnd p (m + 1) z)
        (hmono : ∀ x ∈ C, Monotone fun j : Fin k => (s j x) (Fin.last m))
        (f : (Fin p → ℝ) → ℝ)
        (hwit : ∃ j : Fin k, ∀ x ∈ C, f x = (s j x) (Fin.last m))
        (hlt : ∀ x ∈ C, -1 < f x)
        (hmin : ∀ j : Fin k, (∀ x ∈ C, f x ≤ (s j x) (Fin.last m)) ∨
          (∀ x ∈ C, (s j x) (Fin.last m) = -1))
        (D : ℕ)
        (hXF : X.fmt ≤ F) (hXD : X.deg ≤ D) (hZF : Z.fmt ≤ F) (hZD : Z.deg ≤ D),
      (∃ P : WilkiesDesign.E.StarPiece (p + 1),
          P.set = {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ -1 < y (Fin.last p) ∧
            y (Fin.last p) < f (Fin.init y)} ∧
          P.X.fmt ≤ A ∧ P.X.deg ≤ Cb.eval D) ∧
      WilkiesDesign.E.SubPf (p + 1)
        {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ -1 < y (Fin.last p) ∧
          y (Fin.last p) < f (Fin.init y)} := by
  classical
  -- the two format/degree data: the below-band piece (`belowBandX`) and the two-sheet band
  -- (`bandCell_bd`); we combine them with `max` and a sum of polynomials.
  obtain ⟨A₁, Cb₁, h₁⟩ := belowBandX F
  obtain ⟨A₂, Cb₂, h₂⟩ := bandCell_bd F
  refine ⟨max A₁ A₂, Cb₁ + Cb₂, ?_⟩
  intro p m X Z u₀ hu₀ C hC hCpf k hk s hcont hinj hsub hcov hmono f hwit hlt hmin D
    hXF hXD hZF hZD
  obtain ⟨j₀, hj₀⟩ := hwit
  -- the target set is the below-band of the witness sheet `j₀`
  have hGoalEq : {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ -1 < y (Fin.last p) ∧
        y (Fin.last p) < f (Fin.init y)}
      = {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ -1 < y (Fin.last p) ∧
        y (Fin.last p) < (s j₀ (Fin.init y)) (Fin.last m)} := extremeBandSet_eq j₀ hj₀
  refine ⟨?_, ?_⟩
  · -- the `*`-piece half
    by_cases hcase : ∃ i : Fin k, ∀ x ∈ C, (s i x) (Fin.last m) = -1
    · -- case 1: some sheet is identically `-1`; the band is the band between two sheets
      obtain ⟨i, hi⟩ := hcase
      have hle : ∀ x ∈ C, (s i x) (Fin.last m) < (s j₀ x) (Fin.last m) := by
        intro x hx
        rw [hi x hx, ← hj₀ x hx]
        exact hlt x hx
      obtain ⟨P, hPset, hPfmt, hPdeg⟩ :=
        h₂ p m X X Z u₀ hu₀ C hC hCpf k s hcont hinj hsub hcov k s hcont hinj hsub hcov
          i j₀ hle D hXF hXF hZF hXD hXD hZD
      have hBand_eq : {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧
            (s i (Fin.init y)) (Fin.last m) < y (Fin.last p) ∧
            y (Fin.last p) < (s j₀ (Fin.init y)) (Fin.last m)}
          = {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ -1 < y (Fin.last p) ∧
            y (Fin.last p) < f (Fin.init y)} := by
        ext y
        constructor
        · rintro ⟨h1, h2, h3⟩
          exact ⟨h1, by rwa [hi (Fin.init y) h1] at h2,
            by rwa [← hj₀ (Fin.init y) h1] at h3⟩
        · rintro ⟨h1, h2, h3⟩
          exact ⟨h1, by rwa [← hi (Fin.init y) h1] at h2,
            by rwa [hj₀ (Fin.init y) h1] at h3⟩
      refine ⟨P, hPset.trans hBand_eq, le_trans hPfmt (le_max_right A₁ A₂), ?_⟩
      rw [Polynomial.eval_add]
      exact le_trans hPdeg (Nat.le_add_left _ _)
    · -- case 2: no sheet is identically `-1`; `hmin` forces sheet `0` to carry the level `f`
      have hminAll : ∀ j : Fin k, ∀ x ∈ C, f x ≤ (s j x) (Fin.last m) := by
        intro j
        rcases hmin j with h | h
        · exact h
        · exact absurd h (fun hall => hcase ⟨j, hall⟩)
      have hf0 : ∀ x ∈ C, f x = (s ⟨0, hk⟩ x) (Fin.last m) := by
        intro x hx
        have hle1 : f x ≤ (s ⟨0, hk⟩ x) (Fin.last m) := hminAll ⟨0, hk⟩ x hx
        have hle2 : (s ⟨0, hk⟩ x) (Fin.last m) ≤ (s j₀ x) (Fin.last m) := by
          have h0 : (⟨0, hk⟩ : Fin k) ≤ j₀ := Fin.le_iff_val_le_val.mpr (Nat.zero_le _)
          exact hmono x hx h0
        rw [← hj₀ x hx] at hle2
        exact le_antisymm hle1 hle2
      have hlt0 : ∀ x ∈ C, -1 < (s ⟨0, hk⟩ x) (Fin.last m) := by
        intro x hx
        rw [← hf0 x hx]
        exact hlt x hx
      obtain ⟨P, hPset, hPfmt, hPdeg⟩ :=
        h₁ p m X Z u₀ hu₀ C hC hCpf k hk s hcont hinj hsub hcov hlt0 D hXF hXD hZF hZD
      have hEq : {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ -1 < y (Fin.last p) ∧
            y (Fin.last p) < f (Fin.init y)}
          = {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ -1 < y (Fin.last p) ∧
            y (Fin.last p) < (s ⟨0, hk⟩ (Fin.init y)) (Fin.last m)} :=
        extremeBandSet_eq ⟨0, hk⟩ hf0
      refine ⟨P, hPset.trans hEq.symm, le_trans hPfmt (le_max_left A₁ A₂), ?_⟩
      rw [Polynomial.eval_add]
      exact le_trans hPdeg (Nat.le_add_right _ _)
  · -- the sub-Pfaffian half: `belowBandSubPfX` at the witness index
    rw [hGoalEq]
    exact belowBandSubPfX p m X C hCpf k s hinj hsub hcov hmono j₀

end Work.WilE7.SheetData
