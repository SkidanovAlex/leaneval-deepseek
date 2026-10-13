import Mathlib
import Submission.Work.WilE7.SheetData.aboveBandX
import Submission.Work.WilE7.SheetData.aboveBandSubPfX
import Submission.Work.WilE7.SheetData.bandCell_bd
import Submission.Work.WilE7.SheetData.multiStrata_cellsX_aux

-- the hypotheses of the target live inside the `∀` of an `∃ … ∀ …` statement; the unused-variable
-- linter mis-reports such binders, which cannot be renamed without changing the statement
set_option linter.unusedVariables false

namespace Work.WilE7.SheetData

/-- **The extreme above-band is a single `*`-piece and sub-Pfaffian** (mirror of
`belowExtremeCell`).

Sheet data of a semi-Pfaffian set `X ⊆ ℝ^{p+(m+1)}` over the cell
`C = π_p (connectedComponentIn Z.set u₀)`: `k > 0` continuous sheets `s j : C → ℝ^{m+1}` whose
graphs over `C` are exactly the fibre of `X.set` (`hsub` + `hcov`), pairwise distinct over `C`
(`hinj`), with levels non-decreasing in `j` on `C` (`hmono`).

Let `f : ℝ^p → ℝ` be
* the level of one of the sheets on `C` (`hwit`),
* strictly below `1` on `C` (`hgt`),
* an upper bound on `C` for every sheet level that is not identically `1` (`hmax`).

Then the open band `{y : π_p y ∈ C, f (π_p y) < y (last p) < 1}` above `f` is the set of a single
`*`-piece with format `≤ A` and `*`-degree `≤ Cb.eval D` whenever `X.fmt, Z.fmt ≤ F` and
`X.deg, Z.deg ≤ D`, and it is sub-Pfaffian.

Proof sketch: if some sheet is identically `1` on `C`, the band is the band between two sheets of
the same stratum and `bandCell_bd`/`bandSubPfX` apply; if no sheet is identically `1`, `hmax`
forces the *last* sheet to have level exactly `f`, and `aboveBandX`/`aboveBandSubPfX` (index
`k-1`) apply.  For the sub-Pfaffian half no case split is needed: `aboveBandSubPfX` at the witness
index of `hwit` already gives `SubPf` of the right set. -/
theorem aboveExtremeCell (F : ℕ) :
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
        (hgt : ∀ x ∈ C, f x < 1)
        (hmax : ∀ j : Fin k, (∀ x ∈ C, (s j x) (Fin.last m) ≤ f x) ∨
          (∀ x ∈ C, (s j x) (Fin.last m) = 1))
        (D : ℕ)
        (hXF : X.fmt ≤ F) (hXD : X.deg ≤ D) (hZF : Z.fmt ≤ F) (hZD : Z.deg ≤ D),
      (∃ P : WilkiesDesign.E.StarPiece (p + 1),
          P.set = {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ f (Fin.init y) < y (Fin.last p) ∧
            y (Fin.last p) < 1} ∧
          P.X.fmt ≤ A ∧ P.X.deg ≤ Cb.eval D) ∧
      WilkiesDesign.E.SubPf (p + 1)
        {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ f (Fin.init y) < y (Fin.last p) ∧
          y (Fin.last p) < 1} := by
  -- the two packaged constructions: the band above the sheet `k-1` and the band between two sheets
  obtain ⟨A₁, Cb₁, hAB⟩ := aboveBandX F
  obtain ⟨A₂, Cb₂, hBC⟩ := bandCell_bd F
  refine ⟨max A₁ A₂, Cb₁ + Cb₂, ?_⟩
  intro p m X Z u₀ hu₀ C hC hCpf k hk s hcont hinj hsub hcov hmono f hwit hgt hmax D
    hXF hXD hZF hZD
  -- the sub-Pfaffian half: `aboveBandSubPfX` at the witness index of `hwit`
  have hsubpf : WilkiesDesign.E.SubPf (p + 1)
      {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ f (Fin.init y) < y (Fin.last p) ∧
        y (Fin.last p) < 1} := by
    obtain ⟨j, hj⟩ := hwit
    have hbase := aboveBandSubPfX p m X C hCpf k s hinj hsub hcov hmono j
    have hset : {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧
          (s j (Fin.init y)) (Fin.last m) < y (Fin.last p) ∧ y (Fin.last p) < 1}
        = {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ f (Fin.init y) < y (Fin.last p) ∧
          y (Fin.last p) < 1} := by
      ext y
      simp only [Set.mem_ofPred_eq]
      constructor
      · rintro ⟨h1, h2, h3⟩
        exact ⟨h1, by rw [hj _ h1]; exact h2, h3⟩
      · rintro ⟨h1, h2, h3⟩
        exact ⟨h1, by rw [← hj _ h1]; exact h2, h3⟩
    rw [hset] at hbase
    exact hbase
  refine ⟨?_, hsubpf⟩
  -- the `*`-piece half, by cases on whether some sheet is identically `1`
  by_cases hcase : ∃ l : Fin k, ∀ x ∈ C, (s l x) (Fin.last m) = 1
  · -- **Case 1**: a sheet `l` is identically `1`; the band is the band between the sheets
    -- `j` (witness of `hwit`) and `l`
    obtain ⟨l, hl⟩ := hcase
    obtain ⟨j, hj⟩ := hwit
    have hle : ∀ x ∈ C, (s j x) (Fin.last m) < (s l x) (Fin.last m) := by
      intro x hx
      rw [← hj x hx, hl x hx]
      exact hgt x hx
    obtain ⟨P, hPset, hPfmt, hPdeg⟩ :=
      hBC p m X X Z u₀ hu₀ C hC hCpf k s hcont hinj hsub hcov k s hcont hinj hsub hcov
        j l hle D hXF hXF hZF hXD hXD hZD
    refine ⟨P, ?_, le_trans hPfmt (le_max_right _ _), ?_⟩
    · rw [hPset]
      ext y
      simp only [Set.mem_ofPred_eq]
      constructor
      · rintro ⟨h1, h2, h3⟩
        exact ⟨h1, by rw [hj _ h1]; exact h2, by rw [← hl _ h1]; exact h3⟩
      · rintro ⟨h1, h2, h3⟩
        exact ⟨h1, by rw [← hj _ h1]; exact h2, by rw [hl _ h1]; exact h3⟩
    · rw [Polynomial.eval_add]
      exact le_trans hPdeg (Nat.le_add_left _ _)
  · -- **Case 2**: no sheet is identically `1`; `hmax` forces the last sheet to have level `f`,
    -- and `aboveBandX` at index `k-1` applies
    obtain ⟨j₀, hj₀⟩ := hwit
    -- every sheet level is `≤ f`
    have hle_j : ∀ j : Fin k, ∀ x ∈ C, (s j x) (Fin.last m) ≤ f x := by
      intro j
      rcases hmax j with h | h
      · exact h
      · exact absurd ⟨j, h⟩ hcase
    -- the top sheet has level exactly `f`
    have hf_top : ∀ x ∈ C, (s ⟨k - 1, by omega⟩ x) (Fin.last m) = f x := by
      intro x hx
      have h1 : (s ⟨k - 1, by omega⟩ x) (Fin.last m) ≤ f x := hle_j _ x hx
      have h2 : (s j₀ x) (Fin.last m) ≤ (s ⟨k - 1, by omega⟩ x) (Fin.last m) := by
        apply hmono x hx
        rw [Fin.le_iff_val_le_val]
        show j₀.val ≤ k - 1
        have := j₀.isLt
        omega
      have h3 : f x = (s j₀ x) (Fin.last m) := hj₀ x hx
      linarith
    have hgt' : ∀ x ∈ C, (s ⟨k - 1, by omega⟩ x) (Fin.last m) < 1 := fun x hx => by
      rw [hf_top x hx]
      exact hgt x hx
    obtain ⟨P, hPset, hPfmt, hPdeg⟩ :=
      hAB p m X Z u₀ hu₀ C hC hCpf k hk s hcont hinj hsub hcov hgt' D hXF hXD hZF hZD
    refine ⟨P, ?_, le_trans hPfmt (le_max_left _ _), ?_⟩
    · rw [hPset]
      ext y
      simp only [Set.mem_ofPred_eq]
      constructor
      · rintro ⟨h1, h2, h3⟩
        exact ⟨h1, by rw [← hf_top _ h1]; exact h2, h3⟩
      · rintro ⟨h1, h2, h3⟩
        exact ⟨h1, by rw [hf_top _ h1]; exact h2, h3⟩
    · rw [Polynomial.eval_add]
      exact le_trans hPdeg (Nat.le_add_right _ _)

end Work.WilE7.SheetData
