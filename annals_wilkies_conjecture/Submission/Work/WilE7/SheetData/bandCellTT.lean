import Mathlib
import Submission.Work.WilE7.SheetData.multiStrata_cellsX_aux
import Submission.Work.WilE7.SheetData.bandCell_bd

namespace Work.WilE7.SheetData

/-- **The band between the levels of two sheets is a single `*`-piece and sub-Pfaffian.**

Sheet data of two semi-Pfaffian sets `X₁, X₂ ⊆ ℝ^{p+(m+1)}` over the cell
`C = π_p (connectedComponentIn Z.set u₀)`: continuous sheets `sᵢ j : C → ℝ^{m+1}` whose graphs over
`C` are exactly the fibres of `Xᵢ.set` (`hsubᵢ` + `hcovᵢ`), pairwise distinct over `C` (`hinjᵢ`),
with levels non-decreasing in `j` on `C` (`hmonoᵢ`).  If `fᵢ` is the level of one of the sheets of
the `i`-th family on `C` and `f₁ x < f₂ x` for every `x ∈ C`, then the open band
`{y : π_p y ∈ C, f₁ (π_p y) < y (last p) < f₂ (π_p y)}` is a single `*`-piece with format `≤ A`
and `*`-degree `≤ Cb.eval D` whenever `X₁.fmt, X₂.fmt, Z.fmt ≤ F` and `X₁.deg, X₂.deg, Z.deg ≤ D`,
and it is sub-Pfaffian.

(The `*`-piece half is `bandCell_bd`; the sub-Pfaffian half is `bandSubPfX`, i.e. the intersection
of the region above the lower sheet and the region below the upper sheet.) -/
theorem bandCellTT (F : ℕ) :
    ∃ (A : ℕ) (Cb : Polynomial ℕ),
      ∀ (p m : ℕ) (X₁ X₂ : WilkiesDesign.E.SemiPf (p + (m + 1)))
        (Z : WilkiesDesign.E.SemiPf (p + (m + 1))) (u₀ : Fin (p + (m + 1)) → ℝ)
        (hu₀ : u₀ ∈ Z.set) (C : Set (Fin p → ℝ))
        (hC : C = Set.image (WilkiesDesign.E.projFirst p (m + 1))
          (connectedComponentIn Z.set u₀))
        (hCpf : WilkiesDesign.E.SubPf p C)
        (k₁ : ℕ) (s₁ : Fin k₁ → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
        (hcont₁ : ∀ j : Fin k₁, ContinuousOn (s₁ j) C)
        (hinj₁ : ∀ x ∈ C, Function.Injective fun j : Fin k₁ => s₁ j x)
        (hsub₁ : ∀ j : Fin k₁, ∀ x ∈ C, Fin.append x (s₁ j x) ∈ X₁.set)
        (hcov₁ : ∀ z ∈ X₁.set, WilkiesDesign.E.projFirst p (m + 1) z ∈ C →
          ∃ j : Fin k₁, s₁ j (WilkiesDesign.E.projFirst p (m + 1) z) =
            WilkiesDesign.E.projSnd p (m + 1) z)
        (hmono₁ : ∀ x ∈ C, Monotone fun j : Fin k₁ => (s₁ j x) (Fin.last m))
        (k₂ : ℕ) (s₂ : Fin k₂ → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
        (hcont₂ : ∀ j : Fin k₂, ContinuousOn (s₂ j) C)
        (hinj₂ : ∀ x ∈ C, Function.Injective fun j : Fin k₂ => s₂ j x)
        (hsub₂ : ∀ j : Fin k₂, ∀ x ∈ C, Fin.append x (s₂ j x) ∈ X₂.set)
        (hcov₂ : ∀ z ∈ X₂.set, WilkiesDesign.E.projFirst p (m + 1) z ∈ C →
          ∃ j : Fin k₂, s₂ j (WilkiesDesign.E.projFirst p (m + 1) z) =
            WilkiesDesign.E.projSnd p (m + 1) z)
        (hmono₂ : ∀ x ∈ C, Monotone fun j : Fin k₂ => (s₂ j x) (Fin.last m))
        (f₁ f₂ : (Fin p → ℝ) → ℝ)
        (hwit₁ : ∃ j : Fin k₁, ∀ x ∈ C, f₁ x = (s₁ j x) (Fin.last m))
        (hwit₂ : ∃ j : Fin k₂, ∀ x ∈ C, f₂ x = (s₂ j x) (Fin.last m))
        (hlt : ∀ x ∈ C, f₁ x < f₂ x)
        (D : ℕ) (hXF₁ : X₁.fmt ≤ F) (hXF₂ : X₂.fmt ≤ F) (hZF : Z.fmt ≤ F)
        (hXD₁ : X₁.deg ≤ D) (hXD₂ : X₂.deg ≤ D) (hZD : Z.deg ≤ D),
      (∃ P : WilkiesDesign.E.StarPiece (p + 1),
          P.set = {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ f₁ (Fin.init y) < y (Fin.last p) ∧
            y (Fin.last p) < f₂ (Fin.init y)} ∧
          P.X.fmt ≤ A ∧ P.X.deg ≤ Cb.eval D) ∧
      WilkiesDesign.E.SubPf (p + 1)
        {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ f₁ (Fin.init y) < y (Fin.last p) ∧
          y (Fin.last p) < f₂ (Fin.init y)} := by
  obtain ⟨A, Cb, hbd⟩ := bandCell_bd F
  refine ⟨A, Cb, ?_⟩
  intro p m X₁ X₂ Z u₀ hu₀ C hC hCpf k₁ s₁ hcont₁ hinj₁ hsub₁ hcov₁ hmono₁
    k₂ s₂ hcont₂ hinj₂ hsub₂ hcov₂ hmono₂ f₁ f₂ hwit₁ hwit₂ hlt D
    hXF₁ hXF₂ hZF hXD₁ hXD₂ hZD
  -- the sheets realising the two levels
  obtain ⟨i, hi⟩ := hwit₁
  obtain ⟨j, hj⟩ := hwit₂
  have hle : ∀ x ∈ C, (s₁ i x) (Fin.last m) < (s₂ j x) (Fin.last m) := by
    intro x hx
    rw [← hi x hx, ← hj x hx]
    exact hlt x hx
  -- the `*`-piece half
  obtain ⟨P, hPset, hPfmt, hPdeg⟩ :=
    hbd p m X₁ X₂ Z u₀ hu₀ C hC hCpf k₁ s₁ hcont₁ hinj₁ hsub₁ hcov₁
      k₂ s₂ hcont₂ hinj₂ hsub₂ hcov₂ i j hle D hXF₁ hXF₂ hZF hXD₁ hXD₂ hZD
  -- the two descriptions of the band agree
  have heq : {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧
        (s₁ i (Fin.init y)) (Fin.last m) < y (Fin.last p) ∧
        y (Fin.last p) < (s₂ j (Fin.init y)) (Fin.last m)}
      = {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ f₁ (Fin.init y) < y (Fin.last p) ∧
        y (Fin.last p) < f₂ (Fin.init y)} := by
    ext y
    constructor
    · rintro ⟨hy, h1, h2⟩
      exact ⟨hy, by rw [hi _ hy]; exact h1, by rw [hj _ hy]; exact h2⟩
    · rintro ⟨hy, h1, h2⟩
      exact ⟨hy, by rw [← hi _ hy]; exact h1, by rw [← hj _ hy]; exact h2⟩
  refine ⟨⟨P, hPset.trans heq, hPfmt, hPdeg⟩, ?_⟩
  -- the sub-Pfaffian half
  have hsp := bandSubPfX X₁ X₂ C hCpf hinj₁ hsub₁ hcov₁ hmono₁
    hinj₂ hsub₂ hcov₂ hmono₂ i j
  rwa [heq] at hsp

end Work.WilE7.SheetData
