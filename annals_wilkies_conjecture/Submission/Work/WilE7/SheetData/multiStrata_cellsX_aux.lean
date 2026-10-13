import Mathlib
import Submission.Work.WilE7.DecompDefs
import Submission.Work.WilE7.SheetData.graphCellSubPfX
import Submission.Work.WilE7.SheetData.aboveBandSubPfX
import Submission.Work.WilE7.SheetData.belowBandSubPfX
import Submission.Work.WilE7.CoreStep.subPf_inter
import Submission.Work.WilE7.SheetData.graphCellStar_piece

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
noncomputable section
open Classical

namespace Work.WilE7.SheetData

open WilkiesDesign WilkiesDesign.E
open Work.WilE7 (gr bd)

/-! ## Helper lemmas for `Work.WilE7.SheetData.multiStrata_cellsX` -/

/-- Two band cells with pointwise equal boundary functions on the base cell are equal. -/
theorem bd_congr {n : ℕ} {C : Set (Fin n → ℝ)} (a a' b b' : (Fin n → ℝ) → ℝ)
    (ha : ∀ x ∈ C, a x = a' x) (hb : ∀ x ∈ C, b x = b' x) :
    bd C a b = bd C a' b' := by
  ext y
  simp only [bd, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hyC, h1, h2⟩
    exact ⟨hyC, by rw [← ha _ hyC]; exact h1, by rw [← hb _ hyC]; exact h2⟩
  · rintro ⟨hyC, h1, h2⟩
    exact ⟨hyC, by rw [ha _ hyC]; exact h1, by rw [hb _ hyC]; exact h2⟩

/-- Two graph cells with pointwise equal graph functions on the base cell are equal. -/
theorem gr_congr {n : ℕ} {C : Set (Fin n → ℝ)} (f f' : (Fin n → ℝ) → ℝ)
    (hf : ∀ x ∈ C, f x = f' x) : gr C f = gr C f' := by
  ext y
  simp only [gr, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hyC, h⟩
    exact ⟨hyC, by rw [← hf _ hyC]; exact h⟩
  · rintro ⟨hyC, h⟩
    exact ⟨hyC, by rw [hf _ hyC]; exact h⟩

/-- **The graph cell of a sheet is a single `*`-piece, uniformly.**  The bound is obtained by
specialising `Work.WilE7.SheetData.graphCellStar_piece` to `X.fmt, Z.fmt ≤ F` and
`X.deg, Z.deg ≤ D`. -/
theorem graphCellStarX (F : ℕ) :
    ∃ (A : ℕ) (Cb : Polynomial ℕ),
      ∀ (p m : ℕ) (X : WilkiesDesign.E.SemiPf (p + (m + 1)))
        (Z : WilkiesDesign.E.SemiPf (p + (m + 1))) (u₀ : Fin (p + (m + 1)) → ℝ) (hu₀ : u₀ ∈ Z.set)
        (C : Set (Fin p → ℝ))
        (hC : C = Set.image (WilkiesDesign.E.projFirst p (m + 1)) (connectedComponentIn Z.set u₀))
        (hCpf : WilkiesDesign.E.SubPf p C)
        (k : ℕ) (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
        (hcont : ∀ j, ContinuousOn (s j) C)
        (hinj : ∀ x ∈ C, Function.Injective fun j : Fin k => s j x)
        (hsub : ∀ j : Fin k, ∀ x ∈ C, Fin.append x (s j x) ∈ X.set)
        (hcov : ∀ z ∈ X.set, WilkiesDesign.E.projFirst p (m + 1) z ∈ C →
          ∃ j : Fin k, s j (WilkiesDesign.E.projFirst p (m + 1) z) =
            WilkiesDesign.E.projSnd p (m + 1) z)
        (j : Fin k) (D : ℕ),
        X.fmt ≤ F → Z.fmt ≤ F → X.deg ≤ D → Z.deg ≤ D →
        ∃ P : WilkiesDesign.E.StarPiece (p + 1),
          P.set = {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧
            y (Fin.last p) = (s j (Fin.init y)) (Fin.last m)} ∧
          P.X.fmt ≤ A ∧ P.X.deg ≤ Cb.eval D := by
  refine ⟨2 * F + 1, Polynomial.C (2 * (1 + F)) * (1 + 2 * Polynomial.X) ^ 2, ?_⟩
  intro p m X Z u₀ hu₀ C hC hCpf k s hcont hinj hsub hcov j D hXF hZF hXD hZD
  obtain ⟨P, hPset, hPfmt, hPdeg⟩ :=
    graphCellStar_piece X Z u₀ hu₀ C hC hCpf k s hcont hinj hsub hcov j
  refine ⟨P, hPset, ?_, ?_⟩
  · have hmax : max X.fmt Z.fmt ≤ F := max_le hXF hZF
    omega
  · have hev : (Polynomial.C (2 * (1 + F)) * (1 + 2 * Polynomial.X) ^ 2 : Polynomial ℕ).eval D
        = 2 * (1 + F) * (1 + 2 * D) ^ 2 := by
      simp [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X,
        Polynomial.eval_C, Polynomial.eval_one]
    rw [hev]
    have hmax : max X.fmt Z.fmt ≤ F := max_le hXF hZF
    have h1 : 1 + max X.fmt Z.fmt ≤ 1 + F := by omega
    have h2 : (1 + (Z.deg + X.deg)) ^ 2 ≤ (1 + 2 * D) ^ 2 := by
      have h3 : 1 + (Z.deg + X.deg) ≤ 1 + 2 * D := by omega
      exact Nat.pow_le_pow_left h3 2
    exact le_trans hPdeg (Nat.mul_le_mul (Nat.mul_le_mul_left 2 h1) h2)

/-- The level of a sheet over the base cell is bounded by `1` in absolute value. -/
theorem sheet_level_abs_le_one {p m k : ℕ} {X : WilkiesDesign.E.SemiPf (p + (m + 1))}
    {C : Set (Fin p → ℝ)} {s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ)}
    (hsub : ∀ j : Fin k, ∀ x ∈ C, Fin.append x (s j x) ∈ X.set)
    (j : Fin k) {x : Fin p → ℝ} (hx : x ∈ C) :
    |(s j x) (Fin.last m)| ≤ 1 := by
  have hcube := (hsub j x hx).1 (Fin.natAdd p (Fin.last m))
  rwa [Fin.append_right] at hcube

/-- **The band between two sheets is the intersection of the band above the lower sheet and
the band below the upper one.**  The two extra constraints `y < 1` and `-1 < y` are redundant
because the sheet levels lie in `[-1,1]`. -/
theorem bandX_eq_inter {p m : ℕ} (X₁ X₂ : WilkiesDesign.E.SemiPf (p + (m + 1)))
    (C : Set (Fin p → ℝ))
    {k₁ : ℕ} {s₁ : Fin k₁ → (Fin p → ℝ) → (Fin (m + 1) → ℝ)}
    (hsub₁ : ∀ j : Fin k₁, ∀ x ∈ C, Fin.append x (s₁ j x) ∈ X₁.set)
    {k₂ : ℕ} {s₂ : Fin k₂ → (Fin p → ℝ) → (Fin (m + 1) → ℝ)}
    (hsub₂ : ∀ j : Fin k₂, ∀ x ∈ C, Fin.append x (s₂ j x) ∈ X₂.set)
    (i : Fin k₁) (j : Fin k₂) :
    {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧
        (s₁ i (Fin.init y)) (Fin.last m) < y (Fin.last p) ∧
        y (Fin.last p) < (s₂ j (Fin.init y)) (Fin.last m)}
      = {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧
          (s₁ i (Fin.init y)) (Fin.last m) < y (Fin.last p) ∧ y (Fin.last p) < 1} ∩
        {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ -1 < y (Fin.last p) ∧
          y (Fin.last p) < (s₂ j (Fin.init y)) (Fin.last m)} := by
  ext y
  constructor
  · rintro ⟨hyC, h1, h2⟩
    have hb1 := sheet_level_abs_le_one hsub₁ i hyC
    have hb2 := sheet_level_abs_le_one hsub₂ j hyC
    exact ⟨⟨hyC, h1, lt_of_lt_of_le h2 (abs_le.mp hb2).2⟩,
      ⟨hyC, lt_of_le_of_lt (abs_le.mp hb1).1 h1, h2⟩⟩
  · rintro ⟨⟨hyC, h1, _⟩, ⟨_, _, h2⟩⟩
    exact ⟨hyC, h1, h2⟩

/-- **The interior band between two sheets is sub-Pfaffian.**  It is the intersection of the
band above the lower sheet (`aboveBandSubPfX`) and the band below the upper one
(`belowBandSubPfX`); `SubPf` is closed under intersections (`CoreStep.subPf_inter`). -/
theorem bandSubPfX {p m : ℕ} (X₁ X₂ : WilkiesDesign.E.SemiPf (p + (m + 1)))
    (C : Set (Fin p → ℝ)) (hCpf : WilkiesDesign.E.SubPf p C)
    {k₁ : ℕ} {s₁ : Fin k₁ → (Fin p → ℝ) → (Fin (m + 1) → ℝ)}
    (hinj₁ : ∀ x ∈ C, Function.Injective fun j : Fin k₁ => s₁ j x)
    (hsub₁ : ∀ j : Fin k₁, ∀ x ∈ C, Fin.append x (s₁ j x) ∈ X₁.set)
    (hcov₁ : ∀ z ∈ X₁.set, WilkiesDesign.E.projFirst p (m + 1) z ∈ C →
      ∃ j : Fin k₁, s₁ j (WilkiesDesign.E.projFirst p (m + 1) z) =
        WilkiesDesign.E.projSnd p (m + 1) z)
    (hmono₁ : ∀ x ∈ C, Monotone fun j : Fin k₁ => (s₁ j x) (Fin.last m))
    {k₂ : ℕ} {s₂ : Fin k₂ → (Fin p → ℝ) → (Fin (m + 1) → ℝ)}
    (hinj₂ : ∀ x ∈ C, Function.Injective fun j : Fin k₂ => s₂ j x)
    (hsub₂ : ∀ j : Fin k₂, ∀ x ∈ C, Fin.append x (s₂ j x) ∈ X₂.set)
    (hcov₂ : ∀ z ∈ X₂.set, WilkiesDesign.E.projFirst p (m + 1) z ∈ C →
      ∃ j : Fin k₂, s₂ j (WilkiesDesign.E.projFirst p (m + 1) z) =
        WilkiesDesign.E.projSnd p (m + 1) z)
    (hmono₂ : ∀ x ∈ C, Monotone fun j : Fin k₂ => (s₂ j x) (Fin.last m))
    (i : Fin k₁) (j : Fin k₂) :
    WilkiesDesign.E.SubPf (p + 1)
      {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧
        (s₁ i (Fin.init y)) (Fin.last m) < y (Fin.last p) ∧
        y (Fin.last p) < (s₂ j (Fin.init y)) (Fin.last m)} := by
  have h₁ := aboveBandSubPfX p m X₁ C hCpf k₁ s₁ hinj₁ hsub₁ hcov₁ hmono₁ i
  have h₂ := belowBandSubPfX p m X₂ C hCpf k₂ s₂ hinj₂ hsub₂ hcov₂ hmono₂ j
  rw [bandX_eq_inter X₁ X₂ C hsub₁ hsub₂ i j]
  exact Work.WilE7.CoreStep.subPf_inter h₁ h₂

end Work.WilE7.SheetData
