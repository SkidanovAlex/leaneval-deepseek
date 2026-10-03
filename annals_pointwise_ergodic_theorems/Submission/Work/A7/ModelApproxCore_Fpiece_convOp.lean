import Mathlib
import Submission.Work.KMTAreas.A7.ModelApproxKer

/-!
# `Fpiece` as a convolution with the explicit kernel `pieceKer`

We prove

`Fpiece (kmtPj ρ) 0 l₁ k₁ N f = convOp (pieceKer ρ l₁ (fun s => -logN N + s) 0 k₁) f`

for bounded `f`.  The identity is the elementary additivity of `convOp` in its kernel: `piExact`
(hence `piece`, hence `Fpiece`) is a finite difference of Ionescu--Wainger projections, and
`exactKer` (hence `pieceKer`) is the *same* finite difference of the corresponding kernels, so the
two sides agree kernel by kernel, the only content being that the convolution sums are summable --
which is exactly the hypothesis `BoundedZ f` (`Work.KMTAreas.A5.summable_kmtKern_mul`).

No symbol algebra is needed: `exactKer` is *defined* as the difference of the `kmtKern`s, so the
only bridges are `kmtProj_eq_conv` (`kmtProj` is the convolution with `kmtKern`) and the
summability of the families (`Summable.tsum_sub`).
-/

namespace Work.A7

open Work.KMTAreas.A5
open Work.KMTAreas.A7

noncomputable section

/-! ## Unfoldings of the exact-height pieces -/

/-- The exact-height kernel at `l = 0` is `kmtKern ρ 0 k`. -/
theorem exactKer_zero (ρ : ℝ) (k : ℤ) : exactKer ρ 0 k = kmtKern ρ 0 k := rfl

/-- The exact-height kernel away from `l = 0` is a difference of two `kmtKern`s. -/
theorem exactKer_of_ne (ρ : ℝ) {l : ℕ} (hl : l ≠ 0) (k : ℤ) :
    exactKer ρ l k = kmtKern ρ l k - kmtKern ρ (l - 1) k := by
  rw [exactKer, if_neg hl]

/-- The exact-height projection at `l = 0` is `kmtProj ρ 0 k`. -/
theorem piExact_zero (ρ : ℝ) (k : ℤ) (f : ℤ → ℂ) :
    Work.Analysis.EndVar.piExact (Work.KMTContract.kmtPj ρ) 0 k f
      = Work.KMTContract.kmtProj ρ 0 k f := rfl

/-- The exact-height projection away from `l = 0` is a difference of two projections. -/
theorem piExact_of_ne (ρ : ℝ) {l : ℕ} (hl : l ≠ 0) (k : ℤ) (f : ℤ → ℂ) :
    Work.Analysis.EndVar.piExact (Work.KMTContract.kmtPj ρ) l k f
      = Work.KMTContract.kmtProj ρ l k f - Work.KMTContract.kmtProj ρ (l - 1) k f := by
  simp only [Work.Analysis.EndVar.piExact, if_neg hl, Work.KMTContract.kmtPj_proj]

/-! ## Linearity of `convOp` in its kernel -/

/-- **Linearity of `convOp` in its kernel**, for pointwise summable families.  This is the only
place where `tsum` additivity is used; it needs the two families to be summable, which for the
`kmtKern`s is automatic for bounded input (`summable_kmtKern_mul`). -/
theorem convOp_sub {κ₁ κ₂ u : ℤ → ℂ}
    (h₁ : ∀ x : ℤ, Summable fun j : ℤ => κ₁ j * u (x - j))
    (h₂ : ∀ x : ℤ, Summable fun j : ℤ => κ₂ j * u (x - j)) :
    convOp (κ₁ - κ₂) u = convOp κ₁ u - convOp κ₂ u := by
  funext x
  simp only [convOp]
  rw [show (∑' j : ℤ, (κ₁ - κ₂) j * u (x - j))
        = ∑' j : ℤ, (κ₁ j * u (x - j) - κ₂ j * u (x - j)) from
      tsum_congr fun j => by rw [Pi.sub_apply]; ring]
  exact (h₁ x).tsum_sub (h₂ x)

/-- The convolution with `kmtKern ρ l k` is `kmtProj ρ l k` (pointwise, for every `f`). -/
theorem convOp_kmtKern (ρ : ℝ) (l : ℕ) (k : ℤ) (f : ℤ → ℂ) :
    convOp (kmtKern ρ l k) f = Work.KMTContract.kmtProj ρ l k f := by
  funext n
  rw [convOp, Work.KMTAreas.A5.kmtProj_eq_conv]

/-- A `kmtKern`-family times a bounded function is summable. -/
theorem summable_exactKer_mul (ρ : ℝ) (l : ℕ) (k : ℤ) {f : ℤ → ℂ} (hf : BoundedZ f) (x : ℤ) :
    Summable fun j : ℤ => exactKer ρ l k j * f (x - j) := by
  rcases eq_or_ne l 0 with hl | hl
  · subst hl
    rw [exactKer_zero]
    exact summable_kmtKern_mul ρ 0 k hf x
  · rw [exactKer_of_ne ρ hl]
    rw [show (fun j : ℤ => (kmtKern ρ l k - kmtKern ρ (l - 1) k) j * f (x - j))
          = fun j : ℤ =>
              (kmtKern ρ l k j * f (x - j) - kmtKern ρ (l - 1) k j * f (x - j)) from
        funext fun j => by rw [Pi.sub_apply]; ring]
    exact (summable_kmtKern_mul ρ l k hf x).sub (summable_kmtKern_mul ρ (l - 1) k hf x)

/-! ## The two identifications -/

/-- **The exact-height projection is the convolution with `exactKer`**, for bounded input. -/
theorem piExact_eq_convOp (ρ : ℝ) (l : ℕ) (k : ℤ) {f : ℤ → ℂ} (hf : BoundedZ f) :
    Work.Analysis.EndVar.piExact (Work.KMTContract.kmtPj ρ) l k f
      = convOp (exactKer ρ l k) f := by
  rcases eq_or_ne l 0 with hl | hl
  · subst hl
    rw [piExact_zero, exactKer_zero]
    exact (convOp_kmtKern ρ 0 k f).symm
  · rw [piExact_of_ne ρ hl, exactKer_of_ne ρ hl,
      convOp_sub (fun x => summable_kmtKern_mul ρ l k hf x)
        (fun x => summable_kmtKern_mul ρ (l - 1) k hf x)]
    rw [convOp_kmtKern, convOp_kmtKern]

/-- **The continuous piece is the convolution with `pieceKer`**: `piece` and `pieceKer` are the
same case distinction, so the identity follows from `piExact_eq_convOp` in both branches. -/
theorem piece_eq_convOp (ρ : ℝ) (l : ℕ) (κs : ℤ → ℤ) (a s : ℤ) {f : ℤ → ℂ} (hf : BoundedZ f) :
    Work.Analysis.EndVar.piece (Work.KMTContract.kmtPj ρ) l κs a s f
      = convOp (pieceKer ρ l κs a s) f := by
  rw [Work.Analysis.EndVar.piece, pieceKer]
  split_ifs with h
  · exact piExact_eq_convOp ρ l (κs s) hf
  · rw [piExact_eq_convOp ρ l (κs s) hf, piExact_eq_convOp ρ l (κs (s - 1)) hf]
    exact (convOp_sub (fun x => summable_exactKer_mul ρ l (κs s) hf x)
      (fun x => summable_exactKer_mul ρ l (κs (s - 1)) hf x)).symm

/-- `Fpiece` is the convolution with the explicit kernel `pieceKer`. -/
theorem ModelApproxCore_Fpiece_convOp (ρ : ℝ) (l₁ k₁ N : ℕ) {f : ℤ → ℂ}
    (hf : Work.KMTAreas.A5.BoundedZ f) :
    Work.Analysis.EndVar.Fpiece (Work.KMTContract.kmtPj ρ) 0 l₁ (k₁ : ℤ) N f
      = Work.KMTAreas.A7.convOp
          (Work.KMTAreas.A7.pieceKer ρ l₁ (fun s : ℤ => -(Work.Analysis.EndVar.logN N) + s) 0 (k₁ : ℤ)) f := by
  simp only [Work.Analysis.EndVar.Fpiece]
  exact piece_eq_convOp ρ l₁ (fun s : ℤ => -(Work.Analysis.EndVar.logN N) + s) (-(0 : ℤ)) (k₁ : ℤ) hf

end

end Work.A7
