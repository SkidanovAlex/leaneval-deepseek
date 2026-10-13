/-
  annals_wilkies_conjecture, AREA E3, count half of the frame step: the *cut system*.

  The count half of `E3_identity` bounds the order of vanishing of `f` on `{h = 0}` by
  `MultiplicityBound` applied to a square system of `k` equations in `k` unknowns whose zero set
  near `x` is a curve through `x` inside `{h = 0}`:

  * the `j` equations `h a` (rows `rowH`),
  * `k - j - 1` real affine forms `Σ_{i ∈ ιᶜ} μ a i · (z_i - x_i)` cutting the tangent space of
    `{h = 0}` down to a line (rows `rowL`, with `μ` from `Work.WilE3.Frame.exists_cut_forms`),
  * the equation `f` (row `rowF`).

  This file only fixes the vocabulary: the straightening predicate `IsStraightening` (the conclusion
  of `Work.WilE3.Frame.exists_param`), the cut-form predicate `CutForms`, the row maps
  `rowH, rowL, rowF`, the system `cutSys`, the constant perturbation `pertSys` used to realise the
  right hand side `f = ε`, and the row lemmas identifying the three blocks.
-/
import Mathlib
import Submission.Work.WilE3.Defs
import Submission.Work.WilE3.Frame.Setup
import Submission.Work.WilE3.Frame.Vcoef
import Submission.Work.WilE3.Frame.Count

namespace Work.WilE3.Frame

set_option autoImplicit false
noncomputable section
open Classical Topology Matrix
open WilkiesDesign.E
open Work.WilE3 (jacDet)

variable {k r j : ℕ}

/-! ## §1. The two predicates -/

/-- `Ψ` *straightens* `{h = 0}` at the real point `x`: it is the complex-analytic local inverse of
the coordinate map `PhiC = (ιᶜ-coordinates, h)` at `toC x`.  This is the conclusion of
`Work.WilE3.Frame.exists_param`. -/
def IsStraightening (c : EAChain k r) (h : Fin j → EAPoly k r) (ι : Fin j → Fin k)
    (x : Fin k → ℝ) (Ψ : ((U k ι → ℂ) × (Fin j → ℂ)) → (Fin k → ℂ)) : Prop :=
  Ψ (uCoord k ι (toC x), 0) = toC x ∧
    AnalyticAt ℂ Ψ (uCoord k ι (toC x), 0) ∧
    (∀ᶠ w in 𝓝 (uCoord k ι (toC x), 0), PhiC c h ι (Ψ w) = w) ∧
    (∀ᶠ z in 𝓝 (toC x), Ψ (PhiC c h ι z) = z)

/-- The cut forms `μ` annihilate the direction `w` and their common kernel is at most
one-dimensional.  This is the conclusion of `Work.WilE3.Frame.exists_cut_forms`. -/
def CutForms (ι : Fin j → Fin k) (w : U k ι → ℝ)
    (μ : Fin (k - j - 1) → (U k ι → ℝ)) : Prop :=
  (∀ a, ∑ i, μ a i * w i = 0) ∧
    (∀ v v' : U k ι → ℝ, (∀ a, ∑ i, μ a i * v i = 0) →
      (∀ a, ∑ i, μ a i * v' i = 0) → ∃ c c' : ℝ, (c, c') ≠ 0 ∧ c • v = c' • v')

/-! ## §2. The cut system -/

/-- The row of the cut system carrying the `a`-th equation `h a`. -/
def rowH (hjk : j < k) (a : Fin j) : Fin k := ⟨a.val, lt_trans a.isLt hjk⟩

/-- The row of the cut system carrying the `a`-th cut form. -/
def rowL (hjk : j < k) (a : Fin (k - j - 1)) : Fin k := ⟨j + a.val, by omega⟩

/-- The row of the cut system carrying the equation `f`. -/
def rowF (hjk : j < k) : Fin k := ⟨k - 1, by omega⟩

/-- The cut system `(h, L, f)`: rows `rowH` carry `h`, rows `rowL` carry the cut forms `L`, and
`rowF` carries `f`. -/
def cutSys (h : Fin j → EAPoly k r) (L : Fin (k - j - 1) → EAPoly k r) (f : EAPoly k r)
    (i : Fin k) : EAPoly k r :=
  if hi : i.val < j then h ⟨i.val, hi⟩
  else if _ : i.val < k - 1 then L ⟨i.val - j, by omega⟩
  else f

/-- The perturbation used to realise the right hand side `f = ε`: `-1` in the `rowF` slot and `0`
elsewhere, so that the perturbed system is `(h, L, f - ε)`. -/
def pertSys (hjk : j < k) : Fin k → EAPoly k r :=
  Function.update (fun _ : Fin k => (0 : EAPoly k r)) (rowF hjk) (MvPolynomial.C (-1))

/-! ## §3. Row lemmas -/

theorem cutSys_rowH (hjk : j < k) (h : Fin j → EAPoly k r) (L : Fin (k - j - 1) → EAPoly k r)
    (f : EAPoly k r) (a : Fin j) : cutSys h L f (rowH hjk a) = h a := by
  rw [cutSys, dif_pos (show (rowH hjk a).val < j from a.isLt)]
  exact congrArg h (Fin.ext rfl)

theorem cutSys_rowL (hjk : j < k) (h : Fin j → EAPoly k r) (L : Fin (k - j - 1) → EAPoly k r)
    (f : EAPoly k r) (a : Fin (k - j - 1)) : cutSys h L f (rowL hjk a) = L a := by
  rw [cutSys]
  rw [dif_neg (by simp only [rowL]; omega)]
  rw [dif_pos (by simp only [rowL]; omega)]
  exact congrArg L (Fin.ext (by simp only [rowL]; omega))

theorem cutSys_rowF (hjk : j < k) (h : Fin j → EAPoly k r) (L : Fin (k - j - 1) → EAPoly k r)
    (f : EAPoly k r) : cutSys h L f (rowF hjk) = f := by
  rw [cutSys, dif_neg (by simp only [rowF]; omega), dif_neg (by simp only [rowF]; omega)]

/-- Every index of `Fin k` is one of the three rows. -/
theorem cutSys_cases (hjk : j < k) (i : Fin k) :
    (∃ a : Fin j, i = rowH hjk a) ∨ (∃ a : Fin (k - j - 1), i = rowL hjk a) ∨ i = rowF hjk := by
  by_cases hi : i.val < j
  · exact Or.inl ⟨⟨i.val, hi⟩, Fin.ext rfl⟩
  · by_cases hi2 : i.val < k - 1
    · refine Or.inr (Or.inl ⟨⟨i.val - j, by omega⟩, Fin.ext ?_⟩)
      simp only [rowL]
      omega
    · exact Or.inr (Or.inr (Fin.ext (by simp only [rowF]; omega)))

theorem pertSys_rowF (hjk : j < k) : pertSys (r := r) hjk (rowF hjk) = MvPolynomial.C (-1) :=
  Function.update_self _ _ _

theorem pertSys_of_ne (hjk : j < k) {i : Fin k} (hi : i ≠ rowF hjk) :
    pertSys (r := r) hjk i = 0 :=
  Function.update_of_ne hi _ _

/-- Evaluation of the perturbation. -/
theorem eaEvalC_pertSys (c : EAChain k r) (hjk : j < k) (z : Fin k → ℂ) :
    eaEvalC c (pertSys (r := r) hjk (rowF hjk)) z = -1 := by
  rw [pertSys_rowF, Work.WilE3.API.eaEvalC_eq]
  simp

end

end Work.WilE3.Frame
