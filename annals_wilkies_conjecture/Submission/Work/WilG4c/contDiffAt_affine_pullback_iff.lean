/-
  WilG4c — `ContDiffAt` invariance under the affine `x`-change of variables of BNZ §5.4.

  The chart of BNZ §5.4 is

      `Φ(v) = (α + β * v 0, Fin.tail v)  :  R^{n+1} → R^{n+1}`   (`β ≠ 0`);

  it is an affine bijection of `R^{n+1}` (a diagonal scaling of the first coordinate followed by
  a translation).  The lemma proved here is the elementary regularity statement used when pulling
  the family `F` back along `Φ`: a function is `C^m` at `u` after being composed with `Φ` exactly
  when it is `C^m` at the image point `Φ u`.

  The proof writes `Φ` as the composite of the smooth affine chart `affPhi` with its explicit
  inverse `affPsi`, which is smooth because `β ≠ 0`; the two directions are then the two halves of
  `ContDiffAt.comp`, using `affPsi (affPhi u) = u` and `affPhi (affPsi w) = w`.

  The declaration lives in `Work.WilG4c` (matching this file's module path), while the point
  `pt` it is phrased with lives in `Work.WilkG4c` (the namespace of
  `Submission.Work.WilG4c.Defs`); an alias with the same statement is also provided in the
  latter namespace, since `Work.WilkG4c`-spelled files (`StepEngAux2`, `StepHigherMain`, …)
  refer to it.
-/
import Mathlib
import Submission.Work.WilG4c.Defs
import Submission.Work.WilG4c.Pullback

namespace Work.WilG4c

open Work.WilkG4c

noncomputable section

/- The affine chart `v ↦ (α + β * v 0, Fin.tail v)` of `R^{n+1}`. -/
private def affPhi {n : ℕ} (α β : ℝ) (v : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  pt (α + β * v 0) (Fin.tail v)

/- The explicit inverse of `affPhi` when `β ≠ 0`. -/
private def affPsi {n : ℕ} (α β : ℝ) (w : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  pt ((w 0 - α) / β) (Fin.tail w)

/- `affPsi` is a left inverse of `affPhi`. -/
private lemma affPsi_affPhi {n : ℕ} (α β : ℝ) (hβ : β ≠ 0) (v : Fin (n + 1) → ℝ) :
    affPsi α β (affPhi α β v) = v := by
  unfold affPhi affPsi
  rw [pt_zero, tail_pt]
  have h : ((α + β * v 0) - α) / β = v 0 := by
    rw [add_sub_cancel_left, mul_div_cancel_left₀ _ hβ]
  rw [h, pt_eta]

/- `affPsi` is a right inverse of `affPhi`. -/
private lemma affPhi_affPsi {n : ℕ} (α β : ℝ) (hβ : β ≠ 0) (w : Fin (n + 1) → ℝ) :
    affPhi α β (affPsi α β w) = w := by
  unfold affPhi affPsi
  rw [pt_zero, tail_pt]
  have h : α + β * ((w 0 - α) / β) = w 0 := by
    rw [mul_div_cancel₀ _ hβ]
    ring
  rw [h, pt_eta]

/- The affine chart is smooth (indeed of every order) everywhere. -/
private lemma contDiffAt_affPhi {n m : ℕ} (α β : ℝ) (u : Fin (n + 1) → ℝ) :
    ContDiffAt ℝ m (affPhi α β) u := by
  rw [contDiffAt_pi]
  intro i
  induction i using Fin.cases with
  | zero => simp only [affPhi, pt_zero]; fun_prop
  | succ j => simp only [affPhi, pt_succ, Fin.tail]; fun_prop

/- The explicit inverse of the chart is likewise smooth everywhere. -/
private lemma contDiffAt_affPsi {n m : ℕ} (α β : ℝ) (u : Fin (n + 1) → ℝ) :
    ContDiffAt ℝ m (affPsi α β) u := by
  rw [contDiffAt_pi]
  intro i
  induction i using Fin.cases with
  | zero => simp only [affPsi, pt_zero]; fun_prop
  | succ j => simp only [affPsi, pt_succ, Fin.tail]; fun_prop

theorem contDiffAt_affine_pullback_iff {n m : ℕ} (f : (Fin (n + 1) → ℝ) → ℝ) (α β : ℝ)
    (hβ : β ≠ 0) (u : Fin (n + 1) → ℝ) :
    ContDiffAt ℝ m
        (fun v : Fin (n + 1) → ℝ => f (Work.WilkG4c.pt (α + β * v 0) (Fin.tail v))) u ↔
      ContDiffAt ℝ m f (Work.WilkG4c.pt (α + β * u 0) (Fin.tail u)) := by
  have hΦ : ContDiffAt ℝ m (affPhi α β) u := contDiffAt_affPhi α β u
  have hΨ : ContDiffAt ℝ m (affPsi α β) (affPhi α β u) := contDiffAt_affPsi α β (affPhi α β u)
  constructor
  · -- `⟹`: `f = (f ∘ affPhi) ∘ affPsi` globally, and `affPsi` is smooth at `affPhi u`.
    intro h
    have hg : ContDiffAt ℝ m (f ∘ affPhi α β) (affPsi α β (affPhi α β u)) := by
      rw [affPsi_affPhi α β hβ u]
      simpa only [affPhi, Function.comp_def] using h
    have hcomp := ContDiffAt.comp (affPhi α β u) hg hΨ
    have heq : (f ∘ affPhi α β) ∘ affPsi α β = f := by
      funext w
      simp only [Function.comp_apply]
      rw [affPhi_affPsi α β hβ w]
    rw [heq] at hcomp
    simpa only [affPhi] using hcomp
  · -- `⟸`: compose with the smooth chart `affPhi`.
    intro h
    have h' : ContDiffAt ℝ m f (affPhi α β u) := by simpa only [affPhi] using h
    have hcomp := ContDiffAt.comp u h' hΦ
    simpa only [affPhi, Function.comp_def] using hcomp

end

end Work.WilG4c

namespace Work.WilkG4c

/- Same statement as `Work.WilG4c.contDiffAt_affine_pullback_iff`, in the namespace of
`Submission.Work.WilG4c.Defs`'s `pt`. -/
theorem contDiffAt_affine_pullback_iff {n m : ℕ} (f : (Fin (n + 1) → ℝ) → ℝ) (α β : ℝ)
    (hβ : β ≠ 0) (u : Fin (n + 1) → ℝ) :
    ContDiffAt ℝ m
        (fun v : Fin (n + 1) → ℝ => f (Work.WilkG4c.pt (α + β * v 0) (Fin.tail v))) u ↔
      ContDiffAt ℝ m f (Work.WilkG4c.pt (α + β * u 0) (Fin.tail u)) :=
  Work.WilG4c.contDiffAt_affine_pullback_iff f α β hβ u

end Work.WilkG4c
