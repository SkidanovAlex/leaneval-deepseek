import Mathlib
import Submission.Work.WilG4c.Defs
import Submission.Work.WilG4c.Pullback
import Submission.Work.WilG4c.CdpSliceContDiffAt
import Submission.Work.WilG4c.NormIteratedFDerivCompLinearGeneral

/-!
# The degree-`≤ 1` jet bound for the `β = 0` pullback

`DegJetLeOne` is the elementary half of the §5.4 reduction of `PYLip` to `PYLipDef`: pulling
`F` back along the affine chart `x = α` (i.e. `β = 0`) keeps the mixed `y`-derivatives of the
slice at `x = α` bounded by `1`, uniformly over the cube and over all evaluation directions
`t ↦ Pi.single (v t) 1`.

The proof is that `pullX F (fun _ => α) (fun _ => 0) i l = slice (F i l) α ∘ Fin.tail`: the
`m`-th derivative of the pullback at `pt x y` is the `m`-th derivative of the slice at `y`
composed with `Fin.tail` in every variable (`NormIteratedFDerivCompLinearGeneral`, whose
hypothesis is supplied by `CdpSliceContDiffAt` applied to the given smoothness of the
pullback), `‖Fin.tail‖ ≤ 1`, and `YBound` bounds the slice-derivative by `1`.  Evaluating a
continuous multilinear map at directions of norm `≤ 1` cannot increase the norm.
-/

set_option autoImplicit false
open Classical

namespace Work.WilG4c

open WilkiesDesign

noncomputable section

/-! ### `Fin.tail` as a continuous linear map with operator norm `≤ 1` -/

/-- `Fin.tail` (forget the first coordinate of a tuple) as a continuous linear map. -/
private def tailL (n : ℕ) : (Fin (n + 1) → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi fun i : Fin n =>
    (ContinuousLinearMap.proj i.succ : (Fin (n + 1) → ℝ) →L[ℝ] ℝ)

private theorem tailL_apply (n : ℕ) (x : Fin (n + 1) → ℝ) : tailL n x = Fin.tail x := by
  funext i
  simp [tailL, Fin.tail]

/-- The operator norm of `Fin.tail` is at most `1`. -/
private theorem norm_tailL_le (n : ℕ) : ‖tailL n‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => ?_)
  rw [one_mul, pi_norm_le_iff_of_nonneg (norm_nonneg x)]
  intro i
  rw [tailL_apply]
  exact norm_le_pi_norm x i.succ

theorem DegJetLeOne {k p n r : ℕ} {F : Work.WilkG4c.Family k p (n + 1)}
    (hY : Work.WilkG4c.YBound F r) (i : Fin k) (l : Fin p → ℝ) (α : ℝ)
    (hα : α ∈ Work.WilkG4c.I) (m : ℕ) (hm : m ≤ r) (v : Fin m → Fin (n + 1))
    (x : ℝ) (y : Fin n → ℝ) (hy : y ∈ WilkiesDesign.openCube n)
    (hcd : ContDiffAt ℝ m (Work.WilkG4c.pullX F (fun _ => α) (fun _ => (0 : ℝ)) i l)
      (Work.WilkG4c.pt x y)) :
    |iteratedFDeriv ℝ m (Work.WilkG4c.pullX F (fun _ => α) (fun _ => (0 : ℝ)) i l)
      (Work.WilkG4c.pt x y) (fun t => Pi.single (v t) 1)| ≤ 1 := by
  let w : Fin m → (Fin (n + 1) → ℝ) := fun t => Pi.single (v t) 1
  have hw_def : ∀ t, w t = Pi.single (v t) (1 : ℝ) := fun t => rfl
  -- The `β = 0` pullback is the `x = α` slice composed with `Fin.tail`.
  have hpull : Work.WilkG4c.pullX F (fun _ => α) (fun _ => (0 : ℝ)) i l
      = fun t : Fin (n + 1) → ℝ => Work.WilkG4c.slice (F i l) α (Fin.tail t) := by
    funext t
    simp [Work.WilkG4c.pullX, Work.WilkG4c.slice, Work.WilkG4c.pt]
  -- Slicing the pullback at `x` recovers the slice of `F` at `α`.
  have hslice_eq :
      Work.WilkG4c.slice (Work.WilkG4c.pullX F (fun _ => α) (fun _ => (0 : ℝ)) i l) x
        = Work.WilkG4c.slice (F i l) α := by
    funext z
    simp [Work.WilkG4c.pullX, Work.WilkG4c.slice, Work.WilkG4c.pt]
  -- hence the slice at `α` is `C^m` at `y`, by assumption on the pullback.
  have hslice : ContDiffAt ℝ m (Work.WilkG4c.slice (F i l) α) y := by
    rw [← hslice_eq]
    exact Work.WilG4c.CdpSliceContDiffAt (x := x) (y := y) hcd
  -- operator-norm bound on the whole `m`-th derivative of the pullback
  have hkey : ‖iteratedFDeriv ℝ m (Work.WilkG4c.pullX F (fun _ => α) (fun _ => (0 : ℝ)) i l)
        (Work.WilkG4c.pt x y)‖ ≤ 1 := by
    have hfun : Work.WilkG4c.pullX F (fun _ => α) (fun _ => (0 : ℝ)) i l
        = fun t : Fin (n + 1) → ℝ => Work.WilkG4c.slice (F i l) α (tailL n t) := by
      rw [hpull]
      funext t
      rw [tailL_apply]
    rw [hfun]
    have hcomp := Work.WilG4c.NormIteratedFDerivCompLinearGeneral (tailL n)
      (Work.WilkG4c.slice (F i l) α) (Work.WilkG4c.pt x y) m hslice
    calc ‖iteratedFDeriv ℝ m (fun t : Fin (n + 1) → ℝ =>
            Work.WilkG4c.slice (F i l) α (tailL n t)) (Work.WilkG4c.pt x y)‖
        ≤ ‖iteratedFDeriv ℝ m (Work.WilkG4c.slice (F i l) α)
            (tailL n (Work.WilkG4c.pt x y))‖ * ‖tailL n‖ ^ m := hcomp
      _ ≤ 1 * 1 := by
            refine mul_le_mul ?_ (pow_le_one₀ (norm_nonneg _) (norm_tailL_le n))
              (by positivity) (by norm_num)
            rw [tailL_apply, Work.WilkG4c.tail_pt]
            exact hY i l α hα m hm y hy
      _ = 1 := one_mul 1
  -- each evaluation direction is a unit vector
  have hprod : ∏ t : Fin m, ‖w t‖ = 1 := by
    apply Finset.prod_eq_one
    intro t _
    rw [hw_def t, Pi.norm_single]
    norm_num
  show |(iteratedFDeriv ℝ m (Work.WilkG4c.pullX F (fun _ => α) (fun _ => (0 : ℝ)) i l)
        (Work.WilkG4c.pt x y)) w| ≤ 1
  rw [← Real.norm_eq_abs]
  calc ‖(iteratedFDeriv ℝ m (Work.WilkG4c.pullX F (fun _ => α) (fun _ => (0 : ℝ)) i l)
        (Work.WilkG4c.pt x y)) w‖
      ≤ ‖iteratedFDeriv ℝ m (Work.WilkG4c.pullX F (fun _ => α) (fun _ => (0 : ℝ)) i l)
          (Work.WilkG4c.pt x y)‖ * ∏ t : Fin m, ‖w t‖
        := ContinuousMultilinearMap.le_opNorm
            (iteratedFDeriv ℝ m (Work.WilkG4c.pullX F (fun _ => α) (fun _ => (0 : ℝ)) i l)
              (Work.WilkG4c.pt x y)) w
    _ = ‖iteratedFDeriv ℝ m (Work.WilkG4c.pullX F (fun _ => α) (fun _ => (0 : ℝ)) i l)
          (Work.WilkG4c.pt x y)‖ * 1 := by rw [hprod]
    _ ≤ 1 := by rw [mul_one]; exact hkey

end

end Work.WilG4c
