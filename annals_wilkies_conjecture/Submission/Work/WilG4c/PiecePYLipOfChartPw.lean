import Mathlib
import Submission.Work.WilG4c.PiecePYLipOfChart
import Submission.Work.WilG4c.SliceLipAlongPhi
import Submission.Work.WilG4c.SliceLipAlongPhiPw
import Submission.Work.WilG4c.SliceLipInY
import Submission.Work.WilG4c.PullXLipAt
import Submission.Work.WilG4c.PullXLipAtPw
import Submission.Work.WilG4c.Hyps

/-!
  WilG4c / PiecePYLipOfChartPw — the *pointwise* version of
  `Work.WilG4c.PiecePYLipOfChart`.

  `PiecePYLipOfChart` requires the chart `φ l`, the near-maximising curve `γ i l` and the
  composed curve `s ↦ F i l (cons s (γ i l s))` to be `C¹` *on the whole interval* `I`
  (`ContDiffOn ℝ 1 · I`).  Here this is weakened to differentiability at the individual
  points of the image of `φ`.

  Only two ingredients of the proof of `PiecePYLipOfChart` consumed `C¹`-on-`I`:

  * `Work.WilG4c.PullXLipAtPw` — the pointwise `x`-derivative bound; `C¹` was used there only
    through `DifferentiableAt`-at-a-point of `γ i l` and of the composed curve;
  * `Work.WilG4c.SliceLipAlongPhiPw` — the mean value theorem along `φ`; `C¹` of `φ` was used
    there only to obtain `HasDerivAt (φ l) (deriv (φ l) t) t` at each `t ∈ I`.

  Everything else (`SliceLipInY`, the `PY` transfer, the constant bookkeeping) is unchanged.
-/

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c

theorem PiecePYLipOfChartPw {p n k r : ℕ} (Λ : Set (Fin p → ℝ))
    (F : Work.WilkG4c.Family k p (n + 1))
    (γ : Fin k → (Fin p → ℝ) → ℝ → (Fin n → ℝ)) (φ : (Fin p → ℝ) → ℝ → ℝ) (C : ℝ)
    (hC : max (2 * ((n : ℝ) + 1)) 1 * ((n : ℝ) + 1) ≤ C)
    (hφI : ∀ l ∈ Λ, ∀ t ∈ Work.WilkG4c.I, φ l t ∈ Work.WilkG4c.I)
    (hφd : ∀ l ∈ Λ, ∀ t ∈ Work.WilkG4c.I, DifferentiableAt ℝ (φ l) t)
    (hφb : ∀ l ∈ Λ, ∀ t ∈ Work.WilkG4c.I, |deriv (φ l) t| ≤ 1)
    (hY : ∀ i, ∀ l ∈ Λ, ∀ t ∈ Work.WilkG4c.I, ∀ m, m ≤ r → ∀ y ∈ WilkiesDesign.openCube n,
      ‖iteratedFDeriv ℝ m (Work.WilkG4c.slice (F i l) (φ l t)) y‖ ≤ 1)
    (hC1 : ∀ i, ∀ l ∈ Λ, ∀ t ∈ Work.WilkG4c.I, ∀ y ∈ WilkiesDesign.openCube n,
      ContDiffAt ℝ 1 (Work.WilkG4c.famFunHat (F i)) (Work.WilkG4c.xPt l (φ l t) y))
    (hyb : ∀ i, ∀ l ∈ Λ, ∀ t ∈ Work.WilkG4c.I, ∀ y ∈ WilkiesDesign.openCube n, ∀ j : Fin n,
      |fderiv ℝ (Work.WilkG4c.famFunHat (F i)) (Work.WilkG4c.xPt l (φ l t) y)
        (Pi.single (Fin.natAdd p j.succ) 1)| ≤ 1)
    (hmax : ∀ i, ∀ l ∈ Λ, ∀ t ∈ Work.WilkG4c.I, ∀ y ∈ WilkiesDesign.openCube n,
      |Work.WilkG4c.xDeriv (F i) l (φ l t) y| ≤
        2 * |Work.WilkG4c.xDeriv (F i) l (φ l t) (γ i l (φ l t))|)
    (hγc : ∀ i, ∀ l ∈ Λ, ∀ t ∈ Work.WilkG4c.I, γ i l (φ l t) ∈ WilkiesDesign.openCube n)
    (hγd : ∀ i, ∀ j : Fin n, ∀ l ∈ Λ, ∀ t ∈ Work.WilkG4c.I,
      DifferentiableAt ℝ (fun s : ℝ => γ i l s j) (φ l t))
    (hγb : ∀ i, ∀ l ∈ Λ, ∀ t ∈ Work.WilkG4c.I, ∀ j : Fin n,
      |deriv (fun s : ℝ => γ i l s j) (φ l t)| * |deriv (φ l) t| ≤ 1)
    (hcd : ∀ i, ∀ l ∈ Λ, ∀ t ∈ Work.WilkG4c.I,
      DifferentiableAt ℝ (fun s : ℝ => F i l (Fin.cons s (γ i l s))) (φ l t))
    (hcb : ∀ i, ∀ l ∈ Λ, ∀ t ∈ Work.WilkG4c.I,
      |deriv (fun s : ℝ => F i l (Fin.cons s (γ i l s))) (φ l t)| * |deriv (φ l) t| ≤ 1) :
    (∀ i, ∀ l ∈ Λ, ∀ t ∈ Work.WilkG4c.I, ∀ m, m ≤ r → ∀ y ∈ WilkiesDesign.openCube n,
        ‖iteratedFDeriv ℝ m (Work.WilkG4c.slice (Work.WilkG4c.pieceFam F φ i l) t) y‖ ≤ 1) ∧
      (∀ i, ∀ l ∈ Λ, ∀ z ∈ WilkiesDesign.openCube (n + 1),
        ∀ z' ∈ WilkiesDesign.openCube (n + 1),
        |Work.WilkG4c.pieceFam F φ i l z - Work.WilkG4c.pieceFam F φ i l z'|
          ≤ C * dist z z') := by
  constructor
  · -- The `PY` bounds transfer: the `t`-slices of the piece are the `φ l t`-slices of `F`.
    intro i l hl t ht m hm y hy
    rw [Work.WilkG4c.slice_pieceFam F φ i l t]
    exact hY i l hl t ht m hm y hy
  · -- The Lipschitz bound: the `y`-step at `x = φ l (z 0)`, then the `x`-step along `φ`.
    intro i l hl z hz z' hz'
    have hz0 : z 0 ∈ Work.WilkG4c.I := hz 0
    have hz0' : z' 0 ∈ Work.WilkG4c.I := hz' 0
    have htz : Fin.tail z ∈ WilkiesDesign.openCube n := fun j => hz j.succ
    have htz' : Fin.tail z' ∈ WilkiesDesign.openCube n := fun j => hz' j.succ
    have h1 : |F i l (Work.WilkG4c.pt (φ l (z 0)) (Fin.tail z))
        - F i l (Work.WilkG4c.pt (φ l (z 0)) (Fin.tail z'))|
        ≤ (n : ℝ) * dist (Fin.tail z) (Fin.tail z') :=
      Work.WilG4c.SliceLipInY (F i) l (φ l (z 0))
        (fun y hy => hC1 i l hl (z 0) hz0 y hy)
        (fun y hy j => hyb i l hl (z 0) hz0 y hy j)
        (Fin.tail z) htz (Fin.tail z') htz'
    -- The pointwise `x`-derivative bound at the image points, scaled by `|φ'(t)|`.
    have hx : ∀ t ∈ Work.WilkG4c.I, ∀ y ∈ WilkiesDesign.openCube n,
        |Work.WilkG4c.xDeriv (F i) l (φ l t) y| * |deriv (φ l) t| ≤ 2 * ((n : ℝ) + 1) := by
      intro t ht y hy
      by_cases hd0 : deriv (φ l) t = 0
      · -- Here `∂ₓ F · φ'` vanishes identically, so no bound on `∂ₓ F` is needed.
        have hzd : |deriv (φ l) t| = 0 := by rw [hd0, abs_zero]
        rw [hzd, mul_zero]
        positivity
      · have hpos : 0 < |deriv (φ l) t| := abs_pos.mpr hd0
        have h := Work.WilG4c.PullXLipAtPw (F i) (γ i) l (φ l t) |deriv (φ l) t| hpos.le
          (hγc i l hl t ht)
          (fun y hy => hC1 i l hl t ht y hy)
          (fun y hy j => hyb i l hl t ht y hy j)
          (fun y hy => hmax i l hl t ht y hy)
          (fun j => hγd i j l hl t ht)
          (fun j => hγb i l hl t ht j)
          (hcb i l hl t ht)
          (hcd i l hl t ht)
          y hy
        simpa using h
    have h2 := Work.WilG4c.SliceLipAlongPhiPw (F i) φ l
        (fun t ht => hφd l hl t ht)
        (fun t ht y hy => hC1 i l hl t ht y hy) hx (z 0) hz0 (z' 0) hz0' (Fin.tail z') htz'
    have htail : dist (Fin.tail z) (Fin.tail z') ≤ dist z z' := by
      rw [dist_pi_le_iff dist_nonneg]
      intro j
      exact dist_le_pi_dist z z' j.succ
    have h0 : |z 0 - z' 0| ≤ dist z z' := by
      have h := dist_le_pi_dist z z' (0 : Fin (n + 1))
      rwa [Real.dist_eq] at h
    have hC' : (n : ℝ) + 2 * ((n : ℝ) + 1) ≤ C := by
      have h1' : 2 * ((n : ℝ) + 1) * ((n : ℝ) + 1) ≤ C :=
        le_trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) hC
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      nlinarith [sq_nonneg ((n : ℝ) + 1)]
    calc |Work.WilkG4c.pieceFam F φ i l z - Work.WilkG4c.pieceFam F φ i l z'|
        = |F i l (Work.WilkG4c.pt (φ l (z 0)) (Fin.tail z))
            - F i l (Work.WilkG4c.pt (φ l (z' 0)) (Fin.tail z'))| := rfl
      _ ≤ |F i l (Work.WilkG4c.pt (φ l (z 0)) (Fin.tail z))
              - F i l (Work.WilkG4c.pt (φ l (z 0)) (Fin.tail z'))|
            + |F i l (Work.WilkG4c.pt (φ l (z 0)) (Fin.tail z'))
              - F i l (Work.WilkG4c.pt (φ l (z' 0)) (Fin.tail z'))| := abs_sub_le _ _ _
      _ ≤ (n : ℝ) * dist (Fin.tail z) (Fin.tail z') + (2 * ((n : ℝ) + 1)) * |z 0 - z' 0| :=
            add_le_add h1 h2
      _ ≤ ((n : ℝ) + 2 * ((n : ℝ) + 1)) * dist z z' := by
          have hh1 : (n : ℝ) * dist (Fin.tail z) (Fin.tail z') ≤ (n : ℝ) * dist z z' :=
            mul_le_mul_of_nonneg_left htail (Nat.cast_nonneg n)
          have hh2 : 2 * ((n : ℝ) + 1) * |z 0 - z' 0| ≤ 2 * ((n : ℝ) + 1) * dist z z' :=
            mul_le_mul_of_nonneg_left h0 (by positivity)
          nlinarith [dist_nonneg (x := z) (y := z')]
      _ ≤ C * dist z z' := mul_le_mul_of_nonneg_right hC' dist_nonneg

end Work.WilG4c
