import Mathlib
import Submission.Work.WilG4c.LipDefs
import Submission.Work.WilG4c.PullXLip
import Submission.Work.WilG4c.PullXLipOn

namespace Work.WilkG4c

open WilkiesDesign

/-!
  `SliceLipInX` — the one-dimensional mean value estimate in the distinguished `x`-direction.

  A bound `|∂₀ f (l, x, y)| · β ≤ 2 (n+1)` on the `x`-derivative of a family member, valid for
  all `x` in an interval `(u, v)` and all `y` in the cube, integrates to a Lipschitz bound for
  the `x`-slice `x ↦ f l (pt x y)` with constant `2 (n+1) / β`.

  The two ingredients are
  * `xPt_affine`: the curve `s ↦ xPt l s y` of `ℝ^{p+(n+1)}` is affine, with direction the
    `x`-basis vector `Pi.single (xDirHat p n) 1`;
  * `hasDerivAt_xPt`: that curve is differentiable with that direction as derivative, so the
    chain rule identifies `deriv (fun s => f l (pt s y)) x` with `xDeriv f l x y`.

  The result then follows from the mean value inequality `Convex.norm_image_sub_le_of_norm_deriv_le`
  on the convex interval `Set.Ioo u v`.
-/

/-- The curve `s ↦ xPt l s y` is affine: it is the constant point `xPt l 0 y` plus `s` times
the `x`-basis direction `Pi.single (xDirHat p n) 1` of `ℝ^{p+(n+1)}`. -/
theorem xPt_affine {p n : ℕ} (l : Fin p → ℝ) (s : ℝ) (y : Fin n → ℝ) :
    xPt l s y = xPt l 0 y + s • (Pi.single (xDirHat p n) (1:ℝ)) := by
  funext i
  induction i using Fin.addCases with
  | left a =>
    have hne : Fin.castAdd (n + 1) a ≠ xDirHat p n := by
      intro h; have hv := congrArg Fin.val h
      simp only [xDirHat, Fin.val_natAdd, Fin.val_castAdd] at hv; omega
    rw [xPt, Fin.append_left, Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne hne,
      smul_zero, add_zero, xPt, Fin.append_left]
  | right b =>
    rw [xPt, Fin.append_right, Pi.add_apply, Pi.smul_apply, xPt, Fin.append_right]
    have hxd : xDirHat p n = Fin.natAdd p 0 := rfl
    rw [hxd]
    induction b using Fin.cases with
    | zero => rw [Fin.cons_zero, Fin.cons_zero, Pi.single_eq_same, smul_eq_mul, mul_one, zero_add]
    | succ k =>
      have hne : Fin.natAdd p k.succ ≠ Fin.natAdd p 0 := by
        intro h; have hv := (Fin.natAdd_inj p).mp h; exact absurd hv (by simp)
      rw [Fin.cons_succ, Fin.cons_succ, Pi.single_eq_of_ne hne, smul_zero, add_zero]

/-- The `x`-curve of `ℝ^{p+(n+1)}` has derivative the `x`-basis direction. -/
theorem hasDerivAt_xPt {p n : ℕ} (l : Fin p → ℝ) (x : ℝ) (y : Fin n → ℝ) :
    HasDerivAt (fun s : ℝ => xPt l s y) (Pi.single (xDirHat p n) (1:ℝ)) x := by
  have h := ((hasDerivAt_id (𝕜 := ℝ) x).smul_const (Pi.single (xDirHat p n) (1:ℝ))).const_add
    (xPt l 0 y)
  rw [one_smul] at h
  simp only [id_eq] at h
  have hfun : (fun s : ℝ => xPt l 0 y + s • Pi.single (xDirHat p n) 1) = fun s => xPt l s y := by
    funext s; exact (xPt_affine l s y).symm
  rwa [hfun] at h

/-- The `x`-slice `x ↦ f l (pt x y)` has derivative `xDeriv f l x y`. -/
theorem hasDerivAt_sliceX {p n : ℕ} (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (l : Fin p → ℝ) (x : ℝ) (y : Fin n → ℝ)
    (hC1 : ContDiffAt ℝ 1 (famFunHat f) (xPt l x y)) :
    HasDerivAt (fun s : ℝ => f l (pt s y)) (xDeriv f l x y) x := by
  have hfd : HasFDerivAt (famFunHat f) (fderiv ℝ (famFunHat f) (xPt l x y)) (xPt l x y) :=
    hC1.differentiableAt_one.hasFDerivAt
  have hcomp := hfd.comp_hasDerivAt x (hasDerivAt_xPt l x y)
  have hfun : (fun s : ℝ => f l (pt s y)) = famFunHat f ∘ (fun s : ℝ => xPt l s y) := by
    funext s; rw [Function.comp_apply, famFunHat_xPt]; rfl
  rwa [hfun]

theorem SliceLipInX {p n : ℕ} (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (l : Fin p → ℝ) (u v : ℝ) (βl : ℝ) (hβ : 0 < βl)
    (hC1 : ∀ x ∈ Set.Ioo u v, ∀ y ∈ WilkiesDesign.openCube n,
      ContDiffAt ℝ 1 (Work.WilkG4c.famFunHat f) (Work.WilkG4c.xPt l x y))
    (hx : ∀ x ∈ Set.Ioo u v, ∀ y ∈ WilkiesDesign.openCube n,
      |Work.WilkG4c.xDeriv f l x y| * βl ≤ 2 * ((n : ℝ) + 1)) :
    ∀ a ∈ Set.Ioo u v, ∀ b ∈ Set.Ioo u v, ∀ y ∈ WilkiesDesign.openCube n,
      |f l (Work.WilkG4c.pt a y) - f l (Work.WilkG4c.pt b y)| ≤ (2 * ((n : ℝ) + 1) / βl) * |a - b| := by
  intro a ha b hb y hy
  have hHd : ∀ x ∈ Set.Ioo u v,
      HasDerivAt (fun s : ℝ => f l (pt s y)) (xDeriv f l x y) x :=
    fun x hxc => hasDerivAt_sliceX f l x y (hC1 x hxc y hy)
  have hbound : ∀ x ∈ Set.Ioo u v,
      ‖deriv (fun s : ℝ => f l (pt s y)) x‖ ≤ 2 * ((n : ℝ) + 1) / βl := by
    intro x hxc
    rw [Real.norm_eq_abs, (hHd x hxc).deriv, le_div_iff₀ hβ]
    exact hx x hxc y hy
  have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun x hxc => (hHd x hxc).differentiableAt) hbound (convex_Ioo u v) ha hb
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmvt
  rw [abs_sub_comm (f l (pt b y)) (f l (pt a y)), abs_sub_comm b a] at hmvt
  exact hmvt

end Work.WilkG4c

namespace Work.WilG4c

/-- The lemma `Work.WilkG4c.SliceLipInX` re-exported under the namespace spelling of the module
path `Submission.Work.WilG4c.SliceLipInX`, so that it can be referred to as
`Work.WilG4c.SliceLipInX` (as the harness expects) as well as `Work.WilkG4c.SliceLipInX`
(which is the spelling used by the neighbouring files of this area). -/
abbrev SliceLipInX := @Work.WilkG4c.SliceLipInX

end Work.WilG4c
