import Mathlib
import Submission.Work.WilG4c.StepLipDefs
import Submission.Work.WilG4c.PullXLip
import Submission.Work.WilG4c.contDiffAt_famFunHat_xPt
import Submission.Work.WilG4b.xDeriv_eq

set_option autoImplicit false

namespace Work.WilG4c

open Work.WilkG4c

/-! ## Auxiliary: the affine inclusion `y ↦ Fin.cons x y` and its derivative -/

/-- The continuous linear map `v ↦ Fin.cons 0 v : ℝⁿ → ℝⁿ⁺¹`.  It is the linear part of the
affine inclusion `y ↦ Fin.cons x y`. -/
private def incl (n : ℕ) : (Fin n → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) :=
  ContinuousLinearMap.pi
    (fun j : Fin (n + 1) => Fin.cases (0 : (Fin n → ℝ) →L[ℝ] ℝ)
      (fun i : Fin n => ContinuousLinearMap.proj i) j)

private lemma incl_apply (n : ℕ) (v : Fin n → ℝ) : incl n v = Fin.cons (0 : ℝ) v := by
  funext j
  induction j using Fin.cases with
  | zero => simp [incl]
  | succ i => simp [incl]

/-- The inclusion `ℝⁿ ↪ ℝⁿ⁺¹` carries the `i`-th coordinate direction to the `(i+1)`-st. -/
private lemma incl_single {n : ℕ} (i : Fin n) :
    incl n (Pi.single i (1 : ℝ)) = (Pi.single i.succ (1 : ℝ) : Fin (n + 1) → ℝ) := by
  rw [incl_apply]
  funext j
  induction j using Fin.cases with
  | zero => simp
  | succ k =>
    by_cases h : k = i
    · subst h; simp
    · simp only [Fin.cons_succ, Pi.single_eq_of_ne h,
        Pi.single_eq_of_ne (fun hh => h (Fin.succ_injective n hh))]

/-- A `y`-directional derivative of `g` is a directional derivative of its slice. -/
private theorem fcy_slice_eq {n : ℕ} (g : (Fin (n + 1) → ℝ) → ℝ)
    (x : ℝ) (y : Fin n → ℝ) (hd : DifferentiableAt ℝ g (Fin.cons x y)) (j : Fin n) :
    fderiv ℝ g (Fin.cons x y) (Pi.single j.succ (1 : ℝ))
      = fderiv ℝ (Work.WilkG4c.slice g x) y (Pi.single j (1 : ℝ)) := by
  have hinc : HasFDerivAt (fun w : Fin n → ℝ => Fin.cons x w) (incl n) y := by
    have hfun : (fun w : Fin n → ℝ => Fin.cons x w)
        = fun w => Fin.cons x (0 : Fin n → ℝ) + incl n w := by
      funext w
      rw [incl_apply]
      funext k
      induction k using Fin.cases with
      | zero => simp
      | succ i => simp
    rw [hfun]
    exact (incl n).hasFDerivAt.const_add _
  have hcomp : HasFDerivAt (fun w : Fin n → ℝ => g (Fin.cons x w))
      ((fderiv ℝ g (Fin.cons x y)).comp (incl n)) y :=
    (hd.hasFDerivAt).comp y hinc
  have hslice : (fun w : Fin n → ℝ => g (Fin.cons x w)) = Work.WilkG4c.slice g x := by
    funext w; simp [Work.WilkG4c.slice, Work.WilkG4c.pt]
  have hfderiv : fderiv ℝ (Work.WilkG4c.slice g x) y
      = (fderiv ℝ g (Fin.cons x y)).comp (incl n) := by
    rw [← hslice]; exact hcomp.fderiv
  rw [hfderiv, ContinuousLinearMap.comp_apply, incl_single]

/-- A `y`-directional derivative of `g` at `Fin.cons x y` is bounded by the slice jet norm. -/
private theorem fcy_aux {n : ℕ} (g : (Fin (n + 1) → ℝ) → ℝ)
    (x : ℝ) (y : Fin n → ℝ) (hd : DifferentiableAt ℝ g (Fin.cons x y))
    (hY : ‖iteratedFDeriv ℝ 1 (Work.WilkG4c.slice g x) y‖ ≤ 1) (j : Fin n) :
    |fderiv ℝ g (Fin.cons x y) (Pi.single j.succ (1 : ℝ))| ≤ 1 := by
  rw [fcy_slice_eq g x y hd j]
  calc |fderiv ℝ (Work.WilkG4c.slice g x) y (Pi.single j (1 : ℝ))|
      = ‖fderiv ℝ (Work.WilkG4c.slice g x) y (Pi.single j (1 : ℝ))‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ‖fderiv ℝ (Work.WilkG4c.slice g x) y‖ * ‖(Pi.single j (1 : ℝ) : Fin n → ℝ)‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ = ‖iteratedFDeriv ℝ 1 (Work.WilkG4c.slice g x) y‖ * 1 := by
        rw [← norm_iteratedFDeriv_one (f := Work.WilkG4c.slice g x), Pi.norm_single, norm_one]
    _ = ‖iteratedFDeriv ℝ 1 (Work.WilkG4c.slice g x) y‖ := mul_one _
    _ ≤ 1 := hY

/-! ## Auxiliary: the reparametrisation chain rule -/

/-- If `t ↦ g (a + b * t)` is `C¹` at `s` and `b ≠ 0`, then `g` is differentiable at
`a + b * s` and the two derivatives differ by the factor `b`. -/
private theorem dca_aux {g : ℝ → ℝ} {a b s : ℝ} (hb : b ≠ 0)
    (h : ContDiffAt ℝ 1 (fun t : ℝ => g (a + b * t)) s) :
    DifferentiableAt ℝ g (a + b * s) ∧
      deriv (fun t : ℝ => g (a + b * t)) s = b * deriv g (a + b * s) := by
  have hG : DifferentiableAt ℝ (fun t : ℝ => g (a + b * t)) s := h.differentiableAt_one
  have hds : (a + b * s - a) / b = s := by
    rw [show a + b * s - a = b * s by ring]
    exact mul_div_cancel_left₀ s hb
  have hd : HasDerivAt (fun x : ℝ => (x - a) / b) (1 / b) (a + b * s) :=
    ((hasDerivAt_id (a + b * s)).sub_const a).div_const b
  have hxa : ∀ x : ℝ, a + b * ((x - a) / b) = x := by
    intro x
    rw [show b * ((x - a) / b) = x - a by
      rw [← mul_div_assoc]
      exact mul_div_cancel_left₀ (x - a) hb]
    ring
  have hgd : g = (fun t : ℝ => g (a + b * t)) ∘ (fun x : ℝ => (x - a) / b) := by
    funext x
    simp only [Function.comp_apply]
    rw [hxa x]
  have hG' : DifferentiableAt ℝ (fun t : ℝ => g (a + b * t))
      ((fun x : ℝ => (x - a) / b) (a + b * s)) := by
    simpa only [hds] using hG
  have hg : DifferentiableAt ℝ g (a + b * s) := by
    rw [hgd]
    exact ((hG'.hasFDerivAt).comp (a + b * s) (hd.differentiableAt.hasFDerivAt)).differentiableAt
  refine ⟨hg, ?_⟩
  have hc : HasDerivAt (fun t : ℝ => a + b * t) b s := by
    have h' := ((hasDerivAt_id s).const_mul b).const_add a
    simpa using h'
  have hcomp' : HasDerivAt (g ∘ (fun t : ℝ => a + b * t)) (deriv g (a + b * s) * b) s :=
    (hg.hasDerivAt).comp s hc
  have hd2 : deriv (fun t : ℝ => g (a + b * t)) s = deriv g (a + b * s) * b := hcomp'.deriv
  rw [hd2]
  exact mul_comm _ _

/-! ## Auxiliary: the finite-sum bound -/

private theorem asml_aux {n : ℕ} (a c : Fin n → ℝ)
    (ha : ∀ j, |a j| ≤ 1) (hc : ∀ j, |c j| ≤ 1) :
    |∑ j, a j * c j| ≤ (n : ℝ) := by
  have hle : ∀ j : Fin n, |a j| * |c j| ≤ 1 := by
    intro j
    nlinarith [ha j, hc j, abs_nonneg (a j), abs_nonneg (c j)]
  calc |∑ j, a j * c j| ≤ ∑ j, |a j * c j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, |a j| * |c j| := by simp only [abs_mul]
    _ ≤ ∑ _j : Fin n, (1 : ℝ) := Finset.sum_le_sum (fun j _ => hle j)
    _ = (n : ℝ) := by simp

theorem curveDerivBound {p n k : ℕ} {F : Fin k → (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ}
    {γ : (Fin p → ℝ) → ℝ → (Fin n → ℝ)} {α β : (Fin p → ℝ) → ℝ} {l : Fin p → ℝ}
    {i : Fin k} {s : ℝ} (hβ : 0 < β l) (hs : s ∈ Work.WilkG4c.I)
    (hγc : γ l (α l + β l * s) ∈ WilkiesDesign.openCube n)
    (hC1 : Work.WilkG4c.xPt l (α l + β l * s) (γ l (α l + β l * s)) ∈
      interior {z | ContDiffAt ℝ 1 (Work.WilkG4c.famFunHat (F i)) z})
    (hY : ∀ y ∈ WilkiesDesign.openCube n,
      ‖iteratedFDeriv ℝ 1 (Work.WilkG4c.slice (F i l) (α l + β l * s)) y‖ ≤ 1)
    (hcomp : ContDiffAt ℝ 1 (fun t : ℝ =>
      F i l (Work.WilkG4c.pt (α l + β l * t) (γ l (α l + β l * t)))) s)
    (hcompid : ∀ j : Fin n, ContDiffAt ℝ 1 (fun t : ℝ => γ l (α l + β l * t) j) s)
    (hderF : |deriv (fun t : ℝ =>
      F i l (Work.WilkG4c.pt (α l + β l * t) (γ l (α l + β l * t)))) s| ≤ 1)
    (hderγ : ∀ j : Fin n,
      |deriv (fun t : ℝ => γ l (α l + β l * t) j) s| ≤ 1) :
    β l * |Work.WilkG4c.xDeriv (F i) l (α l + β l * s) (γ l (α l + β l * s))| ≤ 1 + n := by
  have hβne : β l ≠ 0 := ne_of_gt hβ
  have hC1' : ContDiffAt ℝ 1 (famFunHat (F i))
      (xPt l (α l + β l * s) (γ l (α l + β l * s))) := interior_subset hC1
  have hdiffHat : DifferentiableAt ℝ (famFunHat (F i))
      (xPt l (α l + β l * s) (γ l (α l + β l * s))) := hC1'.differentiableAt_one
  have hxC1 : ContDiffAt ℝ 1 (F i l) (Fin.cons (α l + β l * s) (γ l (α l + β l * s))) :=
    Work.WilkG4c.contDiffAt_famFunHat_xPt (F i) l (α l + β l * s) (γ l (α l + β l * s)) hC1'
  have hxd : DifferentiableAt ℝ (F i l)
      (Fin.cons (α l + β l * s) (γ l (α l + β l * s))) := hxC1.differentiableAt_one
  -- the `x`-derivative is the `fderiv` of the member in the first coordinate
  have hbridge : xDeriv (F i) l (α l + β l * s) (γ l (α l + β l * s))
      = fderiv ℝ (F i l) (Fin.cons (α l + β l * s) (γ l (α l + β l * s)))
          (Pi.single (0 : Fin (n + 1)) (1 : ℝ)) :=
    Work.WilG4c.pullX_xDeriv_eq_fderiv (F i) l (α l + β l * s) (γ l (α l + β l * s)) hdiffHat
  -- reparametrisation of the `t`-derivative of the curve into an `x`-derivative
  have hγA : ∀ j : Fin n,
      deriv (fun t : ℝ => γ l (α l + β l * t) j) s
        = β l * deriv (fun x : ℝ => γ l x j) (α l + β l * s) :=
    fun j => (dca_aux (g := fun x : ℝ => γ l x j) (a := α l) (b := β l) (s := s)
      hβne (hcompid j)).2
  have hφA : deriv (fun t : ℝ => F i l (pt (α l + β l * t) (γ l (α l + β l * t)))) s
      = β l * deriv (fun x : ℝ => F i l (Fin.cons x (γ l x))) (α l + β l * s) :=
    (dca_aux (g := fun x : ℝ => F i l (Fin.cons x (γ l x))) (a := α l) (b := β l) (s := s)
      hβne hcomp).2
  -- the derivative data required by the chain rule `Work.WilG4b.xDeriv_eq`
  have hγi : ∀ j : Fin n, HasDerivAt (fun x : ℝ => γ l x j)
      (deriv (fun x : ℝ => γ l x j) (α l + β l * s)) (α l + β l * s) :=
    fun j => (dca_aux (g := fun x : ℝ => γ l x j) (a := α l) (b := β l) (s := s)
      hβne (hcompid j)).1.hasDerivAt
  have hφi : HasDerivAt (fun x : ℝ => F i l (Fin.cons x (γ l x)))
      (deriv (fun x : ℝ => F i l (Fin.cons x (γ l x))) (α l + β l * s)) (α l + β l * s) :=
    (dca_aux (g := fun x : ℝ => F i l (Fin.cons x (γ l x))) (a := α l) (b := β l) (s := s)
      hβne hcomp).1.hasDerivAt
  have hkey : fderiv ℝ (F i l) (Fin.cons (α l + β l * s) (γ l (α l + β l * s)))
        (Pi.single (0 : Fin (n + 1)) (1 : ℝ))
      = deriv (fun x : ℝ => F i l (Fin.cons x (γ l x))) (α l + β l * s)
        - ∑ j : Fin n, fderiv ℝ (F i l) (Fin.cons (α l + β l * s) (γ l (α l + β l * s)))
            (Pi.single j.succ (1 : ℝ)) * deriv (fun x : ℝ => γ l x j) (α l + β l * s) :=
    Work.WilG4b.xDeriv_eq (F i l) (fun x : ℝ => γ l x) (α l + β l * s)
      (deriv (fun x : ℝ => F i l (Fin.cons x (γ l x))) (α l + β l * s))
      (fun j : Fin n => deriv (fun x : ℝ => γ l x j) (α l + β l * s)) hxC1 hγi hφi
  -- the `y`-partials are bounded by `1`
  have hB : ∀ j : Fin n,
      |fderiv ℝ (F i l) (Fin.cons (α l + β l * s) (γ l (α l + β l * s)))
          (Pi.single j.succ (1 : ℝ))| ≤ 1 :=
    fun j => fcy_aux (F i l) (α l + β l * s) (γ l (α l + β l * s)) hxd
      (hY (γ l (α l + β l * s)) hγc) j
  -- the key identity: `β * xDeriv` equals the `t`-derivative minus the `y`-corrections
  have hmain : β l * xDeriv (F i) l (α l + β l * s) (γ l (α l + β l * s))
      = deriv (fun t : ℝ => F i l (pt (α l + β l * t) (γ l (α l + β l * t)))) s
        - ∑ j : Fin n, fderiv ℝ (F i l) (Fin.cons (α l + β l * s) (γ l (α l + β l * s)))
            (Pi.single j.succ (1 : ℝ)) * deriv (fun t : ℝ => γ l (α l + β l * t) j) s := by
    rw [hbridge, hkey]
    have hsumγ : β l * (∑ j : Fin n, fderiv ℝ (F i l)
          (Fin.cons (α l + β l * s) (γ l (α l + β l * s))) (Pi.single j.succ (1 : ℝ))
          * deriv (fun x : ℝ => γ l x j) (α l + β l * s))
        = ∑ j : Fin n, fderiv ℝ (F i l)
            (Fin.cons (α l + β l * s) (γ l (α l + β l * s))) (Pi.single j.succ (1 : ℝ))
            * deriv (fun t : ℝ => γ l (α l + β l * t) j) s := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [hγA j]
      ring
    rw [← hsumγ, hφA]
    ring
  -- the numerical bound
  have hbound : |deriv (fun t : ℝ => F i l (pt (α l + β l * t) (γ l (α l + β l * t)))) s
        - ∑ j : Fin n, fderiv ℝ (F i l) (Fin.cons (α l + β l * s) (γ l (α l + β l * s)))
            (Pi.single j.succ (1 : ℝ)) * deriv (fun t : ℝ => γ l (α l + β l * t) j) s| ≤
        1 + n := by
    have h3 : |deriv (fun t : ℝ => F i l (pt (α l + β l * t) (γ l (α l + β l * t)))) s
          - ∑ j : Fin n, fderiv ℝ (F i l) (Fin.cons (α l + β l * s) (γ l (α l + β l * s)))
              (Pi.single j.succ (1 : ℝ)) * deriv (fun t : ℝ => γ l (α l + β l * t) j) s|
        ≤ |deriv (fun t : ℝ => F i l (pt (α l + β l * t) (γ l (α l + β l * t)))) s|
          + |∑ j : Fin n, fderiv ℝ (F i l)
              (Fin.cons (α l + β l * s) (γ l (α l + β l * s))) (Pi.single j.succ (1 : ℝ))
              * deriv (fun t : ℝ => γ l (α l + β l * t) j) s| := by
      have h := abs_add_le (deriv (fun t : ℝ => F i l (pt (α l + β l * t)
          (γ l (α l + β l * t)))) s)
        (-(∑ j : Fin n, fderiv ℝ (F i l)
            (Fin.cons (α l + β l * s) (γ l (α l + β l * s))) (Pi.single j.succ (1 : ℝ))
            * deriv (fun t : ℝ => γ l (α l + β l * t) j) s))
      simpa only [sub_eq_add_neg, abs_neg] using h
    have h2 : |∑ j : Fin n, fderiv ℝ (F i l)
          (Fin.cons (α l + β l * s) (γ l (α l + β l * s))) (Pi.single j.succ (1 : ℝ))
          * deriv (fun t : ℝ => γ l (α l + β l * t) j) s| ≤ (n : ℝ) :=
      asml_aux _ _ hB hderγ
    linarith [h3, h2]
  calc β l * |xDeriv (F i) l (α l + β l * s) (γ l (α l + β l * s))|
      = |β l * xDeriv (F i) l (α l + β l * s) (γ l (α l + β l * s))| := by
        rw [abs_mul, abs_of_pos hβ]
    _ = |deriv (fun t : ℝ => F i l (pt (α l + β l * t) (γ l (α l + β l * t)))) s
        - ∑ j : Fin n, fderiv ℝ (F i l) (Fin.cons (α l + β l * s) (γ l (α l + β l * s)))
            (Pi.single j.succ (1 : ℝ)) * deriv (fun t : ℝ => γ l (α l + β l * t) j) s| := by
        rw [hmain]
    _ ≤ 1 + n := hbound

end Work.WilG4c
