import Mathlib
import Submission.Work.WilG4c.StepCleanDefs

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilCrux

open Work.WilG4c

/-- The continuous linear map `v ↦ Fin.append 0 v`: the inclusion of the fibre coordinates
`Fin b` into `Fin (a + b)`, with the parameter block set to `0`. -/
def fibreIncl (a b : ℕ) : (Fin b → ℝ) →L[ℝ] (Fin (a + b) → ℝ) :=
  ContinuousLinearMap.pi
    (Fin.addCases (fun _ : Fin a => (0 : (Fin b → ℝ) →L[ℝ] ℝ))
      (fun j : Fin b => ContinuousLinearMap.proj j))

/-- Value of `fibreIncl` on a vector: it is `Fin.append 0 v`. -/
theorem fibreIncl_apply (a b : ℕ) (v : Fin b → ℝ) :
    fibreIncl a b v = Fin.append (0 : Fin a → ℝ) v := by
  funext k
  unfold fibreIncl
  rw [ContinuousLinearMap.pi_apply]
  induction k using Fin.addCases with
  | left i' => rw [Fin.addCases_left, zero_apply, Fin.append_left]; rfl
  | right j' =>
      rw [Fin.addCases_right, ContinuousLinearMap.proj_apply, Fin.append_right]

/-- The affine map `y ↦ Fin.append u y` (parameter block held fixed at `u`) equals the linear
inclusion `fibreIncl a b` plus the constant `Fin.append u 0`. -/
theorem append_eq_fibreIncl_add (a b : ℕ) (u : Fin a → ℝ) (y : Fin b → ℝ) :
    Fin.append u y = fibreIncl a b y + Fin.append u (0 : Fin b → ℝ) := by
  rw [fibreIncl_apply]
  funext k
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · simp [Fin.append_left]
  · simp [Fin.append_right]

/-- The affine map `y ↦ Fin.append u y` has derivative `fibreIncl a b`, independently of the
base point `u` (the constant part is annihilated). -/
theorem hasFDerivAt_append_const' (a b : ℕ) (u : Fin a → ℝ) (y₀ : Fin b → ℝ) :
    HasFDerivAt (fun y : Fin b → ℝ => Fin.append u y) (fibreIncl a b) y₀ := by
  have hfun : (fun y : Fin b → ℝ => Fin.append u y)
      = fun y => fibreIncl a b y + Fin.append u (0 : Fin b → ℝ) := by
    funext y; exact append_eq_fibreIncl_add a b u y
  rw [hfun]
  exact (fibreIncl a b).hasFDerivAt.add_const _

/-- `famFun G` restricted to the fibre over the parameter `w`: `y ↦ famFun G (Fin.append w y)`
is the one-variable function `G w`. -/
theorem famFun_comp_append (a b : ℕ) (G : (Fin a → ℝ) → (Fin b → ℝ) → ℝ)
    (w : Fin a → ℝ) :
    (famFun G ∘ (fun y : Fin b → ℝ => Fin.append w y)) = G w := by
  funext y
  simp only [Function.comp_apply]
  simp [famFun, Fin.append_left, Fin.append_right]

theorem fibreFderivFamFun {a b : ℕ} (G : (Fin a → ℝ) → (Fin b → ℝ) → ℝ)
    (w : Fin a → ℝ) (z v : Fin b → ℝ)
    (hd : DifferentiableAt ℝ (Work.WilG4c.famFun G) (Fin.append w z)) :
    fderiv ℝ (Work.WilG4c.famFun G) (Fin.append w z) (Fin.append 0 v)
      = fderiv ℝ (G w) z v := by
  have hφ : DifferentiableAt ℝ (fun y : Fin b → ℝ => Fin.append w y) z :=
    (hasFDerivAt_append_const' a b w z).differentiableAt
  have hφ' : fderiv ℝ (fun y : Fin b → ℝ => Fin.append w y) z = fibreIncl a b :=
    (hasFDerivAt_append_const' a b w z).fderiv
  have hcomp := fderiv_comp (𝕜 := ℝ) (x := z)
    (f := fun y : Fin b → ℝ => Fin.append w y) (g := famFun G) hd hφ
  have hchain : fderiv ℝ (famFun G ∘ (fun y : Fin b → ℝ => Fin.append w y)) z
      = (fderiv ℝ (famFun G) (Fin.append w z)).comp (fibreIncl a b) := by
    rw [hcomp, hφ']
  have hGfun := famFun_comp_append a b G w
  have key : fderiv ℝ (G w) z
      = (fderiv ℝ (famFun G) (Fin.append w z)).comp (fibreIncl a b) := by
    rw [← hGfun]
    exact hchain
  calc fderiv ℝ (famFun G) (Fin.append w z) (Fin.append 0 v)
      = fderiv ℝ (famFun G) (Fin.append w z) (fibreIncl a b v) := by
        rw [fibreIncl_apply]
    _ = ((fderiv ℝ (famFun G) (Fin.append w z)).comp (fibreIncl a b)) v := by
        rw [ContinuousLinearMap.comp_apply]
    _ = fderiv ℝ (G w) z v :=
        (congrArg (fun L : (Fin b → ℝ) →L[ℝ] ℝ => L v) key).symm

end Work.WilCrux
