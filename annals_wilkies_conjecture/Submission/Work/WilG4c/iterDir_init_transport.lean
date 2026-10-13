import Mathlib
import Submission.Work.WilG4c.Engine
import Submission.Work.WilG4c.IterDirAux
import Submission.Work.WilG4c.iterDir_slice_transport

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace Work.WilG4c

open Work.WilkG4c

/-! ### The affine insertion `v ↦ Fin.snoc v c` and its linear part

The coordinate projection `Fin.init : ℝⁿ⁺¹ → ℝⁿ` is split by the affine insertion
`v ↦ Fin.snoc v c` (for any `c : ℝ`), since `Fin.init (Fin.snoc v c) = v`.  To differentiate along
this splitting one needs the linear part of the insertion, the continuous linear map
`snocCubeCLM n : ℝⁿ →L[ℝ] ℝⁿ⁺¹`, `v ↦ Fin.snoc v 0`. -/

/-- The continuous linear "insertion at the end" `v ↦ Fin.snoc v 0 : ℝⁿ → ℝⁿ⁺¹`. -/
def snocCubeCLM (n : ℕ) : (Fin n → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) :=
  ContinuousLinearMap.pi fun i : Fin (n + 1) =>
    Fin.lastCases (0 : (Fin n → ℝ) →L[ℝ] ℝ)
      (fun j : Fin n => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j) i

lemma snocCubeCLM_apply (n : ℕ) (v : Fin n → ℝ) : snocCubeCLM n v = Fin.snoc v 0 := by
  funext i
  simp only [snocCubeCLM, ContinuousLinearMap.pi_apply]
  cases i using Fin.lastCases with
  | last => simp
  | cast j => simp

/-- The insertion `v ↦ Fin.snoc v c` is affine, with linear part `snocCubeCLM n`. -/
lemma hasFDerivAt_snocCube (n : ℕ) (c : ℝ) (v : Fin n → ℝ) :
    HasFDerivAt (fun v : Fin n → ℝ => Fin.snoc v c) (snocCubeCLM n) v := by
  have hfun : (fun v : Fin n → ℝ => Fin.snoc v c)
      = (fun v : Fin n → ℝ => Fin.snoc (0 : Fin n → ℝ) c + snocCubeCLM n v) := by
    funext w
    rw [snocCubeCLM_apply]
    funext i
    cases i using Fin.lastCases with
    | last => simp
    | cast j => simp
  rw [hfun]
  exact (snocCubeCLM n).hasFDerivAt.const_add _

/-- The insertion carries the `i`-th coordinate direction to the `Fin.castSucc i`-th one. -/
lemma snocCubeCLM_single {n : ℕ} (i : Fin n) :
    snocCubeCLM n (Pi.single i (1 : ℝ))
      = (Pi.single (Fin.castSucc i) (1 : ℝ) : Fin (n + 1) → ℝ) := by
  funext j
  rw [snocCubeCLM_apply]
  cases j using Fin.lastCases with
  | last =>
    have hne : Fin.last n ≠ Fin.castSucc i := by
      intro hh
      have h2 := congrArg Fin.val hh
      simp only [Fin.val_last, Fin.val_castSucc] at h2
      omega
    rw [Fin.snoc_last, Pi.single_eq_of_ne hne]
  | cast k =>
    rw [Fin.snoc_castSucc]
    by_cases h : k = i
    · subst h; simp
    · rw [Pi.single_eq_of_ne h,
        Pi.single_eq_of_ne (fun hh => h (Fin.castSucc_injective n hh))]

/-- **`iterDir` transports through the projection `Fin.init`.**  For `g : (Fin n → ℝ) → ℝ`,
directions `M` in the cube coordinates of `Fin n` and a base point `y : Fin (n+1) → ℝ`, the
iterated directional derivative of the *padded* function `w ↦ g (Fin.init w)` in the directions
`M.map Fin.castSucc` (which never point into the dropped last coordinate) is the iterated
directional derivative of `g` at `Fin.init y` in the directions `M`.

The proof is by induction on `M`, exactly parallel to the existing, proved
`Work.WilkG4c.iterDir_slice_transport` (which does the same for the front insertion
`pt x y = Fin.cons x y` and directions `M.map Fin.succ`): peel the head with `iterDir_cons`,
replace `iterDir (M'.map Fin.castSucc) (fun w => g (Fin.init w))` by
`fun w => iterDir M' g (Fin.init w)` using the induction hypothesis (an eventual equality, the
smoothness hypothesis propagating through `ContDiffAt.eventually`; note
`((i :: M').map Fin.castSucc).length = (M'.map Fin.castSucc).length + 1` definitionally), then
the chain rule `fderiv_comp` against the continuous linear map `Fin.init`, using
`Fin.init (Pi.single (Fin.castSucc i) 1) = Pi.single i 1`. -/
theorem iterDir_init_transport {n : ℕ} (g : (Fin n → ℝ) → ℝ) (M : List (Fin n))
    (y : Fin (n + 1) → ℝ)
    (h : ContDiffAt ℝ (M.map Fin.castSucc).length
        (fun w : Fin (n + 1) → ℝ => g (Fin.init w)) y) :
    Work.WilkG4c.iterDir (M.map Fin.castSucc) (fun w : Fin (n + 1) → ℝ => g (Fin.init w)) y =
      Work.WilkG4c.iterDir M g (Fin.init y) := by
  revert y
  induction M with
  | nil => intro y _; rfl
  | cons i M' ih =>
    intro y h
    -- `h` is the `C^{|M'.map Fin.castSucc|+1}` statement at `y`.
    have h' : ContDiffAt ℝ ((M'.map Fin.castSucc).length + 1)
        (fun w : Fin (n + 1) → ℝ => g (Fin.init w)) y := by simpa using h
    -- Hence the padded function is `C^{|M'.map Fin.castSucc|}` on a neighbourhood of `y`, which is
    -- what the induction hypothesis needs.
    have hle : ContDiffAt ℝ ((M'.map Fin.castSucc).length : WithTop ℕ∞)
        (fun w : Fin (n + 1) → ℝ => g (Fin.init w)) y := h'.of_le (by simp)
    have hS : ∀ᶠ z in 𝓝 y, ContDiffAt ℝ ((M'.map Fin.castSucc).length : WithTop ℕ∞)
        (fun w : Fin (n + 1) → ℝ => g (Fin.init w)) z := hle.eventually (by simp)
    -- The induction hypothesis, as an eventual equality of functions on `ℝⁿ⁺¹`.
    have h_ev : iterDir (M'.map Fin.castSucc) (fun w : Fin (n + 1) → ℝ => g (Fin.init w))
        =ᶠ[𝓝 y] (fun w : Fin (n + 1) → ℝ => iterDir M' g (Fin.init w)) := by
      filter_upwards [hS] with w hw
      exact ih w hw
    -- Consequently this composed function is `C¹` (and hence differentiable) at `y`.
    have hFsmooth : ContDiffAt ℝ 1
        (iterDir (M'.map Fin.castSucc) (fun w : Fin (n + 1) → ℝ => g (Fin.init w))) y :=
      iterDir_contDiffAt (fun w : Fin (n + 1) → ℝ => g (Fin.init w)) (M'.map Fin.castSucc) 1 y h'
    have hHsmooth : ContDiffAt ℝ 1
        (fun w : Fin (n + 1) → ℝ => iterDir M' g (Fin.init w)) y :=
      hFsmooth.congr_of_eventuallyEq h_ev.symm
    have hHdiff : DifferentiableAt ℝ
        (fun w : Fin (n + 1) → ℝ => iterDir M' g (Fin.init w)) y :=
      hHsmooth.differentiableAt (by norm_num)
    -- The affine section `v ↦ Fin.snoc v (y (last n))` of the projection `Fin.init` maps
    -- `Fin.init y` back to `y`.
    have hσ : HasFDerivAt (fun v : Fin n → ℝ => Fin.snoc v (y (Fin.last n)))
        (snocCubeCLM n) (Fin.init y) := hasFDerivAt_snocCube n (y (Fin.last n)) (Fin.init y)
    -- Chain rule along that section: `iterDir M' g = (iterDir M' g ∘ Fin.init) ∘ snoc`.
    have hcomp : fderiv ℝ (iterDir M' g) (Fin.init y)
        = (fderiv ℝ (fun w : Fin (n + 1) → ℝ => iterDir M' g (Fin.init w)) y).comp
            (snocCubeCLM n) := by
      have h₁ := fderiv_comp (x := Fin.init y)
        (f := fun v : Fin n → ℝ => Fin.snoc v (y (Fin.last n)))
        (g := fun w : Fin (n + 1) → ℝ => iterDir M' g (Fin.init w))
        (by simpa using hHdiff) hσ.differentiableAt
      have hfun : ((fun w : Fin (n + 1) → ℝ => iterDir M' g (Fin.init w)) ∘
          (fun v : Fin n → ℝ => Fin.snoc v (y (Fin.last n)))) = iterDir M' g := by
        funext v
        simp only [Function.comp_apply, Fin.init_snoc]
      simp only [Fin.snoc_init_self, hσ.fderiv] at h₁
      rw [hfun] at h₁
      exact h₁
    -- Peel the outermost derivative and combine the three rewrites.
    simp only [List.map_cons, iterDir_cons]
    rw [h_ev.fderiv_eq, hcomp, ContinuousLinearMap.comp_apply, snocCubeCLM_single]

end Work.WilG4c
