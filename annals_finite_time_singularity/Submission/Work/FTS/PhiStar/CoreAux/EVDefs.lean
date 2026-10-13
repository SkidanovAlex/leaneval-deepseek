/-
# `FTS/PhiStar/CoreAux/EVDefs.lean` — the coefficients of `EVz`/`EV`, and the flat-calculus
helpers used to bound them

`Work.FTS.PhiStar.EVz Y = 2(cos²θ − 2 sin²θ)·Y + sin(2θ)·∂_θY` and
`Work.FTS.PhiStar.EV Y = (z/(z+1))·EVz Y` are two of the fields of `StarPkgo2`; the task
`Fb_EV_bound` asks for the flat bounds

`Fb 4 (C A⁴(K+1)) (EVz Y)`, `Fb 4 (C A⁴(K+1)) (EV Y)`

from `Fb 6 (A(K+1)) Y`, `SmoothOpen Y` and the flat bounds of the three coefficients
`cos²θ − 2 sin²θ`, `sin 2θ`, `z/(1+z)`.

This file only fixes the vocabulary:

* `EVphi`, `EVsin`, `EVrho` — the three coefficient functions (as functions on the quadrant);
* `EVC` — the constant of the two bounds;
* `EVCoef A` — the bundle of coefficient facts consumed by the proof: the flat bounds of the
  three coefficients and of `cos 2θ`, the smoothness of the coefficients and of the two
  `θ`-derivatives `∂_θ(sin 2·) = 2 cos 2·`, `∂_θ(cos² − 2 sin²) = −3 sin 2·`, and the three
  derivative identities.

It also collects the elementary flat-calculus lemmas the assembly needs and that were not yet
available in the `CoreAux` chapter:

* `F0_const_mul` — `F0` is closed under scalar multiples (`|c| K`);
* `F0_Dth` — `D_θ f = sin(2θ)∂_θf` acts as one more angular derivative, so `F0 (n+1) K f`
  gives `F0 n K (D_θ f)` (the angular analogue of `F0_zpz`);
* `pth_add_Q0`, `pth_const_mul`, `pth_congr_Q0` — locality/linearity of `∂_θ` on the open
  quadrant;
* `SmoothOpen.const_mul`, `SmoothOpen.add`, `SmoothOpen.congr` — the corresponding closure
  facts for `SmoothOpen`.

Nothing here is a `sorry` or an axiom.
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.PhiStar.CoreAux.Defs
import Submission.Work.FTS.PhiStar.CoreAux.FieldsDefs
import Submission.Work.FTS.PhiStar.CoreAux.F0_congr

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.CoreAux

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The coefficients and the coefficient bundle -/

/-- The angular coefficient `cos²θ − 2 sin²θ` of `EVz`. -/
def EVphi : ℝ → ℝ → ℝ := fun _ θ => Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2

/-- The angular coefficient `sin 2θ` of `EVz`. -/
def EVsin : ℝ → ℝ → ℝ := fun _ θ => Real.sin (2 * θ)

/-- The radial coefficient `z/(1+z)` of `EV`. -/
def EVrho : ℝ → ℝ → ℝ := fun z _ => z / (1 + z)

/-- The constant of the `Fb`-bounds of `EVz` and `EV`. -/
def EVC : ℝ := 4096

/-- **The coefficient data of `EVz` and `EV`.**  `EVCoef A` collects everything the flat
product calculus needs to bound `EVz Y` and `EV Y`: the flat bounds (`F0 6 A`) of the three
coefficient functions and of `cos 2θ`, the smoothness of the coefficients and of the two
angular derivatives, and the three pointwise derivative identities. -/
structure EVCoef (A : ℝ) : Prop where
  /-- `cos²θ − 2 sin²θ` is `C^∞` on the open quadrant -/
  smoothPhi : EllipticEst.SmoothOpen EVphi
  /-- `sin 2θ` is `C^∞` on the open quadrant -/
  smoothSin : EllipticEst.SmoothOpen EVsin
  /-- `z/(1+z)` is `C^∞` on the open quadrant -/
  smoothRho : EllipticEst.SmoothOpen EVrho
  /-- `cos 2θ` is `C^∞` on the open quadrant -/
  smoothCos2 : EllipticEst.SmoothOpen (fun _ θ => Real.cos (2 * θ))
  /-- `∂_θ(cos²θ − 2 sin²θ)` is `C^∞` on the open quadrant -/
  smoothDPhi : EllipticEst.SmoothOpen (Work.Spaces.pth EVphi)
  /-- `∂_θ(sin 2θ)` is `C^∞` on the open quadrant -/
  smoothDSin : EllipticEst.SmoothOpen (Work.Spaces.pth EVsin)
  /-- flat bound for `cos²θ − 2 sin²θ` -/
  f0Phi : F0 6 A EVphi
  /-- flat bound for `sin 2θ` -/
  f0Sin : F0 6 A EVsin
  /-- flat bound for `z/(1+z)` -/
  f0Rho : F0 6 A EVrho
  /-- flat bound for `cos 2θ` -/
  f0Cos2 : F0 6 A (fun _ θ => Real.cos (2 * θ))
  /-- `∂_θ(cos²θ − 2 sin²θ) = −3 sin 2θ` -/
  dPhi : ∀ z θ : ℝ, Work.Spaces.pth EVphi z θ = -3 * Real.sin (2 * θ)
  /-- `∂_θ(sin 2θ) = 2 cos 2θ` -/
  dSin : ∀ z θ : ℝ, Work.Spaces.pth EVsin z θ = 2 * Real.cos (2 * θ)
  /-- `∂_θ(z/(1+z)) = 0` -/
  dRho : ∀ z θ : ℝ, Work.Spaces.pth EVrho z θ = 0

/-! ## `SmoothOpen` closure -/

theorem SmoothOpen.const_mul {f : ℝ → ℝ → ℝ} (hf : EllipticEst.SmoothOpen f) (c : ℝ) :
    EllipticEst.SmoothOpen (fun z θ => c * f z θ) := by
  have h : Function.uncurry (fun z θ => c * f z θ)
      = fun p : ℝ × ℝ => c * Function.uncurry f p := rfl
  simpa only [EllipticEst.SmoothOpen, h] using (contDiffOn_const.mul hf)

theorem SmoothOpen.add {f g : ℝ → ℝ → ℝ} (hf : EllipticEst.SmoothOpen f)
    (hg : EllipticEst.SmoothOpen g) :
    EllipticEst.SmoothOpen (fun z θ => f z θ + g z θ) := by
  have h : Function.uncurry (fun z θ => f z θ + g z θ)
      = fun p : ℝ × ℝ => Function.uncurry f p + Function.uncurry g p := rfl
  simpa only [EllipticEst.SmoothOpen, h] using hf.add hg

theorem SmoothOpen.congr {f g : ℝ → ℝ → ℝ} (hf : EllipticEst.SmoothOpen f)
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → f z θ = g z θ) :
    EllipticEst.SmoothOpen g := by
  refine (EllipticEst.smoothOpen_iff_forall g).mpr fun n => ?_
  refine ((EllipticEst.smoothOpen_iff_forall f).mp hf n).congr ?_
  intro p hp
  obtain ⟨hz, hθ, hθ'⟩ := EllipticEst.mem_Q0.mp hp
  exact (h p.1 p.2 hz hθ hθ').symm

theorem SmoothOpen.const (c : ℝ) : EllipticEst.SmoothOpen (fun _ _ : ℝ => c) := by
  have h : Function.uncurry (fun _ _ : ℝ => c) = fun _ : ℝ × ℝ => c := rfl
  simpa only [EllipticEst.SmoothOpen, h] using contDiffOn_const

/-! ## Scalar multiples in the flat class -/

theorem pzIter_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) (k : ℕ) :
    Work.Spaces.pzIter k (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.pzIter k f z θ := by
  induction k with
  | zero => rfl
  | succ n ih =>
    rw [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_succ, ih]
    funext z θ
    simp only [Work.Spaces.pz]
    exact deriv_const_mul_field c

theorem DthIter_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) (k : ℕ) :
    Work.Spaces.DthIter k (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.DthIter k f z θ := by
  induction k with
  | zero => rfl
  | succ n ih =>
    rw [Work.Spaces.DthIter_succ, Work.Spaces.DthIter_succ, ih]
    funext z θ
    simp only [Work.Spaces.Dth, Work.Spaces.pth]
    rw [deriv_const_mul_field c]
    ring

theorem F0_const_mul {n : ℕ} {K : ℝ} {f : ℝ → ℝ → ℝ} (c : ℝ) (hf : F0 n K f) :
    F0 n (|c| * K) (fun z θ => c * f z θ) := by
  intro k i hki z θ hz hθ hθ'
  rw [DthIter_const_mul c f i, pzIter_const_mul c (Work.Spaces.DthIter i f) k]
  have h : (z + 1) ^ k * (c * Work.Spaces.pzIter k (Work.Spaces.DthIter i f) z θ)
      = c * ((z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter i f) z θ) := by ring
  rw [h, abs_mul]
  exact mul_le_mul_of_nonneg_left (hf k i hki z θ hz hθ hθ') (abs_nonneg c)

/-! ## `D_θ` raises the angular order by one -/

theorem DthIter_Dth (i : ℕ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.DthIter i (Work.Spaces.Dth g) = Work.Spaces.DthIter (i + 1) g := by
  induction i with
  | zero => rfl
  | succ n ih =>
    rw [Work.Spaces.DthIter_succ (n := n) (f := Work.Spaces.Dth g), ih,
      Work.Spaces.DthIter_succ (n := n + 1) (f := g)]

/-- `D_θ` is one more angular derivative: `F0 (n+1) K f` gives `F0 n K (D_θ f)`. -/
theorem F0_Dth {n : ℕ} {K : ℝ} {g : ℝ → ℝ → ℝ} (h : F0 (n + 1) K g) :
    F0 n K (Work.Spaces.Dth g) := by
  intro k i hki z θ hz hθ hθ'
  have h' := h k (i + 1) (by omega) z θ hz hθ hθ'
  rwa [← DthIter_Dth i g] at h'

/-! ## Locality and linearity of `∂_θ` on the open quadrant -/

theorem pth_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pth (fun z θ => c * f z θ) = fun z θ => c * Work.Spaces.pth f z θ := by
  funext z θ
  simp only [Work.Spaces.pth]
  exact deriv_const_mul_field c

theorem pth_add_Q0 {f g : ℝ → ℝ → ℝ} (hf : EllipticEst.SmoothOpen f)
    (hg : EllipticEst.SmoothOpen g) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pth (fun z θ => f z θ + g z θ) z θ
        = Work.Spaces.pth f z θ + Work.Spaces.pth g z θ := by
  intro z θ hz h1 h2
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨h1, h2⟩
  have hd1 : DifferentiableAt ℝ (fun θ' : ℝ => f z θ') θ :=
    ((hf.curry_θ hz).differentiableOn (by simp)).differentiableAt (isOpen_Ioo.mem_nhds hθ)
  have hd2 : DifferentiableAt ℝ (fun θ' : ℝ => g z θ') θ :=
    ((hg.curry_θ hz).differentiableOn (by simp)).differentiableAt (isOpen_Ioo.mem_nhds hθ)
  have hff : (fun θ' : ℝ => f z θ' + g z θ')
      = (fun θ' : ℝ => f z θ') + (fun θ' : ℝ => g z θ') := by
    funext θ'; rfl
  simp only [Work.Spaces.pth]
  rw [hff]
  exact deriv_add hd1 hd2

theorem pth_congr_Q0 {f g : ℝ → ℝ → ℝ}
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → f z θ = g z θ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pth f z θ = Work.Spaces.pth g z θ := by
  intro z θ hz h1 h2
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨h1, h2⟩
  have heq : (fun θ' : ℝ => f z θ') =ᶠ[𝓝 θ] (fun θ' : ℝ => g z θ') := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
    exact h z θ' hz hθ'.1 hθ'.2
  simp only [Work.Spaces.pth]
  exact heq.deriv_eq

end Work.FTS.PhiStar.CoreAux
