/-
Copyright: work module for the Elgindi finite-time singularity project.

# `aeI1Base`: the finite-order calculus layer for the compact `I₁` identity

`Work.FTS.EllipticEst.Dispatch.aeI1Identity` is the chain identity

  `i1D Φ = i1Pp Φ - 2η(1+η) i1N Φ - 2η i1Aa Φ + i1X Φ`

for `Φ` of class `C³` on the open quadrant `(0,∞) × (0,π/2)`, vanishing off a rectangle
`[a,b] × [c,d]` with `0 < a`, `0 < c`, `d < π/2`.

This module provides the calculus layer that the assembly needs: the partial derivatives
`pz`, `pth` lower the order of smoothness by one *on the open quadrant* (finite order, as opposed
to the `C^∞` statements of `Work.FTS.LocData.SmoothChain`), whence all the derivative factors of
`Φ` are continuous on the rectangle; and the vanishing of those factors off the rectangle, which
is what makes every integrand compactly supported.
-/
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.Dispatch.AeI1Defs
import Submission.Work.Spaces.CurrySmooth
import Submission.Work.FTS.EllipticEst.H2W.SlotA.radialDerivPointwiseOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Dispatch

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-- The open half-strip `(0,∞) × (0,π/2)`. -/
abbrev ftsQd : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)

/-- The rectangle `[a,b] × [c,d]`. -/
abbrev ftsBox (a b c d : ℝ) : Set (ℝ × ℝ) := Set.Icc a b ×ˢ Set.Icc c d

theorem isOpen_ftsQd : IsOpen ftsQd := isOpen_Ioi.prod isOpen_Ioo

theorem natCast_succ_ne_zero (n : ℕ) : ((n + 1 : ℕ) : ℕ∞ω) ≠ 0 := by
  simp

/-! ## Finite-order smoothness of the slice derivatives -/

/-- `Work.Spaces.pz` lowers the order of smoothness by one. -/
theorem contDiffOn_uncurry_pz_fin {n : ℕ} {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pz G)) V := by
  have hchain : ∀ p ∈ V, Work.Spaces.pz G p.1 p.2
      = fderiv ℝ (Function.uncurry G) p (1, 0) := fun p hp =>
    Work.Spaces.pz_eq_fderiv ((h.differentiableOn
      (natCast_succ_ne_zero n)).differentiableAt (hV.mem_nhds hp))
  have hfd : ContDiffOn ℝ n (fun (p : ℝ × ℝ) => fderiv ℝ (Function.uncurry G) p) V :=
    h.fderiv_of_isOpen hV (m := n) (by simp)
  have hcomp : ContDiffOn ℝ n
      (fun (p : ℝ × ℝ) => (fderiv ℝ (Function.uncurry G) p) (1, 0)) V := by
    simpa using hfd.clm_apply contDiffOn_const
  exact hcomp.congr hchain

/-- `Work.Spaces.pth` lowers the order of smoothness by one. -/
theorem contDiffOn_uncurry_pth_fin {n : ℕ} {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pth G)) V := by
  have hchain : ∀ p ∈ V, Work.Spaces.pth G p.1 p.2
      = fderiv ℝ (Function.uncurry G) p (0, 1) := fun p hp =>
    Work.Spaces.pth_eq_fderiv ((h.differentiableOn
      (natCast_succ_ne_zero n)).differentiableAt (hV.mem_nhds hp))
  have hfd : ContDiffOn ℝ n (fun (p : ℝ × ℝ) => fderiv ℝ (Function.uncurry G) p) V :=
    h.fderiv_of_isOpen hV (m := n) (by simp)
  have hcomp : ContDiffOn ℝ n
      (fun (p : ℝ × ℝ) => (fderiv ℝ (Function.uncurry G) p) (0, 1)) V := by
    simpa using hfd.clm_apply contDiffOn_const
  exact hcomp.congr hchain

/-! ## The smoothness of the derivative factors of `Φ` on the open quadrant -/

theorem contDiffOn_uncurry_pz {Φ : ℝ → ℝ → ℝ}
    (hsm : ContDiffOn ℝ 3 (Function.uncurry Φ) ftsQd) :
    ContDiffOn ℝ 2 (Function.uncurry (Work.Spaces.pz Φ)) ftsQd :=
  contDiffOn_uncurry_pz_fin isOpen_ftsQd hsm

theorem contDiffOn_uncurry_pth {Φ : ℝ → ℝ → ℝ}
    (hsm : ContDiffOn ℝ 3 (Function.uncurry Φ) ftsQd) :
    ContDiffOn ℝ 2 (Function.uncurry (Work.Spaces.pth Φ)) ftsQd :=
  contDiffOn_uncurry_pth_fin isOpen_ftsQd hsm

theorem contDiffOn_uncurry_pzIter_two {Φ : ℝ → ℝ → ℝ}
    (hsm : ContDiffOn ℝ 3 (Function.uncurry Φ) ftsQd) :
    ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pzIter 2 Φ)) ftsQd := by
  have h1 : ContDiffOn ℝ 2 (Function.uncurry (Work.Spaces.pz Φ)) ftsQd :=
    contDiffOn_uncurry_pz hsm
  have h2 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pz (Work.Spaces.pz Φ))) ftsQd :=
    contDiffOn_uncurry_pz_fin isOpen_ftsQd (n := 1) h1
  simpa only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero] using h2

theorem contDiffOn_uncurry_pthIter_two {Φ : ℝ → ℝ → ℝ}
    (hsm : ContDiffOn ℝ 3 (Function.uncurry Φ) ftsQd) :
    ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pthIter 2 Φ)) ftsQd := by
  have h1 : ContDiffOn ℝ 2 (Function.uncurry (Work.Spaces.pth Φ)) ftsQd :=
    contDiffOn_uncurry_pth hsm
  have h2 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pth (Work.Spaces.pth Φ))) ftsQd :=
    contDiffOn_uncurry_pth_fin isOpen_ftsQd (n := 1) h1
  simpa only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero] using h2

theorem contDiffOn_uncurry_pz_pth {Φ : ℝ → ℝ → ℝ}
    (hsm : ContDiffOn ℝ 3 (Function.uncurry Φ) ftsQd) :
    ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pz (Work.Spaces.pth Φ))) ftsQd :=
  contDiffOn_uncurry_pz_fin isOpen_ftsQd (n := 1) (contDiffOn_uncurry_pth hsm)

theorem continuousOn_uncurry_pz_pthIter_two {Φ : ℝ → ℝ → ℝ}
    (hsm : ContDiffOn ℝ 3 (Function.uncurry Φ) ftsQd) :
    ContinuousOn (Function.uncurry (Work.Spaces.pz (Work.Spaces.pthIter 2 Φ))) ftsQd :=
  (contDiffOn_uncurry_pz_fin isOpen_ftsQd (n := 0)
    (contDiffOn_uncurry_pthIter_two hsm)).continuousOn

theorem continuousOn_uncurry_pz {Φ : ℝ → ℝ → ℝ}
    (hsm : ContDiffOn ℝ 3 (Function.uncurry Φ) ftsQd) :
    ContinuousOn (Function.uncurry (Work.Spaces.pz Φ)) ftsQd :=
  (contDiffOn_uncurry_pz hsm).continuousOn

theorem continuousOn_uncurry_pth {Φ : ℝ → ℝ → ℝ}
    (hsm : ContDiffOn ℝ 3 (Function.uncurry Φ) ftsQd) :
    ContinuousOn (Function.uncurry (Work.Spaces.pth Φ)) ftsQd :=
  (contDiffOn_uncurry_pth hsm).continuousOn

theorem continuousOn_uncurry_pthIter_two {Φ : ℝ → ℝ → ℝ}
    (hsm : ContDiffOn ℝ 3 (Function.uncurry Φ) ftsQd) :
    ContinuousOn (Function.uncurry (Work.Spaces.pthIter 2 Φ)) ftsQd :=
  (contDiffOn_uncurry_pthIter_two hsm).continuousOn

theorem continuousOn_uncurry_pzIter_two {Φ : ℝ → ℝ → ℝ}
    (hsm : ContDiffOn ℝ 3 (Function.uncurry Φ) ftsQd) :
    ContinuousOn (Function.uncurry (Work.Spaces.pzIter 2 Φ)) ftsQd :=
  (contDiffOn_uncurry_pzIter_two hsm).continuousOn

theorem continuousOn_uncurry_pz_pth {Φ : ℝ → ℝ → ℝ}
    (hsm : ContDiffOn ℝ 3 (Function.uncurry Φ) ftsQd) :
    ContinuousOn (Function.uncurry (Work.Spaces.pz (Work.Spaces.pth Φ))) ftsQd :=
  (contDiffOn_uncurry_pz_pth hsm).continuousOn

/-! ## Vanishing on strips -/

theorem pz_eq_zero_of_strip {Ψ : ℝ → ℝ → ℝ} {J : Set ℝ} (hJ : IsOpen J)
    (h : ∀ z ∈ J, ∀ θ, Ψ z θ = 0) : ∀ z ∈ J, ∀ θ, Work.Spaces.pz Ψ z θ = 0 := by
  intro z hz θ
  have hev : (fun z' : ℝ => Ψ z' θ) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
    filter_upwards [hJ.mem_nhds hz] with z' hz'
    exact h z' hz' θ
  rw [show Work.Spaces.pz Ψ z θ = deriv (fun z' : ℝ => Ψ z' θ) z from rfl, hev.deriv_eq]
  simp

theorem pth_eq_zero_of_strip {Ψ : ℝ → ℝ → ℝ} {J : Set ℝ} (hJ : IsOpen J)
    (h : ∀ z ∈ J, ∀ θ, Ψ z θ = 0) : ∀ z ∈ J, ∀ θ, Work.Spaces.pth Ψ z θ = 0 := by
  intro z hz θ
  have hev : (fun θ' : ℝ => Ψ z θ') = fun _ => (0 : ℝ) := funext (fun θ' => h z hz θ')
  rw [show Work.Spaces.pth Ψ z θ = deriv (fun θ' : ℝ => Ψ z θ') θ from rfl, hev]
  simp

theorem pzIter_eq_zero_of_strip_z {Ψ : ℝ → ℝ → ℝ} {J : Set ℝ} (hJ : IsOpen J)
    (h : ∀ z ∈ J, ∀ θ, Ψ z θ = 0) (k : ℕ) :
    ∀ z ∈ J, ∀ θ, Work.Spaces.pzIter k Ψ z θ = 0 := by
  induction k with
  | zero => exact h
  | succ k ih =>
      rw [Work.Spaces.pzIter_succ]
      exact pz_eq_zero_of_strip hJ ih

theorem pthIter_eq_zero_of_strip_z {Ψ : ℝ → ℝ → ℝ} {J : Set ℝ} (hJ : IsOpen J)
    (h : ∀ z ∈ J, ∀ θ, Ψ z θ = 0) (k : ℕ) :
    ∀ z ∈ J, ∀ θ, Work.Spaces.pthIter k Ψ z θ = 0 := by
  intro z hz
  induction k with
  | zero => exact h z hz
  | succ k ih =>
      intro θ
      have hev : (fun θ' : ℝ => Work.Spaces.pthIter k Ψ z θ') = fun _ => (0 : ℝ) := funext ih
      rw [show Work.Spaces.pthIter (k + 1) Ψ z θ
            = deriv (fun θ' : ℝ => Work.Spaces.pthIter k Ψ z θ') θ from rfl, hev]
      simp

theorem pzIter_eq_zero_of_strip_θ {Ψ : ℝ → ℝ → ℝ} {J : Set ℝ} (hJ : IsOpen J)
    (h : ∀ z, ∀ θ ∈ J, Ψ z θ = 0) (k : ℕ) :
    ∀ z, ∀ θ ∈ J, Work.Spaces.pzIter k Ψ z θ = 0 := by
  induction k with
  | zero => exact h
  | succ k ih =>
      intro z θ hθ
      have hev : (fun z' : ℝ => Work.Spaces.pzIter k Ψ z' θ) = fun _ => (0 : ℝ) :=
        funext (fun z' => ih z' θ hθ)
      rw [show Work.Spaces.pzIter (k + 1) Ψ z θ
            = deriv (fun z' : ℝ => Work.Spaces.pzIter k Ψ z' θ) z from rfl, hev]
      simp

theorem pthIter_eq_zero_of_strip_θ {Ψ : ℝ → ℝ → ℝ} {J : Set ℝ} (hJ : IsOpen J)
    (h : ∀ z, ∀ θ ∈ J, Ψ z θ = 0) (k : ℕ) :
    ∀ z, ∀ θ ∈ J, Work.Spaces.pthIter k Ψ z θ = 0 := by
  induction k with
  | zero => exact h
  | succ k ih =>
      intro z θ hθ
      have hev : (fun θ' : ℝ => Work.Spaces.pthIter k Ψ z θ') =ᶠ[𝓝 θ] (fun _ => (0 : ℝ)) := by
        filter_upwards [hJ.mem_nhds hθ] with θ' hθ'
        exact ih z θ' hθ'
      rw [show Work.Spaces.pthIter (k + 1) Ψ z θ
            = deriv (fun θ' : ℝ => Work.Spaces.pthIter k Ψ z θ') θ from rfl, hev.deriv_eq]
      simp

/-! ## Instantiating the vanishing for `Φ` supported in the rectangle -/

theorem notMem_Icc_of_lt {a b z : ℝ} (h : z < a) : z ∉ Set.Icc a b :=
  fun hc => (not_le.mpr h) hc.1

theorem notMem_Icc_of_gt {a b z : ℝ} (h : b < z) : z ∉ Set.Icc a b :=
  fun hc => (not_le.mpr h) hc.2

theorem notMem_Icc_of_lt' {c d θ : ℝ} (h : θ < c) : θ ∉ Set.Icc c d :=
  fun hc => (not_le.mpr h) hc.1

theorem notMem_Icc_of_gt' {c d θ : ℝ} (h : d < θ) : θ ∉ Set.Icc c d :=
  fun hc => (not_le.mpr h) hc.2

section Support

variable {Φ : ℝ → ℝ → ℝ} {a b c d : ℝ}

/-- Every `z`- and `θ`-derivative of `Φ` (and of `pthIter l Φ`) vanishes for `z` outside `[a,b]`. -/
theorem pzIter_pthIter_eq_zero_of_z
    (hsupp : ∀ z θ, z ∉ Set.Icc a b ∨ θ ∉ Set.Icc c d → Φ z θ = 0)
    {z : ℝ} (hz : z ∉ Set.Icc a b) (k l : ℕ) (θ : ℝ) :
    Work.Spaces.pzIter k (Work.Spaces.pthIter l Φ) z θ = 0 := by
  have hz' : z < a ∨ b < z := by
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hz
    exact hz
  rcases hz' with hlt | hgt
  · refine pzIter_eq_zero_of_strip_z (Ψ := Work.Spaces.pthIter l Φ) (J := Set.Iio a)
      isOpen_Iio ?_ k z hlt θ
    intro z' hz' θ'
    exact pthIter_eq_zero_of_strip_z (Ψ := Φ) (J := Set.Iio a) isOpen_Iio
      (fun z'' hz'' θ'' => hsupp z'' θ'' (Or.inl (notMem_Icc_of_lt hz''))) l z' hz' θ'
  · refine pzIter_eq_zero_of_strip_z (Ψ := Work.Spaces.pthIter l Φ) (J := Set.Ioi b)
      isOpen_Ioi ?_ k z hgt θ
    intro z' hz' θ'
    exact pthIter_eq_zero_of_strip_z (Ψ := Φ) (J := Set.Ioi b) isOpen_Ioi
      (fun z'' hz'' θ'' => hsupp z'' θ'' (Or.inl (notMem_Icc_of_gt hz''))) l z' hz' θ'

theorem pthIter_eq_zero_of_z
    (hsupp : ∀ z θ, z ∉ Set.Icc a b ∨ θ ∉ Set.Icc c d → Φ z θ = 0)
    {z : ℝ} (hz : z ∉ Set.Icc a b) (k : ℕ) (θ : ℝ) :
    Work.Spaces.pthIter k Φ z θ = 0 :=
  pzIter_pthIter_eq_zero_of_z hsupp hz 0 k θ

theorem pzIter_pthIter_eq_zero_of_theta
    (hsupp : ∀ z θ, z ∉ Set.Icc a b ∨ θ ∉ Set.Icc c d → Φ z θ = 0)
    {θ : ℝ} (hθ : θ ∉ Set.Icc c d) (k l : ℕ) (z : ℝ) :
    Work.Spaces.pzIter k (Work.Spaces.pthIter l Φ) z θ = 0 := by
  have hθ' : θ < c ∨ d < θ := by
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hθ
    exact hθ
  rcases hθ' with hlt | hgt
  · refine pzIter_eq_zero_of_strip_θ (Ψ := Work.Spaces.pthIter l Φ) (J := Set.Iio c)
      isOpen_Iio ?_ k z θ hlt
    intro z' θ' hθ'
    exact pthIter_eq_zero_of_strip_θ (Ψ := Φ) (J := Set.Iio c) isOpen_Iio
      (fun z'' θ'' hθ'' => hsupp z'' θ'' (Or.inr (notMem_Icc_of_lt' hθ''))) l z' θ' hθ'
  · refine pzIter_eq_zero_of_strip_θ (Ψ := Work.Spaces.pthIter l Φ) (J := Set.Ioi d)
      isOpen_Ioi ?_ k z θ hgt
    intro z' θ' hθ'
    exact pthIter_eq_zero_of_strip_θ (Ψ := Φ) (J := Set.Ioi d) isOpen_Ioi
      (fun z'' θ'' hθ'' => hsupp z'' θ'' (Or.inr (notMem_Icc_of_gt' hθ''))) l z' θ' hθ'

theorem pthIter_eq_zero_of_theta
    (hsupp : ∀ z θ, z ∉ Set.Icc a b ∨ θ ∉ Set.Icc c d → Φ z θ = 0)
    {θ : ℝ} (hθ : θ ∉ Set.Icc c d) (k : ℕ) (z : ℝ) :
    Work.Spaces.pthIter k Φ z θ = 0 :=
  pzIter_pthIter_eq_zero_of_theta hsupp hθ 0 k z

end Support

/-! ## Clairaut on the open quadrant -/

theorem pz_pth_comm_qd {Φ : ℝ → ℝ → ℝ}
    (hsm : ContDiffOn ℝ 3 (Function.uncurry Φ) ftsQd)
    {z θ : ℝ} (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    Work.Spaces.pz (Work.Spaces.pth Φ) z θ = Work.Spaces.pth (Work.Spaces.pz Φ) z θ :=
  Work.Spaces.pz_pth_comm ((hsm.contDiffAt
    (isOpen_ftsQd.mem_nhds (show (z, θ) ∈ ftsQd from ⟨hz, hθ, hθ2⟩))).of_le (by norm_num))

end Work.FTS.EllipticEst.Dispatch
