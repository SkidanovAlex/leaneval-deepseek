import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Have
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.CurrySmooth
import Submission.Work.FTS.EllipticEst.weight_algebra_fts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Prop

open scoped ContDiff Real Topology
open Filter

set_option autoImplicit false

/-!
# `zFluxHasDerivAt`

The pointwise `z`-derivative of the radial flux integrand
`z' ↦ -(z' · D_z v(z',θ) · ∂_θ²v(z',θ) · w(z')² · sin(2θ)^q)`.

With `D z = D_z v(z,θ) = z ∂_z v(z,θ)`, `P z = ∂_θ²v(z,θ)` and the weight
`w(z) = (1+z)²/z²`, the product rule together with the one-dimensional identity
`(z w(z)²)' = w(z)² (z-3)/(1+z)` (`Work.FTS.EllipticEst.weight_algebra_fts`) gives

`(z D P w²)' = w² [ D·D_zP + D_zD·P + D·P·(z-3)/(1+z) ]`,

which is exactly the stated right-hand side.  The only analytic input is the
`z`-differentiability of the slices of `v`, `∂_z v` and `∂_θ²v` (hence the third
joint derivative in the hypothesis): `∂_θ²v` is only `C¹` jointly, so the generic
order-lowering lemmas `cdOn_pz_of`/`cdOn_pth_of` (`F` smooth on an open set ⇒ its
partials lose one order) are used to obtain joint `C¹` of `D_z v` and of `∂_θ²v`.
-/

/-! ## Order-lowering lemmas for the curried partial derivatives

The versions `Work.Spaces.contDiffOn_uncurry_pz`/`_pth` are stated for `⊤`-smoothness;
the following are the honest finite-order analogues used below. -/

/-- The `z`-partial of a `C^{m+1}` function on an open set is `C^m` there. -/
theorem cdOn_pz_of {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) {m n : ℕ}
    (hmn : m + 1 ≤ n) (h : ContDiffOn ℝ (n : ℕ∞ω) (Function.uncurry G) V) :
    ContDiffOn ℝ (m : ℕ∞ω) (Function.uncurry (Work.Spaces.pz G)) V := by
  have hn : ((n : ℕ) : ℕ∞ω) ≠ 0 := by
    have : n ≠ 0 := by omega
    exact_mod_cast this
  have hchain : ∀ p ∈ V, Work.Spaces.pz G p.1 p.2 = fderiv ℝ (Function.uncurry G) p (1, 0) := by
    intro p hp
    exact Work.Spaces.pz_eq_fderiv ((h.contDiffAt (hV.mem_nhds hp)).differentiableAt hn)
  have hfd : ContDiffOn ℝ (m : ℕ∞ω) (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) V := by
    have hcast : ((m + 1 : ℕ) : ℕ∞ω) ≤ ((n : ℕ) : ℕ∞ω) := by exact_mod_cast hmn
    have h' : ContDiffOn ℝ (m : ℕ∞ω) (fderivWithin ℝ (Function.uncurry G) V) V :=
      h.fderivWithin hV.uniqueDiffOn (by simpa using hcast)
    refine h'.congr ?_
    intro p hp
    rw [fderivWithin_of_isOpen hV hp]
  have hcomp : ContDiffOn ℝ (m : ℕ∞ω)
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (1, 0)) V := by
    simpa using hfd.clm_apply contDiffOn_const
  exact hcomp.congr hchain

/-- The `θ`-partial of a `C^{m+1}` function on an open set is `C^m` there. -/
theorem cdOn_pth_of {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) {m n : ℕ}
    (hmn : m + 1 ≤ n) (h : ContDiffOn ℝ (n : ℕ∞ω) (Function.uncurry G) V) :
    ContDiffOn ℝ (m : ℕ∞ω) (Function.uncurry (Work.Spaces.pth G)) V := by
  have hn : ((n : ℕ) : ℕ∞ω) ≠ 0 := by
    have : n ≠ 0 := by omega
    exact_mod_cast this
  have hchain : ∀ p ∈ V, Work.Spaces.pth G p.1 p.2 = fderiv ℝ (Function.uncurry G) p (0, 1) := by
    intro p hp
    exact Work.Spaces.pth_eq_fderiv ((h.contDiffAt (hV.mem_nhds hp)).differentiableAt hn)
  have hfd : ContDiffOn ℝ (m : ℕ∞ω) (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) V := by
    have hcast : ((m + 1 : ℕ) : ℕ∞ω) ≤ ((n : ℕ) : ℕ∞ω) := by exact_mod_cast hmn
    have h' : ContDiffOn ℝ (m : ℕ∞ω) (fderivWithin ℝ (Function.uncurry G) V) V :=
      h.fderivWithin hV.uniqueDiffOn (by simpa using hcast)
    refine h'.congr ?_
    intro p hp
    rw [fderivWithin_of_isOpen hV hp]
  have hcomp : ContDiffOn ℝ (m : ℕ∞ω)
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (0, 1)) V := by
    simpa using hfd.clm_apply contDiffOn_const
  exact hcomp.congr hchain

/-- The `θ`-partial of order `j` is `C^m` as soon as the function is `C^{m+j}`. -/
theorem cdOn_pthIter_of {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) :
    ∀ (j m n : ℕ), m + j ≤ n →
      ContDiffOn ℝ (n : ℕ∞ω) (Function.uncurry G) V →
      ContDiffOn ℝ (m : ℕ∞ω) (Function.uncurry (Work.Spaces.pthIter j G)) V := by
  intro j
  induction j with
  | zero =>
    intro m n hmn h
    have : m ≤ n := by omega
    simpa [Work.Spaces.pthIter] using h.of_le (by exact_mod_cast this)
  | succ j ih =>
    intro m n hmn h
    have h1 : ContDiffOn ℝ ((m + 1 : ℕ) : ℕ∞ω) (Function.uncurry (Work.Spaces.pthIter j G)) V :=
      ih (m + 1) n (by omega) h
    have h2 := cdOn_pth_of hV (m := m) (n := m + 1) (by omega) h1
    simpa [Work.Spaces.pthIter] using h2

/-- The `z`-slice derivative of a jointly `C¹` function is its `z`-partial. -/
theorem hasDerivAt_slice_one {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ContDiffOn ℝ 1 (Function.uncurry G) V) {z θ : ℝ} (hmem : (z, θ) ∈ V) :
    HasDerivAt (fun y : ℝ => G y θ) (Work.Spaces.pz G z θ) z := by
  have hd : DifferentiableAt ℝ (Function.uncurry G) (z, θ) :=
    (h.contDiffAt (hV.mem_nhds hmem)).differentiableAt (by norm_num)
  have hsl := Work.Spaces.differentiableAt_curry_left hd
  simpa only [Work.Spaces.pz] using hsl.hasDerivAt

/-- The derivative of the radial weight factor `z ↦ z·w(z)²`:
`(z w(z)²)' = w(z)² (z-3)/(1+z)`, the form in which the identity is used below. -/
theorem hasDerivAt_mul_w_sq {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun y : ℝ => y * (Work.Spaces.w y) ^ 2)
      ((Work.Spaces.w z) ^ 2 * ((z - 3) / (1 + z))) z := by
  have hw : ContDiffOn ℝ 1 (fun y : ℝ => Work.Spaces.w y) (Set.Ioi 0) := by
    show ContDiffOn ℝ 1 (fun y : ℝ => (1 + y) ^ 2 / y ^ 2) (Set.Ioi 0)
    exact ContDiffOn.div (by fun_prop) (by fun_prop)
      (fun y hy => pow_ne_zero 2 (ne_of_gt (show (0 : ℝ) < y from hy)))
  have hd : DifferentiableAt ℝ (fun y : ℝ => y * (Work.Spaces.w y) ^ 2) z :=
    differentiableAt_id.mul (((hw.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioi.mem_nhds hz)).pow 2)
  refine hd.hasDerivAt.congr_deriv ?_
  have h1 : deriv (fun y : ℝ => y * (Work.Spaces.w y) ^ 2) z
      = (z - 3) * (1 + z) ^ 3 / z ^ 4 :=
    Work.FTS.EllipticEst.weight_algebra_fts.2.2.2.1 z (ne_of_gt hz)
  rw [h1, show (Work.Spaces.w z) ^ 2 = (1 + z) ^ 4 / z ^ 4 from by
    simp only [Work.Spaces.w]
    field_simp]
  have hz0 : z ≠ 0 := ne_of_gt hz
  have h1z : (1 : ℝ) + z ≠ 0 := by linarith
  field_simp

theorem zFluxHasDerivAt (q : ℝ) (v : ℝ → ℝ → ℝ)
    (hv : ContDiffOn ℝ 3 (Function.uncurry v) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (fun z' : ℝ => -(z' * (Work.Spaces.Dz v z' θ) * (Work.Spaces.pth (Work.Spaces.pth v) z' θ)
        * (Work.Spaces.w z') ^ 2 * (Real.sin (2 * θ)) ^ q)) z
      = -(((Work.Spaces.Dz v z θ) * (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth v)) z θ)
            + (Work.Spaces.Dz (Work.Spaces.Dz v) z θ) * (Work.Spaces.pth (Work.Spaces.pth v) z θ)
            + (Work.Spaces.Dz v z θ) * (Work.Spaces.pth (Work.Spaces.pth v) z θ)
                * ((z - 3) / (1 + z)))
          * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ q) := by
  have hV : IsOpen (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) := isOpen_Ioi.prod isOpen_Ioo
  have hmem : (z, θ) ∈ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) := ⟨hz, hθ⟩
  have hpz2 : ContDiffOn ℝ (2 : ℕ∞ω) (Function.uncurry (Work.Spaces.pz v))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    cdOn_pz_of hV (m := 2) (n := 3) (by norm_num) hv
  have hDz1 : ContDiffOn ℝ (1 : ℕ∞ω) (Function.uncurry (Work.Spaces.Dz v))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have h1 : ContDiffOn ℝ (1 : ℕ∞ω) (fun p : ℝ × ℝ => p.1)
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) := contDiffOn_fst
    have h2 : ContDiffOn ℝ (1 : ℕ∞ω) (fun p : ℝ × ℝ => Work.Spaces.pz v p.1 p.2)
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) := hpz2.of_le (by norm_num)
    have hm := h1.mul h2
    have hfun : Function.uncurry (Work.Spaces.Dz v)
        = fun p : ℝ × ℝ => p.1 * Work.Spaces.pz v p.1 p.2 := by
      funext p
      rfl
    rw [hfun]
    exact hm
  have hpth2 : ContDiffOn ℝ (1 : ℕ∞ω) (Function.uncurry (Work.Spaces.pth (Work.Spaces.pth v)))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have h := cdOn_pthIter_of (V := Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) hV 2 1 3
      (by norm_num) hv
    simpa [Work.Spaces.pthIter] using h
  have hD : HasDerivAt (fun y : ℝ => Work.Spaces.Dz v y θ)
      (Work.Spaces.pz (Work.Spaces.Dz v) z θ) z := hasDerivAt_slice_one hV hDz1 hmem
  have hP : HasDerivAt (fun y : ℝ => Work.Spaces.pth (Work.Spaces.pth v) y θ)
      (Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.pth v)) z θ) z :=
    hasDerivAt_slice_one hV hpth2 hmem
  have hF : HasDerivAt (fun y : ℝ => y * (Work.Spaces.w y) ^ 2)
      ((Work.Spaces.w z) ^ 2 * ((z - 3) / (1 + z))) z := hasDerivAt_mul_w_sq hz
  have hG : HasDerivAt
      (fun y : ℝ => Work.Spaces.Dz v y θ * Work.Spaces.pth (Work.Spaces.pth v) y θ)
      (Work.Spaces.pz (Work.Spaces.Dz v) z θ * Work.Spaces.pth (Work.Spaces.pth v) z θ
        + Work.Spaces.Dz v z θ * Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.pth v)) z θ) z :=
    hD.mul hP
  have hFP : HasDerivAt
      (fun y : ℝ => (y * (Work.Spaces.w y) ^ 2)
        * (Work.Spaces.Dz v y θ * Work.Spaces.pth (Work.Spaces.pth v) y θ))
      (((Work.Spaces.w z) ^ 2 * ((z - 3) / (1 + z)))
          * (Work.Spaces.Dz v z θ * Work.Spaces.pth (Work.Spaces.pth v) z θ)
        + (z * (Work.Spaces.w z) ^ 2)
          * (Work.Spaces.pz (Work.Spaces.Dz v) z θ * Work.Spaces.pth (Work.Spaces.pth v) z θ
            + Work.Spaces.Dz v z θ * Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.pth v)) z θ)) z :=
    hF.mul hG
  have hfin : HasDerivAt
      (fun y : ℝ => -(((y * (Work.Spaces.w y) ^ 2)
        * (Work.Spaces.Dz v y θ * Work.Spaces.pth (Work.Spaces.pth v) y θ))
          * (Real.sin (2 * θ)) ^ q))
      (-((((Work.Spaces.w z) ^ 2 * ((z - 3) / (1 + z)))
          * (Work.Spaces.Dz v z θ * Work.Spaces.pth (Work.Spaces.pth v) z θ)
        + (z * (Work.Spaces.w z) ^ 2)
          * (Work.Spaces.pz (Work.Spaces.Dz v) z θ * Work.Spaces.pth (Work.Spaces.pth v) z θ
            + Work.Spaces.Dz v z θ * Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.pth v)) z θ))
          * (Real.sin (2 * θ)) ^ q)) z :=
    (hFP.mul_const ((Real.sin (2 * θ)) ^ q)).neg
  rw [show (fun z' : ℝ => -(z' * Work.Spaces.Dz v z' θ * Work.Spaces.pth (Work.Spaces.pth v) z' θ
        * (Work.Spaces.w z') ^ 2 * (Real.sin (2 * θ)) ^ q))
      = (fun z' : ℝ => -(((z' * (Work.Spaces.w z') ^ 2)
          * (Work.Spaces.Dz v z' θ * Work.Spaces.pth (Work.Spaces.pth v) z' θ))
            * (Real.sin (2 * θ)) ^ q)) from by funext z'; ring]
  rw [hfin.deriv]
  rw [show Work.Spaces.Dz (Work.Spaces.Dz v) z θ
        = z * Work.Spaces.pz (Work.Spaces.Dz v) z θ from rfl,
      show Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth v)) z θ
        = z * Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.pth v)) z θ from rfl]
  ring

end Work.FTS.EllipticEst.Prop
