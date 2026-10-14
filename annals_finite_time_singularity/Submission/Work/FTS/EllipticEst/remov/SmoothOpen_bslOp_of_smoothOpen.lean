import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_Bmom_div
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.bslOp_DzIter_eq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.TT

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.EllipticEst.Cert

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

/-! ## Preliminaries: derivative linearity, smoothness closure, `D_z`-linearity

The proof is the algebraic computation described in the docstring below:
`bslOp α Ψ = -α²D_z²Ψ - 5αD_zΨ + Lzero Ψ` on the open quadrant (the identity
`z²∂_zz = D_z² - D_z`), `Lzero` has `z`-independent coefficients and commutes with `D_z`
(only the commutation of `∂_θ` with `∂_z`, i.e. Clairaut, is needed, since the `z`
differentiation passes through the `θ`-derivatives and the `θ`-dependent factor `tan θ`),
and `D_z^j` is a linear differential operator, so it distributes over the combination
`-α²D_z² - 5αD_z + Lzero`. -/

/-- The `D_z`-form of the elliptic operator of (PolarBSL):
`bslOp α Ψ = -α²D_z²Ψ - 5αD_zΨ + Lzero Ψ`, valid on the open quadrant. -/
noncomputable def bslD (α : ℝ) (g : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => (-(α ^ 2)) * Work.Spaces.DzIter 2 g z θ + (-(5 * α)) * Work.Spaces.Dz g z θ
    + 1 * Work.Elliptic.Lzero g z θ

/-- Linearity of `deriv` for a three-term linear combination. -/
private theorem deriv_lin3 (A B C : ℝ → ℝ) (a b c : ℝ) {x : ℝ}
    (hA : DifferentiableAt ℝ A x) (hB : DifferentiableAt ℝ B x) (hC : DifferentiableAt ℝ C x) :
    deriv (fun y => a * A y + b * B y + c * C y) x
      = a * deriv A x + b * deriv B x + c * deriv C x := by
  have h1 : HasDerivAt (fun y => a * A y) (a * deriv A x) x := hA.hasDerivAt.const_mul a
  have h2 : HasDerivAt (fun y => b * B y) (b * deriv B x) x := hB.hasDerivAt.const_mul b
  have h3 : HasDerivAt (fun y => c * C y) (c * deriv C x) x := hC.hasDerivAt.const_mul c
  exact ((h1.add h2).add h3).deriv

/-- The `z`-slice of a function smooth on the open quadrant is differentiable at every
interior point. -/
private theorem diffAt_slice {f : ℝ → ℝ → ℝ} (hf : SmoothOpen f) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : DifferentiableAt ℝ (fun z' => f z' θ) z :=
  (hf.hasDerivAt_slice hθ hz).differentiableAt

/-- `SmoothOpen` is closed under multiplication by the `θ`-dependent factor `tan θ`. -/
private theorem SmoothOpen_tan_mul {g : ℝ → ℝ → ℝ} (hg : SmoothOpen g) :
    SmoothOpen (fun z θ => Real.tan θ * g z θ) :=
  smoothOpen_mul_bsl smoothOpen_tan_bsl hg

/-- `Lzero` preserves smoothness on the open quadrant:
`Lzero g = -∂_θθg + ∂_θ(tan θ · g) - 6g` and all coefficients are `z`-independent. -/
private theorem SmoothOpenLzero (g : ℝ → ℝ → ℝ) (hg : SmoothOpen g) :
    SmoothOpen (Work.Elliptic.Lzero g) := by
  have htan : SmoothOpen (fun z θ => Real.tan θ * g z θ) := SmoothOpen_tan_mul hg
  refine smoothOpen_congr_bsl ?_ (fun z θ _ _ _ => rfl)
  exact smoothOpen_sub_bsl
    (smoothOpen_add_bsl
      (smoothOpen_neg_bsl (smoothOpen_pthIter_bsl hg 2))
      (SmoothOpen.pth htan))
    (smoothOpen_const_mul_bsl 6 hg)

/-- Two functions agreeing on an open set have the same `D_z`-iterates there. -/
private theorem Dz_congr_of_isOpen {f f' : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : Set.EqOn (Function.uncurry f) (Function.uncurry f') V) (j : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DzIter j f))
      (Function.uncurry (Work.Spaces.DzIter j f')) V := by
  induction j with
  | zero => exact h
  | succ n ih =>
      intro y hy
      obtain ⟨z, θ⟩ := y
      show z * deriv (fun z' => Work.Spaces.DzIter n f z' θ) z
        = z * deriv (fun z' => Work.Spaces.DzIter n f' z' θ) z
      congr 1
      refine Filter.EventuallyEq.deriv_eq ?_
      filter_upwards [(Continuous.prodMk_left θ).continuousAt.eventually
        (hV.mem_nhds hy)] with z' hz'
      exact ih hz'

/-- Multiplication by an angular factor passes through `D_z` (the factor does not depend
on `z`); no differentiability is needed, `deriv` being totalised. -/
private theorem Dz_tan_mul (g : ℝ → ℝ → ℝ) :
    Work.Spaces.Dz (fun z θ => Real.tan θ * g z θ)
      = fun z θ => Real.tan θ * Work.Spaces.Dz g z θ := by
  funext z θ
  simp only [Work.Spaces.Dz, Work.Spaces.pz]
  rw [deriv_const_mul_field]
  ring

/-- `z² ∂_zzg = D_z²g - D_zg` in the form used below. -/
private theorem zsq_pzIter2_eq (g : ℝ → ℝ → ℝ) {z θ : ℝ}
    (h2 : DifferentiableAt ℝ (fun z' => Work.Spaces.pz g z' θ) z) :
    Work.Spaces.DzIter 2 g z θ = Work.Spaces.Dz g z θ + z ^ 2 * Work.Spaces.pzIter 2 g z θ := by
  have hd : deriv (fun z' => z' * Work.Spaces.pz g z' θ) z
      = Work.Spaces.pz g z θ + z * deriv (fun z' => Work.Spaces.pz g z' θ) z := by
    have hprod := (hasDerivAt_id z).mul h2.hasDerivAt
    have hfun : (id : ℝ → ℝ) * (fun z' => Work.Spaces.pz g z' θ)
        = fun z' => z' * Work.Spaces.pz g z' θ := by funext y; rfl
    rw [hfun] at hprod
    simpa using hprod.deriv
  show z * deriv (fun z' => z' * Work.Spaces.pz g z' θ) z
      = z * Work.Spaces.pz g z θ + z ^ 2 * deriv (fun z' => Work.Spaces.pz g z' θ) z
  rw [hd]; ring

/-! ## `∂_θ` commutes with `D_z` on the open quadrant, and so does `Lzero` -/

/-- One step of the commutation: `∂_θ (D_z g) = D_z (∂_θ g)` on the open quadrant. -/
private theorem pth_Dz_eqOn_step (g : ℝ → ℝ → ℝ) (hg : SmoothOpen g) :
    Set.EqOn (Function.uncurry (Work.Spaces.pth (Work.Spaces.Dz g)))
      (Function.uncurry (Work.Spaces.Dz (Work.Spaces.pth g))) Q0 := by
  intro p hp
  obtain ⟨z, θ⟩ := p
  obtain ⟨hz, hθ0, hθ1⟩ := mem_Q0.mp hp
  have h2 : ContDiffAt ℝ 2 (Function.uncurry g) (z, θ) :=
    ((smoothOpen_iff_forall g).mp hg 2).contDiffAt (isOpen_Q0.mem_nhds hp)
  have h1 : Work.Spaces.pth (Work.Spaces.Dz g) z θ
      = z * Work.Spaces.pth (Work.Spaces.pz g) z θ := by
    show deriv (fun θ' => z * Work.Spaces.pz g z θ') θ
      = z * deriv (fun θ' => Work.Spaces.pz g z θ') θ
    rw [deriv_const_mul_field]
  change Work.Spaces.pth (Work.Spaces.Dz g) z θ = Work.Spaces.Dz (Work.Spaces.pth g) z θ
  rw [h1, ← Work.Spaces.pz_pth_comm (f := g) h2]
  rfl

/-- `∂_θθ` commutes with `D_z` on the open quadrant (two steps of the previous lemma,
the second one applied to `∂_θ g`). -/
private theorem pthIter2_Dz_eqOn_step (g : ℝ → ℝ → ℝ) (hg : SmoothOpen g) :
    Set.EqOn (Function.uncurry (Work.Spaces.pthIter 2 (Work.Spaces.Dz g)))
      (Function.uncurry (Work.Spaces.Dz (Work.Spaces.pthIter 2 g))) Q0 := by
  intro p hp
  obtain ⟨z, θ⟩ := p
  have hstep2 : Work.Spaces.pth (Work.Spaces.Dz (Work.Spaces.pth g)) z θ
      = Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth g)) z θ :=
    pth_Dz_eqOn_step (Work.Spaces.pth g) (hg.pth) hp
  have hcongr : Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.Dz g)) z θ
      = Work.Spaces.pth (Work.Spaces.Dz (Work.Spaces.pth g)) z θ :=
    Work.Spaces.pth_congr_of_isOpen isOpen_Q0 (pth_Dz_eqOn_step g hg) hp
  have hfun : Work.Spaces.pthIter 2 (Work.Spaces.Dz g)
      = Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.Dz g)) := rfl
  have hfun2 : Work.Spaces.pthIter 2 g
      = Work.Spaces.pth (Work.Spaces.pth g) := rfl
  change Work.Spaces.pthIter 2 (Work.Spaces.Dz g) z θ
      = Work.Spaces.Dz (Work.Spaces.pthIter 2 g) z θ
  rw [hfun, hfun2, hcongr, hstep2]

/-- `Lzero` commutes with `D_z` on the open quadrant: `Lzero (D_z g) = D_z (Lzero g)`.
`Lzero` is `z`-independent, so this is the commutation of `∂_z` with `∂_θθ` and with
`∂_θ(tan θ ·)`, which follows from Clairaut. -/
private theorem Lzero_Dz_comm (g : ℝ → ℝ → ℝ) (hg : SmoothOpen g) :
    Set.EqOn (Function.uncurry (Work.Elliptic.Lzero (Work.Spaces.Dz g)))
      (Function.uncurry (Work.Spaces.Dz (Work.Elliptic.Lzero g))) Q0 := by
  intro p hp
  obtain ⟨z, θ⟩ := p
  obtain ⟨hz, hθ0, hθ1⟩ := mem_Q0.mp hp
  have hθI : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ0, hθ1⟩
  -- (A) the double angular derivative
  have hA : Work.Spaces.pthIter 2 (Work.Spaces.Dz g) z θ
      = Work.Spaces.Dz (Work.Spaces.pthIter 2 g) z θ :=
    pthIter2_Dz_eqOn_step g hg hp
  -- (B) `∂_θ(tan θ · D_z g) = D_z(∂_θ(tan θ · g))`: both sides are the single-step
  -- commutation applied to `tan θ · g`, since `tan θ` is independent of `z`.
  have hB : Work.Spaces.pth (fun z θ => Real.tan θ * Work.Spaces.Dz g z θ) z θ
      = Work.Spaces.Dz (Work.Spaces.pth (fun z θ => Real.tan θ * g z θ)) z θ := by
    have hDzd : Work.Spaces.Dz (fun z θ => Real.tan θ * g z θ)
        = fun z θ => Real.tan θ * Work.Spaces.Dz g z θ := Dz_tan_mul g
    have hstep : Work.Spaces.pth (Work.Spaces.Dz (fun z θ => Real.tan θ * g z θ)) z θ
        = Work.Spaces.Dz (Work.Spaces.pth (fun z θ => Real.tan θ * g z θ)) z θ :=
      pth_Dz_eqOn_step (fun z θ => Real.tan θ * g z θ) (SmoothOpen_tan_mul hg) hp
    rwa [hDzd] at hstep
  -- (C) the `z`-derivative of `Lzero g`, computed from its definition by linearity
  have hC : Work.Spaces.Dz (Work.Elliptic.Lzero g) z θ
      = -Work.Spaces.Dz (Work.Spaces.pthIter 2 g) z θ
        + Work.Spaces.Dz (Work.Spaces.pth (fun z θ => Real.tan θ * g z θ)) z θ
        - 6 * Work.Spaces.Dz g z θ := by
    simp only [Work.Spaces.Dz, Work.Spaces.pz]
    have hslice : (fun z' => Work.Elliptic.Lzero g z' θ)
        = fun z' => -Work.Spaces.pthIter 2 g z' θ
          + Work.Spaces.pth (fun z θ => Real.tan θ * g z θ) z' θ - 6 * g z' θ := by
      funext z'; rfl
    rw [hslice]
    rw [show (fun z' => -Work.Spaces.pthIter 2 g z' θ
            + Work.Spaces.pth (fun z θ => Real.tan θ * g z θ) z' θ - 6 * g z' θ)
        = (fun z' => (-1 : ℝ) * Work.Spaces.pthIter 2 g z' θ
            + 1 * Work.Spaces.pth (fun z θ => Real.tan θ * g z θ) z' θ
            + (-6) * g z' θ) from by funext z'; ring]
    rw [deriv_lin3 (fun z' => Work.Spaces.pthIter 2 g z' θ)
          (fun z' => Work.Spaces.pth (fun z θ => Real.tan θ * g z θ) z' θ)
          (fun z' => g z' θ) (-1) 1 (-6)
          (diffAt_slice (smoothOpen_pthIter_bsl hg 2) hz hθI)
          (diffAt_slice ((SmoothOpen_tan_mul hg).pth) hz hθI)
          (diffAt_slice hg hz hθI)]
    ring
  -- the `Lzero`-form of the two sides
  change Work.Elliptic.Lzero (Work.Spaces.Dz g) z θ
      = Work.Spaces.Dz (Work.Elliptic.Lzero g) z θ
  simp only [Work.Elliptic.Lzero, hA, hB]
  exact hC.symm

/-! ## The commutation of `bslOp α` with a single `D_z` -/

/-- `D_z` distributes over a three-term linear combination, as a function of `D_z` of the
three summands. -/
private theorem Dz_lin3 (A B C : ℝ → ℝ → ℝ) (a b c : ℝ) {z θ : ℝ}
    (hA : DifferentiableAt ℝ (fun z' => A z' θ) z)
    (hB : DifferentiableAt ℝ (fun z' => B z' θ) z)
    (hC : DifferentiableAt ℝ (fun z' => C z' θ) z) :
    Work.Spaces.Dz (fun z θ => a * A z θ + b * B z θ + c * C z θ) z θ
      = a * Work.Spaces.Dz A z θ + b * Work.Spaces.Dz B z θ + c * Work.Spaces.Dz C z θ := by
  simp only [Work.Spaces.Dz, Work.Spaces.pz]
  rw [deriv_lin3 (fun z' => A z' θ) (fun z' => B z' θ) (fun z' => C z' θ) a b c hA hB hC]
  ring

/-- The `D_z`-form of `bslOp α` on the open quadrant (`z²∂_zz = D_z² - D_z`). -/
private theorem bslOp_eq_bslD (α : ℝ) (g : ℝ → ℝ → ℝ) (hg : SmoothOpen g) :
    Set.EqOn (Function.uncurry (Work.Elliptic.bslOp α g))
      (Function.uncurry (bslD α g)) Q0 := by
  intro p hp
  obtain ⟨z, θ⟩ := p
  obtain ⟨hz, hθ0, hθ1⟩ := mem_Q0.mp hp
  have hθI : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hD2 : Work.Spaces.DzIter 2 g z θ
      = Work.Spaces.Dz g z θ + z ^ 2 * Work.Spaces.pzIter 2 g z θ :=
    zsq_pzIter2_eq g (diffAt_slice (hg.pz) hz hθI)
  change Work.Elliptic.bslOp α g z θ
      = (-(α ^ 2)) * Work.Spaces.DzIter 2 g z θ + (-(5 * α)) * Work.Spaces.Dz g z θ
        + 1 * Work.Elliptic.Lzero g z θ
  rw [Work.Elliptic.bslOp_apply, hD2,
    show Work.Spaces.Dz g z θ = z * Work.Spaces.pz g z θ from rfl]
  ring

/-- **`bslOp α` commutes with the single radial derivative `D_z`** on the open quadrant:
`bslOp α (D_z g) = D_z (bslOp α g)`. -/
private theorem bslOp_Dz_comm (α : ℝ) (g : ℝ → ℝ → ℝ) (hg : SmoothOpen g) :
    Set.EqOn (Function.uncurry (Work.Elliptic.bslOp α (Work.Spaces.Dz g)))
      (Function.uncurry (Work.Spaces.Dz (Work.Elliptic.bslOp α g))) Q0 := by
  intro p hp
  obtain ⟨z, θ⟩ := p
  obtain ⟨hz, hθ0, hθ1⟩ := mem_Q0.mp hp
  have hθI : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ0, hθ1⟩
  -- the inner commutation `bslOp α (D_z g) = D_z (bslOp α g)`
  have hinner : bslD α (Work.Spaces.Dz g) z θ
      = Work.Spaces.Dz (bslD α g) z θ := by
    change (-(α ^ 2)) * Work.Spaces.DzIter 2 (Work.Spaces.Dz g) z θ
        + (-(5 * α)) * Work.Spaces.Dz (Work.Spaces.Dz g) z θ
        + 1 * Work.Elliptic.Lzero (Work.Spaces.Dz g) z θ
      = Work.Spaces.Dz (fun z θ => (-(α ^ 2)) * Work.Spaces.DzIter 2 g z θ
        + (-(5 * α)) * Work.Spaces.Dz g z θ + 1 * Work.Elliptic.Lzero g z θ) z θ
    have hDzEq : Work.Spaces.DzIter 2 (Work.Spaces.Dz g)
        = Work.Spaces.Dz (Work.Spaces.DzIter 2 g) := rfl
    have hL : Work.Elliptic.Lzero (Work.Spaces.Dz g) z θ
        = Work.Spaces.Dz (Work.Elliptic.Lzero g) z θ := Lzero_Dz_comm g hg hp
    rw [hDzEq, hL]
    rw [Dz_lin3 (Work.Spaces.DzIter 2 g) (Work.Spaces.Dz g) (Work.Elliptic.Lzero g)
      (-(α ^ 2)) (-(5 * α)) 1
      (diffAt_slice (hg.DzIter 2) hz hθI) (diffAt_slice hg.Dz hz hθI)
      (diffAt_slice (SmoothOpenLzero g hg) hz hθI)]
  have hbsl : Work.Elliptic.bslOp α (Work.Spaces.Dz g) z θ = bslD α (Work.Spaces.Dz g) z θ :=
    bslOp_eq_bslD α (Work.Spaces.Dz g) (hg.Dz) hp
  change Work.Elliptic.bslOp α (Work.Spaces.Dz g) z θ
      = Work.Spaces.Dz (Work.Elliptic.bslOp α g) z θ
  rw [hbsl, hinner]
  exact (Dz_congr_of_isOpen isOpen_Q0 (bslOp_eq_bslD α g hg) 1 hp).symm

/-- **The elliptic equation commutes with the radial derivation `D_z = z∂_z`.**  Writing
`bslOp α Ψ = -α²D_z²Ψ - 5αD_zΨ + Lzero Ψ` (using `z²∂_zzΨ = D_z²Ψ - D_zΨ`) and noting that
`Lzero` (`= -∂_θθ + ∂_θ(tan θ ·) - 6`, with `z`-independent coefficients) commutes with `D_z`,
the operator `bslOp α` commutes with every power of `D_z` on the open quadrant.  Hence the
radially differentiated slices `D_z^jΨ` of a solution of `bslOp α Ψ = F` solve the same equation
with source `D_z^j F` — the paper's "the equation commutes with `D_R` derivatives" (§H2,
tex 950), which is what lets the estimates be applied to the slices. -/
theorem bslOp_DzIter_eq (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) (j : ℕ)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (heq : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 → Work.Elliptic.bslOp α Ψ z θ = F z θ) :
    ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 →
      Work.Elliptic.bslOp α (Work.Spaces.DzIter j Ψ) z θ = Work.Spaces.DzIter j F z θ := by
  have hSO : SmoothOpen Ψ := smoothOpen_of_forall hsm
  -- the equation holds on the open quadrant
  have hEqF : Set.EqOn (Function.uncurry (Work.Elliptic.bslOp α Ψ)) (Function.uncurry F) Q0 := by
    intro p hp
    obtain ⟨z, θ⟩ := p
    obtain ⟨hz, hθ0, hθ1⟩ := mem_Q0.mp hp
    exact heq z hz θ hθ0 hθ1
  -- `D_z^j` commutes with the whole operator
  have hkey : Set.EqOn (Function.uncurry (Work.Elliptic.bslOp α (Work.Spaces.DzIter j Ψ)))
      (Function.uncurry (Work.Spaces.DzIter j (Work.Elliptic.bslOp α Ψ))) Q0 := by
    induction j with
    | zero => intro p hp; rfl
    | succ j ih =>
        intro p hp
        obtain ⟨z, θ⟩ := p
        have hstep : Work.Elliptic.bslOp α (Work.Spaces.Dz (Work.Spaces.DzIter j Ψ)) z θ
            = Work.Spaces.Dz (Work.Elliptic.bslOp α (Work.Spaces.DzIter j Ψ)) z θ :=
          bslOp_Dz_comm α (Work.Spaces.DzIter j Ψ) (hSO.DzIter j) hp
        have hcongr : Work.Spaces.Dz (Work.Elliptic.bslOp α (Work.Spaces.DzIter j Ψ)) z θ
            = Work.Spaces.Dz (Work.Spaces.DzIter j (Work.Elliptic.bslOp α Ψ)) z θ :=
          Dz_congr_of_isOpen isOpen_Q0 ih 1 hp
        have hsucc : Work.Spaces.DzIter (j + 1) Ψ
            = Work.Spaces.Dz (Work.Spaces.DzIter j Ψ) := rfl
        have hsucc' : Work.Spaces.DzIter (j + 1) (Work.Elliptic.bslOp α Ψ)
            = Work.Spaces.Dz (Work.Spaces.DzIter j (Work.Elliptic.bslOp α Ψ)) := rfl
        change Work.Elliptic.bslOp α (Work.Spaces.DzIter (j + 1) Ψ) z θ
            = Work.Spaces.DzIter (j + 1) (Work.Elliptic.bslOp α Ψ) z θ
        rw [hsucc, hsucc', hstep, hcongr]
  intro z hz θ hθ0 hθ1
  have hp : (z, θ) ∈ Q0 := mem_Q0.mpr ⟨hz, hθ0, hθ1⟩
  have h1 : Work.Elliptic.bslOp α (Work.Spaces.DzIter j Ψ) z θ
      = Work.Spaces.DzIter j (Work.Elliptic.bslOp α Ψ) z θ := hkey hp
  have h2 : Work.Spaces.DzIter j (Work.Elliptic.bslOp α Ψ) z θ = Work.Spaces.DzIter j F z θ :=
    Dz_congr_of_isOpen isOpen_Q0 hEqF j hp
  rw [h1, h2]

end Work.FTS.EllipticEst.TT
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov

open scoped Real Topology

set_option autoImplicit false

/-- **`bslOp α Ψ` is `C^∞` on the open quadrant as soon as `Ψ` is.**

This is the *open-quadrant* version of `Work.FTS.EllipticEst.Cert.SmoothOpen_bslOp`, whose
hypothesis `Work.Spaces.SmoothNbhd Ψ` (analyticity on a neighbourhood of the closed quadrant)
is far too strong for the weak classes, where only `ContDiffOn ℝ n (uncurry Ψ) Q0` is
available.

The proof is the same algebraic bookkeeping: `bslOp α Ψ` is built from `Ψ` and its partials
`∂_z²Ψ`, `∂_zΨ`, `∂_θ²Ψ`, `∂_θ(tan θ·Ψ)` — all `SmoothOpen` by `SmoothOpen.pzIter`,
`SmoothOpen.pz`, `Cert.smoothOpen_pthIter_bsl` and `SmoothOpen.pth` — together with the
`C^∞` factors `z²`, `z`, `tan θ` (`tan` is smooth on `Q0` because `cos θ ≠ 0` there), using
the closure properties `Cert.smoothOpen_{add,sub,neg,const_mul,mul,congr}_bsl`. -/
theorem SmoothOpen_bslOp_of_smoothOpen {α : ℝ} {Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.bslOp α Ψ) := by
  have hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ := h
  have hzsq : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => z ^ 2) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_zsq_bsl
  have hz : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => z) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_z_bsl
  have htan : Work.FTS.EllipticEst.SmoothOpen (fun _ : ℝ => Real.tan) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_tan_bsl
  -- the second-order term `-α²z²·∂_z²Ψ`
  have hA : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => -(α ^ 2 * z ^ 2) * Work.Spaces.pzIter 2 Ψ z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
      (Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl (-(α ^ 2))
        (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl hzsq
          (Work.FTS.EllipticEst.SmoothOpen.pzIter hΨso 2)))
      (fun z θ _ _ _ => by ring)
  -- the first-order term `-α(5+α)z·∂_zΨ`
  have hB : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (α * (5 + α) * z) * Work.Spaces.pz Ψ z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
      (Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl (α * (5 + α))
        (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl hz
          (Work.FTS.EllipticEst.SmoothOpen.pz hΨso)))
      (fun z θ _ _ _ => by ring)
  -- the angular operator `Lzero Ψ = -∂_θ²Ψ + ∂_θ(tan θ·Ψ) - 6Ψ`
  have htΨ : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Real.tan θ * Ψ z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl htan hΨso
  have hC : Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.Lzero Ψ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
      (Work.FTS.EllipticEst.Cert.smoothOpen_sub_bsl
        (Work.FTS.EllipticEst.Cert.smoothOpen_add_bsl
          (Work.FTS.EllipticEst.Cert.smoothOpen_neg_bsl
            (Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl hΨso 2))
          (Work.FTS.EllipticEst.SmoothOpen.pth htΨ))
        (Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl 6 hΨso))
      (fun z θ _ _ _ => by simp only [Work.Elliptic.Lzero])
  -- assembly
  exact Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
    (Work.FTS.EllipticEst.Cert.smoothOpen_add_bsl
      (Work.FTS.EllipticEst.Cert.smoothOpen_sub_bsl hA hB) hC)
    (fun z θ _ _ _ => by simp only [Work.Elliptic.bslOp_apply])

end Work.FTS.EllipticEst.remov
end
