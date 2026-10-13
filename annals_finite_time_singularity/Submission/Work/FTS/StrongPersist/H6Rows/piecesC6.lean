/-
# `Work.FTS.StrongPersist.H6Rows.piecesC6` — the `C^6` regularity of the two nonlinear pieces

The two nonlinear pieces of the modulation right-hand side, `N₀` and `N`
(`Work.Construction.N0`, `Work.Construction.N`), are `C^6` on the **open** quadrant
`Q0 = (0,∞) × (0,π/2)` for every datum of the level-six coercivity context `L6Ctx`.

This is the *regularity* half of the level-six rows `row_N0_pair`/`row_N_pair` of
`Submission/Work/FTS/StrongPersist/H6Pair6Aux/`: the rows consume it to make the
`HkMem α 6`-honesty of `N₀`, `N` and of the pairing slots meaningful.

## The mathematics

`N₀` is a sum of six products of the angular factors `sin 2θ`, `c2m θ`, the radial factors
`z ↦ L₁₂(F_*)(z)`, `z ↦ L₁₂(f)(z)` and the fields `f`, `∂_θf`, `D_zf`, so its regularity is
the `C^6`-instance of the *proved* `H6Pair6Aux.SmoothN0` (which gives `C^∞` from `C^∞` data;
here `L₁₂(f)` is `C^∞` on `(0,∞)` because the perturbation residual `𝒱(Φ̃_g)` is smooth —
`NonlinRows.smoothOpen_L12_radial`).

For `N` the structural facts are

* the splitting `Φ̃ = Φ̃_* + Φ̃_g`, `F = F_* + f`, `Φ = Φ_s + E f` of the elliptic context
  (`Ell6Ctx.hsum`), together with the **linearity** of `ℛ`, `𝒰`, `𝒱` and the additivity of
  `L₁₂` (`L3Rhs.L3RhsL12add`) and of the angular moment `FK` (`L3Rhs.L3RhsFKadd`);
* the angular moment is `C^6`: `FK = 3·F_*(·)` (`NfkAux.fk_eq_three_Fstar`), and `F_*(f)` is
  `C^6` on `(0,∞)` for `HkMem α 7 f` (`UopHk.contDiffOn_Fstar_of_smoothOpen_Hk`), while
  `FK(F_*) = α·2z/(1+z)²` is explicit (`Nonlinear.FstarPkg.FK_Fstar`).

## Layout

The file proves the local `C^6`-closure API (`CO6`), the `SmoothOpen`-closure of `𝒰`, `𝒱` and
of `Φ̃` (local copies, the tree's versions being private), the `C^6`-regularity of the two
`FK`-terms, and finally both conjuncts of the target.

Everything is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.EllipticEst.UopHk.L12_contDiffOn_reg
import Submission.Work.FTS.StrongPersist.H6Rows.RowAux
import Submission.Work.FTS.NonlinRows.NRow1_7Aux
import Submission.Work.FTS.NonlinRows.smoothOpen_radA
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.SmoothN0
import Submission.Work.FTS.StrongPersist.L3Rhs.L3RhsFKadd
import Submission.Work.FTS.StrongPersist.L3Rhs.L3RhsL12add
import Submission.Work.FTS.StrongPersist.L3Rhs.NfkAux.Basic
import Submission.Work.FTS.Nonlinear.FstarPkg.FK_Fstar

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.StrongPersist.H6Pair6Aux
  (so_add so_sub so_mul so_const_mul so_radial so_snd contDiff_s2 smoothOpen_Fstar
    smoothOpen_L12_Fstar)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## A local `C^6`-closure API

`CO6 f` is `C^6`-smoothness of the uncurried `f` on the open quadrant.  The combinators are
the order-six instances of the `SmoothOpen`-combinators of `H6Pair6Aux/SmoothN0`;
`co6_radial` promotes a radial function. -/

/-- `C^6` on the open quadrant. -/
abbrev CO6 (f : Fn) : Prop := ContDiffOn ℝ 6 (Function.uncurry f) Work.FTS.EllipticEst.Q0

theorem co6_add {f g : Fn} (hf : CO6 f) (hg : CO6 g) : CO6 (fun z θ => f z θ + g z θ) := by
  change ContDiffOn ℝ 6 (Function.uncurry (fun z θ => f z θ + g z θ)) Work.FTS.EllipticEst.Q0
  have h : Function.uncurry (fun z θ => f z θ + g z θ)
      = Function.uncurry f + Function.uncurry g := by
    funext p; obtain ⟨z, θ⟩ := p; rfl
  rw [h]; exact hf.add hg

theorem co6_sub {f g : Fn} (hf : CO6 f) (hg : CO6 g) : CO6 (fun z θ => f z θ - g z θ) := by
  change ContDiffOn ℝ 6 (Function.uncurry (fun z θ => f z θ - g z θ)) Work.FTS.EllipticEst.Q0
  have h : Function.uncurry (fun z θ => f z θ - g z θ)
      = Function.uncurry f - Function.uncurry g := by
    funext p; obtain ⟨z, θ⟩ := p; rfl
  rw [h]; exact hf.sub hg

theorem co6_mul {f g : Fn} (hf : CO6 f) (hg : CO6 g) : CO6 (fun z θ => f z θ * g z θ) := by
  change ContDiffOn ℝ 6 (Function.uncurry (fun z θ => f z θ * g z θ)) Work.FTS.EllipticEst.Q0
  have h : Function.uncurry (fun z θ => f z θ * g z θ)
      = Function.uncurry f * Function.uncurry g := by
    funext p; obtain ⟨z, θ⟩ := p; rfl
  rw [h]; exact hf.mul hg

theorem co6_const_mul (c : ℝ) {f : Fn} (hf : CO6 f) : CO6 (fun z θ => c * f z θ) := by
  change ContDiffOn ℝ 6 (Function.uncurry (fun z θ => c * f z θ)) Work.FTS.EllipticEst.Q0
  have h : Function.uncurry (fun z θ => c * f z θ)
      = fun p : ℝ × ℝ => c * Function.uncurry f p := rfl
  rw [h]; exact (contDiffOn_const (c := c)).mul hf

/-- A radial function `C^6` on `(0,∞)` is `C^6` on the open quadrant. -/
theorem co6_radial {r : ℝ → ℝ} (h : ContDiffOn ℝ 6 r (Set.Ioi 0)) :
    CO6 (fun z (_ : ℝ) => r z) := by
  change ContDiffOn ℝ 6 (fun p : ℝ × ℝ => r p.1) Work.FTS.EllipticEst.Q0
  exact h.comp contDiffOn_fst (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).1)

theorem co6_of_smoothOpen {f : Fn} (h : Work.FTS.EllipticEst.SmoothOpen f) : CO6 f :=
  h.forall 6

/-- `SmoothOpen` is a pointwise property on the open quadrant: two functions agreeing there
are smooth together.  (Stated in this orientation so that it composes with `ContDiffOn.congr`,
which replaces the *second* function.) -/
theorem so_congr {f g : Fn} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (h : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → g z θ = f z θ) :
    Work.FTS.EllipticEst.SmoothOpen g := by
  unfold Work.FTS.EllipticEst.SmoothOpen at hf ⊢
  refine hf.congr (fun p hp => ?_)
  obtain ⟨z, θ⟩ := p
  exact h z θ (Work.FTS.EllipticEst.mem_Q0.mp hp).1 (Work.FTS.EllipticEst.mem_Q0.mp hp).2.1
    (Work.FTS.EllipticEst.mem_Q0.mp hp).2.2

/-! ## `SmoothOpen`-closure of `𝒰`, `𝒱` and `Φ̃`

`𝒰` and `𝒱` are linear combinations of the identity and the two first-order operators with
smooth coefficients, and `Φ̃ = Φ - (1/(4α)) sin 2θ · L₁₂(F)` is a difference of a `C^∞`
function and an angular factor times a radial one.  (`smoothOpen_Rop` for `ℛ` is already in
the tree, `NonlinRows.smoothOpen_Rop`.) -/

/-- The radius `(z,θ) ↦ z` is `C^∞` on the quadrant. -/
theorem h6rows_so_Z : Work.FTS.EllipticEst.SmoothOpen (fun z (_ : ℝ) => z) :=
  so_radial (r := fun z => z) (fun _ => contDiffOn_id)

/-- `sin²θ` is `C^∞` on the quadrant. -/
theorem h6rows_so_sinsq :
    Work.FTS.EllipticEst.SmoothOpen (fun (_ : ℝ) (θ : ℝ) => Real.sin θ ^ 2) := by
  have hsin : ContDiff ℝ Work.Stability.smoothOrder (fun θ : ℝ => Real.sin θ) :=
    Real.contDiff_sin.comp contDiff_id
  exact so_snd (hsin.pow 2)

/-- `tan θ = sin θ / cos θ` is `C^∞` on the quadrant (`cos θ > 0` there). -/
theorem h6rows_so_tan : Work.FTS.EllipticEst.SmoothOpen (fun (_ : ℝ) (θ : ℝ) => Real.tan θ) := by
  have hsin : Work.FTS.EllipticEst.SmoothOpen (fun (_ : ℝ) (θ : ℝ) => Real.sin θ) :=
    so_snd Real.contDiff_sin
  have hcos : Work.FTS.EllipticEst.SmoothOpen (fun (_ : ℝ) (θ : ℝ) => Real.cos θ) :=
    so_snd Real.contDiff_cos
  have key : (fun (_ : ℝ) (θ : ℝ) => Real.sin θ / Real.cos θ)
      = (fun (_ : ℝ) (θ : ℝ) => Real.tan θ) := by
    funext z θ; exact (Real.tan_eq_sin_div_cos θ).symm
  rw [← key]
  exact hsin.div hcos (fun p hp => by
    obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ1⟩))

/-- `𝒰(Ψ) = -3Ψ - α z ∂_zΨ` preserves `C^∞`. -/
theorem h6rows_so_Uop {α : ℝ} {Ψ : Fn} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Uop α Ψ) := by
  have h1 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => -3 * Ψ z θ) := so_const_mul (-3) hΨ
  have h2a : Work.FTS.EllipticEst.SmoothOpen (fun z (_ : ℝ) => α * z) :=
    so_const_mul α h6rows_so_Z
  have h2 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => α * z * Work.Spaces.pz Ψ z θ) :=
    so_mul (f := fun z (_ : ℝ) => α * z) (g := fun z θ => Work.Spaces.pz Ψ z θ) h2a hΨ.pz
  have hfin : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => -3 * Ψ z θ - α * z * Work.Spaces.pz Ψ z θ) := so_sub h1 h2
  unfold Work.Construction.Uop
  exact hfin

/-- `𝒱(Ψ) = ∂_θΨ - tan θ · Ψ` preserves `C^∞`. -/
theorem h6rows_so_Vop {Ψ : Fn} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Vop Ψ) := by
  have h2 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Real.tan θ * Ψ z θ) :=
    so_mul (f := fun (_ : ℝ) (θ : ℝ) => Real.tan θ) (g := Ψ) h6rows_so_tan hΨ
  have hfin : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Spaces.pth Ψ z θ - Real.tan θ * Ψ z θ) := so_sub hΨ.pth h2
  unfold Work.Construction.Vop
  exact hfin

/-- `Φ̃ = Φ - (1/(4α)) sin 2θ · L₁₂(F)` is `C^∞` for `C^∞` data. -/
theorem h6rows_so_PhiTil {α : ℝ} {F Φ : Fn} (hΦ : Work.FTS.EllipticEst.SmoothOpen Φ)
    (hL : Work.FTS.EllipticEst.SmoothOpen (fun z (_ : ℝ) => Work.Construction.L12 F z)) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Construction.PhiTil α F Φ) := by
  have hTheta : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (1 / (4 * α)) * Work.Construction.s2 θ * Work.Construction.L12 F z) :=
    so_mul (f := fun z θ => (1 / (4 * α)) * Work.Construction.s2 θ)
      (g := fun z (_ : ℝ) => Work.Construction.L12 F z)
      (so_const_mul (1 / (4 * α)) (so_snd contDiff_s2)) hL
  have hsub : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Φ z θ - (1 / (4 * α)) * Work.Construction.s2 θ * Work.Construction.L12 F z) :=
    so_sub hΦ hTheta
  have key : (fun z θ =>
        Φ z θ - (1 / (4 * α)) * Work.Construction.s2 θ * Work.Construction.L12 F z)
      = Work.Construction.PhiTil α F Φ := by
    funext z θ
    simp only [Work.Construction.PhiTil, Work.Construction.Theta]
  rw [← key]
  exact hsub

/-! ## The angular moment `FK` at order six -/

/-- **`z ↦ FK f z` is `C^6` on `(0,∞)`** for `SmoothOpen f` + `HkMem α 7 f`: `FK f = 3·F_*(f)`
and the elliptic angular moment `F_*(f)` is `C^6` as soon as `f` is honest in `ℋ⁷`. -/
theorem co6_FK_radial {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : Fn}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem7 : Work.Spaces.HkMem α 7 f) :
    CO6 (fun z (_ : ℝ) => Work.Construction.FK f z) := by
  have h := Work.FTS.EllipticEst.UopHk.contDiffOn_Fstar_of_smoothOpen_Hk α 7 f hsm hmem7
    (by norm_num)
  have h3 : ContDiffOn ℝ 6 (fun z : ℝ => 3 * Work.Elliptic.Fstar f z) (Set.Ioi 0) :=
    (h.const_smul (3 : ℝ)).of_le (by decide)
  have hrad : CO6 (fun z (_ : ℝ) => 3 * Work.Elliptic.Fstar f z) := co6_radial h3
  refine hrad.congr (fun p hp => ?_)
  obtain ⟨z, θ⟩ := p
  simp only [Function.uncurry]
  exact congrFun (Work.FTS.StrongPersist.L3Rhs.NfkAux.fk_eq_three_Fstar f) z

/-- **The angular moment of the *full* profile is `C^6`**: `FK(F_* + f) = FK(F_*) + FK(f)` on
`z > 0` (`L3Rhs.L3RhsFKadd`), the two summands being `C^6` by
`Nonlinear.FstarPkg.FK_Fstar` (`FK(F_*) = α·2z/(1+z)²`) and `co6_FK_radial`. -/
theorem co6_FK_Ftot {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : Fn}
    (hadm : Work.FTS.StrongPersist.H6Adm α f) (hmem7 : Work.Spaces.HkMem α 7 f) :
    CO6 (fun z (_ : ℝ) => Work.Construction.FK (Work.Construction.Ftot α f) z) := by
  have hf : Work.FTS.EllipticEst.SmoothOpen f := hadm.reg.1
  have hFstar : ContDiffOn ℝ 6
      (fun z : ℝ => Work.Construction.FK (Work.Construction.Fstar α) z) (Set.Ioi 0) := by
    have hR : ContDiffOn ℝ 6 (fun z : ℝ => α * (2 * z / (1 + z) ^ 2)) (Set.Ioi 0) := by
      refine contDiffOn_const.mul ?_
      exact (contDiffOn_const.mul contDiffOn_id).div ((contDiffOn_const.add contDiffOn_id).pow 2)
        (fun z hz => pow_ne_zero 2 (ne_of_gt (by linarith [Set.mem_Ioi.mp hz] : (0 : ℝ) < 1 + z)))
    exact hR.congr (fun z hz => Work.FTS.Nonlinear.FstarPkg.FK_Fstar hα hα1)
  have hsum : CO6 (fun z θ => Work.Construction.FK (Work.Construction.Fstar α) z
      + Work.Construction.FK f z) :=
    co6_add (f := fun z (_ : ℝ) => Work.Construction.FK (Work.Construction.Fstar α) z)
      (g := fun z (_ : ℝ) => Work.Construction.FK f z)
      (co6_radial hFstar) (co6_FK_radial hα hα1 hf hmem7)
  refine hsum.congr (fun p hp => ?_)
  obtain ⟨z, θ⟩ := p
  simp only [Function.uncurry]
  exact Work.FTS.StrongPersist.L3Rhs.L3RhsFKadd α ⟨hα, hα1⟩ f hadm z
    (Work.FTS.EllipticEst.mem_Q0.mp hp).1

/-! ## The target -/

theorem piecesC6 (Ce : ℝ) : ∃ α₂ : ℝ, 0 < α₂ ∧ α₂ ≤ 1 ∧
    ∀ α ∈ Set.Ioc 0 α₂, ∀ (g Φ : Work.FTS.Galerkin.Fam) (τ M Cs : ℝ)
      (E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn) (Φs : Work.FTS.Galerkin.Fn),
      0 ≤ τ →
      Work.FTS.StrongPersist.L6Ctx (Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1)
        α M Ce Cs E Φs g Φ τ →
      ContDiffOn ℝ 6 (Function.uncurry
          (Work.Construction.N0 α (Work.Construction.Ftau α g τ)
            (Work.FTS.Galerkin.slice g τ))) Work.FTS.EllipticEst.Q0 ∧
      ContDiffOn ℝ 6 (Function.uncurry
          (Work.Construction.N α (Work.Construction.Ftau α g τ)
            (Work.FTS.Galerkin.slice Φ τ))) Work.FTS.EllipticEst.Q0 := by
  refine ⟨1, one_pos, le_rfl, ?_⟩
  intro α hαIoc g Φ τ M Cs E Φs hτ hL
  obtain ⟨hα, hα1⟩ := Set.mem_Ioc.mp hαIoc
  -- the slice of `g` and the radial function `L₁₂` of it
  have hf : Work.FTS.EllipticEst.SmoothOpen (slice g τ) := hL.hreg.reg.1
  have hL12f : Work.FTS.EllipticEst.SmoothOpen
      (fun z (_ : ℝ) => Work.Construction.L12 (slice g τ) z) :=
    Work.FTS.NonlinRows.smoothOpen_L12_radial hα hL.hell.hgo.smooth hL.hell.hgo.V.1.1
  -- the slice of `Φ`
  have hΨ : Work.FTS.EllipticEst.SmoothOpen (slice Φ τ) := by
    have h' : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => Φs z θ + E (slice g τ) z θ) :=
      so_add hL.hell.hstar.smooth hL.hell.hgo.smooth
    rw [hL.hell.hsum]
    exact h'
  constructor
  · -- the `N₀`-piece
    exact (Work.FTS.StrongPersist.H6Pair6Aux.SmoothN0 hα hf hL12f).forall 6
  · -- the `N`-piece
    -- `L₁₂` of the full profile: additivity across `F_* + f`
    have hL12F : Work.FTS.EllipticEst.SmoothOpen
        (fun z (_ : ℝ) => Work.Construction.L12 (Work.Construction.Ftot α (slice g τ)) z) := by
      have hsum : Work.FTS.EllipticEst.SmoothOpen
          (fun z θ => Work.Construction.L12 (Work.Construction.Fstar α) z
            + Work.Construction.L12 (slice g τ) z) :=
        so_add (f := fun z (_ : ℝ) => Work.Construction.L12 (Work.Construction.Fstar α) z)
          (g := fun z (_ : ℝ) => Work.Construction.L12 (slice g τ) z)
          (smoothOpen_L12_Fstar α) hL12f
      refine so_congr hsum (fun z θ hz hθ hθ' => ?_)
      exact Work.FTS.StrongPersist.L3Rhs.L3RhsL12add α ⟨hα, hα1⟩ (slice g τ) hL.hreg z hz
    have hF : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Ftau α g τ) := by
      unfold Work.Construction.Ftau
      exact so_add (smoothOpen_Fstar α) hf
    have hΞ : Work.FTS.EllipticEst.SmoothOpen
        (Work.Construction.PhiTil α (Work.Construction.Ftau α g τ) (slice Φ τ)) :=
      h6rows_so_PhiTil hΨ hL12F
    -- the five summands of `N`
    have hRop : CO6 (Work.Construction.Rop α
        (Work.Construction.PhiTil α (Work.Construction.Ftau α g τ) (slice Φ τ))) :=
      co6_of_smoothOpen (Work.FTS.NonlinRows.smoothOpen_Rop hΞ)
    have hUop : CO6 (Work.Construction.Uop α
        (Work.Construction.PhiTil α (Work.Construction.Ftau α g τ) (slice Φ τ))) :=
      co6_of_smoothOpen (h6rows_so_Uop hΞ)
    have hVop : CO6 (Work.Construction.Vop
        (Work.Construction.PhiTil α (Work.Construction.Ftau α g τ) (slice Φ τ))) :=
      co6_of_smoothOpen (h6rows_so_Vop hΞ)
    have hFc : CO6 (Work.Construction.Ftau α g τ) := co6_of_smoothOpen hF
    have hpthF : CO6 (Work.Spaces.pth (Work.Construction.Ftau α g τ)) :=
      co6_of_smoothOpen hF.pth
    have hDzF : CO6 (Work.Spaces.Dz (Work.Construction.Ftau α g τ)) :=
      co6_of_smoothOpen hF.Dz
    have hFK : CO6 (fun z (_ : ℝ) => Work.Construction.FK (Work.Construction.Ftau α g τ) z) :=
      co6_FK_Ftot hα hα1 hL.hreg hL.h7
    have hs2 : CO6 (fun z θ => (1 / 2) * Work.Construction.s2 θ) :=
      co6_const_mul (1 / 2) (co6_of_smoothOpen (so_snd contDiff_s2))
    have hsinsq : CO6 (fun (_ : ℝ) (θ : ℝ) => Real.sin θ ^ 2) :=
      co6_of_smoothOpen h6rows_so_sinsq
    -- assemble the five summands in the association of the definition of `N`
    have hT1 : CO6 (fun z θ => 2 * Work.Construction.Rop α
        (Work.Construction.PhiTil α (Work.Construction.Ftau α g τ) (slice Φ τ)) z θ
          * Work.Construction.Ftau α g τ z θ) :=
      co6_mul (co6_const_mul 2 hRop) hFc
    have hT2 : CO6 (fun z θ => 2 * Work.Construction.Uop α
        (Work.Construction.PhiTil α (Work.Construction.Ftau α g τ) (slice Φ τ)) z θ
          * Work.Spaces.pth (Work.Construction.Ftau α g τ) z θ) :=
      co6_mul (co6_const_mul 2 hUop) hpthF
    have hS2 : CO6 (fun z θ => 2 * Work.Construction.Rop α
        (Work.Construction.PhiTil α (Work.Construction.Ftau α g τ) (slice Φ τ)) z θ
          * Work.Construction.Ftau α g τ z θ
        - 2 * Work.Construction.Uop α
        (Work.Construction.PhiTil α (Work.Construction.Ftau α g τ) (slice Φ τ)) z θ
          * Work.Spaces.pth (Work.Construction.Ftau α g τ) z θ) :=
      co6_sub hT1 hT2
    have hT3 : CO6 (fun z θ => 2 * α * Work.Construction.Vop
        (Work.Construction.PhiTil α (Work.Construction.Ftau α g τ) (slice Φ τ)) z θ
          * Work.Spaces.Dz (Work.Construction.Ftau α g τ) z θ) :=
      co6_mul (co6_const_mul (2 * α) hVop) hDzF
    have hS3 : CO6 (fun z θ => 2 * Work.Construction.Rop α
        (Work.Construction.PhiTil α (Work.Construction.Ftau α g τ) (slice Φ τ)) z θ
          * Work.Construction.Ftau α g τ z θ
        - 2 * Work.Construction.Uop α
        (Work.Construction.PhiTil α (Work.Construction.Ftau α g τ) (slice Φ τ)) z θ
          * Work.Spaces.pth (Work.Construction.Ftau α g τ) z θ
        - 2 * α * Work.Construction.Vop
        (Work.Construction.PhiTil α (Work.Construction.Ftau α g τ) (slice Φ τ)) z θ
          * Work.Spaces.Dz (Work.Construction.Ftau α g τ) z θ) :=
      co6_sub hS2 hT3
    have hT4 : CO6 (fun z θ => (1 / 2) * Work.Construction.s2 θ
        * Work.Construction.FK (Work.Construction.Ftau α g τ) z
          * Work.Spaces.pth (Work.Construction.Ftau α g τ) z θ) :=
      co6_mul (co6_mul hs2 hFK) hpthF
    have hS4 : CO6 (fun z θ => 2 * Work.Construction.Rop α
        (Work.Construction.PhiTil α (Work.Construction.Ftau α g τ) (slice Φ τ)) z θ
          * Work.Construction.Ftau α g τ z θ
        - 2 * Work.Construction.Uop α
        (Work.Construction.PhiTil α (Work.Construction.Ftau α g τ) (slice Φ τ)) z θ
          * Work.Spaces.pth (Work.Construction.Ftau α g τ) z θ
        - 2 * α * Work.Construction.Vop
        (Work.Construction.PhiTil α (Work.Construction.Ftau α g τ) (slice Φ τ)) z θ
          * Work.Spaces.Dz (Work.Construction.Ftau α g τ) z θ
        - (1 / 2) * Work.Construction.s2 θ
        * Work.Construction.FK (Work.Construction.Ftau α g τ) z
          * Work.Spaces.pth (Work.Construction.Ftau α g τ) z θ) :=
      co6_sub hS3 hT4
    have hT5 : CO6 (fun z θ => Real.sin θ ^ 2
        * Work.Construction.FK (Work.Construction.Ftau α g τ) z
          * Work.Construction.Ftau α g τ z θ) :=
      co6_mul (co6_mul hsinsq hFK) hFc
    have hS5 : CO6 (fun z θ => 2 * Work.Construction.Rop α
        (Work.Construction.PhiTil α (Work.Construction.Ftau α g τ) (slice Φ τ)) z θ
          * Work.Construction.Ftau α g τ z θ
        - 2 * Work.Construction.Uop α
        (Work.Construction.PhiTil α (Work.Construction.Ftau α g τ) (slice Φ τ)) z θ
          * Work.Spaces.pth (Work.Construction.Ftau α g τ) z θ
        - 2 * α * Work.Construction.Vop
        (Work.Construction.PhiTil α (Work.Construction.Ftau α g τ) (slice Φ τ)) z θ
          * Work.Spaces.Dz (Work.Construction.Ftau α g τ) z θ
        - (1 / 2) * Work.Construction.s2 θ
        * Work.Construction.FK (Work.Construction.Ftau α g τ) z
          * Work.Spaces.pth (Work.Construction.Ftau α g τ) z θ
        - Real.sin θ ^ 2 * Work.Construction.FK (Work.Construction.Ftau α g τ) z
          * Work.Construction.Ftau α g τ z θ) :=
      co6_sub hS4 hT5
    refine ContDiffOn.congr
      (f₁ := Function.uncurry (Work.Construction.N α (Work.Construction.Ftau α g τ)
        (slice Φ τ))) hS5 ?_
    intro p hp
    obtain ⟨z, θ⟩ := p
    simp only [Function.uncurry, Work.Construction.N]

end Work.FTS.StrongPersist.H6Rows
