/-
# Row 15 (`N₂^{ss}`) — the definitions and the basic identities

This module fixes the vocabulary of the primed row-15 estimate
`Work.FTS.NonlinRows.NRow15T2` and proves the elementary facts about it.

The row is about `N₂^{ss} = -2·𝒰(Φ̃_*)·∂_θF_*`.  Writing

* `𝒰 := Uop α (PhiTs α Φs)`,
* `G15 α Φs z θ = ((z+1)/z)·(𝒰 z θ / sin 2θ)`  — the **weighted star coefficient** whose
  `𝒲^{4,∞}`-membership is the field `UszW` of `VocabO.StarPkgo2`,
* `C15 α θ = -2·(α/c(α))·D_θΓ(θ)`  — the **angular coefficient**, `Γ = (sinθcos²θ)^{α/3}`,

the whole row is governed by the identity

  `((z+1)³/z²)·N₂^{ss}(z,θ) = 2·C15 α θ·G15 α Φs z θ`  (`N2ss_weighted_eq`),

which is `row15`'s identity `((z+1)³/z²)·N₂^{ss} = -2[((z+1)/z)(𝒰/sin2θ)]·[((z+1)²/z)D_θF_*]`
of the design note, with the second factor evaluated in closed form:
`((z+1)²/z)·D_θF_* = 2(α/c)·D_θΓ` because `F_* = α(Γ/c)·2z/(1+z)²` and
`(z+1)²/z·(2z/(1+z)²) = 2`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS.NonlinRows.Defs
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Construction.Basic
import Submission.Work.Construction.L12_Fstar_eq
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Spaces.Gamma_WlInf
import Submission.Work.Spaces.c_bounds
import Submission.Work.Spaces.Gam_bounds
import Submission.Work.FTS.NonlinRows.smoothOpen_radA
import Submission.Work.FTS.EllipticEst.Cert.SmoothOpen_bslOp
import Submission.Work.FTS.H2.STFacts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.NonlinRows

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## The two factors of row 15 -/

/-- The **weighted star coefficient** of row 15: `((z+1)/z)·(𝒰(Φ̃_*)/sin 2θ)`.  Its
`𝒲^{4,∞}`-membership (with the bound `≤ Cs·α`) is the field `UszW` of
`Work.FTS.VocabO2.StarPkgo2`. -/
def G15 (α : ℝ) (Φs : Fn) : Fn :=
  fun z θ => (z + 1) / z
    * (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ / Work.Construction.s2 θ)

/-- The **angular coefficient** of row 15: `C15 α θ = -2·(α/c(α))·D_θΓ(θ)`. -/
def C15 (α : ℝ) : ℝ → ℝ :=
  fun θ => -2 * (α / Work.Spaces.c α) * Work.Spaces.dthU (Work.Spaces.Gam α) θ

theorem C15_apply (α θ : ℝ) :
    C15 α θ = -2 * (α / Work.Spaces.c α) * Work.Spaces.dthU (Work.Spaces.Gam α) θ := rfl

theorem G15_apply (α : ℝ) (Φs : Fn) (z θ : ℝ) :
    G15 α Φs z θ = (z + 1) / z
      * (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ / Work.Construction.s2 θ) :=
  rfl

/-! ## The identity

`((z+1)³/z²)·N₂^{ss} = 2·C15·G15` on the closed quadrant.  The proof is the elementary
computation

`((z+1)³/z²)·(-2𝒰·α(Γ'/c)·2z/(1+z)²) = -4(α/c)·(sin2θ·Γ')·((z+1)/z)(𝒰/sin2θ)`,

the `z`-factors cancelling because `((z+1)³/z²)·(z/(1+z))·(2z/(1+z)²) = 2`; at the two
angular endpoints and at `z = 0` both sides vanish (at `θ = 0, π/2` by `VanishTheta` of `𝒰`,
and at `z = 0` by the junk values `1/0 = 0` of the two prefactors). -/

theorem N2ss_weighted_eq {α : ℝ} {Φs : Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hv : Work.Spaces.VanishTheta (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs))) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      (z + 1) ^ 3 / z ^ 2 * Work.FTS.Nonlin.N2ss α Φs z θ = 2 * C15 α θ * G15 α Φs z θ := by
  intro z hz θ hθ
  have hc : Work.Spaces.c α ≠ 0 := by
    have h := (Work.Spaces.c_bounds α hα hα1).1
    linarith
  have hz0 : (0 : ℝ) ≤ z := hz
  rcases eq_or_lt_of_le hz0 with hz' | hz'
  · subst hz'
    simp [Work.FTS.Nonlin.N2ss, G15, C15, Work.Spaces.dthU, Work.Construction.s2_eq]
  rcases eq_or_lt_of_le hθ.1 with hθ0' | hθ0'
  · subst hθ0'
    simp [Work.FTS.Nonlin.N2ss, G15, C15, Work.Spaces.dthU, Work.Construction.s2_eq, hv.1 z]
  rcases eq_or_lt_of_le hθ.2 with hθ1' | hθ1'
  · subst hθ1'
    have hs' : Work.Construction.s2 (π / 2) = 0 := by
      rw [Work.Construction.s2_eq, show 2 * (π / 2) = π by ring, Real.sin_pi]
    simp [Work.FTS.Nonlin.N2ss, G15, C15, Work.Spaces.dthU, hs', hv.2 z]
  -- the open quadrant
  have hs2pos : 0 < Work.Construction.s2 θ := by
    rw [Work.Construction.s2_eq]
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hs2 : Work.Construction.s2 θ ≠ 0 := ne_of_gt hs2pos
  have hz1 : (1 : ℝ) + z ≠ 0 := by linarith
  rw [Work.FTS.Nonlin.N2ss, Work.Construction.pth_Fstar_eq hα]
  simp only [G15_apply, C15_apply, Work.Spaces.dthU, Work.FM.Fstar]
  field_simp
  rw [Work.Construction.s2_eq]
  ring


/-! ## Smoothness of the two factors -/

/-- `Γ(θ) = (sinθcos²θ)^{α/3}` is `C^∞` on the open interval `(0,π/2)`. -/
theorem contDiffOn_Gam (α : ℝ) :
    ContDiffOn ℝ Work.Stability.smoothOrder (fun θ : ℝ => Work.Spaces.Gam α θ)
      (Set.Ioo 0 (π / 2)) := by
  have hsin : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ : ℝ => Real.sin θ)
      (Set.Ioo 0 (π / 2)) := Real.contDiff_sin.contDiffOn
  have hcos : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ : ℝ => Real.cos θ)
      (Set.Ioo 0 (π / 2)) := Real.contDiff_cos.contDiffOn
  have hbase : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2) (Set.Ioo 0 (π / 2)) := hsin.mul (hcos.pow 2)
  have hne : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), Real.sin θ * Real.cos θ ^ 2 ≠ 0 := by
    intro θ hθ
    have h1 : 0 < Real.sin θ :=
      Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
    have h2 : 0 < Real.cos θ :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    positivity
  have h := hbase.rpow (contDiffOn_const (c := α / 3)) hne
  refine h.congr (fun θ hθ => ?_)
  simp only [Work.Spaces.Gam]

/-- `D_θΓ = sin(2θ)·Γ'` is `C^∞` on `(0,π/2)`. -/
theorem contDiffOn_dthU_Gam (α : ℝ) :
    ContDiffOn ℝ Work.Stability.smoothOrder
      (fun θ : ℝ => Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ) (Set.Ioo 0 (π / 2)) := by
  have hderiv : ContDiffOn ℝ Work.Stability.smoothOrder
      (deriv (fun t => Work.Spaces.Gam α t)) (Set.Ioo 0 (π / 2)) :=
    (contDiffOn_Gam α).deriv_of_isOpen isOpen_Ioo le_rfl
  have hsin : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ : ℝ => Real.sin (2 * θ))
      (Set.Ioo 0 (π / 2)) := by
    have h1 : ContDiff ℝ Work.Stability.smoothOrder (fun θ : ℝ => 2 * θ) :=
      contDiff_const.mul contDiff_id
    exact (Real.contDiff_sin.comp h1).contDiffOn
  have h := hsin.mul hderiv
  refine h.congr (fun θ hθ => ?_)
  simp only [Work.Spaces.dthU]

/-- `C15 α` is `C^∞` on `(0,π/2)`. -/
theorem contDiffOn_C15 (α : ℝ) :
    ContDiffOn ℝ Work.Stability.smoothOrder (C15 α) (Set.Ioo 0 (π / 2)) := by
  have h := (contDiffOn_const (c := -2 * (α / Work.Spaces.c α))).mul (contDiffOn_dthU_Gam α)
  refine h.congr (fun θ hθ => ?_)
  simp only [C15_apply]

/-- A θ-only function smooth on `(0,π/2)` is `SmoothOpen` as a function of `(z,θ)`. -/
theorem smoothOpen_theta_only {a : ℝ → ℝ}
    (ha : ContDiffOn ℝ Work.Stability.smoothOrder a (Set.Ioo 0 (π / 2))) :
    Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => a θ) :=
  ha.comp contDiffOn_snd (fun p hp => hp.2)

/-- A `z`-only function smooth on `(0,∞)` is `SmoothOpen` as a function of `(z,θ)`. -/
theorem smoothOpen_z_only {r : ℝ → ℝ}
    (hr : ContDiffOn ℝ Work.Stability.smoothOrder r (Set.Ioi 0)) :
    Work.FTS.EllipticEst.SmoothOpen (fun (z : ℝ) _ => r z) :=
  hr.comp contDiffOn_fst (fun p hp => hp.1)

theorem smoothOpen_C15_bsl (α : ℝ) :
    Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => C15 α θ) :=
  smoothOpen_theta_only (contDiffOn_C15 α)

/-- The `𝒰`-expression of the `Φ̃_*`-node is smooth on the open quadrant. -/
theorem smoothOpen_Uop_PhiTs {α Cs : ℝ} {Φs : Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hs : Work.FTS.VocabO.StarPkgo α Cs Φs) :
    Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)) := by
  have hΦ : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.PhiTs α Φs) :=
    Work.FTS.NonlinRows.smoothOpen_PhiTs hα hα1 hs
  have h1 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => -3 * Work.FTS.Nonlin.PhiTs α Φs z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl (-3) hΦ
  have h2 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => -α * (z * Work.Spaces.pz (Work.FTS.Nonlin.PhiTs α Φs) z θ)) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl (-α)
      (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl
        Work.FTS.EllipticEst.Cert.smoothOpen_z_bsl hΦ.pz)
  refine Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
    (Work.FTS.EllipticEst.Cert.smoothOpen_add_bsl h1 h2) ?_
  intro z θ _ _ _
  rw [Work.Construction.Uop]
  ring

/-- `G15 α Φs = ((z+1)/z)·(𝒰(Φ̃_*)/sin 2θ)` is smooth on the open quadrant. -/
theorem smoothOpen_G15 {α Cs : ℝ} {Φs : Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hs : Work.FTS.VocabO.StarPkgo α Cs Φs) :
    Work.FTS.EllipticEst.SmoothOpen (G15 α Φs) := by
  have hU : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) p.1 p.2)
      Work.FTS.EllipticEst.Q0 :=
    smoothOpen_Uop_PhiTs hα hα1 hs
  have hz : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => (p.1 + 1) / p.1) Work.FTS.EllipticEst.Q0 := by
    refine ContDiffOn.div (contDiffOn_fst.add (contDiffOn_const (c := (1 : ℝ))))
      contDiffOn_fst ?_
    intro p hp
    exact ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1
  have hs2 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => (Real.sin (2 * p.2))⁻¹) Work.FTS.EllipticEst.Q0 := by
    refine ContDiffOn.inv ?_ ?_
    · have h1 : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => 2 * p.2)
          Work.FTS.EllipticEst.Q0 :=
        (contDiffOn_const (c := (2 : ℝ))).mul contDiffOn_snd
      exact (Real.contDiff_sin.contDiffOn).comp h1 (fun p hp => Set.mem_univ _)
    · intro p hp
      obtain ⟨-, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
      exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos]))
  change ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry (G15 α Φs))
    Work.FTS.EllipticEst.Q0
  refine ContDiffOn.congr ((hz.mul hU).mul hs2) ?_
  intro p hp
  obtain ⟨z, θ⟩ := p
  have hpoint : ∀ z θ : ℝ,
      ((z + 1) / z * Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ)
        * (Real.sin (2 * θ))⁻¹ = G15 α Φs z θ := by
    intro z θ
    rw [G15_apply, Work.Construction.s2_eq]
    ring
  exact (hpoint z θ).symm

/-- `F̲(z) = 2z/(1+z)²` is smooth on `(0,∞)`. -/
theorem smoothOpen_FM_Fstar_z :
    Work.FTS.EllipticEst.SmoothOpen (fun (z : ℝ) _ => Work.FM.Fstar z) := by
  have h : ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => 2 * z / (1 + z) ^ 2)
      (Set.Ioi 0) := by
    refine ContDiffOn.div (contDiff_const.mul contDiff_id).contDiffOn
      ((contDiff_const.add contDiff_id).pow 2).contDiffOn ?_
    intro z hz
    have h1 : (0 : ℝ) < 1 + z := by linarith [Set.mem_Ioi.mp hz]
    positivity
  have h2 := smoothOpen_z_only h
  have hfun : (fun z (_ : ℝ) => 2 * z / (1 + z) ^ 2) = fun z (_ : ℝ) => Work.FM.Fstar z := by
    funext z θ; rw [Work.FM.Fstar]
  rwa [hfun] at h2

/-- `N₂^{ss} = -2·𝒰(Φ̃_*)·∂_θF_*` is smooth on the open quadrant. -/
theorem smoothOpen_N2ss {α Cs : ℝ} {Φs : Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hs : Work.FTS.VocabO.StarPkgo α Cs Φs) :
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N2ss α Φs) := by
  have hU : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) p.1 p.2)
      Work.FTS.EllipticEst.Q0 :=
    smoothOpen_Uop_PhiTs hα hα1 hs
  have hder : ContDiffOn ℝ Work.Stability.smoothOrder
      (deriv (fun t => Work.Spaces.Gam α t)) (Set.Ioo 0 (π / 2)) :=
    (contDiffOn_Gam α).deriv_of_isOpen isOpen_Ioo le_rfl
  have hth0 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun θ : ℝ => α * (deriv (fun t => Work.Spaces.Gam α t) θ / Work.Spaces.c α))
      (Set.Ioo 0 (π / 2)) :=
    (contDiffOn_const (c := α)).mul (hder.div_const _)
  have hth : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => α * (deriv (fun t => Work.Spaces.Gam α t) p.2 / Work.Spaces.c α))
      Work.FTS.EllipticEst.Q0 :=
    smoothOpen_theta_only hth0
  have hrad : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Work.FM.Fstar p.1) Work.FTS.EllipticEst.Q0 :=
    smoothOpen_FM_Fstar_z
  change ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry (Work.FTS.Nonlin.N2ss α Φs))
    Work.FTS.EllipticEst.Q0
  refine ContDiffOn.congr
    ((contDiffOn_const (c := (-2 : ℝ))).mul hU |>.mul (hth.mul hrad)) ?_
  intro p hp
  obtain ⟨z, θ⟩ := p
  have hpoint : ∀ z θ : ℝ,
      ((-2 : ℝ) * Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ)
        * (α * (deriv (fun t => Work.Spaces.Gam α t) θ / Work.Spaces.c α) * Work.FM.Fstar z)
      = Work.FTS.Nonlin.N2ss α Φs z θ := by
    intro z θ
    rw [Work.FTS.Nonlin.N2ss, Work.Construction.pth_Fstar_eq hα]
  exact (hpoint z θ).symm

/-! ## The angular jets of `C15` -/

/-- For a θ-only function, `D_θ^j` is the `dthU`-iterate. -/
theorem DthIter_theta_only (g : ℝ → ℝ) (j : ℕ) :
    Work.Spaces.DthIter j (fun _ (θ : ℝ) => g θ) = fun _ θ => Work.Spaces.dthU^[j] g θ := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [Work.Spaces.DthIter_succ, ih]
      funext z θ
      show Real.sin (2 * θ) * deriv (fun θ' => Work.Spaces.dthU^[j] g θ') θ
        = Work.Spaces.dthU^[j + 1] g θ
      rw [Function.iterate_succ_apply' Work.Spaces.dthU j g, Work.Spaces.dthU]

/-- The `z`-derivatives of a product with a θ-only factor. -/
theorem pzIter_theta_mul (j : ℕ) (c : ℝ → ℝ) (K : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pzIter j (fun z θ => c θ * K z θ) z θ = c θ * Work.Spaces.pzIter j K z θ :=
  Work.FTS.H2.pzIter_const_mul c K j z θ

/-- The `dthU`-iterates of `C15 α` are the `D_θ`-jets of `Γ`, up to the constant
`-2α/c`: `dthU^[a] (C15 α) = -2(α/c)·D_θ^{a+1}Γ`. -/
theorem dthU_iter_C15 (α : ℝ) (a : ℕ) :
    Work.Spaces.dthU^[a] (C15 α)
      = fun θ => (-2 * (α / Work.Spaces.c α))
          * Work.Spaces.dthU^[a + 1] (fun t => Work.Spaces.Gam α t) θ := by
  have hfun : C15 α = fun θ => (-2 * (α / Work.Spaces.c α))
      * Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ := by
    funext θ; rw [C15_apply]
  rw [hfun, Work.Spaces.dthU_iter_const_mul, Work.Spaces.dthU_iter_comp]

/-- **The angular jet bound of `C15`**: `|D_θ^a (C15 α)(θ)| ≤ K·α²·Γ(θ)` for `a ≤ 4`,
`0 < α ≤ 1`, `θ ∈ Iθ`. -/
theorem dthU_iter_C15_le :
    ∃ K : ℝ, 0 < K ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (a : ℕ), a ≤ 4 →
      ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.dthU^[a] (C15 α) θ| ≤ K * α ^ 2 * Work.Spaces.Gam α θ := by
  refine ⟨20 * ((∑ a ∈ Finset.range 5, Work.Spaces.tBound a 0) + 1), ?_, ?_⟩
  · have h0 : (0 : ℝ) ≤ ∑ a ∈ Finset.range 5, Work.Spaces.tBound a 0 :=
      Finset.sum_nonneg fun a _ => Work.Spaces.tBound_nonneg a 0
    linarith
  · intro α hα hα1 a ha θ hθ
    have hGam0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
    have hc : (0 : ℝ) < Work.Spaces.c α := by
      have h := (Work.Spaces.c_bounds α hα hα1).1
      linarith
    have hcinv : (Work.Spaces.c α)⁻¹ ≤ 10 := by
      rw [inv_eq_one_div, div_le_iff₀ hc]
      linarith [(Work.Spaces.c_bounds α hα hα1).1]
    have hk : |α / Work.Spaces.c α| ≤ 10 * α := by
      rw [abs_of_nonneg (div_nonneg hα.le hc.le), div_eq_mul_inv]
      calc α * (Work.Spaces.c α)⁻¹ ≤ α * 10 := mul_le_mul_of_nonneg_left hcinv hα.le
        _ = 10 * α := by ring
    have hsum0 : (0 : ℝ) ≤ ∑ a ∈ Finset.range 5, Work.Spaces.tBound a 0 :=
      Finset.sum_nonneg fun a _ => Work.Spaces.tBound_nonneg a 0
    have htb : Work.Spaces.tBound a 0 ≤ ∑ a ∈ Finset.range 5, Work.Spaces.tBound a 0 :=
      Finset.single_le_sum (f := fun a => Work.Spaces.tBound a 0)
        (fun a _ => Work.Spaces.tBound_nonneg a 0) (Finset.mem_range.mpr (by omega))
    have hdth := Work.Spaces.dthU_Gam_le (a + 1) (by omega) α hα hα1 θ hθ
    rw [show a + 1 - 1 = a from by omega] at hdth
    rw [dthU_iter_C15]
    rw [abs_mul, abs_mul]
    have h2 : |Work.Spaces.dthU^[a + 1] (fun t => Work.Spaces.Gam α t) θ|
        ≤ α * (∑ a ∈ Finset.range 5, Work.Spaces.tBound a 0) * Work.Spaces.Gam α θ := by
      refine hdth.trans ?_
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left htb hα.le) hGam0
    have h3 : |(-2 : ℝ)| * |α / Work.Spaces.c α| = 2 * |α / Work.Spaces.c α| := by
      norm_num
    calc |(-2 : ℝ)| * |α / Work.Spaces.c α|
          * |Work.Spaces.dthU^[a + 1] (fun t => Work.Spaces.Gam α t) θ|
        = 2 * |α / Work.Spaces.c α|
          * |Work.Spaces.dthU^[a + 1] (fun t => Work.Spaces.Gam α t) θ| := by rw [h3]
      _ ≤ 2 * (10 * α) * (α * (∑ a ∈ Finset.range 5, Work.Spaces.tBound a 0)
            * Work.Spaces.Gam α θ) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hk (by norm_num)) h2 (abs_nonneg _)
            (by positivity)
      _ ≤ 20 * ((∑ a ∈ Finset.range 5, Work.Spaces.tBound a 0) + 1) * α ^ 2
            * Work.Spaces.Gam α θ := by
          have h1 : (2 : ℝ) * (10 * α) * (α * (∑ a ∈ Finset.range 5, Work.Spaces.tBound a 0)
              * Work.Spaces.Gam α θ)
              ≤ 20 * ((∑ a ∈ Finset.range 5, Work.Spaces.tBound a 0) + 1) * α ^ 2
                * Work.Spaces.Gam α θ := by
            nlinarith [hGam0, hα, hsum0, sq_nonneg α]
          linarith [h1]

end Work.FTS.NonlinRows
