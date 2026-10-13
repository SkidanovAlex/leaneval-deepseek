/-
# `E4R3/N4C/HonRows/n0row4` — row 4 of the `N₀`-block in the **honest** (open-quadrant) class

This is the honest (class-`C`) counterpart of `Work.FTS.NonlinRows.row4`
(`Submission/Work/FTS/NonlinRows/NRow1_7Aux.lean`) — row 4 of the `§8` table,

  `N₀₄ᵇ = (3/(2α)) · sin(2θ) · L₁₂(g) · ∂_θ g = ((3/(2α)) L₁₂(g)) · D_θ g`,

with `ℋ⁴`-honesty and the pairing bound `|IP α N₀₄ᵇ g| ≤ K α^{-3/2} Xn α g ^ 3`.

The differences with the frozen statement are exactly the honesty hypotheses: the profile `g` is
only supposed `C^∞` on the **open** quadrant (`SmoothOpen g`), honestly in `ℋ⁴`/`ℋ⁵`, with
`L₁₂(g)(0) = 0` and the `L¹`-decay of its partials (`DecayAll 4 g`); the pair package is
`N4C.N4ExtraH` (whose `t4` clause is the honest, coefficient-free `D_θ`-transport clause), not
`OpenPkg.N4Extra'`.  The proof is the frozen one with three substitutions:

* `L₁₂`-`D_z`-iterate bounds: `L12_dzdIter_abs_le` ↦ `N4C.L12_dzdIter_abs_le_open`;
* the radial smoothness of the coefficient is obtained from the elliptic package `EllPkgGo` as in
  the frozen proof (`NonlinRows.smoothOpen_L12_radial`);
* `HkMem α 4 (D_θ g)` from `HkMem α 5 g`: `HkMem_dth_of_RegQ_ge` ↦ `IPGen.HkMem_Dth_le`.

`sorry`-free.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongEps.E4R3.N4C.Defs
import Submission.Work.FTS.StrongEps.E4R3.N4C.L12AbsLeHon
import Submission.Work.FTS.NonlinRows.NRow1_7Aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

-- Uniform-in-`Cs`, `Ce` restatement of `Work.FTS.StrongEps.E4R3.N4C.HonRows.n0row4`.
-- The two binders `Cs`, `Ce` are moved from the theorem's argument list into the inner
-- `forall`, so that the constant `K` does not depend on them (the target `rowsN0T`
-- quantifies `{Cs Ce}` *after* the `exists K`).  The proof script is unchanged.

namespace Work.FTS.StrongEps.E4R3.N4C.HonRowsU

open Work.FTS.Galerkin (Fn)
open Work.Spaces (HkMem HkSq HkNorm Dz Dth)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

theorem n0row4u (IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ)
    {α₂ Ci Ct : ℝ} (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂)
    (hE : Work.FTS.StrongEps.E4R3.N4C.N4ExtraH IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {Cs Ce α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      0 < α → α ≤ 1 → α ≤ α₂ →
      Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 4 g →
      Work.Spaces.HkMem α 5 g → Work.Construction.L12 g 0 = 0 →
      Work.Spaces.DecayAll 4 g →
      Work.FTS.VocabO2.StarPkgo2 α Cs Φs → Work.FTS.VocabO.EllPkgGo α Ce g Φg →
      Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N04bF α g) ∧
        |IP α (Work.FTS.Nonlin.N04bF α g) g|
          ≤ K * (α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 3) := by
  obtain ⟨hCt, _⟩ := hE.pos
  obtain ⟨KL, hKLpos, hKLb⟩ := Work.FTS.StrongEps.E4R3.N4C.L12_dzdIter_abs_le_open
  refine ⟨Ct * 25 * (3 / 2) * KL + 1, by positivity, ?_⟩
  intro Cs Ce α g Φs Φg hα hα1 hαα₂ hsm hmem4 hmem5 hL120 hdec hs hell
  have hIoc : α ∈ Set.Ioc 0 α₂ := ⟨hα, hαα₂⟩
  -- the radial coefficient `(3/(2α)) L₁₂(g)`
  have hL12sm : Work.FTS.EllipticEst.SmoothOpen
      (fun z _ => Work.Construction.L12 g z) :=
    Work.FTS.NonlinRows.smoothOpen_L12_radial hα hell.smooth hell.V.1.1
  have hL12 := hN.l12H α hIoc g ⟨hsm, hmem4⟩ hL120
  have hfMem : Work.Spaces.HkMem α 4
      (fun z θ => (3 / (2 * α)) * Work.Construction.L12 g z) :=
    Work.FTS.LocData.HkMem_const_mul α 4 (3 / (2 * α)) hL12.1
  have hfx0 : (0 : ℝ) ≤ 3 / (2 * α) := by positivity
  have hX0 : (0 : ℝ) ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hM0 : (0 : ℝ) ≤ (3 / (2 * α)) * (KL * Work.FTS.Nonlin.Xn α g) :=
    mul_nonneg hfx0 (mul_nonneg hKLpos.le hX0)
  have hfXn : Work.FTS.Nonlin.Xn α
        (fun z θ => (3 / (2 * α)) * Work.Construction.L12 g z)
      ≤ (3 / (2 * α)) * (Ci * Work.FTS.Nonlin.Xn α g) := by
    rw [Work.FTS.Nonlinear.Pieces.RowsN0Aux.Xn_const_mul, abs_of_nonneg hfx0]
    exact mul_le_mul_of_nonneg_left hL12.2 hfx0
  -- the pointwise (`D`-sup) bound on the coefficient
  have hpt : ∀ b j : ℕ, b + j ≤ 4 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed b j (fun z θ => (3 / (2 * α)) * Work.Construction.L12 g z) z θ|
        ≤ (3 / (2 * α)) * (KL * Work.FTS.Nonlin.Xn α g) := by
    intro b j hbj z θ hz hθ0 hθ1
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj
      have hmixed : Work.Spaces.mixed b 0
            (fun z θ => (3 / (2 * α)) * Work.Construction.L12 g z) z θ
          = (3 / (2 * α)) * Work.Elliptic.DzdIter b (fun z => Work.Construction.L12 g z) z := by
        rw [Work.Spaces.mixed_zero_right,
          Work.FTS.Nonlinear.Pieces.RowsN0Aux.DzIter_const_mul]
        simp only [Work.Elliptic.DzIter_rad]
      rw [hmixed, abs_mul, abs_of_nonneg hfx0]
      exact mul_le_mul_of_nonneg_left
        (hKLb hα hα1 hsm hmem4 hL120 b hbj z hz) hfx0
    · have hzero : Work.Spaces.mixed b j
          (fun z θ => (3 / (2 * α)) * Work.Construction.L12 g z) z θ = 0 := by
        have hd : Work.Spaces.DthIter j
            (fun z θ => (3 / (2 * α)) * Work.Construction.L12 g z) = 0 := by
          rw [Work.FTS.Nonlinear.Pieces.RowsN0Aux.DthIter_const_mul,
            Work.FTS.NonlinRows.dthIter_rad_eq_zero (fun z => Work.Construction.L12 g z) j hj]
          funext z θ
          simp only [Pi.zero_apply]
          ring
        simp only [Work.Spaces.mixed, hd]
        rw [Work.FTS.NonlinRows.dzIter_zero b]
        simp only [Pi.zero_apply]
      rw [hzero, abs_zero]
      exact hM0
  have hWDmem : Work.FTS.VocabO.WDMem 4
      (fun z θ => (3 / (2 * α)) * Work.Construction.L12 g z) :=
    fun b j hbj => ⟨(3 / (2 * α)) * (KL * Work.FTS.Nonlin.Xn α g),
      fun z θ hz hθ0 hθ1 => hpt b j hbj z θ hz hθ0 hθ1⟩
  have hWDp : Work.FTS.VocabO.WDp 4
        (fun z θ => (3 / (2 * α)) * Work.Construction.L12 g z)
      ≤ 25 * ((3 / (2 * α)) * (KL * Work.FTS.Nonlin.Xn α g)) :=
    Work.FTS.OpenPkg.WDp_le_of_pointwise (α := α) hM0 hpt
  -- the `ℋ⁴`-honesty of the piece, by the product rule with `D_θ g`
  have hDthMem : Work.Spaces.HkMem α 4 (Work.Spaces.Dth g) :=
    Work.FTS.IPGen.HkMem_Dth_le (k := 4) (by linarith) hsm hmem5
  have hDthSm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dth g) := hsm.Dth
  have hprod := hN.prod α hIoc (fun z θ => (3 / (2 * α)) * Work.Construction.L12 g z)
    (Work.Spaces.Dth g)
    ⟨Work.FTS.NonlinRows.smoothOpen_const_mul (3 / (2 * α)) hL12sm, hfMem⟩
    ⟨hDthSm, hDthMem⟩
  have hid : Work.FTS.Nonlin.N04bF α g
      = fun z θ => (fun z θ => (3 / (2 * α)) * Work.Construction.L12 g z) z θ
          * Work.Spaces.Dth g z θ := by
    funext z θ
    simp only [Work.FTS.Nonlin.N04bF, Work.Construction.N04b, Work.Construction.Ftot,
      Work.Construction.Fstar, Work.Spaces.Dth, Work.Spaces.pth, Work.Construction.s2,
      Work.FTS.Nonlin.PhiTg]
    ring
  rw [hid]
  refine ⟨hprod.1, ?_⟩
  -- the pairing bound, from the honest transport clause `t4`
  have ht4 := hE.t4 α hIoc (fun z θ => (3 / (2 * α)) * Work.Construction.L12 g z) g
    (Work.FTS.NonlinRows.smoothOpen_const_mul (3 / (2 * α)) hL12sm) hWDmem hsm hmem4 hmem5 hdec
  refine ht4.trans ?_
  have hrp : (0 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
  have hb1 : (0 : ℝ) ≤ α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 3 :=
    mul_nonneg (Real.rpow_nonneg hα.le _) (pow_nonneg hX0 3)
  have hXg3 : (0 : ℝ) ≤ Work.FTS.Nonlin.Xn α g ^ 2 := pow_nonneg hX0 2
  calc Ct * α ^ (-(1 / 2 : ℝ)) * Work.FTS.VocabO.WDp 4
          (fun z θ => (3 / (2 * α)) * Work.Construction.L12 g z)
        * Work.FTS.Nonlin.Xn α g ^ 2
      ≤ Ct * α ^ (-(1 / 2 : ℝ)) * (25 * ((3 / (2 * α)) * (KL * Work.FTS.Nonlin.Xn α g)))
        * Work.FTS.Nonlin.Xn α g ^ 2 := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hWDp ?_) hXg3
        exact mul_nonneg hCt.le hrp
    _ = Ct * 25 * (3 / 2) * KL * (α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 3) := by
        have hpow : α ^ (-(1 / 2 : ℝ)) * α ^ (-(1 : ℝ)) = α ^ (-(3 / 2 : ℝ)) := by
          rw [← Real.rpow_add hα]
          norm_num
        have hinv : (3 : ℝ) / (2 * α) = (3 / 2) * α ^ (-(1 : ℝ)) := by
          rw [Real.rpow_neg_one]
          field_simp
        rw [hinv]
        linear_combination (Ct * 25 * (3 / 2) * KL * Work.FTS.Nonlin.Xn α g ^ 3) * hpow
    _ ≤ (Ct * 25 * (3 / 2) * KL + 1)
          * (α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 3) := by
        refine mul_le_mul_of_nonneg_right ?_ hb1
        linarith [hCt, hKLpos]

end Work.FTS.StrongEps.E4R3.N4C.HonRowsU
