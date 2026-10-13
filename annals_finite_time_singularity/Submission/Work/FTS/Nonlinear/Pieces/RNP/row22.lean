import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.Nonlinear.Pieces.Ctx
import Submission.Work.FTS.Nonlinear.Pieces.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Pieces.RNP

set_option linter.unusedVariables false

/-! ## Row 22 of the design table of `Submission/Work/FTS/Nonlinear/NOTES_N4.md`

The piece is `N₄^{∗g} = -(1/2)·FK(F_*)·D_θ g` (row 22 of `Defs.lean`), i.e. the slot of the
transport estimate in which the coefficient `-(1/2)·FK(F_*)` is a function of `z` alone and the
derivative `D_θ g = sin(2θ)·∂_θ g` falls on the test function.  The relevant clause of the
`IP`-interface is `N4Extra.t4`,

  `|IP α (f · D_θ g) g| ≤ Ct·α^{-1/2}·|f|_{𝒲^{4,∞}}·X²`,

so everything reduces to the `𝒲^{4,∞}`-norm of the radial coefficient.

The two facts needed about the coefficient:

* `FK (F_*(α)) z = α·(2z/(1+z)²) = α·2·hKer z` (`FstarPkg.FK_Fstar`), so that the coefficient
  is `-α·hKer`;
* for any constant `c`, the function `(z,θ) ↦ c·hKer z` lies in `𝒲^{4,∞}` with norm at most
  `200·|c|`.

The second fact is the radial (angular-factor-free) companion of `Work.Spaces.Gamma_WlInf`
(which bounds `Γ(θ)·hKer z` uniformly in `α`): here the angular variable does not occur at all,
so every positive `D_θ`-iterate vanishes identically and only the five radial summands of the
norm survive, each bounded by `|c|·k!·(k+1)` (`Work.Spaces.pzIter_hKer_bound`).  Since
`∑_{k≤4} k!(k+1) = 153 < 200` the norm is at most `200|c|`. -/

/-- **The `𝒲^{4,∞}`-norm of a constant multiple of the radial profile `hKer(z) = z/(1+z)²`.**

`(z,θ) ↦ c·hKer z` is `θ`-independent, so all its positive `D_θ`-iterates vanish
(`Work.Spaces.DthIter` of a function of `z` alone), and the `𝒲^{4,∞}`-norm is just the sum of
the five radial summands `sup |(z+1)^k h^{(k)}|`, each `≤ |c|·k!·(k+1)`. -/
theorem hKerConstWlInf (α c : ℝ) :
    Work.Spaces.WlInfMem α 4 (fun z θ => c * Work.Spaces.hKer z) ∧
    Work.Spaces.WlInf α 4 (fun z θ => c * Work.Spaces.hKer z) ≤ 200 * |c| := by
  -- every positive `D_θ`-iterate of a `θ`-independent function vanishes
  have hDth : ∀ j : ℕ, Work.Spaces.DthIter (j + 1) (fun z θ => c * Work.Spaces.hKer z)
      = fun _ _ => (0 : ℝ) := by
    intro j
    induction j with
    | zero => funext z θ; simp [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth]
    | succ j ih =>
        rw [show j + 1 + 1 = (j + 1) + 1 from rfl, Work.Spaces.DthIter_succ, ih]
        funext z θ
        simp [Work.Spaces.Dth, Work.Spaces.pth]
  have hpzIter0 : ∀ k : ℕ, Work.Spaces.pzIter k (fun _ _ : ℝ => (0 : ℝ)) = fun _ _ => (0 : ℝ) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [Work.Spaces.pzIter_succ, ih]; funext z θ; simp [Work.Spaces.pz]
  -- the pointwise bounds of the radial summands
  have hrad : ∀ k : ℕ, ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |(z + 1) ^ k * Work.Spaces.pzIter k (fun z θ => c * Work.Spaces.hKer z) z θ|
        ≤ |c| * ((k.factorial : ℝ) * (k + 1)) := by
    intro k z hz θ hθ
    rw [Work.Spaces.pzIter_decomp k (fun _ : ℝ => c) Work.Spaces.hKer z θ]
    rw [show (z + 1) ^ k * (c * deriv^[k] Work.Spaces.hKer z)
        = c * ((z + 1) ^ k * deriv^[k] Work.Spaces.hKer z) by ring]
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (Work.Spaces.pzIter_hKer_bound k z hz) (abs_nonneg c)
  have hmem : Work.Spaces.WlInfMem α 4 (fun z θ => c * Work.Spaces.hKer z) := by
    constructor
    · intro k hk
      exact ⟨|c| * ((k.factorial : ℝ) * (k + 1)), fun y hy => by
        rcases hy with ⟨z, hz, θ, hθ, rfl⟩
        exact hrad k z hz θ hθ⟩
    · intro j hj k hk hj1 hjk
      have hDj : Work.Spaces.DthIter j (fun z θ => c * Work.Spaces.hKer z) = fun _ _ => (0 : ℝ) := by
        rw [← Nat.sub_add_cancel hj1]
        exact hDth (j - 1)
      refine ⟨0, fun y hy => ?_⟩
      rcases hy with ⟨z, hz', θ, hθ, rfl⟩
      simp only []
      rw [hDj]
      have h0 : Work.Spaces.pzIter k (fun _ _ : ℝ => (0 : ℝ)) z θ = 0 :=
        congrFun (congrFun (hpzIter0 k) z) θ
      rw [h0, mul_zero, zero_mul, zero_div, abs_zero]
  refine ⟨hmem, ?_⟩
  rw [Work.Spaces.WlInf]
  have h1 : (∑ k ∈ Finset.range 5, Work.Spaces.supAbs
      (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k (fun z θ => c * Work.Spaces.hKer z) z θ))
      ≤ ∑ k ∈ Finset.range 5, (|c| * ((k.factorial : ℝ) * (k + 1))) :=
    Finset.sum_le_sum fun k _ => Work.Spaces.supAbs_le (hrad k)
  have h2 : (∑ j ∈ Finset.range 5, ∑ k ∈ Finset.range 5,
      if 1 ≤ j ∧ k + j ≤ 4 then Work.Spaces.supAbs
        (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k
            (Work.Spaces.DthIter j (fun z θ => c * Work.Spaces.hKer z)) z θ
          * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
      else 0) ≤ 0 := by
    refine Finset.sum_nonpos (fun j _ => Finset.sum_nonpos (fun k _ => ?_))
    by_cases hc : 1 ≤ j ∧ k + j ≤ 4
    · rw [if_pos hc]
      refine Work.Spaces.supAbs_le (fun z hz' θ hθ => ?_)
      have hDj : Work.Spaces.DthIter j (fun z θ => c * Work.Spaces.hKer z) = fun _ _ => (0 : ℝ) := by
        rw [← Nat.sub_add_cancel hc.1]
        exact hDth (j - 1)
      rw [hDj]
      have h0 : Work.Spaces.pzIter k (fun _ _ : ℝ => (0 : ℝ)) z θ = 0 :=
        congrFun (congrFun (hpzIter0 k) z) θ
      rw [h0, mul_zero, zero_mul, zero_div, abs_zero]
    · rw [if_neg hc]
  calc (∑ k ∈ Finset.range 5, Work.Spaces.supAbs
          (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k (fun z θ => c * Work.Spaces.hKer z) z θ))
        + ∑ j ∈ Finset.range 5, ∑ k ∈ Finset.range 5,
            (if 1 ≤ j ∧ k + j ≤ 4 then Work.Spaces.supAbs
              (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k
                  (Work.Spaces.DthIter j (fun z θ => c * Work.Spaces.hKer z)) z θ
                * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) else 0)
      ≤ (∑ k ∈ Finset.range 5, (|c| * ((k.factorial : ℝ) * (k + 1)))) + 0 := add_le_add h1 h2
    _ = |c| * (∑ k ∈ Finset.range 5, ((k.factorial : ℝ) * (k + 1))) := by
        rw [Finset.mul_sum, add_zero]
    _ ≤ |c| * 200 := mul_le_mul_of_nonneg_left (by norm_num) (abs_nonneg c)
    _ = 200 * |c| := by ring

/-- **Row 22 of the design table** (Elgindi §8): the `ℋ⁴`-pairing of
`N₄^{∗g} = -(1/2) FK(F_*)·D_θ g` with `g`, bounded by `C·√α·X²` with `X = |g|_{ℋ⁴}`.

The coefficient `FK(F_*) = ∫_θ K g` is the *radial* angular moment of the fundamental profile
`F_*`, equal to `α·2z/(1+z)² = α·2·hKer z` (`FstarPkg.FK_Fstar`, where the angular integral
of `ΓK/c` collapses to `1` by the definition of `c = ∫_θ ΓK`).  Hence the slot is exactly the
`D_θ`-transport clause `N4Extra.t4` applied with the coefficient `f = -(1/2)·FK(F_*)`:

`|IP α (N₄^{∗g}) g| ≤ Ct·α^{-1/2}·|(1/2)FK(F_*)|_{𝒲^{4,∞}}·X²`,

and `|(1/2)FK(F_*)|_{𝒲^{4,∞}} ≤ 100·|α| = 100·α` by `hKerConstWlInf` (the factor `1/2` of the
coefficient gives the constant `200·(1/2) = 100`).  The loss `α^{-1/2}·α = √α` is what produces
the `√α` of the stated bound; the constant is `K = 200·Ct` (generously absorbing the `1/2`),
positive because `Ct > 0`.  The hypotheses `StarPkg α Cs Φs` and `EllPkgG α Ce g Φg` are not
needed for this row; `GalClass α g` is used only through `galClass_regQ4`. -/
theorem row22 (IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ)
    {α₂ Ci Ct Ce Cs : ℝ} (hN : Work.FTS.Nonlin.N4Norm Ci α₂)
    (hE : Work.FTS.Nonlin.N4Extra IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      Work.FTS.Nonlin.GalClass α g → Work.FTS.Nonlin.StarPkg α Cs Φs →
      Work.FTS.Nonlin.EllPkgG α Ce g Φg → 0 < α → α ≤ 1 → α ≤ α₂ →
      |IP α (Work.FTS.Nonlin.N4sg α g) g|
        ≤ K * (Real.sqrt α * Work.FTS.Nonlin.Xn α g ^ 2) := by
  have hCt0 : 0 < Ct := hE.pos.1
  refine ⟨200 * Ct, by positivity, ?_⟩
  intro α g Φs Φg hgal hstar hell hα hα1 hαα₂
  have hIoc : α ∈ Set.Ioc 0 α₂ := ⟨hα, hαα₂⟩
  have hreg4 : Work.FTS.Nonlin.RegQ α 4 g := Work.FTS.Nonlin.galClass_regQ4 hgal
  have hX0 : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  -- `FK(F_*) = α·2·hKer`, so the coefficient `-(1/2)FK(F_*)` equals `-α·hKer`
  have hcoef : (fun z θ : ℝ => -(1 / 2) * Work.Construction.FK (Work.Construction.Fstar α) z)
      = fun z θ : ℝ => (-α) * Work.Spaces.hKer z := by
    funext z θ
    rw [Work.FTS.Nonlinear.FstarPkg.FK_Fstar hα hα1, Work.Spaces.hKer_apply]
    ring
  have hmem : Work.Spaces.WlInfMem α 4
      (fun z θ : ℝ => -(1 / 2) * Work.Construction.FK (Work.Construction.Fstar α) z) := by
    rw [hcoef]
    exact (hKerConstWlInf α (-α)).1
  have hnorm : Work.Spaces.WlInf α 4
      (fun z θ : ℝ => -(1 / 2) * Work.Construction.FK (Work.Construction.Fstar α) z) ≤ 200 * α := by
    rw [hcoef]
    have h := (hKerConstWlInf α (-α)).2
    rw [show |(-α)| = α from by rw [abs_neg, abs_of_pos hα]] at h
    exact h
  -- the `D_θ`-transport clause of the interface
  have ht4 := hE.t4 α hIoc
    (fun z θ => -(1 / 2) * Work.Construction.FK (Work.Construction.Fstar α) z) g hmem hreg4
  have hN4 : Work.FTS.Nonlin.N4sg α g = fun z θ =>
      (fun z θ => -(1 / 2) * Work.Construction.FK (Work.Construction.Fstar α) z) z θ
        * Work.Spaces.Dth g z θ := by
    funext z θ
    simp only [Work.FTS.Nonlin.N4sg]
  rw [hN4]
  have hA0 : 0 ≤ Ct * α ^ (-(1 / 2 : ℝ)) := mul_nonneg hCt0.le (Real.rpow_nonneg hα.le _)
  have hsqrt : Real.sqrt α = α * α ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow]
    have h := Real.rpow_add hα (1 : ℝ) (-(1 / 2 : ℝ))
    rw [Real.rpow_one, show (1 : ℝ) + -(1 / 2) = 1 / 2 by norm_num] at h
    exact h
  refine ht4.trans ?_
  refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnorm hA0)
    (pow_nonneg hX0 2)).trans ?_
  rw [hsqrt]
  exact le_of_eq (by ring)

end Work.FTS.Nonlinear.Pieces.RNP
