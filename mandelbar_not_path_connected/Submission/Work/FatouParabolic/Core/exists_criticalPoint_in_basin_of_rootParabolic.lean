/-
Copyright: subproject `Submission/Work/FatouParabolic/` of `mandelbar_not_path_connected`.

# Fatou's theorem at a root-parabolic parameter: the critical point in the basin of `z₁`

This module is the *assembly* of the petal/Liouville core of `Core/Main.lean` at a
root-parabolic parameter `c` of the tricorn, i.e. at the input bundle `Work.EL.RootParabolic c`.

The second return map is `F c = (Tsq c)^[5] = (T_c)^{10}` (`Tsq c = (T_c)^2` is its holomorphic
square), the parabolic point is `d.z₁`; the hypothesis is that the punctured basin of `z₁` is
simply connected.  Then:

* `F c = (Tsq c)^[5]` is a polynomial map of degree `4^5 = 1024 ≥ 2`
  (`Work.FatouParabolic.Poly.tsq_iterate_isPolynomialMap`);
* `d.z₁` is a fixed point of `F c` of multiplier `1` (`d.per_half`, `d.mult`), and the parabolic
  point is simple (`d.simple`);
* `g = (T_c)^5` is an *antiholomorphic* square root of `F c` (`g ∘ g = F c`, `g z₁ = z₁`, and
  `star ∘ g` is a polynomial in `z`), so the repaired Leau–Fatou flower of
  `Work.FatouCoordFix` exists at `z₁` and carries the petal-image property: this is exactly
  `Work.FatouParabolic.Core.exists_flowerImageFix`.

Feeding these into the Liouville step `Work.FatouParabolic.exists_isCriticalPoint_in_basin_of_flowerImageFix_of_simplyConnected`
(`Core/Main.lean`) gives a critical point of `F c` in the basin of `z₁`.

## Main result

* `Work.FatouParabolic.Core.exists_criticalPoint_in_basin_of_rootParabolic` — at every
  root-parabolic parameter, if the parabolic basin is simply connected then it contains a
  critical point of the second return map.
-/
import Mathlib
import Submission.Work.FatouParabolic.Core.Main
import Submission.Work.FatouParabolic.Core.exists_flowerImageFix
import Submission.Work.FatouParabolic.Poly.tsq_iterate_isPolynomialMap
import Submission.Work.ELTop.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FatouParabolic.Core

open LeanEval.ComplexAnalysis (Tantibar)

/-! ## The holomorphic square `Tsq c = (T_c)^2` and the antiholomorphic root `g = (T_c)^5`

The five lemmas below are the local restatements, at `F = F c` and `g = (T_c)^5`, of the facts
that the flower existence theorem `Core/exists_flowerImageFix` asks for.  They are proved from
scratch so that this module depends only on `Work.ELTop.Defs`, the `Core` modules and the
polynomial-map lemmas of `Poly/`. -/

/-- `Tsq c = T_c ∘ T_c`, as functions. -/
private theorem tsq_eq_comp (c : ℂ) : Work.Landing.Tsq c = (Tantibar c)^[2] := by
  funext z
  simp [Work.Landing.Tsq, LeanEval.ComplexAnalysis.Tantibar, map_add, map_pow]

/-- `Tsq c z = (z^2 + conj c)^2 + c` is a polynomial, hence entire. -/
private theorem differentiable_tsq (c : ℂ) : Differentiable ℂ (Work.Landing.Tsq c) := by
  rw [show Work.Landing.Tsq c = fun z : ℂ => (z ^ 2 + star c) ^ 2 + c from rfl]
  fun_prop

/-- The second return map `F c = (Tsq c)^[5]` is the tenth iterate of `T_c`. -/
private theorem F_eq_tantibar_ten (c : ℂ) : Work.EL.F c = (Tantibar c)^[10] := by
  rw [show Work.EL.F c = (Work.Landing.Tsq c)^[5] from rfl, tsq_eq_comp c,
    show (10 : ℕ) = 2 * 5 from rfl, Function.iterate_mul]

/-- `z₁` is a fixed point of `F c` as soon as it is fixed by `(T_c)^5` (it is then fixed by the
second iterate `(T_c)^{10} = F c`). -/
private theorem tanti_five_fix (c z₁ : ℂ) (h : (Tantibar c)^[5] z₁ = z₁) :
    Work.EL.F c z₁ = z₁ := by
  rw [F_eq_tantibar_ten c, show (10 : ℕ) = 5 + 5 from rfl, Function.iterate_add_apply, h, h]

/-- `g = (T_c)^5` is an antiholomorphic square root of `F c = (T_c)^{10}`:
`g ∘ g = F c`. -/
private theorem tanti_five_comp (c : ℂ) :
    ((Tantibar c)^[5]) ∘ ((Tantibar c)^[5]) = Work.EL.F c := by
  funext z
  rw [Function.comp_apply, F_eq_tantibar_ten c,
    show (10 : ℕ) = 5 + 5 from rfl, Function.iterate_add_apply]

/-- `(T_c)^5 = T_c ∘ (Tsq c)^[2]`: the odd iterate of the antiholomorphic quadratic is the
antiholomorphic `T_c` composed with a *holomorphic* polynomial. -/
private theorem tanti_five_eq (c : ℂ) :
    (Tantibar c)^[5] = Tantibar c ∘ (Work.Landing.Tsq c)^[2] := by
  have h4 : (Tantibar c)^[4] = (Work.Landing.Tsq c)^[2] := by
    have h : (Tantibar c)^[4] = ((Tantibar c)^[2])^[2] := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, Function.iterate_mul (Tantibar c) 2 2]
    rw [h, ← tsq_eq_comp c]
  rw [show (5 : ℕ) = 1 + 4 from rfl, Function.iterate_add (Tantibar c) 1 4,
    Function.iterate_one (Tantibar c), h4]

/-- **`star ∘ (T_c)^5` is holomorphic**, explicitly: it is the polynomial
`z ↦ ((Tsq c)^[2] z)^2 + conj c`.  This is the differentiability requirement of the flower for
`F = F c`, `g = (T_c)^5`. -/
private theorem star_tanti_five (c z : ℂ) :
    star ((Tantibar c)^[5] z) = ((Work.Landing.Tsq c)^[2] z) ^ 2 + star c := by
  rw [tanti_five_eq c, Function.comp_apply, LeanEval.ComplexAnalysis.Tantibar]
  simp

/-- Differentiability of `star ∘ (T_c)^5`, from the explicit formula. -/
private theorem differentiable_star_tanti_five (c : ℂ) :
    ∀ z, DifferentiableAt ℂ (fun z => star ((Tantibar c)^[5] z)) z := by
  have hfun : (fun z : ℂ => star ((Tantibar c)^[5] z)) =
      fun z : ℂ => ((Work.Landing.Tsq c)^[2] z) ^ 2 + star c :=
    funext (star_tanti_five c)
  rw [hfun]
  exact fun _ => (Differentiable.add_const (star c)
    (((differentiable_tsq c).iterate 2).pow 2)).differentiableAt

/-! ## The assembly -/

/-- **Fatou's theorem at a root-parabolic parameter.**  Let `d` be a root-parabolic parameter of
the tricorn (`Work.EL.RootParabolic c`: the characteristic parabolic point `d.z₁`, fixed by the
second return map `F c = (T_c)^{10}` with multiplier `1`, and simple), and suppose that the
punctured basin of `d.z₁` under `F c` is simply connected.  Then the basin of `d.z₁` contains a
critical point of `F c`.

This is `Work.FatouParabolic.exists_isCriticalPoint_in_basin_of_flowerImageFix_of_simplyConnected` with the flower
of `Core/exists_flowerImageFix` at `F = F c`, `g = (T_c)^5`, `z₀ = d.z₁`: the second return map
is a polynomial map of degree `4^5 = 1024 ≥ 2`, `d.z₁` is a multiplier-one fixed point of it, and
`(T_c)^5` is an antiholomorphic square root of it with `star ∘ (T_c)^5` holomorphic. -/
theorem exists_criticalPoint_in_basin_of_rootParabolic {c : ℂ} (d : Work.EL.RootParabolic c)
    (hsc : Work.FatouParabolic.ParabolicBasinSimplyConnected (Work.EL.F c) d.z₁) :
    ∃ w : ℂ, Work.FatouParabolic.IsCriticalPoint (Work.EL.F c) w ∧
      w ∈ Work.FatouParabolic.basin (Work.EL.F c) d.z₁ := by
  -- `F c` is a polynomial map of degree `1024 ≥ 2`
  have hF : Work.FatouParabolic.IsPolynomialMapOfDegreeAtLeastTwo (Work.EL.F c) :=
    Work.FatouParabolic.Poly.tsq_iterate_isPolynomialMap c (m := 5) (by norm_num)
  have hdiff : Differentiable ℂ (Work.EL.F c) :=
    Work.FatouParabolic.Poly.isPolynomialMap_differentiable hF
  -- `d.z₁` is a multiplier-one fixed point, and it is a simple parabolic point
  have hfix : Work.EL.F c d.z₁ = d.z₁ := tanti_five_fix c d.z₁ d.per_half
  have h1 : deriv (Work.EL.F c) d.z₁ = 1 := d.mult
  -- the repaired Leau–Fatou flower with the petal-image property
  obtain ⟨fl, -⟩ := Work.FatouParabolic.Core.exists_flowerImageFix (Work.EL.F c)
    ((Tantibar c)^[5]) d.z₁ hdiff (differentiable_star_tanti_five c) (tanti_five_comp c)
    hfix h1 d.simple d.per_half one_pos
  -- the Liouville step
  exact Work.FatouParabolic.exists_isCriticalPoint_in_basin_of_flowerImageFix_of_simplyConnected hF hfix h1 fl hsc

end Work.FatouParabolic.Core
