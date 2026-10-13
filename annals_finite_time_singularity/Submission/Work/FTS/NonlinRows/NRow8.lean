import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.Nonlinear.Pieces.Rows
import Submission.Work.FTS.Nonlinear.Pieces.Basic
import Submission.Work.FTS.LocData.HkMem_const_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.NonlinRows

open Work.FTS.Galerkin (Fn)

set_option linter.unusedVariables false

/-- **Row 8 of the §8 table, in the open-quadrant (primed) vocabulary** (Elgindi §8, tex 1450):
the `ℋ⁴`-honesty and the bound of the piece `N₁^{gg} = 2·ℛ(Φ̃_g)·g`.

Mathematically this is the product rule `HProdQ` for the `ℋ⁴`-product of the coefficient
`ℛ(Φ̃_g) = Rop α (Φ̃_g)` and the perturbation `g`:

* `EllPkgGo.R` gives `HQo α 4 (Rop α (Φ̃_g))` together with
  `|Rop α (Φ̃_g)|_{ℋ⁴} ≤ Ce·|g|_{ℋ⁴}`;
* `GalClass α g` gives `HQo α 4 g` (`galClass_HQo4`);
* `N4Norm'.prod` then yields both the `ℋ⁴`-honesty of the product `Rop α (Φ̃_g)·g` and the bound
  `|Rop α (Φ̃_g)·g|_{ℋ⁴} ≤ Ci·α^{-1/2}·|Rop α (Φ̃_g)|_{ℋ⁴}·|g|_{ℋ⁴}`;
* the factor `2` of `N₁^{gg}` is pulled out by `HkMem_const_mul` / `Xn_const_mul`, giving the
  constant `K = 2·Ci·max Ce 1` (positive independently of the sign of `Ce`).

No `IP`-level clause is needed: `hE` is not used. -/
theorem NRow8 (IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ) {α₂ Ci Ct Ce Cs : ℝ}
    (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂) (hE : Work.FTS.OpenPkg.N4Extra' IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      0 < α → α ≤ 1 → α ≤ α₂ → Work.FTS.Nonlin.GalClass α g →
      Work.FTS.VocabO.StarPkgo α Cs Φs → Work.FTS.VocabO.EllPkgGo α Ce g Φg →
      Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N1gg α g Φg) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N1gg α g Φg)
          ≤ K * (α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2) := by
  obtain ⟨hCi, _⟩ := hN.pos
  have hmax : 0 < max Ce 1 := lt_of_lt_of_le zero_lt_one (le_max_right Ce 1)
  refine ⟨2 * Ci * max Ce 1, mul_pos (mul_pos (by norm_num) hCi) hmax, ?_⟩
  intro α g Φs Φg hα hα1 hαα₂ hgal hstar hell
  -- the coefficient `R = ℛ(Φ̃_g) = Rop α (Φ̃_g)`
  have hRreg : Work.FTS.VocabO.HQo α 4
      (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg)) := hell.R.1
  have hRB : Work.FTS.Nonlin.Xn α
        (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg))
      ≤ Ce * Work.FTS.Nonlin.Xn α g := hell.R.2
  -- `g ∈ ℋ⁴`, and the product rule `N4Norm'.prod`
  have hg4 : Work.FTS.VocabO.HQo α 4 g := Work.FTS.OpenPkg.galClass_HQo4 hgal
  have hαIoc : α ∈ Set.Ioc 0 α₂ := ⟨hα, hαα₂⟩
  have hprod := hN.prod α hαIoc (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg)) g
    hRreg hg4
  -- positivity of the pieces
  have hXg : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hA : 0 ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
  -- `N₁^{gg}` is `2` times the product
  have heq : Work.FTS.Nonlin.N1gg α g Φg = fun z θ =>
      2 * (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg) z θ * g z θ) := by
    funext z θ
    simp only [Work.FTS.Nonlin.N1gg]
    ring
  constructor
  · -- `ℋ⁴`-honesty: scalar multiple of the honest product
    rw [heq]
    exact Work.FTS.LocData.HkMem_const_mul α 4 2 hprod.1
  · -- the norm bound
    rw [heq, Work.FTS.Nonlinear.Pieces.RowsN0Aux.Xn_const_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    -- it suffices to bound the product, then multiply by `2`
    have hbound : Work.FTS.Nonlin.Xn α
          (fun z θ => Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg) z θ * g z θ)
        ≤ (Ci * max Ce 1) * (α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2) := by
      refine le_trans hprod.2 ?_
      have hp : 0 ≤ Ci * α ^ (-(1 / 2 : ℝ)) := mul_nonneg hCi.le hA
      -- replace `|ℛ(Φ̃_g)|_{ℋ⁴}` by `Ce·|g|_{ℋ⁴}`
      have h1 : Ci * α ^ (-(1 / 2 : ℝ))
            * Work.FTS.Nonlin.Xn α (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg))
            * Work.FTS.Nonlin.Xn α g
          ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (Ce * Work.FTS.Nonlin.Xn α g)
            * Work.FTS.Nonlin.Xn α g :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hRB hp) hXg
      -- replace `Ce` by `max Ce 1`
      have h2 : Ci * α ^ (-(1 / 2 : ℝ)) * (Ce * Work.FTS.Nonlin.Xn α g)
            * Work.FTS.Nonlin.Xn α g
          ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (max Ce 1 * Work.FTS.Nonlin.Xn α g)
            * Work.FTS.Nonlin.Xn α g :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (le_max_left Ce 1) hXg) hp) hXg
      refine le_trans h1 (le_trans h2 ?_)
      have he : Ci * α ^ (-(1 / 2 : ℝ)) * (max Ce 1 * Work.FTS.Nonlin.Xn α g)
            * Work.FTS.Nonlin.Xn α g
          = (Ci * max Ce 1) * (α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2) := by
        ring
      rw [he]
    -- multiply the bound by `2` and reassociate
    have h2bound := mul_le_mul_of_nonneg_left hbound (by norm_num : (0 : ℝ) ≤ 2)
    have he2 : 2 * ((Ci * max Ce 1) * (α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2))
        = (2 * Ci * max Ce 1) * (α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2) := by
      ring
    rw [he2] at h2bound
    exact h2bound

end Work.FTS.NonlinRows
