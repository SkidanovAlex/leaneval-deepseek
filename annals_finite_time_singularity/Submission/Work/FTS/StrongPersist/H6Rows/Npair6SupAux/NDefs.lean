/-
# `Npair6SupAux/NDefs` — the twenty pieces of the `N`-row

The level-six `N`-row (`Work.FTS.StrongPersist.H6Rows.Npair6_sup`) has to bound
`IP6 1…1 α (N α (F_*+f) (Φs+Ef)) f` for `f = slice g τ` and `Φs + Ef = slice Φ τ`.

On the open quadrant (`Work.Construction.Qd`) the structural identity `NZaux.nzs_N_form`
writes the nonlinear term as

`N α F Ψ = 2 ℛ(Ξ) F − 2 (𝒰(Ξ)/sin 2θ) D_θF − 2α 𝒱(Ξ) D_zF − (1/2) (F,K) D_θF − sin²θ (F,K) F`

with `Ξ = PhiTil α F Ψ = Ξ₁ + Ξ₂`, `Ξ₁ = PhiTil α F_* Φs = PhiTs α Φs`,
`Ξ₂ = PhiTil α f (Ef)`, `F = F_* + f` and `(F,K) = (F_*,K) + (f,K)` (`L3RhsFKadd`).

Expanding gives exactly twenty pieces `A · P`, namely
the twelve `{ℛ(Ξ₁), ℛ(Ξ₂), 𝒰(Ξ₁)/s2, 𝒰(Ξ₂)/s2, 𝒱(Ξ₁), 𝒱(Ξ₂)} × {F_*, f, D_θF_*, D_θf, D_zF_*, D_zf}`
pieces and the eight `{(F_*,K), (f,K)} × {D_θF_*, D_θf, F_*, f}` pieces.

This file only *names* them (no proofs), so that the per-piece estimates of the row can be
stated and delegated independently of the splitting identity itself.

Everything here is a definition; the module has no declaration of mathematical content.
-/
import Mathlib.Analysis.Complex.Trigonometric
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.VocabO2
import Submission.Work.Construction.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology

namespace Work.FTS.StrongPersist.H6Rows.Npair6SupAux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## The six coefficients and the six slots -/

/-- `ℛ(Ξ₁)`, the `ℛ`-coefficient of the *star* residual `Ξ₁ = PhiTs α Φs`. -/
abbrev coefR1 (α : ℝ) (Φs : Fn) : Fn :=
  Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs)

/-- `ℛ(Ξ₂)`, the `ℛ`-coefficient of the *perturbation* residual `Ξ₂ = PhiTil α f Ef`. -/
abbrev coefR2 (α : ℝ) (f Ef : Fn) : Fn :=
  Work.Construction.Rop α (Work.Construction.PhiTil α f Ef)

/-- `𝒰(Ξ₁)/sin 2θ`. -/
abbrev coefU1 (α : ℝ) (Φs : Fn) : Fn :=
  fun z θ => Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ / Work.Construction.s2 θ

/-- `𝒰(Ξ₂)/sin 2θ`. -/
abbrev coefU2 (α : ℝ) (f Ef : Fn) : Fn :=
  fun z θ => Work.Construction.Uop α (Work.Construction.PhiTil α f Ef) z θ
    / Work.Construction.s2 θ

/-- `𝒱(Ξ₁)`. -/
abbrev coefV1 (α : ℝ) (Φs : Fn) : Fn := Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs)

/-- `𝒱(Ξ₂)`. -/
abbrev coefV2 (α : ℝ) (f Ef : Fn) : Fn := Work.Construction.Vop (Work.Construction.PhiTil α f Ef)

/-- The radial `(F_*,K)`-coefficient, `z ↦ (F_*(·,θ),K)`. -/
abbrev coefKs (α : ℝ) : Fn := fun z (_ : ℝ) => Work.Construction.FK (Work.Construction.Fstar α) z

/-- The radial `(f,K)`-coefficient, `z ↦ (f, K)`. -/
abbrev coefKf (f : Fn) : Fn := fun z (_ : ℝ) => Work.Construction.FK f z

/-- The `F_*`-slot. -/
abbrev slotFs (α : ℝ) : Fn := Work.Construction.Fstar α

/-- The `D_θF_*`-slot. -/
abbrev slotTs (α : ℝ) : Fn := Work.Spaces.Dth (Work.Construction.Fstar α)

/-- The `D_zF_*`-slot. -/
abbrev slotZs (α : ℝ) : Fn := Work.Spaces.Dz (Work.Construction.Fstar α)

/-- The `D_θf`-slot. -/
abbrev slotTf (f : Fn) : Fn := Work.Spaces.Dth f

/-- The `D_zf`-slot. -/
abbrev slotZf (f : Fn) : Fn := Work.Spaces.Dz f

/-- The angular factor `sin²θ`. -/
abbrev angSin2 : Fn := fun (_ : ℝ) (θ : ℝ) => Real.sin θ ^ 2

/-! ## The twenty pieces

`nsP0 … nsP19` in the order of the five terms of `N` and, inside each, the star/perturbation
split of the coefficient and the `F_*`/`f` split of the slot. -/

abbrev nsP0 (α : ℝ) (Φs : Fn) : Fn :=
  fun z θ => 2 * coefR1 α Φs z θ * slotFs α z θ

abbrev nsP1 (α : ℝ) (Φs f : Fn) : Fn :=
  fun z θ => 2 * coefR1 α Φs z θ * f z θ

abbrev nsP2 (α : ℝ) (f Ef : Fn) : Fn :=
  fun z θ => 2 * coefR2 α f Ef z θ * slotFs α z θ

abbrev nsP3 (α : ℝ) (f Ef : Fn) : Fn :=
  fun z θ => 2 * coefR2 α f Ef z θ * f z θ

abbrev nsP4 (α : ℝ) (Φs : Fn) : Fn :=
  fun z θ => -2 * coefU1 α Φs z θ * slotTs α z θ

abbrev nsP5 (α : ℝ) (Φs f : Fn) : Fn :=
  fun z θ => -2 * coefU1 α Φs z θ * slotTf f z θ

abbrev nsP6 (α : ℝ) (f Ef : Fn) : Fn :=
  fun z θ => -2 * coefU2 α f Ef z θ * slotTs α z θ

abbrev nsP7 (α : ℝ) (f Ef : Fn) : Fn :=
  fun z θ => -2 * coefU2 α f Ef z θ * slotTf f z θ

abbrev nsP8 (α : ℝ) (Φs : Fn) : Fn :=
  fun z θ => -2 * α * coefV1 α Φs z θ * slotZs α z θ

abbrev nsP9 (α : ℝ) (Φs f : Fn) : Fn :=
  fun z θ => -2 * α * coefV1 α Φs z θ * slotZf f z θ

abbrev nsP10 (α : ℝ) (f Ef : Fn) : Fn :=
  fun z θ => -2 * α * coefV2 α f Ef z θ * slotZs α z θ

abbrev nsP11 (α : ℝ) (f Ef : Fn) : Fn :=
  fun z θ => -2 * α * coefV2 α f Ef z θ * slotZf f z θ

abbrev nsP12 (α : ℝ) : Fn :=
  fun z θ => -(1 / 2) * coefKs α z θ * slotTs α z θ

abbrev nsP13 (α : ℝ) (f : Fn) : Fn :=
  fun z θ => -(1 / 2) * coefKs α z θ * slotTf f z θ

abbrev nsP14 (α : ℝ) (f : Fn) : Fn :=
  fun z θ => -(1 / 2) * coefKf f z θ * slotTs α z θ

abbrev nsP15 (α : ℝ) (f : Fn) : Fn :=
  fun z θ => -(1 / 2) * coefKf f z θ * slotTf f z θ

abbrev nsP16 (α : ℝ) : Fn :=
  fun z θ => -angSin2 z θ * coefKs α z θ * slotFs α z θ

abbrev nsP17 (α : ℝ) (f : Fn) : Fn :=
  fun z θ => -angSin2 z θ * coefKs α z θ * f z θ

abbrev nsP18 (α : ℝ) (f : Fn) : Fn :=
  fun z θ => -angSin2 z θ * coefKf f z θ * slotFs α z θ

abbrev nsP19 (α : ℝ) (f : Fn) : Fn :=
  fun z θ => -angSin2 z θ * coefKf f z θ * f z θ

/-- The sum of the twenty pieces, in the association used by the splitting identity. -/
abbrev nsum (α : ℝ) (f Ef Φs : Fn) : Fn :=
  fun z θ => nsP0 α Φs z θ + nsP1 α Φs f z θ + nsP2 α f Ef z θ + nsP3 α f Ef z θ
    + nsP4 α Φs z θ + nsP5 α Φs f z θ + nsP6 α f Ef z θ + nsP7 α f Ef z θ
    + nsP8 α Φs z θ + nsP9 α Φs f z θ + nsP10 α f Ef z θ + nsP11 α f Ef z θ
    + nsP12 α z θ + nsP13 α f z θ + nsP14 α f z θ + nsP15 α f z θ
    + nsP16 α z θ + nsP17 α f z θ + nsP18 α f z θ + nsP19 α f z θ

end Work.FTS.StrongPersist.H6Rows.Npair6SupAux
