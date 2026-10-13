/-
# `Submission/Work/FTS_MuLipC/LinQuad.lean` — the polynomial structure of the two blocks

Each of the two nonlinear blocks of the modulation is a *polynomial of degree ≤ 2* in the
profile, on the open quadrant:

```
Sn0 α g = C0 α + Lin0 α g + Quad0 α g                       (N₀, quadratic)
Sn  α Φs E g = C1 α Φs + Lin1 α Φs E g + Quad1 α E g       (N,  bilinear)
```

with `Lin·` linear and `Quad·` homogeneous quadratic (`Quad0 u = Bil0 u u`,
`Quad1 u = Bil1 α E u u` for the symmetric bilinear forms `Bil0`, `Bil1`).  These are the
*field* identities behind the two difference rows (`RowN0/diffRow0.lean`,
`RowN/diffRow1.lean`): the difference of two values of a degree-≤2 polynomial is
`Lin(d) + Bil(u,d) + Bil(d,u)` (`u = f+f'`, `d = f−f'`), and each monomial of the bilinear part
carries exactly one `d`-factor.

The identities hold pointwise on the open quadrant `{z > 0, 0 < θ < π/2}`, where `∂_θ`, `D_θ`,
`D_z`, `L₁₂` and the angular moment `FK` are additive.  `sn0_eq_sum` (the `N₀` case) is proved
below; the `N` case (`sn_eq_sum`) is delegated, the definitions being fixed here.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS_MuLipC.Defs
import Submission.Work.FTS.NonlinRows.Rl1.splitOpen
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.SmoothN0
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.Rl0Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_MuLipC

open Work.FTS.Galerkin (Fn Fam slice muDyn)

set_option autoImplicit false

/-! ## The `N₀` block -/

/-- The `g`-independent part of `N₀ α (F_*+g) g`. -/
def C0 (α : ℝ) : Fn := fun z θ =>
  (3 / (2 * α)) * Work.Construction.s2 θ * Work.Construction.L12 (Work.Construction.Fstar α) z
      * Work.Spaces.pth (Work.Construction.Fstar α) z θ
    - Work.Construction.c2m θ * Work.Construction.L12 (Work.Construction.Fstar α) z
      * Work.Spaces.Dz (Work.Construction.Fstar α) z θ

/-- The part of `N₀ α (F_*+g) g` linear in `g`. -/
def Lin0 (α : ℝ) (g : Fn) : Fn := fun z θ =>
  (3 / (2 * α)) * Work.Construction.s2 θ * Work.Construction.L12 g z
      * Work.Spaces.pth (Work.Construction.Fstar α) z θ
    - Work.Construction.c2m θ * Work.Construction.L12 g z
      * Work.Spaces.Dz (Work.Construction.Fstar α) z θ
    - Work.Construction.c2m θ * Work.Construction.L12 (Work.Construction.Fstar α) z
      * Work.Spaces.Dz g z θ

/-- The part of `N₀ α (F_*+g) g` quadratic in `g`. -/
def Quad0 (α : ℝ) (g : Fn) : Fn := fun z θ =>
  (1 / α) * Work.Construction.L12 g z * g z θ
    + (3 / (2 * α)) * Work.Construction.s2 θ * Work.Construction.L12 g z
      * Work.Spaces.pth g z θ
    - Work.Construction.c2m θ * Work.Construction.L12 g z * Work.Spaces.Dz g z θ

/-- The symmetric bilinear form of `Quad0`: `Quad0 α u = Bil0 α u u` and
`Quad0 α (u+d) = Quad0 α u + Bil0 α u d + Bil0 α d u + Quad0 α d` (the second identity needs the
additivity `L₁₂(u+d) = L₁₂u + L₁₂d`). -/
def Bil0 (α : ℝ) (u d : Fn) : Fn := fun z θ =>
  (1 / α) * Work.Construction.L12 u z * d z θ
    + (3 / (2 * α)) * Work.Construction.s2 θ * Work.Construction.L12 u z
      * Work.Spaces.pth d z θ
    - Work.Construction.c2m θ * Work.Construction.L12 u z * Work.Spaces.Dz d z θ

theorem Bil0_self (α : ℝ) (u : Fn) : Bil0 α u u = Quad0 α u := rfl

/-- **The `N₀` block is a degree-≤2 polynomial in the profile**, pointwise on the open
quadrant: `N₀ α (F_*+g) g = C0 α + Lin0 α g + Quad0 α g`. -/
theorem sn0_eq_sum {α : ℝ} {g : Fn} (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Sn0 α g z θ = (C0 α + Lin0 α g + Quad0 α g) z θ := by
  have hF : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
    Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_Fstar α
  intro z θ hz hθ0 hθ1
  have hpth : Work.Spaces.pth (Work.Construction.Ftot α g) z θ
      = Work.Spaces.pth (Work.Construction.Fstar α) z θ + Work.Spaces.pth g z θ :=
    Work.FTS.NonlinRows.Rl1.openSlice_pth_add hF hg hz ⟨hθ0, hθ1⟩
  have hDz : Work.Spaces.Dz (Work.Construction.Ftot α g) z θ
      = Work.Spaces.Dz (Work.Construction.Fstar α) z θ + Work.Spaces.Dz g z θ :=
    Work.FTS.Nonlinear.Pieces.Dz_add_of_diff
      (Work.FTS.NonlinRows.Rl1.openSlice_pz_add hF hg hz ⟨hθ0, hθ1⟩)
  simp only [Sn0_apply, C0, Lin0, Quad0, Pi.add_apply, Work.Construction.N0]
  rw [hpth, hDz]
  ring


/-! ## The `N` block -/

/-- The part of `Φ̃ = Φ − (1/(4α))·sin(2θ)·L₁₂(F)` that is *linear* in the profile `g`, when
`F = F_* + g` and `Φ = Φ_s + E g`: `U_g = E g − (1/(4α))·sin(2θ)·L₁₂(g)`. -/
def Ug (α : ℝ) (E : Fn → Fn) (g : Fn) : Fn := fun z θ =>
  E g z θ - (1 / (4 * α)) * Work.Construction.s2 θ * Work.Construction.L12 g z

/-- The `g`-independent part of `N α (F_*+g) (Φ_s + E g)`. -/
def C1 (α : ℝ) (Φs : Fn) : Fn := fun z θ =>
  2 * Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
      * Work.Construction.Fstar α z θ
    - 2 * Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
      * Work.Spaces.pth (Work.Construction.Fstar α) z θ
    - 2 * α * Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
      * Work.Spaces.Dz (Work.Construction.Fstar α) z θ
    - (1 / 2) * Work.Construction.s2 θ * Work.Construction.FK (Work.Construction.Fstar α) z
      * Work.Spaces.pth (Work.Construction.Fstar α) z θ
    - Real.sin θ ^ 2 * Work.Construction.FK (Work.Construction.Fstar α) z
      * Work.Construction.Fstar α z θ

/-- The part of `N α (F_*+g) (Φ_s + E g)` linear in `g`. -/
def Lin1 (α : ℝ) (Φs : Fn) (E : Fn → Fn) (g : Fn) : Fn := fun z θ =>
  2 * Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
      * g z θ
    - 2 * Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
      * Work.Spaces.pth g z θ
    - 2 * α * Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
      * Work.Spaces.Dz g z θ
    + 2 * Work.Construction.Rop α (Ug α E g) z θ * Work.Construction.Fstar α z θ
    - 2 * Work.Construction.Uop α (Ug α E g) z θ
      * Work.Spaces.pth (Work.Construction.Fstar α) z θ
    - 2 * α * Work.Construction.Vop (Ug α E g) z θ
      * Work.Spaces.Dz (Work.Construction.Fstar α) z θ
    - (1 / 2) * Work.Construction.s2 θ * Work.Construction.FK (Work.Construction.Fstar α) z
      * Work.Spaces.pth g z θ
    - Real.sin θ ^ 2 * Work.Construction.FK (Work.Construction.Fstar α) z * g z θ
    - (1 / 2) * Work.Construction.s2 θ * Work.Construction.FK g z
      * Work.Spaces.pth (Work.Construction.Fstar α) z θ
    - Real.sin θ ^ 2 * Work.Construction.FK g z * Work.Construction.Fstar α z θ

/-- The part of `N α (F_*+g) (Φ_s + E g)` quadratic in `g`. -/
def Quad1 (α : ℝ) (E : Fn → Fn) (g : Fn) : Fn := fun z θ =>
  2 * Work.Construction.Rop α (Ug α E g) z θ * g z θ
    - 2 * Work.Construction.Uop α (Ug α E g) z θ * Work.Spaces.pth g z θ
    - 2 * α * Work.Construction.Vop (Ug α E g) z θ * Work.Spaces.Dz g z θ
    - (1 / 2) * Work.Construction.s2 θ * Work.Construction.FK g z * Work.Spaces.pth g z θ
    - Real.sin θ ^ 2 * Work.Construction.FK g z * g z θ

/-- The symmetric bilinear form of `Quad1`: `Quad1 α E u = Bil1 α E u u` and
`Quad1 α E (u+d) = Quad1 α E u + Bil1 α E u d + Bil1 α E d u + Quad1 α E d` (the second identity
needs `E` additive, `L₁₂`-additivity on the profiles and the additivity of `Rop`, `Uop`, `Vop`,
`FK`, `pth`, `Dz` on the relevant sums). -/
def Bil1 (α : ℝ) (E : Fn → Fn) (u d : Fn) : Fn := fun z θ =>
  2 * Work.Construction.Rop α (Ug α E u) z θ * d z θ
    - 2 * Work.Construction.Uop α (Ug α E u) z θ * Work.Spaces.pth d z θ
    - 2 * α * Work.Construction.Vop (Ug α E u) z θ * Work.Spaces.Dz d z θ
    - (1 / 2) * Work.Construction.s2 θ * Work.Construction.FK u z * Work.Spaces.pth d z θ
    - Real.sin θ ^ 2 * Work.Construction.FK u z * d z θ

theorem Bil1_self (α : ℝ) (E : Fn → Fn) (u : Fn) : Bil1 α E u u = Quad1 α E u := rfl

end Work.FTS_MuLipC
