/-
# `Submission/Work/FTS_MuLipC/RowN/Defs.lean` — the atoms of the `N`-difference row

Setting: `α ∈ (0,1]`, a star stream function `Φs`, and an additive/homogeneous map
`E : Fn → Fn`.  The bilinear field of the row is

  `Sn α Φs E g = N α (F_* + g) (Φ_s + E g)`   (`Work.FTS_MuLipC.Sn`),

and the difference row `DiffRow1` asks for the Lipschitz bound of `g ↦ L₁₂(Sn α Φs E g)(0)`
in the `ℋ⁴`-norm, the constant depending only on `α, C₀, Ce, Cs`.

The route is the **polarization** of the quadratic map `g ↦ Sn α Φs E g`: `N` is a sum of
products of *affine* functions of the profile, so the field is `C + Lin + Quad` and hence

  `Sn f - Sn f' = (1/(4t)) • (Sn(u+td) - Sn(u-td) + Sn(td) - Sn(-td))`,   `u = f+f'`, `d = f-f'`,

which reduces the difference row to the *proved* single-profile row `KMu1_row` applied at the
four scaled profiles.

For the *field* identity one needs the product structure of `N`.  It is supplied here by the
twenty-piece split `Work.FTS.NonlinRows.Rl1.splitOpen`, whose summands are the products
`Work.FTS.Nonlin.N1gg, …, N5ss` — each of them a product `c · X(g) · Y(g)` of two of the
`Fn → Fn` *atoms* defined in this file:

| atom | meaning |
|---|---|
| `AtF` | `g` |
| `AtP` | `∂_θg` |
| `AtZ` | `D_zg` |
| `AtD` | `D_θg = sin(2θ) ∂_θg` |
| `AtK` | `(z,θ) ↦ FK g z` |
| `AtR` | `ℛ(Φ̃_g)` with `Φ̃_g = PhiTil α g (E g)` |
| `AtU` | `𝒰(Φ̃_g)` |
| `AtV` | `𝒱(Φ̃_g)` |

and of the *constants* `cF = F_*`, `cP = ∂_θF_*`, `cZ = D_zF_*`, `cK = FK F_*`,
`cR = ℛ(Φ̃_*)`, `cU = 𝒰(Φ̃_*)`, `cV = 𝒱(Φ̃_*)` (with `Φ̃_* = PhiTil α F_* Φ_s`), together with
the angular factors `sin(2θ)` and `sin²θ`.

The remaining ingredient, `L₁₂`-additivity on the *fields* `Sn α Φs E x`, is recorded in the
sibling file `L12Ae.lean` (`Work.FTS_MuLipC.RowN.L12_ae_sub`); the honesty (measurability and
integrability) of those fields is in `NHonest.lean` (`Work.FTS_MuLipC.RowN.N_honest`).
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS_MuLipC.Defs
import Submission.Work.FTS.NonlinRows.Rl1.splitOpen
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.Pvec

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_MuLipC.RowN

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## The elliptic residual of a perturbation -/

/-- `Φ̃_g = PhiTil α g (E g)`. -/
def PhiTilg (α : ℝ) (E : Fn → Fn) (g : Fn) : Fn :=
  fun z θ => E g z θ
    - (1 / (4 * α)) * Work.Construction.s2 θ * Work.Construction.L12 g z

/-- The star part `Φ̃_* = PhiTil α F_* Φ_s`. -/
def Zs (α : ℝ) (Φs : Fn) : Fn :=
  fun z θ => Φs z θ
    - (1 / (4 * α)) * Work.Construction.s2 θ
        * Work.Construction.L12 (Work.Construction.Fstar α) z

theorem Zs_eq_PhiTs (α : ℝ) (Φs : Fn) : Zs α Φs = Work.FTS.Nonlin.PhiTs α Φs := rfl

theorem PhiTilg_eq (α : ℝ) (E : Fn → Fn) (g : Fn) :
    PhiTilg α E g = Work.FTS.Nonlin.PhiTg α g (E g) := rfl

@[simp] theorem PhiTilg_apply (α : ℝ) (E : Fn → Fn) (g : Fn) (z θ : ℝ) :
    PhiTilg α E g z θ = E g z θ
      - (1 / (4 * α)) * Work.Construction.s2 θ * Work.Construction.L12 g z := rfl

@[simp] theorem Zs_apply (α : ℝ) (Φs : Fn) (z θ : ℝ) :
    Zs α Φs z θ = Φs z θ
      - (1 / (4 * α)) * Work.Construction.s2 θ
          * Work.Construction.L12 (Work.Construction.Fstar α) z := rfl

/-! ## The atoms -/

/-- The profile atom `g`. -/
def AtF (g : Fn) : Fn := g

/-- The angular derivative atom `∂_θg`. -/
def AtP (g : Fn) : Fn := Work.Spaces.pth g

/-- The radial atom `D_zg = z ∂_zg`. -/
def AtZ (g : Fn) : Fn := Work.Spaces.Dz g

/-- The weighted angular atom `D_θg = sin(2θ) ∂_θg`. -/
def AtD (g : Fn) : Fn := Work.Spaces.Dth g

/-- The angular moment atom `FK g`. -/
def AtK (g : Fn) : Fn := fun z _ => Work.Construction.FK g z

/-- The atom `ℛ(Φ̃_g)`. -/
def AtR (α : ℝ) (E : Fn → Fn) (g : Fn) : Fn :=
  Work.Construction.Rop α (PhiTilg α E g)

/-- The atom `𝒰(Φ̃_g)`. -/
def AtU (α : ℝ) (E : Fn → Fn) (g : Fn) : Fn :=
  Work.Construction.Uop α (PhiTilg α E g)

/-- The atom `𝒱(Φ̃_g)`. -/
def AtV (α : ℝ) (E : Fn → Fn) (g : Fn) : Fn :=
  Work.Construction.Vop (PhiTilg α E g)

/-! ## The constant parts -/

/-- `F_*`. -/
def cF (α : ℝ) : Fn := Work.Construction.Fstar α

/-- `∂_θF_*`. -/
def cP (α : ℝ) : Fn := Work.Spaces.pth (Work.Construction.Fstar α)

/-- `D_zF_*`. -/
def cZ (α : ℝ) : Fn := Work.Spaces.Dz (Work.Construction.Fstar α)

/-- `FK F_*`. -/
def cK (α : ℝ) : Fn := fun z _ => Work.Construction.FK (Work.Construction.Fstar α) z

/-- `ℛ(Φ̃_*)`. -/
def cR (α : ℝ) (Φs : Fn) : Fn := Work.Construction.Rop α (Zs α Φs)

/-- `𝒰(Φ̃_*)`. -/
def cU (α : ℝ) (Φs : Fn) : Fn := Work.Construction.Uop α (Zs α Φs)

/-- `𝒱(Φ̃_*)`. -/
def cV (α : ℝ) (Φs : Fn) : Fn := Work.Construction.Vop (Zs α Φs)

end Work.FTS_MuLipC.RowN
