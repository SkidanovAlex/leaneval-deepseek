import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.lpSpace
import Submission.Work.BoseBoxFock.KafzHonest
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.KzOpC` — the spectator (`c`-number) form `KzOpC` of `KzOpFS`

`KzOpFS F T E gHat0 ρ` (FS `eq:Kz`) is an operator on `F.H = RealFock m`, the Fock
space of the `m` box modes *including the condensate coordinate* `0`.  On the
subspace of zero condensate (`split x = Finsupp.single 0 v`) it acts as

    split (KzOpFS … ρ x) = (monoOp 1 1 ((b/2ℓ²):ℂ) + monoOp 0 0 (KzOpC … ρ)) (split x),

so evaluating at `Finsupp.single 0 v` gives `single 0 (KzOpC … ρ v)`, and
`bomb m f (KzOpFS … ρ f) = ⟪v, KzOpC … ρ v⟫.re` for `split f = single 0 v`.

This file contains the **definition** `KzOpC` (and its row-wise constituents
`nOpC`, `nPlusC`, `KzBogC`, `linOpTC`, `Q2exC`, `Q3TC`), which is the operator the
symbol comparison of `KAFZ_HONEST_ROUTE.md` §2 / `KAFZ_STATUS2.md` §2 is stated
against.  The transport itself is `split_KzOpFS` / `bomb_KzOpC` (see the route notes).
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseBoxFock

open Work.BoseB4

set_option autoImplicit false
set_option linter.unusedVariables false

variable {m : ℕ} [NeZero m]

/-! ## 1. The number-type spectators -/

/-- The spectator number operator of a single superposition mode `φ`: `a_φ^C† a_φ^C`. -/
noncomputable def nOpC (φ : Fin m → ℝ) : cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  (creOfE φ).comp (annOfE φ)

/-- The excited number `n₊` in the spectator space: `Σ_{l ≠ 0} a_l^C† a_l^C`.  (Same
normal form as `KafzDict.Bgap` / `KafzHonest.split_excited_number`.) -/
noncomputable def nPlusC : cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  ∑ l : Excited m, (1 : ℂ) • ((creC (Excited m) l).comp (annC (Excited m) l))

/-! ## 2. The row-wise spectators -/

/-- FS `eq:BogHamPositive-1` on the spectator space (`KzBogFS` with
`F.a k ↦ annOfE (f k)`, `F.aDag k ↦ creOfE (f k)`, `F.nOp k ↦ nOpC (f k)`). -/
noncomputable def KzBogC {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (f : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode) (ρ : ℝ) :
    cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  ∑ k : Mode, ((1 / 2 : ℝ) : ℂ) •
    ((((E.tau k + ρ * E.W1 k : ℝ)) : ℂ) • (nOpC (f k) + nOpC (f (-k)))
      + (((ρ * E.W1 k : ℝ)) : ℂ) •
          ((annOfE (f k)).comp (annOfE (f (-k)))
            + (creOfE (f k)).comp (creOfE (f (-k))))
      + (((((ρ - E.mu) * E.W1 0 * E.hatChi k * Real.sqrt (ρ * E.ell ^ 3)) : ℝ)) : ℂ) •
          (annOfE (f k) + creOfE (f k) + annOfE (f (-k)) + creOfE (f (-k))))

/-- FS's linear term (`TildeData.linOpT`) on the spectator space: `T.ta s ↦ annOfE (g s)`,
`T.taDag s ↦ creOfE (g s)`. -/
noncomputable def linOpTC {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (g : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode) :
    cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  (((E.rho * E.z * E.W1omega0 : ℝ)) : ℂ) •
    ∑ s ∈ Work.BoseB7.excited Mode, (((E.hatChiSq s : ℝ)) : ℂ) •
      (creOfE (g s) + annOfE (g s))

/-- FS's `𝒬₂^{ex}` (`FockData.Q2ex`) on the spectator space. -/
noncomputable def Q2exC {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode) :
    cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  ∑ k ∈ Work.BoseB7.excited Mode,
    ((((E.rho * (E.W1omega k + E.W1omega0)) : ℝ)) : ℂ) • nOpC (f k)

/-- FS `eq:kroelleQ3z` (`TildeData.Q3T`) on the spectator space. -/
noncomputable def Q3TC {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f g : Mode → Fin m → ℝ) (F : Work.BoseB7.FockData Mode) (E : Work.BoseB7.Q3Env Mode) :
    cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  (((E.z / E.ell ^ 3 : ℝ)) : ℂ) •
    ∑ s ∈ Work.BoseB7.excited Mode, ∑ k ∈ F.PHset E,
      ((((E.fL s * E.W1 k) : ℝ)) : ℂ) •
        ((creOfE (g s)).comp ((annOfE (f (s - k))).comp (annOfE (f k)))
          + (creOfE (f k)).comp ((creOfE (f (s - k))).comp (annOfE (g s))))

/-! ## 3. The spectator form of `KzOpFS` -/

/-- **FS `eq:Kz` on the zero-condensate slice** (the spectator form of `KzOpFS`):
the same eight rows with every mode operator replaced by its `annOfE`/`creOfE`
image and the total number `T.N` replaced by the excited number `nPlusC`. -/
noncomputable def KzOpC {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f g : Mode → Fin m → ℝ) (BNH : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
    (F : Work.BoseB7.FockData Mode) (E : Work.BoseB7.Q3Env Mode) (gHat0 ρ : ℝ) :
    cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  ((((E.b / (2 * E.ell ^ 2) : ℝ)) : ℂ) • (nPlusC (m := m))
  + ((((E.eT * E.b / (2 * E.d ^ 2 * E.ell ^ 2) : ℝ)) : ℂ) • BNH)
  + ((((E.ell ^ 3 * (-(1 / 2) * E.mu ^ 2 * gHat0 + (1 / 2) * (ρ - E.mu) ^ 2 * gHat0
        + (1 / 2) * ρ ^ 2 * E.W1omega0) : ℝ)) : ℂ) •
      (1 : cfock (Excited m) →ₗ[ℂ] cfock (Excited m)))
  + KzBogC f E ρ
  + ((((ρ - E.mu) * E.W1 0 : ℝ)) : ℂ) • ∑ k : Mode, nOpC (f k)
  + linOpTC g (Work.BoseFixR.KzEnvAt E ρ)
  + Q2exC f (Work.BoseFixR.KzEnvAt E ρ)
  + Q3TC f g F (Work.BoseFixR.KzEnvAt E ρ))

end Work.BoseBoxFock
