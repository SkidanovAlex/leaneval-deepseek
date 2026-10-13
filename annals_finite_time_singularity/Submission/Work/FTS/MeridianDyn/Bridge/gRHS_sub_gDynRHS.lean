import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.Ring.RingNF
import Submission.Work.FTS.MeridianDyn.Defs
import Submission.Work.Stability.Defs
import Submission.Work.Construction.Equation
import Submission.Work.Construction.Basic
import Submission.Work.FTS.Galerkin.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.MeridianDyn.Bridge

open scoped Real Topology

/-- **The bridge identity of the dynamic meridian reduction**: the *stationary* `g`-right-hand
side `gRHS` at the τ-dependent modulation constants `(μ̄(τ), λ(τ))` differs from the *dynamical*
one `gDynRHS` of the Stability layer by exactly the `AK`-multiple

`(2αμ̄(τ) − μ̄ − L₁₂(Transport g)(0)) · AK`,

which is the forcing that the reference-rate reduction produces (`F_* − D_zF_* = 2α·AK`) once
the paper's choice `λ = -2μ/(1+μ)` (i.e. `μ+λ+μλ = -μ`, the dictionary `κ*b* = 1-μ`) is used.

The proof is pointwise algebra: both sides carry the same `N₀`, `N` and `N_*` terms
(`Ftot α g τ` and `Ftau α g τ` are the same function), so only the `F_*`/`D_zF_*` forcing and the
`AK·L₁₂(Transport g)(0)` term survive; the substitutions `κ = 1+μ`, `b = 1+λ`, `μ+λ+μλ = -μ` and
`D_zF_* = F_* − 2α·AK` reduce the difference to the stated `AK`-coefficient.

**No change is needed for the sign fix.**  The statement is *generic* in `muDyn` (the modulation
constant enters only as the opaque function `Work.FTS.Galerkin.muDyn α Φ g`), so it stays true
verbatim when `muDyn` becomes `Construction.mufunS`; what changes is that the `AK`-coefficient
`2α·muDyn − μ̄ − L₁₂(Transport g)(0)` is now *identically zero* (`two_mul_muDyn`,
`FTS_MUFUN_SIGN.md` §5) — which is exactly why the defect hypothesis disappears from `DynEqF` and
`Main`.  The only edit here is this docstring. -/
theorem gRHS_sub_gDynRHS {α : ℝ} (hα : 0 < α) {g Φ : Work.FTS.MeridianDyn.Fam}
    {M : Work.Stability.ModState} {z θ τ : ℝ} (hz : -1 < z)
    (hne : 1 + Work.FTS.Galerkin.muDyn α Φ g τ ≠ 0)
    (hκ : M.kappa τ = 1 + Work.FTS.Galerkin.muDyn α Φ g τ)
    (hb : M.b τ = 1 + Work.FTS.Galerkin.lamDyn α Φ g τ) :
    Work.Construction.gRHS α (Work.FTS.Galerkin.muDyn α Φ g τ)
        (Work.FTS.Galerkin.lamDyn α Φ g τ) (Work.Construction.Ftau α g τ)
        (Work.FTS.Galerkin.slice Φ τ) (Work.FTS.Galerkin.slice g τ) z θ
      - Work.Stability.gDynRHS α M g Φ z θ τ
      = (2 * α * Work.FTS.Galerkin.muDyn α Φ g τ
            - Work.Construction.mubar
                (Work.Construction.N0 α (Work.Construction.Ftau α g τ)
                  (Work.FTS.Galerkin.slice g τ))
                (Work.Construction.N α (Work.Construction.Ftau α g τ)
                  (Work.FTS.Galerkin.slice Φ τ))
            - Work.Construction.L12 (Work.Coercivity.Transport
                (Work.FTS.Galerkin.slice g τ)) 0)
          * Work.Construction.AK α z θ := by
  -- the paper's choice `λ = -2μ/(1+μ)`: the dictionary identity `μ + λ + μλ = -μ`.
  have hlam : Work.FTS.Galerkin.muDyn α Φ g τ
      + Work.Construction.lamfun (Work.FTS.Galerkin.muDyn α Φ g τ)
      + Work.FTS.Galerkin.muDyn α Φ g τ
        * Work.Construction.lamfun (Work.FTS.Galerkin.muDyn α Φ g τ)
      = -Work.FTS.Galerkin.muDyn α Φ g τ := by
    rw [Work.Construction.lamfun]
    field_simp
    ring
  -- `κ - 1 = μ`
  have hκ' : M.kappa τ - 1 = Work.FTS.Galerkin.muDyn α Φ g τ := by rw [hκ]; ring
  -- `b - 1 = λ`
  have hb' : M.b τ - 1 = Work.FTS.Galerkin.lamDyn α Φ g τ := by rw [hb]; ring
  -- `κ b - 1 = -μ` (the dictionary `κ* b* = 1 - μ` at the dynamical rates).
  have hkb : M.kappa τ * M.b τ - 1 = -Work.FTS.Galerkin.muDyn α Φ g τ := by
    have h2 : Work.Construction.lamfun (Work.FTS.Galerkin.muDyn α Φ g τ)
        = Work.FTS.Galerkin.lamDyn α Φ g τ := rfl
    rw [hκ, hb, ← h2]
    nlinarith [hlam]
  -- `D_z F_* = F_* - 2α·AK`.
  have hDz : Work.Spaces.Dz (Work.Construction.Fstar α) z θ
      = Work.Construction.Fstar α z θ - 2 * α * Work.Construction.AK α z θ := by
    have h := Work.Construction.Fstar_sub_DzFstar (α := α) (z := z) (θ := θ) hα hz
    linarith
  -- unfold the two right-hand sides.
  simp only [Work.Construction.gRHS, Work.Stability.gDynRHS]
  -- rewrite the definitionally-equal vocabulary of the two layers.
  rw [show Work.Stability.Ftot α g τ = Work.Construction.Ftau α g τ from rfl,
    show Work.Stability.slice g τ = Work.FTS.Galerkin.slice g τ from rfl,
    show Work.Stability.slice Φ τ = Work.FTS.Galerkin.slice Φ τ from rfl]
  -- substitute the four identities and close by polynomial algebra.
  rw [hkb, hκ', hb', hDz]
  ring

end Work.FTS.MeridianDyn.Bridge
