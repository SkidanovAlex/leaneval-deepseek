import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.NSplit6
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.IP6UnfoldCd6
import Submission.Work.FTS.StrongPersist.N6Trans_exists
import Submission.Work.FTS.TransportS.Slots

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork

open scoped Real Topology
open MeasureTheory Set Filter

/-! ### The free parameter `Ce` of the statement

The requested statement mentions `Ce` (the perturbation constant of `L6Ctx`) without binding it
in its binder list — Lean's `autoImplicit` would bind it as the *implicit* universally
quantified variable `{Ce : ℝ}`, which is exactly what the `variable` declaration below does,
with the statement left character for character as requested. -/
variable {Ce : ℝ}

/-- **The pairing of the `N`-row against the datum, priced by the per-slot bound, at the
finite smoothness order `C⁶`.**

This is the sibling of `Npair6BWork.pairing_le_of_slotBound`, with the hypothesis
`SmoothOpen (nsum α (g τ) (E (g τ)) Φs)` (`C^∞` on the open quadrant) weakened to
`ContDiffOn ℝ 6 (uncurry (nsum …)) Q0`.  The only place where the smoothness order was used is
the level-six unfolding of the coercive recursion, and the finite-order version
`Npair6SupAux.IP6UnfoldCd6` supplies exactly `C⁶`:

  `|IP6 1…1 α u v| ≤ C · SlotSum α 6 u v`   for `u, v` of class `C⁶` on the open quadrant.

The rest of the argument is unchanged: `IP6 1…1` unfolds into the level-six slot sum
(`IP6UnfoldCd6`), which is bounded by `84·B` once every one of the leaf slot pairings is
bounded by `B` (`StrongPersist.SlotSum_six_le`); and the nonlinearity
`N α (F_* + g(τ)) (Φs + E(g(τ)))` is replaced by the twenty-piece sum `nsum` of
`Npair6SupAux` on the open quadrant (`NSplit6`), the equality of the two pairings being the
congruence `IP6_congr` on the (co-null) open quadrant.

The three smoothness facts used are: the datum `g(τ)` is smooth (`L6Ctx.hreg.reg.1`), the
perturbation stream function `E(g(τ))` is smooth (`EllPkgK.smooth` through `Ell6Ctx.hell`) and
the star profile `Φs` is smooth (`StarPkgo.smooth` through `Ell6Ctx.hstar`). -/
theorem pairing_le_of_slotBoundB : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (g Φ : Work.FTS.Galerkin.Fam) (τ M Cs : ℝ)
      (E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn) (Φs : Work.FTS.Galerkin.Fn) (B : ℝ),
      0 ≤ τ →
      Work.FTS.StrongPersist.L6Ctx (Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1)
        α M Ce Cs E Φs g Φ τ →
      ContDiffOn ℝ 6
        (Function.uncurry (Work.FTS.StrongPersist.H6Rows.Npair6SupAux.nsum α
          (Work.FTS.Galerkin.slice g τ) (E (Work.FTS.Galerkin.slice g τ)) Φs))
        Work.FTS.EllipticEst.Q0 →
      0 ≤ B →
      (∀ (a b : ℕ) (ρ : ℝ → ℝ → ℝ), a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
          |Work.FTS.TransportS.slotPairing ρ a b
            (Work.FTS.StrongPersist.H6Rows.Npair6SupAux.nsum α (Work.FTS.Galerkin.slice g τ)
              (E (Work.FTS.Galerkin.slice g τ)) Φs)
            (Work.FTS.Galerkin.slice g τ)| ≤ B) →
      |Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α
          (Work.Construction.N α (Work.Construction.Ftau α g τ) (Work.FTS.Galerkin.slice Φ τ))
          (Work.FTS.Galerkin.slice g τ)| ≤ C * B := by
  obtain ⟨CIP, hCIPpos, hIP6u⟩ := Work.FTS.StrongPersist.H6Rows.Npair6SupAux.IP6UnfoldCd6
  refine ⟨CIP * 84, by nlinarith [hCIPpos], ?_⟩
  intro α hα g Φ τ M Cs E Φs B hτ hctx hsm hB0 hslot
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  -- smoothness of the three ingredients
  have hfsm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Galerkin.slice g τ) := hctx.hreg.reg.1
  have hEsm : Work.FTS.EllipticEst.SmoothOpen (E (Work.FTS.Galerkin.slice g τ)) :=
    hctx.hell.hell.smooth
  have hPsm : Work.FTS.EllipticEst.SmoothOpen Φs := hctx.hell.hstar.smooth
  have hfsm6 : ContDiffOn ℝ 6
      (Function.uncurry (Work.FTS.Galerkin.slice g τ)) Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall (Work.FTS.Galerkin.slice g τ)).mp hfsm 6
  -- the twenty-piece splitting of the nonlinearity
  have hsplit := Work.FTS.StrongPersist.H6Rows.Npair6SupAux.NSplit6 hα0 hα1
    (f := Work.FTS.Galerkin.slice g τ) (Ef := E (Work.FTS.Galerkin.slice g τ)) (Φs := Φs)
    hctx.hreg hEsm hPsm
  -- the pairing only sees `nsum` (the two profiles agree on the open quadrant)
  have hgoal :
      Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α
          (Work.Construction.N α (Work.Construction.Ftau α g τ) (Work.FTS.Galerkin.slice Φ τ))
          (Work.FTS.Galerkin.slice g τ)
        = Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α
            (Work.FTS.StrongPersist.H6Rows.Npair6SupAux.nsum α (Work.FTS.Galerkin.slice g τ)
              (E (Work.FTS.Galerkin.slice g τ)) Φs) (Work.FTS.Galerkin.slice g τ) := by
    rw [hctx.hell.hsum]
    exact hsplit.2 (Work.FTS.Galerkin.slice g τ)
  -- the level-six unfolding at finite order
  have hIP := hIP6u α
    (Work.FTS.StrongPersist.H6Rows.Npair6SupAux.nsum α (Work.FTS.Galerkin.slice g τ)
      (E (Work.FTS.Galerkin.slice g τ)) Φs)
    (Work.FTS.Galerkin.slice g τ) hsm hfsm6
  -- the slot sum
  have hsl := Work.FTS.StrongPersist.SlotSum_six_le α
    (Work.FTS.StrongPersist.H6Rows.Npair6SupAux.nsum α (Work.FTS.Galerkin.slice g τ)
      (E (Work.FTS.Galerkin.slice g τ)) Φs)
    (Work.FTS.Galerkin.slice g τ) B hB0 hslot
  calc
    |Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α
        (Work.Construction.N α (Work.Construction.Ftau α g τ) (Work.FTS.Galerkin.slice Φ τ))
        (Work.FTS.Galerkin.slice g τ)|
        = |Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α
            (Work.FTS.StrongPersist.H6Rows.Npair6SupAux.nsum α (Work.FTS.Galerkin.slice g τ)
              (E (Work.FTS.Galerkin.slice g τ)) Φs) (Work.FTS.Galerkin.slice g τ)| := by
          rw [hgoal]
    _ ≤ CIP * Work.FTS.TransportS.SlotSum α 6
            (Work.FTS.StrongPersist.H6Rows.Npair6SupAux.nsum α (Work.FTS.Galerkin.slice g τ)
              (E (Work.FTS.Galerkin.slice g τ)) Φs) (Work.FTS.Galerkin.slice g τ) := hIP
    _ ≤ CIP * (84 * B) := by
          refine mul_le_mul_of_nonneg_left hsl ?_
          linarith [hCIPpos]
    _ = (CIP * 84) * B := by ring

end Work.FTS.StrongPersist.H6Rows.Npair6BWork
