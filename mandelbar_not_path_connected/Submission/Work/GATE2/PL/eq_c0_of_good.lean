import Mathlib
import Submission.Work.GATE2.PL.Defs
import Submission.Work.GATE2.PL.Main
import Submission.Work.GATE2.PL.eq_v_of_eq_c0
import Submission.Work.GATE2.PL.ne_iterate_crit
import Submission.Work.GATE2.PL.isCoveringMapOn_tantibar_five
import Submission.Work.GATE2.PL.UCore
import Submission.Work.GATE2.PL.Uavoid
import Submission.Work.GATE2.PL.Good_eq
import Submission.Work.GATE2.PL.Urec
import Submission.Work.GATE2.PL.Uhol
import Submission.Work.GATE2.PL.analytic_shift
import Submission.Work.GATE2.PL.deriv_tsqIterate_ne_zero_of_iterate_ne_zero

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.GATE2.PL

/-- **The principal Fatou parametrisation of the `c₀`-flower passes through the critical value**
(the design's §4.1 of `NOTES_LEAD_mandelbar_gate2transport.md`).

Let `fl` be the Leau–Fatou flower of `F = Work.EL.F c₀ = (T_{c₀})^[10]` at the parabolic point
`d.z₁`, with antiholomorphic square root `G5 c₀ = (T_{c₀})^[5]`; let `FF` be the `FatouCoord` fix
(`φa ∘ F = φa + 1` on `fl.Pa`, with the invariant sub-petal `FF.Pg ⊆ fl.Pa`), and let `Ψs : ℂ → ℂ`
be a **continuous** function on the slit plane `slitAt v = ℂ \ (−∞, v − 1/2]` which
* intertwines `G5 c₀` with `sig w = w̄ + 1/2`: `G5 c₀ (Ψs w) = Ψs (sig w)` for `w ∈ slitAt v`,
* is the inverse of the Fatou coordinate far to the right: for `X < Re w`,
  `Ψs w ∈ FF.Pg` and `fl.φa (Ψs w) = w`.

Then `Ψs v = c₀` (where `v` is the real number of the hypothesis `hv`).

Proof plan (suppose `Ψs v ≠ c₀` and derive a contradiction):
1. *No obstruction.*  The branch points of the half-step lift through `G5 c₀` are its critical
   values `critVals = {T^[j] c₀ : 0 ≤ j ≤ 4}`.  `Ψs w = T^[j] c₀` with `1 ≤ j ≤ 4` is impossible
   (`ne_iterate_crit`, via the equivariant shifts: `F^[n] (T^[j] c₀) = T^[10n+j] c₀ ∈ fl.Pa` would
   force `T^[j] z₁ = z₁`, contradicting the exact period `5` of `z₁`), and `Ψs w = c₀` forces
   `w = v` (`eq_v_of_eq_c0`), hence `Ψs v = c₀`, excluded.
2. *Global extension.*  Repeat the lift-step recursion of
   `Submission/Work/GATE2/PL/Main.lean` (`exists_step_of_avoid`, the recursive `seqGood`, and
   `Psi`), but over the domains without a cut: `U_k := {w : X − k/2 < w.re}` (each an open convex
   set, hence simply connected and locally path connected: use
   `convex_halfSpace_re_gt`/`StarConvex.contractibleSpace` and
   `IsOpen.locallyPathConnectedSpace`), noting `sig '' U_{k+1} ⊆ U_k`, `{Re > X} ⊆ U_k` and
   `⋃ U_k = ℂ`.  `IsCoveringMapOn.existsUnique_continuousMap_lifts` applied to
   `isCoveringMapOn_tantibar_five c₀` gives at each step a lift agreeing with the previous one.
   The result is `Ψg : ℂ → ℂ` with `G5 c₀ (Ψg w) = Ψg (sig w)` for all `w` (hence
   `F (Ψg w) = Ψg (w+1)` for all `w`, since `F = G5 c₀ ∘ G5 c₀`), continuous everywhere,
   `Ψg = Ψs` on `slitAt v`, and `Ψg w ∈ FF.Pg`, `fl.φa (Ψg w) = w` for `X < Re w`.
3. *Holomorphy.*  `Ψg` is holomorphic on `{Re > X}`: there it is the inverse of the holomorphic
   injective `φa` on `FF.Pg ⊆ fl.Pa` (a local analytic inverse).  Holomorphy propagates one unit
   leftwards: if `Ψg` is holomorphic near `w+1` then near `w` it equals `ρ (Ψg (·+1))` with `ρ` the
   local analytic inverse of the polynomial `F` at `Ψg w` (`F` is `Tsq^[5]`, Mathlib's
   `HasStrictDerivAt.localInverse`); this needs `deriv F (Ψg w) ≠ 0`.  For that, show `Ψg` avoids
   `critVals` (part 1), and `deriv F z = 0` implies `z ∈ crit (G5 c₀) ∪ (G5 c₀)⁻¹ (crit (G5 c₀))`
   (chain rule), from which `Ψg` hits `critVals` — contradiction.  Alternatively use the
   antiholomorphic local inverse of `G5 c₀` directly (its regular values are exactly `critVals`).
   Since every `w` satisfies `w + n ∈ {Re > X}` for large `n`, `Ψg` is entire.
4. *Boundedness.*  `F^[n] (Ψg w) = Ψg (w + n) ∈ FF.Pg ⊆ fl.Pa ⊆ Work.EL.K c₀` for `n` large, and
   `K c₀` is completely invariant under `T_{c₀}` (hence under `F`) and bounded
   (`Work.ParamRays.filledJulia`, `Work.ParamRays.norm_le_max_of_bounded`,
   `Work.ParamRays.BoundedOrbit.shift`).
5. *Liouville.*  A bounded entire function is constant
   (`Differentiable.exists_eq_const_of_bounded`), contradicting injectivity on the half-plane: for
   `w ≠ w'` with `X < Re w, Re w'`, `φa (Ψg w) = w ≠ w' = φa (Ψg w')`. -/
theorem eq_c0_of_good {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    {fl : Work.EL.ParabolicFlower (Work.EL.F c₀) (Work.GATE2.PL.G5 c₀) d.z₁}
    {FF : Work.PARIMPL.FlowerFix d (Work.EL.F c₀) (Work.GATE2.PL.G5 c₀) d.z₁ fl.Pa fl.φa}
    (hK : fl.Pa ⊆ Work.EL.K c₀)
    {v X : ℝ} (hX : v - 1 / 2 ≤ X)
    (hv : ∃ N : ℕ, (Work.EL.F c₀)^[N] c₀ ∈ fl.Pa ∧
      fl.φa ((Work.EL.F c₀)^[N] c₀) = (((v + N : ℝ)) : ℂ))
    {Ψs : ℂ → ℂ}
    (hanti : ∀ w : ℂ, w ∈ Work.GATE2.slitAt v → Work.GATE2.PL.G5 c₀ (Ψs w) = Ψs (Work.GATE2.PL.sig w))
    (hfar : ∀ w : ℂ, X < w.re → Ψs w ∈ FF.Pg ∧ fl.φa (Ψs w) = w)
    (hcont : ContinuousOn Ψs (Work.GATE2.slitAt v)) :
    Ψs (v : ℂ) = c₀ := by
  by_contra hne
  -- The recursion of `PL/Urec` runs at every level under the negation of the conclusion, and
  -- produces the global extension `PsiU` of `Ψs`.
  have S : Seed fl FF v X Ψs := ⟨hX, hanti, hfar, hcont, hv, hne⟩
  -- `PsiU` is differentiable on `ℂ` and bounded, hence constant by Liouville; on the half-plane
  -- `{Re > X}` it is injective (`φa (PsiU w) = w`), which is impossible.
  exact PsiU_not_bounded_differentiable fl FF S
    ⟨PsiU_differentiable fl FF S,
      ⟨max 2 ‖c₀‖, fun w => PsiU_norm_le fl FF S hK w⟩⟩

end Work.GATE2.PL
