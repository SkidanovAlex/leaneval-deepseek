/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsMem.lean` — the *honest* uniform `ε`-interface

The verbatim interface `EpsUniform` of the design (`Submission/Work/FTS/StrongEps/Basic.lean`) says
that for every `T > 0` and all small `ε` the scheme has a solution whose **weighted `L²`-sizes**
`Xn α (slice (Jfam ρ ε g) τ)` and `Xn6 α (slice g τ)` are bounded.

In Mathlib the weighted `L²`-size is a Bochner integral, so for an integrand which is *not*
integrable it is the junk value `0`; a *bound* on it therefore carries no information about
integrability.  Two items of E5 genuinely need the integrability (`HkMem`), not only the bound:

* the interior Arzelà–Ascoli extraction `exists_locUnif_subseq_of_uniform_H6` consumes
  `HkMem α 6 (slice g k τ)` (`hmem`), because its first step turns the *bound* `HkNorm α 6 ≤ B`
  into local `L²`-bounds for the plane derivatives;
* the `dbd` clause of the limit package needs the honest membership of the mollified slices for the
  level-three estimate `S6`/`L3Data`.

This module therefore records the **stronger** interface `EpsUniformMem`, which adds the two
membership clauses to the conclusion of `EpsUniform`.  It is the interface that the *provable*
route uses (`EpsUniformMem.exists_lim` in `Submission/Work/FTS/StrongEps/EpsLimit.lean`), and it
*does not* imply the verbatim one: after the `P₀` repair the two interfaces are stated for
*different* schemes (`IsEpsSolP` vs `IsEpsSol`), so the former transfer
`EpsUniformBd.to_uniform`/`EpsUniformMem.to_uniform` no longer exists (it was removed from
`EpsBd.lean`).  The verbatim `EpsUniform` survives only in the statement file; the proof path is
`EpsUniformMem`.

*Design note for the lead.*  `EpsUniformMem` is not a cosmetic strengthening: `EpsUniform` alone
does **not** give the extraction (its bounds can hold vacuously on junk integrals), and no argument
in the current scheme recovers `HkMem` from a bound.  The pipeline is therefore: data +
elliptic layer → `EpsUniform_of_data` producing `EpsUniformMem` → `EpsUniformMem.exists_lim` →
`Assembly.global_strong2_mem`.  The verbatim `global_strong2` (with `EpsUniform`) is retained for
the statement file, and its skeleton `EpsUniform.exists_lim` is exactly the missing link
(`EpsUniform → EpsUniformMem` would have to come from the scheme's own construction).
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.ClassC.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-- **The slot bound of the decay clause**: the majorant `Maj` dominates every mixed slot
`D_z^jD_θ^i f` of order `j + i ≤ k` on the open quadrant. -/
def SlotMaj (k : ℕ) (Maj : ℝ → ℝ) (f : ℝ → ℝ → ℝ) : Prop :=
  ∀ z ∈ Set.Ioi 0, ∀ θ : ℝ, ∀ j i : ℕ, j + i ≤ k →
    |Work.Spaces.mixed j i f z θ| ≤ Maj z

/-- **The radial slot-decay clause of `EpsUniformMem`** (fifth interface repair; the lead's ruling
(G-B)).

The identification `hlim` of E5 (`epsRHSP … → rhsFun …`) has one step which is *not* a continuity
statement: the modulation constants `muDyn`/`lamDyn` are defined through the **zero modes**
`L₁₂(Y)(0) = ∫_0^∞ (1/s)∫_θ K(θ)Y(s,θ) dθ ds` (`Construction.mufunS`), and `L₁₂(·)(0)` is a bounded
functional on `ℋ⁴` (`OpenPkg.l12zero_field`) but *not* continuous along a locally uniformly
convergent sequence with uniform `ℋ⁴`/`ℋ⁶`-bounds: `Xn α (Y_n − Y) ↛ 0`.  The provable route — the
one the frozen `GalLimit` route also *assumes* under the names N1/N5 — is dominated convergence in
the radial variable, which needs a *majorant* `Maj` with `∫_0^∞ Maj(s)/s ds < ∞`, uniform in `ε`.

This definition names that clause.  `Maj` dominates the mixed slots of order `≤ 1` of the projected
slice `P₀ J_ε g(τ)`; the three elliptic blocks of `N α F Φ` (which is where the elliptic solution
`E (P₀ J_ε g(τ))` enters the right-hand side through `PhiTil`) are only **bounded, by the constant
`3`, on the open quadrant** (curric-46 repair 2026-10-12, `cbc/fts_e5swap_e4chapters.md` §B1 and
its REVIEW: the former clause "blocks `≤ Maj`" is refuted on the route — the explicit `Θ(F_*)` part
makes `|Uop/sin 2θ| ≥ 1` on all of `(0,1/10)`, so no `Maj` with `∫ Maj/z < ∞` dominates it
(`EpsE4Thr.C46B.not_EpsDecay`).  The blocks multiply slots of `F = F_* + W`, whose `F_*`-part is
`O(z/(1+z)²)` and whose `W`-part is `≤ Maj`, so a constant bound suffices for E5).  The clauses `0 ≤ Maj`,
`Maj ≤ 1` and the integrability of `Maj z / z` are part of it, so that *every* polynomial
combination of the slots which occurs in `N₀`, `N` and `Transport` is dominated by a fixed multiple
of `Maj` (+ the decaying `F_*`-slots) (the powers `Maj^k`, `k ≥ 1`, are dominated by `Maj` because `Maj ≤ 1`), and the three
zero-mode integrands are then dominated by multiples of `Maj(s)/s`.

The cap of the majorant is `Maj ≤ 1`.

Why these five profiles: the right-hand side of the scheme is
`dynLin α g τ + dynRHS α (PsiCan Φs E g) g τ`, and `mufunS` reads off the three zero modes of
`N₀ α (Ftau α g τ) (slice g τ)`, `N α (Ftau α g τ) (slice (PsiCan Φs E g) τ)` and
`Transport (slice g τ)`.  In `N` only the *values* of `Rop`, `Uop/sin 2θ`, `Vop` of
`PhiTil α (Ftau) (slice (PsiCan …))` occur, together with the slots of `F = F_* + g` of order `≤ 1`;
in `N₀` only the slots of `F` of order `≤ 1` occur (the `F_*`-terms are fixed and decaying), and
`Transport f = 3 D_θ f/(1+z)` is of order `≤ 1` in `f`.  The fixed profile `F_* = α(Γ/c)·2z/(1+z)²`
decays like `z^{-1}` and its `L₁₂`-mode is `2α/(1+z)` (`Construction.L12_Fstar`) — no hypothesis is
needed for those. -/
def EpsDecay (α : ℝ) (ρ : ℝ × ℝ → ℝ) (Φs : Fn) (E : Fn → Fn) (ε τ : ℝ) (g : Fam)
    (Maj : ℝ → ℝ) : Prop :=
  (∀ z, 0 ≤ Maj z) ∧ (∀ z, Maj z ≤ 1) ∧
    MeasureTheory.IntegrableOn (fun z => Maj z / z) (Set.Ioi 0) ∧
    SlotMaj 1 Maj (slice (JfamP ρ ε g) τ) ∧
    ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      |Work.Construction.Rop α (Work.Construction.PhiTil α (slice (JfamP ρ ε g) τ)
          (slice (Work.FTS.Nonlin.PsiCan Φs E (JfamP ρ ε g)) τ)) z θ| ≤ 3 ∧
      |Work.Construction.Uop α (Work.Construction.PhiTil α (slice (JfamP ρ ε g) τ)
          (slice (Work.FTS.Nonlin.PsiCan Φs E (JfamP ρ ε g)) τ)) z θ
          / Work.Construction.s2 θ| ≤ 3 ∧
      |Work.Construction.Vop (Work.Construction.PhiTil α (slice (JfamP ρ ε g) τ)
          (slice (Work.FTS.Nonlin.PsiCan Φs E (JfamP ρ ε g)) τ)) z θ| ≤ 3

def EpsUniformMem (α : ℝ) (ρ : ℝ × ℝ → ℝ) (Φs : Fn) (E : Fn → Fn) (g₀ : Fn)
    (C₀ K : ℝ) : Prop :=
  (∀ z, 0 ≤ z → g₀ z 0 = 0 ∧ g₀ z (π / 2) = 0) ∧ Work.Construction.L12 g₀ 0 = 0 ∧
    ∀ T > 0, ∃ K' : ℝ, K ≤ K' ∧ ∃ ε₁ > 0, ∃ Maj : ℝ → ℝ,
      MeasureTheory.IntegrableOn (fun z => Maj z / z) (Set.Ioi 0) ∧
      ∀ ε ∈ Set.Ioc 0 ε₁, ∃ g : Fam,
      IsEpsSolP α ρ ε T Φs E g₀ g ∧
        ∀ τ ∈ Set.Icc 0 T,
          Work.FTS.EllipticEst.SmoothOpen (slice g τ) ∧
            Work.Spaces.HkMem α 4 (slice (JfamP ρ ε g) τ) ∧
            Work.Spaces.HkMem α 6 (slice g τ) ∧
            Work.FTS.Nonlin.Xn α (slice (JfamP ρ ε g) τ) ≤ C₀ * α ^ 2 ∧
            Work.FTS.StrongGlobal.Xn6 α (slice g τ) ≤ K' ∧
            Work.FTS.ClassC.ClassC α (slice (JfamP ρ ε g) τ) ∧
            ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)
              (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Icc 0 T) ∧
            EpsDecay α ρ Φs E ε τ g Maj

/-- **`EpsUniformMem` is monotone in the two constants** (for `α ≥ 0`): the existential `K'` of the
definition absorbs the increase of `K`. -/
theorem EpsUniformMem.mono {α : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn}
    {C₀ K C₀' K' : ℝ} (h : EpsUniformMem α ρ Φs E g₀ C₀ K) (hα : 0 ≤ α) (h4 : C₀ ≤ C₀')
    (hK : K ≤ K') : EpsUniformMem α ρ Φs E g₀ C₀' K' := by
  refine ⟨h.1, h.2.1, ?_⟩
  intro T hT
  obtain ⟨K'', hK'', ε₁, hε₁, Maj, hMajint, hg⟩ := h.2.2 T hT
  refine ⟨max K'' K', le_max_right _ _, ε₁, hε₁, Maj, hMajint, ?_⟩
  intro ε hε
  obtain ⟨g, hsol, hb⟩ := hg ε hε
  refine ⟨g, hsol, ?_⟩
  intro τ hτ
  exact ⟨(hb τ hτ).1, (hb τ hτ).2.1, (hb τ hτ).2.2.1,
    le_trans (hb τ hτ).2.2.2.1 (mul_le_mul_of_nonneg_right h4 (pow_nonneg hα 2)),
    le_trans (hb τ hτ).2.2.2.2.1 (le_max_left _ _), (hb τ hτ).2.2.2.2.2.1,
    (hb τ hτ).2.2.2.2.2.2.1, (hb τ hτ).2.2.2.2.2.2.2⟩

end Work.FTS.StrongEps
