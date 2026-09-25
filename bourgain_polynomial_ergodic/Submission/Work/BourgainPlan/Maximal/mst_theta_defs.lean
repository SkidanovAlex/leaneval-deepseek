import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_major_defs
import Submission.Work.BourgainPlan.Maximal.mstThetaEpsDefs
import Submission.Work.BourgainPlan.Maximal.iw_superset

/-!
# MST's input `(C2)`: the signed lacunary profile differences, as an `Lʳ(ℝ)`-multiplier

Mirek–Stein–Trojan's Theorem 7 (the `ℓᵖ` estimate for the level model `ν^s_{2^n}` in the range
`n ≤ 2^{κ_s}`) is proved by replacing the β-dependent Gauss sum `G(a/q)` by the *global* Weyl sum
`μ_J(ξ) = m_J(ξ)` (close to `G(a/q)` on the arcs) and then applying the Rademacher–Menshov
sup-to-blocks inequality followed by Khintchine.  The resulting signed sums involve the multiplier

  `Θ_ε = Σ_{j<M} ε_j (Φ_{2^{(j+1)2^i}} − Φ_{2^{j2^i}})`,

a *signed lacunary combination of profile increments*.  MST invoke the theory of **continuous
singular Radon transforms** (`[bigs, Section 11]`, Duoandikoetxea–Rubio de Francia) to conclude that
`Θ_ε` is bounded on `L^r(ℝ)` **uniformly in the signs** — their `(C2)` (`MST_ROUTE.md` §1), and also
the content of their Theorem 17.

**Warning (`MST_LANE_NOTE.md` Addendum 4).**  `Θ_ε` is *not* a Mikhlin multiplier uniformly in the
signs (a reviewer-refuted claim; see the header of `Maximal/mstThetaEpsDefs.lean` for the explicit
counterexample), so the `ℓʳ` half of §5 must **not** pass through the Mikhlin hypotheses of
`IWSupersetBoundLift`.  The correct interface is `IWMult r ψ A` — the multiplier-norm hypothesis
consumed directly by `iwEndpoint2r`/`iwRangeBound` — which is what `MSTThetaBound` below states.
The corpus has the *band-localized* version of `(C2)`
(`Maximal/bandedBlockMultiplier_lp`); the remaining gap to the raw lacunary sum is the
partition-of-unity passage described in `MST_LANE_NOTE.md` Addendum 4.
-/

open MeasureTheory Finset
open scoped BigOperators ENNReal

set_option autoImplicit false

namespace Work.BourgainPlan.Maximal

open Work.BourgainPlan.IonescuWainger

noncomputable section

/-- The **circle symbol** of the signed-sum step of MST Theorem 7: the product of the signed
lacunary profile-difference multiplier `Θ_ε` (evaluated along the canonical lift) with the level-`s`
bump `η_s`.  Because `η_s` is supported in a ball of radius `< 1/2`, this product is a genuine
circle function whose lift is `θ ↦ Θ_ε θ · η_s θ`. -/
noncomputable def mstThetaSym (P : Polynomial ℤ) (d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (i M s : ℕ)
    (ε : ℕ → ℂ) : Work.BourgainPlan.IonescuWainger.Circle → ℂ :=
  fun ξ => mstThetaEps P i M ε (iwRep ξ) * mstEta d χ η s ξ

@[simp] theorem mstThetaSym_apply (P : Polynomial ℤ) (d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (i M s : ℕ)
    (ε : ℕ → ℂ) (ξ : Work.BourgainPlan.IonescuWainger.Circle) :
    mstThetaSym P d χ η i M s ε ξ = mstThetaEps P i M ε (iwRep ξ) * mstEta d χ η s ξ := rfl

/-- **MST's `(C2)`** (their Theorem 17 / the citation of the continuous singular Radon transform
theory): for every integer polynomial `P` of degree `≥ 2` with positive leading coefficient and every
`r ≥ 2`, there is `A > 0` such that for all levels `i, M, s` and all sign sequences `ε` with
`‖ε j‖ ≤ 1`, the multiplier-norm hypothesis `IWMult r (Θ_ε · η_s) A` holds — i.e. the compactly
supported lift of the symbol `Θ_ε · η_s` is an `L^{2r}(ℝ)`-multiplier with norm `≤ A`, uniformly in
the signs, in the level bump and in the number of terms.

This is the named analytic input of the `ℓʳ` half of §5 (MST Theorem 7); it is *not* yet derived in
the corpus (the band-localized version is `bandedBlockMultiplier_lp`). -/
def MSTThetaBound : Prop :=
  ∀ (P : Polynomial ℤ), 2 ≤ P.natDegree → 0 < P.leadingCoeff → ∀ r : ℕ, 2 ≤ r →
    ∃ A : ℝ, 0 < A ∧ ∀ (d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (Mη : ℝ), 0 < Mη →
      ContDiff ℝ 2 η →
      (∀ x : ℝ, ‖η x‖ ≤ Mη) →
      (∀ x : ℝ, |x| * ‖deriv η x‖ ≤ Mη) →
      (∀ x : ℝ, |x| ^ 2 * ‖iteratedDeriv 2 η x‖ ≤ Mη) →
      (∀ x : ℝ, 1 / 2 < |x| → η x = 0) →
      ∀ (i M s : ℕ) (ε : ℕ → ℂ), (∀ j : ℕ, ‖ε j‖ ≤ 1) →
        Work.BourgainPlan.Maximal.IWMult r (mstThetaSym P d χ η i M s ε) (A * Mη) ∧
        Work.BourgainPlan.Maximal.IWMult r
          (fun ξ => star (mstThetaSym P d χ η i M s ε ξ)) (A * Mη)

end

end Work.BourgainPlan.Maximal
