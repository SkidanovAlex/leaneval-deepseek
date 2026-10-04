import Mathlib
import Submission.Work.Diff.STE.Lead.Gal.GardDef
import Submission.Work.Diff.STE.Lead.Gal.gardingAssembly

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The **tame (L²) transport data** of the DeTurck operator

The interface `Work.Diff.STE.Lead.Gal.GardData` of the Gårding assembly asks for *pointwise* sup
bounds on the `pdVec`-jets of the principal coefficient `A` up to order `k`:
`‖pdVec m β (ofReal (A c d)) z‖ ≤ C` for `m ≤ k`.  Those bounds are **not** available along a
solution: the order-`m` jet of the chart matrix is controlled by the energy `ENormB k₀ h` only when
`2m + n < 2k₀` (see `Work.Diff.STE.B3.mat_jet_bound_of_energy`), so a pointwise bound at order
`k+1` would require an energy bound at a level strictly *above* `k`, and iterating levels cannot
supply it.

The way out — DESIGN.md §4/§10.2 — is to use only **`L²`** bounds on the high-order jets of the
coefficient, and `L∞` (Sobolev) bounds on the *low*-order jets:

* `E := galE k h = D.ENormB k h + D.ENormB 0 h ≤ B` bounds the `Hᵏ` norm of the section (through
  the Poincaré chain `ENormB m h ≤ C ENormB k h` for `1 ≤ m ≤ k`, plus the `L²` term);
* the *transport* `Work.Diff.STE.B3.transport_deTurck_tame` gives the coefficient `A` with
  `ENormSq 0 (pdVec m β (ofReal (A c d))) ≤ C²(1 + ENormB m h)` for `m ≤ k`, i.e. the `L²` bound of
  `∂^m A` at the level `m ≤ k` (this is where the level-`k` *scalar* energy enters);
* for the low-order jets one uses Sobolev: the `Hᵐ` norm of a smooth periodic function controls the
  sup norm of its derivatives of order `≤ m − n/2 − 1`.

Consequently the commutator `[∂^k, A ∂∂]` (the `pdVec`-defect of the Leibniz rule, which is what
`Work.Diff.STE.Lead.Gal.pdVec_gard_defect_bound` bounds *pointwise*) must be bounded in `L²`, and
the *defect* hypothesis of the assembly must be restated accordingly.

This module records the resulting weakened interface `GardDataL2`, which is exactly `GardData` with

* the pointwise jet clause replaced by the `L²` clause
  `ENormSq 0 (pdVec m β (ofReal (A c d))) ≤ C` for `m ≤ k`;
* two explicit sup clauses for `A` itself and its first derivative (these are conclusions of the
  tame transport, and are all that `Work.Diff.STE.garding_vec_uniform` needs of `A`).

Everything else (symmetry, ellipticity, smoothness, periodicity and the periodised localised
identity) is verbatim `GardData`; the energy clauses however carry the factor `(1 + D.ENormB (k+1) h)`
(summed over ALL charts and frame indices — an unavoidable *off-component* coupling: the residual of
the transport identity is a smooth function of the full first jet of the chart matrix, so its `k`-th
energy sees `∂^{k+1}` of the OTHER components of `h` as well, which is exactly what
`transport_deTurck_tame` returns: the residual `Th` is the difference
`Rper_j (P h) − Σ A ∂∂ (Rper_j h)` and the tame transport controls its `k`-th jet by the `H^{k+1}`
energy of the section (the `+1` in
`transport_deTurck_tame`'s `ENormSq 0 (pdVec m β (Psi …)) ≤ C² (1 + Σ ENormB (m+1) (Rper i h a b))`),
not by the level-`k` energy; and the two low-order energies are only informative against the
`H^{k+1}` energy of the section anyway.  The extra factor costs nothing downstream: it appears
multiplied against the level-`k` energy, and is absorbed by Young into the dissipation
`-(lam'/2) ENormB (k+1) h`.
-/

namespace Work.Diff.STE.Lead.GalTame

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg Submission.Diff.STEGal
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

local notation "Idx" => Fin (Module.finrank ℝ E)

/-- **The tame (L²) transport data of the DeTurck operator in the Layer B3 components.**

This is `Work.Diff.STE.Lead.Gal.GardData` with the pointwise jet bound on the coefficient `A`
replaced by an `L²` bound (`ENormSq 0` of the `pdVec`-jets of `A c d` up to order `k`), together
with the two sup bounds on `A` and `∂A` that the tame transport
(`Work.Diff.STE.B3.transport_deTurck_tame`) actually provides.  The `L∞` bounds of the low-order
jets of `A` are *not* asked for: they are recovered inside the assembly from the `L²` bounds by
Sobolev (`k ≥ n + 4`), and the high-order jets of `A` pair with *bounded* low-order jets of the
section. -/
def GardDataL2 (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (hLC : Submission.Diff.LCSmooth I M) (k : ℕ) (lam' C : ℝ)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsym : ∀ (x : M) (u v : TangentSpace I x), h x u v = h x v u)
    (hpos : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < h x v v)
    (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h) : Prop :=
  ∀ j : ι₀,
    ∃ (A : Idx → Idx → (Idx → ℝ) → ℝ)
      (Th : Idx → Idx → (Idx → ℝ) → ℂ),
      -- the coefficient
      (∀ c d z, A c d z = A d c z) ∧
      (∀ z (ξ : Idx → ℝ), lam' * ∑ i, (ξ i) ^ 2 ≤ ∑ c, ∑ d, A c d z * ξ c * ξ d) ∧
      (∀ c d, ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (A c d)) ∧
      (∀ c d, Work.Diff.STE.Periodic1 (A c d)) ∧
      (∀ (z : Idx → ℝ) (c d : Idx), |A c d z| ≤ C) ∧
      (∀ (z : Idx → ℝ) (r c d : Idx),
        |Work.Diff.STE.pdR r (fun y : Idx → ℝ => A c d y) z| ≤ C) ∧
      (∀ (m : ℕ) (hm : m ≤ k) (β : Fin m → Idx) (c d : Idx),
        Work.Diff.STE.ENormSq 0 (Work.Diff.STE.pdVec m β
          (fun y : Idx → ℝ => ((A c d y : ℝ) : ℂ)))
          ≤ C * (1 + D.ENormB m h)) ∧
      -- the residual
      (∀ a b, ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (Th a b)) ∧
      (∀ a b, Work.Diff.STE.Periodic1 (Th a b)) ∧
      (∀ a b, Work.Diff.STE.ENormSq k (Th a b) ≤ C * (1 + D.ENormB (k + 1) h)) ∧
      -- the periodised localised identity
      (∀ a b z,
        D.Rper j (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth) a b z
          = (∑ c, ∑ d,
              ((A c d z : ℝ) : ℂ) * Work.Diff.STE.pd c (Work.Diff.STE.pd d (D.Rper j h a b)) z)
            + Th a b z) ∧
      -- the low-order energies (the level-`k-1` and `L²` energies of `P h`)
      (∀ a b, Work.Diff.STE.ENormSq (k - 1)
          (D.Rper j (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth) a b)
        ≤ C * (1 + D.ENormB (k + 1) h)) ∧
      (∀ a b, Work.Diff.STE.ENormSq 0
          (D.Rper j (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth) a b)
        ≤ C * (1 + D.ENormB (k + 1) h))

/-- **`ENormSq 0` of a pointwise bounded function.**  This is the only analytic input needed to see
that the pointwise interface `GardData` implies the `L²` interface `GardDataL2` (at the price of
replacing the constant `C` by `max (C^2) 1`); we record it here because the tame transport produces
its coefficient bounds in exactly this (`L²`, `ENormSq 0`) form. -/
lemma ENormSq_zero_le_of_sup_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → ℝ) → ℂ) (hf : Continuous f) {C : ℝ} (hb : ∀ z, ‖f z‖ ≤ C) :
    Work.Diff.STE.ENormSq 0 f ≤ C ^ 2 := by
  have hpv : ∀ l : Fin 0 → ι, Work.Diff.STE.pdVec 0 l f = f := by
    intro l
    simp only [Work.Diff.STE.pdVec, Work.Diff.STE.pdList, List.ofFn_zero, List.foldr_nil]
  rw [Work.Diff.STE.ENormSq, Finset.univ_unique, Finset.sum_singleton]
  simp only [hpv]
  exact Work.Diff.STE.Lead.Gal.integral_normSq_le hf hb

end

end Work.Diff.STE.Lead.GalTame
