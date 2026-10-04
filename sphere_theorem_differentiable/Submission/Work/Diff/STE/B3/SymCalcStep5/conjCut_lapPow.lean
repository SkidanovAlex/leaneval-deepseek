import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.B3.SymCalc

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# B3 symbol calculus, step 5: the exact conjugation identity for `[Λ^k, conjCut]` (all `k`)

The second half of the cross-term crux (PIECE 4), in the general-`k` form the `k`-th order assembly
consumes.  Nothing here is analytic: it is the *exact* identity that turns the commutator of the
chart-`i` Laplacian power with the *transported* cutoff into a commutator in the other chart,
where the flat multiplier estimates (`mulDeriv_comm_trunc_le`, `mulDeriv_comm_trunc_s0_le`,
`flat_multiplier_commutator`) apply.

Setup, with `T = τ` the chart-2 ↦ chart-1 transition and `T' = τ⁻¹`:

* `lapPow k` — the flat Laplacian power `Λ^k` on functions of the torus: the Fourier multiplier
  with symbol `flatLam m ^ k` (the pointwise version of `Work.Diff.STE.B3.lamSym ^ k`);
* `conjLapPow k T T' := compMap T ∘ lapPow k ∘ compMap T'` — **the conjugate operator** `P_k`, i.e.
  the flat Laplacian power written in the other chart;
* `conjCut ρ ε T T' = compMap T' ∘ flatCut ρ ε ∘ compMap T` — the transported cutoff `V = S_ε^{(j→i)}`.

Then, using only the two inverse identities:

* `compMap T' (compMap T g) = g`  (from `hTinv1`) and `compMap T (compMap T' g) = g` (from `hTinv2`);
* `lapPow k (compMap T' h) = compMap T' (conjLapPow k T T' h)`  (`rfl`-unfolding + `hTinv2`);
* `compMap T (lapPow k g) = conjLapPow k T T' (compMap T g)`  (`rfl`-unfolding + `hTinv1`);

one gets, for every `g`, the exact identity

  `[Λ^k, V] g = lapPow k (conjCut ρ ε T T' g) − conjCut ρ ε T T' (lapPow k g)`
            `= compMap T' ( [P_k, S_ε] (compMap T g) )`,

written out in `conjCut_lapPow_comm` below.  Composing with the `k`-th order flat estimate
`[P_k, S_ε] = Σ_{|β|≤2k} [M_{A_β}, S_ε] ∂^β` (chain rule for `P_k`, whose coefficients come from
`DT'`) and the estimates in `SymCalcStep1` gives PIECE 4-k: order `2k−1`, uniformly in `ε`.
The `k = 1` case is the separately delegated `conj_cut_comm_laplacian_le`.
-/

noncomputable section

open MeasureTheory BigOperators

namespace Work.Diff.STE.B3.SymCalcStep5

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The flat Laplacian power `Λ^k` on functions**: the Fourier multiplier with symbol
`flatLam m ^ k`. -/
def lapPow (k : ℕ) (g : (ι → ℝ) → ℂ) : (ι → ℝ) → ℂ :=
  Work.Diff.STE.seriesFun (fun m : ι → ℤ =>
    (((Work.Diff.STE.B3.SymCalc.flatLam m) ^ k : ℝ) : ℂ) *
      Work.Diff.STE.fourierCoeff g m)

/-- **The conjugate operator `P_k`**: `Λ^k` written in the `T'`-coordinates. -/
def conjLapPow (k : ℕ) (T T' : (ι → ℝ) → (ι → ℝ)) (h : (ι → ℝ) → ℂ) : (ι → ℝ) → ℂ :=
  Work.Diff.STE.B3.SymCalc.compMap T
    (lapPow k (Work.Diff.STE.B3.SymCalc.compMap T' h))

/-- The left inverse identity for the two chart maps (one `funext`, no analysis). -/
theorem compMap_T_compMap_T' (T T' : (ι → ℝ) → (ι → ℝ))
    (hTinv1 : ∀ x : ι → ℝ, T' (T x) = x) (g : (ι → ℝ) → ℂ) :
    Work.Diff.STE.B3.SymCalc.compMap T (Work.Diff.STE.B3.SymCalc.compMap T' g) = g := by
  funext x
  simp only [Work.Diff.STE.B3.SymCalc.compMap]
  rw [hTinv1]

/-- The right inverse identity for the two chart maps. -/
theorem compMap_T'_compMap_T (T T' : (ι → ℝ) → (ι → ℝ))
    (hTinv2 : ∀ y : ι → ℝ, T (T' y) = y) (g : (ι → ℝ) → ℂ) :
    Work.Diff.STE.B3.SymCalc.compMap T' (Work.Diff.STE.B3.SymCalc.compMap T g) = g := by
  funext x
  simp only [Work.Diff.STE.B3.SymCalc.compMap]
  rw [hTinv2]

/-- `Λ^k` commutes with the conjugation: `Λ^k ∘ compMap T' = compMap T' ∘ P_k`. -/
theorem lapPow_compMap_T' (k : ℕ) (T T' : (ι → ℝ) → (ι → ℝ))
    (hTinv2 : ∀ y : ι → ℝ, T (T' y) = y) (h : (ι → ℝ) → ℂ) :
    lapPow k (Work.Diff.STE.B3.SymCalc.compMap T' h)
      = Work.Diff.STE.B3.SymCalc.compMap T' (conjLapPow k T T' h) := by
  rw [conjLapPow]
  exact (compMap_T'_compMap_T T T' hTinv2
    (lapPow k (Work.Diff.STE.B3.SymCalc.compMap T' h))).symm

/-- `compMap T` intertwines `Λ^k` with the conjugate operator `P_k`. -/
theorem compMap_T_lapPow (k : ℕ) (T T' : (ι → ℝ) → (ι → ℝ))
    (hTinv2 : ∀ y : ι → ℝ, T (T' y) = y) (g : (ι → ℝ) → ℂ) :
    Work.Diff.STE.B3.SymCalc.compMap T (lapPow k g)
      = conjLapPow k T T' (Work.Diff.STE.B3.SymCalc.compMap T g) := by
  rw [conjLapPow, compMap_T'_compMap_T T T' hTinv2 g]

/-- **The exact conjugation identity**, general `k`:

  `[Λ^k, V] g = compMap T' ( [P_k, S_ε] (compMap T g) )`

where `V = conjCut ρ ε T T'` and `P_k = conjLapPow k T T'`.  A pure rewriting exercise from the
three identities above; no `ε`-analysis, no smoothness, no support hypothesis. -/
theorem conjCut_lapPow_comm (ρ : (ι → ℝ) → ℝ) (ε : ℝ) (k : ℕ)
    (T T' : (ι → ℝ) → (ι → ℝ))
    (hTinv1 : ∀ x : ι → ℝ, T' (T x) = x)
    (hTinv2 : ∀ y : ι → ℝ, T (T' y) = y)
    (g : (ι → ℝ) → ℂ) :
    lapPow k (Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T' g)
        - Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T' (lapPow k g)
      = Work.Diff.STE.B3.SymCalc.compMap T'
          (conjLapPow k T T'
              (Work.Diff.STE.B3.SymCalc.flatCut ρ ε
                (Work.Diff.STE.B3.SymCalc.compMap T g))
            - Work.Diff.STE.B3.SymCalc.flatCut ρ ε
                (conjLapPow k T T' (Work.Diff.STE.B3.SymCalc.compMap T g))) := by
  simp only [Work.Diff.STE.B3.SymCalc.conjCut]
  rw [lapPow_compMap_T' k T T' hTinv2]
  rw [compMap_T_lapPow k T T' hTinv2]
  funext x
  simp only [Work.Diff.STE.B3.SymCalc.compMap, Pi.sub_apply]

end Work.Diff.STE.B3.SymCalcStep5
