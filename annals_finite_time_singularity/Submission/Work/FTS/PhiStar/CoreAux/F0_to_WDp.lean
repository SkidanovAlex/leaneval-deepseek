/-
# `FTS/PhiStar/CoreAux/F0_to_WDp.lean` — the flat class `F0` controls the open-quadrant norm `WDp`

`Work.FTS.PhiStar.F0 n K f` (see `CoreAux/Defs.lean`) says that all the mixed weighted
derivatives `(z+1)^k ∂_z^k D_θ^i f` with `k + i ≤ n` are bounded by `K` on the open quadrant
`Q0 = (0,∞) × (0,π/2)`.  `Work.FTS.VocabO.WDp n f` is the *unweighted* open-quadrant norm: the
sum of the suprema `supAbsO (D_z^b D_θ^j f)` over the `(n+1)²` pairs `b, j ≤ n` with
`b + j ≤ n`, and `WDMem n f` its honesty predicate.

This file proves the bridge between the two vocabularies:

`F0 n K f  →  WDMem n f ∧ WDp n f ≤ C(n) · K`

for every `f` which is `C^∞` on the open quadrant (`SmoothOpen f`) and every `K ≥ 0`.

**The mathematics.**  The single non-trivial ingredient is the Stirling expansion of the
curvilinear operator `D_z = z ∂_z`,

`D_z^b = ∑_{k ≤ b} S(b,k) z^k ∂_z^k`   (`Work.Spaces.scoef`, `D_z^n f = ∑ S(n,k) z^k ∂_z^k f`),

available on the *open* half-line `(0,∞)` for a slice which is `C^∞` there
(`Work.FTS.OpenPkg.DzIter_eq_sum_scoef_open` — exactly the regularity that `SmoothOpen` gives,
the `z`-slices need not be differentiable at the boundary angles).  Applying it to the slice
`g = D_θ^j f` at an interior angle,

`D_z^b D_θ^j f = ∑_{k ≤ b} S(b,k) (z^k ∂_z^k D_θ^j f)`,

and since `z ≤ z+1` and `k + j ≤ b + j ≤ n`, every summand is bounded by `K`:

`|z^k ∂_z^k D_θ^j f| ≤ (z+1)^k |∂_z^k D_θ^j f| ≤ K`.

The total coefficient mass of the expansion is the Bell number `bell b = ∑_{k ≤ b} S(b,k)`
(`Work.Spaces.abs_sum_scoef_mul_le`), so `|D_z^b D_θ^j f| ≤ bell b · K ≤ B · K` on the open
quadrant, where `B := ∑_{m ≤ n} bell m` is a constant which dominates `bell b` for every
`b ≤ n` (each summand of `B` is nonnegative and `b` is one of its indices — no monotonicity of
the Bell numbers is needed).  `supAbsO_le` then turns the pointwise bound into the bound of each
supremum, and the `(n+1)²`-entry grid bound `WDp_le_of_pointwise_gen` gives the `WDp` estimate.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.PhiStar.CoreAux.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.OpenPkg.ScoefOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.CoreAux

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The `WDp`-grid bound at a general order -/

/-- **Pointwise bounds give the `WDp` estimate at any order `n`.**  If every mixed derivative
`D_z^b D_θ^j f` with `b + j ≤ n` is bounded by `M ≥ 0` on the whole open quadrant, then the
double sum of the corresponding open-quadrant suprema is at most the number `(n+1)²` of grid
entries times `M` (the entries with `b + j > n` contribute the junk value `0 ≤ M`).

This is the general-`n` form of `Work.FTS.OpenPkg.WDp_le_of_pointwise` (which is the case
`n = 4`, with the loose constant `25`); the only point to note is that the supremum `supAbsO`
ranges over exactly the same open quadrant on which the hypothesis bounds `f`. -/
theorem WDp_le_of_pointwise_gen {n : ℕ} {M : ℝ} (hM : 0 ≤ M) {f : ℝ → ℝ → ℝ}
    (h : ∀ b j : ℕ, b + j ≤ n → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed b j f z θ| ≤ M) :
    Work.FTS.VocabO.WDp n f ≤ ((n : ℝ) + 1) ^ 2 * M := by
  classical
  rw [Work.FTS.VocabO.WDp]
  calc
    ∑ b ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
        (if b + j ≤ n then Work.FTS.H2.supAbsO (Work.Spaces.mixed b j f) else 0)
      ≤ ∑ _b ∈ Finset.range (n + 1), ∑ _j ∈ Finset.range (n + 1), M := by
        refine Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun j _ => ?_
        split_ifs with hbj
        · exact Work.FTS.H2.supAbsO_le (fun z θ hz hθ hθ' => h b j hbj z θ hz hθ hθ')
        · exact hM
    _ = ((n : ℝ) + 1) ^ 2 * M := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

/-! ## The bridge `F0 → WDp` -/

theorem F0_to_WDp (n : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ (K : ℝ) (f : ℝ → ℝ → ℝ), 0 ≤ K → Work.FTS.EllipticEst.SmoothOpen f → Work.FTS.PhiStar.F0 n K f → Work.FTS.VocabO.WDMem n f ∧ Work.FTS.VocabO.WDp n f ≤ C * K := by
  classical
  -- the constant: `(n+1)² · (∑_{m ≤ n} bell m + 1)`, which dominates every `bell b` with `b ≤ n`
  set B : ℝ := ∑ m ∈ Finset.range (n + 1), (Work.Spaces.bell m : ℝ) with hBdef
  have hBnn : (0 : ℝ) ≤ B := by
    rw [hBdef]
    exact Finset.sum_nonneg fun m _ => Nat.cast_nonneg (Work.Spaces.bell m)
  refine ⟨((n : ℝ) + 1) ^ 2 * (B + 1), ?_, ?_⟩
  · have h1 : (0 : ℝ) < (n : ℝ) + 1 := by
      have := Nat.cast_nonneg (α := ℝ) n
      linarith
    exact mul_pos (pow_pos h1 2) (by linarith)
  · intro K f hK hsf hf
    -- `bell b ≤ B` for `b ≤ n`: the term `b` occurs in the defining sum of `B`
    have hBle : ∀ m ≤ n, (Work.Spaces.bell m : ℝ) ≤ B := by
      intro m hm
      rw [hBdef]
      exact Finset.single_le_sum (fun i _ => Nat.cast_nonneg (Work.Spaces.bell i))
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hm))
    have hBK : (0 : ℝ) ≤ B * K := mul_nonneg hBnn hK
    -- the pointwise bound on the open quadrant
    have hpt : ∀ b j : ℕ, b + j ≤ n → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed b j f z θ| ≤ B * K := by
      intro b j hbj z θ hz hθ hθ'
      -- the Stirling expansion of `D_z^b` on the open half-line, for the slice `D_θ^j f`
      have hslice : ContDiffOn ℝ Work.Stability.smoothOrder
          (fun z' => Work.Spaces.DthIter j f z' θ) (Set.Ioi 0) :=
        Work.FTS.OpenPkg.smoothOpen_DthIter_slice_z hsf j ⟨hθ, hθ'⟩
      rw [Work.Spaces.mixed,
        Work.FTS.OpenPkg.DzIter_eq_sum_scoef_open (h := Work.Spaces.DthIter j f) hslice b z
          (Set.mem_Ioi.mpr hz)]
      -- each summand is bounded by `K`, because `z ≤ z+1` and `k + j ≤ n`
      have hterm : ∀ k ≤ b,
          |z ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j f) z θ| ≤ K := by
        intro k hk
        have hkj : k + j ≤ n := by omega
        have h2 : (z + 1) ^ k
            * |Work.Spaces.pzIter k (Work.Spaces.DthIter j f) z θ| ≤ K := by
          have h1 := hf k j hkj z θ hz hθ hθ'
          rwa [abs_mul, abs_of_pos (pow_pos (by linarith : (0 : ℝ) < z + 1) k)] at h1
        have h3 : z ^ k * |Work.Spaces.pzIter k (Work.Spaces.DthIter j f) z θ|
            ≤ (z + 1) ^ k
              * |Work.Spaces.pzIter k (Work.Spaces.DthIter j f) z θ| :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hz.le (by linarith) k) (abs_nonneg _)
        calc |z ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j f) z θ|
            = z ^ k * |Work.Spaces.pzIter k (Work.Spaces.DthIter j f) z θ| := by
              rw [abs_mul, abs_of_nonneg (pow_nonneg hz.le k)]
          _ ≤ (z + 1) ^ k
                * |Work.Spaces.pzIter k (Work.Spaces.DthIter j f) z θ| := h3
          _ ≤ K := h2
      refine le_trans (Work.Spaces.abs_sum_scoef_mul_le b K
        (fun k => z ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j f) z θ) hterm) ?_
      exact mul_le_mul_of_nonneg_right (hBle b (le_trans (Nat.le_add_right b j) hbj)) hK
    refine ⟨?_, ?_⟩
    · intro b j hbj
      exact ⟨B * K, fun z θ hz hθ hθ' => hpt b j hbj z θ hz hθ hθ'⟩
    · have hgrid := WDp_le_of_pointwise_gen (n := n) (M := B * K) hBK (f := f) hpt
      refine le_trans hgrid ?_
      have h1 : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := sq_nonneg _
      have h2 : B * K ≤ (B + 1) * K := by
        rw [add_mul, one_mul]
        exact le_add_of_nonneg_right hK
      calc ((n : ℝ) + 1) ^ 2 * (B * K)
          ≤ ((n : ℝ) + 1) ^ 2 * ((B + 1) * K) := mul_le_mul_of_nonneg_left h2 h1
        _ = ((n : ℝ) + 1) ^ 2 * (B + 1) * K := by ring

end Work.FTS.PhiStar.CoreAux
