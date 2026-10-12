import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseC3QAll.NWindow_ta_sum
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseC3QAll.NWindow_linear_bound`

The **linear term in the `ã`-modes on the window** (`eq:EstimateQ3Tilde4`, the
`ρ_z z Ŵ₁ω(0)(2π)⁻³∫χ̂²(s)(ã_s†+ã_s)ds` term of FS `eq:Q3Cancels`, and also the
`χ̂`-weighted linear term of FS `lem:EstimatesOnQ3-js`):

```
|⟨Φ, (Σ_{s∈S} c_s (ã_s† + ã_s))Φ⟩| ≤ 2 √𝓜 √(Σ_{s∈S} c_s²) ‖Φ‖²
```

for `Φ = 1_{[0,𝓜]}(n₊)Φ` (`Work.BoseB7A.TildeData.NWindow M Φ`) and `S ∌ 0`.  Note the
**`ℓ²`** weight `√(Σ c_s²)`: the linear form's coefficients enter through
Cauchy–Schwarz *twice* (once in the Fock form, once in weighting the modes), so
the `ℓ²`-bound is the correct and strictly stronger statement (the `ℓ¹`-version
`2√𝓜 (Σ|c_s|)‖Φ‖²` is `Work.BoseB7.linearTerm_bound` for the `χ`-modes).

## The argument

Write `L = Σ_{s∈S} c_s (ã_s† + ã_s)` and `A = Σ_{s∈S} c_s ã_s` (`L = A† + A`).

1. *The two halves contribute equally.*  `ã_s†` is the adjoint of `ã_s`
   (`Work.BoseB7A.TildeData.taDag_adjoint`) and `bp` is symmetric, so
   `⟨LΦ, Φ⟩ = 2⟨AΦ, Φ⟩` (`bp_taLinOp_eq`).
2. *Cauchy–Schwarz in the Fock form*: `|⟨AΦ,Φ⟩| ≤ √⟨AΦ,AΦ⟩ √‖Φ‖²`
   (`Work.BoseB7.bp_cauchy_abs`).
3. *The `ℓ²`-weighted mode bound*: `⟨AΦ,AΦ⟩ ≤ (Σ c_s²)(Σ ‖ã_sΦ‖²)`
   (`bp_sum_l2_bound`, Cauchy–Schwarz for the positive semidefinite Fock form
   with the Gram matrix `⟨ã_sΦ, ã_{s'}Φ⟩` of the vectors `ã_sΦ` — *not* the
   `ℓ¹`-weighted AM–GM bound of `Work.BoseB7.sum_a_bound`, which would give
   `(Σ|c_s|)²`).
4. *The window*: `Σ_{s∈S} ‖ã_sΦ‖² ≤ 𝓜‖Φ‖²` (`NWindow_ta_sum`: a finite family
   of orthonormal θ-modes counts at most `n₊` particles, and `ã_s` lowers the
   window).
5. *Square-root arithmetic*: `Work.BoseB7.sqrt_mul_sqrt_le` turns
   `⟨AΦ,AΦ⟩ ≤ (Σc_s²)(𝓜‖Φ‖²)` into `√⟨AΦ,AΦ⟩·‖Φ‖ ≤ √(Σc_s²)·√𝓜·‖Φ‖²`.

-/

noncomputable section

open scoped BigOperators

namespace Work.BoseC3QAll

open Work.BoseB7

/-- **`ℓ²`-weighted Cauchy–Schwarz for the Fock form.**  A linear combination of
vectors is controlled, in the Fock form `bp`, by the `ℓ²`-norm of its
coefficients times the sum of the individual energies:

  `⟨Σ_s c_s v_s, Σ_s c_s v_s⟩ ≤ (Σ_s c_s²)·(Σ_s ⟨v_s, v_s⟩)`.

This is the statement that the Gram matrix `⟨v_s, v_{s'}⟩` is positive
semidefinite with diagonal `⟨v_s,v_s⟩`, hence bounded by the trace: expand the
form on the double sum (`Work.BoseB7.SumABound.bp_sum_sum`), bound every entry
by `√⟨v_s,v_s⟩√⟨v_{s'},v_{s'}⟩` (`Work.BoseB7.bp_cauchy_abs`), and apply
Cauchy–Schwarz (`Finset.sum_mul_sq_le_sq_mul_sq`).  It is the `ℓ²`-counterpart
of the `ℓ¹`-weighted `Work.BoseB7.sum_a_bound`. -/
theorem bp_sum_l2_bound {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (F : Work.BoseB7.FockData Mode) (S : Finset Mode) (c : Mode → ℝ) (v : Mode → F.H) :
    F.bp (∑ s ∈ S, (c s) • v s) (∑ s ∈ S, (c s) • v s)
      ≤ (∑ s ∈ S, c s ^ 2) * (∑ s ∈ S, F.bp (v s) (v s)) := by
  rw [SumABound.bp_sum_sum F S c v]
  -- every entry of the Gram matrix is bounded by the product of the two diagonal roots
  have hterm : ∀ s ∈ S, ∀ s' ∈ S,
      c s * c s' * F.bp (v s) (v s')
        ≤ (|c s| * Real.sqrt (F.bp (v s) (v s))) *
            (|c s'| * Real.sqrt (F.bp (v s') (v s'))) := by
    intro s _ s' _
    have h2 : |F.bp (v s) (v s')| ≤
        Real.sqrt (F.bp (v s) (v s)) * Real.sqrt (F.bp (v s') (v s')) :=
      bp_cauchy_abs F _ _
    calc c s * c s' * F.bp (v s) (v s')
        ≤ |c s * c s' * F.bp (v s) (v s')| := le_abs_self _
      _ = |c s| * |c s'| * |F.bp (v s) (v s')| := by rw [abs_mul, abs_mul]
      _ ≤ |c s| * |c s'| *
            (Real.sqrt (F.bp (v s) (v s)) * Real.sqrt (F.bp (v s') (v s'))) :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ = (|c s| * Real.sqrt (F.bp (v s) (v s))) *
            (|c s'| * Real.sqrt (F.bp (v s') (v s'))) := by ring
  refine le_trans (Finset.sum_le_sum fun s hs => Finset.sum_le_sum fun s' hs' =>
    hterm s hs s' hs') ?_
  -- the double sum of the bounding products is `(Σ_s |c_s|√⟨v_s,v_s⟩)²`
  have hsquare : (∑ s ∈ S, ∑ s' ∈ S,
        (|c s| * Real.sqrt (F.bp (v s) (v s))) *
          (|c s'| * Real.sqrt (F.bp (v s') (v s'))))
      = (∑ s ∈ S, |c s| * Real.sqrt (F.bp (v s) (v s)))^2 := by
    rw [sq, Finset.sum_mul_sum]
  rw [hsquare]
  have h1 : (∑ s ∈ S, |c s| ^ 2) = ∑ s ∈ S, c s ^ 2 :=
    Finset.sum_congr rfl (fun s _ => by rw [sq_abs])
  have h2 : (∑ s ∈ S, (Real.sqrt (F.bp (v s) (v s)))^2)
      = ∑ s ∈ S, F.bp (v s) (v s) :=
    Finset.sum_congr rfl (fun s _ => Real.sq_sqrt (F.bp_nonneg (v s)))
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S (fun s => |c s|)
    (fun s => Real.sqrt (F.bp (v s) (v s)))
  rw [h1, h2] at hcs
  exact hcs

/-- **The linear term is twice its annihilation part in the Fock form.**  For
`L = Σ_{s∈S} c_s (ã_s† + ã_s)` and `A = Σ_{s∈S} c_s ã_s` (its adjoint),
`⟨LΦ, Φ⟩ = 2⟨AΦ, Φ⟩`: this is the adjointness of `ã_s†`
(`Work.BoseB7A.TildeData.taDag_adjoint`) plus symmetry of the Fock form
(`FockData.bp_symm`), so the creation and annihilation halves contribute
equally.  (`Work.BoseB7.bp_linearOp_eq` is the same identity for the `χ`-modes
and the full `excited Mode`.) -/
theorem bp_taLinOp_eq {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (T : Work.BoseC3QAll.TildeData F) (S : Finset Mode)
    (c : Mode → ℝ) (Φ : F.H) :
    F.bp ((∑ s ∈ S, (c s) • (T.taDag s + T.ta s)) Φ) Φ
      = 2 * F.bp ((∑ s ∈ S, (c s) • T.ta s) Φ) Φ := by
  have hsplit : (∑ s ∈ S, (c s) • (T.taDag s + T.ta s))
      = (∑ s ∈ S, (c s) • T.taDag s) + (∑ s ∈ S, (c s) • T.ta s) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun s _ => smul_add _ _ _)
  have hadj : F.bp ((∑ s ∈ S, (c s) • T.taDag s) Φ) Φ
      = F.bp Φ ((∑ s ∈ S, (c s) • T.ta s) Φ) := by
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      T.taDag_adjoint]
  rw [hsplit, LinearMap.add_apply, map_add, LinearMap.add_apply, hadj,
    F.bp_symm Φ ((∑ s ∈ S, (c s) • T.ta s) Φ)]
  ring

/-- **The linear term in the `ã`-modes is bounded on FS's window by the `ℓ²`-norm
of its coefficients.**  If `Φ = 1_{[0,𝓜]}(n₊)Φ` (`Work.BoseB7A.TildeData.NWindow M Φ`), `M ≥ 0`
and `S` contains no condensate mode, then for every real coefficient family `c`

  `|⟨Φ, (Σ_{s∈S} c_s (ã_s† + ã_s))Φ⟩| ≤ 2 √𝓜 √(Σ_{s∈S} c_s²) ‖Φ‖²`.

Proof: `bp_taLinOp_eq` reduces to the annihilation part `A = Σ_{s∈S} c_s ã_s`,
Cauchy–Schwarz (`bp_cauchy_abs`) bounds `|⟨AΦ,Φ⟩|` by `√⟨AΦ,AΦ⟩√‖Φ‖²`, the
`ℓ²`-weighted Gram bound `bp_sum_l2_bound` gives
`⟨AΦ,AΦ⟩ ≤ (Σ c_s²)(Σ_s ‖ã_sΦ‖²)`, `NWindow_ta_sum` bounds the mode sum by
`𝓜‖Φ‖²`, and `Work.BoseB7.sqrt_mul_sqrt_le` performs the square-root
arithmetic.  The degenerate case `‖Φ‖ = 0` is absorbed by the `√W = 0` branch of
that lemma (and `hM` is used only through `√` multiplicativity and `𝓜‖Φ‖² ≥ 0`). -/
theorem NWindow_linear_bound {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (T : Work.BoseC3QAll.TildeData F) {M : ℝ} (hM : 0 ≤ M)
    {Φ : F.H} (hΦ : T.NWindow M Φ) (S : Finset Mode) (hS : ∀ s ∈ S, s ≠ 0) (c : Mode → ℝ) :
    |F.qw Φ (∑ s ∈ S, (c s) • (T.taDag s + T.ta s))| ≤
      2 * Real.sqrt M * Real.sqrt (∑ s ∈ S, c s ^ 2) * F.normSq Φ := by
  have hW : 0 ≤ F.normSq Φ := by
    rw [Work.BoseB7.FockData.normSq]
    exact F.bp_nonneg Φ
  have hSQ : 0 ≤ ∑ s ∈ S, c s ^ 2 := Finset.sum_nonneg fun s _ => sq_nonneg _
  -- the annihilation combination, as a vector of `F.H`
  have hval : (∑ s ∈ S, (c s) • T.ta s) Φ = ∑ s ∈ S, (c s) • (T.ta s Φ) := by
    simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  -- ### 1. the annihilation part: `ℓ²`-weighted Gram bound + the window
  have hA : F.bp ((∑ s ∈ S, (c s) • T.ta s) Φ) ((∑ s ∈ S, (c s) • T.ta s) Φ)
      ≤ (∑ s ∈ S, c s ^ 2) * (M * F.normSq Φ) := by
    rw [hval]
    calc F.bp (∑ s ∈ S, (c s) • (T.ta s Φ)) (∑ s ∈ S, (c s) • (T.ta s Φ))
        ≤ (∑ s ∈ S, c s ^ 2) * (∑ s ∈ S, F.bp (T.ta s Φ) (T.ta s Φ)) :=
          bp_sum_l2_bound F S c fun s => T.ta s Φ
      _ ≤ (∑ s ∈ S, c s ^ 2) * (M * F.normSq Φ) :=
          mul_le_mul_of_nonneg_left (NWindow_ta_sum F T hM hΦ S hS) hSQ
  -- ### 2. Cauchy–Schwarz in the Fock form
  have hcs : |F.bp ((∑ s ∈ S, (c s) • T.ta s) Φ) Φ|
      ≤ Real.sqrt (F.bp ((∑ s ∈ S, (c s) • T.ta s) Φ) ((∑ s ∈ S, (c s) • T.ta s) Φ))
        * Real.sqrt (F.normSq Φ) := by
    rw [Work.BoseB7.FockData.normSq]
    exact bp_cauchy_abs F ((∑ s ∈ S, (c s) • T.ta s) Φ) Φ
  -- ### 3. square roots
  have hMW : 0 ≤ M * F.normSq Φ := mul_nonneg hM hW
  have hsq : Real.sqrt (∑ s ∈ S, c s ^ 2) * Real.sqrt (∑ s ∈ S, c s ^ 2)
      = ∑ s ∈ S, c s ^ 2 := by
    rw [← sq, Real.sq_sqrt hSQ]
  have hroot : Real.sqrt (F.bp ((∑ s ∈ S, (c s) • T.ta s) Φ)
          ((∑ s ∈ S, (c s) • T.ta s) Φ)) * Real.sqrt (F.normSq Φ)
      ≤ Real.sqrt (∑ s ∈ S, c s ^ 2) * Real.sqrt M * F.normSq Φ := by
    refine sqrt_mul_sqrt_le (Real.sqrt_nonneg _) hW hMW ?_
    rw [hsq]
    exact hA
  -- ### 4. assembly
  have hlin := bp_taLinOp_eq F T S c Φ
  calc |F.qw Φ (∑ s ∈ S, (c s) • (T.taDag s + T.ta s))|
      = 2 * |F.bp ((∑ s ∈ S, (c s) • T.ta s) Φ) Φ| := by
        rw [Work.BoseB7.FockData.qw, hlin, abs_mul,
          abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
    _ ≤ 2 * (Real.sqrt (F.bp ((∑ s ∈ S, (c s) • T.ta s) Φ)
            ((∑ s ∈ S, (c s) • T.ta s) Φ)) * Real.sqrt (F.normSq Φ)) :=
        mul_le_mul_of_nonneg_left hcs (by norm_num)
    _ ≤ 2 * (Real.sqrt (∑ s ∈ S, c s ^ 2) * Real.sqrt M * F.normSq Φ) :=
        mul_le_mul_of_nonneg_left hroot (by norm_num)
    _ = 2 * Real.sqrt M * Real.sqrt (∑ s ∈ S, c s ^ 2) * F.normSq Φ := by ring

end Work.BoseC3QAll
